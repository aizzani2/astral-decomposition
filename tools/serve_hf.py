"""
Serve a Hugging Face model (optionally with a LoRA adapter) behind the subset
of Ollama's API the pipeline uses, so `--base-url` can point at it.

    python tools/serve_hf.py astral-expmath/olmo3-7b-agda-pairs-delim-sft --port 11437
    python -m cli.run_dsp_dataset samples/heldout24.json --format definition \\
        --model astral-expmath/olmo3-7b-agda-pairs-delim-sft --base-url http://localhost:11437

MODEL is a model or an adapter repo; an adapter is loaded on the base model
its adapter_config.json names. By default the base is loaded in 4-bit NF4,
as the astral-expmath fine-tunes were trained (QLoRA) and evaluated;
`--no-4bit` loads it in bf16 and merges the adapter in, which is faster
when the model fits (Qwen3.5-4B: ~9 GB).
Prompts are completed as they are, with no chat template. Requests are
answered one at a time. Needs `pip install -e '.[serve]'`.

Endpoints: POST /api/generate {model, prompt, options: {temperature, top_p,
num_predict, stop}} -> {response, model, prompt_eval_count, eval_count,
done_reason}; GET /api/tags.
"""

from __future__ import annotations

import argparse
import json
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("model", help="Model or LoRA adapter repo (or local path).")
    parser.add_argument("--port", type=int, default=11437)
    parser.add_argument("--no-4bit", dest="four_bit", action="store_false")
    args = parser.parse_args(argv)

    model, tokenizer = load(args.model, args.four_bit)
    lock = threading.Lock()

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            if self.path.rstrip("/") == "/api/tags":
                self._reply(200, {"models": [{"name": args.model, "model": args.model}]})
            else:
                self._reply(404, {"error": "not found"})

        def do_POST(self) -> None:
            if self.path.rstrip("/") != "/api/generate":
                self._reply(404, {"error": "not found"})
                return

            body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")

            with lock:
                started = time.monotonic()
                text, n_prompt, n_out, reason = generate(
                    model, tokenizer, body.get("prompt", ""), body.get("options") or {},
                )

            self._reply(200, {
                "model": args.model, "response": text, "done": True, "done_reason": reason,
                "prompt_eval_count": n_prompt, "eval_count": n_out,
                "total_duration": int((time.monotonic() - started) * 1e9),
            })

        def _reply(self, status: int, payload: dict) -> None:
            data = json.dumps(payload).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def log_message(self, *_: object) -> None:
            pass

    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"Serving {args.model} on http://127.0.0.1:{args.port}", file=sys.stderr, flush=True)
    server.serve_forever()
    return 0


def load(name: str, four_bit: bool):
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig

    base, adapter = name, None

    try:
        from peft import PeftConfig

        base, adapter = PeftConfig.from_pretrained(name).base_model_name_or_path, name
    except Exception:
        pass   # not an adapter: a whole model

    quantization = BitsAndBytesConfig(
        load_in_4bit=True, bnb_4bit_quant_type="nf4", bnb_4bit_compute_dtype=torch.bfloat16,
    ) if four_bit else None

    model = AutoModelForCausalLM.from_pretrained(
        base, quantization_config=quantization, dtype=torch.bfloat16, device_map="cuda",
    )

    if adapter is not None:
        from peft import PeftModel

        model = PeftModel.from_pretrained(model, adapter)
        if not four_bit:   # bf16 weights take the adapter in: no LoRA layers per token
            model = model.merge_and_unload()

    model.eval()
    # An adapter repo has its own tokenizer but no config.json: give it the model's.
    tokenizer = AutoTokenizer.from_pretrained(adapter or base, config=model.config)
    print(f"Loaded {base}" + (f" + adapter {adapter}" if adapter else ""), file=sys.stderr, flush=True)
    return model, tokenizer


def generate(model, tokenizer, prompt: str, options: dict) -> tuple[str, int, int, str]:
    import torch

    inputs = tokenizer(prompt, return_tensors="pt").to(model.device)
    temperature = float(options.get("temperature", 0.0) or 0.0)
    max_new = int(options.get("num_predict") or 1024)
    stop = [s for s in (options.get("stop") or []) if s]

    sampling = dict(do_sample=True, temperature=temperature, top_p=float(options.get("top_p", 1.0))) \
        if temperature > 0 else dict(do_sample=False)

    with torch.no_grad():
        out = model.generate(
            **inputs, max_new_tokens=max_new, eos_token_id=tokenizer.eos_token_id,
            pad_token_id=tokenizer.eos_token_id, stop_strings=stop or None, tokenizer=tokenizer,
            **sampling,
        )

    new = out[0][inputs["input_ids"].shape[-1]:]
    text = tokenizer.decode(new, skip_special_tokens=True)

    for s in stop:   # stop strings are matched on tokens; cut the text exactly
        if s in text:
            text = text[: text.index(s)]

    reason = "length" if len(new) >= max_new else "stop"
    return text, int(inputs["input_ids"].shape[-1]), int(len(new)), reason


if __name__ == "__main__":
    raise SystemExit(main())
