# astral-decomposition

Draft, Sketch, Prove (Jiang et al. 2023) for Agda, on theorems from
agda-stdlib, agda-categories and agda-algebras.

1. **Draft**: the model writes an informal proof as numbered steps, marking
   steps that deserve their own lemma.
2. **Sketch**: the model writes the theorem's clauses with `{!!}` holes and
   signatures for its lemmas. The lemmas are postulated above the theorem in
   its own file so the sketch can be checked.
3. **Prove**: each hole is closed by `refl`, Agda's Mimer, or the model. A
   hole nothing closes becomes a lemma.
4. **Recurse**: each lemma the proof uses is proved the same way. A theorem
   is proved when its file checks with no holes and no postulates.

Each run is compared with the library's own proof, taken apart by `deproof`.

## Setup

```bash
python -m venv .venv && source .venv/bin/activate
pip install -e '.[claude,data,dev]'      # add ,serve for tools/serve_hf.py
pytest
python -m cli.doctor --model claude-haiku-5-5
```

Needs Agda 2.8.0 as `agda`, with standard-library-2.3 registered in
`~/.config/agda/libraries-2.8.0` (agda-categories and agda-algebras depend
on it). Claude models use `ANTHROPIC_API_KEY` if set, otherwise the
signed-in Claude Code plan. Ollama models are expected at `localhost:11434`
(`--base-url`). Hugging Face models and LoRA adapters are served locally by
`tools/serve_hf.py`.

## Running

From the repository root:

```bash
python -m cli.run_dsp ~/agda/data/agda-stdlib/src/Data/Nat/Properties.agda +-comm \
    --model claude-haiku-5-5
python -m cli.run_dsp_dataset samples/heldout24.json --model claude-haiku-5-5 --jobs 2 --tag mytag
python -m cli.analyze_runs --dataset mytag
```

Options worth knowing (`--help` lists all):

- `--no-draft`, `--draft-samples`, `--sketch-max-attempts`, `--gap-llm-attempts`, `--max-depth`
- `--format chat|definition|continuation`: how the model is prompted for a
  proof (the sketch prompt; a pairs-delim `<signature>…<definition>`; the
  file up to the signature, for a raw-Agda model)
- `--planner MODEL`: a chat model drafts, states lemmas and fills holes
  while `--model` writes the proofs
- `--place-holes`: keep a sketch that fails to check, with holes where it fails
- `--state-lemmas`: a stuck hole's lemma states its exact goal
- `--level k`: on a hidden-lemma sample, remove the theorem's lemmas to depth k

A run works in a symlink mirror of the library checkout, so nothing is
written into the checkout.

## Layout

- `src/core/`: config, model backends and prompts, the Agda interaction
  client, the hammer, run logging, Agda source parsing
- `src/proof/`: the pipeline (`proof_sketch.py`), the theorem's file and its
  lemma region (`layout.py`), hole placement in failed attempts (`holes.py`)
- `src/deproof/`: takes a finished proof apart into clauses, steps and
  lemmas; compares two decompositions; turns a proof back into a checked
  sketch; builds the tree of same-file lemmas behind a proof
- `src/data/`: the datasets and checkout mirroring
- `src/cli/`: run, sample, analyze and doctor commands
- `tools/serve_hf.py`: a model or LoRA adapter behind Ollama's API
- `tests/`: pytest suite, with a fixture Agda project in `tests/agda/`
- `samples/`, `runs/`, `reports/`: theorem samples, run logs, results

## Data

Theorems come from the astral-expmath datasets built by
[astral-autoformalizer](https://github.com/kfish610/astral-autoformalizer):
`agda-decls` (every declaration with its source range),
`agda-autoformalize-context` (train/eval/test prompts; samples are drawn from
its test split) and `agda-informalize-stdlib`.

```bash
hf download --repo-type dataset astral-expmath/agda-decls --local-dir ~/agda/data/hf/agda-decls
hf download --repo-type dataset astral-expmath/agda-autoformalize-context --local-dir ~/agda/data/hf/agda-autoformalize-context
git -C ~/agda/data clone https://github.com/agda/agda-stdlib   # check out the commit in data/agda_data.py
```

Each library is cloned under `ASTRAL_CHECKOUTS` (default `~/agda/data`) at
the commit the datasets pin. Datasets go under `ASTRAL_DATASETS` (default
`<checkouts>/hf`).

Samples:

```bash
python -m cli.sample_dataset --out samples/test24.json
python -m cli.sample_dataset --held-out-in agda-pairs-delim --out samples/heldout24.json
python -m cli.sample_hidden --n 24 --depth 2 --out samples/hidden24.json
```

`sample_hidden` picks theorems whose proof rests on same-file lemmas at least
two deep. For each depth k it records the lines to remove: those lemmas, and
whatever between them and the theorem uses them. Each level is checked to
load with the theorem as a hole and to leave the hidden names out of scope.
A run with `--level k` records which hidden lemmas it stated again.

deproof on its own:

```bash
python -m deproof src/Data/Nat/Properties.agda +-comm --checkout ~/agda/data/agda-stdlib
python -m deproof.tree src/Data/Nat/Properties.agda +-comm --checkout ~/agda/data/agda-stdlib
```

Reports go to `reports/deproof/<library>/<file>/<name>.agda`.

## Run logs

Each run writes `runs/<timestamp>_<model>_<tag>/`: `meta.json` (config,
git commit, Agda version), `events.jsonl` (every model call and Agda check),
`summary.json`, and, for a sample, `results.jsonl` with one record per
theorem and `theorems/<NN>-<name>/` holding that theorem's events and its
`final.agda` or best `sketch.agda`.

## Results

See `reports/evals.md`. In short:

- Holes placed where a model's proof fails, closed by Mimer, account for a
  large share of proofs.
- Most library proofs are one step that applies an existing lemma, so there
  is little to decompose. `--level` removes those lemmas to make
  decomposition necessary.
- Haiku with drafting proves as many theorems as without (12/24), but 4 of
  its proofs go through lemmas it stated, which is the first evidence of
  decomposition at work.
- A model that sees the theorem's file (raw CPT Qwen, 11/24) beats ones
  that see only the signature.
