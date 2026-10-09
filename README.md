# astral-decomposition

Draft, Sketch, Prove (Jiang et al. 2023) for Agda, on real library theorems.
Given a theorem in a file of an Agda project (agda-stdlib, agda-categories,
agda-algebras), the pipeline:

1. **Draft** – the model writes an informal proof as delineated `<STEP>`s,
   marking steps that deserve their own lemma.
2. **Sketch** – the model turns the draft into an Agda skeleton for the
   theorem: clauses with `{!!}` holes, each preceded by the informal step it
   came from, plus type signatures for any lemmas. The lemmas are
   *postulated* just above the theorem, in its own file, so the skeleton can
   be checked (`proof/layout.py`).
3. **Prove** – each hole is closed by the hammer (`core/hammer.py`): `refl`,
   then Agda's Mimer with the run's lemmas and the names the model used as
   hints, then the model. A stuck hole can be promoted to a lemma.
4. **Recurse** – every lemma the proof uses is proved by the same pipeline,
   in place. Success means the file typechecks with no holes and no
   postulates left.

The library's own proof of the theorem is taken apart (`util/deproof.py`)
and the run's decomposition is compared with it.

## Setup

```bash
python -m venv .venv && source .venv/bin/activate
pip install -e '.[claude,data,dev]'   # anthropic, pyarrow (datasets), pytest
pytest                                # parsers, layout, hole placement, and the whole
                                      # pipeline on a tiny fixture project with a scripted model
python code/cli/doctor.py --model claude-sonnet-5-5   # everything a library run needs
```

Needs Agda 2.8.0 as `agda` on `PATH`, with standard-library-2.3 (what
agda-categories and agda-algebras depend on) registered in its libraries
file (`~/.config/agda/libraries-2.8.0`). Claude models need
`ANTHROPIC_API_KEY`; Ollama models are expected at `localhost:11434`
(`--base-url` otherwise).

## Running

Everything is run from `code/`:

```bash
cd code
python cli/run_dsp.py ~/agda/data/agda-stdlib/src/Data/Nat/Properties.agda +-comm \
    --model claude-sonnet-5-5                    # one theorem
python cli/run_dsp_dataset.py ../samples/test24.json --model claude-sonnet-5-5 \
    --jobs 4 --tag mytag                         # a sample (see Datasets)
python cli/run_dsp.py --help                     # budgets, --no-draft, --place-holes, ...
```

The backend is picked from the model name (`claude*` → Anthropic, otherwise
Ollama). Defaults live in `core/config.py`. A run works in a symlink mirror
of the project (`util/checkout.py`): the theorem's file is a private copy,
cut after the theorem, and nothing is ever written into the project.

## Run logs

Every run writes `runs/<timestamp>_<model>[_<tag>]/`:

| file | contents |
|---|---|
| `meta.json` | model, backend, full CLI config, git commit + dirty flag, Agda version, host |
| `events.jsonl` | one JSON object per event, in order (see below) |
| `summary.json` | outcome, elapsed time, event and token counters |
| `result.json` | the decomposition the run found and its comparison with the library's (one theorem) |
| `final.agda` / `sketch.agda` | the finished proof, or the best sketch |

A dataset run writes `results.jsonl` (one record per theorem) and
`theorems/<NN>-<name>/` with each theorem's own events and files.

Every event has `seq`, `ts`, `t` (seconds since start), `kind`, and the active
scope (`target`, `depth`, `draft_index`). Kinds:

- `run_start` / `run_end`
- `llm_call` – stage (`draft`, `sketch`, `gap`, `lemma_signature`), full prompt,
  response text, model thinking (if any), token counts, duration, stop reason,
  or the error
- `agda_check` – mode (`sketch` = interaction load with holes, `plain` = final
  `agda` run), the exact source checked, result, goals, duration
- `draft`, `drafts_ready` – parsed steps or the parse failure
- `sketch_attempt` – accepted or rejected (`parse` / `signature` / `agda`),
  with the sketch, lemmas, and the file as checked; `sketch_repair`
- `prove_start`, `gap_start`, `gap_candidate` (every term tried, with Agda's
  verdict), `mimer`, `promote`, `gap_result`
- `lemma_start` / `lemma_end`, `lemma_unused`, `dsp_result` (per nested
  attempt, with the stage that failed)
- `decomposition` – every sketch and finished proof taken apart by
  `util/deproof.py`: its clauses, the steps of each clause, and the lemmas
  each step uses; `decomposition_compare` – the run lined up against the
  library's proof

Summarise runs with:

```bash
python cli/analyze_runs.py                  # one row per run
python cli/analyze_runs.py --dataset <tag>  # per theorem: lemma funnel, holes, repairs
python cli/analyze_runs.py --llm <run-id>   # every model call; --full adds prompts/responses
python cli/analyze_runs.py --events <run-id>
python cli/analyze_runs.py --decomposition <run-id>  # finished proofs as steps + lemmas
```

## Layout

- `code/core/` – `config`, `llm_client` (backends + stage prompts), `prompts`,
  `agda_client` (interaction protocol, Mimer), `hammer`, `run_log`, file and
  state helpers
- `code/proof/proof_sketch.py` – the DSP orchestration; `proof/layout.py`
  (the theorem's file and its lemma region), `proof/holes.py` (holes placed
  where an attempt fails)
- `code/util/agda_source.py` – reading declarations, clauses and
  `begin ... ∎` chains from Agda text (nested modules, multi-line
  signatures, `rewrite`/`with`, literate Markdown)
- `code/util/deproof.py` – takes a finished proof apart into its case split,
  equational steps and lemmas, and compares two decompositions of the same
  theorem. `code/util/sketch_export.py` (`--sketch {clause,step,lemma}`)
  turns a finished proof back into a holed sketch, checked by Agda
- `code/util/agda_data.py`, `code/util/checkout.py` – reading the
  astral-expmath datasets and working on a checkout through a symlink mirror
- `code/cli/` – `run_dsp.py`, `run_dsp_dataset.py`, `sample_dataset.py`,
  `analyze_runs.py`, `deproof_dataset.py`, `doctor.py`
- `code/tests/` – pytest suite; `tests/agda/` is its fixture project
- `samples/` – theorem samples for `run_dsp_dataset.py`
- `examples/` – harder targets, discussed in `decomp-examples.md`

## Datasets

The theorems come from the astral-expmath datasets built by
[astral-autoformalizer](https://github.com/kfish610/astral-autoformalizer):
`agda-decls` (every declaration of each pinned checkout, with the compiler's
ranges), `agda-informalize-stdlib` (stdlib lemmas and theorems with an
LLM-written informal statement and proof, written from the formal proof and
naming its lemmas) and `agda-autoformalize-context` (the autoformalize
fine-tune's train/eval/test prompts, over agda-stdlib, agda-categories and
agda-algebras; DSP runs sample its test split, which the fine-tune never saw).

```bash
hf download --repo-type dataset astral-expmath/agda-decls --local-dir ~/agda/data/hf/agda-decls
hf download --repo-type dataset astral-expmath/agda-informalize-stdlib --local-dir ~/agda/data/hf/agda-informalize-stdlib
hf download --repo-type dataset astral-expmath/agda-autoformalize-context --local-dir ~/agda/data/hf/agda-autoformalize-context
# each library at the commit the datasets pin (util/agda_data.py: PINNED), and stdlib v2.3
git -C ~/agda/data clone https://github.com/agda/agda-stdlib && git -C ~/agda/data/agda-stdlib checkout 47beb938489d1d9dd27c93c828a4e5e161acf758
```

Checkouts are found under `ASTRAL_CHECKOUTS` (default `~/agda/data`), one
directory per repo, and must be at the pinned commit; datasets under
`ASTRAL_DATASETS` (default `<checkouts>/hf`).

```bash
cd code
python cli/sample_dataset.py --out ../samples/test24.json   # 8 per repo, 4 of them chains
python util/deproof.py src/Data/Nat/Properties.agda +-comm \
    --checkout ~/agda/data/agda-stdlib --sketch step
python cli/deproof_dataset.py --informal <informalize parquet> --decls <decls parquet> \
    --sample 40 --jobs 3 --out deproof.jsonl
```

### What the pipeline does beyond the paper

- **Holes in a failed attempt** (`--place-holes`, `proof/holes.py`): a sketch
  that does not check is not thrown away. A `begin ... ∎` chain keeps its
  steps with its justifications holed, then the smallest piece around each
  Agda error becomes a hole. This is for a model that writes whole proofs
  rather than skeletons.
- **Repairs, not rejections**, each logged as `sketch_repair`: a declared
  lemma whose statement does not check is dropped, and a hole of function
  type gets its binders introduced by Agda (refine/intro).
- **Only used lemmas are proved**; unused ones are logged as `lemma_unused`.
  A stuck hole becomes a lemma stated from the hole's goal and context as
  written (not normalised, which unfolds into names the file never imported).
- **One Agda session per sketch**: candidates are given to the hole rather
  than reloading the file. A candidate that calls the function being proved
  is still checked by a reload, since a give skips the termination checker.
  `--jobs N` proves theorems in parallel.

## What the first runs showed (qwen3.5:4b, 2026-09-09)

These came from a toy setup (addition lemmas in a `Tests/` tree), since
removed in favour of library theorems.

- **Mimer needs hints and first-order lemmas.** Agda's `auto` uses a lemma only
  if its name is passed as a hint, and it cannot synthesise higher-order
  arguments such as `cong suc`. The toy context therefore carried a
  first-order `congSuc`; with it, hinted Mimer closes every addComm gap. Never
  hint the function being defined: Mimer already tries recursive calls, and
  the extra hint makes the search time out.
- **Mimer ignores termination.** Its first pick can be a non-structural
  recursive call. The hammer asks for the solution list (`-l`) and typechecks
  candidates in order.
- **Thinking mode.** With `--think`, one draft costs 80-100 s and ~10k tokens
  on the 4B model; stop sequences also fire inside the thinking stream, so
  they are disabled in that mode. With thinking off a draft costs 5-35 s, but
  the model deliberates inline instead, often until the token cap.
- **Sketch failure modes (small model):** proving the lemmas inline inside the
  target's sketch, inventing `with ... | sym ?_ ...`, and restating the goal
  as the "missing" lemma. The sketch stage drops foreign clauses, rejects
  forbidden syntax before Agda sees it, and both repairs are logged as
  `sketch_repair` / `sketch_attempt(reason=syntax)` events.
- **Holes must be equations, not functions.** A clause like `f (suc m) = {!!}`
  for a two-argument `f` leaves a Π-typed hole that Mimer does not close. The
  sketch stage used to reject those and ask for every argument to be bound;
  library proofs are often point-free, so Agda now introduces the binders
  (refine/intro) and only a hole that stays Π-typed is rejected
  (`sketch_attempt(reason=unbound_args)`).
- **The 4B model is not a gap filler.** Its direct hole-filling terms were
  never accepted; the successful run closed every hole with `refl`, hinted
  Mimer, or by promoting the hole to a lemma that was then proved recursively.
- The draft few-shot in `core/prompts.py` contains an addition-commutativity
  example, so addComm measures the sketch/prove machinery, not drafting.

## Placing holes: what we have learned (2026-10-09)

The question: where should the holes in a proof go, and should they be found
by working backwards from an existing proof or by prompting a model? Runs are
under `runs/`; the library sample is 24 theorems from the fine-tune's
held-out test split, 8 each from agda-stdlib, agda-categories and
agda-algebras (`cli/sample_dataset.py`, seed 11).

**What makes a good hole.** A hole should be one step whose both sides are
stated. Mimer's limit is unknown intermediate terms, not missing lemmas: it
fails a two-step equation even when given exactly the right lemmas, but
closes each step in under a second once the midpoint is written as a
`begin ... ∎` chain. `trans {!!} {!!}` is a badly placed hole:
the midpoint becomes an unsolved meta. Holes must also be writable in the
file: a goal that Agda prints with qualified names, or that mentions
variables the clause never binds, cannot be stated as a lemma there.

**Working backwards from a proof (analytic) works.** `util/deproof.py` takes
a finished proof apart into clauses, steps and the lemmas each step uses;
`util/sketch_export.py` turns it back into a sketch with holes at clause,
step or lemma granularity, and Agda checks the result. On stdlib, step
sketches were valid for 28/30 proofs of `Data.Nat.Properties` and 27/35 of a
random sample (lemma sketches 25/30 and 21/35), before later fixes; where a
finer hole cannot be written it falls back to a coarser one and says so.
Chains give the best holes, since the author has stated every midpoint and
only the justifications become holes. The catch is the data: most library
proofs are one step that applies other library lemmas (18 of the 24 sample
theorems; stdlib has only about 1,200 chains). In a library, the
decomposition is mostly *which lemmas a proof calls*, not steps inside it.
This is the method for producing hole-aware training data and for comparing
a run's decomposition with the library's (there is no ground truth in real
use, so the comparison matters).

**Asking a model to place holes does not work yet, with small models.**

- Chat models asked for skeletons (gemma4:12b, the original sketch prompt):
  11/24 sketches accepted, nearly all only after a repair; one hole per
  clause, never per step, even where the library proof had 2–3 steps; no
  lemma statement survived. Rejections were mostly malformed clause heads.
- Asking a model for a hole's whole term: 1/16 accepted. Asking it only for
  a chain's intermediate expressions and letting Mimer justify each step:
  6/12. Small models are better at stating intermediate facts than at
  writing the terms that justify them.
- The autoformalize fine-tune (astral-expmath/qwen3.5-4b-agda-autoformalize-context,
  the other team's model) cannot leave holes on purpose; it writes whole
  proofs.

**What works best: the model writes, the holes are placed analytically.**
The fine-tune writes a full proof attempt; where Agda rejects it,
`proof/holes.py` keeps what checks and places holes: a chain keeps its steps
with the justifications holed, then the smallest piece around each error
becomes a hole (parenthesised group, then pair component, then the clause's
right-hand side). Mimer, given the names the attempt used, closes what it
can; a stuck hole becomes a lemma stating its goal over the clause's
variables, proved one level down. With 3 samples per theorem this proved
11/24, 5 of them only through the placed holes. Most holes were still whole
clauses (36 clause, 20 chain-justification, 12 subterm).

**Does decomposing help the model? Not in this setup.** Same 24 theorems, 4
fine-tune attempts per theorem in each condition:

| Condition | Proved | Wall time | Model time |
|---|---|---|---|
| fine-tune + holes + Mimer, no draft | 8 | 5 min | 3 min |
| + draft shown as comments | 6 | 13 min | 22 min |
| full DSP: lemmas stated from a qwen3.5:4b draft | 8 | 14 min | 23 min |
| full DSP: lemmas stated from a gemma4:12b draft | 9 | 15 min | 26 min |

No proof used a drafted lemma, and the three proofs that seemed to go
through a promoted lemma were the theorem restated (that check is now
fixed). The likely reasons, in order:

1. **Little to decompose.** One-step library proofs need the right library
   lemma, not a new one; drafted lemmas mostly restated the theorem or a
   library fact.
2. **The fine-tune is not trained for DSP.** It learned to write a
   declaration from its file and an informal statement, not to follow a
   draft or use lemmas placed above the theorem, and extra context in its
   prompt made it slightly worse (8 → 6 with the draft as comments).
3. **This is not DSP's original setting.** DSP was built for competition
   mathematics in Isabelle, with multi-step proofs and a hammer
   (Sledgehammer) strong enough to close each step. Here the steps are
   library-sized and Mimer is weak.

So these runs do not show that decomposition is useless; they show it does
not help a model that never learned to use it, on theorems that barely need
it. To answer the question properly:

- run the formal side with a model that can follow a sketch (e.g. Sonnet
  5.5) to separate the method from the fine-tune;
- sample theorems whose library proof has several steps (deproof's step
  count, or chains) instead of one-step ones;
- give the fine-tune the lemmas the library proof actually uses, renamed,
  to test whether it can use a lemma at all;
- train on hole-aware data: deproof's sketches give, for real proofs, the
  holes, their goals and the lemmas behind them.

The fine-tune was dropped from the pipeline afterwards (2026-10-09): it is
trained for a different task (statement + file → declaration), and the
runs above show it gains nothing from DSP's structure. The code that drove
it (`proof/formalizer.py`) is in git history at commit a2cc8a6; the
ablation runs remain under `runs/*ablation-*`. The next experiment puts a
general model (Sonnet 5.5) at every stage, with and without the draft.
