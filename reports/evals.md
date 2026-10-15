# Evaluation results

Proofs found out of 24 library theorems (8 each from agda-stdlib,
agda-categories, agda-algebras). Run logs are in `runs/`.

## Held-out sample (`samples/heldout24.json`)

Theorems held out from both fine-tunes' training data. 4 proof attempts per
theorem; holes placed where an attempt fails; Mimer (and, for chat models,
the model, 3 tries) closes holes; stuck holes become lemmas.

| Model | Drafting | Proved | Via a lemma | Model time |
|---|---|---|---|---|
| Haiku 5.5 | yes (DSP) | **12** | 4 | 79 min |
| Haiku 5.5 | no | **12** | 0 | 34 min |
| Haiku plans, Qwen 4B raw CPT proves | yes | 11 | 0 | 91 min |
| Qwen 4B raw CPT (sees the file) | no | 11 | 0 | 14 min |
| Qwen 4B pairs-delim | no | 8 | 0 | 11 min |
| OLMo 7B pairs-delim | no | 2 | 0 | 19 min |

Proved by at least one run: 16 / 24.

The Haiku runs are after the prove-stage fixes (hole prompt shows the
file's imports, 3 tries per hole with Agda's error, exact-goal lemma
fallback). Before them, Haiku with drafting proved 3 of 16.

## Hidden lemmas (`samples/hidden24.json`)

24 theorems whose library proof rests on lemmas defined earlier in the same
file, at least two levels deep. Level 0 hides nothing; level 1 removes the
lemmas the proof uses directly; level 2 also removes the lemmas those use.
"Recovered" counts hidden lemmas the run stated again (same statement up to
binder names and symmetry).

| Prover | Level 0 | Level 1 | Level 2 |
|---|---|---|---|
| Haiku 5.5, no drafting | 16 | 3 | 3 |
| Haiku 5.5, drafting (DSP) | – | **10** (7 via lemmas) | **6** (3 via lemmas) |
| Qwen 4B raw CPT | 6 | 0 | 0 |
| Qwen 4B raw CPT, qwen3.5:4b drafting | 8 | 0 | 0 |

| | Level 1 | Level 2 |
|---|---|---|
| Hidden lemmas recovered, Haiku DSP | 4 / 32 | 2 / 68 |
| Hidden lemmas recovered, others | 0–1 / 32 | 0 / 68 |
| Haiku model time: no drafting / drafting | 52 / 172 min | 47 / 188 min |

- Without its lemmas, a theorem becomes much harder: Haiku without drafting
  drops from 16 to 3, Qwen to 0.
- Drafting recovers much of that for Haiku (3 → 10 at level 1), mostly
  through lemmas it states and proves itself. Some restate the hidden lemma
  (`toℕ-fromℕ`, `*-zeroˡ`, `*-zeroʳ`, `∨-idem`); others decompose
  differently (`H-id1` via a new `liftEnv` lemma).
- Recovered lemmas carry the library's own names, so Haiku likely knows
  stdlib; recovery on agda-categories and agda-algebras is the cleaner signal.
- Small-model drafting (qwen3.5:4b) does not help the Qwen prover.

## Ablation (`samples/test24.json`)

Prover: the qwen3.5-4b autoformalize-context fine-tune. 4 attempts per theorem.

| Setup | Proved |
|---|---|
| No draft | 8 |
| Draft shown as comments | 6 |
| DSP, lemmas from a qwen3.5:4b draft | 8 |
| DSP, lemmas from a gemma4:12b draft | 9 |

## Notes

- Drafting does not change Haiku's count (12 vs 12) but changes how it
  proves: 4 of its proofs go through lemmas (`*+-is-fold`, `<-respects₂`,
  `merge₂ˡ`, `Radjunct-resp-≈`), the first decomposed proofs in any run.
  It proves 2 theorems the no-draft run does not, and misses 2 it proves,
  at 2.3x the model time.
- Haiku's planned lemmas did not help the Qwen prover: same count as Qwen alone.
- The two samples are different, so their numbers are not comparable.
- 24 theorems is small: differences of 2–3 are within noise.

- try harder proofs by hiding lemmas: done, see "Hidden lemmas" above.
