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

- try harder proofs by hiding lemmas.
