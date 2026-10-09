import os
from pathlib import Path

# ---------------------------------------------------------------------------
# Models
# ---------------------------------------------------------------------------

# Ollama model tag, or an Anthropic model id (anything starting with "claude").
DEFAULT_MODEL = "qwen3.5:4b"

# "auto" picks the Anthropic backend for models named claude*, Ollama otherwise.
DEFAULT_BACKEND = "auto"

OLLAMA_BASE_URL = "http://localhost:11434"
LLM_TIMEOUT_SECONDS = 600

# qwen3.5 is a thinking model. With thinking on, one draft took ~90s and ~10k
# tokens on a 4B model and the model tended to keep "thinking" inside the
# answer; with it off, ~7s. Keep it switchable so the two can be compared.
OLLAMA_THINK = False
# With thinking on, only these stages think. The short, term-level stages
# (gap, lemma_signature) otherwise spend the whole token budget deliberating
# and return empty text (observed: 15.8k thinking tokens, 140 s, no answer).
OLLAMA_THINK_STAGES = frozenset({"draft", "sketch"})
OLLAMA_NUM_CTX = 16384          # ollama's default (4096) truncates our prompts
OLLAMA_NUM_PREDICT = 4096       # hard cap on generated tokens per call
OLLAMA_NUM_PREDICT_THINKING = 16384
OLLAMA_TEMPERATURE = 0.6
OLLAMA_TOP_P = 0.95

# Anthropic (Claude). Thinking is adaptive; effort is the knob.
ANTHROPIC_DEFAULT_MODEL = "claude-sonnet-5-5"
ANTHROPIC_EFFORT = "high"
ANTHROPIC_MAX_TOKENS = 16000

# ---------------------------------------------------------------------------
# Search budget
# ---------------------------------------------------------------------------

# DSP pipeline
DRAFT_SAMPLES = 4  # informal proofs sampled per problem
SKETCH_MAX_ATTEMPTS = 3  # sketches tried per draft
GAP_LLM_ATTEMPTS = 2  # model attempts per hole, after tactics and Mimer
MAX_DEPTH = 3  # recursion depth for lemmas

# The paper's budget finding (Figure 5, right): with a fixed number of
# autoformalization attempts, spending them on more *drafts* beats spending
# them on more sketches per draft. Raise DRAFT_SAMPLES before SKETCH_MAX_ATTEMPTS.

# ---------------------------------------------------------------------------
# Agda
# ---------------------------------------------------------------------------

# Agda 2.8.0, as `agda` on PATH. A checkout's library dependencies
# (standard-library-2.3 for agda-categories and agda-algebras) must be
# registered in Agda's libraries file; cli/doctor.py checks.
AGDA_TIMEOUT_SECONDS = 30

# Mimer (Agda's `auto`) is our Sledgehammer. It only uses lemmas it is given
# as hints. Seconds.
MIMER_TIMEOUT_SECONDS = 5
# Offered to Mimer on every hole besides the run's lemmas and the names the
# model used. A name not in scope in the file is dropped when Agda rejects it.
MIMER_BASE_HINTS = ("sym", "trans", "cong")

PROJECT_ROOT = Path(__file__).resolve().parents[2]

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

RUNS_ROOT = PROJECT_ROOT / "runs"

# ---------------------------------------------------------------------------
# Library data (the astral-expmath datasets and the checkouts they pin)
# ---------------------------------------------------------------------------

# One checkout per source repo, named after it (agda/agda-stdlib -> agda-stdlib),
# each at the commit the datasets pin; see util/agda_data.py and cli/doctor.py.
CHECKOUTS_ROOT = Path(os.environ.get("ASTRAL_CHECKOUTS", PROJECT_ROOT.parent / "data"))
# Downloaded datasets (hf download --local-dir <here>/<name>).
DATASETS_ROOT = Path(os.environ.get("ASTRAL_DATASETS", CHECKOUTS_ROOT / "hf"))
