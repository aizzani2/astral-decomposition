import os
import shlex
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
ANTHROPIC_DEFAULT_MODEL = "claude-sonnet-5"
ANTHROPIC_EFFORT = "high"
ANTHROPIC_MAX_TOKENS = 16000

# ---------------------------------------------------------------------------
# Search budget
# ---------------------------------------------------------------------------

# Legacy single-shot pipeline
DIRECT_MAX_ATTEMPTS = 3
SINGLE_MAX_ATTEMPTS = 3
HELPER_MAX_ATTEMPTS = 5

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

# The Agda binary. The datasets' stdlib snapshot needs Agda 2.8.0 while the
# system Agda is 2.6.4.3, so point this at another build (e.g.
# AGDA_BIN=/home/jamie/agda/tools/agda-2.8.0/agda) rather than replacing it.
AGDA_BIN = os.environ.get("AGDA_BIN", "agda")

# Extra flags for every Agda invocation. A library checkout wants
# `--no-default-libraries`: ~/.config/agda/defaults names a stdlib installed
# for the system Agda, which another Agda version then fails to find.
AGDA_FLAGS: list[str] = shlex.split(os.environ.get("AGDA_FLAGS", ""))

AGDA_ERROR_MAX_CHARS = 4000
AGDA_TIMEOUT_SECONDS = 30

# Mimer (Agda's `auto`) is our Sledgehammer. It only uses lemmas it is given
# as hints, so the hammer passes it every name in scope. Seconds.
MIMER_TIMEOUT_SECONDS = 5

PROJECT_ROOT = Path(__file__).resolve().parents[2]
AGDA_ROOT = PROJECT_ROOT / "agda_files"
AGDA_IMPORT_PATH = str(AGDA_ROOT)

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
# Agda library file listing each library's .agda-lib: agda-categories and
# agda-algebras depend on standard-library-2.3.
AGDA_LIBRARY_FILE = Path(os.environ.get("AGDA_LIBRARY_FILE", CHECKOUTS_ROOT / "libraries-2.8.0"))

# The autoformalize fine-tune, served by Ollama (see README).
FORMALIZER_MODEL = os.environ.get(
    "FORMALIZER_MODEL", "hf.co/astral-expmath/qwen3.5-4b-agda-autoformalize-context-GGUF:Q8_0"
)
FORMALIZER_URL = os.environ.get("FORMALIZER_URL", "http://localhost:11436")
