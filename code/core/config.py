DEFAULT_MODEL = "qwen2.5-coder:7b"  # TODO: replace me!

# Legacy single-shot pipeline
DIRECT_MAX_ATTEMPTS = 3
SINGLE_MAX_ATTEMPTS = 3
HELPER_MAX_ATTEMPTS = 5

# DSP pipeline
DRAFT_SAMPLES = 1  # informal proofs sampled per problem
SKETCH_MAX_ATTEMPTS = 3  # sketches tried per draft
GAP_LLM_ATTEMPTS = 2  # model attempts per hole, after tactics and Mimer
MAX_DEPTH = 3  # recursion depth for lemmas

# The paper's budget finding (Figure 5, right): with a fixed number of
# autoformalization attempts, spending them on more *drafts* beats spending
# them on more sketches per draft. Raise DRAFT_SAMPLES before SKETCH_MAX_ATTEMPTS.

AGDA_ERROR_MAX_CHARS = 4000
AGDA_TIMEOUT_SECONDS = 120
AGDA_IMPORT_PATH = "agda_files"

OLLAMA_BASE_URL = "http://localhost:11434"
LLM_TIMEOUT_SECONDS = 180
