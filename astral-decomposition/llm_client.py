import requests

from proof_state import LLMDeclResult, LLMHelperDeclResult


class OllamaClient:
    def __init__(
        self,
        model: str = "qwen2.5-coder:7b",
        base_url: str = "http://localhost:11434",
    ) -> None:
        self.model = model
        self.base_url = base_url.rstrip("/")

    def ask_for_direct_declaration(
        self,
        source: str,
        target_name: str,
        goal_type: str,
        previous_errors: list[str],
    ) -> str:
        """
        Ask for a direct proof and return only the parsed Agda declaration.

        This wrapper exists because proof_direct.py expects a raw declaration.
        """
        result = self.ask_for_declaration(
            source=source,
            target_name=target_name,
            goal_type=goal_type,
            previous_errors=previous_errors,
        )

        return result.declaration

    def ask_for_declaration(
        self,
        source: str,
        target_name: str,
        goal_type: str,
        previous_errors: list[str],
    ) -> LLMDeclResult:
        error_text = self._format_previous_errors(previous_errors)

        prompt = f"""
You are an Agda proof assistant agent.

You are completing this declaration:

{target_name}

Your task:
Return the full replacement declaration, including the original type signature and all implementation clauses.

Rules:
- The first line inside <AGDA_DECL> must start with exactly: {target_name} :
- Keep the original type signature exactly the same.
- Do not change the theorem or lemma type.
- Do not return helper lemmas.
- Do not return a different declaration.
- You may change only the implementation clauses of {target_name}.
- You may split into pattern-matching cases.
- Do not change any other declarations.
- Do not import new libraries.
- Use only definitions already available in the file.
- Put the full replacement declaration inside these tags:

<AGDA_DECL>
full_declaration_here
</AGDA_DECL>

Current Agda file:

{source}

Agda reported this goal:

{goal_type}
{error_text}

Now explain briefly, then give the replacement declaration.
"""

        full_response = self._generate(prompt, timeout=180).strip()
        declaration = extract_agda_declaration(full_response)

        return LLMDeclResult(
            declaration=declaration,
            full_response=full_response,
        )

    def ask_for_helpers_and_declaration(
        self,
        source: str,
        target_name: str,
        goal_type: str,
        previous_errors: list[str],
    ) -> LLMHelperDeclResult:
        error_text = self._format_previous_errors(previous_errors)

        prompt = f"""
You are an Agda decomposition agent.

You are given:
1. The full Agda file.
2. The target declaration name.
3. The goal type of a hard hole.

Your task:
Propose helper lemma signatures and then prove the target declaration using those helpers.

The helper lemmas will be inserted into Tests.Helpers as postulates.
So in <AGDA_HELPERS>, write only helper lemma signatures.
Do not include implementations there.
Do not write the word postulate.

Then in <AGDA_DECL>, write the full replacement declaration for the target.
IMPORTANT: use suc instead of S. For example, if you want to prove a base case, you can write a pattern match for zero and then use "suc n" in the inductive case.

Rules for <AGDA_HELPERS>:
- Write only type signatures.
- Do not include proofs.
- Do not include postulate.
- Do not include helper names that already exist in the file.
- Helpers will be placed in Tests.Helpers, which imports Tests.Context.
- Therefore helper signatures may refer to names available from Tests.Context.
- Do not refer to names declared only in Tests.Target.
- Prefer small reusable lemmas.

Rules for <AGDA_DECL>:
- The first line must start with exactly: {target_name} :
- Keep the original type signature exactly the same.
- You may change only the implementation clauses.
- You may use the helper lemmas from <AGDA_HELPERS>.
- Do not change other declarations.
- Do not import new libraries.

Output format:

<AGDA_HELPERS>
helperLemma1 : ...
helperLemma2 : ...
</AGDA_HELPERS>

<AGDA_DECL>
{target_name} : original_type_here
{target_name} ... = ...
</AGDA_DECL>

Current Agda file:

{source}

Hard goal type:

{goal_type}
{error_text}

Now explain briefly, then give both blocks.
"""

        full_response = self._generate(prompt, timeout=180).strip()

        helpers = extract_agda_helpers(full_response)
        declaration = extract_agda_declaration(full_response)

        return LLMHelperDeclResult(
            helpers=helpers,
            declaration=declaration,
            full_response=full_response,
        )

    def _format_previous_errors(self, previous_errors: list[str]) -> str:
        if not previous_errors:
            return ""

        error_text = "\nPrevious failed attempts and Agda errors:\n"

        for i, err in enumerate(previous_errors, start=1):
            error_text += f"\nAttempt {i} failed:\n{err}\n"

        return error_text

    def _generate(self, prompt: str, timeout: int) -> str:
        response = requests.post(
            f"{self.base_url}/api/generate",
            json={
                "model": self.model,
                "prompt": prompt,
                "stream": False,
            },
            timeout=timeout,
        )

        if response.status_code != 200:
            print("Ollama error:")
            print(response.status_code)
            print(response.text)
            response.raise_for_status()

        return response.json()["response"]


def extract_agda_declaration(text: str) -> str:
    tagged = extract_between_tags(text, "AGDA_DECL")

    if tagged is not None:
        return tagged.strip()

    cleaned = strip_markdown_code_fences(text).strip()

    if not cleaned:
        raise ValueError("Could not extract Agda declaration from empty response.")

    return cleaned


def extract_agda_helpers(text: str) -> str:
    tagged = extract_between_tags(text, "AGDA_HELPERS")

    if tagged is None:
        raise ValueError("Could not find <AGDA_HELPERS>...</AGDA_HELPERS> block.")

    return tagged.strip()


def extract_between_tags(text: str, tag: str) -> str | None:
    start_tag = f"<{tag}>"
    end_tag = f"</{tag}>"

    start = text.find(start_tag)
    end = text.find(end_tag)

    if start == -1 or end == -1:
        return None

    if end < start:
        return None

    start += len(start_tag)

    return text[start:end]


def strip_markdown_code_fences(text: str) -> str:
    lines = text.strip().splitlines()

    if not lines:
        return ""

    if lines[0].strip().startswith("```"):
        lines = lines[1:]

    if lines and lines[-1].strip().startswith("```"):
        lines = lines[:-1]

    return "\n".join(lines)