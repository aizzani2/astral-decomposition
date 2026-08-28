"""
Prompt templates for the Draft / Sketch / Prove pipeline.

Kept out of llm_client.py so that prompts can be edited, versioned and
ablated without touching transport code. The DSP paper's ablations show the
two things that matter most here:

  1. drafting an informal proof first (worth ~4-5% absolute), and
  2. copying informal segments into the sketch as in-line comments
     (worth ~3-5% absolute).

So every sketch example below annotates each formal block with the informal
sentence it came from, and every hole is preceded by that comment.
"""

# ---------------------------------------------------------------------------
# Stage 1: DRAFT
# ---------------------------------------------------------------------------

DRAFT_SYSTEM = """\
You are a mathematician writing informal proofs that will later be formalised
in Agda by another agent. Write in ordinary mathematical English. Do not write
Agda. Do not skip steps by saying "clearly" or "trivially".
"""

DRAFT_FEW_SHOT = """\
### Example 1

Informal statement:
For every natural number n, n + 0 = n.

Formal statement (Agda, for reference only):
+-identityr : (n : Nat) -> n + 0 == n

<INFORMAL_PROOF>
<STEP index="1" kind="induction">
We argue by induction on n.
</STEP>
<STEP index="2" kind="case">
Base case: when n is zero, 0 + 0 reduces to 0, so the two sides are equal.
</STEP>
<STEP index="3" kind="case">
Inductive case: suppose n + 0 = n. Then (suc n) + 0 reduces to suc (n + 0),
and rewriting with the induction hypothesis turns this into suc n.
</STEP>
</INFORMAL_PROOF>

### Example 2

Informal statement:
For all natural numbers m and n, m + suc n = suc (m + n).

Formal statement (Agda, for reference only):
+-suc : (m n : Nat) -> m + suc n == suc (m + n)

<INFORMAL_PROOF>
<STEP index="1" kind="induction">
We argue by induction on m, holding n fixed.
</STEP>
<STEP index="2" kind="case">
Base case: 0 + suc n reduces to suc n, and suc (0 + n) also reduces to suc n.
</STEP>
<STEP index="3" kind="case">
Inductive case: assume m + suc n = suc (m + n). Then (suc m) + suc n reduces
to suc (m + suc n), which by the induction hypothesis equals suc (suc (m + n)),
which is suc ((suc m) + n).
</STEP>
</INFORMAL_PROOF>

### Example 3

Informal statement:
Addition of natural numbers is commutative: m + n = n + m.

Formal statement (Agda, for reference only):
+-comm : (m n : Nat) -> m + n == n + m

<INFORMAL_PROOF>
<STEP index="1" kind="lemma" name="plusZeroRight">
First we need that n + 0 = n for every n; this is a separate induction and we
record it as its own lemma.
</STEP>
<STEP index="2" kind="lemma" name="plusSucRight">
We also need that m + suc n = suc (m + n) for all m and n; again a separate
induction, recorded as its own lemma.
</STEP>
<STEP index="3" kind="induction">
Now argue by induction on m.
</STEP>
<STEP index="4" kind="case">
Base case: 0 + n reduces to n, and n + 0 equals n by the first lemma.
</STEP>
<STEP index="5" kind="case">
Inductive case: assume m + n = n + m. Then suc m + n reduces to suc (m + n),
which by the hypothesis is suc (n + m), which by the second lemma is n + suc m.
</STEP>
</INFORMAL_PROOF>
"""

DRAFT_TEMPLATE = """\
{system}

Follow the format of these examples exactly.

{few_shot}

### Now your turn

Informal statement:
{informal_statement}

Formal statement (Agda, for reference only):
{formal_signature}

{extra_context}
Rules:
- Output exactly one <INFORMAL_PROOF> block and nothing else after it.
- Each <STEP> gets an index, and a kind from: step, case, induction, lemma.
- Use kind="lemma" with a name="..." attribute for any step that deserves its
  own standalone proof. Prefer this for anything needing its own induction.
- Keep each step to one idea. Small steps are easier to formalise than big ones.
- Do not write Agda code inside the steps.

<INFORMAL_PROOF>
"""


# ---------------------------------------------------------------------------
# Stage 2: SKETCH
# ---------------------------------------------------------------------------

SKETCH_SYSTEM = """\
You are an Agda autoformalizer. You turn an informal proof into a formal proof
SKETCH: a skeleton that has the right structure and leaves the hard parts as
holes for an automated prover to close later.
"""

SKETCH_FEW_SHOT = """\
### Example 1

Informal proof:
1. [induction] We argue by induction on n.
2. [case] Base case: 0 + 0 reduces to 0.
3. [case] Inductive case: rewriting with the induction hypothesis gives suc n.

Target signature:
+-identityr : (n : Nat) -> n + 0 == n

<AGDA_LEMMAS>
</AGDA_LEMMAS>

<AGDA_SKETCH>
+-identityr : (n : Nat) -> n + 0 == n
-- Base case: 0 + 0 reduces to 0.
+-identityr zero = {!!}
-- Inductive case: rewrite with the induction hypothesis.
+-identityr (suc n) = {!!}
</AGDA_SKETCH>

### Example 2

Informal proof:
1. [lemma:plusZeroRight] We need n + 0 = n.
2. [lemma:plusSucRight] We need m + suc n = suc (m + n).
3. [induction] Induct on m.
4. [case] Base case: 0 + n is n, and n + 0 is n by the first lemma.
5. [case] Inductive case: chain the hypothesis and the second lemma.

Target signature:
+-comm : (m n : Nat) -> m + n == n + m

<AGDA_LEMMAS>
plusZeroRight : (n : Nat) -> n + 0 == n
plusSucRight : (m n : Nat) -> m + suc n == suc (m + n)
</AGDA_LEMMAS>

<AGDA_SKETCH>
+-comm : (m n : Nat) -> m + n == n + m
-- Base case: 0 + n is n, and n + 0 is n by plusZeroRight.
+-comm zero n = {!!}
-- Inductive case: chain the induction hypothesis with plusSucRight.
+-comm (suc m) n = {!!}
</AGDA_SKETCH>
"""

SKETCH_TEMPLATE = """\
{system}

Follow the format of these examples exactly.

{few_shot}

### Now your turn

Informal proof (each line is one step you should mirror in the sketch):
{informal_proof}

Target signature (copy this line verbatim as the first line of the sketch):
{signature}

Names already available from the imports:
{available_names}

Current file (for context; you are replacing only {target_name}):
{source}
{error_text}
Rules for <AGDA_LEMMAS>:
- One type signature per line, no implementations, no `postulate` keyword.
- Only for steps marked as lemmas, or steps that need their own induction.
- These are placed in {helpers_module}, which imports {context_module} only.
  So they may not mention names declared in the target file.
- Emit an empty block if the sketch needs no lemmas.

Rules for <AGDA_SKETCH>:
- The first line must be exactly: {signature}
- Write the clause structure (pattern matches, `with`, `where`, equational
  reasoning chains) but leave every non-obvious term as a hole: {{!!}}
- Precede each hole with an Agda comment quoting the informal step it comes
  from. This alignment matters; do not drop it.
- Prefer many small holes over one big hole. An automated prover will try to
  close each hole independently.
- Use `suc n`, never `S n`.
- You may use the lemma names you declared in <AGDA_LEMMAS>.
- Do not add imports. Do not redefine anything else in the file.

<AGDA_LEMMAS>
"""


# ---------------------------------------------------------------------------
# Stage 3: PROVE (per-hole gap filling)
# ---------------------------------------------------------------------------

GAP_TEMPLATE = """\
You are closing a single hole in an Agda proof.

Return ONLY the term that replaces the hole. No type signature, no clause,
no surrounding definition, no explanation outside the tags.

The hole's goal type is:
{goal_type}

The variables in scope at the hole are:
{context}

The informal step this hole corresponds to:
{informal_hint}

Names available from the imports and the rest of the file:
{available_names}

Surrounding code (the hole is marked HERE):
{excerpt}
{error_text}
Rules:
- The term must have exactly the goal type shown above.
- Use only the variables listed in scope, plus imported names.
- If the term needs parentheses to sit inside a clause body, include them.
- Do not introduce new holes. Do not write {{!!}}.
- Do not write `postulate` and do not invent lemma names that do not exist.

<AGDA_TERM>
"""


# ---------------------------------------------------------------------------
# Lemma signature abstraction (used when a hole is promoted to a lemma)
# ---------------------------------------------------------------------------

LEMMA_FROM_GAP_TEMPLATE = """\
You are turning a stuck Agda goal into a standalone lemma.

Goal type at the hole:
{goal_type}

Variables in scope at the hole:
{context}

Write a single top-level Agda type signature named {lemma_name} that:
- quantifies over exactly the in-scope variables the goal type actually needs,
- has the goal type as its conclusion,
- mentions only names available from {context_module} (not from the target file),
- is written on one line.

Output only the signature inside the tags.

<AGDA_SIG>
{lemma_name} : \
"""
