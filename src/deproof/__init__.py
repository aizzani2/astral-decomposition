"""
deproof: take a finished Agda proof apart into the decomposition it implies,
turn it back into checked sketches with holes, and compare decompositions.

    decompose.py      the proof's clauses, steps and lemmas (`decompose`)
    decomposition.py  what a decomposition is (`Decomposition`, `render`)
    comparison.py     lining up two decompositions of a theorem (`compare`)
    sketch_export.py  the proof back as a sketch, at clause, step or lemma
                      granularity, checked by Agda (`export_sketch`)
    __main__.py       `python -m deproof FILE NAME`: a report for one proof
    dataset.py        `python -m deproof.dataset`: over the astral-expmath datasets

The DSP pipeline uses it to log the decomposition of every sketch and proof
and to compare a run with the library's proof.
"""
