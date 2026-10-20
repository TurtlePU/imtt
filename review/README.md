# Prose review, 20 October 2026

The reviewed base is `bcbf7d5f8719ee93e7212ee6967bd1c8c201402c`.
The scope is `latex/main.tex` and its seven `\input` files. There is no
separate includes directory in this revision.

[MINOR_CORRECTIONS.md](../MINOR_CORRECTIONS.md) records all 68 changed
source lines. [WORDING_SUGGESTIONS.md](../WORDING_SUGGESTIONS.md) contains
27 optional, unapplied proposals in the saved checkbox/CriticMarkup format.
Rejecting each passage's CriticMarkup reproduces its corrected source
excerpt exactly. Original source line breaks and line numbers are retained.

## Services and coverage

The saved MLTT-S prose-review workflow was used with the official Grazie
extension's Text Playground and the free DeepL Write website, set to
English (British). No paid API, AI chat/rewrite upgrade, direct authenticated
endpoint call, or credential extraction was used.

DeepL returned results for all **184 prepared blocks**. Grazie returned
complete, exact-input-matched cloud responses for **165**; **19 remain
unverified**. All prepared blocks were attempted. Absence of a complete
response is not a clean result. [COVERAGE.json](COVERAGE.json) identifies
each block and records original and corrected source hashes.

The preparation was adapted for plain LaTeX: indented prose, abstracts,
definitions, proofs and list items were included. Math, code, macro
arguments, headings and figure environments were protected or excluded.
TeX quotation marks and nonbreaking spaces were shielded from the
Markdown-aware extension. This is a review of the extracted prose, not a
claim that every visible word in the typeset paper was checked by both
services. Incomplete/cached Grazie responses and missing or altered DeepL
placeholders are recorded as gaps or rejected evidence.

## Filtering and editorial decisions

Both providers passed through the same saved renderer, protected-name
inventory and technical glossary. Proper names were inventoried from the
authors, prose and bibliography; mathematical vocabulary was inventoried
from definitions and theorem/proof prose. Retained replacements were then
inspected individually. Oxford spelling and technical capitalization and
hyphenation variants were preserved.

[AUDIT.json](AUDIT.json) retains record identifiers, provider attribution,
filter decisions, contextual exclusions and both inventories. Raw requests,
responses and browser state are not included in the commit. Suggestions
that changed mathematics, names or protected markers were discarded;
incorrect or grammatically disconnected rewrites were also discarded.
Identical independent proposals are deduplicated without inventing shared
provider support. Distinct alternatives retain their own attribution.

Minor corrections were applied only after sentence-level review. Contextual
corrections are distinguished from exact provider agreement in the applied
corrections report. Optional rewrites remain unapplied. Proposals touching
an already corrected span were omitted rather than partially reconstructed;
disjoint proposals were aligned to the corrected sources and revalidated.

## Validation

Baseline and corrected builds used isolated copies of `latex/` with TeX
Live 2026. In each copy, the full successful sequence was:

```sh
LC_ALL=en_US.UTF-8 LANG=en_US.UTF-8 lualatex --shell-escape -interaction=nonstopmode -halt-on-error main.tex
LC_ALL=en_US.UTF-8 LANG=en_US.UTF-8 biber main
LC_ALL=en_US.UTF-8 LANG=en_US.UTF-8 lualatex --shell-escape -interaction=nonstopmode -halt-on-error main.tex
LC_ALL=en_US.UTF-8 LANG=en_US.UTF-8 lualatex --shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

All commands exited 0. After the last text-only corrections, one additional
LuaLaTeX pass also exited 0. Both PDFs have 28 pages. The final warnings
match the baseline: a FontAwesome italic substitution and three overfull
boxes (9.97194 pt, 6.31786 pt and 1.8722 pt). There are no final undefined
reference/citation or missing-character warnings. Pages 1, 11, 19, 20 and
23 were rendered with PDFKit and visually inspected.

Read-only comparisons against the base passed for all eight sources:
inline/display mathematics, math/BNF environments, citation/reference keys,
labels, inputs, TeX control sequences and source line counts are unchanged.
The bibliography and Agda sources are unchanged. CriticMarkup rejection,
source excerpt alignment, nonempty accepted alternatives, and overlap
handling were checked. `git diff --check` passed.

Local raw evidence, collection/normalization manifests, scratch adapters,
build logs and generated PDFs are retained in the ignored `review-data/`
directory. This review does not verify mathematical claims.
