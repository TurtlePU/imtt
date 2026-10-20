# Handoff: prose review

Reviewed the main manuscript and all seven input files at base
`bcbf7d5f8719ee93e7212ee6967bd1c8c201402c` on 20 October 2026.

- Applied minor spelling, punctuation, agreement and article corrections
  across 68 source lines. Exact before/after lines are in
  [MINOR_CORRECTIONS.md](../MINOR_CORRECTIONS.md).
- Saved 27 unapplied, source-aligned provider proposals in
  [WORDING_SUGGESTIONS.md](../WORDING_SUGGESTIONS.md).
- DeepL returned all 184 prepared blocks; Grazie verified 165 and left 19
  unverified. All blocks were attempted. See the per-block coverage and
  filtering audit under [review](../review/README.md).
- All baseline/full corrected build commands and the final syntax pass
  exited 0; both PDFs have 28 pages and matching baseline warnings.
  [review/README.md](../review/README.md) records exact commands, invariant
  checks, inspected PDF pages and limitations.
- Raw provider data, scratch scripts, immutable source manifests, logs and
  PDFs remain local under ignored `review-data/`; do not commit them.

Git's existing authentication permits publishing `prose/grazie-deepl-review`.
GitHub CLI authentication was unavailable when preparing this handoff, so
opening the requested PR requires a normal `gh auth login`, then creating
a PR from that branch against TurtlePU/imtt main. The prepared PR body is
local at `review-data/PULL_REQUEST.md`.
No credentials were read, copied or placed in this repository.
