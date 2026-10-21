# Formalization coverage and planned paper labels

This is a plan, not a claim that the paper has been formalized. Baseline: [TurtlePU/imtt, revision 5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1](https://github.com/TurtlePU/imtt/tree/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1), “Towards Type Systems That Reinterpret Themselves”. See [the implementation plan](PLAN.md) for proof dependencies, specification questions and OCaml extraction.

Scope: the paper's contributions: **4 definitions, 8 figures and 11 theorems**, plus the necessary internal-model constructions and proof-support lemmas below. The six standard categorical definitions are reused from libraries, not re-formalized. The four discussion-section items are excluded as side remarks. The paper has no separately declared proposition or lemma environments. Original inventory IDs are retained so this scope change is auditable.

## Reuse existing formalizations

Import established definitions/results; add only notation aliases and paper-specific adapters. No local redevelopment or new paper badge is planned for this background.

| Paper background | Existing Rocq library to reference/reuse | Treatment |
| --- | --- | --- |
| D02: Cartesian closed category, simply-typed.tex:34 | UniMath: [Exponentials](https://github.com/UniMath/UniMath/blob/96eb565099e5e08e2542eba57f994217ed463195/UniMath/CategoryTheory/Exponentials.v), [binary products](https://github.com/UniMath/UniMath/blob/96eb565099e5e08e2542eba57f994217ed463195/UniMath/CategoryTheory/Limits/BinProducts.v) and [terminal objects](https://github.com/UniMath/UniMath/blob/96eb565099e5e08e2542eba57f994217ed463195/UniMath/CategoryTheory/Limits/Terminal.v) | Use the existing product/exponential structure; no local CCC definition or badge. |
| D06–D07: category and terminal object, dependently-typed.tex:470,501 | UniMath: [Core.Categories](https://github.com/UniMath/UniMath/blob/96eb565099e5e08e2542eba57f994217ed463195/UniMath/CategoryTheory/Core/Categories.v) and Terminal above | Reuse the appropriate precategory/category interface, without assuming object univalence. |
| D08–D09: presheaf and category of elements, dependently-typed.tex:508,525 | UniMath: [Presheaf](https://github.com/UniMath/UniMath/blob/96eb565099e5e08e2542eba57f994217ed463195/UniMath/CategoryTheory/Presheaf.v) and [CategoryOfElementsPsh](https://github.com/UniMath/UniMath/blob/96eb565099e5e08e2542eba57f994217ed463195/UniMath/CategoryTheory/Categories/CategoryOfElementsPsh.v) | Reuse constructions; check variance and set-valuedness at the adapter boundary. |
| D10: category with families, dependently-typed.tex:535–536 | UniMath/TypeTheory: [CwF_def.v](https://github.com/UniMath/TypeTheory/blob/d5d992d34649e1835d52f0a42e9a6b7058677060/TypeTheory/CwF/CwF_def.v), including `cwf_structure` and `cwf` | Reference/import the existing CwF development; only relate it to the paper's internal signature where required. |
| Ordinary binding operations and their algebra | [Autosubst](https://github.com/rocq-community/autosubst/tree/755000e9f8e10919791523e3a2675e36b92af636) | Reuse automation and laws; prove only new lock/interpretation-specific obligations. |
| First-order unification for inference | [FOUnify](https://github.com/rocq-archive/founify), including its [extraction entry point](https://github.com/rocq-archive/founify/blob/master/extract.v) | Existing certified extraction candidate; archived/toolchain and fixed-arity encoding compatibility must be checked before adoption, not assumed. |
| Base MLTT metatheory | [LogRel-Coq](https://github.com/CoqHott/logrel-coq/tree/9ca549d553bd41a6c00efb0655d23fa9a8dabd48) | Reuse where applicable. This revision has one universe and function/pair η, unlike the paper: matching arbitrary levels, no η and strong normalization remains an explicit compatibility gate, not a claimed existing theorem. |

The revisions identify inspected sources, not a tested mutually compatible dependency lock. [The plan](PLAN.md#11-reuse-policy-and-dependency-boundaries) sets the integration gates. Reuse of external categorical theory does not replace the novel executable **object-syntax encoding** of the internal model telescope.

## Excluded side remarks

No formalization modules, milestones or badges are planned for D11 (computational modality of global elements), D12 (modal computational reinterpretation), T12 (modal no-go) or T13 (computational-modal collapse), all in `latex/discussion.tex`. Likewise exclude generic modal-K theory, synthetic-mathematics transfer, general parametricity theory, general universe-displacement theory, and speculative interpretation-of-interpretation. Only concrete internal model instances needed to validate the paper's reinterpretation construction remain in scope.

## Label convention

Each row gives a **1-based line in the pinned paper**. Insert a new line immediately **after** that original line, not at the same numerical position after earlier edits. Figure labels go after their existing LaTeX label. Definition/theorem labels go after the opening declaration (and any immediately following label or optional title).

The exact proposed command is shown in the last column. Its target is a future published documentation anchor for the corresponding exported declaration in `formalization/rocq/theories/Paper/Claims.v`, logical module `IMTT.Paper.Claims`. These anchors and the configured `rocq:` documentation root must be verified against generated HTML before insertion. They are proposed stable declaration names, not existing URLs or fabricated future Rocq source line numbers.

The target paper currently has no `\formalized` command. Adding compatible badge support is a later implementation task. A statement badge must only mark a checked definition/statement; it must not imply a checked proof. Proof-completion badges, if used, are separate. **This PR adds neither badges nor LaTeX infrastructure.**

| ID | Definition, figure or theorem | Paper insertion point | Planned command |
| --- | --- | --- | --- |
| D01 | Naïve computational interpretation | [latex/nogo.tex:31](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/nogo.tex#L31) | `\formalized{rocq:IMTT.Paper.Claims.html\#naive_interpretation}` |
| T01 | Naïve no-go theorem | [latex/nogo.tex:48](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/nogo.tex#L48) | `\formalized{rocq:IMTT.Paper.Claims.html\#naive_no_go}` |
| D03 | Values | [latex/simply-typed.tex:172](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L172) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_values}` |
| F01 | Grammar; sstlc-grammar | [latex/simply-typed.tex:222](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L222) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_syntax}` |
| D04 | Term interpretation | [latex/simply-typed.tex:229](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L229) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_interpret_term}` |
| F02 | Computation; sstlc-comp | [latex/simply-typed.tex:334](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L334) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_reduction}` |
| D05 | Type interpretation | [latex/simply-typed.tex:355](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L355) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_interpret_type}` |
| F03 | Typing; sstlc-typing | [latex/simply-typed.tex:444](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L444) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_typing}` |
| T02 | Church–Rosser | [latex/simply-typed.tex:463](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L463) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_confluence}` |
| T03 | Preservation (all four assertions) | [latex/simply-typed.tex:521](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L521) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_preservation}` |
| T04 | Strong normalization | [latex/simply-typed.tex:547](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L547) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_strong_normalization}` |
| T05 | Conservativity over STLC | [latex/simply-typed.tex:632](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L632) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_conservativity}` |
| T06 | Decidable type inference (unnamed theorem) | [latex/simply-typed.tex:645](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L645) | `\formalized{rocq:IMTT.Paper.Claims.html\#sstlc_inference_decidable}` |
| F04 | Grammar; twoltt-grammar | [latex/dependently-typed.tex:170](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L170) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_syntax}` |
| F05 | Context/level rules; twoltt-wf | [latex/dependently-typed.tex:298](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L298) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_well_formedness}` |
| F06 | Bidirectional typing; twoltt-typing | [latex/dependently-typed.tex:451](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L451) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_typing}` |
| F07 | Type computation; twoltt-typcomp | [latex/dependently-typed.tex:673](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L673) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_type_reduction}` |
| F08 | Term computation; twoltt-comp | [latex/dependently-typed.tex:780](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L780) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_term_reduction}` |
| T07 | Church–Rosser | [latex/dependently-typed.tex:834](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L834) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_confluence}` |
| T08 | Preservation | [latex/dependently-typed.tex:929](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L929) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_preservation}` |
| T09 | Identity model | [latex/dependently-typed.tex:977](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L977) | `\formalized{rocq:IMTT.Paper.Claims.html\#identity_model}` |
| T10 | Strong normalization | [latex/dependently-typed.tex:993](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L993) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_strong_normalization}` |
| T11 | Conservativity over MLTT | [latex/dependently-typed.tex:1027](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L1027) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_conservativity}` |

## Additional constructions and implicit lemmas

These targets belong to the same future `Claims.v` facade: expand each anchor below as `\formalized{rocq:IMTT.Paper.Claims.html\#ANCHOR}`. Insert badges in prose, outside displayed mathematics. Appendix badges cover checked telescopes/procedures, not unproved claims of reflexivity.

| Coverage obligation | Planned insertion after pinned source line | Future declaration / anchor |
| --- | --- | --- |
| Closed-value polymorphic substitution and its side conditions | [simply-typed.tex:286](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L286) | `sstlc_value_substitution` |
| Parallel substitution, diamond and comparison with ordinary reduction | After the proof, before the next theorem, [simply-typed.tex:519](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L519) | `sstlc_parallel_development` |
| Reducibility, saturation, interpretation and fundamental lemma | After the proof, [simply-typed.tex:630](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L630) | `sstlc_fundamental_lemma` |
| Context conversion | After the display, [dependently-typed.tex:945](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L945) | `twoltt_context_conversion` |
| Three interpretation typing lemmas | After [dependently-typed.tex:974](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L974) | `twoltt_interpretation_typing` |
| Internal model telescope, all coherence fields and explicit transports | After model display, [appendix.tex:223](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L223) | `internal_model_telescope` |
| Context/type/check/synthesis interpretation, substitution, weakening, equality witnesses | Before next section, after [appendix.tex:320](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L320) | `interpretation_procedures` |
| Displacement model and level-shift correctness | After model display, [appendix.tex:349](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L349) | `displacement_model` |
| Parametricity model and relational interpretation correctness | After final note, [appendix.tex:395](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L395) | `parametricity_model` |

Before implementation, validate these extra prose insertion points against their surrounding environments; preserve the anchored baseline when rebasing. Unprinted structural lemmas, base-calculus normalization, algorithm correctness and extraction refinement are documented in the plan, not given artificial paper theorem numbers.

## Completion criterion

Each in-scope coverage entry needs a precise exported statement, a dependency/assumption audit and a kernel-checked implementation or proof. Existing library results are imported and credited, never redeveloped. Unresolved specification issues remain visibly blocked, especially identity-model definitional equality, frozen-code computation, conversion-witness coherence and normalization. No theorem may be silently weakened to make its badge green. Deliver a buildable Rocq library, generated OCaml core, documented public OCaml interface, and regression examples; keep the mathematical claim and the executable guarantee distinct.
