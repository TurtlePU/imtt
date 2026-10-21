# Formalization coverage and planned paper labels

This is a plan, not a claim that the paper has been formalized. Baseline: [TurtlePU/imtt, revision 5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1](https://github.com/TurtlePU/imtt/tree/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1), “Towards Type Systems That Reinterpret Themselves”. See [the implementation plan](PLAN.md) for proof dependencies, specification questions and OCaml extraction.

Scope: all **12 explicit definitions, 8 figures and 13 theorems**, plus the appendix constructions and implicit lemmas below. There are no separately declared proposition or lemma environments in these sources; the proof-support lemmas must nevertheless be formalized. Introductory examples and proposed future self-interpreting extensions are not additional proved theorems.

## Label convention

Each row gives a **1-based line in the pinned paper**. Insert a new line immediately **after** that original line, not at the same numerical position after earlier edits. Figure labels go after their existing LaTeX label. Definition/theorem labels go after the opening declaration (and any immediately following label or optional title).

The exact proposed command is shown in the last column. Its target is a future published documentation anchor for the corresponding exported declaration in `formalization/rocq/theories/Paper/Claims.v`, logical module `IMTT.Paper.Claims`. These anchors and the configured `rocq:` documentation root must be verified against generated HTML before insertion. They are proposed stable declaration names, not existing URLs or fabricated future Rocq source line numbers.

The target paper currently has no `\formalized` command. Adding compatible badge support is a later implementation task. A statement badge must only mark a checked definition/statement; it must not imply a checked proof. Proof-completion badges, if used, are separate. **This PR adds neither badges nor LaTeX infrastructure.**

| ID | Definition, figure or theorem | Paper insertion point | Planned command |
| --- | --- | --- | --- |
| D01 | Naïve computational interpretation | [latex/nogo.tex:31](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/nogo.tex#L31) | `\formalized{rocq:IMTT.Paper.Claims.html\#naive_interpretation}` |
| T01 | Naïve no-go theorem | [latex/nogo.tex:48](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/nogo.tex#L48) | `\formalized{rocq:IMTT.Paper.Claims.html\#naive_no_go}` |
| D02 | Cartesian closed category | [latex/simply-typed.tex:34](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L34) | `\formalized{rocq:IMTT.Paper.Claims.html\#cartesian_closed_category}` |
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
| D06 | Category | [latex/dependently-typed.tex:470](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L470) | `\formalized{rocq:IMTT.Paper.Claims.html\#category}` |
| D07 | Terminal object | [latex/dependently-typed.tex:501](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L501) | `\formalized{rocq:IMTT.Paper.Claims.html\#terminal_object}` |
| D08 | Presheaf | [latex/dependently-typed.tex:508](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L508) | `\formalized{rocq:IMTT.Paper.Claims.html\#presheaf}` |
| D09 | Category of elements | [latex/dependently-typed.tex:525](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L525) | `\formalized{rocq:IMTT.Paper.Claims.html\#category_of_elements}` |
| D10 | Category with families | [latex/dependently-typed.tex:536](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L536) | `\formalized{rocq:IMTT.Paper.Claims.html\#category_with_families}` |
| F07 | Type computation; twoltt-typcomp | [latex/dependently-typed.tex:673](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L673) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_type_reduction}` |
| F08 | Term computation; twoltt-comp | [latex/dependently-typed.tex:780](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L780) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_term_reduction}` |
| T07 | Church–Rosser | [latex/dependently-typed.tex:834](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L834) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_confluence}` |
| T08 | Preservation | [latex/dependently-typed.tex:929](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L929) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_preservation}` |
| T09 | Identity model | [latex/dependently-typed.tex:977](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L977) | `\formalized{rocq:IMTT.Paper.Claims.html\#identity_model}` |
| T10 | Strong normalization | [latex/dependently-typed.tex:993](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L993) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_strong_normalization}` |
| T11 | Conservativity over MLTT | [latex/dependently-typed.tex:1027](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L1027) | `\formalized{rocq:IMTT.Paper.Claims.html\#twoltt_conservativity}` |
| D11 | Computational modality of global elements | [latex/discussion.tex:98](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/discussion.tex#L98) | `\formalized{rocq:IMTT.Paper.Claims.html\#computational_global_modality}` |
| D12 | Modal computational reinterpretation | [latex/discussion.tex:134](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/discussion.tex#L134) | `\formalized{rocq:IMTT.Paper.Claims.html\#modal_computational_interpretation}` |
| T12 | Modal no-go theorem | [latex/discussion.tex:156](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/discussion.tex#L156) | `\formalized{rocq:IMTT.Paper.Claims.html\#modal_no_go}` |
| T13 | Collapse of computational modalities | [latex/discussion.tex:209](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/discussion.tex#L209) | `\formalized{rocq:IMTT.Paper.Claims.html\#computational_modality_collapse}` |

## Additional constructions and implicit lemmas

These targets belong to the same future `Claims.v` facade: expand each anchor below as `\formalized{rocq:IMTT.Paper.Claims.html\#ANCHOR}`. Insert badges in prose, outside displayed mathematics. Appendix badges cover checked telescopes/procedures, not unproved claims of reflexivity.

| Coverage obligation | Planned insertion after pinned source line | Future declaration / anchor |
| --- | --- | --- |
| Closed-value polymorphic substitution and its side conditions | [simply-typed.tex:286](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L286) | `sstlc_value_substitution` |
| Parallel substitution, diamond and comparison with ordinary reduction | After the proof, before the next theorem, [simply-typed.tex:519](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L519) | `sstlc_parallel_development` |
| Reducibility, saturation, interpretation and fundamental lemma | After the proof, [simply-typed.tex:630](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/simply-typed.tex#L630) | `sstlc_fundamental_lemma` |
| Derived modal K law | After the display, [dependently-typed.tex:233](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L233) | `twoltt_modal_k` |
| Context conversion | After the display, [dependently-typed.tex:945](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L945) | `twoltt_context_conversion` |
| Three interpretation typing lemmas | After [dependently-typed.tex:974](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/dependently-typed.tex#L974) | `twoltt_interpretation_typing` |
| Internal model telescope, all coherence fields and explicit transports | After model display, [appendix.tex:223](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L223) | `internal_model_telescope` |
| Context/type/check/synthesis interpretation, substitution, weakening, equality witnesses | Before next section, after [appendix.tex:320](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L320) | `interpretation_procedures` |
| Displacement model and level-shift correctness | After model display, [appendix.tex:349](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L349) | `displacement_model` |
| Parametricity model and relational interpretation correctness | After final note, [appendix.tex:395](https://github.com/TurtlePU/imtt/blob/5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1/latex/appendix.tex#L395) | `parametricity_model` |

Before implementation, validate these extra prose insertion points against their surrounding environments; preserve the anchored baseline when rebasing. Unprinted structural lemmas, base-calculus normalization, algorithm correctness and extraction refinement are documented in the plan, not given artificial paper theorem numbers.

## Completion criterion

Each coverage entry needs a precise exported statement, a dependency/assumption audit and a kernel-checked implementation or proof. Unresolved specification issues remain visibly blocked, especially identity-model definitional equality, frozen-code computation, conversion-witness coherence, normalization and modal collapse. No theorem may be silently weakened to make its badge green. Deliver a buildable Rocq library, generated OCaml core, documented public OCaml interface, and regression examples; keep the mathematical claim and the executable guarantee distinct.
