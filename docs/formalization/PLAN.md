# Rocq formalization and OCaml extraction plan

Companion to the [coverage and label map](README.md). Baseline: paper revision `5bdb198c86a0b0a6f7407985068e2cd5d29c9bd1`. This document proposes future work; no Rocq theorem, executable or performance result is asserted to exist.

## 1. Deliverables and trust boundary

Deliver two related developments:

1. A faithful, deep syntactic formalization of the restricted simply typed calculus (SSTLC), the dependent two-level calculus, their internal models and interpretations, and all claims listed in the coverage map.
2. Executable syntax operations, SSTLC inference, checked reduction/interpretation and normalization, extracted to OCaml with a small documented interface.

Rocq proves facts **about the object calculus**. Its own universes, conversion, function η or proof irrelevance must not silently discharge an object-language equation absent from the paper. Object identity proofs stored in models are object terms, not erased Rocq proofs.

Aim for a constructive, axiom-free closed development. Generic no-go statements may quantify over explicit hypotheses. Audit every public theorem with `Print Assumptions`; distinguish such parameters from global axioms. No `Admitted`, unchecked termination, universe inconsistency, assumed normalization, UIP or functional extensionality in the completed syntactic core. If an external categorical presentation needs additional assumptions, isolate it, document them and do not route the core claims through it.

Generated OCaml inherits the extractor/compiler/runtime trust boundary; this is not a verified OCaml compiler project. Parsing and pretty-printing are untrusted unless proved separately, so raw input always crosses a verified checker.

## 2. Specification audit: first milestone, not deferred cleanup

Maintain the following issue register in this plan during implementation. For each item, record a precise formal statement, a minimal positive/negative example, a resolution and the affected coverage IDs. Do not change the paper in this planning PR. Any required mathematical correction needs a separate reviewed source change.

| Gate | Source and issue | Required resolution |
| --- | --- | --- |
| G1 | `nogo.tex:30–96`, `discussion.tex:98–198`: primitive recursion on normal forms alone does not supply every compositionality equation used in the proofs. | State the normal-neutral application equation, substitution stability, reduction compatibility, typing and confluence explicitly. Prove the claimed implication, not an unconditional impossibility theorem. |
| G2 | `simply-typed.tex:276–335, 513–517, 581–590`: closed-value substitution, omitted closure condition in the parallel contraction, and saturation notation. | Preserve closedness in every substitution lemma; reconcile parallel and ordinary reductions. Check the printed inclusion into SAT versus the intended candidate X before using it. |
| G3 | `dependently-typed.tex:238–452`: budget bounds, noncumulative universes, model-profile/quotation-level alignment and bidirectional annotations. | Make all presuppositions explicit; check Level-Uni/Level-Nat bounds, the model's coverage of quotation levels, dependent projection substitution and synthesis-preserving β outputs. Preserve the printed theorem or seek its correction; do not silently weaken exact synthesis preservation to conversion. |
| G4 | `dependently-typed.tex:612–781, 838–927`: frozen quotes/types versus active splices; parallel congruence appears broader than one-step congruence. | Specify evaluation contexts crossing only splice boundaries, if intended. Prove ordinary-step inclusion in parallel reduction and parallel inclusion in ordinary multisteps. Do not enable unrestricted reduction under quotation or Box. |
| G5 | `appendix.tex:5–223`: transports omitted; uniqueness omitted because object η is absent. | Elaborate the complete finite model telescope. Separate external lawful categories/CwFs from the internal signature and its listed propositional laws; prove the relationship actually needed, not an unjustified equivalence. |
| G6 | `appendix.tex:225–320`: interpretation has no explicit splice clause, and conversion inserts proof-relevant transports. | Define splice environment semantics, all binder cases and an executable conversion certificate. Prove substitution/weakening compatibility of generated witnesses; deterministic choice alone does not establish this coherence. |
| G7 | `dependently-typed.tex:977–991`, `appendix.tex:313–320, 393–395`: identity interpretation and all-equations-by-reflexivity claims without η. | Test neutral functions and dependent pairs, including η-expanded shallow embeddings. Prove object definitional equality exactly as stated or obtain a paper revision; propositional equality is a different theorem. Expand every parametricity component and its coherence proof. |
| G8 | `dependently-typed.tex:993–1051`: normalization via finite tuples of model interpretations; conservativity is open-context while normalization is stated closed. | Close the finite model-instance set under substitution/reduction, use one stable typed translation, and establish a well-founded simulation. Account for administrative/stuttering steps. Prove an open normalization strengthening or a valid reduction to the closed theorem. Canonicity alone is not strong normalization. |
| G9 | `discussion.tex:209–230`: modal collapse has only a proof idea. | State exactly what level(T) measures, which contexts are fixed, and which computational variant is quantified over. Test normal neutrals and high-level annotations; prove the stated budget-lowering lemma or report a counterexample. Do not infer computational collapse for the frozen modality. |

Existing `src/stlc-r.agda` and `src/mltt-r.agda` are exploratory references, not proof provenance. Inventory holes and compare every constructor/rule with this pinned paper before porting anything. The STLC sketch's unfinished semantic definition must not become an assumed Rocq constant.

**Gate to proceed:** freeze a rule-by-rule specification and record any unresolved theorem as blocked. Infrastructure and independent STLC work can continue, but dependent theorem badges cannot bypass G3–G9.

## 3. Representation and proposed directory/file structure

Use ordinary first-order inductive syntax in `Set`, with extrinsic scoping and typing predicates in `Prop`. Use de Bruijn indices, distinct polymorphic and monomorphic STLC variable namespaces, and explicit type-variable binders. Preserve user names only in an OCaml presentation layer. Keep inferred, checked and type syntax distinct where the paper does.

Dependent scopes record unlocked versus singly locked contexts and the two variable zones. Renaming/substitution must respect the lock boundary; splicing uses the outer environment, not post-lock locals. Object universe levels are natural-number syntax with checked bounds. They are not a runtime map into Rocq universes. An unbounded syntactic hierarchy does not license `Type : Type` or unchecked universe constraints.

Proposed logical root: `IMTT`. Every name below denotes a future file; this PR creates only the two planning documents.

```text
formalization/
  README.md                         # build, trust profile, examples
  rocq/
    dune-project                    # pinned compatible Rocq/Dune setup
    imtt.opam                       # exact supported dependencies
    theories/
      dune
      Common/
        Names.v                     # indices, scopes, finite maps
        Levels.v                    # budgets and finite level profiles
        Relations.v                 # multisteps, joinability, SN
        Certificates.v              # informative trace datatypes
      Category/
        Category.v                  # category, terminal, elements
        Presheaf.v                  # contravariance and laws
        CwF.v                       # external CwF presentation
      Base/
        STLC.v                      # syntax, typing, reduction
        MLTT.v                      # noncumulative Pi/Sigma/Id/Nat/U
        MLTTStructural.v            # substitution, conversion
        MLTTNormalization.v         # exact base SN theorem
      SSTLC/
        Syntax.v                    # grammar, values, model templates
        Substitution.v              # ordinary and closed-value forms
        Typing.v
        Interpretation.v            # type and term algorithms
        Reduction.v
        Confluence.v
        Preservation.v
        Reducibility.v              # saturation and fundamental lemma
        Normalization.v
        Conservativity.v
        Unification.v               # occurs check and correctness
        Inference.v                 # algorithm and decidability
      TwoLevel/
        Syntax.v
        Scope.v                     # lock-aware renaming/substitution
        Typing.v                    # WF, levels, check and synthesis
        Reduction.v                 # frozen contexts and active splices
        Structural.v                # weakening, substitution, contexts
        ModelSignature.v            # complete internal telescope AST
        ModelTyping.v               # its well-formedness theorem
        ConversionTrace.v           # strict strategy and certificates
        Interpretation.v            # context/type/check/synth recursion
        InterpretationLaws.v        # sub, wk, typing and witness laws
        Confluence.v
        Preservation.v
        Identity.v
        Normalization.v
        Conservativity.v
        Checking.v                  # certified practical entry points
      Models/
        Displacement.v              # syntax generator and typing
        Parametricity.v             # full components and laws
        Examples.v                  # free theorem / synthetic transfer
      Limits/
        Naive.v                     # abstract assumptions and no-go
        Modal.v                     # global modality and modal no-go
        Collapse.v                  # exact budget-lowering statement
      API/
        Errors.v                    # structured errors, resource limits
        Public.v                    # first-order extraction boundary
        Refinement.v                # executable/declarative agreement
      Paper/
        Claims.v                    # stable exports for every map row
        Assumptions.v               # public theorem dependency audit
    extraction/
      dune
      Extract.v                     # selected roots only, OCaml backend
  ocaml/
    generated/                      # generated .ml/.mli; never hand-edit
    lib/
      dune
      imtt.ml
      imtt.mli                      # small, documented abstract API
      syntax_io.ml                  # names, parsing, printing
    bin/
      dune
      main.ml                       # infer/check/normalize/interpret
  tests/
    rocq/
      RuleExamples.v
      RejectedPrograms.v
      ModelExamples.v
    ocaml/
      dune
      roundtrip.ml
      examples.ml
      resource_limits.ml
  examples/
    stlc/
    dependent/
```

Avoid many competing representations. A scoped/typed view may wrap raw ASTs for proofs, but prove erasure/refinement and keep the extraction path first-order to reduce casts. An external semantic CwF record may organize mathematics; it does not replace the syntactic term that inhabits the paper's internal model type.

`Paper/Claims.v` re-exports or bundles the actual definitions/theorems under the exact names in the coverage map; it contains no duplicate assumed statements. Multi-assertion preservation exports all conjuncts. Figure exports expose the full mutually defined judgments, not a token declaration named after the figure.

## 4. Ordered proof and implementation milestones

### M0 — Freeze the specification and toolchain

Complete the issue register, constructor/rule matrix and Agda comparison. Pin a supported Rocq/Stdlib/OCaml/Dune combination and dependency revisions; Rocq 9.2 is a documentation baseline, not a tested build claim here. Start with Stdlib and minimal local support; reuse another normalization library only after matching universes, identity elimination, reduction and η policy.

Acceptance: each of the 33 explicit items has a formal statement owner and dependency list; every changed interpretation of a printed rule is visible.

### M1 — Binding, levels and base calculi

Implement raw syntax and capture-avoiding operations. Prove renaming identity/composition, lifting, substitution identity/composition, weakening, scope preservation, free-variable and level invariants. For the lock discipline, prove that ordinary variables cannot cross the lock and splices cannot capture inner locals.

Define base STLC and exact base MLTT: noncumulative indexed universes, Pi, Sigma, intensional identity/J and indexed naturals, without object η. Prove their structural and conversion lemmas.

Establish a kernel-checked base MLTT normalization result before relying on it for equality-witness generation. Either port a matching proof or develop syntactic reducibility. Separate finite-fragment universe sizing from arbitrary syntactic level indices. This is a substantial proof milestone, not a one-line appeal to Rocq normalization.

Acceptance: binder tests, substitution proofs and the precise base-normalization dependency compile without axioms.

### M2 — Complete SSTLC definitions and preservation

Implement raw model templates with the two distinguished type parameters and the closed terminal type. Distinguish this equation-free internal signature from a lawful Cartesian closed category. Formalize values, restricted polymorphic let, interpretation of types and interpretation of closed values.

Implement the special substitution used by let reduction; its interpretation branch must invoke the recursive interpreter, not ordinary variable substitution. Prove well-scoping and closedness invariants, interpretation typing, ordinary substitution, special substitution and subject reduction. These are the four parts of T03.

Acceptance: every rule in the three SSTLC figures has both a constructor and a representative derivation; all side conditions are preserved.

### M3 — SSTLC confluence, normalization, conservativity and inference

Define parallel development and prove substitution compatibility, diamond, and agreement with ordinary multisteps. Prove strong normalization using the saturated-set/logical-relations argument, including interpretation reducibility and the fundamental lemma. Derive the stated normal-form characterization and conservativity with the same result type.

Implement Hindley–Milner-style inference with occurs-checking unification, fresh instantiation, context-aware generalization and explicit expansion of model type templates. Prove unification soundness/completeness and inference soundness/completeness, yielding the paper's decidability theorem. Principality is an additional goal only if separately stated and proved.

Acceptance: extraction of SSTLC inference can be demonstrated before the harder dependent milestones; rejection examples include illegal open let bindings and scope escapes.

### M4 — Dependent judgments and frozen operational semantics

Formalize each of the five dependent figures after resolving G3/G4. Include all well-formedness premises rather than treating ill-formed contexts as admissible. Distinguish checking, synthesis, type formation, type conversion and term conversion.

Prove context conversion, weakening, lock-aware substitution, presupposition, inversion and reduction compatibility. Record annotations needed to preserve the syntactic mode of a reduct. A frozen quotation's object skeleton remains unchanged; any allowed reduction of embedded host computations must follow an explicit splice-context rule.

Acceptance: forbidden nested locks and reinterpretation of inner object variables are rejected; allowed splices and modal K are derived without introducing an object computation rule under quotes.

### M5 — Full finite internal model telescope

Generate the model's object-language type from a finite level profile. Elaborate all transports suppressed in the appendix. Organize fields in dependency order: contexts/substitutions and laws; Ty/Tm and reindexing; comprehension; universes and codes; Pi/Sigma/Id/Nat and eliminators; all β/naturality equations.

Prove the telescope is well-formed at the claimed level bounds. Check universe/code indices in each field and closure under every substitution used by interpretation. Keep required object identity witnesses as syntax. Do not add uniqueness or η fields merely to ease later proofs.

Acceptance: the complete telescope typechecks in the formalized object system, not just as a Rocq record.

### M6 — Proof-relevant conversion and interpretation

Use informative trace data in `Set`/`Type`: endpoints, contracted rule and active position, plus a verified replay function. Relational convertibility proofs may live in `Prop`, but an interpreter that generates object equality proofs cannot inspect erased Prop derivations to choose computational data.

Define the fixed strict base strategy, trace construction on well-typed inputs, redex-to-model-equation translation, congruence, symmetry/transitivity and explicit transport insertion. Supply the missing splice case and all context/type/check/synthesis clauses.

Prove substitution and weakening laws for interpreted syntax and witnesses. Different conversion traces may produce different object identity terms; neither deterministic normalization nor metalevel proof irrelevance makes them judgmentally equal. Establish the coherence actually needed for confluence and preservation, or make the required paper correction explicit.

Avoid circular termination arguments: first give a relational specification or fuel-bounded prototype; justify total witness generation from base MLTT normalization; only then use it in the host metatheory.

Acceptance: interpreter output is well-typed for arbitrary well-typed finite models, including non-reflexive law fields; extracted witness generation retains those fields.

### M7 — Dependent confluence, preservation and identity model

Prove interpreter typing in all three modes, then the exact subject-reduction statement. Complete the parallel proof with treatment of witness-generating redexes, frozen contexts and critical overlaps; establish both comparisons with ordinary reduction.

Construct identity models as object syntax and verify their full telescopes. Prove the exact identity-model equation. Test closed terms with neutral functional subcomponents: Rocq's equality of semantic functions is not object definitional equality without η.

Acceptance: T07–T09 and their helpers have audited dependencies. If G6/G7 prevents the printed claim, report that rather than substituting a weaker theorem under the same name.

### M8 — Dependent normalization and conservativity

First evaluate the paper's translation into base MLTT. Define one typing-preserving translation for a fixed source derivation and a finite interpretation-family closure stable under substitution and reduction. Prove simulation for every reduction rule, including quotation η and administrative transports. If some steps stutter, provide a well-founded secondary measure; do not claim strict simulation without proof.

If finite closure or simulation fails, pursue a direct reducibility proof for the frozen calculus. Record the alternative argument and its exact assumptions; neither a test evaluator nor assumed strong normalization closes T10.

Strengthen normalization to the open contexts required by T11, or prove a sound closure argument. Show a normal host term of a base MLTT type in a base context contains no surviving host constructs, and use preservation to obtain conservativity at the original type.

Acceptance: full strong normalization for the specified reduction relation, not merely termination of one evaluator; normal-form characterization includes neutral/open terms.

### M9 — Applications and limitations

Construct displacement models and prove level shifting, typing and the intended term correspondence. Expand every parametricity field abbreviated “componentwise” or “…”; prove all naturality and identity-type coherence obligations. Resolve the appendix's explicit η warning before claiming those models inhabit the telescope.

Provide a small checked relational/free-theorem example and a generic synthetic-transfer lemma from an already checked model. Do not broaden this into a formalization of arbitrary higher geometry or of the paper's explicitly out-of-scope self-interpreting extensions.

Formalize the two no-go results parametrically with the explicit hypotheses from G1. For collapse, formulate the exact computational variant and prove budget lowering for normal forms. A counterexample is a specification result, not permission to add an axiom.

Acceptance: application claims and limitations are separately audited; no global normalization assumptions are smuggled into executable definitions.

### M10 — Certified executable boundary and OCaml delivery

Expose small first-order operations and structured errors. Suggested interface shape, subject to representation refinement:

```ocaml
type checked_program
type checked_model
type checked_code
type error = Ill_scoped | Type_error of diagnostic | Resource_exhausted

val infer_stlc : stlc_context -> stlc_term -> (scheme, error) result
val check : fuel:int -> raw_program -> (checked_program, error) result
val normalize : checked_program -> normal_form
val interpret :
  checked_model -> checked_code -> (checked_program, error) result
```

The public wrapper validates model/code compatibility and budget bounds. Keep checked constructors abstract in the hand-written interface; clients cannot fabricate proof-bearing values after extraction erases proofs. Normalize is total on successfully checked programs once its termination theorem is complete.

A fuel-bounded dependent checker returns resource exhaustion distinctly from rejection. Prove successful results sound and eventual success for derivable inputs. This is **not** a total decision procedure unless a complete termination argument for the whole checker is also supplied. The paper explicitly promises decidable inference for SSTLC, not automatically an arbitrary raw dependent-input decision algorithm.

Use Rocq's OCaml extraction backend with explicitly listed public roots. Generate both implementation and interface, compile them and wrap only presentation/error handling in handwritten OCaml. Never hand-edit generated code or replace verified algorithms with unproved fast alternatives. The extraction manual documents erasure of logical content and the handling of computational axioms; reject unrealized computational assumptions in the released dependency closure. See [Rocq extraction](https://rocq-prover.org/doc/V9.2.0/refman/addendum/extraction.html).

Start with faithful unbounded representations. Do not map naturals or levels to overflowing OCaml machine integers without a checked range invariant; accept presentation-layer fuel only after validating nonnegativity. Optimize arithmetic or data structures later with proved refinement. Audit for unsafe casts, `Obj.magic`, unrealized-axiom placeholders and supposedly impossible exception branches; redesign the boundary if extraction requires unchecked casts.

Dune's current `rocq.theory` and `rocq.extraction` support can build proofs and extracted OCaml together; the documented extraction stanza requires a compatible recent language version and an explicit generated-file list. Pin that configuration and place generated files according to the extraction stanza, staging into the proposed generated directory only if needed. Do not assume an untested stanza works. See [Dune Rocq support](https://dune.readthedocs.io/en/stable/rocq.html).

Acceptance: clean generation and OCaml compilation, stable documented `.mli`, no axioms on executable roots, and agreement tests against Rocq evaluation on representative accepted inputs.

### M11 — Documentation, badges and reproducible release

Generate declaration-linked HTML and verify every proposed anchor in the coverage map. Configure the paper's Rocq documentation root to a pinned release, add badge support separately, and rebase insertion points using their original declaration/figure anchors. Only then add definition/statement labels; distinguish proof-completion status.

Rocq's documentation tool supports links to declarations; see [documentation generation](https://rocq-prover.org/doc/v9.0/refman/using/tools/coqdoc.html). Link to checked declarations, not merely a directory containing sketches.

Acceptance: each coverage row resolves to the correct statement/definition and, where applicable, its proof and assumptions. Clean release builds reproduce the library, documentation and generated OCaml.

## 5. Verification matrix and stopping rules

| Area | Required checks |
| --- | --- |
| Rule coverage | Every grammar constructor and rule has a mapped definition plus positive/negative examples; all 33 explicit items and appendix/helper rows are traced. |
| Binding and modality | Rename/substitute composition; no capture; lock separation; nested-lock rejection; legitimate host splice computation without object reduction under quote. |
| Mathematical metatheory | Kernel-checked preservation, confluence, strong normalization and conservativity; no replacement of SN with canonicity or evaluator termination. |
| Models/witnesses | Complete telescopes; all transports; nontrivial model laws; conversion certificate replay; substitution coherence; exact identity equation; η-sensitive examples. |
| Algorithms | SSTLC inference sound/complete; dependent checking success sound and exhaustion distinct; normalization on certified input agrees with the relation; interpretation typing. |
| Extraction | Selected roots regenerate .ml/.mli; OCaml compiles with warnings reviewed; public checked values abstract; bounds validated; no unintended proof-data erasure or unrealized constants. |
| Reproducibility | Locked versions; clean proof/extraction/example builds; theorem assumptions recorded; generated documentation anchors verified; no private machine paths or credentials. |

The future implementation should document its exact commands, for example `dune build @all` and `dune runtest` after defining those targets, and run the pinned Rocq version's kernel rechecker. These are proposed release commands, **not commands executed by this planning PR**.

Stop a claim at its unresolved gate. Preserve completed independent modules, record the counterexample or missing argument, and request a mathematical decision before revising the paper's theorem. The dependency order is M0 → M1; M2–M3 can finish independently of dependent-model gates; M4–M6 feed M7–M8; M9 depends on the relevant model/metatheory results; M10 can begin with SSTLC but full dependent release waits for its proofs; M11 comes last.

## 6. Scope of this planning PR

Only this plan and the coverage summary are added. No Rocq files, extracted OCaml, build configuration, tests, badge macros, manuscript edits or generated PDFs are included. The implementation will require its own reviewed milestones; the high-risk dependent proofs must not be presented as routine transcription.

