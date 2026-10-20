# Wording suggestions

For coauthor review; none of these proposals has been applied. Excerpts match the corrected sources. Applied minor corrections are listed separately in [MINOR_CORRECTIONS.md](MINOR_CORRECTIONS.md).

Coverage and exclusions are recorded in [review/COVERAGE.json](review/COVERAGE.json) and [review/AUDIT.json](review/AUDIT.json). A missing or rejected response does not certify clean prose.

[CriticMarkup](https://fletcher.github.io/MultiMarkdown-6/syntax/critic.html): `{~~old~>new~~}`, `{++addition++}`, `{--deletion--}`.

## latex/appendix.tex:314-314 · appendix-L314-S2-P1 · Suggested by Grazie

- [ ] $\mathrm{step}_m$ maps the contracted redex to the corresponding model equation — $\Pi$-$\beta$, $\Sigma$-$\beta_i$, $\mathrm{Nat}$-$\beta_{0/\mathrm S}$, $\mathrm{Id}$-$\beta$, the $\mathrm{El}$-equations, $\mathrm{refl}$ for $(t:T)\leadsto t$ — composed with $\mathrm{sub}_m$ where the redex substitutes, and placed under the surrounding term formers by $\mathrm{ap}$ (interpretation of a former is a meta-level function of the interpretations of its immediate subterms, so congruence is $\mathrm{ap}$). Termination: the argument of the recursive call is strictly closer to `{++the ++}`normal form, and $a,b$ are MLTT terms, hence strongly normalising; well-definedness: convertible normal MLTT terms are $\alpha$-equal (confluence; no $\eta$).

## latex/conclusion.tex:3-11 · conclusion-L3-S2-P2 · Suggested by Grazie

- [ ] In retrospect, we managed to define two
self-interpreting type systems, $\SSTLC$ and $\twoLTT$,
meaning that they have a notion of their own ``internal
models'' which they then can use to reinterpret their
own terms inside such models. In doing so, such type
systems get new `{~~features~>features,~~}` which previously were defined
as separate builtin quirks of a system. Basic
metatheoretical properties are proven; for future work
we have the following plans:

## latex/conclusion.tex:53-57 · conclusion-L53 · Suggested by DeepL Write

- [ ]     \item At some `{~~moment~>point,~~}` we `{~~would have~>will need~~}` to `{~~pay~>conduct~~}` due
        `{~~diligence: provide~>diligence by providing~~}` mechanized proofs of
        `{++the ++}`metatheoretical properties of `{~~systems and~>the systems, as well as~~}` an
        implementation of $\twoLTT$ `{~~in~>within~~}` a practical proof
        assistant.

## latex/dependently-typed.tex:22-27 · dependently-typed-L22-S1-P1 · Suggested by Grazie

- [ ]     \item If we na\"{\i}vely adopt an approach to
        typing of models from Section~\ref{SSTLC}, `{--in
        order--}` to specify a model, we would need to
        specify countably many models, one per each
        universe. And even if we did, to which universe
        does the type of models belong?

## latex/dependently-typed.tex:69-80 · dependently-typed-L69-S1-P3 · Suggested by Grazie

- [ ] To interpret the conversion rule, we start by first
pinpointing the locations where the conversion rule is
actually used; `{--in order--}` to do this ergonomically, we
use bidirectional type checking. At the moment of
conversion, interpretation has enough information to
know both $T$ and $T'$; thus we can translate a chain
of reductions performed during definitional equality
check into a chain of propositional equalities taken
from coherence conditions proven in the definition of a
model. Then, a point of conversion is wrapped in
equality elimination with synthesized witness as a
scrutinee.

## latex/dependently-typed.tex:496-496 · dependently-typed-L496 · Suggested by DeepL Write

- [ ]         `{++This applies ++}`whenever all compositions are well-defined.

## latex/dependently-typed.tex:611-619 · dependently-typed-L611-S3-P1 · Suggested by Grazie

- [ ] Finally, on to computation rules as given in
Figures~\ref{twoltt-typcomp}-\ref{twoltt-comp}.
Mostly they are standard MLTT computation rules for
bidirectional typing (without $\eta$-equality for now).
Importantly enough, we \textbf{do not compute inside
locked terms and inside boxed types} `{--in order--}` to not
stumble into a variant of our no-go theorem \ref{no-go}
again (modal variant is spelled out in discussion, see
Section~\ref{global-elements}).

## latex/dependently-typed.tex:984-989 · dependently-typed-L984-S2-P1 · Suggested by Grazie

- [ ]     Take a universe at an appropriate level as a type of
    contexts; $\mathrm{Ty}_\ell(\Gamma)=
    \Gamma\to\mathcal{U}_\ell$;
    $\mathrm{Tm}_\ell(\Gamma, T)=(\gamma:\Gamma)\to
    T\,\gamma$. Define all `{--of--}` the remaining term
    interpretations to reinterpret to the same terms.

## latex/discussion.tex:12-25 · discussion-L12-S4-P2 · Suggested by Grazie

- [ ] Conal Elliott's ``Compiling to Categories''
\cite{Elliott:Compcat2017} shows how to interpret (some
subset of) Haskell in arbitrary \texttt{Category}
(again, definable in Haskell) via GHC compiler plugin.
That paper is a direct inspiration for this one. There
is an important difference, though: reinterpretation is
internal to our type systems, unlocking new patterns in
the usage of reinterpretation, including (but not
limited to) universe polymorphism, external
parametricity and more. However, Conal's approach is
more flexible since his translation to categories
requires the desired category to only implement primitives
actually used `{~~for translation of~>to translate~~}` a particular term at
hand.

## latex/discussion.tex:117-120 · discussion-L117 · Suggested by DeepL Write

- [ ]     `{~~And, in~>In~~}` addition, the following reduction is
    admissible: $K\,(\mathrm{nec}\,\lambda x.t)\,
    (\mathrm{nec}\,s)\leadsto^*
    \mathrm{nec}(t[s/x])$.

## latex/discussion.tex:131-132 · discussion-L131 · Suggested by DeepL Write

- [ ] `{~~Then, a~>The~~}` corresponding weakening of computational
reinterpretation can `{++then ++}`be defined as `{~~follows.~>follows:~~}`

## latex/discussion.tex:206-207 · discussion-L206 · Suggested by DeepL Write

- [ ] Another benefit of modal computational reinterpretation
is `{++its ability to exhibit ++}`the following property:

## latex/discussion.tex:228-229 · discussion-L228-S1-P1 · Suggested by Grazie

- [ ] `{~~But,~>But~~}` again, it all comes down to defining the type of
\textit{definitional} internal models.

## latex/discussion.tex:233-257 · discussion-L233-S3-P1 · Suggested by Grazie

- [ ] In Section~\ref{twoLTT}, we introduced our
``reinterpretable terms'' modality in a very
constraining way specifically so that we wouldn't have
to provide interpretation of this modality inside
internal models. Once again, the problem is with terms
that try to interpret variables from CwF context;
the simplest example is $\llbracket \lambda x.\llbracket x
\rrbracket_1\rrbracket_2$. `{~~In order to~>To~~}` be able to
interpret such a term, we would have to define \textit{
what reinterpretation operator means inside an internal
model}. This quickly gets out of hand: rather than just
turning the type of models into a (recursive? inductive?)
type, the type of models would become such a type that a
type of one of its fields depends on the value of the
whole model. Actually, this happened before:
Kolomatskaia et al. \cite{Kolomatskaia_Shulman_2025}
have already defined a type like this inside their
\textit{displayed type theory}: type SST of
semi-simplicial types is defined coinductively in terms
of values of itself\footnote{More generally, Shulman
dubs such types \textit{modal codatatypes}
\cite{shulman2026}.}. While defining type of models in
a similar vein could be an interesting development of the type
system presented in this paper, we deem it out of scope
for now.

## latex/intro.tex:62-79 · intro-L62-S1-P1 · Suggested by Grazie

- [ ] Turns out, we would get quite a few useful
metatheoretical results about object-level theory for
free; in particular, Wadler's parametricity theorem
\cite{wadler1989theorems,reynolds1983types} (for its
formulation in dependently typed context, see
\cite{Bernardy:Parametricity2010} and
\cite{Altenkirch:Parametricity2024}) about object-level
theory would be provable on the meta-level by `{--means of--}`
specifying a relational model; a fraction of displayed
type theory \cite{Kolomatskaia_Shulman_2025} can be
obtained via similar translation of a type into a unary
predicate. Another fun consequence is that object-level
theory would get universe polymorphism via displacements
as described by Conor McBride \cite{McBride:Crude2011,
McBride:Crude2012} and Favonia
\cite{Favonia:Displacement2023}; we suspect that there
might be other useful applications of internal
interpretation.

## latex/intro.tex:84-90 · intro-L84-S2-P1 · Suggested by Grazie

- [ ]     \item So our main goal is to construct an
        implementable reflective type system. The main
        difficulty in constructing such a system arises
        from a certain no-go result discussed in
        Section~\ref{no-go-section}, which forces us to
        limit the power of reinterpretation `{--in order--}` to
        keep type checking decidable.

## latex/intro.tex:101-107 · intro-L101-S2-P1 · Suggested by Grazie

- [ ]     \item Building upon the insights gathered from
        developing $\SSTLC$, we are finally equipped to
        dive into the reflective version of two-level
        type theory, where object level is vanilla MLTT,
        dubbed $\twoLTT$ (Section~\ref{twoLTT}). We
        prove `{++the ++}`soundness and conservativity of it as well
        (Section~\ref{twoLTT-properties}).

## latex/nogo.tex:4-18 · nogo-L4-S4-P2 · Suggested by Grazie

- [ ] So we want to build a reflective type system. That is,
a system where a user is able to both define a model of
a system internally and apply it to well-typed terms to
get their internal interpretations. Naturally, we would
like user-defined models to respect definitional
equalities of a system; in a dependently typed system,
this could be naturally achieved by using an identity
type to spell out corresponding equalities inside a
model. Then, it would be nice if, before interpreting
a term, the system `{--would--}` first `{~~bring~>brought~~}` it to normal form to
get rid of the artifacts of the construction in the
result of the interpretation. Finally, in a dependently
typed system, it is natural to expect reductions of open
terms, so we would like our interpretation to compute on
open terms.

## latex/nogo.tex:20-21 · nogo-L20 · Suggested by DeepL Write

- [ ] The theorem proven below asserts that `{~~we cannot~>it is impossible to~~}` have all
three in a single system.

## latex/nogo.tex:98-107 · nogo-L98-S2-P1 · Suggested by Grazie

- [ ] Fundamentally, the proof above exploits the openness of
the original term; if we restrict interpretation to
compute on closed terms only, we can arrive at a sound
system without requiring definitional equalities in
models, as exemplified by our non-dependently typed
system $\SSTLC$ described in Section~\ref{SSTLC}. And
this, actually, is a well-known setup: under the same
conditions (no dependent types `{~~+~>and~~}` computation on closed
terms), self-interpreter for System~F$\omega$ was
developed \cite{brown2016breaking}.

## latex/nogo.tex:109-110 · nogo-L109 · Suggested by DeepL Write

- [ ] `{~~For~>However, for~~}` a dependently typed system, `{--however,--}` our no-go
theorem leaves us with three `{~~options:~>options.~~}`

## latex/simply-typed.tex:16-32 · simply-typed-L16-S2-P2 · Suggested by Grazie

- [ ] So, what are the models of STLC? In addition to the
usual set-theoretic semantics where $S\to T$ is
interpreted as a function from $S$ to $T$ and
$S\times T$ is a cartesian product, there `{~~is~>are~~}`
proof-theoretic semantics that relate terms of type $T$
to intuitionistic proofs of proposition
$\llbracket T\rrbracket$, where $(\to)$ is now
understood to mean implication, and $(\times)$ is
conjunction. This, of course, is a classic Curry-Howard
correspondence \cite{ho80}; both set-theoretic and
proof-theoretic semantics are generalized by a complete
description of STLC models as given by Joachim Lambek
\cite{Lambek1980}. According to this
\textit{Curry-Howard-Lambek} correspondence, models
of STLC are precisely the cartesian closed categories
(or CCCs for short). Definitions vary; we're going to
use the definition \ref{ccc}.

## latex/simply-typed.tex:61-61 · simply-typed-L61 · Suggested by DeepL Write

- [ ]     `{++This applies ++}`whenever all compositions are well-defined.

## latex/simply-typed.tex:349-352 · simply-typed-L349 · Suggested by DeepL Write

- [ ] `{~~To~>In order to~~}` check reinterpretation, we `{++first ++}`need to define how the
model acts on monomorphic types. `{~~Since there's~>As there is~~}` no
computation on them, reinterpretation of types is `{++defined ++}`once
again `{--defined--}` as a recursive function on `{~~syntax:~>syntax.~~}`

## latex/simply-typed.tex:450-460 · simply-typed-L450-S1-P1 · Suggested by Grazie

- [ ] Here we only study some basic properties of a system to
make sure that everything works as expected:
computations are confluent; types are preserved by all
computations; all `{--of--}` the types can be inferred if you
wish to do so; everything terminates, and, modulo
reduction of \texttt{let}-bindings, this is the same old
STLC we started with. Proofs mostly follow
standard techniques since the rules for reinterpretation
are structured to directly plug into proofs of
properties of the STLC and the Hindley-Milner type
system.

## latex/simply-typed.tex:467-469 · simply-typed-L467 · Suggested by DeepL Write

- [ ]     `{~~Classic~>The classic~~}` proof `{~~via~>uses the~~}` parallel reduction relation
    \cite{takahashi1995parallel,barendregt1984lambda}.
    Parallel reduction is defined `{~~as:~>as follows:~~}`

## latex/simply-typed.tex:543-543 · simply-typed-L543 · Suggested by DeepL Write

- [ ]     `{~~By~>This is achieved through~~}` structural induction on terms and $(\leadsto)$.
