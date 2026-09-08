# *Handbook of Practical Logic and Automated Reasoning*: contents and summaries

Source: John Harrison, *Handbook of Practical Logic and Automated Reasoning* (Cambridge University Press, 2009). 
Page numbers below are the book's printed page numbers.

## Table of contents

- Preface — xi
- 1. Introduction — 1
  - 1.1 What is logical reasoning? — 1
  - 1.2 Calculemus! — 4
  - 1.3 Symbolism — 5
  - 1.4 Boole's algebra of logic — 6
  - 1.5 Syntax and semantics — 9
  - 1.6 Symbolic computation and OCaml — 13
  - 1.7 Parsing — 16
  - 1.8 Prettyprinting — 21
- 2. Propositional logic — 25
  - 2.1 The syntax of propositional logic — 25
  - 2.2 The semantics of propositional logic — 32
  - 2.3 Validity, satisfiability and tautology — 39
  - 2.4 The De Morgan laws, adequacy and duality — 46
  - 2.5 Simplification and negation normal form — 49
  - 2.6 Disjunctive and conjunctive normal forms — 54
  - 2.7 Applications of propositional logic — 61
  - 2.8 Definitional CNF — 73
  - 2.9 The Davis–Putnam procedure — 79
  - 2.10 Stålmarck's method — 90
  - 2.11 Binary decision diagrams — 99
  - 2.12 Compactness — 107
- 3. First-order logic — 118
  - 3.1 First-order logic and its implementation — 118
  - 3.2 Parsing and printing — 122
  - 3.3 The semantics of first-order logic — 123
  - 3.4 Syntax operations — 130
  - 3.5 Prenex normal form — 139
  - 3.6 Skolemization — 144
  - 3.7 Canonical models — 151
  - 3.8 Mechanizing Herbrand's theorem — 158
  - 3.9 Unification — 164
  - 3.10 Tableaux — 173
  - 3.11 Resolution — 179
  - 3.12 Subsumption and replacement — 185
  - 3.13 Refinements of resolution — 194
  - 3.14 Horn clauses and Prolog — 202
  - 3.15 Model elimination — 213
  - 3.16 More first-order metatheorems — 225
- 4. Equality — 235
  - 4.1 Equality axioms — 235
  - 4.2 Categoricity and elementary equivalence — 241
  - 4.3 Equational logic and completeness theorems — 246
  - 4.4 Congruence closure — 249
  - 4.5 Rewriting — 254
  - 4.6 Termination orderings — 264
  - 4.7 Knuth–Bendix completion — 271
  - 4.8 Equality elimination — 287
  - 4.9 Paramodulation — 297
- 5. Decidable problems — 308
  - 5.1 The decision problem — 308
  - 5.2 The AE fragment — 309
  - 5.3 Miniscoping and the monadic fragment — 313
  - 5.4 Syllogisms — 317
  - 5.5 The finite model property — 320
  - 5.6 Quantifier elimination — 328
  - 5.7 Presburger arithmetic — 336
  - 5.8 The complex numbers — 352
  - 5.9 The real numbers — 366
  - 5.10 Rings, ideals and word problems — 380
  - 5.11 Gröbner bases — 400
  - 5.12 Geometric theorem proving — 414
  - 5.13 Combining decision procedures — 425
- 6. Interactive theorem proving — 464
  - 6.1 Human-oriented methods — 464
  - 6.2 Interactive provers and proof checkers — 466
  - 6.3 Proof systems for first-order logic — 469
  - 6.4 LCF implementation of first-order logic — 473
  - 6.5 Propositional derived rules — 478
  - 6.6 Proving tautologies by inference — 484
  - 6.7 First-order derived rules — 489
  - 6.8 First-order proof by inference — 494
  - 6.9 Interactive proof styles — 506
- 7. Limitations — 526
  - 7.1 Hilbert's programme — 526
  - 7.2 Tarski's theorem on the undefinability of truth — 530
  - 7.3 Incompleteness of axiom systems — 541
  - 7.4 Gödel's incompleteness theorem — 546
  - 7.5 Definability and decidability — 555
  - 7.6 Church's theorem — 564
  - 7.7 Further limitative results — 575
  - 7.8 Retrospective: the nature of logic — 586
- Appendix 1. Mathematical background — 593
- Appendix 2. OCaml made light of — 603
- Appendix 3. Parsing and printing of formulas — 623
- References — 631
- Index — 668

## 1. Introduction

The opening chapter defines logical reasoning as inference whose correctness depends on form rather than subject matter: valid deduction exposes what follows necessarily from explicit assumptions, even though it cannot supply empirical premises of its own. Harrison places automated reasoning in the historical tradition running from Leibniz's ambition to turn reasoning into calculation through Boole's algebra of propositions. The recurring idea is that a precise symbolic language, a semantics for interpreting it, and mechanically applicable transformation rules make deductive reasoning amenable to computation.

The chapter then establishes the book's practical method. It distinguishes concrete notation from recursively defined abstract syntax and introduces interpretation functions as the bridge from syntax to semantics. A small OCaml datatype for arithmetic expressions demonstrates symbolic representation, pattern matching, recursive simplification, lexical analysis, recursive-descent parsing, and precedence-sensitive pretty-printing. These are not incidental programming preliminaries: they supply the representation and traversal techniques used throughout the later prover implementations.

## 2. Propositional logic

This chapter develops propositional logic as both a mathematical system and an executable toolkit. It defines formulas and their OCaml representation, assigns them truth-functional semantics through valuations, and formalizes the central notions of validity, satisfiability, contradiction, consequence, and equivalence. It then derives useful structural transformations—simplification, negation normal form, disjunctive normal form, and conjunctive normal form—and explains both their logical justification and their potential exponential cost.

The second half turns these foundations into automated reasoning methods. It encodes combinatorial and circuit problems as propositional formulas, uses Tseitin-style definitions to obtain compact equisatisfiable CNF, and implements the Davis–Putnam and DPLL SAT procedures, Stålmarck’s saturation method, and reduced ordered binary decision diagrams. The chapter closes with the compactness theorem, showing that the finite, computational character of each formula has a powerful consequence for infinite sets of formulas.

### 2.1 The syntax of propositional logic

Propositional formulas are built from the constants false and true, atomic propositions, negation, and the binary connectives conjunction, disjunction, implication, and equivalence. The OCaml datatype is parameterized over the atom type and already includes `Forall` and `Exists` constructors for the later transition to first-order logic. The section fixes concrete ASCII syntax, precedence, and right-association rules; builds generic parsers and printers specialized to named propositional variables; and introduces constructor/destructor helpers plus recursive traversals such as `onatoms`, `overatoms`, and `atom_union`. These operations matter because all later algorithms work structurally over the formula datatype rather than manipulating unparsed strings.

### 2.2 The semantics of propositional logic

A valuation maps atoms to Boolean truth values, and the recursive `eval` function gives each compound formula its truth-functional meaning; in particular, implication is interpreted as `not p or q`, while equivalence tests equality of truth values. Truth tables make these definitions explicit and lead to two basic structural results: every formula contains only finitely many atoms, and its value depends only on the valuation of those atoms. The code therefore enumerates the finitely many relevant valuations to print complete truth tables. The section also carefully distinguishes the formal material conditional from causal or conversational uses of “if,” explaining why its apparently odd cases are forced once implication is required to be truth-functional.

### 2.3 Validity, satisfiability and tautology

A formula is valid or a tautology when every valuation satisfies it, satisfiable when at least one does, and unsatisfiable when none does; validity of `p` is equivalent to unsatisfiability of `¬p`. The definitions extend to sets of formulas and semantic consequence `Γ |= q`. Exhaustive valuation enumeration yields direct decision procedures for tautology and satisfiability, while substitution is defined by replacing atoms with formulas. The key substitution theorem relates evaluating a substituted formula to evaluating the original under a modified valuation, establishing that substitution instances of tautologies remain tautologies and that logically equivalent subformulas may replace one another without changing truth. A catalogue of characteristic tautologies then records algebraic laws, contraposition, and the distinction between an implication and its converse.

### 2.4 The De Morgan laws, adequacy and duality

The De Morgan equivalences connect negation with conjunction and disjunction and show how connectives can be defined from others. The chapter calls a collection of connectives *adequate* when it can express every propositional formula, proving examples such as `{∧, ¬}` and `{⇒, false}` and showing that neither the usual positive binary connectives alone nor any one of them can express negation. Among all binary truth functions, NAND and NOR are each adequate by themselves, explaining their foundational role in digital circuits. For formulas using false, true, conjunction, disjunction, and negation, the `dual` operation swaps false/true and conjunction/disjunction; its semantic law says that evaluating the dual under `v` negates the original formula evaluated under the complemented valuation, allowing valid laws to generate dual laws systematically.

### 2.5 Simplification and negation normal form

The first normalization pass, `psimplify`, recursively eliminates occurrences of true and false using elementary equivalences and removes double negations. A literal is an atom or its negation, with complementary literals obtained by adding or removing one negation. A formula is in negation normal form (NNF) when it uses only conjunction and disjunction over literals (apart from the two constants). The `nnf` transformation removes implication and equivalence and pushes negations inward with De Morgan’s laws, preserving logical equivalence, though expanding equivalences can cause exponential growth. The alternative `nenf` keeps equivalence while still pushing negation to atoms. NNF is useful not merely as syntax: positive-only occurrences yield monotonic dependence on an atom, while negative-only occurrences yield antimonotonic dependence.

### 2.6 Disjunctive and conjunctive normal forms

DNF is a disjunction of conjunctions of literals, while CNF is the dual conjunction of disjunctions. One DNF construction reads the satisfying rows of a truth table and creates a complete conjunction of signed atoms for each; another starts from NNF and repeatedly distributes conjunction over disjunction. Representing normal forms as sets of sets makes associativity, commutativity, and idempotence implicit and enables simplification by deleting contradictory terms and subsumed supersets. CNF is obtained dually by forming DNF for the negation and negating its literals. These forms make satisfiability of DNF and validity of CNF locally recognizable, but conversion may expand exponentially, so they clarify the decision problem without yet providing a generally efficient solver.

### 2.7 Applications of propositional logic

The section demonstrates how concise real problems generate demanding propositional instances. Ramsey statements are encoded with one atom per graph edge, making `R(s,t) <= n` equivalent to validity of a formula asserting an `s`-clique or a `t`-vertex independent set. Digital circuits map naturally to formulas: wires become atoms, gates become connectives, and internal wires express shared subcomputations. Half- and full-adders are composed into ripple-carry and carry-select adders, whose equivalence becomes a tautology-checking problem; repeated addition similarly constructs multipliers, and the absence of a nontrivial factorization becomes a primality tautology. These reductions motivate stronger solvers: SAT captures many practical combinatorial problems, is NP-complete, and often serves as an effective common backend despite exponential worst-case behavior.

### 2.8 Definitional CNF

Ordinary equivalent CNF may be exponentially larger than its input, so definitional CNF weakens the requirement from logical equivalence to *equisatisfiability*. Fresh atoms name compound subformulas, and equivalences tying each name to its definition are conjoined with the renamed top-level formula. The defining theorem proves that replacing a fresh atom by its definition preserves satisfiability in both directions, while the resulting clauses are only a constant-factor larger because each local definition has bounded size. The implementation reuses existing definitions, chooses fresh indexed names safely, exposes existing conjunction/disjunction structure to avoid needless definitions, and can enforce 3-CNF. This linear-size Tseitin-style transformation is the practical bridge from arbitrary formulas to the clausal inputs expected by SAT algorithms.

### 2.9 The Davis–Putnam procedure

CNF is represented as a set of clauses, with the empty clause denoting false and the empty clause set true. The original Davis–Putnam procedure repeatedly applies unit propagation, the pure-literal rule, and—when neither applies—resolution on an atom; resolution combines every positive clause with every negative clause after removing the pivot, and a theorem proves the transformation equisatisfiable. A heuristic chooses the pivot that minimizes clause blowup. DPLL replaces resolution with branching on a frequent atom, retaining unit and pure-literal simplification; an iterative version records guessed and deduced literals on a trail, then backtracks on conflict. The section also motivates modern refinements such as backjumping, conflict explanation and learned clauses, restarts, better branching heuristics, satisfying assignments, unsatisfiable cores, and checkable refutations.

### 2.10 Stålmarck’s method

Stålmarck’s method limits nested case splits by using a dilemma rule: split on a literal, saturate both branches with simple deductions, and retain every equivalence derived in both. Exhaustive direct deduction is 0-saturation; recursively using dilemmas produces 1-, 2-, and higher saturation, with an *n-easy* formula decided at level `n`. The input is converted into triplets of the form `l_i ⇔ l_j op l_k`, and truth-table checks precompute trigger rules that derive equivalences among literals and constants. A union-find structure maintains equivalence classes, relevance indexing restricts trigger processing, and branch intersections preserve shared consequences or propagate a contradiction. The resulting bounded prover performs well on circuit identities, though failure below the chosen saturation limit is inconclusive and may be complemented by DPLL splitting.

### 2.11 Binary decision diagrams

A binary decision tree represents valuations as paths and a Boolean function as truth-valued leaves. Removing nodes whose branches coincide and sharing identical subtrees yields a reduced ordered binary decision diagram (BDD); for a fixed variable order this representation is canonical, so equivalence reduces to comparing representations and a tautology is exactly the true terminal. The implementation adds complemented edges, making negation constant-time and increasing sharing, plus a unique table for canonical nodes and a computed table that memoizes Boolean operations. Formulas are compiled bottom-up through BDD conjunction and derived connectives. A further optimization recognizes acyclic definitional equivalences and substitutes their BDDs directly. BDD performance depends critically on variable order and can still be exponential, but canonical symbolic representation makes BDDs valuable beyond proving, especially in hardware verification and model checking.

### 2.12 Compactness

The compactness theorem states that if every finite subset of a set `Γ` of propositional formulas is satisfiable, then all of `Γ` is satisfiable. For countably many atoms, the proof constructs a valuation one truth value at a time: at each stage at least one choice must preserve finite satisfiability, since failure of both choices would produce a finite unsatisfiable union. Every individual formula depends on only finitely many atoms, so the completed valuation satisfies it. Contrapositively, every unsatisfiable set has a finite unsatisfiable subset; a related corollary extracts a finite tautologous disjunction from an arbitrary covering family. As an application, graph coloring is encoded propositionally, and compactness lifts finite `k`-colorability to infinite graphs—hence the finite four-colour theorem implies four-colourability for infinite planar graphs as well.

## 3. First-order logic

This chapter extends propositional logic with object-denoting terms, predicates whose truth depends on those terms, and universal and existential quantification. It builds both an abstract semantics—domains, interpretations, valuations, and recursive truth—and a matching OCaml representation. Much of the early chapter develops the syntactic machinery needed to manipulate quantified formulas correctly: capture-avoiding substitution, normal forms, and Skolemization. The central semantic reduction is that a quantifier-free formula is satisfiable exactly when its ground instances are propositionally satisfiable; canonical and Herbrand models make that bridge precise.

The second half turns this reduction into theorem provers. Naive enumeration of ground instances gives Gilmore and Davis–Putnam procedures, while unification discovers useful instances symbolically. That idea yields free-variable tableaux and first-order resolution, followed by redundancy controls such as subsumption and directed strategies such as positive resolution and set of support. Horn clauses support least-model semantics, goal-directed proof, and Prolog; model elimination extends that style to arbitrary clauses. The chapter closes by comparing top-down and bottom-up proof search and deriving compactness and Löwenheim–Skolem results from the same machinery.

### 3.1 First-order logic and its implementation

First-order logic distinguishes *terms*, which denote objects, from *formulas*, which denote truth values. Terms are represented as variables or an (n)-ary function applied to arguments (`Var` and `Fn`), with constants treated as nullary functions; atomic formulas are predicates applied to term lists, embedded in the existing propositional formula datatype. A signature records permitted function and predicate symbols with arities. Quantifiers bind object variables only: `Forall(x,p)` and `Exists(x,p)` distinguish bound from free occurrences, and their ordering can change meaning, as the contrast between continuity and uniform continuity illustrates. The implementation deliberately remains first-order—function and predicate variables cannot be quantified—and defines the basic syntax on which every later transformation operates.

### 3.2 Parsing and printing

The parser turns quotations into formulas by default and bar-delimited quotations into terms, while installed printers reconstruct readable concrete syntax. It supports ordinary applications plus familiar infix arithmetic operators, exponentiation, list construction, and unary negation with explicit precedence rules; notably, `-x^2` parses as `(-x)^2` under the chosen convention. Since bare identifiers are ambiguous between variables and constants, names bound by an enclosing quantifier are variables, explicit `c()` forces a constant, and the configurable `is_const_name` recognizes digit strings and `nil` as constants by default. Quantifiers use `forall x.` and `exists x.` syntax, with scopes extending as far right as possible. The section makes concrete notation a disciplined front end to the abstract syntax rather than part of the logic itself.

### 3.3 The semantics of first-order logic

An interpretation supplies a nonempty domain, meanings `D^n → D` for function symbols, and truth-valued relations for predicate symbols; a valuation separately assigns domain elements to variables. `termval` recursively evaluates terms, while `holds` extends propositional truth clauses with quantifiers by ranging over all domain elements under an updated valuation. A formula is valid when it holds in every interpretation and valuation, satisfiable when some interpretation makes it hold for all valuations, and a sentence when it has no free variables. Truth depends only on free-variable assignments, but semantic entailment for open assumptions differs subtly from implication validity—for example, `{P(x)}` entails `P(y)`, although `P(x) ⇒ P(y)` is not valid. Because arbitrary and infinite domains cannot be exhaustively evaluated, later decision procedures must reduce validity indirectly rather than enumerate interpretations.

### 3.4 Syntax operations

The section implements universal closure and capture-avoiding substitution, the two key operations needed by later transformations. Term substitution (`tsubst`) is structural and satisfies both the expected free-variable equation and a semantic substitution lemma. Formula substitution is harder: bound occurrences must not be replaced, and a term’s free variables must not become accidentally captured. `subst` therefore delegates quantified cases to `substq`, which alpha-renames binders with fresh variants when needed and shadows mappings for bound variables. The resulting operation preserves the exact free-variable set predicted by substituted terms and satisfies the fundamental theorem `holds M v (subst i p) = holds M (termval M v ∘ i) p`. Consequently every substitution instance of a valid formula is valid; these proofs justify the implementation’s renaming logic rather than treating it as an informal convention.

### 3.5 Prenex normal form

A formula is in prenex normal form when every quantifier is in an outer prefix and its matrix is quantifier-free. The transformation first simplifies truth constants and vacuous quantifiers, then computes negation normal form by eliminating implications and equivalences and using the quantifier De Morgan laws, and finally pulls quantifiers outward through conjunctions and disjunctions. Moving a quantifier can capture a free variable, so `pullquants` alpha-renames the binder before applying the equivalences; it also merges same-kind quantifiers only in the cases where doing so is sound. `pnf = prenex ∘ nnf ∘ simplify` therefore returns a logically equivalent formula, not merely an equisatisfiable one. Prenex form isolates quantifier structure for analysis and prepares the next reduction, although later Skolemization is sometimes more economical before full prenexing.

### 3.6 Skolemization

Skolemization removes existential quantifiers by replacing each witness with a fresh function of the free variables on which it may depend; an existential with no dependencies becomes a Skolem constant. The result is generally not logically equivalent to the source, but it is equisatisfiable because the interpretation of each fresh function can select suitable witnesses (using choice in the general presentation). The implementation collects existing function symbols to avoid clashes, Skolemizes positive existentials after simplification and NNF conversion, processes outer binders first to minimize function arity, and can then prenex and drop universal quantifiers. The section proves the model-extension theorem underpinning each replacement, notes the transformation’s conservativity for conclusions that omit the new symbols, and explains why direct Skolemization before prenexing can avoid irrelevant function arguments.

### 3.7 Canonical models

For quantifier-free formulas, atomic first-order formulas can initially be viewed as propositional atoms. The easy semantic direction maps any interpretation and valuation to a propositional valuation. The converse builds a *canonical interpretation* whose domain is the set of terms, variables denote themselves, functions construct syntax trees, and predicates reproduce the chosen propositional valuation; consequently term evaluation is substitution. Restricting this construction to ground terms gives the Herbrand universe and Herbrand interpretations. The main Herbrand theorem states that a quantifier-free formula is first-order satisfiable exactly when all of its ground instances are propositionally satisfiable, equivalently exactly when it has a Herbrand model. This canonical-model reduction is limited to quantifier-free or universal formulas, but it is the semantic foundation for mechanized first-order proof search.

### 3.8 Mechanizing Herbrand’s theorem

Propositional compactness strengthens Herbrand’s theorem: unsatisfiability is witnessed by some finite set of ground instances. The implementation enumerates ground term tuples by increasing number of function applications, ensuring eventual coverage of the Herbrand universe. Gilmore’s procedure accumulates instances in DNF and closes when every disjunct contains complementary literals; it is complete as a semidecision procedure but suffers catastrophic DNF growth. A Davis–Putnam variant instead accumulates CNF clauses and calls DPLL, greatly improving space behavior, while a refinement can discard instances unnecessary to the final contradiction. Even so, most enumerated instances are irrelevant and runtime depends unpredictably on when a useful finite set appears. This exposes unstructured Herbrand-universe search—not propositional satisfiability alone—as the deeper bottleneck.

### 3.9 Unification

Unification replaces blind instance enumeration with a syntactic solver for substitutions that make terms identical. A unification problem is a set of term pairs; among its solutions, a most general unifier (MGU) represents every other unifier by further substitution. The recursive algorithm decomposes equal-headed function applications, orients variable equations, records variable-to-term assignments, and rejects symbol clashes and cycles through an occurs check. Its environment remains cycle-free and preserves the solution set; `solve` propagates assignments to obtain an idempotent solved form. The section proves failure means impossibility, success yields an MGU, and termination is guaranteed, while noting possible exponential expansions. It then distinguishes *local/bottom-up* calculi, whose universally reusable clauses permit independent instantiation, from *global/top-down* calculi, whose case splits require substitutions to be propagated consistently across a proof.

### 3.10 Tableaux

The Prawitz procedure combines Gilmore-style DNF reasoning with unification: it introduces fresh variables instead of ground terms, then unifies complementary literals across all disjuncts so that only necessary specializations are imposed. Analytic tableaux make this incremental. A branch decomposes conjunctions, splits on disjunctions, and repeatedly instantiates universal formulas with fresh variables while retaining them for reuse; it closes when a literal unifies with a complement already on the branch. The OCaml implementation threads a global unification environment through continuations and applies iterative deepening to bound universal instantiations, giving completeness without committing to an unbounded depth-first search. Splitting closed top-level DNF disjuncts into independent subproblems further lowers shared variable bounds. This structure-directed method performs well on the chapter’s benchmark problems, though clause and instantiation ordering still strongly affect search.

### 3.11 Resolution

First-order resolution lifts propositional resolution by renaming the variables of two clauses apart, selecting complementary literal sets, and applying their MGU to the remaining literals. Factoring—unifying multiple literals within one clause—is essential: without it, a most-general step may fail to reproduce a ground propositional proof whose instantiation merged literals. The lifting lemma proves that a ground resolvent is an instance of a suitable first-order resolvent, so compactness and Herbrand’s theorem imply refutation completeness: every unsatisfiable clause set derives the empty clause. Resolution is not complete for deriving arbitrary consequences directly, only refutation complete. The implementation constructs factors and resolvents, then uses a given-clause loop with `used` and `unused` sets so every clause pair is eventually considered, providing a simple bottom-up prover after negation, Skolemization, and CNF conversion.

### 3.12 Subsumption and replacement

Naive resolution generates many redundant clauses, especially tautologies and clauses weaker than ones already known. First-order subsumption defines `C <=ss D` when some instance of `C` is a subset of `D`; it is decidable here by one-way term matching, which instantiates variables only in the candidate subsumer. The section proves that resolvents of subsumed clauses are themselves subsumed by appropriate resolvents or ancestors, thereby justifying tautology deletion and carefully controlled forward deletion and backward replacement. Newly generated clauses are discarded when tautologous or subsumed by the current/unused pool; if a new clause properly subsumes an unused one, it replaces it at the old queue position to prevent useful clauses receding indefinitely. Invariants over given, used, and unused clause levels establish refutation completeness of this optimized loop, while experiments show dramatic reductions in generated clauses.

### 3.13 Refinements of resolution

Several complete restrictions focus resolution search. Linear resolution requires each step to reuse the preceding result (possibly with earlier ancestors), reducing duplicated proof trees but complicating tautology and subsumption policies. Positive resolution requires one parent to be all-positive; a minimal-model argument proves refutation completeness, and the implementation often outperforms unrestricted search. Semantic resolution generalizes the idea relative to any interpretation: at least one parent must be false there. The set-of-support strategy instead forbids resolving two clauses outside a designated support set; completeness holds when the unsupported clauses are satisfiable, making hypotheses near the negated goal natural support choices. Positive hyperresolution compresses a sequence resolving every negative literal against positive clauses into one inference, avoiding order permutations. Together these refinements demonstrate how completeness-preserving restrictions can replace indiscriminate clause generation with problem-directed inference.

### 3.14 Horn clauses and Prolog

A Horn clause has at most one positive literal, and a definite clause exactly one. Satisfiable Horn theories have a least Herbrand model; for definite clauses it is the closure generated by their rules. This yields convexity—if a Horn theory entails a finite disjunction of atoms, it entails one disjunct—and an existential witness property for quantifier-free goals. Operationally, a rule `P1 ∧ ... ∧ Pn ⇒ Q` supports backward chaining: unify the current goal with `Q`, replace it by the `Pi`, rename rule variables afresh, and backtrack over alternatives. Iterative deepening makes the resulting Horn prover complete. Removing the bound produces Prolog’s fast depth-first execution, which can loop and is therefore incomplete, but turns definite clauses into procedures with unification as parameter passing and can return witnesses for variable-containing queries.

### 3.15 Model elimination

Model elimination, presented as subgoal-oriented MESON, extends Prolog-style search from Horn clauses to arbitrary clauses. Each clause contributes contrapositives by choosing any literal as a head; all-negative clauses also yield a rule concluding falsity. Ordinary extension unifies a goal with a rule head and generates its premises, while the crucial *ancestor reduction* closes a goal against the complement of a literal already on its path. Viewed as connection tableaux, the requirement that each selected clause connect to the latest branch literal preserves a minimal-unsatisfiable-subset invariant and yields completeness by lifting from ground proofs. The implementation uses continuations, fresh renaming, global substitutions, and iterative proof-size deepening. Repetition checks and balanced allocation of the size bound across subgoals materially improve performance. MESON is memory-light and goal-directed, but CNF expansion and repeated equivalent subgoals remain weaknesses relative to reusable bottom-up lemmas.

### 3.16 More first-order metatheorems

The final section extends Skolemization to countable sets by first renaming every original function symbol into a reserved namespace, then processing formulas sequentially with globally fresh Skolem symbols. A union of the successive model extensions proves preservation of satisfiability in the same domain. Combining this with propositional compactness and Herbrand models yields a countable-model theorem: if every finite subset of a countable theory has a model, the whole theory has a countable model. Its standard corollaries are first-order compactness and the downward Löwenheim–Skolem theorem; the latter shows that even the full first-order theory of an uncountable structure has a countable model. An upward result is trivial without built-in equality because new elements can be made indistinguishable from an old one. The discussion closes by locating these results and proof procedures among model theory, many-sorted logic, and automated-reasoning literature.

## 4. Equality

The chapter changes the semantics of the symbol `=` from an arbitrary binary predicate to genuine identity. It first shows that ordinary first-order logic can simulate this restriction by adding equivalence and congruence axioms, and uses that reduction to transfer compactness and Löwenheim–Skolem results. It then isolates equational logic, where Birkhoff’s rules give a sound and complete proof system, and develops congruence closure as a decision procedure for ground equations and universal equality formulas.

For nonground equations, the chapter turns to directional rewriting. Termination plus confluence makes normalization a complete equality test; lexicographic path order supplies a practical termination proof, and Knuth–Bendix completion attempts to manufacture confluence by adding oriented critical pairs. The final sections compare two ways of integrating equality into general theorem proving: Brand’s preprocessing transformations eliminate most equality axioms, while paramodulation adds a native equality inference rule to resolution. These methods foreshadow ordered superposition, where logical and equational inference are tightly controlled by term orderings.

### 4.1 Equality axioms

A *normal* interpretation gives `=` its intended identity relation. Such models satisfy reflexivity, symmetry, transitivity, and congruence axioms for every function and predicate in the problem. Although these axioms cannot force an arbitrary model itself to be normal, any model satisfying them can be quotiented by its interpreted equality relation; congruence makes functions and predicates well defined on equivalence classes, producing a normal model that preserves every formula. Thus a theory has a normal model exactly when it plus its equality axioms has an ordinary model, and (p) is valid with equality exactly when `eqaxiom(p) ⇒ p` is ordinarily valid. `equalitize` constructs only the relevant finite axioms, omitting redundant equality-predicate congruence and nullary cases, so existing provers—including Horn and MESON procedures—can handle equality unchanged after preprocessing.

### 4.2 Categoricity and elementary equivalence

With genuine equality, first-order theories describe mathematical structures such as groups, and Chapter 3’s metatheorems gain stronger model-theoretic force. Compactness and downward Löwenheim–Skolem transfer via equality axioms; compactness also shows that arbitrarily large finite normal models imply an infinite one and constructs nonstandard models containing elements larger than every standard numeral. An isomorphism is a bijection preserving all functions and predicates, and a theory is categorical when all its models are isomorphic. Löwenheim–Skolem prevents a first-order theory with an infinite model from being categorical across all cardinalities, motivating weaker notions: κ-categoricity fixes a cardinality, while elementary equivalence merely requires models to satisfy the same first-order sentences. The results expose a fundamental expressive limit: first-order truth cannot uniquely determine most infinite structures up to isomorphism.

### 4.3 Equational logic and completeness theorems

Birkhoff’s equational calculus derives equations from equational assumptions using axiom instances, substitution, reflexivity, symmetry, transitivity, and functional congruence. Birkhoff’s theorem states that these rules are both sound and complete: Δ semantically entails (s=t) in all normal models exactly when there is such a derivation. The completeness proof can be read through Horn-clause backchaining on the equality axioms, whose proof tree corresponds to Birkhoff inferences. The section distinguishes full completeness from resolution’s weaker refutation completeness and notes that Birkhoff proofs resemble ordinary algebraic manipulation more closely than clausal refutations do. Yet equational reasoning is not computationally easy: full first-order logic embeds into it, and even small algebraic axiom sets may require unexpectedly creative intermediate equations, as the one-sided group-axiom example demonstrates.

### 4.4 Congruence closure

For ground equations, instantiation disappears from Birkhoff’s calculus and every needed intermediate term can be restricted to the finite set of input subterms. The congruence closure of asserted equalities is the least equivalence relation also closed under corresponding function applications; a target equation follows exactly when its sides belong to the same class. The Nelson–Oppen-style implementation represents classes by union–find and tracks predecessor terms, recursively merging parent applications whenever their arguments become equivalent. This yields a terminating decision procedure. To decide universal formulas over equality and uninterpreted functions, the prover negates and Skolemizes the formula, puts it in DNF, and tests each conjunction of equations and inequations; Horn convexity means an implied disjunction of equalities has an individually implied member. The section also contrasts Ackermann’s reduction, which replaces function applications with variables and congruence constraints, ultimately reducing the problem to SAT.

### 4.5 Rewriting

Rewriting orients equations (l=r) as rules that replace matching instances of (l) by (r) at arbitrary subterms. If every term reaches a unique irreducible normal form, equality becomes a computation: normalize both sides and compare them. The section abstracts from terms to reduction relations and formalizes termination, normal forms, the diamond property, weak confluence, confluence, joinability, and Church–Rosser. Newman’s lemma proves that termination plus weak confluence implies confluence; confluence is equivalent to Church–Rosser, and a terminating confluent system is *canonical*. Birkhoff completeness then shows that interconvertibility by rewrite steps is exactly semantic equational consequence. The implementation performs top-level matching and recursively uses a leftmost-outermost strategy, but termination remains the caller’s responsibility and is undecidable in general—hence the need for termination orders in the next section.

### 4.6 Termination orderings

A reduction order is a terminating, transitive term order closed under substitution and embedding in function contexts. If every rewrite rule decreases such an order, the induced rewrite relation terminates. Simple term-size measures are often inadequate because substitution can reverse size comparisons and algebraic laws such as associativity or distributivity may preserve or increase size. The lexicographic path order (LPO) instead combines the proper-subterm property, lexicographic comparison of same-headed argument lists, and a chosen precedence on function symbols, while requiring the whole left side to dominate every right-side argument. The section proves that, over finitely many symbols, LPO preserves variables, is transitive, substitution-stable, context-stable, irreflexive, and terminating; hence it is a practical reduction order capable of orienting common algebraic rules that crude numerical measures cannot handle.

### 4.7 Knuth–Bendix completion

For a terminating system, Newman’s lemma reduces confluence to local confluence. Two one-step rewrites can fail to rejoin only when their left-hand sides overlap at a nonvariable position; disjoint rewrites and rewrites beneath substituted variables commute. Unification computes finitely many most-general *critical pairs* representing all such overlaps, and a terminating rewrite system is confluent exactly when every critical pair is joinable. Knuth–Bendix completion normalizes a nonjoinable pair, orients the resulting equality using a fixed reduction order, adds it as a rule, simplifies existing rules, and processes newly created overlaps. If it terminates successfully, it returns a canonical rewrite system equivalent to the original equations. It may instead fail because neither orientation decreases the order, or diverge because new critical pairs are generated without end; nevertheless it can automatically discover powerful missing lemmas, including rules needed to complete group axioms.

### 4.8 Equality elimination

This section removes equality axioms by compiling their effect into clauses. General equivalence elimination replaces (R(s,t)) with a formula saying (R(s,w)) and (R(t,w)) agree for every (w), yielding an equisatisfiable formula without separately assuming reflexivity, symmetry, and transitivity. Brand’s specialized transformations retain reflexivity: S-modification expands positive equations to account for symmetry, T-modification encodes transitivity with fresh variables, and E-modification *flattens* nested function terms into auxiliary equalities. A model-construction theorem shows that flat formulas satisfying equivalence can be reinterpreted to satisfy all function and predicate congruences, so E followed by S and T leaves only (x=x) as an explicit equality axiom. Integrated into MESON, this preprocessing can greatly outperform raw equality axioms on some algebraic problems, though clause blowup and problem-dependent performance motivate more selective ordered variants.

### 4.9 Paramodulation

Paramodulation handles equality inside the calculus rather than preprocessing it. From a clause containing (s=t) and another containing a literal with a subterm unifiable with (s), it replaces that occurrence by (t), applies the MGU, and combines the remaining literals; unlike ordinary rewriting, equations may be conditional, used either way, and matched by full unification. Together with resolution it is refutation complete once suitable reflexivity clauses are supplied. The chapter proves this by simulating positive-hyperresolution uses of equivalence and congruence axioms, then discusses Brand’s stronger result that simple reflexivity suffices if paramodulation into variables is largely forbidden—although set-of-support restrictions may again require functional reflexivity. The implementation generates overlaps within literals and clauses and adds paramodulants to the given-clause loop. Effective modern descendants impose term orderings and selection strategies, culminating in superposition-style provers.

## 5. Decidable problems

First-order validity is only semidecidable in general: proof procedures can eventually certify valid formulas, but they need not terminate on invalid ones. This chapter identifies important islands where a genuine yes/no algorithm exists. It first obtains decidability from syntactic restrictions—bounded Herbrand universes, quantifier prefixes, monadic predicates, and finite-model arguments—and then turns to theories whose mathematical structure supports quantifier elimination.

The chapter is also an implementation-oriented tour of symbolic algebra. Cooper-style elimination decides Presburger arithmetic; polynomial normalization and elimination handle algebraically closed and real closed fields; ideals and Gröbner bases decide universal algebraic consequences; coordinate translations support geometry theorem proving; and Nelson–Oppen-style methods combine otherwise separate decision procedures. Together these examples show that decidability is not merely a classification result: the proof of decidability often supplies executable normalization, elimination, or model-search machinery.

### 5.1 The decision problem

The section distinguishes three algorithmic tasks: semideciding validity (or unsatisfiability), semideciding invalidity (or satisfiability), and deciding between the two. Procedures such as tableaux and resolution solve the first task but may search forever on invalid input; running validity and invalidity semidecision procedures in parallel would solve the third task only when both exist. Church and Turing’s negative result rules out such a general first-order decision procedure, motivating two controlled alternatives developed in the chapter: restrict the syntactic form of formulas, especially their quantifier pattern, or restrict interpretations to models of a particular theory. The distinction matters because termination, rather than mere soundness or refutational completeness, is what turns theorem search into decision.

### 5.2 The AE fragment

Herbrand’s theorem yields a decision procedure when Skolemizing the negation of a candidate theorem introduces constants but no positive-arity function symbols: the Herbrand universe is then finite, so all ground instances can be generated and their conjunction tested once by DPLL. For satisfiability this is the EA prefix class, `∃*∀*`; dually, validity is decidable for the AE class `∀*∃*`. The implementation `aedecide` Skolemizes, rejects residual non-nullary functions, forms every tuple over the constants, instantiates the CNF matrix, and invokes propositional decision. The section stresses that prenex transformation order can affect whether a useful AE presentation is exposed, whereas direct Skolemization often preserves a better structure. The procedure may be costly—many variables make the finite instance set enormous—but unlike general proof search it always returns yes or no on its intended fragment.

### 5.3 Miniscoping and the monadic fragment

Miniscoping pushes quantifiers inward to shrink their scopes, sometimes converting formulas with an apparently bad prefix into AE form. The implementation puts an existential body into DNF, distributes the quantifier over disjuncts, and separates conjuncts that contain the variable from those that do not; universal quantifiers are handled through negation. Applying simplification, NNF conversion, miniscoping, and then `aedecide` gives the `wang` procedure. The key theorem is that for a function-free monadic formula—one using only unary predicates—each quantifier in the miniscoped result has a quantifier-free body with no other free variable, so prenexing produces AE and establishes decidability of the whole monadic fragment. This broadens the visibly AE class, although repeated DNF/CNF transformations under alternating quantifiers can cause catastrophic formula growth, so decidability in principle does not imply practical efficiency.

### 5.4 Syllogisms

Aristotle’s A, E, I, and O premises are encoded with unary predicates: “all S are P” as `∀x. S(x) ⇒ P(x)`, “no S are P” similarly with negation, and the two particular forms existentially. Enumerating four figures and all choices for three premises produces 256 syllogisms, all in the decidable monadic fragment. Automated checking finds only 15 valid under ordinary modern first-order semantics, rather than the traditional 24. The discrepancy comes from existential import: traditional syllogistic often presupposes that each term denotes a nonempty class. Adding existence hypotheses for S, P, and M recovers the 24. The experiment both gives a finite decision procedure for syllogistic and exposes how a seemingly obvious formal translation can encode a substantive interpretive choice about empty predicates.

### 5.5 The finite model property

A fragment has the finite model property when satisfiability is equivalent to satisfiability in some finite model, or dually when validity can be checked over finite models. Combined with ordinary theorem semidecision, this yields a decision method: interleave proof search with enumeration of finite interpretations until either a proof or a countermodel appears. The text makes this constructive by enumerating tuples, finite functions, predicates, and interpretations. It then uses model-size arguments to explain prefix-class boundaries: certain classes, including the Gödel class `∀^n∃∃∀^m` without equality, have finite models under explicit bounds, while slightly stronger prefixes admit formulas true in every finite model but false over an infinite strict order. Equality changes the frontier—AE remains decidable, `∀^n∃∀^m` is decidable, but Gödel’s larger class becomes undecidable—and the two-variable function-free fragment retains the finite model property even with equality.

### 5.6 Quantifier elimination

A theory admits quantifier elimination when every formula has an equivalent quantifier-free formula using no new free variables. If ground formulas can be effectively evaluated, elimination immediately yields completeness and decidability: eliminate all quantifiers from a sentence and compute the truth of the result. The general implementation reduces the task to eliminating a single existential from a conjunction of literals. It recursively eliminates inner quantifiers, rewrites universals by negation, converts quantifier-free bodies to DNF, distributes existentials, and separates literals independent of the eliminated variable. Dense linear orders provide the first example: comparisons involving the variable are reduced to consistency constraints among lower and upper bounds. The resulting procedure decides the theory and shows that all dense linear orders without endpoints are elementarily equivalent, so first-order formulas in the order language cannot distinguish, for example, the rationals from the reals.

### 5.7 Presburger arithmetic

Presburger arithmetic is integer arithmetic with addition, order, constants, and multiplication only by constants. Quantifier elimination requires enriching the language with divisibility predicates, since a formula such as `∃x. 2x = y` has no equivalent in the bare additive language. The implementation first normalizes terms into integer linear combinations, simplifies relations, and applies Cooper’s method: normalize coefficients of the eliminated variable, compute a common modulus, and reduce an unbounded existential question to finitely many boundary and residue cases. Divisibility atoms record the periodic information lost by ordinary inequalities. The result decides arbitrary first-order linear integer arithmetic, while the text carefully marks its limits: allowing variable multiplication makes the theory undecidable, whereas some restricted extensions remain decidable. Complexity is severe—general procedures have a doubly exponential lower bound—though useful subproblems such as conjunctions of linear equations admit much better algorithms.

### 5.8 The complex numbers

The theory of complex numbers with addition and multiplication admits quantifier elimination because the field is algebraically closed. The implementation represents multivariate polynomials canonically in nested Horner form, with arithmetic operations preserving a chosen variable ordering. To eliminate an existential variable from a conjunction of polynomial equations and inequations, it reduces formulas to divisibility and common-root conditions, using pseudo-division and resultants-like polynomial transformations so the degree in the selected variable falls recursively. Algebraic closure supplies the crucial existence fact: every nonconstant polynomial has a root, while a constant equation is decided directly. Iterating the core elimination over DNF gives `complex_qelim`, capable of proving identities about polynomial roots. The construction establishes not merely decidability of the complex field but completeness of the theory of algebraically closed fields of characteristic zero in this language.

### 5.9 The real numbers

Real arithmetic with addition, multiplication, equality, and order is decided by quantifier elimination for real closed fields. Rather than Tarski’s original costly procedure or full cylindrical algebraic decomposition, the section implements a simpler Cohen–Hörmander method. Its core object is a sign matrix for a finite family of univariate polynomials: rows represent roots and intervening intervals, columns record whether each polynomial is negative, zero, or positive. A quantifier-free existential formula is true exactly when one row’s signs satisfy it. Sign matrices are built recursively using derivatives, polynomial remainders, and behavior at infinity, then lifted to multivariate elimination with coefficient case splits. The method also specializes to Fourier–Motzkin elimination for linear real inequalities. It proves decidability and completeness of real closed fields while illustrating why nonlinear real reasoning is algorithmically much harder than linear programming.

### 5.10 Rings, ideals and word problems

The word problem asks whether equations `E` force another equation in a class of algebraic structures. For commutative rings, polynomial normalization turns an implication `p₁=0 ∧ … ∧ pₙ=0 ⇒ q=0` into ideal membership: it holds in all rings exactly when `q` lies in the integer-polynomial ideal generated by the premises. Variants characterize torsion-free rings over rational coefficients and integral domains or fields via powers of `q`, yielding forms of Hilbert’s Nullstellensatz. The Rabinowitsch trick replaces `q ≠ 0` by a fresh equation `1 − qz = 0`, reducing universal formulas over fields to checking whether `1` belongs to an ideal. Embeddings into fraction fields and algebraic closures relate universal theories of integral domains, fields, algebraically closed fields, and the complex numbers. The section also derives analogous, simpler linear-combination criteria for abelian groups and monoids.

### 5.11 Gröbner bases

Gröbner bases make the ideal-membership characterizations of the previous section decidable in practice, especially over rational polynomial rings. A polynomial equation is oriented by its greatest monomial under a well-founded multiplicative order and used as a rewrite rule; reduction terminates because each step replaces a monomial by strictly smaller ones. Arbitrary generators need not give confluent reduction, so Buchberger’s algorithm repeatedly constructs S-polynomials for critical overlaps, reduces them, and adds nonzero remainders until all critical pairs close. Dickson’s lemma ensures this completion process terminates. The resulting Gröbner basis has canonical zero remainder exactly for members of the generated ideal, and the implementation also tracks cofactors, producing checkable algebraic certificates rather than a bare Boolean answer. The analogy with Knuth–Bendix completion is explicit: both obtain decision procedures by completing a terminating rewrite system to confluence.

### 5.12 Geometric theorem proving

Analytic geometry translates point relations into polynomial equations in coordinates: collinearity uses a determinant equation, perpendicularity a dot product, equal lengths squared distances, and intersections paired collinearity constraints. The `coordinate` transformation instantiates such templates, after which Gröbner-basis or Wu-style algebra can prove the universal consequence. Translation and rotation invariance justify fixing one point at the origin and another on an axis; scaling or shearing can simplify further but may introduce nondegeneracy assumptions or fail to preserve metric properties. Although the intended coordinates are real, many universal equational claims can be proved over the complex numbers, where algebraic tools are faster; this can also generate explicit degenerate cases that must be excluded. Wu’s triangularization method successively pseudo-divides polynomials, yielding a main conclusion plus side conditions and efficiently proving classical examples such as Pappus’s theorem.

### 5.13 Combining decision procedures

Applications often mix theories and uninterpreted symbols, so a formula is first purified: alien subterms are replaced by fresh variables while congruence constraints preserve equal arguments and results. The Nelson–Oppen framework combines decision procedures for disjoint signatures using equalities between shared variables. Craig interpolation explains completeness: if purified components are jointly inconsistent, their interaction can be expressed entirely in the shared equality language. A naive algorithm enumerates every equality/disequality arrangement of shared variables and asks each theory solver about its part; Nelson–Oppen instead exchanges implied equalities incrementally until one solver reports contradiction or saturation is reached. Stable infiniteness lets separately satisfiable components choose compatible infinite domains. Convex theories need propagate only single equalities, avoiding disjunctive case splits; nonconvex theories such as integer arithmetic may require branching. The discussion closes with Shostak-style canonizers/solvers and modern SMT architecture, where congruence closure, arithmetic solvers, Boolean search, and theory combination cooperate.

## 6. Interactive theorem proving

Complete automation cannot realistically discover most substantial mathematical proofs. This chapter therefore builds an interactive prover in which a human supplies structure while automation fills routine gaps. Its trust story follows the LCF architecture: an abstract theorem type can be created only by a tiny collection of sound primitive inferences, while arbitrary OCaml programs may safely assemble derived rules, proof searches, and tactics from those primitives.

The development proceeds bottom-up. It chooses a Hilbert-style kernel, derives convenient propositional and first-order rules, reconstructs tableau proofs as kernel theorems, and then layers goal-directed tactics and Mizar-like declarative syntax over the result. The chapter’s central engineering lesson is that trustworthy extensibility comes from separating the small logical kernel from large, fallible search code; proof-producing automation can fail or be inefficient without manufacturing a false theorem.

### 6.1 Human-oriented methods

Systematic proof search and attempts to imitate human mathematical thought have different strengths and limitations. Early human-oriented programs by Newell–Simon and Gelernter used heuristics, diagrams, and plausible reasoning, while systematic methods later surpassed them on several domains such as geometry. NQTHM’s induction and generalization heuristics and Bundy’s proof planning show that human-like guidance can nevertheless be powerful. The section resists a simple choice between “human” and “machine” styles: mathematicians rely on intuition, analogy, experimentation, and luck, but computers often excel precisely by following disciplined procedures humans would not. This motivates interactive theorem proving, where users contribute strategic ideas and systems supply exact formal bookkeeping and domain-specific automation.

### 6.2 Interactive provers and proof checkers

An interactive assistant checks human proofs, exposes hidden assumptions and missing cases, and automates routine subarguments. SAM pioneered semi-automated mathematics; AUTOMATH and Mizar showed that substantial mathematics could be checked from structured proof texts. Mizar deliberately permits only small “obvious” gaps, improving readability and predictable checking but making new domain-specific obviousness laborious. LCF solves the extensibility-versus-soundness problem differently: users program arbitrary proof procedures in ML, but values of abstract type `thm` can arise only through trusted primitive inference constructors. Bugs in tactics then cause failure or poor proofs rather than false theorems. This architecture—general-purpose metalanguage outside, tiny protected logic inside—is the foundation for the implementation that follows.

### 6.3 Proof systems for first-order logic

The section surveys formal provability `Γ ⊢ p` and contrasts Hilbert/Frege systems, natural deduction, and sequent calculus. Natural deduction organizes introduction and elimination rules around connectives and resembles reasoning from assumptions. Sequent calculus instead has left- and right-introduction rules; its cut rule composes lemmas, while Gentzen’s cut-elimination theorem shows cut is theoretically dispensable, though removing it may cause enormous growth. Cut-free systems are syntax-directed and closely related to semantic tableaux; resolution and inverse methods can also be understood against this proof-theoretic background. The historical discussion—from Frege and Russell to Hilbert, Ackermann, Gentzen, and Gödel—separates sound formal rules from the inconsistent stronger systems once used for logicism and frames the practical choice of a small Hilbert system for the LCF kernel.

### 6.4 LCF implementation of first-order logic

The kernel deliberately avoids substitution as a primitive because capture-avoiding substitution has subtle side conditions. Its proper rules are modus ponens and universal generalization; axiom schemas cover implicational classical logic, quantifier distribution, equality reflexivity and congruence, existence of an equal term, and definitions of the remaining connectives in terms of implication, falsity, and universal quantification. Soundness follows by checking every schema and showing the two inference rules preserve validity. An OCaml module signature hides the representation of `thm`, exposes only these constructors and a read-only `concl`, and checks side conditions such as freedom of variables with simple trusted code. This is the LCF security boundary: all later complexity is untrusted derived programming whose outputs remain constrained by the abstract type.

### 6.5 Propositional derived rules

From the sparse kernel the text constructs a practical propositional library. It derives reflexivity, weakening, permutation and contraction of implication chains; transitivity and monotonicity; biconditional introduction and elimination; contraposition, double-negation elimination, and ex falso; and introduction/elimination behavior for conjunction and other defined connectives. “Shunting” moves between conjunctive antecedents and curried implications, which becomes essential for tactic goals and proof reconstruction. Each helper is executable OCaml composed solely from primitive theorem constructors, so it extends convenience without extending trust. The exercise also demonstrates why a tiny Hilbert basis is adequate but unpleasant by hand: a short mathematical inference expands into many kernel steps, making derived rules the necessary abstraction layer.

### 6.6 Proving tautologies by inference

The propositional tableau algorithm is rebuilt so that success returns an actual theorem rather than merely a Boolean. Nonprimitive connectives are expanded to implication and falsity; conjunctive and disjunctive tableau splits are mirrored by derived inference rules; complementary literals construct an explicit contradiction theorem; and implication-ordering helpers keep the recursive theorem in a canonical chain-of-assumptions shape. `lcfptab` follows ordinary tableau control flow but reconstructs every recursive step through the LCF rules. To prove `p`, `lcftaut` refutes `p ⇒ ⊥` and applies double-negation elimination. It is slower and more elaborate than direct tautology checking, but the result is kernel-certified, illustrating how an untrusted search method can be converted into proof-producing automation.

### 6.7 First-order derived rules

The main goal is a derived specialization rule taking `⊢ ∀x. P(x)` to `⊢ P(t)` without trusting substitution in the kernel. Equality congruence is first lifted recursively from terms to formulas. Quantifier rules and Tarski’s equality-based idea derive `x=t ⇒ P(x) ⇒ P(t)`, then use the axiom `∃x. x=t` to justify specialization. The difficult case is formulas under binders: `isubst` performs alpha-conversion through a fresh intermediate variable so that replacement never captures variables, and `ispec` alpha-renames when the quantified variable occurs in the specializing term. Symmetry, transitivity, congruence, existential-left, and generalization helpers complete the library. Because all of this is derived, even complicated renaming logic cannot compromise soundness; an error merely prevents construction of the desired `thm`.

### 6.8 First-order proof by inference

The chapter extends proof-producing tableaux to full first-order logic with equality. Search introduces fresh metavariables for universals and uses unification, but delays theorem construction until a successful branch supplies the final substitution, avoiding kernel work on failed branches. Dynamic Skolemization is harder because Skolemized and original formulas are only equisatisfiable, not equivalent in the reconstruction direction. The algorithm therefore records temporary Skolem hypotheses, builds a theorem conditional on them, then replaces ground Skolem terms by fresh variables and eliminates the assumptions using the drinker principle. After assigning consistent Skolem functions, iterative deepening supplies completeness: the resulting `lcffol` produces kernel theorems for valid formulas. The architecture cleanly separates speculative search state—environments, depth limits, Skolem choices—from the final checked derivation.

### 6.9 Interactive proof styles

Goals are represented together with a justification function that reconstructs the final theorem from proofs of current subgoals. Basic tactics introduce implications and quantifiers, split conjunctions, provide existential witnesses, eliminate existential and disjunctive assumptions, add labelled lemmas, and invoke first-order automation on selected hypotheses. This first supports procedural scripts: sequences of state-transforming tactics. The chapter then builds a more readable Mizar-inspired declarative layer—`assume`, `fix`, `consider`, `take`, `have`, `note`, `conclude`, and `qed`—whose annotations are checked parts of the proof rather than comments. A worked monotonicity proof shows users exposing just enough structure for automation. The closing efficiency discussion contrasts direct proof production with search followed by certificate checking and considers reflection as a way to add verified computation without enlarging the trusted kernel casually.

## 7. Limitations

The chapter turns from successful automation to impossibility. By encoding syntax, proofs, and machine computations as natural numbers, arithmetic can express facts about its own formulas and algorithms. Diagonal fixed points then yield Tarski’s undefinability of truth and Gödel’s incompleteness theorems; a precise Turing-machine model and the correspondence between computability and arithmetical definability lead to Church’s undecidability theorem for first-order validity.

These are not isolated paradoxes but a connected boundary theory. The chapter distinguishes truth, provability, definability, recursive enumerability, and decidability; shows how very weak arithmetic already supports the encodings; and surveys stronger consequences such as the second incompleteness theorem, the negative solution of Hilbert’s tenth problem, Rosser’s improvement, and essential undecidability. The final perspective is that formal proofs may be mechanically checkable even though no algorithm can find or settle all truths in sufficiently expressive systems.

### 7.1 Hilbert’s programme

Foundational crises over irrational numbers, infinitesimals, complex numbers, non-Euclidean geometry, and Cantorian infinity sharpened the conflict between classical and constructive mathematics. Brouwer’s intuitionism rejected unrestricted excluded middle and double-negation elimination, while Hilbert sought to preserve classical “ideal” methods by proving, through elementary metamathematics, that they could not yield false concrete conclusions. Because formal proofs are finite strings—and hence encodable as numbers—Hilbert proposed studying proof systems themselves inside weak, finitary mathematics, effectively bootstrapping stronger theories from an accepted base. The programme stimulated proof theory and important positive results, but it also set the stage for Gödel and related limitative theorems showing that sufficiently rich formal systems cannot supply all the completeness and self-justification Hilbert hoped for.

### 7.2 Tarski’s theorem on the undefinability of truth

Working in the standard natural numbers with `0`, successor, addition, multiplication, and order, the section defines relations and functions arithmetically through formulas. It assigns injective Gödel numbers to strings, terms, and formulas using pairing and list encodings, then shows that elementary operations on syntax—including diagonal substitution—are arithmetically definable. The fixed-point lemma follows: for any one-variable formula `P(x)`, there is a sentence `φ` such that `φ ↔ P(⌜φ⌝)` is true in the standard model. Applying it to a hypothetical truth predicate `Tr` gives `φ ↔ ¬Tr(⌜φ⌝)`, contradicting the claim that `Tr` recognizes exactly true sentences. Thus arithmetic truth is not arithmetically definable. The argument is a rigorous semantic-liar construction whose force depends on self-reference being generated by a definable syntactic transformation, not assumed informally.

### 7.3 Incompleteness of axiom systems

Unlike truth, formal provability from a definable axiom set is definable. The section arithmetizes well-formed terms and formulas, freedom side conditions, every primitive axiom schema, modus ponens, and generalization. Reflexive-transitive closure over encoded proof states then defines `Pr_A(n)`, true exactly when `n` codes a consequence of `A`. Tarski’s theorem immediately implies a weak incompleteness result: a definable axiom set cannot have exactly all truths of the standard natural numbers; if its axioms are sound, some true sentence is unprovable. Universal closure turns this into theory incompleteness—there is a sentence neither provable nor refutable. Finite axiom sets and ordinary finite schema presentations, including Peano arithmetic’s induction schema, satisfy the required definability condition, so the limitation applies to conventional formal foundations rather than exotic systems only.

### 7.4 Gödel’s incompleteness theorem

Applying the fixed-point lemma to the definable provability predicate constructs a Gödel sentence `G` satisfying `G ↔ ¬Pr_A(⌜G⌝)`: it asserts its own unprovability. The section refines the argument through the arithmetical hierarchy. Bounded-quantifier `Δ₀` sentences are decidable by finite evaluation; `Σ₁` formulas have only positive unbounded existential force and are semidecidable by searching a common witness bound; `Π₁` is the dual class. Provability from a `Σ₁`-definable axiom set is `Σ₁`, so `G` is `Π₁`. If `A` is `Π₁`-sound, `G` is true but unprovable; if also `Σ₁`-sound, its negation is unprovable. Assuming the realistic property of `Σ₁`-completeness, mere consistency already ensures the first half. This sharpens “truth is not axiomatizable” into a concrete independent sentence tailored effectively to the axiom system.

### 7.5 Definability and decidability

To formalize “effective method,” the section defines Turing machines with a finite state set, a two-way infinite binary tape, and a finite transition map, then gives explicit OCaml representations of configurations, execution, unary input, and output. Programs may compute partial functions by diverging where the function is undefined. Machine configurations and one-step transitions can themselves be encoded by `Δ₀` arithmetic formulas; reachability is `Σ₁`, so the graph of every partial computable function is `Σ₁`-definable. Conversely, true `Σ₁` formulas can be recognized by systematic witness search, establishing the correspondence between recursively enumerable relations and `Σ₁` definability. A set is decidable exactly when both it and its complement are recursively enumerable, equivalently when it has both `Σ₁` and `Π₁` definitions. This bridge converts logical definability results into impossibility results about programs.

### 7.6 Church’s theorem

The finite Robinson arithmetic theory `Q` supplies very weak but sufficient axioms for successor, addition, multiplication, and order—so weak that it cannot prove every familiar universal arithmetic identity. The text nevertheless constructs an LCF-certified `Σ₁` prover: ground terms are evaluated to numerals; true and false equalities are proved from `Q`; connectives and inequalities are reduced to canonical forms; and bounded universal quantifiers are handled by induction performed externally in the proof-producing algorithm, not assumed as an axiom of `Q`. Hence every true `Σ₁` sentence is provable from `Q`. If unprovability from a sound, `Σ₁`-complete theory were recursively enumerable, it would be `Σ₁`-definable, and a fixed point would contradict soundness and completeness; therefore provability is undecidable. Removing finitely many axioms preserves undecidability, so stripping finite `Q` down to pure logic proves Church’s theorem: first-order logical validity is not recursive.

### 7.7 Further limitative results

The section surveys consequences and sharpenings of the core results. Gödel’s second theorem, via the Hilbert–Bernays–Löb derivability conditions, says a sufficiently strong consistent theory cannot prove its own naturally represented consistency; Löb’s theorem generalizes the argument. Reflection principles can strengthen a theory but depend delicately on the chosen provability representation and may be iterated only with care. The Davis–Putnam–Robinson–Matiyasevich theorem identifies recursively enumerable sets with Diophantine ones, giving the negative solution to Hilbert’s tenth problem, while definability of integers in the rationals transfers broad undecidability there (leaving the purely existential rational problem open in the book’s account). Further reductions sharpen Church’s theorem to small prefixes and signatures. Rosser removes the extra soundness assumption from two-sided incompleteness, and Robinson arithmetic is shown essentially—and, through finite axiomatization, strongly—undecidable.

### 7.8 Retrospective: the nature of logic

The retrospective asks what unifies the book’s subject. Logic is broader than traditional mathematics because an explicit quantified language exposes general patterns behind particular algorithms, yet narrower because it studies consequences that depend only on form and stated axioms. A deeper candidate is mechanical checkability: a fully detailed proof should be verifiable without hidden subject knowledge, in principle by a clerk or machine. First-order proof checking satisfies this ideal, even though Church’s theorem prevents a decision procedure for all first-order validity. Arithmetic and stronger systems go further: Tarski and Gödel show that no fixed effective proof system captures every truth of their intended structures. Automated proving and checking therefore have philosophical force precisely because they clarify both sides of the boundary—what formal inference can certify and what no algorithmic method can exhaust.

## Appendix 1. Mathematical background

This appendix collects the mathematical vocabulary used throughout the book rather than developing a separate theory. It reviews notation; sets and their operations; relations, orders, and equivalence classes; functions, images, inverses, and cardinality; and the behavior of finite and infinite sets. Its most structurally important topics are inductive definitions and well-founded relations. The Knaster–Tarski viewpoint explains why positive closure rules determine a least set and justify rule induction, while well-founded induction, lexicographic orders, and multiset orders provide the termination principles later used for recursive definitions and rewriting.

## Appendix 2. OCaml made light of

This appendix is a compact orientation to the functional subset of OCaml used in the implementations. It introduces the toplevel, expressions and persistent definitions, curried and higher-order functions, recursion, static typing with inferred polymorphism, algebraic and recursive datatypes, pattern matching, exceptions, and lists. It then catalogs the book’s shared utility code: arbitrary-precision arithmetic helpers, list operations, list-based finite sets, generation of finite combinations, association lists, finite partial functions, and equivalence-relation partitions. The aim is to make the prover code readable and modifiable without requiring a full OCaml course.

## Appendix 3. Parsing and printing of formulas

The final appendix generalizes Chapter 1’s concrete-syntax machinery into reusable support for the book’s logical languages. Parser combinators handle atomic items, lists, and left- or right-associative infix operators with precedence; formula parsers layer connectives and quantifiers over a configurable atom parser. Pretty-printers use OCaml’s `Format` facilities to preserve grouping while introducing sensible line breaks, and are parameterized over atomic-formula printers. Specialized front ends then parse and print first-order terms and formulas while tracking bound variables and distinguishing constants, variables, function applications, predicates, and infix notation.
