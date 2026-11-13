# Formalizing the p-subtame Hom theorem

English implementation plan for an AI executor. Revision 3, 13 November 2026 (JST).

## How to use this file

This file contains the target, task checklist, implementation order, file layout,
all task contracts and the detailed mathematical proofs. Update this file
in place. No companion plan, task cards, JSON registry, progress script,
archive, document converter or TeX/PDF compilation is required.

1. Read the exact target below. Preserve Stacks as canonical on every overlap.
2. Select an unfinished task whose prerequisite IDs are VERIFIED. Initially select I01.
3. Read its contract under its task ID, then the linked proof section in this same file.
4. Implement the actual mathematical objects and maps; reuse existing proved declarations.
5. Check the exact theorem type, the task's acceptance conditions, relevant Lean build and axiom/import closure.
6. Update that task's single checklist row with its state and concise evidence. Continue to the next ready task.

All build or compilation requirements below concern Lean only. Do not build or
regenerate documents during implementation. IDs identify proof obligations;
they do not prescribe one file per obligation.

**Current status:** source review and planning are complete; **0 of 80 Lean
implementation tasks are VERIFIED**. No new Lean proof or combined kernel build
has been executed as part of this planning work.

### Progress rules

The checklist below is the sole progress record. States are TODO, DOING,
BLOCKED, WRITTEN and VERIFIED. Check a box only for VERIFIED. WRITTEN means the
code exists but a required check remains. For BLOCKED, state the precise failed
obligation and what would resolve it. Waiting for a prerequisite is not itself
a mathematical obstruction.

For VERIFIED, record the actual declaration, source revision or checked working
snapshot, and the successful Lean check in the evidence column. A brief note is
enough; do not create a separate reporting system. Reopen affected tasks when
their statement, implementation or proof dependencies change. Recheck only the
relevant changed closure; the final clean dependency build belongs to I15.

The common completion conditions are: the exact intended statement is proved;
all prerequisite obligations are discharged; actual maps agree as specified;
all task-specific checks pass; the relevant Lean build succeeds; and the
actual dependency closure contains no sorryAx, new mathematical axiom or
conclusion hidden in an input structure. Standard logical axioms are the
accepted baseline. Keep diagnostics out of finished mathematical modules.

## Exact target


### Public conclusion

For every prime p, every characteristic-zero p-subtame field K, every normal,
geometrically integral finite-type K-scheme X, and every smooth geometrically
connected hyperbolic K-curve Y, construct

    Hom_K^dom(X,Y) ≃ Hom_GK^continuous,open(Pi_X,Pi_Y) / Inn(Delta_Y).

The left side contains actual dominant morphisms over Spec K. The right side
contains actual continuous homomorphisms with open image commuting with the
maps to the same absolute Galois group G_K. The quotient is by conjugation by
the geometric subgroup Delta_Y. X need not be separated. Y is separated and
has the specified smooth proper compactification and finite boundary.

Do not replace this target by an Isom theorem, by equality of abelianizations,
or by a theorem with an unproved reconstruction package in its hypotheses.

### Field predicate

`IsPSubtame p K` means there exist a Henselian discretely valued field F of
mixed characteristic (0,p) and an embedding K -> F^tame. F^tame is the maximal
algebraic tamely ramified extension in a chosen separable closure.

K is not required to be complete, discretely valued or finitely generated.
The residue field of F is not required to be finite or perfect. Complete
auxiliary hosts must be constructed, not added as assumptions on K.
Neither a presentation structure nor a typeclass may contain the Hom theorem,
Tate extension or reconstruction conclusion as a field.

### Fundamental groups

Use the actual arithmetic etale fundamental group and its actual geometric
kernel D_X. Put R_X = ker(D_X -> D_X^(p)), Delta_X = D_X^(p), and
Pi_X = pi_1^et(X)/R_X. Prove the actual sequence

    1 -> Delta_X -> Pi_X -> G_K -> 1.

Do not take the pro-p quotient of the whole arithmetic group. Retain all of
G_K and prove actual cover, pullback and base-point compatibility. Preserve
the opposite-deck convention until an explicit inversion changes it.

### Required exported obligations

1. `dominant_induces_open`: the map induced by each dominant K-morphism is
   continuous, open and over G_K.
2. `exists_dominant_realizing`: for every prescribed open theta there are a
   dominant f and one c in Delta_Y comparing f_* and theta on all of Pi_X.
3. `dominant_hom_injective`: equality of geometric conjugacy classes implies
   equality of actual K-morphisms.
4. `pSubtameHomEquiv`: package these into the displayed equivalence and prove
   that its forward map is the one induced by the morphism.

These are proposed public names. Freeze their actual Lean types before use.

### Quantifiers and edge cases

| ID | Required invariant |
| --- | --- |
| Q01 | Every prime p, including p=2. No odd-prime assumption on the endpoint. |
| Q02 | F^tame is algebraic; an auxiliary completion does not redefine p-subtame. |
| Q03 | Separably closed residue is not replaced by perfect residue. |
| Q04 | Auxiliary finite local models need not contain K. All objects live in a specified common algebraic closure where required. |
| Q05 | For each finite cover or finite diagram there exists a suitable finite local stage. Do not require one stage for infinitely many covers. |
| Q06 | One formal point is fixed across all finite Kummer levels. |
| Q07 | For each precision there exists an approximation point. Approximation points may vary with precision. |
| Q08 | There exists one geometric conjugator that works for every element of the entire arithmetic group. Finite-level conjugators are joined by compactness. |
| Q09 | Normal geometrically integral finite-type sources may have any finite dimension and need not be separated. Treat dimension zero explicitly. |
| Q10 | Open hyperbolic targets are included; identify actual residue maps with cusp inertia, not only their ranks. |
| Q11 | Interpret 2g-2+r>0 in integers or an equivalent valid natural inequality. Do not use truncated subtraction. |
| Q12 | Negative p-exponents and fractional differential lattices are interpreted in the correct fraction field. |

### Actual-map interfaces

At each interface, prove the named maps commute: finite cover versus quotient;
torsor versus character; Abel-Jacobi pullback versus multiplication-cover
monodromy; Tate quotient versus actual torsion; integral formal map versus its
division maps; Picard correction versus both Kummer class and differential;
linearization versus actual algebraic differential; reconstruction versus deck
action; and arithmetic torsor comparison versus identity on constant covers.

Coefficient naturality does not imply scheme-pullback naturality. An abstract
isomorphism with the right domain and codomain does not identify the actual map.



## Stages and checklist

All 80 rows start TODO. The source contains 65 statements; I01-I15 are the additional integration and assembly obligations. Stage numbers organize review; the prerequisite IDs in each task determine readiness.

| Stage | Goal | Task IDs |
| --- | --- | --- |
| 0 | Canonical integration | I01 |
| 1 | Actual covers and arithmetic groups | S04, S05, S06, S07, S09, S10, S11, I02, I03, I04 |
| 2 | p-subtame fields | S01, S02, S48, S58, S60 |
| 3 | Formal-group foundations | S12, S13, S14, S15, S16, S17, I05, I06 |
| 4 | Integral Tate extension | S18, S19, S20, S21, S22, S36 |
| 5 | Fixed Picard models | S23, S24, S25, S26, S27, S28, S29, S30, S31, I07 |
| 6 | Inertia and linearization | S32, S33, S34, S35, S37, S38, S39, S40, I08 |
| 7 | Kummer transfer and approximation | S41, S42, S43, S44, S45, S46, S47, S49, I09 |
| 8 | Geometric reconstruction | S50, S51, S52, S53, S54 |
| 9 | Proper curve Hom and arithmetic recovery | S08, S55, S56, S57, S59, I10, I11 |
| 10 | General normal finite-type sources | S61, S62, S63, I12, I13, I14 |
| 11 | Open targets and exact final equivalence | S03, S64, S65 |
| 12 | Final acceptance | I15 |

| Done | Task | Stage | State | Evidence or blocker |
| --- | --- | --- | --- | --- |
| [ ] | [I01](#i01) Reconcile every overlapping owner before mixed imports | 0 | TODO | — |
| [ ] | [I02](#i02) Build the actual arithmetic relative-pro-p exact sequence | 1 | TODO | — |
| [ ] | [I03](#i03) Prove the missing scheme-pullback naturality of finite H1 | 1 | TODO | — |
| [ ] | [I04](#i04) Prove dominant scheme maps induce open arithmetic images | 1 | TODO | — |
| [ ] | [S04](#s04) Compare actual finite-etale fibre functors | 1 | TODO | — |
| [ ] | [S05](#s05) Detect a single conjugator using all finite quotients | 1 | TODO | — |
| [ ] | [S06](#s06) Realize a finite geometric quotient after one constant extension | 1 | TODO | — |
| [ ] | [S07](#s07) Identify relative pro-p groups of actual finite covers | 1 | TODO | — |
| [ ] | [S09](#s09) Recover full arithmetic equality from finite torsors with constants fixed | 1 | TODO | — |
| [ ] | [S10](#s10) Prove ramification and logarithmic Euler-characteristic formulas | 1 | TODO | — |
| [ ] | [S11](#s11) Equate arithmetic and geometric openness | 1 | TODO | — |
| [ ] | [S01](#s01) Define the exact p-subtame field predicate | 2 | TODO | — |
| [ ] | [S02](#s02) Construct a complete tame host and prove field-class closure | 2 | TODO | — |
| [ ] | [S48](#s48) Construct algebraic pro-p test fields | 2 | TODO | — |
| [ ] | [S58](#s58) Descend invariant rational coefficients by a minimal denominator | 2 | TODO | — |
| [ ] | [S60](#s60) Preserve regularity with a translated pencil | 2 | TODO | — |
| [ ] | [I05](#i05) Fix coordinate formal groups and the actual finite-level Tate comparison | 3 | TODO | — |
| [ ] | [I06](#i06) Show division ideals separate actual formal series | 3 | TODO | — |
| [ ] | [S12](#s12) Construct actual formal division groups from a semiabelian model | 3 | TODO | — |
| [ ] | [S13](#s13) Construct and invert the logarithm on the p-squared ball | 3 | TODO | — |
| [ ] | [S14](#s14) Take finite-flat subgroup closures and quotients | 3 | TODO | — |
| [ ] | [S15](#s15) Construct smooth finite-height quotients of formal groups | 3 | TODO | — |
| [ ] | [S16](#s16) Characterize bounded logarithms and retain the explicit denominator | 3 | TODO | — |
| [ ] | [S17](#s17) Lift integral curves through a finite generic embedding | 3 | TODO | — |
| [ ] | [S18](#s18) Prove uniform bounded projection of p-typical logarithmic curves | 4 | TODO | — |
| [ ] | [S19](#s19) Uniformly annihilate the scheme-theoretic special kernel | 4 | TODO | — |
| [ ] | [S20](#s20) Solve descending complete-local cosets and control intersections | 4 | TODO | — |
| [ ] | [S21](#s21) Identify the closed formal graph from finite graph approximations | 4 | TODO | — |
| [ ] | [S22](#s22) Extend every equivariant Tate map to a unique integral formal map | 4 | TODO | — |
| [ ] | [S36](#s36) Detect a characteristic-zero formal homomorphism by its differential | 4 | TODO | — |
| [ ] | [I07](#i07) Construct a split semistable model and prove the horizontal node-divisor formula | 5 | TODO | — |
| [ ] | [S23](#s23) Trivialize a generically trivial line bundle with nonpositive component degrees | 5 | TODO | — |
| [ ] | [S24](#s24) Represent relative Picard classes by uniquely rigidified line bundles | 5 | TODO | — |
| [ ] | [S25](#s25) Construct the multidegree-zero Picard algebraic space of a fixed model | 5 | TODO | — |
| [ ] | [S26](#s26) Identify the actual finite Abel–Jacobi maps and their Tate limit | 5 | TODO | — |
| [ ] | [S27](#s27) Identify Jacobian invariant differentials with curve differentials, naturally | 5 | TODO | — |
| [ ] | [S28](#s28) Classify multiplicative-group covers and identify section differences with Kummer classes | 5 | TODO | — |
| [ ] | [S29](#s29) Lift and realize Kummer torsors over a strictly Henselian base | 5 | TODO | — |
| [ ] | [S30](#s30) Correct any Jacobian point by a constant in one fixed integral model | 5 | TODO | — |
| [ ] | [S31](#s31) Construct fixed Jacobian and multiplicative models with connected finite torsion | 5 | TODO | — |
| [ ] | [I08](#i08) Detect prime-to-p actions modulo p on saturated invariant lattices | 6 | TODO | — |
| [ ] | [S32](#s32) Prove a uniform exponent for unramified connected finite p-groups | 6 | TODO | — |
| [ ] | [S33](#s33) Generate a connected BT Tate representation by inertia differences | 6 | TODO | — |
| [ ] | [S34](#s34) Characterize the connected Tate lattice intrinsically | 6 | TODO | — |
| [ ] | [S35](#s35) Prove inertia differences lie in connected formal torsion | 6 | TODO | — |
| [ ] | [S37](#s37) Realize Tate maps integrally and prove nonvanishing of their differential | 6 | TODO | — |
| [ ] | [S38](#s38) Compare formal and algebraic differentials using finite torsion graphs | 6 | TODO | — |
| [ ] | [S39](#s39) Descend all equivariant Tate maps to a uniform finite local stage | 6 | TODO | — |
| [ ] | [S40](#s40) Define a model-independent linearization over the fixed algebraic closure | 6 | TODO | — |
| [ ] | [I09](#i09) Discharge the auxiliary-cover transfer hypothesis over the fixed p-subtame test field | 7 | TODO | — |
| [ ] | [S41](#s41) Transfer finite Kummer images through actual torsor pushouts | 7 | TODO | — |
| [ ] | [S42](#s42) Embed a curve function field into a Gauss completion with a bounded derivation | 7 | TODO | — |
| [ ] | [S43](#s43) Define logarithmic derivatives as actual tangent vectors | 7 | TODO | — |
| [ ] | [S44](#s44) Use one formal point for all finite Kummer levels and its derivative | 7 | TODO | — |
| [ ] | [S45](#s45) Derive the exact p^n differential congruence in one fixed lattice | 7 | TODO | — |
| [ ] | [S46](#s46) Trivialize an abelian torsor from finite section precision and a degree bound | 7 | TODO | — |
| [ ] | [S47](#s47) Obtain a curve point from a degree-one Picard class by determinant cancellation | 7 | TODO | — |
| [ ] | [S49](#s49) Approximate point sections at each finite precision using all auxiliary covers | 7 | TODO | — |
| [ ] | [S50](#s50) Generate the canonical affine chart by ratios and first derivatives | 8 | TODO | — |
| [ ] | [S51](#s51) Recover an exact algebra map from independent finite-precision values | 8 | TODO | — |
| [ ] | [S52](#s52) Reconstruct a unique nonconstant point from one bounded derivation | 8 | TODO | — |
| [ ] | [S53](#s53) Prove faithfulness of differential pullback in arbitrary source dimension | 8 | TODO | — |
| [ ] | [S54](#s54) Assemble an actual geometric curve map from Picard and Kummer approximation | 8 | TODO | — |
| [ ] | [I10](#i10) Identify proper base change with the actual arithmetic fibre-product group | 9 | TODO | — |
| [ ] | [I11](#i11) Glue the separated-source Hom theorem over a nonseparated curve | 9 | TODO | — |
| [ ] | [S08](#s08) Reduce open Hom to surjective Hom without losing uniqueness | 9 | TODO | — |
| [ ] | [S55](#s55) Kill the full geometric image of every multiplicative-source homomorphism | 9 | TODO | — |
| [ ] | [S56](#s56) Factor maps from open or generic source curves through compactification | 9 | TODO | — |
| [ ] | [S57](#s57) Prove full Hom for proper targets and all smooth finite-type source curves | 9 | TODO | — |
| [ ] | [S59](#s59) Descend the reconstructed proper-curve map and recover the whole arithmetic map | 9 | TODO | — |
| [ ] | [I12](#i12) Give connected finite-etale covers their relative constant-field structures | 10 | TODO | — |
| [ ] | [I13](#i13) Handle dimension zero and preserve dominance under rational-variable descent | 10 | TODO | — |
| [ ] | [I14](#i14) Assemble proper-target full Hom for all normal finite-type sources | 10 | TODO | — |
| [ ] | [S61](#s61) Choose one curve reduction uniformly for all finite geometric covers | 10 | TODO | — |
| [ ] | [S62](#s62) Remove all rational variables from a point of a positive-genus proper curve | 10 | TODO | — |
| [ ] | [S63](#s63) Extend a generic-point map using finite abelian covers of a normal source | 10 | TODO | — |
| [ ] | [S03](#s03) Export the exact p-subtame full Hom equivalence | 11 | TODO | — |
| [ ] | [S64](#s64) Identify actual cusp inertia and construct one proper-hyperbolizing cover | 11 | TODO | — |
| [ ] | [S65](#s65) Reduce open-target full Hom to the proper-target theorem on finite covers | 11 | TODO | — |
| [ ] | [I15](#i15) Certify the final public theorem and its actual checked dependency closure | 12 | TODO | — |

## Stacks first and the Lean layout

Use one independent `MochizukiHom` Lake project. Mathlib is the common upstream;
Stacks owns overlapping definitions, instances, categories, functors and
results. Adapt only the additional NYLL proof closure that the implementation
actually needs, preserving origin and license information in normal source
attribution. The raw NYLL and Stacks closures cannot simply be co-imported:
both declare the global `RingHom.FiniteEtale` and overlapping stability
instances. I01 reconciles those owners and explicitly fixes the universe scope.

The following 21 modules are a compact starting layout for the new mathematics.
Create a module when its first proof is implemented; do not pre-create empty
files. Several task IDs belong to one coherent file. Definitions and early
lemmas in that file precede later ones. The induced module dependency graph is
acyclic. Necessary adapted dependency source files are separate from this list;
do not copy unused library files. I15 checks the existing public entry point and
creates no permanent acceptance module.

Only split a module if its actual proof size or import boundary requires it.
Keep one active writer per module when delegating. Preserve NYLL's existing
publication/import-depth rules; do not silently relax them to admit Stacks.

| Module relative to `MochizukiHom/` | Task IDs |
| --- | --- |
| `Compat/Foundations.lean` | I01, S04, I03 |
| `Profinite/Basic.lean` | S05, S06, S11, I08 |
| `Fields/Basic.lean` | S01, S02, S48, S58, S60 |
| `FundamentalGroup/Basic.lean` | I02, S07, S09, I04, I10, I12 |
| `Curves/Basic.lean` | S10, S50, S53, S62 |
| `FormalGroups/Basic.lean` | I05, I06, S12, S13, S36 |
| `FormalGroups/Quotients.lean` | S14, S15, S16, S17, S20 |
| `FormalGroups/TateExtension.lean` | S18, S19, S21, S22 |
| `Picard/Model.lean` | I07, S23, S24, S25, S29, S30, S31 |
| `Picard/AbelJacobi.lean` | S26, S27, S28 |
| `Picard/Inertia.lean` | S32, S33, S34, S35 |
| `Picard/Linearization.lean` | S37, S38, S39, S40 |
| `Kummer/FormalPoints.lean` | S41, S43, S44, S45 |
| `Kummer/Approximation.lean` | S46, S47, S49 |
| `Reconstruction/FiniteValues.lean` | S51, S52 |
| `Reconstruction/CurveMap.lean` | S42, I09, S54 |
| `Hom/ArithmeticRecovery.lean` | S59 |
| `Hom/ProperCurves.lean` | S08, S55, S56, I11, S57 |
| `Hom/NormalSources.lean` | S61, S63, I13, I14 |
| `Hom/OpenTargets.lean` | S64, S65 |
| `Main.lean` | S03 |

### Dependency boundaries that matter

I11 proves nonseparated gluing conditional on the separated-source theorem;
S57 supplies that theorem. S49 is the abstract point-approximation statement;
I09 supplies its all-cover transfer hypothesis. S65 is the open-target
reduction conditional on proper-cover Hom; S03 discharges that hypothesis.
None of these reductions may import the final theorem it helps prove.
S07 proves the early relative-cover facts it needs without depending on I12.
The basic formal-group lemmas used by S36 retain their characteristic-zero-domain
generality instead of inheriting complete-DVR hypotheses.

The additional implementation edges include S08 -> S10, S40 -> S39,
S44 -> S43, S52 -> S51 and S61 -> S60. Merely reading the manuscript's explicit
label references misses these dependencies.

## Task contracts

Each task records its mathematical prerequisites. I01 is also the workspace
integration prerequisite for every later task; it is not an extra mathematical
hypothesis of pure field or group lemmas. Proposed declaration names are naming
suggestions, not assertions that those APIs already exist. The detailed proofs
are included once, after these contracts.

### I01

**Reconcile every overlapping owner before mixed imports**

Stage 0. Owner: `MochizukiHom/Compat/Foundations.lean`
Prerequisites: none.
Detailed integration or acceptance proof: the steps below and the exact target/common completion rules above.

**Input.**
- Pinned Stacks and NYLL source revisions and their inspected transitive import closures.
- The user policy that Stacks owns all overlapping definitions, theorem statements and instances.

**Output.**
- One compiling independent MochizukiHom package with canonical Stacks finite-etale foundations and only the necessary adapted additional NYLL closure.
- A provenance/migration record of source path, commit, license, replacement declaration and intentional universe restriction.
- Reconcile the predicate and instances first in Compat/Foundations.lean; add S04 and I03 later in the same module without making the early declarations depend on the later ones.

**Proof steps.**
1. Pin Lean, mathlib, Stacks and the NYLL source revision.
2. Enumerate duplicate global names in the selected closure, starting with RingHom.FiniteEtale and its stability instances.
3. Retain the Stacks predicate and instances; prove the equivalence with the NYLL predicate using Algebra.finiteEtale_iff and the algebra-map comparison lemmas.
4. Port only the required additional NYLL proofs to the Stacks objects and choose a common geometric universe explicitly.
5. Compile the smallest combined target for cover, H1, Picard, arithmetic exact sequence and curve-cohomology interfaces before proceeding.

**Acceptance.**
- No duplicate RingHom.FiniteEtale declaration or instance reaches the build.
- The raw conflicting NYLL finite-etale foundation is absent from the import closure.
- The common-universe decision is recorded and no heterogeneous API is claimed without a lift theorem.
- Actual combined compilation evidence is required before completion; source inspection alone is insufficient.
- NYLL publication depth restrictions are retained; public low-level files are not silently changed.

**Exclude.** Trying to solve duplicate global constants by import order or a wrapper. Marking a source-level audit as a successful Lean integration build.

Proposed names: `finiteEtale_predicate_comparison`.

### I02

**Build the actual arithmetic relative-pro-p exact sequence**

Stage 1. Owner: `MochizukiHom/FundamentalGroup/Basic.lean`
Prerequisites: I01, S04.
Detailed integration or acceptance proof: the steps below and the exact target/common completion rules above.

**Input.**
- A geometrically connected qcqs K-scheme X with geometric base point above a chosen algebraic closure.
- The canonical Stacks arithmetic etale sequence and the actual absolute Galois-group presentation.

**Output.**
- Construct Dcal=pi1(X_Kbar), R=ker(Dcal -> Dcal^(p)), Delta_X=Dcal^(p), and Pi_X=pi1(X)/R.
- Prove R is normal in pi1(X) and the actual exact sequence 1 -> Delta_X -> Pi_X -> G_K -> 1, compatible with actual scheme maps.
- Supply the noetherian/qcqs bridge for every finite-type scheme over a field, including nonseparated X.

**Proof steps.**
1. Identify the field-fibre-functor automorphism group with the chosen absolute Galois group and prove map compatibility.
2. Use characteristicity of the maximal pro-p kernel in Dcal and normality of Dcal to prove normality in pi1(X).
3. Descend the arithmetic quotient map through R and calculate its kernel and surjectivity.
4. Define morphism maps by the functorial geometric pro-p quotient, with coherent base-point comparisons.
5. Derive qcqs from noetherianity for the final finite-type source class.

**Acceptance.**
- The arithmetic quotient is the full G_K, not its pro-p quotient.
- The sequence is attached to actual fibre functors and quotient maps.
- Nonseparated finite-type sources satisfy the interface without an extra assumption.
- Kernel maps and scheme-map naturality are named outputs.

**Exclude.** Replacing Pi_X with the maximal pro-p quotient of pi1(X). Introducing a circular dependency on S07 for the basic quotient sequence.

Proposed names: `absoluteGalois_fiberComparison`, `relativeProP_arithmeticExact`, `relativeProP_map`, `finiteType_overField_qcqs`.

### I03

**Prove the missing scheme-pullback naturality of finite H1**

Stage 1. Owner: `MochizukiHom/Compat/Foundations.lean`
Prerequisites: S04.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers).

**Input.**
- The actual finite-cover/fibre comparison S04 and finite constant abelian coefficient groups A.
- A scheme map f:X -> Y and a coefficient homomorphism A -> B.

**Output.**
- Commuting squares identifying the small-site and big-site degree-one torsor-character comparisons under scheme pullback and coefficient pushout.
- Compatibility for Z/p^(n+1) -> Z/p^n and for the maps used in finite Kummer constructions.

**Proof steps.**
1. Represent each degree-one class by an actual finite-etale A-torsor.
2. Identify f-pullback with the fibre-product torsor and coefficient change with the actual contracted-product torsor.
3. Read each construction on the same lift fibres and compare permutation characters.
4. Prove the two naturality directions separately and their joint coherence.

**Acceptance.**
- Both scheme and coefficient naturality squares are proved.
- The reduction maps in the p-power coefficient tower are instantiated.
- No higher-degree derived equivalence is assumed.

**Exclude.** Citing a coefficient-naturality theorem as if it also proved scheme naturality.

Proposed names: `finiteH1Comparison_pullback`, `finiteH1Comparison_coefficients`, `finiteH1Comparison_jointNaturality`.

### I04

**Prove dominant scheme maps induce open arithmetic images**

Stage 1. Owner: `MochizukiHom/FundamentalGroup/Basic.lean`
Prerequisites: I02, S04, S11.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom).

**Input.**
- A dominant K-morphism f:X -> Y of the actual finite-type normal geometrically integral source/curve objects appearing in the final theorem.
- The actual relative-pro-p arithmetic groups and their maps to G_K.

**Output.**
- The induced continuous homomorphism Pi_X -> Pi_Y has open image, and its geometric restriction has open image.
- The construction descends to the required geometric-conjugacy orbit and is independent of compatible base points.

**Proof steps.**
1. Inject K(Y) into K(X) and isolate its finite relative algebraic closure inside the finitely generated extension.
2. Use restriction along the resulting finite separable extension to obtain an open subgroup at the generic-point fundamental-group level.
3. Use normality and the finite-cover/function-field correspondence to relate generic-point maps to the actual scheme groups.
4. Descend through the geometric pro-p quotients and use S11 for the arithmetic/geometric comparison.
5. Prove base-point change induces precisely geometric conjugation.

**Acceptance.**
- The proof uses the actual function-field map of f and the actual cover pullback.
- Finite relative algebraic degree is proved from finite generation.
- X need not be separated.
- The forward map into the final orbit set is defined and its independence is proved.

**Exclude.** Assuming dominance alone gives surjectivity instead of openness. Using a finite-extension argument for an arbitrary transcendental function-field extension without the relative-constant step.

Proposed names: `dominant_induces_open`, `dominantHom_orbitMap`.

### S04

**Compare actual finite-etale fibre functors**

Stage 1. Owner: `MochizukiHom/Compat/Foundations.lean`
Prerequisites: I01.
Source: `lem:actual-fibre-presentation-comparison`, statement lines 343-360 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- A connected scheme X and an algebraically closed geometric point xi.
- Reconciled Stacks finite-etale objects and the required additional NYLL fibre-functor proofs. Compat/Foundations.lean from I01 owns the ring predicate bridge; this task exclusively owns Compat/Foundations.lean for the cover-category comparison.

**Output.**
- A topological group equivalence between the two inspected presentations of Aut(fibre xi), identifying their actions on each actual lift set.
- Naturality for scheme pullback and morphisms of finite covers, and identification of the finite-constant-torsor H1 characters.

**Proof steps.**
1. Transport both presentations to the category of actual finite-etale arrows Y -> X and commuting triangles.
2. Identify both fibres with lifts Spec Omega -> Y above xi.
3. Prove naturality of these bijections and conjugate natural automorphisms by them.
4. Prove continuity in both directions using stabilizers of finitely many fibre points.
5. Use fibre-product universality for pullback and actual torsor fibres for the degree-one comparison.

**Acceptance.**
- The equivalence acts on the actual lift set of every finite cover.
- Both directions are continuous with respect to the actual profinite topologies.
- Scheme-pullback and cover-morphism squares commute.
- Finite H1 is compared through torsors without assuming a derived-site equivalence.

**Exclude.** An abstract group equivalence without cover-action compatibility. Co-importing the two original duplicate RingHom.FiniteEtale declarations. Silently reversing deck-action conventions.

Proposed names: `finiteEtalePresentationEquivalence`, `fiberFunctorComparison`, `actualFundamentalGroupComparison`, `finiteTorsorCharacter_comparison`.

### S05

**Detect a single conjugator using all finite quotients**

Stage 1. Owner: `MochizukiHom/Profinite/Basic.lean`
Prerequisites: none.
Source: `lem:finite-conjugacy-detection`, statement lines 379-384 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- A profinite group P, a closed subgroup D, and continuous homomorphisms alpha,beta:H -> P.
- In each quotient in a cofinal family of finite quotients, alpha and beta are conjugate by some element of the image of D.

**Output.**
- There exists one c in D such that beta(h)=c alpha(h) c^(-1) for every h.
- The converse and the cofinal-family variant.

**Proof steps.**
1. For each open normal N, define the closed subset C_N of D by equality of the two homomorphisms modulo N after conjugation.
2. Prove nonemptiness using the finite-quotient hypothesis.
3. Use the quotient by an intersection of finitely many open normals to prove the finite intersection property.
4. Apply compactness of the closed subgroup D and then separation by all open normals.

**Acceptance.**
- The output quantifier order is exists c, for all h.
- No compatibility is assumed between chosen finite-level conjugators.
- Cofinality is explicitly used to recover all finite quotients.

**Exclude.** Selecting a different conjugator for each element of H. Replacing geometric conjugacy by unrestricted arithmetic conjugacy.

Proposed names: `finiteQuotient_conjugacy_iff`, `cofinalFiniteQuotient_conjugacy_iff`.

### S06

**Realize a finite geometric quotient after one constant extension**

Stage 1. Owner: `MochizukiHom/Profinite/Basic.lean`
Prerequisites: none.
Source: `lem:finite-geometric-quotient-descent`, statement lines 394-406 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- An exact sequence 1 -> D -> P -> Gamma -> 1 of profinite groups.
- An open normal subgroup N of D, with D carrying the induced topology.

**Output.**
- An open normal Gamma0 in Gamma, its inverse image P0 in P, and an open normal H in P0 satisfying H intersect D=N, HD=P0, and D/N = P0/H compatibly with quotient maps.
- All intermediate subgroups of D/N are realized at that same constant stage.

**Proof steps.**
1. Choose an open normal B in P with B intersect D contained in N.
2. Set P0=DB and H=NB.
3. Use [B,D] contained in B intersect D to show that B normalizes N and acts trivially on D/N.
4. Prove H is open normal in P0, compute H intersect D, and apply the second isomorphism theorem.
5. Prove the image Gamma0 of B is open normal by the quotient topology and identify its inverse image.

**Acceptance.**
- The finite quotient comparison includes the actual commuting quotient square.
- Gamma0 is open and normal, giving one finite Galois extension in the arithmetic application.
- N need not be normal in the original P.

**Exclude.** Assuming N is stable under all arithmetic conjugation. Choosing a separate constant extension for each intermediate subgroup.

Proposed names: `finiteGeometricQuotient_constantDescent`.

### S07

**Identify relative pro-p groups of actual finite covers**

Stage 1. Owner: `MochizukiHom/FundamentalGroup/Basic.lean`
Prerequisites: I02, S04.
Source: `lem:relative-p-cover-exact`, statement lines 419-429 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- A profinite group Dcal with maximal pro-p quotient Delta and kernel R.
- An open subgroup J in Delta and its inverse image Hcal.
- For the geometric application, an actual relative-pro-p arithmetic group and an open subgroup H.

**Output.**
- The maximal pro-p quotient of Hcal is J and its kernel is exactly the same R.
- The actual connected finite-etale cover Xprime -> X attached to H, considered over its arithmetic constant field Kprime, has Pi_Xprime=H and Delta_Xprime=H intersect Delta_X, with compatible actual cover maps.

**Proof steps.**
1. For each open normal p-power-index U in Hcal, take finite intersections C of conjugates of Hcal and V of conjugates of U.
2. Identify Dcal/C with a finite p-group quotient of Delta.
3. Embed C/V into a finite product of Hcal/U and deduce Dcal/V is a p-group.
4. Deduce R contained in every U; use Hcal/R=J to obtain equality of pro-p kernels.
5. Apply the actual open-subgroup-cover equivalence and the arithmetic-image constant-field description; transport the geometric kernel calculation.

**Acceptance.**
- The cover-group identification is compatible with the actual map to X.
- No p-power restriction is imposed on [Kprime:K].
- The same R is proved to be the pro-p kernel, not merely contained in it.
- Relative-constant facts needed here are proved as stage-1 cover lemmas, not imported from later I12.

**Exclude.** Taking the total pro-p quotient of the arithmetic group. Introducing a dependency on the later general relative-constants task I12 and creating a cycle.

Proposed names: `openSubgroup_relativeProP_kernel`, `relativeProPCover_groupEquivalence`.

### S09

**Recover full arithmetic equality from finite torsors with constants fixed**

Stage 1. Owner: `MochizukiHom/FundamentalGroup/Basic.lean`
Prerequisites: I02, S04, S05.
Source: `lem:finite-torsor-comparison`, statement lines 463-484 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- Geometrically connected K-schemes X,Y, quotient maps q_Z:pi1(Z) -> P_Z by closed normal subgroups of the geometric kernels, and their actual maps to G_K.
- A continuous theta:P_X -> P_Y over G_K and a K-morphism f:X -> Y.

**Output.**
- Equality of q_Y f_* and theta q_X up to one D_Y-conjugator is equivalent to A_N-equivariant isomorphisms of their actual pulled-back torsors for a cofinal family of N, inducing the identity on the constant quotient.
- Under this condition q_Y f_* kills R_X and factors through P_X.

**Proof steps.**
1. Construct the actual Galois torsor V_N for P_Y/N and its theta-pullback W_N.
2. Identify the quotient by the geometric image with X base-changed to the finite constant field E_N.
3. Read an equivariant torsor isomorphism on a geometric fibre as a finite conjugator.
4. Prove identity on the constant quotient is exactly membership of that conjugator in the geometric image.
5. Apply S05 and prove factorization through P_X by killing R_X.

**Acceptance.**
- Every comparison is A_N-equivariant and is the identity on the stated constant cover.
- W_N may be disconnected and no coherent choice over all N is required.
- The final conjugator lies in D_Y and works on all of pi1(X).
- The deck-opposite conversion is proved explicitly.

**Exclude.** Checking only geometric torsors after forgetting constants. Assuming connectedness of W_N or introducing a compatibility hypothesis absent from the source.

Proposed names: `arithmeticHom_eq_iff_finiteTorsorComparison`, `arithmeticHom_factor_of_torsorComparison`.

### S10

**Prove ramification and logarithmic Euler-characteristic formulas**

Stage 1. Owner: `MochizukiHom/Curves/Basic.lean`
Prerequisites: none.
Source: `lem:curve-local-differential-degree`, statement lines 494-506 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- A characteristic-zero field k and a nonconstant map f:Cprime -> C of smooth proper geometrically connected curves.
- The actual function-field degree d, and optionally a finite reduced divisor D in C over an algebraic closure, with Dprime the reduced inverse image.

**Output.**
- 2g(Cprime)-2 = d(2g(C)-2) + sum_x(e_x-1).
- 2g(Cprime)-2+#Dprime >= d(2g(C)-2+#D), with equality when f is etale outside D.

**Proof steps.**
1. Base change to an algebraic closure and prove f finite flat of degree d using torsion-free modules over target DVRs.
2. Write f* t=u s^e and compute its differential; prove the coefficient e u+s du/ds is a unit.
3. Identify the divisor of the differential line-bundle map and take degrees using deg omega=2g-2.
4. Use fibre lengths sum e_x=d and split the ramification sum into points above D and outside D.

**Acceptance.**
- The formulas use integer arithmetic, not truncated natural subtraction.
- Genus and boundary cardinalities belong to the actual compactifications.
- The local order is proved to be e_x-1 in characteristic zero.
- The inequality specializes to preservation of hyperbolicity under finite-etale covers.

**Exclude.** Using a numerical genus/cusp record unconnected to a curve. Applying the tame differential formula in positive characteristic without its hypotheses.

Proposed names: `curve_ramification_degree_formula`, `logEulerCharacteristic_pullback_inequality`, `hyperbolic_finiteEtale_cover`.

### S11

**Equate arithmetic and geometric openness**

Stage 1. Owner: `MochizukiHom/Profinite/Basic.lean`
Prerequisites: none.
Source: `lem:arithmetic-geometric-open-equivalent`, statement lines 527-537 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- Exact profinite sequences 1 -> D_i -> P_i -> G -> 1 for i=1,2.
- A continuous homomorphism theta:P_1 -> P_2 commuting with the maps to G.

**Output.**
- For H=theta(P_1), prove H intersect D_2=theta(D_1), HD_2=P_2 and [P_2:H]=[D_2:theta(D_1)].
- The arithmetic image is open if and only if the geometric image is open.

**Proof steps.**
1. Use commutation with G and exactness to prove the kernel-image identity.
2. Use surjectivity of P_1 -> G to prove HD_2=P_2.
3. Construct a bijection of coset sets D_2/theta(D_1) -> P_2/H.
4. Use compactness of the images to prove they are closed, then equate finite index with openness.

**Acceptance.**
- No normality of H or theta(D_1) is assumed.
- The index comparison is a coset-set equivalence, not a quotient-group isomorphism.
- Both image subgroups are proved closed before using finite index.

**Exclude.** Using group quotients by nonnormal images. Dropping continuity, exactness or surjectivity to G.

Proposed names: `arithmetic_geometric_image_intersection`, `arithmetic_geometric_index_eq`, `arithmetic_open_iff_geometric_open`.

### S01

**Define the exact p-subtame field predicate**

Stage 2. Owner: `MochizukiHom/Fields/Basic.lean`
Prerequisites: none.
Source: `def:p-subtame-field`, statement lines 190-199 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- A prime p and a characteristic-zero field K.
- A presentation consists of a Henselian DVR field F of mixed characteristic (0,p), a chosen separable closure, its maximal algebraic tame extension, and a field embedding of K into that extension.

**Output.**
- IsPSubtame p K is the existence of such a presentation; it contains no reconstruction, Tate-extension, or Hom theorem as data.
- All later host choices are witnesses derived from this proposition, not extra hypotheses of the final theorem.

**Proof steps.**
1. Define the presentation with valuation-ring, fraction-field and residue-field identifications.
2. Define the maximal tame algebraic extension through actual finite tame subextensions and prove its stated universal property.
3. Define IsPSubtame by existence of the presentation and provide witness transport under field equivalence.

**Acceptance.**
- The final predicate requires only the stated prime, characteristic and existential presentation.
- F tame is an algebraic extension, not a completion.
- There is no completeness, finite-generation or perfect-residue-field field in the predicate.

**Exclude.** Encoding a desired theorem as a field of the presentation. Confusing a valuation on the auxiliary host with a valuation assumption on K.

Proposed names: `PSubtamePresentation`, `IsPSubtame`, `isPSubtame_iff_exists_presentation`.

### S02

**Construct a complete tame host and prove field-class closure**

Stage 2. Owner: `MochizukiHom/Fields/Basic.lean`
Prerequisites: S01.
Source: `lem:subtame-host-closure`, statement lines 201-218 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- IsPSubtame p K as in S01.
- For closure, an embedding of a subfield, a finite extension, or a finitely generated extension of K.

**Output.**
- Produce K -> M tame inside an algebraic closure Omega, where M is complete discretely valued of mixed characteristic (0,p) with separably closed residue field.
- Identify M tame with the union of M(pi^(1/n)) for n prime to p, and prove its Galois group over M is pro-prime-to-p.
- Prove closure of IsPSubtame under subfields, finite extensions and finitely generated extensions.

**Proof steps.**
1. Pass from F to its maximal unramified algebraic extension; retain the uniformizer and value group and identify the separably closed residue field.
2. Complete this DVR and choose compatible roots in a common algebraic closure to embed the old tame extension into M tame.
3. Use Hensel lifting of prime-to-p roots of unity and the Eisenstein degree calculation to identify the tame tower and its finite Galois groups.
4. For finite L/K, adjoin finitely many defining algebraic elements to M and apply tame base change.
5. For K(t), complete the Gauss valuation on M(t); use tame base change for this transcendental extension of DVRs, then combine with finite-extension closure.

**Acceptance.**
- All field maps are explicit embeddings with commuting triangles.
- The auxiliary residue field is separably closed; no step replaces this by perfect.
- The tame-base-change lemma accepts the Gauss-valued transcendental extension.
- The exported closure theorem covers every finitely generated extension and retains the original predicate.

**Exclude.** Assuming K is contained in a finite local stage M0. Using completion as the definition of the tame extension. Assuming tame base change only for finite extensions.

Proposed names: `exists_complete_tame_host`, `isPSubtame_subfield`, `isPSubtame_finite_extension`, `isPSubtame_finitelyGenerated_extension`.

### S48

**Construct algebraic pro-p test fields**

Stage 2. Owner: `MochizukiHom/Fields/Basic.lean`
Prerequisites: none.
Source: `lem:pro-p-algebraic-test-field`, statement lines 2368-2374 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A Henselian discretely valued field F of mixed characteristic (0,p), an arbitrary subfield K, and its algebraic closure Kbar inside a fixed algebraic closure of F.
- L=F_nr Kbar and any finite extension T/L inside that closure.

**Output.**
- L and T are Henselian rank-one valued fields with separably closed residue field, value group Q normalized by v(p)=1, and pro-p absolute Galois group.

**Proof steps.**
1. Extend the Henselian valuation uniquely to the algebraic extension and identify the residue field as algebraic over a separably closed field.
2. Use algebraicity for value-group containment in Q and the roots p^(1/m) in Kbar for the reverse inclusion.
3. For each prime ell different from p, divide a valuation by ell and lift an ellth root of the residual unit by Hensel to prove T* ell-divisible.
4. Use mu_ell in Kbar and Kummer theory to exclude cyclic ell extensions of every finite T/L.
5. Use Cauchy subgroups in a finite Galois quotient to conclude every such quotient is a p-group.

**Acceptance.**
- The resulting field need not remain discretely valued or complete.
- The assertion holds after every finite extension T/L.
- The value group is proved to equal Q, not only to be p-divisible.
- No perfection assertion is made about the separably closed residue field.

**Exclude.** Treating an algebraic infinite extension of a DVR as another DVR. Excluding only cyclic extensions of L while ignoring finite intermediate fields.

Proposed names: `algebraicTestField_valueGroup`, `algebraicTestField_separablyClosedResidue`, `algebraicTestField_absoluteGalois_proP`.

### S58

**Descend invariant rational coefficients by a minimal denominator**

Stage 2. Owner: `MochizukiHom/Fields/Basic.lean`
Prerequisites: none.
Source: `lem:constant-coefficient-field-descent`, statement lines 2891-2897 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A perfect field k, an algebraically closed extension Omega/k, a field extension F/k, and the domain B=Omega tensor_k F.
- Aut(Omega/k) acts on the first tensor factor and its fraction field.

**Output.**
- Frac(B) fixed by all Aut(Omega/k) equals the embedded F.
- For geometrically integral X/k, Omega(X) fixed by Aut(Omega/k) equals k(X).

**Proof steps.**
1. Show Omega fixed by Aut(Omega/k) equals k by moving a non-k algebraic element to another conjugate or a transcendental element by a basis translation, then extending the map.
2. For an invariant b, choose a denominator d=sum a_i e_i with e_i k-linearly independent, the number of terms minimal, and a_1=1.
3. If sigma(d)-d is nonzero it gives a shorter denominator for b, a contradiction.
4. Compare coefficients to show d in F and then bd in F, so b in F.
5. Identify the localized tensor fraction field with the actual base-changed function field.

**Acceptance.**
- Omega may be transcendental over k.
- Minimality counts independent denominator terms and includes the normalization a_1=1.
- The scheme corollary uses actual function-field identifications.

**Exclude.** Using only the algebraic Galois fixed-field theorem when Omega/k is transcendental. Assuming F and Omega linearly disjoint without the stated domain hypothesis.

Proposed names: `constantTensorFraction_invariants`, `geometricFunctionField_invariants`.

### S60

**Preserve regularity with a translated pencil**

Stage 2. Owner: `MochizukiHom/Fields/Basic.lean`
Prerequisites: none.
Source: `lem:two-translations-regular-pencil`, statement lines 2950-2955 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero field k, a finitely generated regular extension M/k, algebraically independent a,b in M, and an independent variable t over M.

**Output.**
- M(t)/k(t,at+b) is regular.

**Proof steps.**
1. Let B0=k(a,b) and let N0 be its finite relative algebraic closure in M; regularity of M/N0 survives adjoining t.
2. For z algebraic over k(t,at+b), place z in N0(t), set L=B0(t,z), and use coefficients of a minimal polynomial of a primitive element to show L=L0(t) for some finite L0/B0.
3. Deduce that the translation t -> t+1 fixing M preserves L.
4. Put u=at+b and uprime=u+a; use their independence to show L=k(t,u,z)(uprime) is regular over k(t,uprime).
5. The translated z is algebraic over k(t,uprime), hence belongs to it; translate back and conclude z belongs to k(t,u).

**Acceptance.**
- The translation acts on the actual rational function field and preserves the intermediate L by proof.
- Algebraic independence of u and uprime over k(t) is established.
- The final output proves both algebraic closedness of the base in M(t) and separability, the latter from characteristic zero.

**Exclude.** Assuming the finite intermediate field L is translation-stable without the minimal-polynomial coefficient argument. Changing the chosen pencil after selecting a finite cover.

Proposed names: `twoTranslations_regularPencil`.

### I05

**Fix coordinate formal groups and the actual finite-level Tate comparison**

Stage 3. Owner: `MochizukiHom/FormalGroups/Basic.lean`
Prerequisites: none.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension).

**Input.**
- Generic coordinate commutative formal groups over a commutative ring for the basic layer.
- For the local tower layer, a complete mixed-characteristic DVR, finite-height groups, actual division quotient rings and surjective [p]-transitions on geometric points.

**Output.**
- One coordinate formal-group API with actual law and morphism identities; a separate finite-height/DVR specialization.
- The actual inverse limit T_pF and natural Galois-equivariant identifications T_pF/p^n = F[p^n](Kbar).
- Named coherent maps for torsion inclusions, [p]-transitions and quotient reduction, keeping them distinct.

**Proof steps.**
1. Define formal group laws, coordinate morphisms and tangent matrices with identities.
2. Define finite height by finite freeness of [p]^* and construct actual division quotient rings.
3. Form the geometric-point inverse limit using [p].
4. Prove surjectivity of the nth coordinate by successive lifting.
5. If x_n=0, form y_m=x_(m+n), verify y_m lies in F[p^m], and prove p^n y=x.
6. Prove naturality and Galois equivariance; derive finite-free Z_p structure from ranks and exact sequences when needed.

**Acceptance.**
- Basic formal groups remain available over a characteristic-zero domain for S36.
- T0 uses the actual quotient rings and actual [p]-tower.
- Torsion inclusions are not confused with inverse-limit transition maps.
- No Tate-extension theorem is built into the data.

**Exclude.** Bundling complete-DVR assumptions into the generic coordinate layer. Postulating an abstract Tate module with unproved finite-level identification.

Proposed names: `CoordinateFormalGroup`, `FormalGroupFiniteHeight`, `tateModule_mod_pPow_equiv`, `tateFiniteLevel_natural`.

### I06

**Show division ideals separate actual formal series**

Stage 3. Owner: `MochizukiHom/FormalGroups/Basic.lean`
Prerequisites: I05.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension).

**Input.**
- A complete separated coordinate formal group over a mixed-characteristic DVR with [p](X)=pX+terms of order at least two.
- J_n is the ideal generated by the coordinates of [p^n](X).

**Output.**
- J_n is contained in (pi,X)^(n+1), hence intersection J_n=0.
- Agreement of integral formal maps on all generic division groups implies equality when the division quotient rings are R-flat.

**Proof steps.**
1. Induct on n, using multiplication by p to increase maximal-ideal order and quadratic terms to increase it further.
2. Apply separatedness of R[[X]] to conclude the intersection is zero.
3. Descend generic equality to each integral finite quotient by flatness.
4. Apply the ideal-intersection result coefficientwise to detect equality of formal maps.

**Acceptance.**
- The ideals are the actual coordinate division ideals.
- The inclusion is proved uniformly for every n.
- Generic-to-integral equality explicitly invokes flatness.

**Exclude.** Replacing equality of schemes with equality of geometric-point values. Asserting density of torsion without proving the division-ideal statement.

Proposed names: `divisionIdeal_adic_bound`, `divisionIdeals_intersection_zero`, `formalMap_eq_of_all_genericDivision_eq`.

### S12

**Construct actual formal division groups from a semiabelian model**

Stage 3. Owner: `MochizukiHom/FormalGroups/Basic.lean`
Prerequisites: I05.
Source: `lem:algebraic-group-formal-division`, statement lines 572-593 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A complete mixed-characteristic DVR R and a smooth separated finite-type commutative algebraic-space group G/R with semiabelian geometric fibres.
- A chosen identity completion P with actual coordinates R[[X]].

**Output.**
- Each multiplication [p^n] on G is flat, quasi-finite, finitely presented and surjective; its map on identity completions is finite free.
- C_n=Spec R[[X]]/([p^n](X)) is an open-and-closed finite-flat subgroup of G[p^n], whose special geometric fibre is the whole identity component.
- rank C_n=p^(nh), the sequence 0 -> C_n -> C_(n+m) ->[p^n] C_m -> 0 is fppf exact, and omega_Cn=omega_P/p^n omega_P.

**Proof steps.**
1. Prove multiplication finite faithfully flat on semiabelian fibres using the torus calculation, the abelian result and the extension torsor.
2. Apply fibrewise flatness over R and finite presentation to get quasi-finite flat surjectivity.
3. Pull back over the completed identity, select its unique Henselian identity-local factor and identify its completed ring with R[[X]].
4. Prove that this finite-free local factor is open and closed and stable under the group operations.
5. Base change multiplication to derive exact division sequences, then compute ranks and cotangent modules.

**Acceptance.**
- The finite groups are the displayed quotient rings and the actual identity factors.
- Exactness is fppf exactness, not only pointwise exactness.
- The special fibre is geometrically connected, including nilpotents.
- Finite unramified chart choices descend back to the original R.

**Exclude.** Assuming a general BT-to-formal-group equivalence. Reconstructing a second torsion tower unrelated to the quotient rings.

Proposed names: `semiabelianModel_formalMultiplication_finiteFree`, `formalDivision_openClosed`, `formalDivision_fppf_exact`, `formalDivision_cotangent`.

### S13

**Construct and invert the logarithm on the p-squared ball**

Stage 3. Owner: `MochizukiHom/FormalGroups/Basic.lean`
Prerequisites: I05.
Source: `lem:small-ball-formal-logarithm-direct`, statement lines 664-676 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A p-adically complete separated ring S in which p is a non-zero-divisor.
- A commutative d-variable formal group F/S; no DVR or perfect-residue assumption.

**Output.**
- ell_F(x)=lim_n p^(-n)[p^n]_F(x) is a continuous group isomorphism from F on (p^2 S)^d to the additive group (p^2 S)^d.
- For an integral formal group map f:F -> H, ell_H(f(x))=df ell_F(x).

**Proof steps.**
1. Write [p](X)=pX+Q(X) with Q of order at least two.
2. Prove x_n lies in p^(n+2) and the normalized successive differences in p^(n+3); use the non-zero-divisor hypothesis to define all divisions uniquely.
3. Prove ell-id raises the congruence order by at least one.
4. Invert ell using the contraction iteration x_(j+1)=z-(ell-id)(x_j).
5. Take limits of group-law and morphism identities to prove additivity and functoriality.

**Acceptance.**
- Both maps preserve the p^2 ball and are continuous.
- The proof works for p=2 with exactly the stated ball.
- The construction uses ring completeness rather than a nonexistent archimedean norm.
- Uniqueness of division by powers of p is explicit.

**Exclude.** Claiming the logarithm has uniformly bounded denominators on the entire formal polydisc. Requiring a field norm or a DVR unnecessarily.

Proposed names: `smallBall_logarithm`, `smallBall_logarithm_equiv`, `smallBall_logarithm_natural`.

### S14

**Take finite-flat subgroup closures and quotients**

Stage 3. Owner: `MochizukiHom/FormalGroups/Quotients.lean`
Prerequisites: none.
Source: `lem:finite-flat-subgroup-closure-quotient`, statement lines 716-723 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A DVR R with fraction field K, a finite-flat commutative group F/R and a closed subgroup H_K of its generic fibre.
- For the nested assertion, finite-flat closed subgroups H contained in G contained in F.

**Output.**
- The schematic closure H is finite flat, and the fppf quotient F/H is a finite-flat group with finite faithfully flat quotient map and the stated generic fibre.
- G/H -> F/H is a closed immersion.

**Proof steps.**
1. Construct the closure ring as the image of O(F) -> O(H_K), hence a finite torsion-free and free R-module.
2. Descend the Hopf operations, detecting their identities after inverting the uniformizer using flatness.
3. Apply the finite free translation-relation quotient theorem to the actual action.
4. Identify the invariant subring and generic-fibre quotient by base change.
5. Prove the nested quotient map is a finite monomorphism and hence a closed immersion.

**Acceptance.**
- Closure flatness follows from the torsion-free image ring.
- The quotient represents the fppf sheaf and its map is finite faithfully flat.
- Generic-fibre compatibility includes the actual quotient maps.

**Exclude.** Treating geometric-point closure as schematic closure. Using invariants without proving the finite free action hypotheses.

Proposed names: `finiteFlatSubgroup_genericClosure`, `finiteFlatGroup_quotient`, `nestedFiniteFlatQuotient_closedImmersion`.

### S15

**Construct smooth finite-height quotients of formal groups**

Stage 3. Owner: `MochizukiHom/FormalGroups/Quotients.lean`
Prerequisites: I05, S14.
Source: `lem:finite-formal-group-quotient`, statement lines 737-742 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A smooth finite-height coordinate formal group P over a complete mixed-characteristic DVR R, and a finite-flat closed subgroup H.
- Also allow the corresponding characteristic-p field version for the special fibre.

**Output.**
- A finite faithfully flat formal quotient q:P -> P/H, with P/H again smooth and of finite height.
- Actual coordinates for the quotient and the descended group law, together with q[p]=[p]q.

**Proof steps.**
1. Define the translation action on R[[X]] using completeness of the finite tensor module and prove it is free.
2. Apply the affine finite-relation quotient to obtain B=A^H and A finite faithfully flat over B.
3. Prove B local Noetherian complete and R-flat, and descend regularity to B/pi B.
4. Construct k[[Z]] -> B/pi B from a cotangent basis and prove it is an isomorphism by dimension; lift to R[[Z]] -> B.
5. Descend the group law through completed tensor products and prove finite freeness of [p] by finiteness and flat descent.

**Acceptance.**
- The ordinary affine quotient is connected to the formal topology by proved completeness and continuity statements.
- Group operations descend through completed tensor products.
- The characteristic-p field case is available for S19.
- Finite height is proved for the quotient, not added as an assumption.

**Exclude.** Assuming Spec R[[X]] already carries the entire formal group law as an ordinary algebraic group. Inferring formal smoothness from an unsupported generic-fibre assertion.

Proposed names: `formalGroup_finiteFlat_quotient`, `formalGroup_quotient_smooth`, `formalGroup_quotient_finiteHeight`.

### S16

**Characterize bounded logarithms and retain the explicit denominator**

Stage 3. Owner: `MochizukiHom/FormalGroups/Quotients.lean`
Prerequisites: I05, S13.
Source: `lem:formal-bounded-logarithm-reduction`, statement lines 790-799 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A smooth finite-height formal group F over a complete mixed-characteristic DVR R, with v(p)=1 and v(pi)=1/e.
- An actual integral curve gamma in F(t R[[t]]).

**Output.**
- log_F gamma belongs to R[[t]][1/p]^d if and only if gamma reduces to zero modulo pi.
- In that case log_F gamma belongs to p^(2-2e) R[[t]]^d.

**Proof steps.**
1. Scale a bounded logarithm into p^2 tR[[t]] and use the inverse small-ball logarithm to see a p-power multiple of gamma reduces to zero.
2. The reduced curve then maps to a finite local division group; reducedness of k[[t]] forces the curve to vanish.
3. Conversely iterate [p](X)=pX+O(X^2) starting from coefficient valuations at least 1/e.
4. Prove b_(n+1)>=min(b_n+1,2b_n)>=b_n+1/e, reach the p^2 ball by n=2e, and divide its logarithm by p^(2e).

**Acceptance.**
- The output has exponent 2-2e, uniformly in the curve and dimension.
- The bounded-denominator ring is distinguished from K[[t]].
- Reduction uses the nilpotent scheme structure of the finite local group.

**Exclude.** Replacing bounded denominators by arbitrary coefficientwise convergence. Assuming finite residue field to obtain a bound.

Proposed names: `formalCurve_boundedLog_iff_reduction_zero`, `formalCurve_boundedLog_uniformBound`.

### S17

**Lift integral curves through a finite generic embedding**

Stage 3. Owner: `MochizukiHom/FormalGroups/Quotients.lean`
Prerequisites: I05, S13.
Source: `lem:finite-formal-embedding-curve-saturation`, statement lines 812-819 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A finite formal-group homomorphism j:Q -> J over a complete mixed-characteristic DVR R, whose coordinate map after inverting p is an isomorphism onto its closed image.
- A=dj, U=image(A_K), and an integral curve gamma in J with logarithm in U[[t]].

**Output.**
- There exists a unique integral curve eta in Q with j eta=gamma.
- A reusable minimum-denominator lemma: an element of R[[t]][1/pi] integral over R[[t]] lies in R[[t]], since k[[t]] is reduced.

**Proof steps.**
1. Complete the generic closed immersion at the identity to prove A_K injective.
2. Construct eta over K[[t]] as exp_Q(A_K^(-1) log_J gamma).
3. Use the finite coordinate image B contained in R[[Y]] and equality after inverting p to show every coordinate of eta has bounded denominators.
4. Use finiteness to obtain a monic equation for each coordinate over R[[t]].
5. Choose its smallest denominator power and reduce the scaled monic equation modulo pi to force that power to be zero.

**Acceptance.**
- Integrality is proved in the bounded-denominator localization before entering K[[t]].
- The lift has zero constant term and is unique.
- The denominator lemma is exported for reuse in S21.

**Exclude.** Treating R[[X]][1/p] and K[[X]] as equal. Using logarithmic image membership to assert integral coefficients without the monic-equation argument.

Proposed names: `integral_boundedDenominator_series`, `formalCurve_lift_finiteGenericEmbedding`.

### S18

**Prove uniform bounded projection of p-typical logarithmic curves**

Stage 4. Owner: `MochizukiHom/FormalGroups/TateExtension.lean`
Prerequisites: I05, S13, S15, S16.
Source: `lem:formal-bounded-projection`, statement lines 849-857 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A finite-height coordinate formal group F over a complete mixed-characteristic DVR R with ramification index e.
- An integral matrix A of any rank and y in D_F, the logarithms of actual integral p-typical curves, such that Ay has bounded coefficients.

**Output.**
- Ay belongs to p^(2-2e) R[[Delta]]^r.
- The estimate holds without residue-field perfection and without injectivity or surjectivity of A.

**Proof steps.**
1. Construct the integral p-typical projector and operators V and rho_lambda on actual curves; identify E=D_F/B_F and E/VE with k^d.
2. For perfect k, use a finite Frobenius annihilator of F_k[p] and the formal quotient to prove V^H E contained in pE.
3. Define the bounded-projection subgroup N of E; prove p-saturation, V-saturation and k-linearity of N/VN.
4. Choose a basis of N/VN and lift arbitrary elements by successive first-coefficient elimination, obtaining a uniform norm M.
5. Apply V^H N contained in pN to the basis lifts and deduce M<=max(|p|M,p^(2e-2)), hence M<=p^(2e-2).
6. Construct a uniformizer-preserving DVR extension with perfect residue field using maximality and adjoining pth roots of residue units; complete it and descend the coefficient bound by valuation preservation.

**Acceptance.**
- The quantifier covers all integral matrices, including ones with kernel.
- The final exponent is 2-2e and does not contain height, dimension or the auxiliary Frobenius exponent H.
- rho_lambda is used only where its first-coefficient scalar action is proved.
- Coefficientwise convergence of the V-adic series is proved without local compactness.
- The general-residue theorem invokes an actual extension preserving pi and e.

**Exclude.** Assuming E is a k-module merely from the substitutions. Using a finite Gauss norm before boundedness has been established. Adding residue-field perfection to the exported theorem.

Proposed names: `pTypicalCurve_operations`, `boundedProjection_perfectResidue`, `exists_uniformizerPreserving_perfectResidue_extension`, `formalCurve_boundedProjection`.

### S19

**Uniformly annihilate the scheme-theoretic special kernel**

Stage 4. Owner: `MochizukiHom/FormalGroups/TateExtension.lean`
Prerequisites: S13, S15, S16, S17, S18.
Source: `lem:finite-generic-embedding-special-kernel`, statement lines 984-992 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A finite homomorphism j:Q -> J of smooth finite-height formal groups over a complete mixed-characteristic DVR R.
- The map after inverting p is a closed immersion; e is the ramification index.

**Output.**
- Multiplication by p^(2e) is zero on the whole finite group scheme ker(j_k).

**Proof steps.**
1. Choose an integral split projection onto the complement of the saturated image lattice of dj.
2. Form the special formal quotient H=Q_k/ker(j_k) and prove H -> J_k is a closed immersion.
3. Use nilpotence to choose an auxiliary p-power annihilator and lift p-typical coordinate curves of H to logarithmic curves in J and Q.
4. Apply S18 to their projected logarithms and S13 to subtract a correction reducing to zero.
5. Apply curve saturation S17 to lift the corrected curves through j.
6. Assemble their reductions into a pointed formal map h:H -> Q_k; use an invertible linear term to arrange qh=[p^(2e)].
7. Show hq-[p^(2e)] factors through the finite local kernel; reducedness of a power-series ring makes this map zero, and restrict to the kernel.

**Acceptance.**
- The annihilation is an identity on a finite group scheme, not merely on geometric points.
- The final exponent is exactly 2e, independent of the chosen auxiliary annihilator.
- No proof that h is a group homomorphism is required or assumed.
- No residue perfection hypothesis remains.

**Exclude.** Testing nilpotent finite groups only on geometric points. Leaving the auxiliary p^a in the final bound.

Proposed names: `finiteGenericEmbedding_specialKernel_annihilated`.

### S20

**Solve descending complete-local cosets and control intersections**

Stage 4. Owner: `MochizukiHom/FormalGroups/Quotients.lean`
Prerequisites: none.
Source: `lem:complete-local-descending-cosets`, statement lines 1056-1067 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- A complete Noetherian local ring (A,m), descending ideals I_n and I=intersection I_n.

**Output.**
- The canonical A/I -> inverse_limit A/I_n is an isomorphism.
- For every r some I_n is contained in I+m^r.
- For every ideal J, intersection(I_n+J)=I+J. In the complete Noetherian doubled power-series ring used for the group law, prove intersection_n(I_n in first variables + I_n in second variables) = (I in first variables + I in second variables).

**Proof steps.**
1. Reduce a compatible sequence of cosets modulo m^r; finite length makes the descending images stabilize.
2. Prove the stabilized cosets at consecutive r map surjectively by another descending finite-length argument.
3. Choose compatible residues and use completeness to obtain a common element; use closedness of each ideal to place it in every original coset.
4. Prove cofinality in A/I by contradiction with a nonzero stable residue.
5. Use cofinality and separatedness of quotients to prove the sum/intersection identities.

**Acceptance.**
- Finite length, not finiteness of the underlying residue sets, is the compactness substitute.
- The intersection-plus-ideal identity is an exported theorem.
- The completed two-variable version has its completeness and Noetherian hypotheses discharged.

**Exclude.** Assuming local compactness or finite residue field. Commuting reduction modulo pi with an infinite intersection without proof.

Proposed names: `completeLocal_descendingCosets`, `descendingIdeals_adic_cofinal`, `intersection_addIdeal`, `completedTwoVariable_intersection`.

### S21

**Identify the closed formal graph from finite graph approximations**

Stage 4. Owner: `MochizukiHom/FormalGroups/TateExtension.lean`
Prerequisites: I05, I06, S17, S20.
Source: `lem:closed-graph-finite-flat-projection`, statement lines 1086-1101 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- Smooth finite-height formal groups P,Q over a complete mixed-characteristic DVR R.
- Increasing finite-flat closed subgroups E_n of (P times Q)[p^n], whose generic first projections identify E_n,K with P[p^n]_K.
- One nonnegative integer s satisfies [p^s] ker(E_n,k -> P_k)=0 for every n.

**Output.**
- C=R[[X,Y]]/intersection I_n is R-flat and defines a closed formal subgroup Gamma0.
- Its first projection a:Gamma0 -> P is an isomorphism.

**Proof steps.**
1. Identify C with the inverse limit of the finite-flat coordinate rings and descend the group law using S20.
2. Reduce the defining intersection modulo (pi,X) using the proved intersection formula; place the special kernel in Q_k[p^s].
3. Use finite special fibre and topological Nakayama to prove C finite over A=R[[X]], and I06 to prove A injects into C.
4. Prove [p]^* is injective from generic graph surjectivity and finite-level flatness.
5. For the finite generic kernel N_K, choose a p-power annihilator; put h=[p^c]a and D=ker h, and identify D_K using the graph at level c.
6. Prove the ordinary tensor-ring relation C tensor_(A,h*) C = C tensor_R O(D) after finiteness, and compute the generic invariant ring to be h* A_K.
7. Use [p^c]-invariance and injectivity to obtain C_K=A_K, then use the minimum-denominator lemma to obtain C=A.

**Acceptance.**
- Finiteness of the projection is proved before ordinary affine invariant-ring arguments.
- Only generic kernels are assumed finite etale; integral N and D are never assumed flat.
- The tensor-product identity is justified by finite-module completeness.
- Reduction of the infinite intersection invokes S20.
- The localized rings remain bounded-denominator rings.

**Exclude.** Assuming the unknown projection finite or flat. Cancelling [p]^* without first proving injectivity. Treating generic agreement on torsion as integral equality without flatness.

Proposed names: `closedGraph_finiteFlatProjection_isIso`.

### S22

**Extend every equivariant Tate map to a unique integral formal map**

Stage 4. Owner: `MochizukiHom/FormalGroups/TateExtension.lean`
Prerequisites: I05, I06, S14, S15, S19, S21.
Source: `thm:formal-tate-extension-elementary`, statement lines 1181-1186 of frozen version 78.
Detailed proof: [P02: Integral formal groups and Tate extension](#p02-integral-formal-groups-and-tate-extension). Search the source label within that section.

**Input.**
- Smooth commutative finite-height coordinate formal groups P,Q over a complete mixed-characteristic DVR R with fraction field K.
- A G_K-equivariant Z_p-linear map u:T_p P -> T_p Q of the actual inverse-limit Tate modules.

**Output.**
- A unique integral formal-group homomorphism f:P -> Q with T_p f=u.
- An equivalence between actual integral formal homomorphisms and equivariant Tate maps, compatible with coordinates and finite complete-DVR extensions.

**Proof steps.**
1. Use T0 to obtain maps of finite geometric division groups and finite-etale Galois descent to obtain their actual generic scheme maps.
2. Take the finite-flat schematic closures E_n of their generic graphs and prove nestedness by finite-level flatness.
3. Form (P times Q)/E_n and its second-axis map j_n; prove j_n finite and generically a closed immersion.
4. Apply S19 to obtain one kernel bound 2e for every E_n.
5. Apply S21, invert the first graph projection and compose with the second projection to construct f.
6. Prove its Tate map is u at each finite level; use I06 and flatness for uniqueness.
7. Derive functoriality, coordinate transport and finite-base-extension compatibility from uniqueness.

**Acceptance.**
- The output is a constructed integral map, not an axiom or an input field in a structure.
- Every finite-level comparison uses the actual quotient ring and the actual transition [p].
- Both inverse laws of the Hom equivalence are proved.
- No residue-field finiteness, perfection or finite-generation hypothesis remains.

**Exclude.** Quoting Tate full faithfulness as an unproved replacement for the central argument. Using unrelated abstract inverse-limit modules.

Proposed names: `formalTateMap_integralExtension`, `formalTateMap_integralExtension_unique`, `formalHom_tateHom_equiv`, `formalTateExtension_baseChange`.

### S36

**Detect a characteristic-zero formal homomorphism by its differential**

Stage 4. Owner: `MochizukiHom/FormalGroups/Basic.lean`
Prerequisites: I05.
Source: `lem:formal-hom-differential-faithful-elementary`, statement lines 1847-1851 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A characteristic-zero integral domain R, smooth coordinate commutative formal groups P,Q/R, and a formal homomorphism F:P -> Q.

**Output.**
- If dF=0, then F=0; consequently equal differentials imply equal formal homomorphisms.

**Proof steps.**
1. Differentiate F(P(X,Y))=Q(F(X),F(Y)) with respect to Y at zero.
2. Use invertibility of the matrix partial_2 P(X,0), whose constant coefficient is the identity.
3. Deduce every partial derivative of F is zero; coefficient comparison over a characteristic-zero domain makes F constant.
4. Use the identity condition to show the constant is zero.

**Acceptance.**
- The theorem is over a characteristic-zero domain and does not require a complete DVR.
- Formal differentiation and the Jacobian chain rule are proved for the coordinate series.
- The zero conclusion is equality of formal maps.

**Exclude.** Using a generic-point analytic argument that silently assumes a topology. Adding finite height when it is unnecessary.

Proposed names: `formalHom_eq_zero_of_differential_zero`, `formalHom_differential_injective`.

### I07

**Construct a split semistable model and prove the horizontal node-divisor formula**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: none.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation).

**Input.**
- A smooth proper geometrically connected curve over a complete mixed-characteristic (0,p) DVR field; no perfection assumption on the residue field.
- For the local subtheorem: a complete DVR R with uniformizer pi, e >= 1, A = R[[x,y]]/(xy-pi^e), the vertical branch D = V(pi,x), and a horizontal height-one prime Z of A.

**Output.**
- After a finite separable constant extension, an actual proper split semistable model with a section through its smooth locus; splitness includes components, nodes and branches.
- For a = x(Z), L = Frac(A/Z), d = [L:Frac(R)] and i = v(a): prove 0 < i < e, L = Frac(R)(a), d*i is integral, and div(P_a(x)) = Z + d*i*D.
- For a constant comparison section c of the same coordinate valuation, construct the Cartier horizontal difference Z-d*c using P_a(x)/(x-a_c)^d and prove that its restrictions to both normalized special branches are trivial. Provide descent to the chosen split etale chart.

**Proof steps.**
1. Apply projectivity and semistable reduction with their actual hypotheses; split the finitely many nodes, branches and component constant fields by finite residue extensions, lift unramified extensions, and Hensel-lift a smooth point.
2. Prove A is normal using the hypersurface S2 property and regularity outside the closed point. Prove A/Z is finite over R from its complete pi-adic filtration.
3. Use the coordinate images a and pi^e/a and completeness to identify the actual fraction field with Frac(R)(a); record this identification before using the degree d.
4. Calculate generic horizontal multiplicity one and vertical multiplicities d*i and zero along the two branches. Henselian uniqueness of the extended valuation controls all conjugates of a.
5. Divide by (x-a_c)^d, cancel vertical multiplicities, and calculate the two normalized reductions, including the nonzero norm ratio.
6. Transport the divisor and its trivial branch restrictions through the specified etale chart and faithfully flat completed-local comparison; do not identify arbitrary etale residue fields with L without proof.

**Acceptance.**
- The finite extension, model, smooth-locus section and splitness witnesses are returned as data.
- The local theorem treats i as a rational valuation and separately proves integrality of d*i.
- Both the Cartier-divisor assertion and triviality on each normalization component are exported.
- The completed-chart-to-etale-chart comparison is a proved lemma with explicit field maps, not a comment or an unproved assumption.

**Exclude.** Using only semistable reduction leaves the node calculation and its descent unproved. Assuming L=K(a) for an arbitrary etale extension, or treating i as an integer, changes the argument. Replacing separably closed residue fields by algebraically closed/perfect ones restricts the final theorem.

Proposed names: `exists_splitSemistableModel_with_section`, `node_horizontal_prime_divisor`, `node_horizontal_difference_cartier`.

### S23

**Trivialize a generically trivial line bundle with nonpositive component degrees**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: none.
Source: `lem:vertical-multidegree-graph`, statement lines 1252-1260 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A DVR R, a proper flat R-scheme Y with reduced connected pure one-dimensional special fibre, and an invertible sheaf L.
- L is trivial on the generic fibre and has degree <= 0 on every irreducible component of the special fibre.

**Output.**
- An actual isomorphism L ≅ O_Y, valid after replacing R by any DVR to which these same hypotheses apply. No regularity, nodal, splitness, or geometrically integral generic-fibre hypothesis is added.

**Proof steps.**
1. Use proper cohomological finiteness and flat base change to make H0(Y,L) a finite torsion-free R-module whose generic fibre is nonzero.
2. Choose a section outside pi*H0(Y,L), and use the multiplication-by-pi exact sequence to prove its special-fibre restriction is nonzero.
3. Apply the connected reduced curve criterion for a line bundle of nonpositive degree on every component to prove that the special section is nowhere zero.
4. The section's zero locus is proper over Spec(R); its closed image misses the closed point, hence is empty. Convert the nowhere-zero section into an invertible-sheaf isomorphism.

**Acceptance.**
- The exported assumptions match the manuscript's weaker hypotheses exactly.
- The reduction map H0/pi -> H0 of the special fibre is proved injective using the exact sequence.
- The output is a sheaf isomorphism, not only equality in the Picard group.
- The separatedness application can instantiate the theorem over an arbitrary test DVR.

**Exclude.** Adding regularity to use intersection theory loses the required generality. A nonzero generic section alone does not show its special restriction is nonzero.

Proposed names: `lineBundle_trivial_of_generic_trivial_of_component_degree_nonpos`.

### S24

**Represent relative Picard classes by uniquely rigidified line bundles**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: none.
Source: `lem:rigidified-picard-effective-descent`, statement lines 1282-1293 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A morphism f:X->S with a section b:S->X, and a proof that O_T -> (f_T)_* O_(X_T) is an isomorphism for every base change T->S.
- The canonical relative Picard fppf sheaf, and optionally an algebraic space P representing it.

**Output.**
- Every relative Picard class over T is represented by a line bundle L with b_T^*L ≅ O_T, unique up to a unique rigidification-preserving isomorphism, functorially in T.
- When P represents the sheaf, an actual universal rigidified line bundle on X×_S P with its pullback/classification identity.

**Proof steps.**
1. Normalize a local representative by tensoring with the inverse pullback of its restriction along b.
2. Identify automorphisms of a line bundle with global units; the universal structural-sheaf identity makes each such unit a base unit.
3. Show that an automorphism preserving rigidification is the identity. Deduce unique normalized transition isomorphisms and their cocycle identities.
4. Apply effective fppf descent to the normalized line bundles.
5. On etale charts of a representing algebraic space, perform the same construction on universal classes and glue the resulting bundles with the unique transition maps.

**Acceptance.**
- The universal quantifier over base changes remains in the input.
- Uniqueness is uniqueness of rigidification-preserving isomorphisms, not uniqueness of an unrigidified bundle.
- The universal bundle includes the actual base-change comparison, needed for point-divisor formulas.
- The construction is expressed using the Stacks Picard sheaf, with any NYLL presentation transported by a proved comparison.

**Exclude.** A Picard-sheaf point need not be an actual line bundle without the section and rigidification argument. Equality of isomorphism classes alone does not supply effective descent data.

Proposed names: `relativePicard_rigidified_representative`, `exists_universal_rigidified_lineBundle`.

### S25

**Construct the multidegree-zero Picard algebraic space of a fixed model**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: S23, S24.
Source: `prop:fixed-multidegree-zero-picard`, statement lines 1305-1319 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A proper flat finitely presented curve X/R over a DVR, with smooth geometrically connected generic fibre and split semistable special fibre C.
- The fppf subsheaf G of relative Picard classes whose restrictions have degree zero on every component of every geometric fibre.

**Output.**
- Represent G by one smooth separated finitely presented commutative group algebraic space; identify its generic fibre with the usual Jacobian.
- Construct the exact fppf sequence 0 -> G_m^(b1(Gamma)) -> G_k -> product_v J_(normalization component v) -> 0 using the actual normalization and dual graph, including loops.

**Proof steps.**
1. Prove universal f_*O_X=O_R and the hypotheses of relative Picard representability and smoothness, retaining quasi-separatedness and local finite presentation.
2. Use locally constant total degree and special normalization-component degrees to construct the specified open subgroup and prove its sheaf-level functor-of-points identity.
3. Patch line bundles on normalization components by branch-fibre identifications; prove this description after arbitrary test k-algebra base change.
4. Show restriction to normalization is fppf surjective and compute its kernel as edge gluing scalars modulo vertex rescalings. A spanning tree identifies this quotient with G_m^b1, including loop edges.
5. Establish quasi-compactness from the generic and special fibres, then finite presentation.
6. For every test DVR, rigidify a generically trivial class in the subgroup and apply S23. Use the discrete valuative criterion to deduce separatedness.

**Acceptance.**
- The representation identifies the specified fppf sheaf, not just groups of algebraically closed points.
- No requirement that G over R is a scheme is introduced.
- Separatedness uses multidegree-zero uniqueness; the geometrically integral-fibre separatedness theorem is not misapplied to a reducible semistable fibre.
- The gluing-torus exact sequence and its maps are explicit enough for S35 to identify a special Picard class.
- The degree-zero/algebraic-equivalence comparison is supplied wherever an imported NYLL representation uses the latter cut.

**Exclude.** Equality on geometric points does not identify fppf subsheaves. The graph must include self-nodes; deleting loops changes b1. Replacing the group algebraic space by an assumed scheme strengthens the construction.

Proposed names: `represents_multidegreeZeroPicard`, `multidegreeZeroPicard_special_exact`, `multidegreeZeroPicard_separated`.

### S26

**Identify the actual finite Abel–Jacobi maps and their Tate limit**

Stage 5. Owner: `MochizukiHom/Picard/AbelJacobi.lean`
Prerequisites: I03, S04, S24.
Source: `lem:proper-abel-jacobi-tate-stacks`, statement lines 1440-1457 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A smooth proper geometrically connected characteristic-zero curve C/k, its canonical usual Jacobian J, and a base point b after a finite constant extension.
- The actual Abel–Jacobi morphism alpha_b defined by the normalized universal line bundle and the point-divisor formula [x-b].

**Output.**
- For every m>=1, alpha_b induces an isomorphism H1_et(J_bar,Z/m) -> H1_et(C_bar,Z/m).
- The composite of pi1(alpha_b) and monodromy of [m]:J->J induces pi1(C_bar)^ab/m ≅ J[m](bar k), compatibly with divisibility of m, Galois actions and base change; its inverse limit is the actual Tate identification.

**Proof steps.**
1. Construct NYLL CurveModel data for the actual curve and transport the represented relative Picard object to the Stacks canonical one.
2. Prove equality of the degree-zero and algebraic-equivalence-zero relative subfunctors, including geometric-fibre tests and descent; use representability uniqueness to compare objects.
3. Verify the universal bundle's point-divisor formula for the actual alpha_b and invoke the audited finite-coefficient Abel–Jacobi H1 theorem on those data.
4. Translate H1 to actual finite torsor characters using S04 and I03, then dualize to finite abelianized fundamental groups.
5. Use connectedness of the multiplication torsor and the two orders m^(2g) to prove bijectivity of the actual monodromy map.
6. Prove transition, Galois and base-change diagrams from the multiplication torsors before passing to the inverse limit; discharge temporary root-of-unity choices.

**Acceptance.**
- The theorem applies to the actual divisor-class Abel–Jacobi map, not an unspecified morphism having the right H1 rank.
- The value m=1 and the transition maps m|m' are covered.
- The induced Tate map is obtained from the coherent finite maps and is Galois equivariant.
- Any primitive-root choice used for coefficients disappears from the final statement.

**Exclude.** An abstract group isomorphism from equal cardinalities does not identify the actual map. Imported H1 coefficient naturality does not automatically imply scheme-pullback naturality. An opaque assumed Picard representation leaves the actual-object bridge unfinished.

Proposed names: `abelJacobi_finiteH1_equiv`, `abelJacobi_finiteMonodromy_equiv`, `abelJacobi_tate_equiv`.

### S27

**Identify Jacobian invariant differentials with curve differentials, naturally**

Stage 5. Owner: `MochizukiHom/Picard/AbelJacobi.lean`
Prerequisites: S26.
Source: `prop:proper-jacobian-differentials-core`, statement lines 1478-1487 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A smooth proper geometrically connected curve C over a characteristic-zero field k, its actual Jacobian and Abel–Jacobi morphism as fixed in S26.

**Output.**
- A base-point-independent k-linear equivalence e^*Omega1_(J/k) ≅ H0(C,omega_C) given by Abel–Jacobi pullback.
- Commuting diagrams for field extension, norms of nonconstant proper-curve maps, and deck transformations, with covariant norm and contravariant pullback directions explicit.

**Proof steps.**
1. Handle genus zero by vanishing of both spaces.
2. Over an algebraic closure, use Riemann–Roch to prove surjectivity of C^g -> J, (x_i) |-> sum[x_i-b]. Equal dimensions make this generically finite; characteristic zero supplies separability.
3. Pull back an invariant differential along the sum map, obtaining the sum of its Abel–Jacobi pullbacks. Injectivity on rational differentials then proves injectivity of alpha_b^*.
4. Use the common dimension g to obtain an isomorphism and cohomological base change plus faithful descent to define it over k.
5. Show changing b translates J and hence fixes invariant differentials.
6. For a nonconstant curve map, prove the norm/Abel–Jacobi identity from the determinant norm on point divisors; differentiate it to obtain all naturality squares.

**Acceptance.**
- The genus-zero case has an explicit proof and no nonempty C^g argument is assumed there.
- The equivalence is the specified pullback map and is independent of b.
- Norm and deck compatibility are exported theorems about the actual maps.
- Field-extension comparison agrees with the cohomological base-change isomorphism.

**Exclude.** Dimension equality by itself does not identify the pullback or prove its injectivity. Reversing the norm direction corrupts later differential naturality.

Proposed names: `abelJacobi_invariantDifferentials_equiv`, `abelJacobi_differentials_norm_naturality`, `abelJacobi_differentials_deck_naturality`.

### S28

**Classify multiplicative-group covers and identify section differences with Kummer classes**

Stage 5. Owner: `MochizukiHom/Picard/AbelJacobi.lean`
Prerequisites: I02, S04, S10.
Source: `lem:gm-covers-without-generalized-jacobian`, statement lines 1517-1523 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A characteristic-zero field k, a prime p, and actual connected finite etale covers of G_m over k or its algebraic closure.

**Output.**
- An identification of the geometric pro-p fundamental group of G_m with Z_p(1).
- After a finite constant extension, every geometrically connected finite p-cover is isomorphic as a cover to t |-> t^(p^b); relative to 1, point-section differences are the usual Kummer classes under the same action convention.

**Proof steps.**
1. Compactify a connected cover to a finite map to P1 and pull back dt/t.
2. Use the local parameter t=u*z^(±e) to compute one simple pole at each boundary point and no zero on the etale locus.
3. Compare the differential-divisor degree with 2g-2 to prove genus zero and exactly one point above each boundary point.
4. Use Riemann–Roch to choose a coordinate and write the cover as c*t^d. Adjoin the required constant root and descend the finitely many coordinates to a finite constant field.
5. Use cofinality of these actual Kummer covers to identify the geometric pro-p group and its Galois action.
6. Compute the action on the fibre of p^n-th roots of a point; identify its cocycle with the arithmetic section difference relative to 1.

**Acceptance.**
- The classification returns cover isomorphisms, not only an equality of degrees.
- The group identification carries the cyclotomic Galois action.
- The Kummer cocycle sign agrees with the arithmetic fundamental-group convention fixed in the compatibility layer.
- All coordinate and scalar normalizations descend after a finite constant extension.

**Exclude.** A geometric group rank calculation does not classify the actual pullback cover needed later. The simple-pole argument requires characteristic zero; do not silently generalize it.

Proposed names: `gm_connected_pCover_normalForm`, `gm_geometricProP_equiv_tateTwist`, `gm_pointSection_difference_kummer`.

### S29

**Lift and realize Kummer torsors over a strictly Henselian base**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: none.
Source: `lem:picard-local-factor-kummer`, statement lines 1556-1572 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A strictly Henselian local ring R, a smooth commutative group algebraic space G/R, m>=1, and fppf-surjective multiplication [m].
- H=ker[m] and an open subgroup C⊆H; C may additionally be finite locally free.

**Output.**
- Surjectivity of H1_fppf(R,C)->H1_fppf(R,H) and of the Kummer map G(R)->H1_fppf(R,H).
- For each H-torsor, explicit C-torsor lifting and an isomorphism of its pushout with the given H-torsor; when C is finite locally free the lift is finite locally free.

**Proof steps.**
1. Construct U=H/C and its torsor quotient map. The open unit section and the difference map make U unramified; descend flatness and local finite presentation to conclude it is etale.
2. Prove that a torsor under a smooth group algebraic space over R has a point, by representation, a smooth etale scheme chart and strictly Henselian lifting.
3. For an H-torsor P, take the fibre over an R-point of P/C; it is a C-torsor whose pushout is P.
4. Trivialize P×^H G, descend [m] of its equivariant map to a point z in G(R), and identify P with [m]^{-1}(z).
5. Use fppf descent of finite local freeness for the final assertion and prove generic-fibre compatibility of the pushout identifications.

**Acceptance.**
- Both surjections are proved with the actual inclusion C->H and Kummer map.
- Pushout and generic-fibre comparison isomorphisms are available for reuse by S41.
- The result permits an algebraic-space group and an arbitrary strictly Henselian local base.
- Finite local freeness of the lifted torsor is proved only under the stated finite-local-freeness assumption on C.

**Exclude.** Vanishing statements for cohomology groups alone do not identify the torsor needed after pushout. The quotient is etale because of the open subgroup argument; H itself need not be etale.

Proposed names: `openSubgroup_torsor_lift_strictHensel`, `kummer_surjective_strictHensel`, `openSubgroup_torsor_lift_pushout`.

### S30

**Correct any Jacobian point by a constant in one fixed integral model**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: I07, S24, S25.
Source: `lem:picard-constant-point-correction`, statement lines 1619-1630 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A fixed split semistable model X/R0 with smooth-locus base section and its fixed multidegree-zero Picard algebraic space G with generic Jacobian J.
- A complete discretely valued extension F of the model field whose valuation ring dominates R0, an algebraic E/F containing the chosen algebraic closure of the model field, and P in J(E).

**Output.**
- Points z in G(O_E) and c in J(algebraic constants) with P=z+c. The model G is the same for all P; no point-dependent replacement of the model is permitted.

**Proof steps.**
1. Pull back the normalized universal line bundle along P, choose a rational trivialization, and descend its signed degree-zero divisor and finite data to a finite extension F'/F inside E.
2. For each closed divisor point with smooth specialization, choose a constant section on the same special component.
3. For each node specialization, choose a constant with matching coordinate valuation and use the specified split chart to obtain a comparison section. Enlarge F' for the finitely many constants and recompute degrees of the decomposed points.
4. At smooth points use local factoriality and degree specialization; at nodes use I07 to prove that each horizontal difference is Cartier and has zero multidegree, with trivial normalized restrictions in the nodal case.
5. Show transition quotients are units by normality and descend the local Cartier divisors.
6. The signed sum represents P-c; total degree zero makes c a Jacobian point. Its multidegree-zero class yields z over O_(F'), then O_E.

**Acceptance.**
- The returned z lies in the original fixed G, independent of P.
- The point c is defined over algebraic constants, so later derivations annihilate it.
- The finite descent and re-decomposition retain the correct closed-point multiplicities and degrees.
- Both smooth and nodal specialization cases produce actual Cartier divisors with proved multidegrees.

**Exclude.** Allowing a new model per point destroys the fixed lattice needed for the lossless estimate. Matching valuations alone does not prove triviality on normalization components; the node reductions are required. A Picard class must be turned into an actual rigidified line bundle before taking its divisor.

Proposed names: `jacobian_point_integral_add_constant_fixedModel`.

### S31

**Construct fixed Jacobian and multiplicative models with connected finite torsion**

Stage 5. Owner: `MochizukiHom/Picard/Model.lean`
Prerequisites: I05, I07, S12, S25, S30.
Source: `lem:ordinary-picard-model-core`, statement lines 1659-1674 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A complete mixed-characteristic (0,p) DVR field K and S equal either to the usual Jacobian of a smooth proper geometrically connected curve or to G_m.

**Output.**
- After a finite constant extension, one smooth commutative group algebraic space G/R0 with generic fibre S, fppf-surjective [p^n], and a connected BT group C whose finite torsion is the open finite flat subgroup G-hat[p^n]⊆G[p^n].
- The actual identities omega_(C[p^n])=omega_G/p^n*omega_G and a saturated inclusion T_pC⊆T_pS, together with constant-point correction in this same G.

**Proof steps.**
1. For a Jacobian, combine split semistable reduction and S25 to construct the single algebraic-space model.
2. Prove multiplication is fppf surjective and apply formal division to the identity completion, obtaining the compatible connected finite flat open kernels and their conormal modules.
3. Prove the finite transition maps satisfy the BT axioms and identify their generic torsion points with reductions of the inverse-limit Tate module.
4. If p*t lies in T_pC, use t_n=(p*t)_(n+1) and the p^n-torsion condition to put t_n in C[p^n] at every n; deduce saturation.
5. Import S30 for the fixed Jacobian model.
6. For G_m use the multiplicative integral model and mu_(p^n); choose an algebraic constant with the same valuation as a given point to obtain an integral unit quotient.

**Acceptance.**
- All torsion, completion, conormal and Tate maps refer to the same model G.
- The word 'ordinary' means usual Jacobian and does not become an ordinary-reduction assumption.
- Connected BT compatibility and saturation are proved, not included as unverified fields of an assumed model package.
- The result permits imperfect residue fields and p=2.
- No inertia, Kummer-transfer or linearization theorem is assumed in constructing this model.

**Exclude.** Packaging downstream conclusions as model data creates circularity. Confusing ordinary Jacobians with ordinary reduction weakens the field scope. Finite-level torsion kernels must agree with the Tate inverse-limit transitions.

Proposed names: `exists_fixedPicardModel`, `fixedPicardModel_connectedTorsion`, `fixedPicardModel_tate_saturated`.

### I08

**Detect prime-to-p actions modulo p on saturated invariant lattices**

Stage 6. Owner: `MochizukiHom/Profinite/Basic.lean`
Prerequisites: none.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation).

**Input.**
- A finite-free Z_p module H with continuous action of a profinite group G, a closed normal N, and a pro-prime-to-p quotient G/N.
- U=H^N; in the Tate application H=Hom_Zp(T_1,T_2).

**Output.**
- U is finite free and p-saturated in H, hence U/pU embeds in H/pH.
- Any subgroup of G whose action on U/pU is trivial acts trivially on U; this applies for p=2.
- For the Tate application, adjoining S_1[p] and S_2[p] is sufficient to kill the action on all of U.

**Proof steps.**
1. From p h in U and p-torsion-freeness of H, prove sigma h=h for every sigma in N.
2. Prove finite freeness and the injective reduction map.
3. For each n, filter the kernel of GL(U/p^n) -> GL(U/p) by congruence level; identify successive factors with additive F_p subspaces.
4. The finite image of G/N has prime-to-p order, so its intersection with this p-group kernel is trivial.
5. Use intersection p^n U=0 to recover equality of the full action from all finite levels.

**Acceptance.**
- The congruence-kernel proof works at p=2 without replacing p-torsion by p^2-torsion.
- Saturation is proved before reduction injectivity.
- The fixed finite extension is uniform for all u in U.

**Exclude.** Invoking a torsion-free congruence subgroup theorem that excludes p=2. Assuming invariants commute with reduction without saturation.

Proposed names: `invariantLattice_p_saturated`, `primeToP_action_detected_mod_p`, `tateInvariant_action_killed_by_pTorsion`.

### S32

**Prove a uniform exponent for unramified connected finite p-groups**

Stage 6. Owner: `MochizukiHom/Picard/Inertia.lean`
Prerequisites: none.
Source: `lem:finite-connected-unramified-exponent`, statement lines 1696-1702 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A Henselian mixed-characteristic (0,p) DVR R0, e=v_pi(p), s>=0 with (p-1)*p^s>e, and a finite flat commutative p-group Q/R0 with connected special fibre and unramified generic fibre.

**Output.**
- Equality of group-scheme maps [p^s]_Q=0, with the exponent depending only on e and p, not the order, height or dimension of Q.

**Proof steps.**
1. Trivialize the generic finite etale group over a finite unramified extension. Extend its generic points over the integer ring using finite properness and normality; connectedness forces reduction to the identity.
2. Split the Hopf algebra as R0⊕I and choose a basis of its finite free augmentation ideal.
3. Use cyclic permutation of the p-fold comultiplication tensors: one-factor terms give p*x_i, nonfixed orbits contribute to p*I^2, and fixed nonzero tensors lie in I^p.
4. For a nonidentity point with minimum coordinate valuation a>=1 prove a([p]g)>=min(e+a,p*a).
5. Iterate to exceed e/(p-1) after at most s steps unless already zero. Above the threshold prove the exact next valuation e+a; a nonzero point in this region can never be killed by further p-powers.
6. Use p-power torsion to deduce vanishing of [p^s] on all generic points, then characteristic-zero etaleness and flatness to obtain equality of group-scheme maps.

**Acceptance.**
- The Hopf-algebra orbit calculation is proved explicitly.
- The strict valuation equality above the threshold is proved, in addition to the lower bound.
- The numerical exponent has no hidden dependence on Q.
- The result uses Henselianity, not an unrequested completeness or perfection assumption.

**Exclude.** A lower bound alone does not contradict eventual torsion; strict equality above the threshold is required. Pointwise equality must be promoted to equality of maps using the generic fibre and flatness.

Proposed names: `finiteConnected_unramified_killed_by_uniform_pPower`.

### S33

**Generate a connected BT Tate representation by inertia differences**

Stage 6. Owner: `MochizukiHom/Picard/Inertia.lean`
Prerequisites: I05, S14, S32.
Source: `lem:connected-bt-no-unramified-direct`, statement lines 1723-1741 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A connected BT group C over a Henselian mixed-characteristic DVR, T=T_pC, inertia I_K and s satisfying the uniform-exponent inequality of S32.
- Define M as the algebraic Z_p-submodule generated by all (sigma-1)t, sigma in I_K, t in T.

**Output.**
- p^s*T⊆M, the rational equality V_pC=span_Qp{(sigma-1)v}, and vanishing of Hom_GK(V_pC,W) for every finite-dimensional unramified Q_p-representation W.

**Proof steps.**
1. Use normality of inertia to prove M is G_K-stable.
2. For each m, identify T/(M+p^m*T) as an unramified quotient of C[p^m](Kbar). Descend the generic quotient and take the schematic closure of its kernel.
3. Apply finite-flat closure and quotient to obtain a finite flat Q_m with connected special fibre and the specified unramified generic quotient.
4. S32 kills every Q_m by the same p^s, so p^s*T lies in every M+p^m*T.
5. Use Noetherian finite generation and p-adic separatedness of T/M to identify the intersection with M, without assuming an infinite sum is closed.
6. Rationalize and observe that every equivariant map to an unramified representation kills the spanning differences.

**Acceptance.**
- M is the generated submodule, not an unspecified topological closure.
- Each Q_m is an actual finite flat quotient with the required connectedness and generic action.
- One common exponent works for all m.
- Both the integral inclusion and the two rational consequences are exported.

**Exclude.** Assuming closure of the infinite sum skips the separatedness argument. An abstract representation quotient must be realized by finite-flat group schemes before using S32.

Proposed names: `connectedBT_inertiaDifferences_contains_pPower`, `connectedBT_inertiaDifferences_span`, `connectedBT_to_unramified_eq_zero`.

### S34

**Characterize the connected Tate lattice intrinsically**

Stage 6. Owner: `MochizukiHom/Picard/Inertia.lean`
Prerequisites: S33.
Source: `cor:picard-connected-inertia-span`, statement lines 1767-1780 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A connected BT group C over a complete mixed-characteristic DVR and a saturated equivariant embedding T_pC -> T into a finite free Z_p representation, with unramified quotient.
- V=T⊗Q_p and W_I(V) the Q_p-span of all inertia differences.

**Output.**
- T_pC = T ∩ W_I(V) inside V; equivariant maps preserve these lattices.
- Rationally surjective maps are surjective on the connected rational subspaces; the lattice is unchanged by finite field extension and hence by choices of fixed models satisfying the hypotheses.

**Proof steps.**
1. Use the unramified quotient to put W_I(V) inside V_pC.
2. Apply S33 to C for the reverse inclusion, then use saturation to intersect back with T.
3. Apply equivariance to the defining inertia differences for functoriality.
4. For rational surjectivity lift each target inertia-difference generator before taking spans.
5. After finite extension, retain geometric connectedness of C and the unramified quotient and repeat the same characterization. Compare both lattices inside the fixed rational Tate space.

**Acceptance.**
- The equality is an equality of actual embedded Z_p-submodules.
- Saturation is used exactly in passing back from the rational space.
- Finite-extension invariance and rational-surjectivity are separate usable results.
- No model-independence conclusion is used before the characterization is proved.

**Exclude.** Unramified quotient without saturation does not recover the integral lattice. Rational equality alone is insufficient for constructing an integral formal map.

Proposed names: `connectedTate_eq_inter_inertiaSpan`, `connectedTate_map_surjective_rational`, `connectedTate_finiteExtension_invariant`.

### S35

**Prove inertia differences lie in connected formal torsion**

Stage 6. Owner: `MochizukiHom/Picard/Inertia.lean`
Prerequisites: I07, S23, S25, S31.
Source: `lem:picard-inertia-difference-connected`, statement lines 1804-1812 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A fixed split semistable model of a proper curve, its multidegree-zero Picard group and Jacobian J, and the finite connected formal torsion C[p^n] of S31.

**Output.**
- For every n>=1, inertia acts trivially on J[p^n](Kbar)/C[p^n](Kbar), and T_pJ/T_pC is torsion-free and unramified.

**Proof steps.**
1. Represent a geometric p^n-torsion point by a signed degree-zero point divisor after a finite Galois extension.
2. For sigma in inertia, compare each point and its sigma-conjugate, which have the same specialization. Use smooth local factoriality or the horizontal node formula to construct their Cartier difference with trivial normalization restrictions.
3. Descend and add these differences to a line bundle N whose generic class is sigma(P)-P.
4. Its p^n-th tensor power is generically trivial and has zero multidegree; S23 makes it globally trivial.
5. The special class of N belongs to the gluing torus of S25 and is killed by p^n. A characteristic-p field has no nontrivial field-valued p-power torsion in this split torus, so the special class is the identity.
6. Use the actual formal-division kernel to identify N with a point of C[p^n]. Pass to the Tate quotient and use saturation from S31.

**Acceptance.**
- The proof reaches equality of the special Picard class with the identity, not merely zero multidegree.
- The finite-level inertia statement is exported for every n.
- The inverse-limit conclusion uses the same embedded torsion groups as S31.
- The torus argument allows imperfect residue fields.

**Exclude.** Zero component degrees do not imply the special Picard class is trivial. Using inertia on only rational Tate modules leaves the integral lattice argument incomplete.

Proposed names: `picard_inertia_difference_mem_connectedTorsion`, `picard_tate_connectedQuotient_unramified`.

### S37

**Realize Tate maps integrally and prove nonvanishing of their differential**

Stage 6. Owner: `MochizukiHom/Picard/Linearization.lean`
Prerequisites: I05, S22, S31, S34, S35, S36.
Source: `prop:ordinary-picard-integral-map-nonzero-core`, statement lines 1864-1886 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- Fixed models G_i/R from S31 over one complete mixed-characteristic DVR, S_i their Jacobian or G_m generic fibres, P_i their coordinate identity completions.
- An actual G_K-equivariant Z_p-linear map u:T_pS_1->T_pS_2 and H_i=T_pP_i embedded in T_pS_i.

**Output.**
- u(H_1)⊆H_2 and a unique integral formal homomorphism F_u:P_1->P_2 inducing this restriction.
- Its generic differential is functorial for addition, Z_p-scalars, identities, composition and finite constant extension, agrees with any pre-existing integral realization, and is nonzero if u_Qp is onto with positive-dimensional S_2 or if S_1=G_m and u≠0.

**Proof steps.**
1. Apply the actual inertia calculation S35 and intrinsic lattice characterization S34; for G_m use H_i=T_pS_i. Deduce preservation of H_i.
2. Invoke the proved formal Tate-extension theorem S22 on the restricted map. Its uniqueness yields the required algebraic and base-extension naturalities.
3. Under rational surjectivity, lift inertia differences to prove surjectivity on connected rational Tate spaces.
4. If the target has positive dimension, use omega_(P_2[p])=omega_(P_2)/p and finite-flat rank preservation to prove P_2[p](Kbar)≠0, hence H_2≠0 via I05.
5. Thus F_u is nonzero; S36 implies its differential is nonzero. For G_m source, use H_1=T_1 directly.

**Acceptance.**
- S22 is present as a proved dependency; no full-faithfulness or realization package is an added input.
- The equality on the actual Tate restriction is part of the exported realization theorem.
- Both nonvanishing alternatives are proved separately with their exact hypotheses.
- The generic differential comes from an integral formal map over the original model ring.
- Functoriality equations are outputs derived from uniqueness.

**Exclude.** Assuming the desired formal map in a LinearizationData structure is circular. Nonzero algebraic target dimension alone does not imply nonzero Tate restriction without the connected-torsion argument.

Proposed names: `tateMap_preserves_connectedLattice`, `exists_unique_integralFormal_realization`, `integralLinearization_nonzero`.

### S38

**Compare formal and algebraic differentials using finite torsion graphs**

Stage 6. Owner: `MochizukiHom/Picard/Linearization.lean`
Prerequisites: I05, I06, S36.
Source: `lem:formal-graph-torsion-compatibility`, statement lines 1922-1934 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- Smooth commutative group algebraic spaces G_i over a complete mixed-characteristic DVR R; coordinate completions P_i with finite-free [p]; separated target generic fibre S_2.
- An algebraic group map f:S_1->S_2 and an integral formal map F:P_1->P_2 agreeing as actual maps to S_2 on P_1[p^n]_K for every n.

**Output.**
- dF⊗K=df. In particular this applies when T_pF is the restriction of T_pf; after generic base change their formal series agree as well.

**Proof steps.**
1. Choose identity affine etale charts after finite unramified extension. Form the formal graph map B=O(U_1×U_2)->A=R[[X]].
2. The inverse image of the algebraic graph is generically closed. Contract its ideal from B[1/pi] to B and prove localization recovers it.
3. For A_n=A/J_n representing finite formal torsion, use formal etale uniqueness to identify the specialized formal graph with the actual torsion graph.
4. Generic torsion agreement and R-flatness of A_n imply every graph-ideal element maps into every J_n.
5. Use the division-ideal separation theorem I06 to kill this image.
6. Evaluate the resulting graph relation on X=epsilon*v in K[epsilon]/epsilon^2 to identify tangent maps; descend from the chosen charts and field extension. Use S36 for the formal-series equality.

**Acceptance.**
- The graph ideal and each specialization map are explicitly identified.
- The proof invokes intersection_n J_n=0 on actual formal division ideals.
- The Tate-map hypothesis is converted to equality on finite torsion via the finite-level comparison.
- R[[X]][1/pi] is never identified with K[[X]].

**Exclude.** These two power-series rings are not interchangeable. Torsion-point equality must be interpreted as equality of the actual generic finite-torsion maps before using the graph ideal.

Proposed names: `formal_algebraic_graph_differential_eq`, `formal_realization_differential_eq_of_tate_eq`.

### S39

**Descend all equivariant Tate maps to a uniform finite local stage**

Stage 6. Owner: `MochizukiHom/Picard/Linearization.lean`
Prerequisites: I08, S02, S26, S28.
Source: `lem:subtame-finite-local-tate-descent`, statement lines 1960-1978 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A fixed p-subtame realization K->T=M^tame⊆Omega=algebraic closure of M, with M complete and separably closed residue field.
- Actual Jacobians or G_m over K, chosen models over one finite M0/M inside T, their Tate modules in Omega, and a G_K-equivariant Z_p-linear map u.

**Output.**
- Every such u is G_L-equivariant for L=M0(S_1[p],S_2[p]); L is finite and depends only on the two chosen groups, not on u.
- The same assertion for finite K1/K inside the fixed Omega with its chosen valuation; neither M0 nor L is required to contain K or K1.

**Proof steps.**
1. Descend the finitely many group equations and operations to M0. Let H=Hom_Zp(T_1,T_2), N=G_T, and U=H^N.
2. Use normality of N to make U stable under G_M0; prove saturation of U by cancelling p in H. Deduce the injection U/pU->H/pH.
3. Restrict G_T automorphisms to algebraic K-constants to show the given G_K-equivariant u belongs to U without an inclusion M⊆K.
4. The action on U factors through the pro-prime-to-p quotient Gal(T/M0). Apply I08 at each finite p^n level: a reduction kernel that is both a p-group and of prime-to-p order is trivial.
5. By definition of L its absolute Galois group acts trivially on both p-torsion groups, hence on H/pH and on U/pU. The preceding finite-level argument and p-adic separatedness make it act trivially on U.
6. For K1=K(alpha), replace M by M(alpha), use tame base change and the persistence of separably closed residue fields, and repeat inside the same Omega.

**Acceptance.**
- The returned stage is exactly the mod-p torsion field of the chosen finite-stage group models.
- The saturation injection and finite prime-to-p congruence calculation are proved and used.
- The p=2 instance is accepted without changing to mod-4 torsion or assuming a torsion-free congruence subgroup.
- The statement does not require any complete local stage to contain the original K.
- The finite-K1 version preserves the ambient algebraic closure and valuation.

**Exclude.** Assuming the original K contains M, or that M0 contains K, invalidates the general p-subtame application. The group 1+2*Mat(Z_2) is not torsion free; the proof needs only finite congruence p-groups. An individual finite stage for each matrix entry does not prove uniform descent of all u.

Proposed names: `subtame_tateMap_equivariant_modPTorsionField`, `subtame_tateMap_finiteConstantExtension_descent`.

### S40

**Define a model-independent linearization over the fixed algebraic closure**

Stage 6. Owner: `MochizukiHom/Picard/Linearization.lean`
Prerequisites: S31, S34, S37, S38, S39.
Source: `lem:ordinary-picard-linearization-elementary`, statement lines 2007-2033 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A fixed p-subtame valued realization K->M^tame⊆Omega and a G_K-equivariant Tate map between actual Jacobians or G_m.
- More generally, a Tate map that becomes equivariant over some finite local extension of M may be used in the same construction.

**Output.**
- An Omega-linear map lambda_u:Lie(S_1)_Omega->Lie(S_2)_Omega independent of finite local stage and fixed model, obtained by differentiating an integral formal realization.
- Additive, scalar, identity, composition and finite-constant-extension naturality; equality lambda_(T_pf)=df for every algebraic group map over Omega; both S37 nonvanishing alternatives.
- Only when K itself is complete discretely valued, an additional proof that the construction descends to a K-linear map. No such descent is asserted for general p-subtame K at this stage.

**Proof steps.**
1. Use S39 to choose a finite local stage for u and enlarge it for the fixed models; apply S37.
2. Compare two choices over a common finite extension of M. S34 identifies their actual connected Tate lattices.
3. Use S37 to realize the identity on the common lattice in both directions and prove the formal comparison maps are inverse by uniqueness.
4. Use S38 on the actual identity algebraic map to show these comparison maps have identity differential on the algebraic Lie spaces. Deduce independence of lambda_u.
5. Obtain all naturality equations from uniqueness. Descend any algebraic map over Omega to finite coefficients, then use S38 to identify its differential.
6. In the separately stated complete-DVR case, compare Galois-conjugate models and descend the invariant differential matrix to K.

**Acceptance.**
- The default codomain is an Omega-linear map; general K-linearity is not an input or a conclusion.
- Choice independence compares actual Lie-space identifications, not only abstract ranks.
- Algebraic-map compatibility covers maps defined over Omega via finite coefficient descent.
- The finite-local descent S39 is an explicit prerequisite.
- All functoriality and nonvanishing claims are proved outputs.

**Exclude.** G_K need not preserve the auxiliary local field M, so naive Galois descent of the local differential is invalid. Model-independent Tate lattices alone do not identify differentials; S38 supplies that missing step.

Proposed names: `subtameLinearization`, `subtameLinearization_independent`, `subtameLinearization_of_algebraicMap`, `subtameLinearization_nonzero`.

### I09

**Discharge the auxiliary-cover transfer hypothesis over the fixed p-subtame test field**

Stage 7. Owner: `MochizukiHom/Reconstruction/CurveMap.lean`
Prerequisites: S02, S26, S28, S39, S41, S42, S48.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation).

**Input.**
- A fixed valued realization K⊆M^tame⊆Omega, a finite local coefficient model for the original source, a Gauss completion F for that model, and the fixed field L=F^nr*Omega.
- One arbitrarily chosen auxiliary pair U,V and base-point data from the hypothesis of S49, descended to a finite constant extension K1/K inside Omega, its actual equivariant Tate map u, a finite T/L, and z in U(T).

**Output.**
- For this exact T and z, choose m with [T:L]|p^m and prove u_m(kappa_m(alpha_U(z))) belongs to the Kummer image of J_V(T). Quantification over the arbitrary data gives the entire transfer hypothesis of S49.
- Omega, L and their valuation stay fixed; the auxiliary finite local model field may depend on U,V,u and is not required to contain K or K1.

**Proof steps.**
1. For the chosen U,V use finite presentation and the finite-K1 version of S39 to descend the actual groups and u to a finite extension M_aux/M inside Omega; enlarge finitely for their fixed Picard models.
2. Inside T form F_aux=F*M_aux. Since M_aux/M is finite and the original F contains a finite extension of M, this compositum is finite over the complete DVR field F and is complete discretely valued.
3. Use the single ambient valuation to prove O_(F_aux) dominates the selected model ring.
4. Since T/L is finite and L/F is algebraic, T/F_aux is algebraic; it contains Omega and has separably closed residue field by S48.
5. Apply S41 to the exact field T and point alpha_U(z), at any finite level, obtaining the required Kummer-image statement without enlarging T.
6. Use the pro-p absolute Galois group of L from S48 to express [T:L] as a p-power and choose m sufficiently large. Generalize over every initially arbitrary cover, component, finite extension and point.

**Acceptance.**
- The construction is repeated separately for each auxiliary cover while keeping L fixed.
- The chosen F_aux is a subfield of the existing T, and the realizing target point stays in J_V(T).
- No assertion K⊆F or K⊆M_aux appears; original objects are compared over Omega before taking their T-base change.
- The adapter proves exactly the quantified hypothesis of S49, including all base-point/component choices.
- The degree-divisibility condition is explicitly discharged using the pro-p test-field theorem.

**Exclude.** Choosing one finite local stage for infinitely many covers is not justified and is unnecessary. A proof over a larger replacement field T' does not establish the required statement over T. Requiring the original p-subtame field to be a complete local subfield loses the intended conclusion.

Proposed names: `subtame_allAuxiliaryCovers_finiteKummerTransfer`.

### S41

**Transfer finite Kummer images through actual torsor pushouts**

Stage 7. Owner: `MochizukiHom/Kummer/FormalPoints.lean`
Prerequisites: I05, S29, S31, S37, S39.
Source: `lem:ordinary-kummer-image-transfer`, statement lines 2072-2091 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A finite complete local stage M0 for two fixed models and an equivariant Tate map u, obtained from the p-subtame data; an F/M0 complete DVR extension dominating the model ring.
- An algebraic E/F containing Omega and having separably closed residue field; P in S_1(E), n>=1.

**Output.**
- There exists Q_n in S_2(E) such that u_n(kappa_(S1,n)(P))=kappa_(S2,n)(Q_n) in the actual H1(E,S_2[p^n]). Q_n is chosen separately for each n; no inter-level compatibility is asserted.

**Proof steps.**
1. Identify O_E as strictly Henselian and the finite formal map v_n=F_u[p^n] with the restriction of u_n on generic torsion.
2. Use fixed-model correction P=z+c. Divisibility of S_1(Omega) kills the constant's finite Kummer class.
3. Apply S29 to lift the [p^n]-division torsor of z to a C_1[p^n]-torsor.
4. Push out along v_n and then C_2[p^n]->G_2[p^n].
5. Use the target Kummer surjectivity in S29 to represent this pushout by one integral target point.
6. Commute generic-fibre restriction with these actual pushouts and Kummer maps to obtain the required equality in H1.

**Acceptance.**
- Every torsor and group map in the pushout diagram is the one produced by the fixed models.
- The resulting point lies in the same E, without an unrecorded field enlargement.
- Finite-level Tate compatibility identifies v_n with u_n before the cohomology equality is claimed.
- The quantifier order is forall n, exists Q_n, not exists Q, forall n.

**Exclude.** A compatible family of Q_n is neither constructed nor needed. An abstract equality of cohomology groups does not establish the naturality of the required pushout diagram.

Proposed names: `subtame_finiteKummerImage_transfer`.

### S42

**Embed a curve function field into a Gauss completion with a bounded derivation**

Stage 7. Owner: `MochizukiHom/Reconstruction/CurveMap.lean`
Prerequisites: none.
Source: `lem:generic-polydisc`, statement lines 2109-2127 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A smooth geometrically integral finite-type curve T/K over a complete mixed-characteristic (0,p) DVR field.

**Output.**
- A finite Galois K'/K, a Gauss completion F=completion(K'(t)), an actual embedding E=K'(T)->F, and a continuous K'-derivation D extending d/dt with D(E)⊆E and D|_E an E-basis of Der_(K')(E,E).
- The unique extension to L=F^nr*Kbar with D(Kbar)=0 and v(Da)>=v(a), hence D(O_L)⊆O_L. The normalized valuation has v(p)=1.

**Proof steps.**
1. Choose a rational smooth point after finite Galois extension and an etale coordinate with an equation P(z,y)=0, normalized at the point.
2. Choose a single sufficiently large scaling m so substituting z=pi^(2m)*t, y=pi^m*w gives pi^(-m)P=w+pi*H with integral coefficients; simultaneously clear the finite chart denominators.
3. Hensel-lift w in the Gauss valuation ring. Transcendence of z supplies a generic curve point and hence the function-field embedding; record t=pi^(-2m)*z in E.
4. Prove the Gauss valuation inequality for polynomial differentiation, extend by the quotient rule and then continuously to F.
5. Differentiate separable minimal polynomials to prove preservation of E and uniqueness of extension; D(t)=1 gives its basis property.
6. For finite constant extensions identify the compositum with the corresponding Gauss completion. For finite unramified extensions use formal etale lifting on dual numbers to extend D integrally.
7. Take the union to L, prove D kills algebraic constants, and divide any nonzero element by a same-valued constant to upgrade integral preservation to the full valuation inequality.

**Acceptance.**
- The returned object is the Gauss completion of a rational function field, not a Laurent-series field.
- The actual field embedding and the identity locating t in E are retained.
- Both preservation of E and the Der basis assertion are proved.
- The extension to L is unique and preserves the integer ring without calling L a complete DVR.
- Later simultaneous shrinking may enlarge the finite denominator list; the theorem supports an explicitly recorded finite list.

**Exclude.** A small analytic point is not enough: the embedding must be generic. Differentiation bounded on K'(t) requires a continuity proof before extending to F. Finite etale extensions and arbitrary algebraic extensions have different integral-derivation behavior.

Proposed names: `exists_genericGaussCurvePoint`, `gaussDerivation_functionField_basis`, `gaussDerivation_unramifiedConstants_bound`.

### S43

**Define logarithmic derivatives as actual tangent vectors**

Stage 7. Owner: `MochizukiHom/Kummer/FormalPoints.lean`
Prerequisites: none.
Source: `unlabelled:logarithmic-derivative`, statement lines 2174-2184 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A smooth commutative group G/R0, an R0-algebra R, an R0-derivation D:R->R, and a point z in G(R); use the finite locally free invariant cotangent/Lie modules relevant to the fixed models.

**Output.**
- A canonical tangent vector partial_D(z) in Lie(G)⊗R characterized by pairing with every invariant differential eta as pairing(z^*eta,D).
- Additivity and the equality partial_D(f(z))=df(partial_D(z)) for each actual group morphism f; compatible base change and integrality for integral D and z.

**Proof steps.**
1. Use the invariant-differential description of the cotangent module and finite local freeness to construct the unique tangent vector from the prescribed pairings.
2. Differentiate the group law to prove additivity and compatibility with multiplication by integers.
3. Use pullback of invariant differentials and the chain rule to prove naturality for actual group maps.
4. Prove the base-change formula and the integral-lattice assertion by evaluating integral invariant differentials against an integral derivation.

**Acceptance.**
- Existence and uniqueness of the tangent vector follow from the actual cotangent/Lie duality.
- Additivity and naturality are theorems about the constructed vector, not fields of its definition.
- The integral version is available for the fixed Picard lattice in S45.

**Exclude.** Postulating an abstract derivative satisfying desired equations skips the geometric construction. The derivation must annihilate the indicated base ring; later changing base fields requires a proved compatibility.

Proposed names: `logarithmicDerivative`, `logarithmicDerivative_add`, `logarithmicDerivative_map`, `logarithmicDerivative_integral`.

### S44

**Use one formal point for all finite Kummer levels and its derivative**

Stage 7. Owner: `MochizukiHom/Kummer/FormalPoints.lean`
Prerequisites: I05, S12, S43.
Source: `lem:formal-point-kummer-compatibility`, statement lines 2187-2208 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- Smooth separated group algebraic spaces G_i over a complete mixed-characteristic (0,p) DVR R (the standing local context), fixed affine etale identity charts, coordinate completions P_i with finite-free [p], an integral formal map phi:P_1->P_2, and an equivariant Tate map u agreeing with T_p(phi) on the formal Tate lattice.
- A complete DVR extension F/K dominating R and x in P_1(m_F); for the differential assertion, a continuous K-derivation D of F preserving O_F.

**Output.**
- The single evaluated actual point q=phi(x) in P_2(m_F)⊆S_2(F) satisfies kappa_n(q)=u_n*kappa_n(x) for every n>=1.
- For that same q, partial_D(q)=dphi(partial_D(x)).

**Proof steps.**
1. Use positive coordinate valuations to prove convergence of every integral formal series at x; evaluate the identity-chart ring map to construct q as an actual integral point.
2. At each n, base change finite-free formal division along x. Choose a generic point of the resulting finite flat algebra to obtain y over a finite F_n/F with [p^n]y=x.
3. Connected support of the special division fibre puts y in the formal maximal-ideal neighbourhood.
4. Compare the Kummer cocycles sigma(phi(y))-phi(y)=phi(sigma(y)-y)=u_n(sigma(y)-y) via finite-level Tate comparison.
5. Evaluate the formal invariant-differential identity and use continuity of D to differentiate convergent series, giving the derivative formula for the already constructed q.

**Acceptance.**
- The quantifier order is exists q, forall n, and q is explicitly phi(x).
- The same formal map defines both finite Kummer classes and the differential.
- Formal evaluation produces actual points through the fixed etale charts.
- The finite division points retain positive valuation.
- Termwise differentiation is justified by continuity and convergence.

**Exclude.** The separate Q_n of S41 do not satisfy this theorem and cannot be substituted for q. A formal power series evaluation must be connected to an actual algebraic-space point.

Proposed names: `formalPoint_allFiniteKummer_compatible`, `formalPoint_logarithmicDerivative_compatible`.

### S45

**Derive the exact p^n differential congruence in one fixed lattice**

Stage 7. Owner: `MochizukiHom/Kummer/FormalPoints.lean`
Prerequisites: S31, S43, S44.
Source: `cor:fixed-picard-point-differential-core`, statement lines 2229-2243 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- The data of S44 with target the Jacobian J and its one fixed model G_2 from S31.
- An algebraic E/F containing algebraic constants, a K-derivation D on E preserving O_E with continuous restriction to F, and z in J(E) with kappa_n(z)=u_n*kappa_n(x).

**Output.**
- partial_D(z)-dphi(partial_D(x)) belongs to p^n*Lie(G_2)⊗O_E, with the exponent exactly n and the integral lattice fixed independently of z, n and auxiliary covers using this model.

**Proof steps.**
1. Take the single q=phi(x) of S44. The finite Kummer equality and exact sequence give z-q=[p^n]w for some w in J(E).
2. Use the fixed-model correction from S31 to write w=w0+a with w0 integral in G_2 and a constant.
3. A characteristic-zero K-derivation annihilates algebraic constants, so partial_D(a)=0.
4. Apply logarithmic-derivative additivity and S44 to identify the difference with p^n*partial_D(w0).
5. Integral invariant differentials and D(O_E)⊆O_E place partial_D(w0) in the specified integral Lie lattice.

**Acceptance.**
- The bound is p^n, not p^(n-c) with an implicit point-dependent c.
- The same fixed G_2 is used for w0 and the output lattice.
- The derivation-annihilates-constants lemma is applied to the actual chosen constant field.
- Any later coordinate denominator bound is recorded separately from this intrinsic lattice statement.

**Exclude.** Changing the model when correcting w removes the uniform lattice. Untracked denominators weaken the lossless estimate needed for reconstruction.

Proposed names: `fixedPicard_kummer_difference_differential_mem_pPower`.

### S46

**Trivialize an abelian torsor from finite section precision and a degree bound**

Stage 7. Owner: `MochizukiHom/Kummer/Approximation.lean`
Prerequisites: S07, S09.
Source: `lem:divided-torsor-transfer`, statement lines 2281-2288 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A field F with char(F)≠p, an abelian variety A/F, an A-torsor T, and an actual section s:G_F->Pi_T of its geometrically pro-p arithmetic fundamental group.
- m=p^a, a finite extension E/F with d=[E:F] dividing m, and P in T(E) whose point-section difference from s|G_E vanishes in H1(E,A[m]).

**Output.**
- An actual F-rational point of T; no global point of T is assumed when defining the arithmetic extension or the section-difference convention.

**Proof steps.**
1. Handle m=1 directly. Choose t0 over Fsep and form c_sigma=sigma(t0)-t0.
2. Choose finite Galois data containing t0, A[m] and the needed division points; realize the division cover A->T, z|->t0+[m]z and its deck group of pairs (sigma,b) with m*b=c_sigma.
3. Prove the pair multiplication law and count automorphisms, then use actual-cover comparison to identify the finite quotient of Pi_T. Fix that geometric (1,b) corresponds to -b under the chosen Kummer convention.
4. Write the section as a continuous cocycle b_sigma. Choose z with m*z=P-t0 and use the vanishing H1 class to adjust z by A[m] so the affine action beta_sigma(w)=sigma(w)+b_sigma fixes z for sigma in G_E.
5. The degree hypothesis makes E/F separable. Sum beta_tau(z) over G_F/G_E to form v and prove sigma(v)+d*b_sigma=v.
6. Show t0+(m/d)*v is G_F-fixed and descend it to the required point.

**Acceptance.**
- The actual finite division cover, pair-extension identification and sign convention are proved before averaging.
- The finite extension is shown separable from d|p^a and char(F)≠p.
- The coset sum is independent of representatives.
- The final point is invariant under the full absolute Galois group and is descended as a scheme point.
- The a=0 case is not lost.

**Exclude.** Defining the argument using an F-point of T assumes its conclusion. A sign mismatch in the pair extension changes the cancellation c_sigma-m*b_sigma. The finite precision must have m divisible by the extension degree.

Proposed names: `abelianTorsor_hasPoint_of_section_finitePrecision`.

### S47

**Obtain a curve point from a degree-one Picard class by determinant cancellation**

Stage 7. Owner: `MochizukiHom/Kummer/Approximation.lean`
Prerequisites: none.
Source: `lem:twisted-trace-picard`, statement lines 2330-2336 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A characteristic-zero field F with pro-p absolute Galois group, a smooth proper geometrically connected curve C/F of genus g, and an F-point of the degree-one Picard sheaf.
- Either p is odd or g is odd; an arbitrary finite closed subscheme B⊆C.

**Output.**
- An F-rational point of C outside B. The input Picard-sheaf point is not assumed to be a line bundle defined over F.

**Proof steps.**
1. Reduce B and choose m>2g-2+deg(B) with p not dividing m*(m+1-g); prove existence using the parity hypothesis.
2. Over a finite Galois F'/F represent the Picard class by a degree-one line bundle M and choose conjugation isomorphisms with scalar defect cocycle c_(sigma,tau).
3. Use Riemann–Roch and duality to obtain V=H0(M^m), h=m+1-g, and a section s not vanishing on B. Choose a determinant basis d.
4. The scalar defects cancel on M^(m*h)⊗(det V)^(-1); explicitly prove its honest semilinear action and set w=s^h⊗d^(-1).
5. Form the twisted trace R_a(w)=sum_sigma sigma(a)*sigma(w). Independence of field embeddings makes each forbidden vanishing condition a proper F-linear subspace of F'; avoid the finite union, or test the generic point when B is empty.
6. Its zero divisor descends, has positive degree m*h prime to p, and avoids B. Since all finite G_F-orbits have p-power size, one support orbit has size one.

**Acceptance.**
- The scalar cocycle and determinant cancellation remain explicit; no Brauer-obstruction vanishing is assumed.
- The p=2 branch uses g odd at the residue-selection step.
- The descended divisor is effective with multiplicities, has positive prime-to-p degree, and avoids B.
- The empty-B case still proves a nonzero trace section.
- A rational support point follows from the pro-p orbit argument and is returned as an actual point.

**Exclude.** A rational point of Pic^1 need not descend to a degree-one line bundle. Dropping the genus parity condition for p=2 invalidates the chosen residue argument. A degree computation without descended divisor data does not yield an F-point.

Proposed names: `curve_point_away_of_picardOnePoint_proP`.

### S49

**Approximate point sections at each finite precision using all auxiliary covers**

Stage 7. Owner: `MochizukiHom/Kummer/Approximation.lean`
Prerequisites: I03, S07, S09, S26, S28, S46, S47.
Source: `lem:proper-source-point-approximation-core`, statement lines 2386-2413 of frozen version 78.
Detailed proof: [P03: Picard models inertia and Kummer approximation](#p03-picard-models-inertia-and-kummer-approximation). Search the source label within that section.

**Input.**
- A characteristic-zero field K, X a smooth proper geometrically connected curve or G_m, a proper hyperbolic curve Y/K, and a continuous G_K-homomorphism theta:Pi_X->Pi_Y.
- A field L/K containing the fixed algebraic closure of K with pro-p absolute Galois group; no valuation or completeness is assumed on L.
- For every a>=2, every actual Delta_Y^ab/p^a-cover V, each geometric component U of its theta-pullback, every base-point choice, every finite T/L and z in U(T): there exists m>=1 with [T:L]|p^m for which the induced actual Tate map sends kappa_m(alpha_U(z)) into the Kummer image of J_V(T).

**Output.**
- For every x in X(L) and n>=1, there exists y in Y(L) whose abelianized point-section difference from theta_L(s_x) lies in p^n*Hom_cont(G_L,T_pJ_Y). Each precision may choose a different y; no coherence or convergence of the y is asserted.

**Proof steps.**
1. Choose a>=max(n,2), split the finite quotient over L using constant points, and write theta_L(s_x) as (rho_a(g),g). Construct the twist Y_a^s by the quotient (q,g)|->q-rho_a(g).
2. Prove the twist geometrically connected, lift s by relative pro-p cover exactness, and push its section along the actual degree-one Abel–Jacobi map to the Pic^1 torsor.
3. Let T/L be fixed by ker(rho_a), a finite p-power extension. Over T identify the twist with V_T, lift x to a point z in one actual pullback component U, and descend all finite component/base-point data to a finite constant field.
4. Use the actual finite Abel–Jacobi or multiplicative Kummer identification and vanishing of the constant cocycle on G_T to identify the section difference with the finite Kummer image in the hypothesis.
5. Choose its supplied precision m and realizing Jacobian point. Apply S46 with [T:L]|p^m to obtain a point of the twisted Pic^1 torsor over L.
6. Compute g(Y_a^s)-1=p^(2*g(Y)*a)*(g(Y)-1). For p=2 the genus is odd, so S47 provides an L-point of the twisted curve.
7. Its image y has section difference zero modulo p^a. Since L contains the torsion constants, the Tate action is trivial; divide the continuous homomorphism by p^a using the homeomorphism to p^a*T_pJ_Y.

**Acceptance.**
- The transfer hypothesis quantifies over every auxiliary cover, actual pullback component and finite T/L.
- The local adapter I09 is not an input to this abstract theorem; it is used later to discharge this hypothesis in the p-subtame application.
- The constant base-point cocycle is proved to restrict trivially on the relevant G_T.
- For p=2 the odd-genus premise of S47 is derived from the actual cover degree.
- The conclusion has quantifier order forall n, exists y and asserts divisibility in Hom_cont, not just pointwise membership without continuity.

**Exclude.** Transfer proved only for the original X,Y does not cover the necessary U,V. Assuming a valuation on L weakens the abstract theorem unnecessarily. Compatible approximation points are an unproved stronger conclusion. Using equality of dimensions instead of the actual finite Abel–Jacobi maps loses section compatibility.

Proposed names: `properCurve_pointSection_finitePrecision_approximation`.

### S50

**Generate the canonical affine chart by ratios and first derivatives**

Stage 8. Owner: `MochizukiHom/Curves/Basic.lean`
Prerequisites: none.
Source: `lem:canonical-first-jet`, statement lines 2480-2499 of frozen version 78.
Detailed proof: [P04: Reconstruction from differentials](#p04-reconstruction-from-differentials). Search the source label within that section.

**Input.**
- A smooth proper geometrically connected curve C/k in characteristic zero with genus at least two, and a basis omega_0,...,omega_(g-1) of its regular differentials.
- U = {omega_0 != 0}, A = O(U), r_i = omega_i/omega_0, db = delta(b) omega_0, h_i = delta(r_i), and B = k[r_i].

**Output.**
- The canonical map is finite onto its image with degree one or two; in degree one it is a closed immersion; in degree two the image is a smooth genus-zero curve and the hyperelliptic involution is central and acts by -1 on regular differentials.
- U is affine, A is finite over B, and A = B + sum_i B h_i = k[r_i,h_i].
- For every nonconstant r_j, k(C) = k(r_i,h_j).

**Proof steps.**
1. Use Riemann-Roch to prove base-point freeness of the canonical system, then finiteness onto the canonical image. Compare 2g - 2 = d deg(L) with h0(L) <= deg(L) + 1 to obtain d <= 2.
2. In degree two, prove the normalized image has genus zero and the complete canonical-image linear series embeds it. Identify the quadratic involution; descend invariant rational differentials using their local order formula, obtaining its -1 action and centrality.
3. In degree one, prove that failure to separate a length-two subscheme would produce a degree-two pencil and hence a canonical map of degree two. Apply the length-two separation criterion to get a closed immersion.
4. Restrict to the canonical affine chart. In degree one A = B. In degree two, prove A is locally free of rank two over the regular one-dimensional B and split A = B direct_sum M using the involution.
5. Locally write A = B[z]/(z^2-a). Compute invariant Kahler differentials and identify them both with Omega_B/k and with M omega_0. Since dr_i generate Omega_B/k, conclude M = sum_i B h_i.
6. For nonconstant r_j, characteristic zero gives h_j != 0; in degree two it is anti-invariant, so adjoining it to the ratio subfield gives the full function field. Descend geometric statements faithfully flatly.

**Acceptance.**
- The exported ring equality is an equality of actual subalgebras of O(U), not only an equality of fraction fields.
- The degree-two canonical image is allowed to be a nonsplit genus-zero curve over k.
- The invariant-differential calculation includes the relation 2z dz = da and does not assume the double cover is etale.
- The Stacks Riemann-Roch input is instantiated with the actual locally free dualizing sheaf and its smooth-curve comparison.
- All field-generation claims explicitly require the chosen r_j to be nonconstant.

**Exclude.** Dropping derivative generators in the hyperelliptic case. Identifying a genus-zero curve with P1 over k without a rational point. Proving birational generation only and using it later as integral affine generation.

Proposed names: `canonical_map_degree_one_or_two`, `canonical_chart_generated_by_first_jets`, `functionField_generated_by_canonical_ratios_and_derivative`.

### S51

**Recover an exact algebra map from independent finite-precision values**

Stage 8. Owner: `MochizukiHom/Reconstruction/FiniteValues.lean`
Prerequisites: none.
Source: `lem:finite-values-algebra-map`, statement lines 2556-2564 of frozen version 78.
Detailed proof: [P04: Reconstruction from differentials](#p04-reconstruction-from-differentials). Search the source label within that section.

**Input.**
- Fields k ⊆ E ⊆ L, an additive real-valued nonarchimedean valuation v on L with v(0) = infinity, a finitely generated k-algebra B = k[b_1,...,b_m], and values z_i in E.
- For every positive integer N, an independently chosen k-algebra map phi_N:B -> L satisfying v(phi_N(b_i)-z_i) >= N for all i.

**Output.**
- A unique k-algebra map psi:B -> E with psi(b_i) = z_i.
- For each b in B, v(phi_N(b)-psi(b)) tends to infinity; no completeness assumption is used.

**Proof steps.**
1. For every polynomial P prove P(x)-P(z) = sum_i (x_i-z_i) Q_i(x,z).
2. Use convergence of the finite coordinates to obtain eventual lower valuation bounds for x_i and hence for each Q_i, independent of N.
3. Deduce P(phi_N(b))-P(z) tends to zero in valuation. When P(b)=0, separatedness of the valuation forces P(z)=0.
4. Factor polynomial evaluation at z through the actual presentation ideal of B to obtain psi.
5. Use generation for uniqueness and the same polynomial estimate for convergence on arbitrary b.

**Acceptance.**
- The theorem takes forall N, exists phi_N, with no compatibility condition between different N.
- The relation-killing argument is proved for every polynomial in the kernel of the actual algebra presentation.
- Eventual estimates account for the finitely many initial N and finite coordinate set.
- Neither completeness nor an analytic limit is assumed for E or L.

**Exclude.** Assuming limits in E exist instead of factoring polynomial evaluation. Using a bound for polynomial coefficients that depends on N. Replacing the common approximation map for all generators at one N by unrelated maps per generator.

Proposed names: `algebraMap_of_approximate_generator_values`, `valuation_tendsto_for_generated_elements`.

### S52

**Reconstruct a unique nonconstant point from one bounded derivation**

Stage 8. Owner: `MochizukiHom/Reconstruction/FiniteValues.lean`
Prerequisites: S50, S51.
Source: `prop:proper-finite-precision-reconstruction-core`, statement lines 2577-2596 of frozen version 78.
Detailed proof: [P04: Reconstruction from differentials](#p04-reconstruction-from-differentials). Search the source label within that section.

**Input.**
- Characteristic-zero fields k ⊆ E ⊆ L with E/k finitely generated of transcendence degree one, and an additive valuation v on L.
- A derivation D:L -> L with D(k)=0, D(E)⊆E, D restricted to E nonzero, and v(Db)>=v(b) for all b.
- A proper hyperbolic curve C/k, a nonzero k-linear map a:H0(C,omega_C)->Omega_E/k, and one fixed basis omega_i.
- For every positive N there exists y_N in C(L) simultaneously approximating evaluation of a(omega_i) on D to valuation at least N; the points need not be compatible.

**Output.**
- A unique nonconstant q in C(E) with actual differential pullback q^* = a; consequently a is injective.

**Proof steps.**
1. Identify Omega_E/k with E by evaluation on the nonzero derivation D|E. Put A_i=<a(omega_i),D> and choose A_0 != 0.
2. For sufficiently large N, beta_0,N=<y_N^*omega_0,D> is nonzero and has valuation v(A_0), so y_N lies in the canonical affine chart U.
3. Prove the actual evaluation identities phi_N(r_i)=beta_i,N/beta_0,N and phi_N(h_i)=D(phi_N(r_i))/beta_0,N.
4. Use boundedness of D and explicit denominator bounds to approximate R_i=A_i/A_0 and H_i=D(R_i)/A_0 to arbitrarily high common precision.
5. Apply S51 to the ring generators supplied by S50 to construct psi:O(U)->E and q in U(E).
6. Write omega_i as a finite sum c_ij db_j in those generators. Pass the finite valuation estimates through this identity and the derivation to prove <q^*omega_i,D>=A_i, hence q^*=a.
7. Use A_0 != 0 for nonconstancy and separability for differential injectivity. Any second solution has the same r_i,h_i values, so S50 gives uniqueness.

**Acceptance.**
- Both canonical ratios and their derivative generators are controlled with one common precision for the entire finite set.
- Every division by A_0 or beta_0,N has a proved valuation bound and an explicit eventual precision shift.
- The conclusion q^*=a is checked on actual regular differentials, not inferred only from equality of ratios.
- The theorem does not require completeness, convergence of y_N, a subsequence, or compatible points.
- The dependency on S51 is explicit even though the original citation graph omits it.

**Exclude.** Conflating a fixed formal-group point with a compatible sequence of curve approximation points. Applying a one-dimensional differential argument to an arbitrary-dimensional source. Stopping after constructing a rational point without proving its prescribed pullback.

Proposed names: `exists_unique_point_of_bounded_derivation_approximation`.

### S53

**Prove faithfulness of differential pullback in arbitrary source dimension**

Stage 8. Owner: `MochizukiHom/Curves/Basic.lean`
Prerequisites: S50.
Source: `lem:proper-differential-faithfulness-core`, statement lines 2641-2646 of frozen version 78.
Detailed proof: [P04: Reconstruction from differentials](#p04-reconstruction-from-differentials). Search the source label within that section.

**Input.**
- An integral characteristic-zero k-scheme X, a proper hyperbolic k-curve Y, and two dominant rational maps f,g:X -->> Y.
- Equality of their pullbacks H0(Y,omega_Y)->Omega_k(X)/k.

**Output.**
- Equality f = g as rational maps, without a restriction on the dimension of X.

**Proof steps.**
1. Choose a target differential omega_0 whose common pullback alpha is nonzero; prove nonvanishing using dominance and characteristic-zero separability.
2. Use f^*omega_i = g^*omega_i to show equality on r_i=omega_i/omega_0.
3. Apply dR_i=(f^*h_i) alpha=(g^*h_i) alpha and nonzero alpha to show equality on all h_i.
4. Use S50's actual affine ring generators to identify the two function-field embeddings and hence the rational maps.

**Acceptance.**
- No hypothesis states that Omega_k(X)/k has dimension one.
- The nonzero common pullback alpha is proved from dominance, not included as an extra theorem hypothesis.
- Equality is equality in the actual rational-map type with compatible source and target structure maps.

**Exclude.** Reusing S52's one-dimensional evaluation isomorphism for higher-dimensional X. Using canonical ratios alone when Y is hyperelliptic.

Proposed names: `dominant_rationalMap_ext_of_differential_pullback`.

### S54

**Assemble an actual geometric curve map from Picard and Kummer approximation**

Stage 8. Owner: `MochizukiHom/Reconstruction/CurveMap.lean`
Prerequisites: I09, S02, S28, S39, S40, S42, S44, S45, S48, S49, S52, S53.
Source: `prop:proper-curve-reconstruction-core`, statement lines 2656-2674 of frozen version 78.
Detailed proof: [P04: Reconstruction from differentials](#p04-reconstruction-from-differentials). Search the source label within that section.

**Input.**
- A p-subtame K with a fixed auxiliary embedding K -> M^tame ⊆ Omega=algebraicClosure(M), where M is the complete auxiliary field from S02.
- X/K is a smooth proper geometrically connected curve or G_m, Y/K is proper hyperbolic, and theta:Pi_X->Pi_Y is continuous over G_K, without an openness assumption.
- u is the actual Tate abelianization of theta, lambda_u is the linearization from S40, and a_theta=alpha_X^* lambda_u^* is nonzero.

**Output.**
- A unique nonconstant Omega-morphism f_Omega:X_Omega->Y_Omega with f_Omega^*=a_theta.
- Compatibility with finite constant extensions inside Omega, actual morphisms between finite cover diagrams, and geometric Omega-linear deck transformations.

**Proof steps.**
1. Descend one finite collection of curves, base points, Abel-Jacobi maps and Tate data to a finite local stage M0/M using S39; do not require K⊆M0.
2. After a finite enlargement obtain the fixed integral Picard models and the integral formal map F_u.
3. Apply S42 with all Abel-Jacobi chart coordinates and denominators included in the Gauss scaling. Obtain E0=M0(X0)⊆F=completed M0(t), a source point x, and a formal-neighbourhood point xi=alpha_X0(x).
4. Put L=F^nr Omega. Prove the extended derivation D annihilates Omega, preserves E0, is nonzero on E0, and is valuation-nonincreasing on all of L.
5. Evaluate F_u once at xi to obtain the fixed q. Use S44 for its Kummer class at every p-power level and its logarithmic derivative identity.
6. Use I09 to establish the auxiliary-cover transfer input inside each fixed finite T/L. Each finite diagram may have its own local stage; T already contains the corresponding compositum with Omega.
7. Use S48 and S49 to choose independent curve points y_n in Y(L) matching q at precision n. Use S45 for simultaneous differential approximation in a fixed integral basis.
8. Apply S52 over M0⊆E0⊆L, extend the generic point to the smooth source curve by properness of Y, and base change to Omega. Use S53 for uniqueness.
9. For each finite cover diagram, place its data at one common finite stage. Naturality of the integral formal map gives differential naturality, and S53 promotes it to equality of geometric morphisms and deck equivariance.

**Acceptance.**
- The theorem does not assume theta open and does not claim the reconstructed map is already defined over K.
- The formal point q is fixed before all finite-level comparisons, while y_n may vary independently.
- The transfer hypotheses hold for every finite T/L without extending T.
- Every use of the valuation on Omega is confined to the chosen realization; arbitrary Aut(Omega/K) is not assumed to preserve it.
- All geometric base changes in a cover diagram are made over their chosen common constant field and preserve the actual map identities.

**Exclude.** Requiring one finite local field for infinitely many covers. Requiring the finite local stage to contain K. Attempting K-descent by valuation invariance of arbitrary field automorphisms. Moving the approximate point to an extension of the specified finite test field.

Proposed names: `exists_unique_geometric_curveMap_of_nonzero_linearization`, `geometric_reconstruction_natural`.

### I10

**Identify proper base change with the actual arithmetic fibre-product group**

Stage 9. Owner: `MochizukiHom/FundamentalGroup/Basic.lean`
Prerequisites: I02, S04, S07.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom).

**Input.**
- A characteristic-zero field extension E/K, a smooth proper geometrically connected curve Y/K, compatible geometric points, and the actual arithmetic exact sequences and proper finite-etale base-change equivalence.

**Output.**
- A continuous isomorphism Pi_(Y_E) ≃ Pi_Y ×_(G_K) G_E, commuting with both projections and restricting to the actual geometric pro-p base-change isomorphism.
- Naturality for the field extensions and morphisms required in descent and curve reduction.

**Proof steps.**
1. Instantiate proper geometric finite-etale base change with the actual curves and geometric points; compare their actual fibre functors.
2. Use the fibre-functor equivalence to prove the isomorphism of geometric groups and pass to the characteristic pro-p quotients.
3. Construct the canonical arithmetic map to the fibre product from the structure map and the field Galois homomorphism.
4. Use the two arithmetic exact sequences and the geometric isomorphism to prove bijectivity, then compact-Hausdorff topology to prove a topological group isomorphism.
5. Prove projection identities and naturality by comparison of actual finite-cover pullbacks.

**Acceptance.**
- The isomorphism is over G_E and its projection to Pi_Y is the actual induced base-change homomorphism.
- The claim is restricted to the proper geometry where the cited base-change theorem applies.
- The proof does not require E/K algebraic or replace G_E by a pro-p quotient.
- All chosen geometric points and induced conjugacy comparisons are explicit.

**Exclude.** Using only an abstract isomorphism of geometric groups to assert an arithmetic fibre-product identification. Applying proper base-change invariance silently to a nonproper curve.

Proposed names: `proper_relativeProP_baseChange_fibreProduct`.

### I11

**Glue the separated-source Hom theorem over a nonseparated curve**

Stage 9. Owner: `MochizukiHom/Hom/ProperCurves.lean`
Prerequisites: I02, I04, S04.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom).

**Input.**
- A smooth geometrically connected finite-type K-curve X, a separated proper hyperbolic Y/K, and a continuous open theta:Pi_X->Pi_Y over G_K.
- As an explicit argument, the full Hom equivalence for separated smooth geometrically connected source curves over K; this argument will be supplied inside S57.

**Output.**
- Existence and uniqueness of a dominant X->Y realizing theta, and an abstract transfer of the separated-source equivalence to the nonseparated-source case.

**Proof steps.**
1. Choose an affine open cover of X. Use normality and nonempty-open generic-point comparison to prove Pi_U -> Pi_X is surjective for each relevant affine U.
2. Compose theta with these surjections; the resulting maps are open. Apply the supplied separated-source theorem to construct dominant maps f_U:U->Y.
3. On intersections, use further affine open refinements and the supplied uniqueness theorem to prove equality of restrictions.
4. Glue the actual morphisms over K. Dominance follows from a nonempty affine member; equality of arithmetic maps is detected by one surjective Pi_U -> Pi_X and the corresponding geometric conjugator.
5. Prove uniqueness by restriction to the affine cover and conclude the equivalence using I04.

**Acceptance.**
- I11 imports no completed proper-target theorem S57; the separated-source theorem is a conditional argument.
- The gluing is in the actual scheme category and the resulting morphism is over K.
- The arithmetic realization uses a single chosen member's conjugator and a surjective source-group map.
- No global separatedness of X is introduced.

**Exclude.** Creating a dependency cycle I11 -> S57 -> I11. Assuming the local geometric conjugators agree on overlaps rather than using morphism uniqueness and surjectivity.

Proposed names: `nonseparated_curveHom_of_separated_curveHom`.

### S08

**Reduce open Hom to surjective Hom without losing uniqueness**

Stage 9. Owner: `MochizukiHom/Hom/ProperCurves.lean`
Prerequisites: S07, S10.
Source: `lem:open-image-hom-reduction`, statement lines 446-452 of frozen version 78.
Detailed proof: [P01: Fields and actual covers](#p01-fields-and-actual-covers). Search the source label within that section.

**Input.**
- A geometrically connected source X/K in the relevant source class, a hyperbolic target Y/K, and a continuous open G_K-homomorphism theta between actual relative pro-p arithmetic groups or actual full profinite arithmetic groups.
- A full existence-and-uniqueness statement for surjective homomorphisms, applicable to the finite cover of Y constructed from the image.

**Output.**
- An explicit reduction from theta to a surjection onto the arithmetic group of a geometrically connected finite-etale cover Y_H/K.
- A realization for the surjection yields a realization of theta; two realizations of theta induce compatible lifts after the prescribed conjugation, so uniqueness for the cover yields uniqueness downstairs.
- The reduction is available separately for the relative pro-p and full profinite versions.

**Proof steps.**
1. Prove H = image(theta) is an open subgroup of the target arithmetic group and maps surjectively to G_K.
2. Realize H by the actual finite-etale cover Y_H -> Y and prove geometric connectedness using H -> G_K.
3. Apply the actual relative-cover identification in the pro-p version to identify Pi_YH with H; retain the actual inclusion into Pi_Y.
4. Factor theta as a surjective homomorphism to H and transport it to Pi_YH.
5. Compose the resulting dominant realization with Y_H -> Y; for uniqueness, use the lifting criterion on actual covers and track the geometric base-point conjugation.

**Acceptance.**
- The finite cover is defined over K and is geometrically connected, rather than silently passing to a larger constant field.
- The group identification commutes with the inclusion into the original target and the projections to G_K.
- Both existence and uniqueness reductions preserve the prescribed geometric conjugacy class.
- The full profinite statement and the relative pro-p statement have separate verified instances of the cover identification.

**Exclude.** Assuming the relative pro-p group of an arbitrary cover is automatically its open subgroup. Proving existence but omitting the lift argument needed for uniqueness. Treating an open image as equal to the target group.

Proposed names: `open_hom_reduces_to_surjective`, `open_full_profinite_hom_reduces_to_surjective`.

### S55

**Kill the full geometric image of every multiplicative-source homomorphism**

Stage 9. Owner: `MochizukiHom/Hom/ProperCurves.lean`
Prerequisites: S02, S07, S40, S54.
Source: `lem:gm-geometric-zero-proper-core`, statement lines 2742-2748 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A p-subtame K, a proper hyperbolic Y/K, and a continuous G_K-homomorphism beta:Pi_Gm->Pi_Y; no openness is assumed.
- The actual section at 1 and Delta_Gm=Z_p(1), including the cyclotomic conjugation relation.

**Output.**
- The restriction of beta to the full geometric group Delta_Gm is trivial, not merely its composition with the abelianization of Delta_Y.

**Proof steps.**
1. Suppose the image z of a geometric topological generator is nontrivial and choose an actual finite arithmetic quotient detecting z.
2. Take the inverse image H in Delta_Y of the cyclic subgroup generated by the detected image of z. Use the cyclotomic relation to prove the arithmetic section normalizes H.
3. Use H times the section image to obtain a geometrically connected proper hyperbolic cover C->Y and lift beta to Pi_C via S07.
4. The chosen cyclic quotient proves that the resulting Z_p(1)->T_p J_C is nonzero. Apply multiplicative-source nonvanishing in S40 and geometric reconstruction S54.
5. Extend the resulting nonconstant G_m,Omega->C_Omega to P1_Omega by properness. A nonzero differential on C has nonzero pullback by separability, contradicting the vanishing of regular differentials on P1.

**Acceptance.**
- The finite cover detects every hypothetical nontrivial z in an abelian quotient of its own geometric subgroup.
- The proof never invokes openness of beta.
- The final conclusion is beta|Delta_Gm=1 on the whole pro-p group.
- The auxiliary reconstructed morphism is used over Omega and is not assumed to descend to K.

**Exclude.** Concluding total geometric vanishing from vanishing of the original target abelianization. Assuming the desired open-target theorem to construct the detecting cover.

Proposed names: `gm_hom_to_proper_hyperbolic_kills_geometric`.

### S56

**Factor maps from open or generic source curves through compactification**

Stage 9. Owner: `MochizukiHom/Hom/ProperCurves.lean`
Prerequisites: I02, S02, S55.
Source: `prop:proper-compactification-factorization-core`, statement lines 2769-2776 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A p-subtame K, a smooth proper geometrically connected curve X/K, a dense open U⊆X or U=Spec K(X), a proper hyperbolic Y/K, and a continuous G_K-homomorphism theta:Pi_U->Pi_Y.

**Output.**
- A unique continuous G_K-homomorphism Pi_X->Pi_Y whose composite from Pi_U is theta, with exactly the same image and therefore the same openness property.

**Proof steps.**
1. Precompose with the generic arithmetic Galois group. For each boundary point, pass to a finite constant extension making it rational; prove this does not change the relevant inertia and keeps the field p-subtame.
2. Use the equal-characteristic-zero Henselian local description to identify the chosen decomposition group with Zhat(1) semidirect G_K'. Construct the splitting from a chosen uniformizer and compatible roots; an exact sequence alone is insufficient.
3. Since the target geometric kernel is pro-p, factor the inertia part through Z_p(1) semidirect G_K'=Pi_Gm and apply S55.
4. Use the theorem that closed-point inertia normally generates the kernel of G_K(X)->pi1(X), and then quotient the geometric prime-to-p kernel to factor through Pi_X.
5. Use generic-point surjectivity to prove agreement with theta, uniqueness and equality of images.

**Acceptance.**
- The generic-point case is included in the exported interface.
- The local semidirect-product splitting is constructed with parameter choices and is not asserted canonical.
- The factor map has exactly the original image, not merely an image contained in it.
- No injectivity of a decomposition group into Pi_Y is used.

**Exclude.** Treating an inertia exact sequence as a canonical splitting. Killing only geometric boundary inertia after a field extension without relating it to the original group. Using an assumed Hom theorem in place of S55.

Proposed names: `hom_to_proper_factors_through_compactification`, `generic_hom_to_proper_factors_through_curve`.

### S57

**Prove full Hom for proper targets and all smooth finite-type source curves**

Stage 9. Owner: `MochizukiHom/Hom/ProperCurves.lean`
Prerequisites: I04, I11, S02, S05, S07, S08, S40, S53, S54, S56, S59.
Source: `thm:proper-local-curve-hom-core`, statement lines 2808-2820 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A p-subtame K, a smooth geometrically connected finite-type curve X/K that need not be separated, and a proper hyperbolic curve Y/K.
- The actual relative pro-p arithmetic groups and geometric conjugacy relation.

**Output.**
- The full dominant-morphism/open-G_K-homomorphism equivalence for (X,Y), including realization of each entire prescribed arithmetic homomorphism by one geometric conjugator.
- For proper X, the reconstructed map satisfies a_theta=(f_Omega)^* in the fixed auxiliary realization.

**Proof steps.**
1. For proper X, apply S08 and work with a surjective theta. Its Tate map is surjective and the positive-dimensional target Jacobian gives nonzero linearization; reconstruct one f_Omega using S54.
2. For each open normal arithmetic quotient N, form the actual torsors V->Y and W->X. Determine their common finite Galois constant field E and base change the selected components over E to Omega.
3. Apply S07 and S54 to obtain r_V:W_Omega->V_Omega. Differential naturality and S53 prove v r_V=f_Omega w and geometric deck equivariance.
4. An equivariant morphism of torsors under the same finite group is an isomorphism; prove this on fibres and descend. Obtain equality of geometric quotient maps for every N.
5. Use cofinality of N intersection Delta_Y and S05 to obtain one geometric conjugator. Apply S59 for K-descent and equality of the entire arithmetic homomorphism.
6. For separated open source curves, use S56 and proper extension of actual morphisms to reduce to the proper-source case.
7. Supply this separated-source theorem to the abstract gluing result I11; thereby obtain the nonseparated statement without a dependency cycle. Use I04 for the forward-map openness and package the inverse laws.

**Acceptance.**
- The proof treats arithmetic torsors over their shared relative constant field E, not an incorrectly connected base change over K.
- The one conjugator is obtained by compactness, without assuming compatible choices of the reconstructed r_V.
- The full arithmetic equality comes from S59 and not from geometric equality alone.
- The public theorem includes nonseparated smooth finite-type curves and the stated proper-source linearization compatibility.
- I11 is proved as an abstract gluing reduction before S57; it does not import S57.

**Exclude.** Confusing surjectivity of theta with surjectivity of a map on an incorrectly chosen connected component. Assuming the local p-adic reconstruction is invariant under arbitrary field automorphisms. A circular implementation in which gluing imports the final theorem that uses it.

Proposed names: `proper_target_curveHomEquiv`, `proper_source_realization_linearization_spec`.

### S59

**Descend the reconstructed proper-curve map and recover the whole arithmetic map**

Stage 9. Owner: `MochizukiHom/Hom/ArithmeticRecovery.lean`
Prerequisites: I05, I10, S07, S26, S27, S53, S58.
Source: `lem:curve-field-descent`, statement lines 2909-2919 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero k, smooth projective geometrically connected X/k, proper hyperbolic Y/k, an open G_k-homomorphism theta:Pi_X->Pi_Y, and a nonconstant map f_L:X_L->Y_L over an extension L/k.
- After the actual proper geometric base-change identifications, the geometric outer homomorphism of f_L equals theta restricted to Delta_X.

**Output.**
- Tate and differential faithfulness for homomorphisms of actual abelian varieties in characteristic zero.
- Faithfulness of the Tate map and hence of the geometric pro-p outer homomorphism on nonconstant maps to a proper hyperbolic curve.
- A unique k-morphism descending f_L and inducing theta on all of Pi_X up to one fixed geometric conjugation; the relevant geometric centralizer is proved trivial rather than assumed.

**Proof steps.**
1. For an abelian-variety homomorphism v, show T_p v=0 kills each actual p^n-torsion group. If the kernel has dimension h and M components, compare p^(2n dim A) with M p^(2nh) for all n to prove v=0.
2. If dv=0, use smoothness of characteristic-zero algebraic-group kernels to obtain the same dimension conclusion. Relate actual Jacobian, Tate and differential maps via the Abel-Jacobi comparisons.
3. Use S53 to deduce equality of nonconstant curve maps with the same geometric Tate map or pro-p outer homomorphism.
4. Over an algebraically closed Omega containing L, arithmetic equivariance of theta makes f_Omega and every sigma f_Omega induce the same geometric outer map. Faithfulness makes them equal.
5. Apply S58 to the pullback of k(Y) inside Omega(X), descend the function-field embedding to k(X), and extend to X by normal proper-curve extension.
6. Choose one geometric conjugation making the two geometric homomorphisms equal. For each gamma, the difference z=f_*(gamma)^(-1)theta(gamma) lies in Delta_Y and centralizes their common open geometric image H.
7. If z is nontrivial, choose open normal N in Delta_Y contained in H and excluding z. The deck automorphism z of the corresponding proper hyperbolic cover acts trivially on N^ab and hence on its Tate module; curve faithfulness makes it the identity, a contradiction.
8. Conclude every difference z is one, so the already chosen conjugator compares the whole arithmetic homomorphism.

**Acceptance.**
- Abelian-variety faithfulness refers to actual p^n-torsion, transition maps, Jacobians and differentials.
- Descent uses Aut(Omega/k) on the chosen algebraically closed extension, including possible transcendental constants.
- The centralizer proof does not assume slimness or the main Hom theorem.
- The same geometric conjugator works for every arithmetic gamma.
- The exported descent conclusion agrees with the original f_L after base change, not only at the level of fundamental groups.

**Exclude.** Using invariants under G_k alone when Omega/k has transcendental constants. Allowing a separate conjugator for each arithmetic element. Claiming zero differential implies zero group map without a characteristic-zero kernel-smoothness argument.

Proposed names: `abelianVariety_hom_ext_of_tate`, `abelianVariety_hom_ext_of_differential`, `curveMap_ext_of_geometric_outerHom`, `curveMap_descends_and_realizes_arithmetic`.

### I12

**Give connected finite-etale covers their relative constant-field structures**

Stage 10. Owner: `MochizukiHom/FundamentalGroup/Basic.lean`
Prerequisites: I02, S04.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom).

**Input.**
- A characteristic-zero K, a normal geometrically integral finite-type K-scheme X, and a connected actual finite-etale cover Z->X.
- E is the relative algebraic closure of K in the actual function field K(Z).

**Output.**
- E/K is finite separable; Z is normal and integral and has an actual finite-type geometrically integral E-scheme structure.
- The maps of arithmetic fundamental groups and constant quotients agree with this structural map; if K is p-subtame, the separate closure theorem S02 applies to E.

**Proof steps.**
1. Use etale stability of normality and connectedness of a noetherian normal scheme to prove integrality of Z.
2. Prove finite generation of K(Z)/K and finiteness of its relative algebraic constant field E; characteristic zero gives separability.
3. For each affine normal chart of Z, an element of E is integral over K and hence over the chart ring; normality places it in that chart ring. Glue these maps to E->globalSections(Z).
4. Define Z->Spec E from these actual regular functions and prove finite type.
5. Relative algebraic closedness together with characteristic-zero separability makes K(Z)/E regular; infer geometric integrality of Z/E and identify the actual arithmetic constant quotient.

**Acceptance.**
- The E-structure on Z is constructed from regular functions, not inferred only from a function-field inclusion.
- Geometric integrality is over E and need not hold over K.
- The proof applies to nonseparated X and Z through affine normal charts.
- The arithmetic constant quotient agrees with the finite field E appearing in the torsor description.

**Exclude.** Assuming a connected finite-etale cover of a geometrically integral K-scheme remains geometrically connected over K. Omitting extension of algebraic constants to regular functions.

Proposed names: `connected_finiteEtale_relativeConstants`, `finiteEtale_geometricallyIntegral_over_relativeConstants`.

### I13

**Handle dimension zero and preserve dominance under rational-variable descent**

Stage 10. Owner: `MochizukiHom/Hom/NormalSources.lean`
Prerequisites: I02, S26.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom).

**Input.**
- A normal geometrically integral finite-type scheme X/K in characteristic zero, with F=K(X), and a proper hyperbolic target Y/K.
- For the positive-dimensional descent clause, an actual point q in Y(F) whose base change to F(t) is dominant as a K-map.

**Output.**
- When trdeg_K F=0, F=K, Delta_X=1, both the dominant-morphism set and the open G_K-homomorphism set to Y are empty, and their orbit-set equivalence is explicit.
- Dominance of Spec F(t)->Y descends to Spec F->Y; composition of the E-dominant curve map with Y_E->Y is dominant in the curve-reduction situation.

**Proof steps.**
1. Use geometric integrality to prove regularity of F/K; transcendence degree zero then gives F=K. Identify the geometric function-field group and its surjective image Delta_X as trivial.
2. Use the actual finite abelian quotients of the proper target, of orders p^(2gn) for all n, to prove Delta_Y infinite.
3. If a G_K-homomorphism from Pi_X had open image, its intersection with Delta_Y would be the trivial subgroup and open, contradicting infinitude. A dimension-zero source cannot dominate a curve.
4. Construct the empty-set equivalence without calling the positive-dimensional pencil construction.
5. For rational-variable descent, use the actual faithfully flat field extension F->F(t) and topological or function-field dominance to reflect dominance. Prove the composition with the surjective base-change projection Y_E->Y is dominant.

**Acceptance.**
- The dimension-zero branch is a separate proof, not a call to S61 with d=0.
- Infinitude of Delta_Y follows from actual finite quotients and their unbounded orders.
- The dominance statement is about the actual scheme maps used by I14.
- The empty arithmetic Hom side is proved before forming its quotient.

**Exclude.** Assuming a dimension-zero source has a nonempty transcendence basis. Descending a point through pure transcendence without proving the map remains dominant.

Proposed names: `dimensionZero_properHomEquiv`, `dominant_descends_rationalExtension`.

### I14

**Assemble proper-target full Hom for all normal finite-type sources**

Stage 10. Owner: `MochizukiHom/Hom/NormalSources.lean`
Prerequisites: I04, I10, I13, S02, S57, S61, S62, S63.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom).

**Input.**
- A p-subtame K, a normal geometrically integral finite-type K-scheme X without separatedness, and a proper hyperbolic Y/K.
- A prescribed continuous open G_K-homomorphism theta:Pi_X->Pi_Y.

**Output.**
- A dominant f:X->Y realizing theta on the entire arithmetic group with one geometric conjugator, uniqueness of f, and the corresponding proper-target Hom equivalence.

**Proof steps.**
1. Use I13 for transcendence degree zero. Otherwise apply S61 to F=K(X) and obtain one F(t), E and smooth curve U/E->X with surjective geometric group map.
2. Use S02 to prove E p-subtame. Form the actual map Pi_U -> Pi_Y times_GK G_E and use I10 to identify it with Pi_YE. Its geometric image is the original one, hence it is open.
3. Apply S57 to obtain a dominant U->Y_E realizing this prescribed arithmetic map. Take its generic point in Y(F(t)) and use S62 to descend it to q in Y(F).
4. Use I13 to prove q remains dominant. Regularity of F(t)/F gives G_F(t)->G_F surjective, so the same conjugator descends the full arithmetic equality at the generic point.
5. Extract the geometric abelianized factorization through Delta_X and apply S63 to extend q to f:X->Y.
6. Use G_F->Pi_X surjective to detect equality of f_* and theta with the same conjugator.
7. For uniqueness, pull two candidates to the fixed U, apply S57, then descend generic equality to X using separatedness of Y. Use I04 and package the equivalence.

**Acceptance.**
- E is proved p-subtame from finite generation over K, with no local-completeness assumption on E.
- The arithmetic fibre-product identification includes both actual projections.
- The same geometric conjugator is retained through F(t), F and X.
- The normal-source extension is invoked only after its actual geometric abelianized factorization has been proved.
- The exported theorem includes every finite source dimension and no source-separatedness assumption.

**Exclude.** Proving only a map over F(t) and omitting descent to F and extension over X. Changing the arithmetic realization after descending rational variables. Adding the generic factorization required by S63 as an extra hypothesis of the final theorem.

Proposed names: `properTarget_normalFiniteTypeHomEquiv`.

### S61

**Choose one curve reduction uniformly for all finite geometric covers**

Stage 10. Owner: `MochizukiHom/Hom/NormalSources.lean`
Prerequisites: I02, S06, S07, S60.
Source: `lem:regular-cover-curve-reduction`, statement lines 2983-3005 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero k and a regular finitely generated extension F/k of transcendence degree d>=1.
- Optionally, a normal geometrically integral finite-type k-scheme X with function field F.

**Output.**
- A single tuple of d-1 independent variables t and intermediate E⊆F(t), with E/k purely transcendental and F(t)/E regular of transcendence degree one.
- For every finite constant extension k'/k and every finite M/Fk' regular over k', the same t,E satisfy regularity of M(t)/Ek' and preservation of extension degree and, when applicable, Galois group.
- Surjectivity of the actual geometric fundamental-group maps, for both full profinite and relative pro-p groups; when X is given, a smooth finite-type curve U/E with an actual k-morphism U->X and Delta_U/E -> Delta_X/k surjective.

**Proof steps.**
1. Choose a transcendence basis x_1,...,x_d and set u_i=x_i+t_i x_d and E=k(t_i,u_i:i<d). The inverse substitution proves algebraic independence and the dimension claims.
2. Apply S60 successively to prove regularity, using the same expressions after every allowed finite constant and finite function-field extension.
3. Use pure transcendental base change to prove equality of finite degrees and preservation of the actual Galois action.
4. Descend each finite geometric cover to finite constants; its regular function field remains connected under this fixed curve reduction. Apply the actual finite-cover criterion for geometric surjectivity.
5. To construct U->X, choose a nonempty affine chart of X and a separable primitive-element presentation of F(t)/E(x_d). Clear denominators and invert the derivative to obtain a smooth affine curve carrying the chart map.
6. Use the generic-point surjections to pass the previously established geometric surjectivity to U->X.

**Acceptance.**
- The quantifier order is exists (t,E), forall k',M, not forall cover, exists a separate pencil.
- The map U->X is an actual morphism and is compatible with the prescribed function-field embedding.
- Geometric groups record the relative constant fields E and k explicitly.
- The d=1 case is handled with an empty tuple of variables and E=k.
- S60 is an explicit dependency despite its omission from the manuscript reference graph.

**Exclude.** Choosing a new pencil for each cover and then claiming uniform surjectivity. Dropping the finite constant extension from the regularity claim. Constructing only a function-field inclusion without the actual curve-to-X morphism.

Proposed names: `exists_uniform_regular_curve_reduction`, `uniform_curve_reduction_geometric_pi1_surjective`.

### S62

**Remove all rational variables from a point of a positive-genus proper curve**

Stage 10. Owner: `MochizukiHom/Curves/Basic.lean`
Prerequisites: none.
Source: `lem:proper-curve-rational-variables`, statement lines 3043-3047 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero field F, a smooth proper geometrically connected curve C/F of genus at least one, and a finite tuple of algebraically independent variables t.

**Output.**
- The base-change map C(F)->C(F(t)) is bijective, with a proved equality after the canonical embedding of fields.

**Proof steps.**
1. For one variable, interpret a C(F(t))-point as a rational map P1_F -->> C and extend it across all points using properness and regularity of P1.
2. After algebraic closure, a nonconstant map would be separable and pull a nonzero regular differential on C back to a nonzero regular differential on P1, which is impossible.
3. Conclude the map is constant; evaluate at an F-rational point of P1 to show its value lies in C(F).
4. Induct on the finite tuple of variables, preserving properness, geometric connectedness and positive genus under field extension; use field-extension faithfulness for injectivity.

**Acceptance.**
- The result includes genus one and the empty tuple of variables.
- The constant value is proved to lie over F rather than only over an algebraic closure.
- No p-subtame hypothesis, Hom theorem, or formal-group result is used.

**Exclude.** Using the hyperbolic genus>=2 hypothesis unnecessarily. Deducing an F-point from geometric constancy without descent or evaluation.

Proposed names: `proper_positiveGenus_points_rationalExtension_equiv`.

### S63

**Extend a generic-point map using finite abelian covers of a normal source**

Stage 10. Owner: `MochizukiHom/Hom/NormalSources.lean`
Prerequisites: I02, S06, S07, S26.
Source: `lem:normal-cover-extension`, statement lines 3058-3069 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero k, a normal geometrically integral finite-type k-scheme X without a separatedness hypothesis, F=k(X), and a smooth proper geometrically connected k-curve C of genus g>=1.
- An actual q:Spec F->C whose geometric abelianized pro-p homomorphism factors through the actual surjection Delta_SpecF -> Delta_X. Dominance of q is not a hypothesis.

**Output.**
- A unique actual k-morphism X->C extending q.

**Proof steps.**
1. Handle the constant q case: its residue field is algebraic over k and embeds in the regular extension F/k, hence is k; the constant k-point extends directly.
2. For a nonconstant q, work locally on affine X and normalize the closure of its graph in X times C. The projection is proper birational; if a geometric fibre has positive dimension, its map to C is surjective.
3. Choose a quasi-finite affine multisection through the generic point of such a fibre. Normalize the affine base in its finite function field to obtain a fixed finite surjection of degree m, and then a nonzero finite algebra T over the geometric function field of C of dimension m.
4. Choose n with p^(2gn)>m, descend the actual abelian quotient Delta_C^ab/p^n to finite constants, and obtain a geometrically connected finite-etale cover V->C of degree p^(2gn).
5. Use the assumed geometric factorization to descend the pulled-back generic torsor to an actual finite-etale torsor over X. Compare generic torsors component by component using normality; the normalization theorem is applied separately to connected components.
6. Pull a section of the etale fibre through T to obtain an injection of the cover function field into T. Its degree forces p^(2gn)<=m, contradicting the choice of n.
7. All graph-projection fibres are zero-dimensional, so proper plus quasi-finite is finite. A finite birational map to normal X is an isomorphism. Glue affine constructions by target-separatedness uniqueness.

**Acceptance.**
- The exported statement permits arbitrary q and explicitly handles the constant-point case.
- The integer m is fixed before n is chosen; a bound varying with the cover does not prove the contradiction.
- The finite algebra T is only required to be nonzero, not a field or reduced.
- Normalization of disconnected torsors is performed componentwise with matching generic components.
- The required factorization is geometric abelianization only; an unnecessary full arithmetic factorization is not added as an input.
- The proof is local on X and does not acquire a separatedness assumption.

**Exclude.** Assuming q dominant even though the manuscript statement includes constant maps. Applying a normalization theorem for integral covers to a disconnected torsor as one integral object. Treating T as a field or obtaining a degree bound that depends on n.

Proposed names: `extends_of_geometric_abelian_cover_factorization`.

### S03

**Export the exact p-subtame full Hom equivalence**

Stage 11. Owner: `MochizukiHom/Main.lean`
Prerequisites: I02, I04, I12, I14, S02, S65.
Source: `thm:finite-type-hom`, statement lines 259-270 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A prime p, including p = 2, and a characteristic-zero field K with IsPSubtame p K defined by an embedding into a maximal algebraic tame extension of a Henselian mixed-characteristic DVR field.
- An actual normal, geometrically integral, finite-type K-scheme X, without a separatedness assumption, and an actual smooth hyperbolic K-curve Y with chosen smooth proper compactification and integer inequality 2g - 2 + r > 0.
- The actual geometrically pro-p arithmetic groups Pi_X and Pi_Y, retaining the full quotient G_K; morphisms on the group side are continuous, over G_K, and have open image.

**Output.**
- An equivalence Hom_K^dom(X,Y) ≃ Hom_GK^open(Pi_X,Pi_Y)/Inn(Delta_Y), whose forward map is the actual map induced by a dominant scheme morphism.
- For each prescribed open theta, a dominant f and one c in Delta_Y such that f_* and theta agree up to conjugation by c on every element of Pi_X.
- Equality of the geometric conjugacy classes of two induced maps implies equality of the actual K-morphisms; independence of all auxiliary choices follows from this uniqueness.

**Proof steps.**
1. Use I14 to obtain the proper-target theorem with the original p-subtame hypotheses.
2. For every connected finite-etale cover Z of X, use I12 to make Z normal and geometrically integral over its finite separable relative constant field E; use S02 to prove E is p-subtame.
3. Supply these proper-target equivalences to S65. The conditional hypothesis of S65 must disappear from the exported theorem.
4. Use I04 for the forward map, and retain the full-arithmetic realization witness supplied by S65 for every representative theta.
5. Descend the realization map to the geometric-conjugacy orbit set, prove both inverse laws, and export the specified forward-map theorem with the equivalence.

**Acceptance.**
- The elaborated public type has exactly the field, source, target, continuity, openness, and geometric-conjugacy conditions stated above.
- No hypothesis assumes a reconstruction package, a proper-cover Hom theorem, completeness of K, residue perfection, separatedness of X, or oddness of p.
- The realization witness quantifies exists c in Delta_Y, forall gamma in Pi_X, not forall gamma, exists c.
- Both inverse laws use actual scheme-morphism equality and the geometric orbit relation; the forward operation reduces to the defined fundamental-group functor.
- The public entry point imports no diagnostics and its checked dependency closure satisfies I15.

**Exclude.** Replacing the arithmetic group by the total pro-p quotient. Leaving the proper-cover Hom assumption of S65 in the main theorem. Claiming only geometric or abelianized realization. Silently changing this task to a Sigma variant because a different paper is present in the destination folder.

Proposed names: `dominant_induces_open`, `exists_dominant_realizing`, `dominant_hom_injective`, `pSubtameHomEquiv`.

### S64

**Identify actual cusp inertia and construct one proper-hyperbolizing cover**

Stage 11. Owner: `MochizukiHom/Hom/OpenTargets.lean`
Prerequisites: I03, S04, S06, S07, S10.
Source: `lem:cofinal-proper-covers`, statement lines 3116-3121 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero field K, a prime p, and a hyperbolic K-curve Y with smooth proper compactification, geometric genus g and r geometric cusps.

**Output.**
- For every cusp, the actual homomorphism Z_p(1)->Delta_Y is injective.
- One finite arithmetic Galois Pi_Y-cover V0->Y whose proper compactification has hyperbolic geometric connected components; equivalently a specified open normal subgroup N0 of Pi_Y with this property.

**Proof steps.**
1. Construct the actual Kummer residue exact sequence for Lambda=Z/p^a with r>=2 and identify each residue coordinate with the local inertia character of a uniformizer. Rank computations alone do not identify these maps.
2. Use residues 1 at a chosen cusp and -1 at another to detect order p^a in that cusp inertia for every a; infer injectivity of Z_p(1)->Delta_Y.
3. Let s=v_p(r-1) and choose a>s with p^a(2g-2+r)>(r-1)+p^s. Realize residues (1,...,1,-(r-1)) by a connected cyclic p^a-cover.
4. Compute ramification indices p^a at the first r-1 cusps and p^(a-s) at the last. Apply S10 to obtain 2g(compactification)-2=p^a(2g-2+r)-((r-1)+p^s)>0.
5. For r=1, use g>=1 and a nontrivial degree-p etale cover of the compactification to obtain p cusps, then apply the r>=2 construction and transport inertia injectivity through S07. For r=0 use Y itself.
6. Take geometric cores, descend the finite quotient after finite constants, and take an arithmetic core. Prove the proper components remain hyperbolic and record the resulting single N0.

**Acceptance.**
- The residue homomorphism is identified with the actual local Kummer/inertia map; a dimension formula is not accepted as this comparison.
- The construction treats r=0, r=1 and r>=2 explicitly and includes p=2.
- All inequalities use integer genus expressions and positive exponents with a>s.
- The result supplies a single fixed arithmetic normal subgroup N0, not an unspecified family of covers.
- All core and constant-descent operations preserve the claimed proper hyperbolicity.

**Exclude.** Inferring cusp injectivity from H1 rank without identifying residues. Assuming r>=2 throughout or ignoring p=2. Using natural-number truncated subtraction in 2g-2+r.

Proposed names: `cusp_proP_inertia_injective`, `exists_arithmetic_cover_with_proper_hyperbolic_components`.

### S65

**Reduce open-target full Hom to the proper-target theorem on finite covers**

Stage 11. Owner: `MochizukiHom/Hom/OpenTargets.lean`
Prerequisites: I04, I12, S07, S08, S09, S64.
Source: `lem:proper-target-hom-reduction-core`, statement lines 3160-3167 of frozen version 78.
Detailed proof: [P05: Arithmetic recovery and general Hom](#p05-arithmetic-recovery-and-general-hom). Search the source label within that section.

**Input.**
- A characteristic-zero K and a normal geometrically integral finite-type K-scheme X, without separatedness.
- For every connected finite-etale cover Z->X, viewed over its relative constant field E, the full dominant/open Hom equivalence for all proper hyperbolic E-curves. This is a conditional input of the reduction lemma and must be discharged in S03.
- An arbitrary hyperbolic Y/K and a prescribed open G_K-homomorphism theta:Pi_X->Pi_Y.

**Output.**
- The full Hom equivalence for X and Y, with one geometric conjugator realizing each entire prescribed arithmetic homomorphism.

**Proof steps.**
1. Use S08 to assume theta is surjective and fix the single proper-hyperbolizing subgroup N0 from S64.
2. For every open normal N⊆N0 form the actual arithmetic torsors V->Y and W=theta^*V->X with common relative constants E. Apply the supplied proper-target equivalence to obtain r_V:W->compactification(V).
3. Use proper-target uniqueness for transitions and semilinear arithmetic deck transformations to obtain compatibility and descent of r_V0 to a dominant map bar_f:X->compactification(Y).
4. If bar_f meets a boundary divisor, use a height-one point x of its pullback; normality makes O_X,x a DVR. Put e=ord_x(bar_f^*t)>0.
5. Injective cusp inertia gives z^e!=1. Choose N⊆N0 detecting it, so the finite inertia order r does not divide e. Normality of N makes this the ramification index at every branch.
6. At w over x, W->X is etale and hence unramified. The local target equation t=u s^r pulls back to e=r ord_w(r_V^*s), contradicting r not dividing e. Thus all maps avoid the boundary.
7. Use the resulting equivariant maps W->V and their identity on constant quotients to identify W with X times_Y V as actual arithmetic torsors.
8. Apply S09 to the cofinal family N⊆N0 to obtain one geometric conjugator for all Pi_X. For uniqueness, pull a second candidate to W0 and apply the proper-target uniqueness theorem.

**Acceptance.**
- The proper-target equivalence is an explicit conditional argument in S65 and is fully discharged by S03.
- The boundary contradiction uses a height-one DVR on a normal possibly nonseparated source.
- All arithmetic deck actions, including semilinear action on constants, are accounted for before descent.
- Torsor comparisons induce the identity on the arithmetic constant quotient and retain their labels.
- The final conjugator lies in Delta_Y and compares the full Pi_X map, not only the geometric subgroup.

**Exclude.** Treating a conditional reduction theorem as an unconditional completed main theorem. Forgetting arithmetic constant fields in the tower of covers. Showing boundary avoidance but omitting whole arithmetic realization or uniqueness.

Proposed names: `openTargetHomEquiv_of_properCoverHomEquiv`.

### I15

**Certify the final public theorem and its actual checked dependency closure**

Stage 12. Owner: Review the existing `MochizukiHom/Main.lean`; no additional module.
Prerequisites: I01, S03.
Detailed integration or acceptance proof: the steps below and the exact target/common completion rules above.

**Input.**
- Completed Lean declarations for S03 and every dependency in their actual transitive import and proof closure; frozen Stacks, adapted NYLL origins, Lean, mathlib and integration revisions.
- The checklist and concise completion evidence in this file, frozen source revisions and declared owner policy.

**Output.**
- A concise acceptance record in I15's checklist row, tied to the exact checked revision, with exported theorem types, clean kernel/build results, actual axiom dependencies and owner/import checks.
- A final completion decision that cannot be set to complete while a required proof, bridge, semantic invariant or build check remains unverified.

**Proof steps.**
1. Freeze all revisions and verify that the final public theorem imports only the reconciled Stacks-first distribution, without duplicated raw NYLL owners.
2. Run the smallest relevant leaf/interface checks as needed and finally build the public entry point from a clean environment at the frozen revision; record the actual command and exit status in the checklist; do not create an additional reporting file.
3. Inspect the elaborated types of the public equivalence, forward-map specification, realization and uniqueness declarations. Compare all field, source, target and quantifier conditions with the immutable main contract.
4. Inspect actual axiom dependencies of those declarations and the proof closure; reject sorryAx, newly introduced mathematical axioms, native_decide in prohibited contributions, or a conclusion concealed in an input typeclass/structure.
5. Check canonical ownership and import-depth rules against the reconciled package dependency configuration, and ensure finished mathematical sources contain no diagnostic commands or temporary verification material.
6. Review the inline completion evidence for every required task, revision consistency, acyclic prerequisites and the absence of an incomplete required bridge. Record the result in I15's checklist row; file existence alone is not completion.

**Acceptance.**
- The inline completion record names the exact repository revision, toolchain, dependency pins, actual command and exit status for the final clean build.
- The exported theorem passes all field-generalities, p=2, nonseparated-source, open-target, actual-group, one-conjugator, uniqueness and forward-map semantic checks.
- Actual proof dependency inspection excludes sorryAx and unauthorized mathematical axioms; lexical searches alone do not count.
- No unproved conditional reconstruction or proper-cover Hom package appears in the public theorem's assumptions.
- All tasks in the actual required closure have evidence-backed completion at the same compatible revision; earlier source inspection is never counted as Lean verification.

**Exclude.** Marking implementation complete because every task has a prose proof or every file exists. Accepting a successful conditional assembly while its unproved assumptions remain. Reusing build evidence from a different source or dependency revision. Checking only text for sorry rather than the elaborated axiom closure.

Proposed names: `Acceptance.FinalContract`, `Acceptance.DependencyAudit`.

## Detailed proofs

The following mathematical proof sections are retained in full, each once.
All proposed local module names have been reconciled with the compact layout
above. References to existing Stacks and NYLL source paths retain their
original names and revisions. Mathematical notation is directly readable text;
no document build is required.

### P01 Fields and actual covers

#### Fields, actual covers, and one global conjugating element

##### Henselian hosts and closure of the field class

**Source.**

`def:p-subtame-field`, `lem:subtame-host-closure`.

**Modules.**

`Fields/Basic.lean`.

The host-normalization theorem must produce, from a presentation, a complete mixed-characteristic discrete valuation field $M$ with separably closed residue field, an embedding into $T=M^{\mathrm{tame}}$, a uniformizer $\pi$, and $$T=M(\pi^{1/n}:(n,p)=1),\qquad
        \Gamma=\operatorname{Gal}(T/M)\text{ pro-prime-to-}p.$$ The complete field is an auxiliary field; it is not a strengthened hypothesis on $K$. A separably closed residue field may be imperfect.

**Proof dossier.**

The finite-etale Henselian equivalence, Tag [`04GK`](https://stacks.math.columbia.edu/tag/04GK), identifies the unramified extensions with finite separable residue extensions. The tame-root description in Tag [`0EXW`](https://stacks.math.columbia.edu/tag/0EXW) then gives $F^{\mathrm{tame}}=F^{\mathrm{nr}}(\pi^{1/n}:(n,p)=1)$. The ring of integers in $F^{\mathrm{nr}}$ still has value group $\mathbf Z$, uniformizer $\pi$, and residue field $k_F^{\mathrm{sep}}$. Its $\pi$-adic completion is a complete DVR with the same residue field and uniformizer. Call its fraction field $M$. Choose compatible prime-to-$p$ roots in a common algebraic closure to embed the old tame extension into the new one. Hensel’s lemma puts all prime-to-$p$ roots of unity in $M$; the root extension of $X^n-\pi$ is then cyclic of degree $n$ by the uniformizer calculation in Tag [`09EV`](https://stacks.math.columbia.edu/tag/09EV). Every finite quotient of the tame Galois group therefore has order prime to $p$.

For a finite extension $L/K$, embed $L$ into $\overline M$ and write $L=K(\alpha_1,\ldots,\alpha_s)$. Since $K\subset M^{\mathrm{tame}}$ is algebraic over $M$ after compositum, the elements $\alpha_i$ are algebraic over $M$. The field $M'=M(\alpha_1,\ldots,\alpha_s)$ is finite over the complete DVR field $M$, hence again complete discretely valued. Tame base change, Tag [`0EXY`](https://stacks.math.columbia.edu/tag/0EXY)(2), gives $M'M^{\mathrm{tame}}\subset(M')^{\mathrm{tame}}$, which contains $L$. Subfields retain the same presentation by composition of embeddings.

For independent variables $\mathbf t$, give $M(\mathbf t)$ its Gauss valuation and complete it to $N$. Its value group is unchanged and its residue field is $k_M(\mathbf t)$. Base change every finite tame extension along the extension of valuation rings $\mathcal O_M\subset\mathcal O_N$; Tag [`0EXY`](https://stacks.math.columbia.edu/tag/0EXY)(2) applies even though the fraction-field extension is transcendental. Thus $K(\mathbf t)\hookrightarrow N^{\mathrm{tame}}$. A finitely generated extension is finite over a purely transcendental extension, so the finite-extension result finishes the proof.

**Implementation obligations.**

Construct embeddings in a common algebraic closure rather than using informal field inclusions; prove that finite extensions of a complete DVR field retain the required valuation; prove the completion/residue identifications; and make tame base change available for arbitrary extensions of DVRs, not only finite ones. The exit test is closure under subfields, finite extensions, and all finitely generated extensions without an extra perfection or completeness assumption on $K$. The finite-local Tate descent is a later theorem and must not be built into the field predicate.

##### Comparing the actual fibre functors

**Source.**

`lem:actual-fibre-presentation-comparison`.

**Modules.**

`Compat/Foundations.lean`.

Once duplicate global definitions have been eliminated according to the Stacks-first policy, use the Stacks category of finite etale $X$-schemes as the canonical category. For a geometric point $\xi:\operatorname{Spec}\Omega\to X$, identify each fibre with the set of lifts $$\{y:\operatorname{Spec}\Omega\to V:\ v\circ y=\xi\}.$$ Construct the equivalence from the NYLL presentation by its object, morphism, identity, composition, and inverse laws. Prove a natural isomorphism of fibre functors, then conjugate natural automorphisms by that isomorphism. This gives a group equivalence; it becomes a topological group equivalence because stabilizers of finitely many fibre elements generate both topologies. The pullback comparison follows from the universal property of a fibre product.

For finite constant abelian coefficients, pass through the group of isomorphism classes of actual finite-etale torsors. Show that both character constructions read the same fibre permutation. This proves the degree-one comparison needed between NYLL’s small-site $H^1$ and the Stacks big-site presentation. It does not assert an automatic equivalence of their derived categories. Required naturality is both in scheme maps and coefficient maps, especially $\mathbf Z/p^{n+1}\to\mathbf Z/p^n$. A bare abstract group isomorphism is not sufficient. The exit criterion is a commuting diagram for the actual cover, torsor character, and pullback used in the main proof.

##### Compactness produces one conjugating element

**Source.**

`lem:finite-conjugacy-detection`.

**Module.**

`Profinite/Basic.lean`.

Let $P$ be profinite, $D\le P$ closed, and $\alpha,\beta:H\to P$ continuous. If their images in every finite quotient (or a cofinal family) are conjugate by an element in the image of $D$, then they are conjugate by one element of $D$. For each open normal $N$, define $$C_N=\{c\in D:\ \forall h\in H,
                  \ \beta(h)\equiv c\alpha(h)c^{-1}\pmod N\}.$$ It is closed: for each $h$, take the inverse image of equality in the finite Hausdorff quotient, then intersect over $h$. It is nonempty by hypothesis. For finitely many $N_i$, the set $C_{\cap_iN_i}$ lies in their intersection. The closed subgroup $D$ is compact, so the finite intersection property produces $c$ in every $C_N$. Open normal subgroups separate points, yielding the claimed equality for every $h$. Conversely, project a single conjugator to every quotient. The crucial quantifier order is $(\forall N\ \exists c_N)\Rightarrow(\exists c\ \forall h)$. No compatibility of the chosen $c_N$ is assumed or constructed.

##### Finite geometric quotients after extending constants

**Source.**

`lem:finite-geometric-quotient-descent`.

**Module.**

`Profinite/Basic.lean`.

For an exact profinite extension $1\to D\to P\to\Gamma\to1$ and open normal $N\triangleleft D$, choose open normal $B\triangleleft P$ with $B\cap D\subset N$. Such a $B$ exists from the induced topology. Set $P_0=DB$ and $H=NB$. Commutators satisfy $[B,D]\subset B\cap D\subset N$, so $H\triangleleft P_0$, $H\cap D=N$, $HD=P_0$, and $P_0/H\simeq D/N$. The image $\Gamma_0$ of $B$ is open normal in $\Gamma$ and $P_0$ is its full inverse image. Thus one finite Galois extension of constants realizes the entire finite geometric quotient and all its intermediate subgroups. Prove openness of the image by the quotient topology or finite index and compactness; never replace an infinite quotient by a finite one without a proof. The output must include the quotient maps and their commuting square.

##### Relative pro-$p$ groups of geometric $p$-covers

**Source.**

`lem:relative-p-cover-exact`.

**Module.**

`FundamentalGroup/Basic.lean`.

Let $\mathcal D\twoheadrightarrow\Delta=\mathcal D^{(p)}$ have kernel $R$, and let $\mathcal H$ be the inverse image of open $J\le\Delta$. For each open normal $U\triangleleft\mathcal H$ of $p$-power index, intersect the conjugates of $\mathcal H$ and $U$ over representatives of $\mathcal D/\mathcal H$, obtaining $C$ and $V$. These intersections are finite. The quotient $\mathcal D/C$ is a finite $p$-group, because it is the quotient of $\Delta$ by the core of $J$. The injection $$C/V\hookrightarrow\prod_g\mathcal H/U$$ shows that $\mathcal D/V$ is also a finite $p$-group. Hence $R\subset V\subset U$. Intersect all $U$. Conversely $\mathcal H/R=J$ is pro-$p$. Thus $\mathcal H^{(p)}\simeq J$, with the *same* kernel $R$.

Apply the actual open-subgroup cover theorem to the full arithmetic group. An open subgroup $H\le\Pi_X$ determines a connected finite-etale cover $X'\to X$ whose relative constant field $K'/K$ is given by the arithmetic image of $H$. The comparison theorem must identify $\Pi_{X'/K'}$ with $H$ and $\Delta_{X'/K'}$ with $H\cap\Delta_X$, compatibly with the actual cover map. There is no requirement that $[K':K]$ be a power of $p$.

##### Open-image reduction and the arithmetic/geometric index

**Source.**

`lem:open-image-hom-reduction`, `lem:arithmetic-geometric-open-equivalent`.

**Modules.**

`Profinite/Basic.lean`, `Hom/ProperCurves.lean`.

For exact profinite extensions over the same $G$ and a homomorphism $\theta:P_1\to P_2$ over $G$, put $H=\theta(P_1)$. Then $$H\cap D_2=\theta(D_1),\qquad HD_2=P_2,\qquad
 [P_2:H]=[D_2:\theta(D_1)].$$ The first equality uses commutation with $G$; the second uses surjectivity to $G$; the last is a bijection of *coset sets*, not a quotient-group assertion. Both images are compact and closed. A closed subgroup of a profinite group is open exactly when its index is finite. This proves equivalence of arithmetic and geometric openness without normality of $H$.

Given open $\theta:\Pi_X\to\Pi_Y$, realize $H=\theta(\Pi_X)$ by a finite-etale cover $Y_H\to Y$. Its arithmetic projection is surjective, hence it is geometrically connected over $K$. The relative-cover comparison identifies $\Pi_{Y_H}=H$; the Euler-characteristic computation below preserves hyperbolicity. Prove existence for the resulting surjection and compose with the cover. For uniqueness, a second realization lifts to $Y_H$ after a permitted geometric base-point adjustment, by the actual finite-cover lifting criterion. Invoke uniqueness in the surjective case. Prove the analogous full profinite lemma only if it is needed independently; the main endpoint remains the relative pro-$p$ statement.

##### Torsor comparison with constants fixed

**Source.**

`lem:finite-torsor-comparison`.

**Module.**

`FundamentalGroup/Basic.lean`.

Allow quotients $P_Z=\pi_1(Z)/R_Z$ by closed normal subgroups of the geometric kernel, for $Z=X,Y$. For open normal $N\triangleleft P_Y$, write $A=P_Y/N$, $A^{\mathrm{geom}}=\operatorname{im}(D_Y\to A)$ and let $V_N\to Y$ be the corresponding actual Galois torsor. Pulling its finite action back along $\theta q_X$ gives $W_N\to X$. Its quotient by $A^{\mathrm{geom}}$ is the constant cover $X_{E_N}\to X$. The necessary and sufficient condition for one $D_Y$-conjugacy between $q_Yf_*$ and $\theta q_X$ is: for a cofinal family of $N$, there is an $A$-equivariant isomorphism $W_N\simeq X\times_YV_N$ inducing the identity on that constant cover.

On a geometric fibre, a torsor isomorphism supplies a conjugating element of $A$. Acting trivially on the constant quotient is exactly membership in $A^{\mathrm{geom}}$. The finite-conjugacy lemma supplies one element of $D_Y$ for all quotients. Since $\theta q_X$ kills $R_X$, its conjugate $q_Yf_*$ kills $R_X$ as well; this proves factorization through $P_X$. Neither connectedness of $W_N$ nor coherent choices across $N$ are necessary. The adapter must retain NYLL’s opposite-deck-group convention until the explicit inversion converting it to the chosen left action has been proved.

##### Local differential orders and logarithmic Euler characteristic

**Source.**

`lem:curve-local-differential-degree`.

**Module.**

`Curves/Basic.lean`.

For a nonconstant map $f:C'\to C$ of smooth proper geometrically connected curves in characteristic zero, pass to an algebraic closure. The map is finite; over each target DVR its finite torsion-free module is free, hence it is finite flat of degree $d$. At a point write $f^*t=us^e$. The local differential is $$d(f^*t)=s^{e-1}(eu+s\,du/ds)\,ds.$$ The bracket is a unit because the residue characteristic is zero. Thus the ramification divisor has coefficient $e-1$. Take degrees of the nonzero map $f^*\omega_C\to\omega_{C'}$, use $\deg\omega_C=2g(C)-2$ from Tag [`0BS6`](https://stacks.math.columbia.edu/tag/0BS6), and use $\sum_{x\mapsto y}e_x=d$ to obtain $$2g(C')-2=d(2g(C)-2)+\sum_x(e_x-1).$$ For finite reduced boundary $D$ and $D'=(f^{-1}D)_{\mathrm{red}}$, subtract $\sum_{x\in D'}(e_x-1)=d\#D-\#D'$ to get $$2g(C')-2+\#D'\ \ge d(2g(C)-2+\#D),$$ with equality when the map is etale outside the boundary. Formalize the local parameter computation, divisor of a line-bundle map, and fibre-length identity as separate reusable lemmas. All uses of this result must carry the actual compactifications and boundary sets, not just two natural numbers called genus and number of cusps.


### P02 Integral formal groups and Tate extension

#### Proof dossiers: integral formal groups and the Tate extension

This part covers every named result in manuscript Sections 3–4. Its output is an actual integral formal group homomorphism attached to a Galois-equivariant map of Tate modules. Neither the existence of that homomorphism nor full faithfulness of the Tate functor is an input. The proof is organized around finite flat division groups and their graph closures. All module paths below are proposed new modules under the independent `MochizukiHom/` root; they are not assertions that those modules already exist in NYLL or Stacks. Wherever the repositories overlap, use the Stacks definitions, instances, and theorems as canonical. Only non-overlapping NYLL results should be transported onto those objects. The proposed local modules add the missing constructions and proofs; they must not introduce alternative notions of finite $\mathrm{\acute et}$ale algebra, flatness, completion, or scheme morphism.

##### Exact objects, coefficient rings, and the local contract

Fix a prime number $p$, a complete discrete valuation ring $R$ of mixed characteristic $(0,p)$, a chosen uniformizer $\pi$, its fraction field $K$, and its residue field $k$. Write $p=u\pi^e$ with $u\in R^\times$ and $e\geq 1$. Normalize the valuation by $v(p)=1$, so $v(\pi)=1/e$. A smooth commutative formal group of finite height is represented here by an actual $d$-tuple of formal power series defining its group law on $R[[X_1,\ldots,X_d]]$, together with the proved assertion that $$[p]^*:R[[V_1,\ldots,V_d]]\longrightarrow R[[X_1,\ldots,X_d]]$$ is finite free. The coordinate law carries associativity, identity, inverse, and commutativity proofs. The term “finite height” must not hide the integer-extension theorem to be established below.

There are three different rings in the proof: $$R[[X]],\qquad R[[X]][1/p],\qquad K[[X]].$$ The second consists of series with a common bound on their $p$-denominators; the third allows unbounded denominators. Their natural injections must be explicit. In particular, a formal logarithm normally belongs to $K[[X]]$ and need not belong to $R[[X]][1/p]$. A proposed simplification that identifies these two rings invalidates the graph and curve-saturation arguments.

The division group $F[p^n]$ is the finite flat group represented by the actual quotient ring $R[[X]]/J_n$, where $$J_n=([p^n]_1(X),\ldots,[p^n]_d(X)).$$ The transition map in $T_pF=\varprojlim_{[p]}F[p^n](\overline K)$ is multiplication by $p$; the inclusions of finite division groups are separate maps. These conventions are needed to make graph inclusions and finite-level Tate reductions commute literally, or through named coherence lemmas.

**Finite-level Tate identification, source equation (T0).**

Assume the transition maps on geometric division points are surjective. Compatible successive lifts show that $T_pF\to F[p^n](\overline K)$ is surjective. If a compatible sequence $x=(x_m)$ satisfies $x_n=0$, set $y_m=x_{m+n}$. The equality $[p^m]x_{m+n}=x_n=0$ places $y_m$ in $F[p^m](\overline K)$, and the transition identities show that $y$ is compatible and $p^ny=x$. Hence $$T_pF/p^nT_pF\simeq F[p^n](\overline K)$$ as groups with continuous $G_K$-action. Prove naturality for maps of division towers. If finite free $\mathbf Z_p$-module structure is needed later, establish it from the ranks and exact division sequences rather than importing it as a property of an unspecified Tate object. Characteristic-zero finite group schemes are smooth by Stacks Tag [047N](https://stacks.math.columbia.edu/tag/047N); their relative dimension is zero, giving the required finite $\mathrm{\acute et}$ale property. Galois descent via Tag [03QR](https://stacks.math.columbia.edu/tag/03QR) then turns each equivariant map on finite division points into a unique map of finite $\mathrm{\acute et}$ale group schemes.

**Division ideals detect equality.**

From $[p](X)=pX+O(X^2)$ prove inductively $$J_n\subseteq(\pi,X)^{n+1}.$$ For the induction, multiplying the linear term by $p$ increases the maximal-ideal order by at least one, and a quadratic term in an element of order $n+1$ has order at least $n+2$. Completeness and separatedness imply $\bigcap_nJ_n=0$. Thus two integral series that agree on every division group agree. Equality on the generic fibres suffices because every division algebra is $R$-flat.

**Suggested modules and gate.**

Place coordinate and valuation conventions, finite-level Tate comparison and ideal separation together in `FormalGroups/Basic.lean`. The gate is a commutative comparison between the actual torsion quotient rings, their geometric points, and the quotients of the actual inverse limit. An abstract tower unrelated to these quotient rings does not pass this gate.

##### Division rings from an existing semiabelian group

**Source and module.**

Source identifier: `lem:algebraic-group-formal-division`. Proposed module: `FormalGroups/Basic.lean`.

**Precise result.**

Let $\mathcal G/R$ be a smooth separated commutative algebraic space group of finite type with semiabelian geometric fibres, and suppose its identity completion has coordinates $A=R[[X_1,\ldots,X_d]]$. Then $[p^n]:\mathcal G\to\mathcal G$ is flat, quasi-finite, finitely presented, and surjective; its map on identity completions is finite free. The scheme $$C_n=\operatorname{Spec}A/([p^n](X))$$ is an open and closed finite flat subgroup of $\mathcal G[p^n]$ and its special geometric fibre is the entire connected component of the identity. There is an integer $h\geq0$ with $$\operatorname{rank}_R C_n=p^{nh},\qquad
 0\longrightarrow C_n\longrightarrow C_{n+m}
 \xrightarrow{[p^n]} C_m\longrightarrow0,
 \qquad \omega_{C_n}=\omega_P/p^n\omega_P.$$ The exact sequence is exact for the fppf topology, not merely on geometric points.

**Proof to formalize.**

For a torus over a field, the power map is finite faithfully flat by the Laurent-polynomial presentation. For an abelian variety use Stacks Tag [0BFG](https://stacks.math.columbia.edu/tag/0BFG). In an extension $0\to T\to S\to B\to0$, division on $B$, followed by lifting and division on $T$, proves fppf surjectivity. The map $S[p^n]\to B[p^n]$ is a $T[p^n]$-torsor, so both the kernel and the multiplication map on $S$ are finite flat. This proves the fibrewise assertion. Apply the coherent flatness criterion, Tag [0APR](https://stacks.math.columbia.edu/tag/0APR), to the nonzero structure sheaf and the smooth $R$-flat source and target. Finite type over the Noetherian DVR supplies local Noetherian hypotheses. Fibrewise quasi-finiteness and surjectivity complete the global assertion; global finiteness of $[p^n]$ on $\mathcal G$ is not claimed.

Let $B=R[[V_1,\ldots,V_d]]$ be the identity-completion ring on the target and form $$Z_n=\mathcal G\times_{\mathcal G,[p^n]}\operatorname{Spec}B.$$ The separated quasi-finite algebraic space $Z_n/B$ is a scheme by Tag [0418](https://stacks.math.columbia.edu/tag/0418). At the special identity point $z$, the Henselian local-factor result, Tag [04GH](https://stacks.math.columbia.edu/tag/04GH), makes $D_n=\mathcal O_{Z_n,z}$ finite over $B$. Flatness and localness make it finite free. A finite local algebra over a complete Noetherian local ring is complete, and its completed presentation is $$D_n=R[[V,X]]/(V-[p^n](X))\simeq R[[X]].$$ This proves finite freeness of the desired formal multiplication map. The finite local factor is open by the Henselian decomposition and closed because it is finite over $B$ and $Z_n/B$ is separated. Base-changing along $V=0$ gives the claimed $C_n$ inside $\mathcal G[p^n]$.

The special-fibre coordinate ring $k[[X]]/(\overline{[p^n]}(X))$ is local Artinian with residue field $k$; after a geometric base change its maximal ideal remains nilpotent and its residue field becomes the base field. Thus this fibre is geometrically connected. The multiplication and inverse maps preserve its identity special point. The inverse image of the complementary open and closed subset in each finite $R$-scheme has empty special fibre and is empty by Nakayama; this makes $C_n$ a subgroup. Its special connected component is the chosen local factor.

The map $C_{n+m}\to C_m$ is obtained by base change from the finite free formal map $[p^n]$, and its kernel is $C_n$. If the rank of $[p]$ is $r$, composition gives rank $r^n$. Differentiating $[p^n](X)$ gives $p^n$ times the identity on invariant cotangents. The characteristic-zero generic fibre of $C_1$ is finite $\mathrm{\acute et}$ale and is killed by $p$, so its order is $p^h$ for some $h$, whence $r=p^h$.

**Implementation obligations and exit test.**

The map from $\operatorname{Spec}B$ to the algebraic space, the finite Henselian local factor, and the identification of its completed ring must all be actual constructions. If an $\mathrm{\acute et}$ale chart is chosen after a finite unramified extension, include the uniqueness and faithfully flat descent argument for the identity factor. The exit test is the fppf exact sequence of the actual $C_n$, the cotangent formula, and the identification of $C_n$ with the same division algebras later used in Tate extension. Rebuilding a second, unconnected division tower is not acceptable.

##### The logarithm on a uniformly small ball

**Source and module.**

Source identifier: `lem:small-ball-formal-logarithm-direct`. Proposed module: `FormalGroups/Basic.lean`.

**Precise result.**

Let $S$ be $p$-adically complete and separated, with multiplication by $p$ injective, and let $F/S$ be a commutative $d$-dimensional formal group. Evaluating convergent series equips $B_F=(p^2S)^d$ with the group law of $F$. There is a continuous group isomorphism $$\ell_F:B_F\xrightarrow{\sim}(p^2S)^d,
 \qquad \ell_F(x)=\lim_{n\to\infty}p^{-n}[p^n]_F(x),$$ whose formation is functorial: $\ell_H(f(x))=df\,\ell_F(x)$ for an integral formal homomorphism $f:F\to H$.

**Proof to formalize.**

Write $[p]_F(X)=pX+Q(X)$ with $Q$ of order at least two. For $x_n=[p^n]_F(x)$, induction gives $$x_n\in(p^{n+2}S)^d,
 \qquad p^{-(n+1)}Q(x_n)\in(p^{n+3}S)^d.$$ Division denotes the unique quotient in $S$ of an element already known to be divisible; it is not inversion of $p$ in $S$. Consecutive terms of the displayed sequence differ by the second expression, which gives uniform convergence. If $x-y\in(p^rS)^d$, $r\geq2$, the difference of each quadratic-or-higher monomial yields $$x_n-y_n\in(p^{n+r}S)^d,\qquad
 p^{-(n+1)}(Q(x_n)-Q(y_n))\in(p^{n+r+1}S)^d.$$ Consequently $e_F=\ell_F-\operatorname{id}$ sends the small ball to $p^3S$ and improves the precision of differences by one power of $p$. For $z\in(p^2S)^d$, the recurrence $x_0=z$, $x_{j+1}=z-e_F(x_j)$ is Cauchy, and its limit is the unique solution of $\ell_F(x)=z$. The same precision estimates give continuity of the inverse.

Apply $[p^n]$ to the formal addition law. After dividing by $p^n$, all nonlinear terms tend to zero since they lie in $p^{n+4}S$. Taking limits proves additivity of $\ell_F$. For $f(X)=df\,X+Q_f(X)$, the same argument applied to $f([p^n]_F(x))=[p^n]_H(f(x))$ proves functoriality. This proof works at $p=2$ with the same $p^2$ ball.

To obtain the characteristic-zero formal series, apply the construction with $S=R[[X]]$ and the input $p^2X$, and rescale the variables in $K[[X]]$. The linear term is $X$. Identities may be tested after substituting $p^2X,p^2Y$ because multiplication by powers of $p$ is injective on coefficients. Formal recursive inversion gives $\exp_F$. Prove that these series evaluate to the constructed inverse maps on the small ball.

**Exit test.**

The proof exports both a formal-series identity and a convergent evaluation identity, linked by a theorem. A bare equivalence of abstract groups on a small ball is insufficient for later coefficientwise logarithms; a bare formal logarithm is insufficient for later integral norm bounds.

##### Finite flat closures and quotient formal groups

**First source result and module.**

Source identifier: `lem:finite-flat-subgroup-closure-quotient`. Proposed module: `FormalGroups/Quotients.lean`.

**Precise result and proof.**

If $F/R$ is a finite flat commutative group and $H_K\subset F_K$ a closed subgroup, its schematic closure $H\subset F$ is finite flat. Indeed, define $\mathcal O(H)$ as the image of $\mathcal O(F)\to\mathcal O(H_K)$. This is a finite torsion-free module over the DVR and hence free. The Hopf maps descend to this image. For the comultiplication, verify the target tensor product is $R$-flat, so the required identity is detected after passing to $K$.

The action relation $H\times_RF\rightrightarrows F$ is an affine equivalence relation with finite locally free projections. Stacks Tag [03BM](https://stacks.math.columbia.edu/tag/03BM) represents its fppf quotient by the spectrum of invariants and makes $F\to F/H$ finite faithfully flat. The invariant ring is a finite torsion-free $R$-module, so $F/H$ is finite flat. Flat base change of the quotient recovers $F_K/H_K$. If $H\subset G\subset F$ are finite flat closed subgroups, $G/H\to F/H$ is a finite monomorphism of fppf sheaves and hence a closed immersion by Tag [03BB](https://stacks.math.columbia.edu/tag/03BB).

The exit test includes base-change comparison and the compatibility of the quotient with inclusions, since graph closures at adjacent torsion levels use both facts.

**Second source result and module.**

Source identifier: `lem:finite-formal-group-quotient`. Proposed module: `FormalGroups/Quotients.lean`.

**Precise result.**

For a smooth commutative finite-height formal group $P/R$ and a finite flat closed subgroup $H$, there is a finite faithfully flat quotient $q:P\to P/H$, and the target again has power-series coordinates and finite free $[p]$. The analogous assertion over the residue field is also required.

**Proof to formalize.**

Put $A=R[[X]]$. Coordinates of $H$ are nilpotent modulo $\pi$, so substituting the translation law into the finite $A$-module $A\otimes_R\mathcal O(H)$ is legitimate by $(\pi,X)$-adic completeness. This produces an ordinary affine scheme action on $\operatorname{Spec}A$. Prove freeness by applying the formal difference map: the coordinates of the acting element lie in the ideal generated by $F_j(h,X)-X_j$, so an element fixing a point is the identity. Only after these constructions may Tag 03BM be applied. It gives $B=A^H\subset A$ and makes $A$ finite faithfully flat over $B$.

The ring $B$ is local with residue field $k$. Noetherianness descends by extending ascending chains of ideals to $A$ and contracting using faithful flatness. Since $A/B$ is finite free over the local ring $B$ and $1\notin\mathfrak m_BA$, choose a basis of $A$ containing $1$; this makes $B$ a direct summand. The equality $\sqrt{\mathfrak m_BA}=\mathfrak m_A$ identifies the two adic topologies, and the direct-summand argument proves completeness of $B$. It similarly proves $\pi$-adic completeness and separatedness. The inclusion $B\subset A$ implies $R$-flatness.

After reduction modulo $\pi$, the map $B/\pi B\to A/\pi A$ remains faithfully flat. Regularity descends by Stacks Tag [07NG](https://stacks.math.columbia.edu/tag/07NG). Let $C=B/\pi B$, let $\mathfrak n$ be its maximal ideal, and choose lifts $z_1,\ldots,z_d$ of a basis of $\mathfrak n/\mathfrak n^2$. Nakayama and successive approximation produce a surjection $k[[Z_1,\ldots,Z_d]]\to C$. The target is a regular local domain; a nonzero prime kernel would shorten maximal chains and force dimension less than $d$. Thus the map is an isomorphism. Choose lifts of the $Z_i$ in the augmentation ideal of $B$. The resulting map $R[[Z]]\to B$ is an isomorphism modulo $\pi$; flatness and $\pi$-adic completeness give an isomorphism over $R$. This establishes actual coordinates. The field case is the same regular-local argument without the $\pi$-lifting step.

The group law is descended using completed tensor products and the finite faithfully flat map from the completed tensor product of $A$ with itself. It is not legitimate to assume that the original formal group law already defines an ordinary group scheme structure on $\operatorname{Spec}A$. Once the quotient group law is present, $[p]^*B\subset B$ is injective. The ring $A$ is finite over $[p]^*A$, and $[p]^*A$ is finite over $[p]^*B$. Noetherianness makes the intermediate $B$ finite over $[p]^*B$. The identity $q[p]_P=[p]_{P/H}q$ and faithful flatness of $q$ descend flatness of $[p]$ by Tag [039V](https://stacks.math.columbia.edu/tag/039V). A finite flat module over a local ring is free. Comparing ranks in the identity shows that $[p]$ has the same degree on $P$ and $P/H$.

**Critical obligation and gate.**

The ordinary affine action, its freeness, completion of tensor products, and descent of the formal group law are proof obligations, not fields of an assumed “quotient model” structure. The gate exports the target coordinates, the quotient universal property, finite faithful flatness, and finite freeness of the target $[p]$ map. The special-kernel proof below consumes all four.

##### Bounded logarithms and integral curve saturation

**Bounded logarithm result.**

Source identifier: `lem:formal-bounded-logarithm-reduction`. Proposed module: `FormalGroups/Quotients.lean`. For an integral one-variable curve $\gamma\in F(tR[[t]])$, $$\log_F\gamma\in R[[t]][1/p]^d
 \quad\Longleftrightarrow\quad \gamma\equiv0\pmod\pi.$$ When these equivalent conditions hold, $$\log_F\gamma\in p^{2-2e}R[[t]]^d.$$

For the forward implication choose $m$ large enough to put $p^m\log_F\gamma$ in $p^2tR[[t]]^d$. The small-ball inverse and uniqueness of formal inverse imply that $[p^m]\gamma$ has coordinates in $p^2tR[[t]]$. Thus the reduction of $\gamma$ is a curve into the finite local group $F_k[p^m]$. Every augmented coordinate of this group is nilpotent, whereas $k[[t]]$ is reduced, so this curve is the identity. For the converse start with all coefficients in $\pi R$ and let $b_n$ be a lower bound for their normalized valuations after applying $[p^n]$. The multiplication series gives $$b_0\geq1/e,\qquad
 b_{n+1}\geq\min(b_n+1,2b_n)\geq b_n+1/e.$$ After $2e$ iterations the curve is in the $p^2$ ball. Apply its logarithm and divide by $p^{2e}$ to obtain exactly $p^{2-2e}$. One can implement the estimate using ideal memberships and integer exponents, avoiding an infimum of valuations when an actual minimum is inconvenient.

**Curve-saturation result.**

Source identifier: `lem:finite-formal-embedding-curve-saturation`. Proposed module: `FormalGroups/Quotients.lean`. Suppose $j:Q\to J$ is finite and its map after inverting $p$ is an isomorphism onto its closed image. Set $A=dj$ and $U=\operatorname{im}(A\otimes_RK)$. If an integral curve $\gamma$ in $J$ has logarithm in $U[[t]]$, there is a unique integral curve $\eta$ in $Q$ with $j\eta=\gamma$.

The generic closed immersion implies injectivity of $A$ over $K$. Define $$\eta=\exp_Q(A^{-1}\log_J\gamma)\in Q(tK[[t]]).$$ Let $B$ be the image of the target coordinate ring in $A_Q=R[[Y]]$. The logarithmic identity shows that $\gamma$ kills the relations defining $B$. Since $B[1/p]=A_Q[1/p]$, its map to $R[[t]]$ extends to a map $A_Q\to R[[t]][1/p]$ whose image in $K[[t]]$ is the displayed $\eta$. Finiteness of $A_Q$ over $B$ makes each image coordinate integral over $R[[t]]$. For such a coordinate $z$, choose a smallest $r\geq0$ with $f=\pi^rz\in R[[t]]$. If $r>0$, multiply a monic degree-$m$ equation for $z$ by $\pi^{rm}$ and reduce modulo $\pi$. All lower terms vanish and $\bar f^{,m}=0$. Reducedness of $k[[t]]$ implies $f\in\pi R[[t]]$, contradicting minimality. Thus every coordinate is integral. The constant terms vanish and uniqueness follows already over $K[[t]]$.

**Gate.**

Prove the common-denominator lemma separately for any ring whose reduction modulo a non-zero-divisor is reduced. Reuse it later with $R[[X]]$. Do not infer integral coordinates merely from membership in $K[[t]]$, and do not replace the finite generic image by a tangent-space condition alone.

##### The bounded-projection theorem for actual curves

**Source and modules.**

Source identifier: `lem:formal-bounded-projection`. Proposed module: `FormalGroups/TateExtension.lean`.

**Statement and definitions.**

Define an additive group of coefficient sequences by $$D_F=\left\{(c_i)_{i\geq0}:\exp_F\left(\sum_{i\geq0}c_it^{p^i}\right)
                 \in F(tR[[t]])\right\}.$$ Use $\Delta$ only as a bookkeeping variable, writing $y=\sum c_i\Delta^i$. Define $B_F=D_F\cap R[[\Delta]][1/p]^d$. For every integral $r\times d$ matrix $A$ and $y\in D_F$, if $Ay$ has bounded coefficients, then $$Ay\in p^{2-2e}R[[\Delta]]^r.$$ The matrix need not be injective. This missing injectivity is essential: the eventual application is a projection onto a quotient of a tangent space.

**Step 1: integral curve operators.**

Define $V_n\gamma(t)=\gamma(t^n)$. For $p\nmid n$, define $F_n\gamma$ by the formal-group sum over the roots of $z^n=t$. Its coordinatewise symmetric expressions are polynomials in elementary symmetric functions; substituting $e_1=\cdots=e_{n-1}=0$ and $e_n=(-1)^{n+1}t$ proves integrality without selecting roots in $R$. Prove compatibility with coefficient-ring maps. Since $[n]$ has integral formal inverse, define the convergent sum in the curve group $$\epsilon_p=\sum_{\substack{n\geq1\\p\nmid n}}
                \frac{\mu(n)}n V_nF_n.$$ Its $n$th summand has order at least $n$, so every coefficient receives finitely many contributions. Over $K$, applying the logarithm and the elementary divisor sum for the Möbius function shows that it keeps exactly the monomials of degree $p^i$. This proves idempotence and identifies $D_F$ with the logarithms of its integral image. For $V=V_p$ one has $V(\sum c_i\Delta^i)=\sum c_i\Delta^{i+1}$. Substitution $t\mapsto\lambda t$, $\lambda\in R$, gives $$\rho_\lambda\left(\sum c_i\Delta^i\right)
    =\sum\lambda^{p^i}c_i\Delta^i.$$ It preserves $D_F$, commutes with $A$, and cannot increase the coefficient Gauss norm of $Ay$. These are operations on actual curves; no realization theorem for abstract Cartier modules is used.

**Step 2: special curves over a perfect residue field.**

Temporarily assume $k$ perfect. Lifting curve coefficients and applying $\epsilon_p$ gives a surjection $$D_F\longrightarrow E=\epsilon_pF_k(tk[[t]])$$ whose kernel is $B_F$. The bounded-logarithm result gives $B_F\subseteq p^{2-2e}R[[\Delta]]^d$. Taking first coefficients yields $E/VE\simeq k^d$. For the kernel statement, lift a special curve whose first coefficient is zero; its logarithm has first coefficient $c_0\in\pi R^d$. Subtract the $\epsilon_p$-image of the integral curve with coordinates $c_0t$. This changes neither the reduction nor the desired divisibility, and it kills the first logarithmic coefficient. The remaining logarithm, and hence the curve, is a series in $t^p$, so it is divisible by $V$. The operator $V$ is injective, and $V^mE$ consists of curves of order at least $p^m$.

Choose $H\geq1$ such that the $p^H$th power of every element of the augmentation ideal of the finite local group $F_k[p]$ vanishes. The $H$th relative Frobenius kills this kernel, so finite flat quotient descent factors it as $\Phi^H=\psi[p]$. Perfection permits the inverse Frobenius twist. Taking $p^H$th roots of the coefficients of a curve in that twist gives $$V^H\gamma=[p]\bigl(\psi^{(-H)}\delta\bigr).$$ Apply $\epsilon_p$, using its commutation with $V$ and $[p]$, to conclude $V^HE\subseteq pE$.

**Step 3: a finite-dimensional estimate.**

Put $M_0=p^{2e-2}$, with absolute value normalized by $|p|=p^{-1}$, and define $$N=\{\bar z\in E:Az\text{ has bounded coefficients}\}.$$ Changing the lift changes $Az$ by an element of norm at most $M_0$, so this definition is independent of the lift. The group $N$ is $p$-saturated, stable under $V$, and $V$-saturated: multiplying by $p$ does not affect boundedness, while shifting coefficients by $V$ preserves their Gauss norm. Thus $N\cap VE=VN$. The substitutions $\rho_\lambda$ show that the image of $N/VN$ in $E/VE=k^d$ is a $k$-linear subspace. The substitutions need not define an additive scalar action on all of $E$; only their action on first coefficients is used.

If $N/VN=0$, repeatedly write $N=VN$ to obtain $N\subseteq V^mE$ for every $m$, forcing $N=0$ by curve orders. Otherwise choose lifts $\bar z_1,\ldots,\bar z_m$ of a basis and then lifts $z_i\in D_F$. Set $M=\max_i\|Az_i\|$. Given $w\in N$, eliminate its first coefficient recursively: $$w_j=\sum_i\rho_{a_{ji}}\bar z_i+Vw_{j+1},\qquad w_j\in N.$$ Choose integral lifts $\lambda_{ji}$ of $a_{ji}$. The convergent sum $$z_w=\sum_{j\geq0}\sum_iV^j\rho_{\lambda_{ji}}z_i$$ is an actual integral curve with logarithm in $D_F$, reduces to $w$, and satisfies $\|Az_w\|\leq M$. Convergence is coefficientwise because the $j$th group of terms starts in degree $p^j$. The residual reduction after truncating at $j$ is in $V^jE$, proving the claimed reduction without any compactness assumption on $k$.

Because $V^HE\subseteq pE$ and $N$ is $p$-saturated, $V^HN\subseteq pN$. Use the just-constructed representatives to write $$V^Hz_i=py_i+b_i,\qquad\|Ay_i\|\leq M,\quad b_i\in B_F.$$ Taking norms and the maximum gives $$M\leq\max\{|p|M,M_0\}.$$ Since $|p|<1$, this forces $M\leq M_0$. Every original $y$ differs from $z_{\bar y}$ by an element of $B_F$, giving the desired bound. The Frobenius integer $H$ disappears from the final bound; that is why it is independent of height and dimension.

**Step 4: remove perfection of the residue field.**

Inside an algebraic closure of $K$, order the DVRs containing $R$ and retaining $\pi$ as uniformizer by inclusion. A chain union still has the property that every nonzero element is a unit times an integral power of $\pi$; units remain units and $\pi$ remains a nonunit. Zorn gives a maximal such DVR $R_\infty$. If its residue field is imperfect, lift an element $\bar a$ that is not a $p$th power to a unit $a$ and form $$S=R_\infty[T]/(T^p-a).$$ This is finite free; modulo $\pi$ it is a degree-$p$ field extension. Integrality implies all maximal ideals lie over $(\pi)$, so it is local with maximal ideal $(\pi)$. Finite freeness gives injectivity of $\pi$ and $\pi$-adic separatedness. Every nonzero element is a unit times a power of $\pi$, so $S$ is a DVR. Its finite fraction-field extension embeds in the chosen algebraic closure, contradicting maximality. Therefore the residue field of $R_\infty$ is perfect.

Complete $R_\infty$ for its $\pi$-adic topology to obtain $R'$. The map $R\to R'$ is faithfully flat and preserves $\pi$, $e$, and the valuation of each original coefficient. Base change preserves the finite free multiplication map and the integral curve. Apply the bound over $R'$ and descend coefficientwise using equality of valuations. This is a proved reduction, not a new hypothesis that $k$ is perfect.

**Exit test.**

The theorem must accept every integral matrix $A$, including matrices with kernel. Its output must retain the explicit uniform exponent $2-2e$. Check each norm statement only for bounded sequences, or use a valuation-bound predicate to avoid an undefined finite Gauss norm. The general-residue theorem must invoke the constructed $R'$ and valuation comparison, not an unproved perfection typeclass.

##### Uniform annihilation of the special kernel

**Source and module.**

Source identifier: `lem:finite-generic-embedding-special-kernel`. Proposed module: `FormalGroups/TateExtension.lean`.

**Statement.**

If $j:Q\to J$ is a finite homomorphism between smooth commutative finite-height formal groups over $R$, and its coordinate map after inverting $p$ is a closed immersion, then $$[p^{2e}]\ker(j_k)=0.$$ This is an equality of maps on the whole finite special group scheme, including its nilpotent structure. A statement only about geometric points would be vacuous for a finite connected group and would not support the graph argument.

**Proof to formalize.**

Let $A=dj$ and $U=\operatorname{im}(A\otimes_RK)$. The lattice $U\cap R^{\dim J}$ is saturated. Over the DVR it is a direct summand, so choose an integral split projection $\operatorname{pr}:R^{\dim J}\to R^r$ with that kernel and an integral right inverse $B$. The special kernel $S=\ker(j_k)$ is finite local. The formal quotient result supplies a smooth formal group $H=Q_k/S$ and a finite faithfully flat $q:Q_k\to H$. Factor $j_k=iq$. The ring $\mathcal O(H)$ is finite over $\mathcal O(J_k)$. Since $i$ has trivial scheme-theoretic kernel, its fibre over the identity is $\operatorname{Spec}k$; Nakayama then makes $i^*$ surjective. Thus $i$ is a closed immersion.

The augmentation ideal of $S$ is nilpotent and $[p]^*$ sends it into its square, so some $p^a$ kills $S$. The quotient property gives $r_0:H\to Q_k$ with $r_0q=[p^a]$ and $qr_0=[p^a]$. Choose coordinates on $H$ and the $d$ coordinate curves $c_i(t)=e_it$; set $\delta_i=\epsilon_pc_i$. Their first coefficients are the standard basis. Lift $i\delta_i$ to $z_i\in D_J$ and $r_0\delta_i$ to $y_i\in D_Q$. The relation $j_kr_0=i[p^a]$ shows $$p^az_i-Ay_i\in B_J.$$ Therefore $\operatorname{pr}(z_i)$ has bounded coefficients. With $s=2e$, the bounded-projection theorem gives $p^s\operatorname{pr}(z_i)\in p^2R[[\Delta]]^r$. Put $w_i=Bp^s\operatorname{pr}(z_i)$. The small-ball logarithm realizes $w_i$ as the logarithm of an integral curve reducing to zero, so $w_i\in B_J$. Then $$v_i=p^sz_i-w_i\in D_J\cap U[[\Delta]].$$ Curve saturation lifts its exponential through $j$ to an integral curve in $Q$. Reducing gives $\eta_i\in Q_k(tk[[t]])$ with $q\eta_i=[p^s]_H\delta_i$, using the monomorphism $i$.

Define the formal maps $$\kappa(Z)=\delta_1(Z_1)+_H\cdots+_H\delta_d(Z_d),\qquad
 \beta(Z)=\eta_1(Z_1)+_{Q_k}\cdots+_{Q_k}\eta_d(Z_d).$$ The linear coefficient of $\kappa$ is the identity, so it has a formal composition inverse. The pointed formal map $h=\beta\kappa^{-1}$ satisfies $qh=[p^s]_H$. The difference $hq-[p^s]_{Q_k}$ factors through $S$. A pointed map from the reduced ring $k[[Y]]$ to the finite local group with nilpotent augmentation ideal is zero. Hence $hq=[p^s]_{Q_k}$; restriction to $S$ proves $[p^s]S=0$.

**Gate.**

There is no need to prove that $h$ is a group homomorphism. Its pointed-map identity is sufficient. The output exponent is $2e$, independent of $a$, the quotient degree, height, and dimension. The perfect-residue reduction belongs to the preceding bounded-projection theorem; it must not reappear as a hypothesis here.

##### Complete local descending cosets

**Source and module.**

Source identifier: `lem:complete-local-descending-cosets`. Proposed module: `FormalGroups/Quotients.lean`.

**Statement.**

For a complete Noetherian local ring $(A,\mathfrak m)$ and a descending chain of ideals $I_n$, with $I=\bigcap_nI_n$, the canonical map $$A/I\xrightarrow{\sim}\varprojlim_nA/I_n$$ is an isomorphism. For every $r$, some $I_n$ is contained in $I+\mathfrak m^r$. No finite residue-field hypothesis is allowed.

**Proof to formalize.**

A compatible system of classes is a descending system of nonempty cosets $C_n=a_n+I_n$. The module $A/\mathfrak m^r$ has finite length. Images of the cosets therefore stabilize to a nonempty coset $D_r$. For a fixed $d\in D_r$, the images in $A/\mathfrak m^{r+1}$ lying over $d$ are again a descending family of nonempty cosets and stabilize; hence $D_{r+1}\to D_r$ is surjective. Choose compatible $d_r$ and use completeness to obtain $a\in A$. Each $I_n$ is $\mathfrak m$-adically closed, so $a\in C_n$ for every $n$. This proves surjectivity; injectivity is the definition of $I$.

For cofinality, pass to the complete Noetherian quotient $A/I$. If the stable image of $I_n$ in $A/\mathfrak m^r$ contained a nonzero $d$, the preceding coset argument would produce an element of every $I_n$ with residue $d$, contradicting zero intersection. The stable image is therefore zero. Derived consequences needed below are $$\bigcap_n(I_n+J)=I+J$$ for every ideal $J$, and the analogous equality for the sum of two copies of $I_n$ in a completed two-variable ring. Prove these using cofinality and separatedness of the relevant quotient, as supplied by Krull intersection, Stacks Tag [00IP](https://stacks.math.columbia.edu/tag/00IP).

**Gate.**

The proof uses finite length, not finiteness of the underlying residue sets and not local compactness. Export the sum/intersection identity explicitly because reduction modulo $(\pi,X)$ of an infinite intersection is not automatic.

##### A finite closed graph has an isomorphic first projection

**Source and module.**

Source identifier: `lem:closed-graph-finite-flat-projection`. Proposed module: `FormalGroups/TateExtension.lean`.

**Precise result.**

Let $E_n\subset(P\times Q)[p^n]$ be increasing finite flat closed subgroups whose generic first projections identify $E_{n,K}$ with $P[p^n]_K$. Suppose one integer $s$ kills all special first-projection kernels. If $I_n\subset R[[X,Y]]$ is their descending chain of defining ideals, then $$C=R[[X,Y]]/\bigcap_nI_n$$ defines an $R$-flat closed formal subgroup $\Gamma_0$ and its first projection $a:\Gamma_0\to P$ is an isomorphism.

**Step 1: use the uniform kernel bound to establish finiteness.**

The descending-coset lemma gives $C=\varprojlim_n\mathcal O(E_n)$. It is torsion-free over $R$, hence flat. The two-variable intersection identity descends the group law; similarly for inverse and identity. Applying the intersection-plus-ideal equality with $J=(\pi,X)$ shows that $\ker(a_k)$ is a closed subgroup of $Q_k[p^s]$. Thus $C/(\pi,X)C$ is finite-dimensional over $k$. Put $A=R[[X]]$. Lifts of a basis of this finite-dimensional space generate $C$ over $A$: the radical equality for $\mathfrak m_AC$ identifies the adic topologies, and successive approximation with completeness gives finite generation. Hence $a$ is finite.

A series in the kernel of $A\to C$ vanishes on every $E_{n,K}$ and therefore every $P[p^n]_K$. Flatness of the division algebras descends vanishing to $P[p^n]$, and the division-ideal separation proves it is zero. Hence identify $A\subset C$. Set $A_K=A[1/p]$ and $C_K=C[1/p]$; these are still the bounded-denominator rings.

**Step 2: obtain a single finite generic kernel.**

On generic fibres, multiplication by $p$ carries $E_{n+1,K}$ onto $E_{n,K}$. Flatness descends containment to the integral groups. If $[p]^*f=0$ in $C$, generic surjectivity forces $f$ to vanish on every $E_{n,K}$; flatness and the inverse-limit identity then force $f=0$. Thus every $[p^r]^*$ is injective on both $C$ and $C_K$.

Let $N=\ker a$. It is finite over $R$ and is a closed subgroup of $Q$; flatness of $N$ is neither known nor needed. If $m$ is prime to $p$, multiplication by $m$ on $Q$ has integral formal inverse, so $N[m]=0$. The generic finite group scheme $N_K$ is $\mathrm{\acute et}$ale in characteristic zero, so its finite geometric point group has $p$-power order and is killed by $p^c$ for some $c\geq1$. Set $h=[p^c]_P\circ a$ and $D=\ker h$. The inverse of $a:E_{c,K}\to P[p^c]_K$ is a group section of $D_K\to P[p^c]_K$. Thus $$D_K\simeq N_K\times E_{c,K},\qquad [p^c]D_K=0.$$

**Step 3: compute one generic invariant ring.**

Write $H=\mathcal O(D)$. Both $C\otimes_{A,h^*}C$ and $C\otimes_RH$ are finite $C$-modules and therefore complete. Their formal coordinates are nilpotent at the closed point, so difference and addition can be evaluated, giving the ordinary-ring isomorphism $$C\otimes_{A,h^*}C\simeq C\otimes_RH.$$ After inverting $p$, this identifies the action relation of $D_K$ on $\operatorname{Spec}C_K$ with its fibre-product relation over $\operatorname{Spec}A_K$. The action is free. Tag 03BM supplies the finite faithfully flat quotient by $D_K$ with coordinate ring $B_K=C_K^{D_K}$.

There are inclusions $h^*A_K\subset B_K\subset C_K$, and the middle ring is finite over the first because the latter is Noetherian. The quotient relation and the fibre-product relation coincide, so faithful flat descent makes $\operatorname{Spec}B_K\to\operatorname{Spec}A_K$ a monomorphism. It is finite and hence a closed immersion by Tag 03BB. Since its coordinate map is also injective, $B_K=h^*A_K$.

The map $[p^c]_{\Gamma_0}$ is invariant under $D_K$-translation. Consequently $$[p^c]^*C_K\subseteq C_K^{D_K}
   =h^*A_K=[p^c]^*a^*A_K.$$ Cancel the injective $[p^c]^*$ to conclude $C_K=a^*A_K$.

**Step 4: return to the integral ring.**

Flatness embeds $C$ in $C_K=A_K$. It is finite over $A$, so all its elements are integral over $A$. The minimum-denominator proof used for curve saturation applies because $A/\pi A=k[[X]]$ is reduced. It shows $C\subset A$, and therefore $C=A$.

**Gate and proof audit.**

Finiteness of $a$ must precede the ordinary affine invariant-ring argument. No argument may assume the unknown kernel $N$ or $D$ flat over $R$. Only their characteristic-zero generic fibres are used in the finite flat quotient at Step 3. The simultaneous-congruence lemma must justify reduction of the infinite intersection. These are proof-critical checks; the source supplies a route for each, but they have not been kernel-checked as Lean declarations in this plan.

##### Integral extension of a Tate-module map

**Source and module.**

Source identifier: `thm:formal-tate-extension-elementary`. Proposed module: `FormalGroups/TateExtension.lean`.

**Final local statement.**

For smooth commutative finite-height formal groups $P,Q/R$, every $G_K$-equivariant $\mathbf Z_p$-linear map $u:T_pP\to T_pQ$ is induced by a unique integral formal group homomorphism $f:P\to Q$. There is no perfection, finiteness, or finite-generation hypothesis on the residue field.

**Construction and proof.**

Use the finite-level Tate comparison to form $u_n$ as a map of actual finite $\mathrm{\acute et}$ale generic division groups. Take its graph and then its schematic closure $$E_n\subset(P\times Q)[p^n].$$ The finite-flat closure theorem proves $E_n$ finite flat. The compatibility of the $u_n$ makes their generic graphs nested; integral flatness descends the containment, so $E_n\subset E_{n+1}$. Form the smooth finite-height formal quotient $\mathcal J_n=(P\times Q)/E_n$ and the map $j_n:Q\to\mathcal J_n$ from the second axis. It is finite: the second axis is a closed immersion and the quotient map is finite. Pulling back the quotient relation gives $$Q\times_{\mathcal J_n}Q
   \simeq \ker(E_n\to P[p^n])\times Q.$$ After inverting $p$, the kernel vanishes because $E_{n,K}$ is a graph. Thus $j_n[1/p]$ is a finite monomorphism and is a closed immersion. The special-kernel theorem applies to $j_n$ and supplies the same exponent $s=2e$ for every $n$.

Apply the closed-graph theorem to get an isomorphism $a:\Gamma_0\to P$. Let $b:\Gamma_0\to Q$ be the second projection and define $f=ba^{-1}$. Restriction to each generic graph gives the original $u_n$, and the Tate comparison identifies its induced map with $u$. For uniqueness, two candidate maps agree on every generic division group. Flatness descends agreement to the integral division groups and the separation of the division ideals gives equality of all coordinate power series.

**Local acceptance criterion.**

The final theorem must be an equivalence between actual integral formal-group homomorphisms and actual continuous Galois-equivariant Tate-module maps, with both inverse laws proved. It must transport through changes of formal coordinates and through finite extensions of the complete DVR, since later Picard constructions use chosen coordinates and local descent. Those functoriality lemmas follow from uniqueness and the finite-level comparisons and should be exported here. Merely postulating a record with a homomorphism and a compatibility field would leave the central local proof unformalized.

##### Local dependency and acceptance ledger

The order is: complete local algebra and actual torsion towers; the small-ball logarithm; finite flat closures and smooth formal quotients; bounded logarithms and curve saturation; integral $p$-typical operators; bounded projection with residue perfection removed; uniform special-kernel annihilation; complete-local inverse limits and finite closed graphs; integral Tate extension. The complete-local coset lemma can be implemented independently of the curve and quotient work. The algebraic division-ring construction can proceed in parallel once the semiabelian model interface is fixed, but its output must be connected to the formal coordinate definitions before integration.

The source’s numerical constants have been preserved: the ball is $p^2$, the bounded-logarithm and bounded-projection denominator is $p^{2-2e}$, and the special kernel is killed by $p^{2e}$. The Frobenius exponent $H$ and the preliminary annihilator $p^a$ are auxiliary and do not survive in the final uniform estimate. Nothing in these proofs allows the replacement of the actual bounded-denominator generic rings by $K[[X]]$, or the replacement of scheme-theoretic kernels by geometric points.

The mathematical route in these sections is sufficiently explicit to give theorem-by-theorem implementation tasks. This review does not certify any of these new tasks as already formalized. In particular, the formal-to-affine quotient bridge, completed tensor products, the perfect-residue extension, and the bounded projection are substantial new proof bodies unless the repository audit locates definitions and theorems with exactly the required hypotheses. A citation to a Stacks tag records the mathematical theorem to port or reuse; it does not by itself assert an existing Lean implementation.


### P03 Picard models inertia and Kummer approximation

##### Picard, inertia, and Kummer pipeline: implementation contract

This dossier covers source Sections 5–7, lines 1208–2456 of manuscript version 78. Every result below is a mathematical specification and a proof to implement; none is reported as an already compiled Lean theorem. The proposed files live under the integration root `MochizukiHom/`. The formal-group Tate-extension theorem is an upstream dependency of this dossier. In particular, a field of type `LinearizationData` carrying the desired conclusions would not discharge that dependency.

The objects must be the actual relative Picard functor, its represented algebraic space, its identity completion, and its finite torsion group schemes. Do not substitute an abstract group with isomorphic points for any of these objects. Torsor classes must be functorial in the actual group-scheme maps. This requirement is essential when the same map is used both for finite Kummer transfer and for differentiation.

Where Stacks and NYLL overlap, the canonical definitions, instances, and theorems are those of Stacks, following the user’s explicit priority. Use NYLL for non-overlapping results and transport their input and output through proved comparison maps in `Compat/`. In particular, the NYLL Abel–Jacobi adapter below is not permission to install a second canonical Picard functor, finite-etale predicate, or fundamental group.

Throughout the local construction, the ground valuation ring is a complete mixed-characteristic $(0,p)$ DVR unless a weaker hypothesis is explicitly given. The word “ordinary” in the manuscript means the usual Jacobian or usual Picard functor; it does *not* impose ordinary reduction on an abelian variety. No perfectness, finiteness, or finite generation assumption on the residue field may be added to the terminal theorems.

##### Fixed semistable models and their relative Picard groups

###### Semistable model input and the node calculation

**Source and proposed location.**

The unnamed paragraphs immediately preceding `lem:vertical-multidegree-graph`; `Picard/Model.lean`.

For a smooth proper geometrically connected curve $C/K$, construct after a finite separable extension a proper split semistable model $X/R$ and a section $b$ through its smooth locus. “Split” means that every normalization component is geometrically connected and every node and both of its branches are rational over the residue field. Proper smooth curves are projective (Stacks Tag `0BY1`); their global regular functions are $K$. Feed these hypotheses to semistable reduction (`0CDN`). A further finite separable residue-field extension splits the finitely many nodes, branches, and component constant fields. Lift this extension to a finite unramified extension of the complete local field. Choose a smooth special point after a finite separable residue extension, and use Hensel lifting to obtain $b$.

The local calculation to formalize is the following. Let $$A=R[[x,y]]/(xy-\pi^e),\qquad D=V(\pi,x),$$ and let $Z$ be a horizontal height-one prime of $A$. Put $L=\operatorname{Frac}(A/Z)$, $a=x(Z)$, $d=[L:K]$, and $i=v_R(a)$, using the extension of the normalization $v_R(\pi)=1$. Then $0<i<e$, $L=K(a)$, and for the monic minimum polynomial $P_a$, $$\operatorname{div}(P_a(x))=Z+diD.                 \tag{PK-NC}$$ Here $i$ may be rational; $di$ is an integer. This distinction must be retained in the Lean statement.

Prove normality of $A$ by $S_2$ for a hypersurface and regularity away from its closed point, using the normality criterion of Tag `031S`. Since $(\pi)$ is primary for the maximal ideal of $A/Z$, lifting a residue basis through its complete $\pi$-adic filtration makes $A/Z$ a finite $R$-module. The two coordinate images are $a$ and $\pi^e/a$; completeness and the indicated local branch identify its fraction field with $K(a)$. On the generic fibre, substitution of these coordinates gives horizontal multiplicity one. The valuation along $D$ is $di$: every conjugate root of $P_a$ has valuation $i$, and its constant term is the unique term of least $D$-valuation. Along the other vertical branch the valuation is zero. These calculations establish (PK-NC) as an equality of Weil divisors.

For a section $C_c$ with coordinate $a_c$ of the same valuation as $a$, the rational function $$P_a(x)/(x-a_c)^d$$ has horizontal divisor $Z-dC_c$ and no vertical component. On the two normalized special branches its reduction, after removing the common vertical valuation, is respectively $1$ and $\overline{\operatorname{Norm}_{L/K}(a)/a_c^d}\ne0$. The same calculation holds for $xy=q$ after absorbing its unit into one coordinate. Pass from complete local rings to split etale charts by the unique Hensel lift at the specified residue point.

**Proof obligations and exit criterion.**

This paragraph is not supplied merely by the existence of semistable models. It needs a divisor valuation API, a finite-normalization lemma, comparison with the completed chart, and descent of the resulting Cartier divisor. In particular, the claim $L=K(a)$ must be proved for the actual chosen etale chart, not silently inferred for an arbitrary etale extension. The exit theorem must provide both the Cartier horizontal difference and its trivial restrictions to normalization components; both outputs are used again below.

###### Vertical line bundles detected by specialization

**Source and module.**

`lem:vertical-multidegree-graph`; `Picard/Model.lean`.

**Statement.**

Let $Y/R$ be proper and flat over a DVR. Assume its special fibre is reduced, connected, and pure of dimension one. If a line bundle $\mathcal L$ is trivial on $Y_K$ and has degree at most zero on every irreducible component of $Y_k$, then $\mathcal L\simeq\mathcal{O}_Y$. Do not add regularity, a nodal hypothesis, splitness, or geometric integrality of the generic fibre.

**Proof to implement.**

Proper cohomological finiteness and flat base change, Tags `02O6` and `02KH`, give a finite module $M=H^0(Y,\mathcal L)$ with $M\otimes_RK=H^0(Y_K,\mathcal{O}_{Y_K})\ne0$. Flatness of $Y/R$ makes $M$ torsion free; over a DVR it is finite free of positive rank. Choose $s\in M\setminus\pi M$. The exact sequence obtained by multiplication by $\pi$ on $\mathcal L$ gives an injection $M/\pi M\hookrightarrow H^0(Y_k,\mathcal L_k)$, so $s_k\ne0$. The componentwise nonpositive-degree criterion of Tag `0E22` makes this special-fibre section nowhere zero. The zero locus of $s$ is closed and proper over $R$. Its image is closed and misses the closed point of $\operatorname{Spec}R$, hence is empty. Thus $s$ trivializes $\mathcal L$.

**Exit criterion.**

Expose a theorem for arbitrary base-changed DVRs $A/R$, since the separatedness proof uses exactly this version. The theorem should return an isomorphism of line bundles, not only equality of their classes in a Picard group.

###### Rigidification and effective descent of Picard classes

**Source and module.**

`lem:rigidified-picard-effective-descent`; `Picard/Model.lean`.

**Statement.**

Suppose $f:X\to S$ has a section $b$ and, after every base change $T\to S$, the natural map $\mathcal{O}_T\to f_{T,*}\mathcal{O}_{X_T}$ is an isomorphism. Every section of the relative Picard fppf sheaf on $T$ has a representative $(\mathcal L,b_T^*\mathcal L\simeq\mathcal{O}_T)$, unique up to a unique rigidification-preserving isomorphism. This correspondence commutes with base change. If an algebraic space $P$ represents the sheaf, it carries a universal rigidified line bundle on $X\times_SP$.

**Proof to implement.**

Tag `0B9N` identifies the relative Picard sheaf with the kernel of restriction to $b$; Tag `0D28` gives the algebraic-space variant. Normalize a representative $L$ by $L\otimes f_T^*(b_T^*L)^{-1}$. An automorphism of a line bundle is multiplication by a global unit. The structural-sheaf hypothesis identifies that unit with a unit of the base, and preservation of the rigidification forces it to be $1$. Existence after fppf localization and uniqueness on overlaps therefore give effective descent. On etale charts of $P$, apply this construction to the represented universal classes; glue using the unique normalized isomorphisms.

**Exit criterion.**

The universal line bundle and its pullback formula must be output as data with a base-change theorem. This is the bridge used to turn points of a Picard space into actual divisors and to identify the actual Abel–Jacobi map later.

###### The multidegree-zero Picard group of a fixed model

**Source and module.**

`prop:fixed-multidegree-zero-picard`; `Picard/Model.lean`.

**Statement.**

For a proper flat finitely presented $X/R$ whose generic fibre is a smooth geometrically connected curve and whose special fibre $C$ is split semistable, let $G$ be the fppf subsheaf of relative Picard classes of degree zero on every component of every geometric fibre. It is a smooth separated finitely presented commutative group algebraic space. Its generic fibre is $J_{X_K}$, and its special fibre has an exact fppf sequence $$0\longrightarrow T_\Gamma\longrightarrow G_k
 \longrightarrow\prod_v J_{\widetilde C_v}\longrightarrow0,
 \qquad T_\Gamma\simeq\mathbf G_m^{b_1(\Gamma)}.        \tag{PK-RP}$$ No assertion that $G$ itself is a scheme is required.

**Proof to implement.**

First establish the hypotheses for the represented relative Picard space. Connectedness of the special fibre follows from the normal base, properness, and the generic global-function calculation (`0AY8`); all geometric fibres are reduced and connected. Tag `0E0L` gives universal $f_*\mathcal{O}_X=\mathcal{O}_R$. Use `0D2C` and `0DPK` for representability and smoothness, and `0DNI` for quasi-separatedness and local finite presentation. Do not use the geometrically integral-fibre separatedness result `0DNJ` at this step.

Define total degree by $\chi(X_t,\mathcal L_t)-\chi(X_t,\mathcal{O}_{X_t})$. Its local constancy under base change is Tag `0B9T`. The total-degree-zero part $P^{\mathrm{tot},0}$ is therefore open and closed. On the special fibre, the finitely many degrees on normalization components are also locally constant, giving an open-and-closed part $P_k^{\mathbf0}$. The desired open subgroup is $$G=P^{\mathrm{tot},0}\setminus
       (P_k^{\mathrm{tot},0}\setminus P_k^{\mathbf0}).$$ Prove that its functor of points is precisely the original sheaf condition and that multiplication and inversion restrict to it.

For the special fibre, describe line bundles on the nodal curve by line bundles on $\coprod_v\widetilde C_v$ together with fibre identifications at pairs of branches. The local construction is patching rank-one modules over a fibre product of the two branch rings over their common residue ring. It commutes with an arbitrary test $k$-algebra. Restriction to the normalization is fppf surjective: represent the component Picard classes by line bundles and choose the finitely many fibre identifications fppf locally. The kernel consists of one gluing scalar per edge, modulo changes of trivialization on vertices: $$\mathbf G_m^{E(\Gamma)}\big/
 \delta(\mathbf G_m^{V(\Gamma)}/\mathbf G_m).$$ A spanning tree splits off the vertex quotient, leaving $\mathbf G_m^{|E|-|V|+1}$. Loops represent self-nodes and must be included. The component Picard groups are Jacobians (`0BA0`, followed by field descent). This proves (PK-RP). The resulting torus torsor over the product of Jacobians is affine, smooth, and of finite type; in particular $G_k$ is a scheme and is semiabelian.

Both $G_K$ and $G_k$ are quasi-compact. Since the DVR spectrum has only its generic and closed point, finitely many members of any open cover cover each fibre, hence their union covers $G$. Thus $G$ is quasi-compact. Combine this with quasi-separatedness and local finite presentation to obtain finite presentation.

For separatedness, pass fpqc locally to a strictly Henselian DVR and choose $b$ through a smooth special point. Rigidification represents a class in the kernel of $G(A)\to G(\operatorname{Frac}A)$ for every test DVR $A/R$ by an actual line bundle. Its generic fibre is trivial and its special component degrees are zero. The preceding vertical-line-bundle theorem makes it trivial on $X_A$. Discrete valuative uniqueness, together with quasi-separatedness and local finite presentation, is exactly the separatedness input of Tag `0ARJ`.

**Exit criterion and integration risk.**

The construction must use one represented Picard object throughout, with explicit equivalences when NYLL and Stacks use different presentations. Checking only the lists of point groups is insufficient. The relative degree-zero versus algebraic-equivalence cut comparison is a separate sheaf-level obligation, not an automatic consequence of equality on algebraically closed points.

##### Actual Abel–Jacobi maps and their finite and differential realizations

###### Finite-coefficient Abel–Jacobi isomorphism

**Source and module.**

`lem:proper-abel-jacobi-tate-stacks`; `Picard/AbelJacobi.lean`.

**Statement.**

For a smooth proper geometrically connected characteristic-zero curve $C/k$, its usual Jacobian $J$, and a base point $b$ after a finite constant extension, the actual morphism $\alpha_b:C\to J$ induces $$H^1_{\mathrm{\acute et}}(J_{\bar k},\mathbf Z/m)
   \xrightarrow{\sim}H^1_{\mathrm{\acute et}}(C_{\bar k},\mathbf Z/m),
 \quad
 \pi_1(C_{\bar k})^{\mathrm{ab}}/m
   \xrightarrow{\sim}J[m](\bar k)
                                                        \tag{PK-AJ}$$ for every $m\ge1$. The second map is the composite of the map on fundamental groups and the monodromy map of the multiplication torsor $[m]:J\to J$. It is compatible with coefficient changes and the Galois action.

**Proof to implement.**

Build the curve model from the smooth proper curve using NYLL’s `CurveModel.ofSmoothProperCurve`, with its curve-over-a-field input obtained from the finite extension of a one-variable transcendental function field. Supply the actual relative Picard representability and Abel–Jacobi data through `CurveModel.exists_representsRelSubPic_abelJacobi_of_isAlgClosed`. Identify the represented algebraic-equivalence-zero subfunctor with the degree-zero subfunctor: over an algebraically closed field, a degree-zero divisor is a sum of $x-b$, each algebraically equivalent to zero; conversely degree is constant in a connected family. Prove this on the specified relative functor, including the geometric-fibre criterion and descent, before applying representability uniqueness. The normalized universal line bundle then satisfies $$\mathcal P_L|_{C_L\times\{\alpha_b(x)\}}
       \simeq\mathcal{O}_{C_L}(x-b_L)$$ for every field extension $L/\bar k$ and $x\in C(L)$.

Feed this actual morphism and point-divisor formula to the audited NYLL Abel–Jacobi $H^1$ interface. Choosing a primitive root only to identify $\mu_m$ with $\mathbf Z/m$ verifies the first isomorphism. Apply NYLL’s finite-character description of $H^1$ to dualize it to the map on abelianized finite fundamental groups. The connected finite etale $J[m]$-torsor $[m]$ gives a surjection from $\pi_1(J)^{\mathrm{ab}}/m$ onto $J[m](\bar k)$. Tags `03RQ` and `03RP` compute both orders as $m^{2g}$, making it an isomorphism. The composite is the second map in (PK-AJ).

**Exit criterion.**

Finite-group cardinality arguments only establish bijectivity. Add separate commutative diagrams for $m\mid m'$, Galois conjugation, and base change, derived from the actual multiplication torsors. The final Tate equivalence is their inverse limit; it must not depend on the temporary primitive-root choice.

###### Invariant differentials on a proper Jacobian

**Source and module.**

`prop:proper-jacobian-differentials-core`; `Picard/AbelJacobi.lean`.

**Statement and proof.**

The pullback of invariant differentials along $\alpha_b$ induces a natural isomorphism $$e^*\Omega^1_{J/k}\xrightarrow{\sim}H^0(C,\omega_C).
                                                        \tag{PK-AD}$$ It is independent of $b$, descends to $k$, and commutes with field extension, norm maps for nonconstant curve morphisms, and deck transformations.

For $g=0$ both spaces vanish. For $g>0$, work first over $\bar k$ and consider $\sigma:C^g\to J$, $(x_i)\mapsto\sum_i[x_i-b]$. Riemann–Roch (`0BS6`) gives a nonzero section of $M(gb)$ for every degree-zero line bundle $M$; its effective zero divisor expresses $M$ in the image of $\sigma$. Properness turns surjectivity on geometric closed points into surjectivity. Equal dimensions $g$ make $\sigma$ generically finite, and characteristic zero makes the resulting function-field extension separable. Pullback of rational differentials is therefore injective. For an invariant differential $\eta$, $$\sigma^*\eta=\sum_i\operatorname{pr}_i^*\alpha_b^*\eta.$$ Hence $\alpha_b^*\eta=0$ forces $\eta=0$. Both spaces in (PK-AD) have dimension $g$, so the map is an isomorphism. Use `047I` for invariant differentials and `02KH` for cohomological base change, then faithfully flat descent.

A nonconstant proper-curve morphism is finite flat (`0CCL`, `0CCK`). Its determinant norm (`0BD2`, `0BCY`) sends point divisors to their images. This proves the square with Abel–Jacobi maps before differentiating. Changing $b$ translates the Jacobian, and invariant differentials are translation invariant; this proves independence and descent to $k$. The same actual morphism identities give deck-equivariance.

**Exit criterion.**

Package both the linear equivalence and its naturality, with the covariant norm map and contravariant differential pullback directions explicit. Later reconstruction uses the naturality to compare different auxiliary covers, not just equality of dimensions.

###### Covers of the multiplicative group and point sections

**Source and module.**

`lem:gm-covers-without-generalized-jacobian`; `Picard/AbelJacobi.lean`.

In characteristic zero, the geometric pro-$p$ fundamental group of $\mathbf G_m$ is $\mathbf Z_p(1)$. A geometrically connected finite $p$-cover becomes $t\mapsto t^{p^b}$ after finite constant extension, and the difference of its point sections relative to $1$ is the usual Kummer class.

Over an algebraic closure, compactify a connected finite etale cover to $\overline V\to\mathbf P^1$. The pullback of $dt/t$ is nowhere vanishing on $V$. At a boundary point, write $t=uz^{\pm e}$; the differential is $\pm e\,dz/z+du/u$ and has a simple pole, since $e\ne0$ in characteristic zero. If $r_0,r_\infty$ count points over $0,\infty$, the canonical-divisor degree formula gives $2g(\overline V)-2=-(r_0+r_\infty)$. Both counts are positive, so the genus is zero and each count is one. Riemann–Roch for the pole point gives a degree-one map to $\mathbf P^1$, an isomorphism by normal proper curve/function-field correspondence (`0BY1`). With the boundary at $0,\infty$, the covering function is $ct^d$, and adjoining a root of $c$ normalizes it to $t^d$. All coordinates descend to a finite constant extension. This proves cofinality of the Kummer covers. The Galois action on the fibre of $p^n$th roots of a point is literally its Kummer cocycle, proving the section formula.

**Exit criterion.**

Prove a classification of actual covers with coordinate isomorphisms, then the profinite and pro-$p$ conclusions. The section-difference formula must use the same action convention as the arithmetic fundamental-group exact sequence.

##### Finite local Kummer lifting and integral point correction

###### Kummer lifting through an open subgroup over a strictly Henselian base

**Source and module.**

`lem:picard-local-factor-kummer`, also `lem:picard-connected-kummer-lift`; `Picard/Model.lean`.

Let $R$ be strictly Henselian, $\mathcal G/R$ a smooth commutative group algebraic space, and $[m]:\mathcal G\to\mathcal G$ an fppf surjection. Put $H=\ker[m]$ and let $C\subset H$ be an open subgroup. The maps $$H^1(R,C)\longrightarrow H^1(R,H),\qquad
 \mathcal G(R)\longrightarrow H^1(R,H)
                                                        \tag{PK-SH}$$ are surjective. If $C$ is finite locally free, its torsors are finite locally free.

The quotient $U=H/C$ exists and $H\to U$ is an fppf torsor (`06PH`). The unit section of $U$ is open because its pullback is $C\subset H$. Its pullback along the difference map is the diagonal, proving that $U$ is unramified. Flatness and local finite presentation descend from $H$, so $U$ is etale. A torsor under any smooth group algebraic space over a strictly Henselian local ring has a point: it is represented (`04UT`); choose a smooth etale scheme chart and apply etale-local sections and Hensel lifting (`055U`, `04GG`). Thus $H^1(R,U)=H^1(R,\mathcal G)=0$.

For an $H$-torsor $P$, a point of $P/C=P\times^HU$ has a fibre which is a $C$-torsor and whose pushout recovers $P$. This gives the first map of (PK-SH). Trivializing $P\times^H\mathcal G$ gives an $H$-equivariant map $P\to\mathcal G$; composing with $[m]$ descends to a point $z\in\mathcal G(R)$, and $P\simeq[m]^{-1}(z)$ as torsors. This proves the second surjectivity. Finite local freeness descends fppf locally.

**Exit criterion.**

Use torsor groupoids or their isomorphism classes with explicit pushout and generic-fibre comparison. A theorem merely saying that some cohomology groups vanish does not supply the required commutative pushout diagram.

###### Constant-point correction by horizontal divisors

**Source and module.**

`lem:picard-constant-point-correction`; `Picard/Model.lean`.

Let $X/R_0$ be the fixed split semistable curve with a smooth-locus base section, and let $\mathcal G$ be its multidegree-zero Picard group, with generic fibre $J$. Suppose $F/K$ is a complete DVR extension whose valuation ring dominates $R_0$, and $E/F$ is algebraic and contains $\bar K$. For every $P\in J(E)$ there are $$z\in\mathcal G(\mathcal O_E),\qquad c\in J(\bar K),
 \qquad P=z+c.                                      \tag{PK-PC}$$

Pull back the normalized universal line bundle by $P$. A rational trivialization gives a degree-zero signed divisor $D=\sum_Zm_ZZ$. Its finite data descend to a finite $F'/F$ inside $E$. At a smooth special point, choose a constant section $c_Z$ on the same component. At a node, choose $a_c\in\bar K$ with the same valuation as the coordinate $a=x(Z)$ and lift $(a_c,q/a_c)$ in the prescribed split chart. Enlarge $F'$ to contain the finitely many constants and re-decompose the divisor into closed points. Denote their degrees by $d_Z$.

For smooth specialization, $\overline Z$ is Cartier by regular local factoriality (`0AG0`), and degree specialization (`0B9T`) puts degree $d_Z$ on exactly the chosen component. Hence $\overline Z-d_Z\overline{c_Z}$ has multidegree zero. At a node, (PK-NC) expresses this difference by $P_a(x)/(x-a_c)^{d_Z}$; its nonzero constant reductions on both normalized branches make the restrictions trivial. On overlaps, the transition quotients and their inverses are regular at all height-one points; normality makes them units (`031T`). Descend the Cartier divisor through the charts (`023T`). The signed sum defines a line bundle of multidegree zero and generic class $P-c$, where $c=[\sum_Zm_Zd_Zc_Z]\in J(\bar K)$ because its total degree is zero. This yields $z$ over $\mathcal O_{F'}$, hence over $\mathcal O_E$.

**Exit criterion.**

The output must lie in the same fixed $\mathcal G$ used for the formal group and its differential lattice. A different integral model for each corrected point would not prove the later uniform $p^n$ differential estimate. This result depends on the full node calculation, not only the existence of a Neron-type model.

###### Fixed models for Jacobians and the multiplicative group

**Source and module.**

`lem:ordinary-picard-model-core`; `Picard/Model.lean`.

For $S$ a usual Jacobian or $\mathbf G_m$ over a complete mixed-characteristic DVR field, a finite constant extension provides a smooth commutative group algebraic space $G/R_0$ with generic fibre $S$, fppf-surjective multiplication maps, and connected finite flat open torsion subgroups $$C[p^n]=\widehat G[p^n]\subset G[p^n],\qquad
 \omega_{C[p^n]}=\omega_G/p^n\omega_G.
                                                        \tag{PK-FM}$$ These form a connected Barsotti–Tate group $C$, its Tate module embeds saturatedly in $T_pS$, and (PK-PC) holds.

For Jacobians, combine the semistable input, the constructed multidegree-zero Picard algebraic space, and the preceding formal-division theorem of source Section 3. Saturation has a useful finite-level proof. If $t=(t_n)\in T_pS$ and $pt\in T_pC$, then $t_n=(pt)_{n+1}$ lies in $C[p^{n+1}]$ and is killed by $p^n$; therefore $t_n\in C[p^n]$ for every $n$, so $t\in T_pC$. For $\mathbf G_m$, use $G=\mathbf G_{m,R_0}$ and $C[p^n]=\mu_{p^n}$. Because $E$ contains algebraically closed constants and is algebraic over a discretely valued extension, its normalized value group is $\mathbf Q$. Choose a constant $c$ with the same value as $P$; then $P/c$ is integral and invertible.

**Exit criterion.**

Supply one structure whose fields are these actual constructions and their proved properties. It must not include inertia characterization, Kummer transfer, or linearization as assumptions: those are the next theorems to derive.

##### Inertia characterization and finite-local linearization

###### A uniform exponent for unramified finite connected groups

**Source and module.**

`lem:finite-connected-unramified-exponent`; `Picard/Inertia.lean`.

Let $R_0$ be a Hensel mixed-characteristic DVR, $e=v_\pi(p)$, and choose $s\ge0$ with $(p-1)p^s>e$. If a finite flat commutative $p$-group $Q/R_0$ has connected special fibre and unramified generic fibre, then $[p^s]_Q=0$.

Rationalize all generic points over a finite unramified extension $R'/R_0$. Finiteness and normality extend them to $R'$-points, and connectedness makes all reduce to the identity. Write $\mathcal{O}(Q)=R_0\oplus I$ and choose an $R_0$-basis $x_i$ of $I$. The iterated $p$-fold comultiplication is cyclically invariant. Orbits of pure tensor terms have length $1$ or $p$. The one-factor terms sum to $px_i$; the other length-$p$ orbits lie in $pI^2$; the fixed nonzero terms lie in $I^p$. Thus $$[p]^*x_i-px_i\in pI^2+I^p.$$ For $g\ne1$, put $a(g)=\min_i v_\pi(x_i(g))\ge1$. Then $$a([p]g)\ge\min(e+a(g),p\,a(g)).                    \tag{PK-UE}$$ Below the threshold $e/(p-1)$ the lower bound multiplies by $p$. After $s$ iterations it exceeds that threshold or the point is already the identity. Above the threshold the error terms have strictly greater valuation than $e+a$, so the next value is exactly $e+a$. Such a nonidentity point can never become the identity under further powers of $p$, contradicting $p$-power torsion. Therefore $p^s$ kills every generic point. Etaleness of the characteristic-zero generic fibre and flatness over $R_0$ promote this to equality of group-scheme maps.

**Exit criterion.**

Keep the exponent independent of the order, dimension, or height of $Q$. Prove the Hopf-algebra orbit calculation and the strict valuation statement, rather than replacing them with a numerical heuristic for coordinates.

###### Inertia differences generate a connected BT representation

**Source and module.**

`lem:connected-bt-no-unramified-direct`, also `lem:connected-bt-no-unramified`; `Picard/Inertia.lean`.

For a connected BT group $C/R$, put $T=T_pC$ and $M=\sum_{\sigma\in I_K}(\sigma-1)T$. With the preceding $s$, $$p^sT\subset M,\qquad
 V_pC=\operatorname{span}_{\mathbf Q_p}
      \{(\sigma-1)v:\sigma\in I_K\}.
                                                        \tag{PK-ID}$$ Consequently $\operatorname{Hom}_{G_K}(V_pC,W)=0$ for every finite-dimensional unramified $\mathbf Q_p$-representation $W$.

The submodule $M$ is $G_K$-stable since inertia is normal. For every $m$, the finite unramified quotient $T/(M+p^mT)$ is a quotient of $C[p^m](\bar K)$. Galois descent realizes it as a finite etale group-scheme quotient on the generic fibre. Take the schematic closure of its kernel in $C[p^m]$ and use the finite-flat closure-and-quotient theorem. Its quotient $Q_m$ is finite flat, has connected special fibre as a quotient of a connected group, and has the indicated unramified generic fibre. The uniform exponent theorem kills every $Q_m$ by $p^s$. Hence $p^sT\subset\bigcap_m(M+p^mT)=M$. The last equality follows because $T/M$ is a finite generated $\mathbf Z_p$-module and is $p$-adically separated. Rationalize to obtain (PK-ID). A map to an unramified representation kills every generator, proving its vanishing.

**Exit criterion.**

Treat $M$ as a genuine submodule generated by the differences. Its finite generation follows from the Noetherian property of $\mathbf Z_p$; no unproved closure assumption on an infinite sum of inertia images is needed.

###### The connected Tate lattice is intrinsic

**Source and module.**

`cor:picard-connected-inertia-span`; `Picard/Inertia.lean`.

Suppose $T_pC\hookrightarrow T$ is a saturated equivariant embedding into a finite free $\mathbf Z_p$-representation, and $T/T_pC$ is unramified. Write $V=T\otimes\mathbf Q_p$ and $W_I(V)=\operatorname{span}\{(\sigma-1)v\}$. Then $$T_pC=T\cap W_I(V).                                  \tag{PK-IL}$$ The quotient being unramified gives $W_I(V)\subset V_pC$; (PK-ID) gives the reverse inclusion, and saturation intersects back with $T$. Equivariant maps preserve inertia differences, so they preserve the lattices. A rationally surjective map is surjective on the rational connected parts by lifting each inertia-difference generator. After finite field extension, the BT special fibre remains geometrically connected and the quotient remains unramified, so the same argument identifies the same lattice. Different fixed models satisfying these conditions consequently produce identical lattices.

**Exit criterion.**

Include the finite-extension and rational-surjectivity theorems; they are used separately in model independence and nonvanishing of the linearization.

###### Inertia differences lie in the formal connected torsion

**Source and module.**

`lem:picard-inertia-difference-connected`; `Picard/Inertia.lean`.

For the fixed semistable model, inertia acts trivially on $J[p^n](\bar K)/C[p^n](\bar K)$ for all $n$. Thus $T_pJ/T_pC$ is torsion free and unramified.

Represent $P\in J[p^n](\bar K)$ as a signed sum $\sum_jm_jz_j$, with $\sum_jm_j=0$, after a finite Galois extension $L/K$. For $\sigma\in I_K$, the specializations of $z_j$ and $\sigma z_j$ coincide. At a smooth point their horizontal difference is Cartier and restricts trivially to the special component. At a node, equal coordinate valuations and (PK-NC) express it by $(x-\sigma a)/(x-a)$, whose reductions on the normalized branches are nonzero constants. Descend and sum these local divisors to a line bundle $\mathcal N$ on $X_{\mathcal O_L}$. Its generic class is $\sigma P-P$ and its special normalization restrictions are trivial.

Since $\mathcal N^{\otimes p^n}$ is generically trivial and has zero multidegree, the vertical-line-bundle theorem makes it trivial on the whole model. The special class of $\mathcal N$ belongs to the split gluing torus and is killed by $p^n$. In characteristic $p$, the group of field-valued $p^n$-torsion points of a split torus is trivial. Thus $\mathcal N$ reduces to the identity. It represents an integral $p^n$-torsion point reducing to the identity, which the formal-division theorem identifies with $C[p^n]$. This proves the finite-level inertia statement. Use the previous saturation theorem and inverse limits for the Tate quotient.

**Exit criterion.**

The proof must establish equality of special Picard classes, not merely zero degree; this is why the gluing torus and its lack of nontrivial characteristic-$p$ field-valued $p$-torsion are needed.

###### A formal-group homomorphism is detected by its differential

**Source and module.**

`lem:formal-hom-differential-faithful-elementary`; `FormalGroups/Basic.lean`.

Over a characteristic-zero integral domain, a homomorphism $F$ between coordinate smooth commutative formal groups is zero if $dF=0$. Differentiate $F(P(X,Y))=Q(F(X),F(Y))$ in $Y$ at $Y=0$: $$J_F(X)\partial_2P(X,0)
       =\partial_2Q(F(X),0)dF.$$ The first formal matrix on the left after $J_F$ has constant term the identity, hence is invertible. Therefore all partial derivatives of $F$ vanish. Coefficient comparison and characteristic zero show that every nonconstant coefficient is zero, and preservation of the identity kills the constant term.

**Exit criterion.**

This is a statement over the original domain, not only over its fraction field; include the coefficient-injectivity lemma used when transporting the conclusion from characteristic-zero scalars.

###### Integral formal realization and nonzero differential

**Source and module.**

`prop:ordinary-picard-integral-map-nonzero-core`; `Picard/Linearization.lean`.

For fixed models $\mathcal G_i/R$ of usual Jacobians or $\mathbf G_m$, put $P_i=\widehat{\mathcal G_i}$, $T_i=T_pS_i$, and $H_i=T_pP_i$. Every equivariant $u:T_1\to T_2$ preserves $H_i$ and has a unique integral formal realization $$F_u:P_1\longrightarrow P_2,
 \qquad T_pF_u=u|_{H_1}.                              \tag{PK-LI}$$ Its differential $\lambda_u^{\mathcal G}=dF_u\otimes_RK$ commutes with addition, $\mathbf Z_p$-scalars, identities, composition, and finite constant extension. It is nonzero if $u\otimes\mathbf Q_p$ is surjective and $\dim S_2>0$, or if $S_1=\mathbf G_m$ and $u\ne0$.

For Jacobians use the preceding inertia theorem, and for $\mathbf G_m$ note $H_i=T_i=\mathbf Z_p(1)$. Formula (PK-IL) shows $u(H_1)\subset H_2$. Apply the previously proved formal Tate-extension theorem to this restriction; its uniqueness gives all the functoriality assertions and agreement with any already existing integral realization.

Under rational surjectivity, lifting inertia differences shows that $H_1\otimes\mathbf Q_p\to H_2\otimes\mathbf Q_p$ is onto. If $\dim S_2>0$, then $\omega_{P_2[p]}=\omega_{P_2}/p\omega_{P_2}\ne0$, so the finite flat group $P_2[p]$ is nontrivial. Its generic fibre has the same rank and is etale, hence $H_2/pH_2=P_2[p](\bar K)\ne0$. Thus $F_u\ne0$, and differential faithfulness gives $\lambda_u^{\mathcal G}\ne0$. For source $\mathbf G_m$, $H_1=T_1$, so a nonzero $u$ already makes $F_u$ nonzero.

**Exit criterion.**

The call to formal Tate extension is a real proof dependency. No realization is available until that theorem has been proved for the unrestricted residue fields needed here. All naturality identities must be theorem outputs, not fields in the assumptions.

###### Algebraic and formal graphs have the same differential

**Source and module.**

`lem:formal-graph-torsion-compatibility`; `Picard/Linearization.lean`.

Let $\mathcal G_i/R$ be smooth commutative group algebraic spaces with coordinate completions $P_i$, finite-free $[p]$ on the completions, and separated target generic fibre $S_2$. If an algebraic $f:S_1\to S_2$ and integral formal $F:P_1\to P_2$ agree on every generic finite torsion subgroup $P_1[p^n]_K$, then $dF\otimes_RK=df$.

After finite unramified extension, choose affine etale charts $U_i$ through the identity. Write $A=R[[X]]$, $B=\mathcal{O}(U_1\times_RU_2)$, and let $\phi:B\to A$ be the formal graph. The inverse image of the algebraic graph is closed on the generic fibre because $S_2$ is separated. If $I_K\subset B[1/\pi]$ is its ideal and $I=I_K\cap B$, then $I[1/\pi]=I_K$. Let $A_n=A/J_n=\mathcal{O}(P_1[p^n])$. Formal etale uniqueness (`02HM`) identifies the specialization of $\phi$ to $A_n$ with the actual torsion graph. Agreement on the generic torsion and flatness of $A_n/R$ give $\phi(I)\subset J_n$. The formal-division theory proves $\bigcap_nJ_n=0$, so $\phi(I)=0$. Evaluate $X\mapsto\epsilon v$ into $K[\epsilon]/(\epsilon^2)$. The resulting tangent pair lies on the algebraic graph; therefore $dF(v)=df(v)$. Etale charts identify tangent spaces and faithful field extension detects the equality. Differential faithfulness over $K$ also yields $F_K=\widehat f$ as formal power series.

**Exit criterion.**

Keep the distinction between $R[[X]][1/\pi]$ and $K[[X]]$. They are not interchangeable rings. The proof uses finite torsion quotient rings and dual numbers, so it does not require that incorrect identification.

###### Finite-local descent of every equivariant Tate map

**Source and module.**

`lem:subtame-finite-local-tate-descent`; `Picard/Linearization.lean`.

**Statement.**

Fix a $p$-subtame presentation $K\hookrightarrow T=M^{\mathrm{tame}}\subset\Omega=\overline M$ with $M$ complete and separably closed residue field. Define the finitely presented groups $S_1,S_2$ over one finite stage $M_0/M$ inside $T$, and put $T_i=T_pS_i(\Omega)$. Every $G_K$-equivariant $\mathbf Z_p$-linear map $u:T_1\to T_2$ is $G_L$-equivariant for the same finite field $$L=M_0(S_1[p],S_2[p]).                               \tag{PK-LD}$$ The assertion also applies after any finite $K_1/K$, inside the same fixed algebraic closure with its valuation. In particular the descent level depends on the groups, not on an arbitrarily chosen matrix of $u$.

**Proof to implement.**

Finite presentation puts the finitely many equations and group-law coefficients in a common finite $M_0$. Let $H=\operatorname{Hom}_{\mathbf Z_p}(T_1,T_2)$, $N=G_T$, and $U=H^N$. Since $N$ is normal in $G_{M_0}$, $U$ is a stable finite free module. It is saturated: if $ph$ is invariant, then $p(\sigma h-h)=0$ and torsion freeness gives invariance of $h$. Hence $U/pU\hookrightarrow H/pH$. Restriction of automorphisms along $K\subset T$ makes each given $u$ belong to $U$; this requires no inclusion $M\subset K$.

The action on $U$ factors through the pro-prime-to-$p$ group $\Gamma=\operatorname{Gal}(T/M_0)$. Let $\Gamma_n$ be its image on $U/p^nU$. The order of $\Gamma_n$ is prime to $p$. The kernel of reduction to $\Gamma_1$ is a subgroup of $1+p\operatorname{Mat}(U/p^nU)$. The filtration by $1+p^j\operatorname{Mat}$ has additive $\mathbf F_p$-vector space subquotients, so this kernel is also a $p$-group. It must be trivial. Thus an element acting trivially modulo $p$ acts trivially at every finite level, and separatedness $\bigcap_n p^nU=0$ makes it trivial on $U$.

By definition of $L$, $G_L$ acts trivially on $T_i/pT_i=S_i[p](\Omega)$ and hence on $H/pH$. Saturation transfers this to $U/pU$, and the preceding argument proves that it fixes $U$. This establishes (PK-LD). It works for $p=2$ as written: the finite congruence kernel is a $2$-group, whereas the acting quotient has odd order. No torsion-freeness claim for $1+2\operatorname{Mat}(\mathbf Z_2)$ is used.

For $K_1=K(\alpha)\subset\Omega$, the field $M(\alpha)/M$ is finite and $K_1\subset T M(\alpha)\subset M(\alpha)^{\mathrm{tame}}$ by tame base change. Its residue field, a finite extension of a separably closed field, remains separably closed. Repeat the same finite-stage and congruence argument without changing $\Omega$ or its valuation.

**Exit criterion.**

This theorem is a mandatory gate for the $p$-subtame conclusion. A theorem only for maps equivariant over a prechosen complete local subfield would leave the main field scope unproved. Formalize the saturation injection and prime-to-$p$ image lemma as reusable algebraic results, including the $p=2$ instance.

###### Linearization in the fixed valued realization

**Source and module.**

`lem:ordinary-picard-linearization-elementary`; `Picard/Linearization.lean`.

For $K\hookrightarrow M^{\mathrm{tame}}\subset\Omega$ as above, every equivariant $u$ has a finite local realization $F_u$ and an induced $$\lambda_u:\operatorname{Lie}(S_1)_\Omega
                 \longrightarrow\operatorname{Lie}(S_2)_\Omega.
                                                        \tag{PK-SL}$$ This map is independent of the finite stage and fixed model, respects addition, scalars, identities, composition, and finite constant extension in $\Omega$, agrees with $df$ for every algebraic group map $f$ over $\Omega$, and satisfies the two nonvanishing statements of integral linearization.

Descend $u$ by (PK-LD), enlarge finitely for models, and apply (PK-LI). Compare any two choices over one common finite extension of $M$. Formula (PK-IL) identifies their connected Tate lattices. Realize the identity on those lattices in both directions; uniqueness makes the resulting formal maps inverse. The formal/algebraic graph theorem applied to the actual identity shows their differentials are the identity on the algebraic Lie space. Composing with these comparison maps proves independence for $u$. The same uniqueness proves the additive and compositional identities. Any algebraic map over $\Omega$ has finitely many coefficients and descends to a finite local stage; torsion compatibility and the graph theorem identify its linearization with its actual differential.

If $K$ itself is complete discretely valued, construct over a finite Galois extension $K'/K$. Conjugate models and the same comparison identify their differential matrices. Equivariance of $u$ makes the matrix Galois invariant, so it descends to $K$. For a general $p$-subtame $K$, do not claim $K$-linearity at this stage. One cannot assume that every automorphism in $G_K$ preserves the auxiliary local field $M$.

**Exit criterion.**

The terminal output here is an $\Omega$-linear map with proved comparison properties. Descent of the reconstructed curve map to $K$ belongs to a later theorem and cannot be smuggled into this interface as an invariance hypothesis.

##### Finite Kummer transfer and a common integral differential estimate

###### Kummer image transfer by finite torsor pushout

**Source and module.**

`lem:ordinary-kummer-image-transfer`; `Kummer/FormalPoints.lean`.

Choose a finite complete local stage $M_0/M$ where $S_i$, $u$, and their fixed models are defined. Let $F/M_0$ be complete discretely valued with the dominating valuation ring and let $E/F$ be algebraic, contain $\Omega$, and have separably closed residue field. For every $P\in S_1(E)$ and $n\ge1$ there exists $Q_n\in S_2(E)$ such that $$u_n\kappa_{S_1,n}(P)=\kappa_{S_2,n}(Q_n)
       \quad\text{in }H^1(E,S_2[p^n]).                 \tag{PK-KT}$$

The valuation ring $R=\mathcal O_E$ is strictly Henselian. Let $v_n=F_u[p^n]:C_1[p^n]\to C_2[p^n]$; its generic fibre is the restriction of $u_n$ by the finite-level Tate comparison. Correct $P=z+c$ in the same fixed source model. The constant group $S_1(\Omega)$ is $p$-divisible, so its Kummer classes vanish and $\kappa(P)=\kappa(z)$. Lift the division torsor of $z$ to a $C_1[p^n]$-torsor by (PK-SH), push it out by $v_n$ and then by $C_2[p^n]\hookrightarrow\mathcal G_2[p^n]$. The second surjection in (PK-SH) represents the resulting torsor by an integral point $Q_n$. Generic fibre and pushout naturality give (PK-KT).

**Exit criterion.**

This result makes an independent existential choice for each $n$. Neither a compatible sequence $(Q_n)$ nor one point working at all levels is asserted. Do not demand such an unproved strengthening in the next stage.

###### A generic curve point in a one-variable Gauss completion

**Source and module.**

`lem:generic-polydisc`; `Reconstruction/CurveMap.lean`.

Given a smooth geometrically integral finite-type curve $T/K$ over a complete mixed-characteristic DVR field, choose a finite Galois $K'/K$ and $$F=\widehat{K'(t)},\qquad K'(T)\hookrightarrow F$$ for the Gauss valuation so that $D=\partial/\partial t$ extends continuously to $F$, preserves $K'(T)$, and is a basis of its one-dimensional space of $K'$-derivations. On $L=F^{\mathrm{nr}}\bar K$ it has a unique extension with $$D(\bar K)=0,
 \qquad v(Da)\ge v(a)\quad(a\in L),
 \qquad D(\mathcal O_L)\subset\mathcal O_L.           \tag{PK-GD}$$

Choose a rational point after finite Galois extension and an etale coordinate near it (`054L`, `02GT`). In a standard etale presentation $P(z,y)=0$, translate the point to $(0,0)$ and normalize $P_y(0,0)=1$. For sufficiently large $m$, substitution $z=\pi^{2m}t$, $y=\pi^mw$ gives $$\pi^{-m}P(\pi^{2m}t,\pi^mw)=w+\pi H(t,w),
 \qquad H\in\mathcal O_{K'}[t,w].$$ All other monomials have $2i+j-1\ge1$, and the finite denominator list in the etale chart can simultaneously be made units congruent to $1$. Hensel’s lemma (`04GG`) in the Gauss valuation ring gives $w\equiv0\pmod\pi$. The resulting point has $z=\pi^{2m}t$ transcendental, so it is a generic point and induces the required field embedding.

Polynomial differentiation does not lower the Gauss valuation; the quotient rule extends the inequality to $K'(t)$, and continuity extends $D$ to its completion. Since $K'(T)/K'(t)$ is finite separable, differentiating the minimum polynomial proves preservation of the function field and uniqueness of its derivation extension. Since $D(t)=1$, this derivation is its basis.

For each finite constant extension $K''/K'$, the compositum $FK''$ is the Gauss completion of $K''(t)$: it is finite, complete, closed, and contains the dense rational subfield. Thus the derivative bound persists. Tensoring a finite unramified extension of $\mathcal O_F$ with $\mathcal O_{FK''}$ gives a finite etale algebra; the chosen field component is the relevant integer ring. Formal etale lifting applied to $a\mapsto a+\epsilon D(a)$ (`00UR`) extends $D$ uniquely and integrally. Taking the union proves integral preservation on $L$ and vanishing on $\bar K$. Every value in $\Gamma_L=\mathbf Q$ is realized by a constant; for $a\ne0$ choose $c\in\bar K$ of equal valuation. Apply integral preservation to $a/c$ and use $D(c)=0$ to obtain the full inequality (PK-GD).

**Exit criterion.**

Do not confuse the rational function field with its Gauss completion or with a Laurent-series field. Record the actual embedding and the equality $t=\pi^{-2m}z$ in the curve function field; this is what permits the assertion that $D$ preserves that field.

###### Logarithmic differentiation

**Source and module.**

The unnamed definition of logarithmic differential; `Kummer/FormalPoints.lean`.

For a smooth commutative group $G/R_0$, an $R_0$-algebra $R$, a derivation $D:R\to R$, and $z\in G(R)$, define $\partial_Dz\in\operatorname{Lie}(G)\otimes_{R_0}R$ by evaluation against invariant differentials: $$\langle\eta,\partial_Dz\rangle
       =\langle z^*\eta,D\rangle.$$ Finite local freeness of the tangent/cotangent module gives existence and uniqueness. Differentiate the group law to prove additivity. For an actual group map $f$, prove $\partial_Df(z)=df(\partial_Dz)$. These are identities of the constructed tangent vectors, not equations chosen as part of a definition of a hypothetical derivative interface.

###### One formal point realizes all finite Kummer classes

**Source and module.**

`lem:formal-point-kummer-compatibility`; `Kummer/FormalPoints.lean`.

Let $\mathcal G_i/R$ be smooth separated group algebraic spaces over a complete DVR, with fixed identity etale charts, formal completions $P_i$, and finite-free $[p]$. Suppose $\varphi:P_1\to P_2$ realizes the restriction of $u:T_pS_1\to T_pS_2$. For a complete DVR extension $F/K$ and $x\in P_1(\mathfrak m_F)$, evaluation gives one actual point $q=\varphi(x)\in P_2(\mathfrak m_F)\subset S_2(F)$ with $$\kappa_{S_2,n}(q)=u_n\kappa_{S_1,n}(x)
                    \quad\text{for every }n\ge1.    \tag{PK-FK}$$ If a continuous $K$-derivation $D$ preserves $\mathcal O_F$, then $\partial_Dq=d\varphi(\partial_Dx)$.

Positive coordinate valuation makes every integral formal series converge. Composing the etale chart ring map with completion and evaluation constructs the actual integral point. Base change of the finite-free formal map $[p^n]$ along $x$ gives a finite flat division algebra. A geometric generic point of it yields a finite $F_n/F$ and a division point $y\in P_1(\mathfrak m_{F_n})$ with $[p^n]y=x$. Its coordinates have positive valuation because the special division kernel is supported at the identity. Then $\varphi(y)$ divides $q$, and for $\sigma\in G_F$, $$\sigma\varphi(y)-\varphi(y)
      =\varphi(\sigma y-y)=u_n(\sigma y-y).$$ This is the equality of Kummer cocycles giving (PK-FK). Evaluate the formal invariant-differential identity for $\varphi$ on $x$; continuity of $D$ permits differentiation through the convergent series and gives the derivative formula.

**Exit criterion.**

Unlike (PK-KT), this statement uses a *single* point $q$ for every level. Both its Kummer classes and its derivative come from the same formal morphism. This shared construction is necessary for the reconstruction proof.

###### A lossless differential congruence in a fixed lattice

**Source and module.**

`cor:fixed-picard-point-differential-core`; `Kummer/FormalPoints.lean`.

Let the target of the preceding theorem be the usual Jacobian $J$ with its fixed model $\mathcal G_2$. Let $E/F$ be algebraic, contain $\bar K$, and carry an extension of $D$ preserving $\mathcal O_E$. If $u_n\kappa_{S_1,n}(x)=\kappa_{J,n}(z)$ for $z\in J(E)$, then $$\partial_Dz-d\varphi(\partial_Dx)
 \in p^n\operatorname{Lie}(\mathcal G_2)
                       \otimes_R\mathcal O_E.        \tag{PK-DC}$$

Set $q=\varphi(x)$. Equality of finite Kummer classes and the Kummer exact sequence give $z-q=[p^n]w$ for some $w\in J(E)$. Correct this one point in the same model: $w=w_0+a$ with $w_0\in\mathcal G_2(\mathcal O_E)$ and $a\in J(\bar K)$. In characteristic zero, the derivation vanishes on algebraic constants, so $\partial_Da=0$. Consequently the left side of (PK-DC) is $p^n\partial_Dw_0$. Integral invariant differentials and $D(\mathcal O_E)\subset\mathcal O_E$ put $\partial_Dw_0$ in the displayed integral Lie lattice.

**Exit criterion.**

The exponent is exactly $n$: do not insert an untracked loss $n-c$ depending on the point or auxiliary cover. If denominators are introduced when choosing bases later, record their fixed bound separately from this intrinsic lattice statement.

##### From finite Kummer images to curve points

###### Finite precision of a section trivializes a torsor

**Source and module.**

`lem:divided-torsor-transfer`; `Kummer/Approximation.lean`.

Let $F$ have characteristic different from $p$, let $A/F$ be an abelian variety, $T$ an $A$-torsor, and $s:G_F\to\Pi_T$ a section of its geometrically pro-$p$ arithmetic fundamental group. Put $m=p^a$. Suppose $E/F$ is finite with $d=[E:F]\mid m$, and $P\in T(E)$ has point section whose difference from $s|_{G_E}$ is zero in $H^1(E,A[m])$. Then $T(F)\ne\varnothing$.

For $m=1$, the hypotheses already give an $F$-point. Otherwise choose $t_0\in T(F^{\mathrm{sep}})$ and write $c_\sigma=\sigma t_0-t_0$. Choose a finite Galois field containing $t_0$, all $m$-torsion, and the $m$-division points of the finitely many cocycle values determined by the orbit of $t_0$. The actual cover $A_{F'}\to T$, $z\mapsto t_0+[m]z$, is Galois with automorphisms indexed by pairs $(\sigma,b)$ with $mb=c_\sigma$, and product $$(\sigma,b)(\tau,d)=(\sigma\tau,b+\sigma d).$$ Count these automorphisms to verify the Galois assertion. Finite-cover comparison then identifies the pertinent quotient of $\Pi_T$ with the extension of $G_F$ by $A[m]$ consisting of those pairs. Fix the sign convention: the geometric element $(1,b)$ corresponds to $-b$ under the usual Kummer convention.

Write the image of $s$ as $(\sigma,b_\sigma)$. It satisfies $mb_\sigma=c_\sigma$ and $b_{\sigma\tau}=b_\sigma+\sigma b_\tau$. Since $d\mid p^a$ and $\operatorname{char}F\ne p$, $E/F$ is separable. Choose $z$ with $mz=P-t_0$ and let $\beta_\sigma(w)=\sigma w+b_\sigma$. The finite section difference is represented by $\beta_\sigma(z)-z\in A[m]$ on $G_E$. Its class is zero, so changing $z$ by an $m$-torsion point makes $\beta_\sigma(z)=z$ for every $\sigma\in G_E$. Then $$v=\sum_{\tau\in G_F/G_E}\beta_\tau(z)$$ is independent of coset representatives. Permuting cosets under $\sigma$ yields $\sigma v+d b_\sigma=v$. The point $t_0+(m/d)v$ is consequently fixed by $G_F$, because its change is $c_\sigma-mb_\sigma=0$. It descends to the required point of $T(F)$.

**Exit criterion.**

Formalize the pair extension and section-difference convention before the averaging calculation. This proof does not assume an actual global point of $T$ to define its fundamental group. The finite division cover supplies the extension intrinsically.

###### A degree-one Picard point yields a curve point over a pro-$p$ field

**Source and module.**

`lem:twisted-trace-picard`; `Kummer/Approximation.lean`.

Let $F$ have characteristic zero and pro-$p$ absolute Galois group. Let $C/F$ be smooth, proper, and geometrically connected of genus $g$. If $\operatorname{Pic}_C^1(F)\ne\varnothing$ and either $p$ or $g$ is odd, then every complement of a finite closed subscheme $B\subset C$ has an $F$-point.

Replace $B$ by its reduction. Choose $m>2g-2+\deg B$ with $p\nmid m(m+1-g)$. Only residues $0$ and $g-1$ are forbidden; if $p=2$, oddness of $g$ makes them the same residue. Over a finite Galois $F'/F$, represent the degree-one Picard point by a line bundle $M$ and choose isomorphisms with its conjugates. Their composition defect is a scalar cocycle $c_{\sigma,\tau}\in(F')^\times$. Riemann–Roch and duality (`0BS2`, `0BS6`) give $$V=H^0(C_{F'},M^{\otimes m}),\qquad
 h=\dim V=m+1-g>0.$$ The degree bound gives surjectivity of evaluation on $B$; choose $s\in V$ nonzero at each point of $B$, or simply nonzero if $B$ is empty. Choose a basis $d$ of $\det V$ and form $w=s^{\otimes h}\otimes d^{-1}$. The defects of $M^{\otimes mh}$ and $\det V$ are both $c_{\sigma,\tau}^{mh}$, so they cancel on $M^{\otimes mh}\otimes(\det V)^{-1}$. This line bundle has a true semilinear action.

For $a\in F'$, the twisted trace $$R_a(w)=\sum_{\sigma\in\operatorname{Gal}(F'/F)}
                     \sigma(a)\sigma(w)$$ is an invariant section. At each geometric point of $B$, the identity-term coefficient is nonzero. Linear independence of the embeddings $F'\to\overline F$ (`0CKM`) shows that its vanishing condition is a proper $F$-linear subspace of $F'$. Since $F$ is infinite, avoid the finite union of these subspaces. If $B$ is empty, the same argument at the generic point gives a nonzero trace. Read it as a section of $M^{\otimes mh}$ after the chosen determinant trivialization. Its conjugates differ by nonzero scalars, so its effective zero divisor, including multiplicities, is Galois invariant and avoids $B$.

This divisor has positive degree $mh$ prime to $p$. Every finite orbit of $G_F$ has $p$-power size; if no orbit had size one, the degree would be divisible by $p$. Thus one support point is rational over $F$ and lies outside $B$.

**Exit criterion.**

A point of the Picard *sheaf* need not be a line bundle defined over $F$. Keep the scalar cocycle and determinant cancellation; deleting them would introduce precisely the Brauer-obstruction gap this proof avoids. The parity hypothesis is essential to this argument and is supplied for $p=2$ by the genus calculation of the auxiliary cover below.

###### The algebraic test field has pro-$p$ absolute Galois group

**Source and module.**

`lem:pro-p-algebraic-test-field`; `Fields/Basic.lean`.

Let $F$ be a Hensel mixed-characteristic DVR field and $K\subset F$ any subfield. In a chosen algebraic closure put $L=F^{\mathrm{nr}}\bar K$. This field and every finite extension are Henselian rank-one valued fields, have separably closed residue field, value group $\mathbf Q$ when $v(p)=1$, and pro-$p$ absolute Galois group.

Unramified closure has separably closed residue field, and an algebraic residue extension of it remains separably closed. Algebraicity over $F$ bounds the value group by $\mathbf Q$; the constants contain $p^{1/m}$ for every $m$, giving all of $\mathbf Q$, unchanged by finite extension. For any finite $T/L$ and prime $\ell\ne p$, divide the valuation of an element by $\ell$ using the value group, then take an $\ell$th root of its unit residue by Hensel lifting. Thus $T^\times$ is $\ell$-divisible. The roots of unity $\mu_\ell$ lie in $\bar K$, so Kummer theory rules out cyclic degree-$\ell$ extensions of every such $T$. If a finite Galois quotient had order divisible by $\ell$, a subgroup of order $\ell$ and its fixed intermediate field would give just such a cyclic extension. Hence every finite Galois quotient is a $p$-group.

**Exit criterion.**

Do not describe $L$ itself as a complete DVR: it is generally neither complete nor discretely valued. The Kummer lifting arguments use its Henselian valuation ring and separably closed residue, which are the correct weaker properties.

###### Point approximation from finite Kummer image transfer

**Source and module.**

`lem:proper-source-point-approximation-core`; `Kummer/Approximation.lean`.

**Statement.**

Let $K$ have characteristic zero; let $X/K$ be a smooth proper geometrically connected curve or $\mathbf G_m$; let $Y/K$ be a proper hyperbolic curve; and let $\theta:\Pi_X\to\Pi_Y$ be continuous over $G_K$. Let $L/K$ contain the fixed $\bar K$ and have pro-$p$ absolute Galois group. For every abelian geometric $\Delta_Y^{\mathrm{ab}}/p^a$-cover $V\to Y$ with $a\ge2$, each geometric connected component $U$ of its actual $\theta$-pullback is defined after finite constants. Let $u:T_pS_U\to T_pJ_V$ be the induced actual map, with $S_U=J_U$ or $\mathbf G_m$ as appropriate. Assume that for every finite $T/L$ and $z\in U(T)$, there is some $m\ge1$ with $[T:L]\mid p^m$ such that $$u_m\kappa_{S_U,m}(\alpha_U(z))
       \in\operatorname{im}\kappa_{J_V,m}.           \tag{PK-PI}$$ Then for every $x\in X(L)$ and $n\ge1$ there is $y\in Y(L)$ with $$s_y^{\mathrm{ab}}-(\theta_Ls_x)^{\mathrm{ab}}
 \in p^n\operatorname{Hom}_{\mathrm{cont}}(G_L,T_pJ_Y).
                                                        \tag{PK-PA}$$ Neither valuation nor completeness of $L$ is part of this abstract theorem. The local pipeline proves its hypothesis (PK-PI) when it is later applied to the test fields.

**Proof to implement.**

Choose $a\ge\max(n,2)$, put $Q_a=\Delta_Y^{\mathrm{ab}}/p^a$, and let $s=\theta_Ls_x$. A constant base point and $L\supset\bar K$ split the quotient as $\Pi_{Y_L}/H_Y=Q_a\times G_L$, where $H_Y=\ker(\Delta_Y\to Q_a)$. Write $s(g)=(\rho_a(g),g)$. The finite quotient $(q,g)\mapsto q-\rho_a(g)$ defines a twisted torsor $Y_a^s\to Y_L$. Surjectivity from the geometric group proves its geometric connectedness; the relative pro-$p$ cover exactness theorem lifts $s$ to its arithmetic fundamental group. The actual degree-one Abel–Jacobi map to $\operatorname{Pic}_{Y_a^s}^1$ pushes this lifted section to a section $\widetilde s$ of that Jacobian torsor.

Let $T/L$ be the finite extension fixed by $\ker\rho_a$. Its degree is a $p$-power. Over $T$, the twist is the constant geometric cover $V_T$. The zero point in the fibre of the pulled-back torsor above $x$ is fixed by $G_T$, so $x$ lifts to $z\in U(T)$ in one geometric connected component. All cover, component, and base-point data descend together to a finite constant extension $K_1/K$; since $T$ contains $\bar K$, these objects and $z$ remain defined over $T$. The classification of $\mathbf G_m$ covers ensures that $U$ is again a proper curve or $\mathbf G_m$. The actual covering fundamental groups provide $u$ and identify the lifted section with the image of $s_z$.

Choose $v_0\in V(\bar K)$ and $\tau_0=[v_0]\in\operatorname{Pic}_{Y_a^s}^1(T)$. In a base-point presentation of the arithmetic map, $(d,g)\mapsto(h(d)\epsilon(g),g)$, its constant cocycle restricts trivially on $G_T$ because the map $G_T\to G_{K_1}$ is trivial. The finite Abel–Jacobi comparison, or the usual multiplicative Kummer formula, therefore identifies the difference of $\widetilde s|_{G_T}$ and $s_{\tau_0}$ modulo $p^m$ with $u_m\kappa_{S_U,m}(\alpha_U(z))$. Choose the level supplied by (PK-PI), and choose $Q\in J_V(T)$ realizing that class. The point $\tau_0+Q$ has section equal to $\widetilde s|_{G_T}$ at that finite precision. The divided-torsor transfer theorem, with $[T:L]\mid p^m$, yields $\operatorname{Pic}_{Y_a^s}^1(L)\ne\varnothing$.

The cover has degree $p^{2g(Y)a}$. Riemann–Hurwitz for this finite etale cover gives $$g(Y_a^s)-1=p^{2g(Y)a}(g(Y)-1).$$ If $p=2$, its genus is odd. Thus the determinant-point theorem gives a point of $Y_a^s(L)$ for every $p$. Its image $y\in Y(L)$ has section difference zero modulo $p^a$ by the definition of the twisted torsor. The action of $G_L$ on $T_pJ_Y$ is trivial because the torsion is defined over $\bar K$. Hence the difference is a continuous homomorphism with values in $p^aT_pJ_Y$; divide by $p^a$ using the homeomorphism onto this submodule. It lies in $p^a\operatorname{Hom}_{\mathrm{cont}}$, and therefore in the subgroup in (PK-PA).

**Exit criterion.**

The theorem must quantify over all auxiliary covers and their actual pullback components. Proving Kummer transfer only for the original $X$ and $Y$ is insufficient. Record separately the finite constant descent of each component and the base-point cocycle restriction. The proof constructs a new $y$ at each precision, and makes no assertion that these points form a coherent sequence or converge in $Y(L)$.

###### Discharging the approximation hypothesis for every auxiliary cover

**Proposed integration module.**

`Reconstruction/CurveMap.lean`.

This adapter is implicit in the manuscript but should be a separate Lean theorem because it closes an important quantifier gap. Start with the fixed valued realization $K\subset M^{\mathrm{tame}}\subset\Omega$. Choose the finite local coefficient field for the original pair and the corresponding Gauss completion $F$; put $L=F^{\mathrm{nr}}\Omega$. The original $K$ need not be contained in $F$. It is contained in $\Omega\subset L$, which is the field needed for base change of the original curves.

Now fix one of the auxiliary covers $U,V$, its finite constant definition field $K_1/K$ inside $\Omega$, the induced equivariant map $u$, a finite extension $T/L$, and $z\in U(T)$. The finite-local descent theorem, including its finite-$K_1$ version, puts these group models and $u$ over a finite extension $M_{\mathrm{aux}}/M$ in $\Omega$; enlarge it for the fixed Picard models. Take the compositum $F_{\mathrm{aux}}=F M_{\mathrm{aux}}\subset T$. It is finite over the complete discretely valued $F$, hence is again complete discretely valued. The single chosen valuation on the ambient algebraic closure makes its integer ring dominate the model ring. The extension $T/F_{\mathrm{aux}}$ is algebraic, contains $\Omega$, and has separably closed residue field by the test-field theorem. Thus finite Kummer image transfer applies to this exact $T$ and to $\alpha_U(z)$ at every level $m$. Since $[T:L]$ is a $p$-power, choose any sufficiently large $m$ to make $[T:L]\mid p^m$. This proves (PK-PI).

There is no need for a single finite local field containing the data of all auxiliary covers at once. The quantified proof chooses its finite coefficient field separately for each cover, while the ambient $\Omega$, the field $L$, and the valued comparison remain fixed. The same distinction prevents one from accidentally strengthening the hypothesis to a complete-DVR coefficient field and losing the $p$-subtame case.

##### Review gates for this pipeline

The manuscript provides a detailed proof route for these results. The review of this range found no decisive counterexample to the finite-local descent, determinant-point, or divided-torsor arguments. This is not a certification of the entire manuscript or of any Lean implementation. The following gates remain mathematical or representation-level proof obligations until implemented and checked.

1.  The node calculation must descend from completed local coordinates to the actual chosen etale chart with all divisor multiplicities and branch reductions proved.

2.  The degree-zero relative Picard subfunctor must be identified with the specific NYLL algebraic-equivalence cut as a sheaf, and the actual Abel–Jacobi and universal line bundle must be transported through that identification.

3.  Finite-character and cardinality results do not alone prove naturality. The finite torsion, Kummer, norm, base change, and section-difference diagrams must be established for the same actual maps.

4.  Integral formal realization remains conditional on the separately proved formal Tate-extension theorem. It may not be replaced by an axiom or a structure field with that conclusion.

5.  The $p$-subtame finite-local descent theorem must precede local model construction for an arbitrary $G_K$-equivariant map; the mod-$p$ saturation argument includes $p=2$.

6.  The two point-existence mechanisms have different quantifiers: (PK-KT) gives independent points $Q_n$, whereas (PK-FK) gives one formal point for all $n$. The later derivative congruence uses the latter, and auxiliary cover trivialization uses only the former.

7.  The terminal point-approximation result must be used with Kummer transfer proved for every relevant cover. Its parity repair at $p=2$ comes from the explicit genus formula, not from an assumption that $p$ is odd.


### P04 Reconstruction from differentials

#### Recovering a curve map from finitely many values and one derivation

This stage is algebraic once the preceding Picard and Kummer work has supplied one differential map and arbitrarily accurate point approximations. It is useful to implement it independently of $p$-adic fields. The input is a valued extension with a bounded derivation; the output is an actual rational point of a curve over its source function field. No convergence of the points themselves is required.

##### Canonical ratios and their first derivatives generate an affine chart

**Source.**

`lem:canonical-first-jet`.

**Module.**

`Curves/Basic.lean`.

Let $C/k$ be a proper hyperbolic curve in characteristic zero and choose a basis $\omega_0,\ldots,\omega_{g-1}$ of $H^0(C,\omega_C)$. Put $$U=\{\omega_0\ne0\},\quad A=\mathcal O(U),\quad
 r_i=\omega_i/\omega_0,\quad db=(\delta b)\omega_0,\quad
 h_i=\delta r_i,\quad B=k[r_i]_i.$$ The canonical morphism is finite onto its image and has degree one or two. In degree one it is a closed immersion. In degree two its image is a smooth genus-zero curve, and the hyperelliptic involution is central and acts by $-1$ on all regular differentials. The precise algebra needed downstream is $$A=B+\sum_iBh_i=k[r_i,h_i]_i,
             \qquad k(C)=k(r_i,h_j)_i
 \label{plan-canonical-generators}$$ for any nonconstant $r_j$ in the second equality. In particular $U$ is affine and $A$ is finite over $B$.

**Proof dossier: the canonical morphism.**

Work first over an algebraic closure. A degree-one linear series on $C$ would give a degree-one map to $\mathbf P^1$, contradicting $g\ge2$. Riemann–Roch therefore shows the canonical linear system has no base point. The canonical morphism is nonconstant and finite onto its image (Tag [`0CCL`](https://stacks.math.columbia.edu/tag/0CCL)). Let $D$ be the normalization of that image, $\mathcal L$ the pulled-back hyperplane bundle, and $d=[k(C):k(D)]$. Then $$\omega_C=q^*\mathcal L,\quad h^0(D,\mathcal L)\ge g,\quad
                  2g-2=d\deg\mathcal L.$$ Removing points one at a time proves $h^0(\mathcal L)\le\deg\mathcal L+1$. Hence $d\le2$. If $d=2$, equality gives a degree-one bundle with at least two sections after removing $g-2$ points, so $D\simeq\mathbf P^1$ over the algebraic closure. The complete linear system of $\mathcal L$ embeds $D$ into the canonical image (Tag [`0C6T`](https://stacks.math.columbia.edu/tag/0C6T)).

The involution of the quadratic function-field extension fixes exactly the canonical-ratio subfield. Its invariant rational differentials descend to $D$. For a rational differential $\eta$ on $D$, the local formula $\operatorname{ord}_P(q^*\eta)=e_P\operatorname{ord}_{q(P)}\eta+e_P-1$ shows that regularity of the pullback implies regularity of $\eta$. There are no regular differentials on $D$, so the involution acts as $-1$. Every automorphism preserves the subfield generated by the canonical ratios; uniqueness of the nonidentity automorphism of a quadratic extension implies centrality.

If a length-two subscheme $Z$ had $h^0(\mathcal O_C(Z))>1$, it would give a degree-two map to $\mathbf P^1$. Its involution would act as $-1$ on all regular differentials, forcing the canonical morphism to have degree two. Thus, in degree one, Riemann–Roch gives $h^0(\omega_C(-Z))=g-2$ for all length-two $Z$. The complete linear system separates these subschemes, so it is a closed immersion by Tag [`0E8T`](https://stacks.math.columbia.edu/tag/0E8T). Descend these geometric conclusions by faithful flatness. Over $k$ the degree-two canonical image need only be a smooth genus-zero curve, not a chosen copy of $\mathbf P^1_k$.

**Proof dossier: integral affine generators.**

The inverse image of the canonical affine chart is $U$, so it is affine and $A$ is finite over $B$. In degree one, $A=B$. In degree two, $B$ is the ring of a smooth affine genus-zero curve. The finite torsion-free module $A$ over the regular one-dimensional ring $B$ is locally free of rank two. Since $2$ is invertible, decompose $A=B\oplus M$ into invariant and anti-invariant summands; $M$ is invertible. Locally write $M=Bz$ and $A=B[z]/(z^2-a)$. Then $$\Omega^1_{A/k}=
 (A\otimes_B\Omega^1_{B/k}\oplus A\,dz)/(2z\,dz-da).$$ Taking the invariant part is exact because the projector $(1+\iota)/2$ exists. Its presentation is $(\Omega^1_{B/k}\oplus Bz\,dz)/B(2z\,dz-da)$, which identifies with $\Omega^1_{B/k}$. On the other hand, $\Omega^1_{A/k}=A\omega_0$ and $\omega_0$ is anti-invariant, so that invariant part is $M\omega_0$. The differentials $dr_i=h_i\omega_0$ generate it because the $r_i$ generate $B$. Hence $M=\sum_iBh_i$, proving <a href="#plan-canonical-generators" data-reference-type="eqref" data-reference="plan-canonical-generators">[plan-canonical-generators]</a>. For nonconstant $r_j$, characteristic zero gives $h_j\ne0$. In degree two the involution changes its sign, so it is outside $k(r_i)_i$ and generates the quadratic extension.

**Implementation obligations.**

Separate Riemann–Roch and differential sheaf adapters, the length-two separation criterion, finite flatness over a regular curve, and the quadratic Kahler-differential calculation. The Stacks declarations for Tag [`0BS6`](https://stacks.math.columbia.edu/tag/0BS6) are applied to a genuine rank-one locally free sheaf on a proper Gorenstein pure-dimensional curve; smoothness and Tag [`0BS2`](https://stacks.math.columbia.edu/tag/0BS2)(6) identify the dualizing sheaf with $\Omega^1_{C/k}$. The exit theorem must generate the coordinate *ring* $A$, not just its fraction field. The derivative generators are essential in the hyperelliptic case; canonical ratios alone do not recover $C$.

##### Approximating a finite generating set gives an exact algebra map

**Source.**

`lem:finite-values-algebra-map`.

**Module.**

`Reconstruction/FiniteValues.lean`.

Let $k\subset E\subset L$ be fields, let $v$ be a real-valued nonarchimedean valuation on $L$ with $v(0)=+\infty$, and let $B=k[b_1,\ldots,b_m]$. Fix $z_i\in E$. Suppose that for each positive integer $N$ there is a $k$-algebra homomorphism $\varphi_N:B\to L$ with $v(\varphi_N(b_i)-z_i)\ge N$ for every $i$. Then there is a unique $k$-algebra map $\psi:B\to E$ carrying $b_i$ to $z_i$, and $v(\varphi_N(b)-\psi(b))\to+\infty$ for every $b\in B$.

For each polynomial $P$, use the identity $$P(x)-P(z)=\sum_i(x_i-z_i)Q_i(x,z).$$ The valuations of the finitely many coordinates $x_i=\varphi_N(b_i)$ are eventually bounded below, so those of $Q_i(x,z)$ have an $N$-independent lower bound. Thus $P(x)$ tends to $P(z)$ in valuation. If $P(b)=0$, then $P(x)=0$ for every $N$, whence $P(z)=0$ by separatedness. Factor polynomial evaluation through the presentation of $B$. The same estimate gives convergence on every element, and generation gives uniqueness. In Lean, formulate the estimate as an eventual lower bound and separate the finite initial values of $N$. No completeness of $E$ or $L$ is used.

##### Reconstruction using one bounded derivation

**Source.**

`prop:proper-finite-precision-reconstruction-core`.

**Module.**

`Reconstruction/FiniteValues.lean`.

Assume $E/k$ is finitely generated of transcendence degree one in characteristic zero and $D:L\to L$ is a derivation such that $$D(k)=0,\quad D(E)\subset E,\quad D|_E\ne0,\quad v(Db)\ge v(b).$$ For a proper hyperbolic $C/k$, let $a:H^0(C,\omega_C)\to\Omega^1_{E/k}$ be nonzero and $k$-linear. For one fixed basis $\omega_i$, suppose that every $N$ admits $y_N\in C(L)$ with $$v\bigl(\langle y_N^*\omega_i,D\rangle-
                  \langle a(\omega_i),D\rangle\bigr)\ge N
                    \quad\text{for all }i.$$ The output is a unique nonconstant point $q\in C(E)$ satisfying $q^*=a$. In particular $a$ is injective as a $k$-linear map.

Since $\dim_E\Omega^1_{E/k}=1$ and $D|_E\ne0$, evaluation on $D$ identifies $\Omega^1_{E/k}$ with $E$. Set $A_i=\langle a(\omega_i),D\rangle$ and reorder the basis so that $A_0\ne0$. For sufficiently large $N$, $\beta_{0,N}=\langle y_N^*\omega_0,D\rangle\ne0$, hence $y_N$ lies in the affine chart $U$ above. Its evaluation map satisfies $$\varphi_N(r_i)=\frac{\beta_{i,N}}{\beta_{0,N}},\qquad
 \varphi_N(h_i)=\frac{D\varphi_N(r_i)}{\beta_{0,N}}.$$ The valuations of the denominators eventually equal $v(A_0)$. Boundedness of $D$ preserves errors tending to infinite valuation. Consequently $$\varphi_N(r_i)\longrightarrow R_i=A_i/A_0,\qquad
 \varphi_N(h_i)\longrightarrow H_i=D(R_i)/A_0.$$ For each desired precision choose a sufficiently large source precision, simultaneously for this finite set of generators. The finite-values lemma produces $\psi:A\to E$ and a point $q\in U(E)$.

To prove the equality on all differentials, do not stop at the ratios. Write the generators $r_i,h_i$ as $b_j$ and express $\omega_i|_U=\sum_jc_{ij}\,db_j$ with $c_{ij}\in A$. Polynomial convergence gives $\varphi_N(c_{ij})\to\psi(c_{ij})$; the derivative estimate gives $D\varphi_N(b_j)\to D\psi(b_j)$. Therefore $$\langle q^*\omega_i,D\rangle
  =\sum_j\psi(c_{ij})D\psi(b_j)
  =\lim_N\sum_j\varphi_N(c_{ij})D\varphi_N(b_j)=A_i.$$ Evaluation on $D$ is injective, so $q^*=a$. The value $A_0\ne0$ makes $q$ nonconstant. Separability of the resulting function-field embedding proves injectivity on differentials. Any other solution sends all $r_i,h_i$ to $R_i,H_i$, so the coordinate-ring presentation proves uniqueness.

**Exit criterion.**

The theorem accepts independently chosen $y_N$. It does not ask for a compatible inverse system of points, a convergent subsequence, a chosen analytic limit, or completeness. Every change of precision caused by division by $A_0$ is accounted for by an explicit eventual bound. This is the precise interface at which finite-level Kummer approximations become a single algebraic map.

##### Differentials distinguish dominant rational maps

**Source.**

`lem:proper-differential-faithfulness-core`.

**Module.**

`Curves/Basic.lean`.

For an integral characteristic-zero $k$-scheme $X$ and a proper hyperbolic $Y/k$, two dominant rational maps $f,g:X\dashrightarrow Y$ with the same pullback on regular differentials are equal. Set $E=k(X)$ and choose a target basis with common nonzero pullback $\alpha=f^*\omega_0=g^*\omega_0$. Then $f^*r_i=g^*r_i=R_i$. The identity $$(f^*h_i)\alpha=dR_i=(g^*h_i)\alpha$$ and nonvanishing of $\alpha$ show equality on $h_i$ as well. The affine generator theorem gives equality of rational maps. This proof works in arbitrary source dimension; it does not require a one-dimensional space of source differentials. Keep it separate from the bounded-derivation theorem.

##### From finite local models to a geometric curve morphism

**Source.**

`prop:proper-curve-reconstruction-core`.

**Module.**

`Reconstruction/CurveMap.lean`.

Fix a presentation $K\hookrightarrow M^{\mathrm{tame}}\subset\Omega=\overline M$. Let $X/K$ be a smooth proper geometrically connected curve or $\mathbf G_m$, let $Y/K$ be proper hyperbolic, and let $\theta:\Pi_X\to\Pi_Y$ be continuous over $G_K$. Its abelianization gives $u:T_pS_X\to T_pJ_Y$, where $S_X=J_X$ or $\mathbf G_m$. Define $$a_\theta=\alpha_X^*\lambda_u^*:
 H^0(Y_\Omega,\omega_{Y_\Omega})\longrightarrow
 H^0(X_\Omega,\omega_{X_\Omega}).$$ If $a_\theta\ne0$, construct the unique nonconstant $\Omega$-morphism $f_\Omega:X_\Omega\to Y_\Omega$ with $f_\Omega^*=a_\theta$. Do not assume openness of $\theta$ in this theorem.

**Detailed assembly.**

1.  Descend the curves, base points, Abel–Jacobi maps, and the given Tate homomorphism to one finite local extension $M_0/M$. The finite-local Tate descent proves equivariance after adjoining only mod-$p$ torsion. One does not require $K\subset M_0$.

2.  Enlarge $M_0$ finitely to obtain the fixed Picard models and their affine etale charts. Construct the unique integral formal morphism $\varphi=F_u$ and its differential $\lambda_{u,0}$.

3.  Use the generic Gauss-disc construction at the chosen source point to obtain $E_0=M_0(X_0)\subset F=\widehat{M_0(t)}$ and $x\in X_0(F)$ with $\xi=\alpha_{X_0}(x)$ in the formal unit neighbourhood. Include the finitely many Abel–Jacobi chart coordinates and their denominators in the Gauss scaling choice. Since $\alpha_X(b)=0$, their valuations become positive, proving that $\xi$ is in the required formal neighbourhood. Let $L=F^{\mathrm{nr}}\Omega$. Construct the extension of $D=\partial/\partial t$ and prove $D(\Omega)=0$, $D(E_0)\subset E_0$, $D|_{E_0}\ne0$, and $v(Db)\ge v(b)$ on all of $L$.

4.  Evaluate the same formal morphism once, at $\xi$, to obtain a single $q=\varphi(\xi)$. For every $n$ prove $\kappa_n(q)=u_n\kappa_n(\xi)$ and $\partial_Dq=\lambda_u(\partial_D\xi)$. The all-level Kummer point is fixed; the later approximating curve points may vary independently.

5.  Verify the point-approximation input for every finite extension $T/L$ and every finite geometric $p$-cover. The local model for each finite diagram is defined over some $M_1/M_0$. Since $T$ contains $\Omega$, it already contains $F_1=FM_1$, and $T/F_1$ is algebraic with separably closed residue field. Apply finite Kummer-image transfer inside this same $T$, without enlarging it. For source $\mathbf G_m$, finite geometric $p$-covers remain copies of $\mathbf G_m$ after finite constants.

6.  The test-field theorem gives $G_L$ pro-$p$. The point-approximation theorem supplies $y_n\in Y(L)$ whose Abel–Jacobi Kummer classes agree with those of $q$ modulo $p^n$. Algebraically closed constants in $L$ eliminate the constant base-point corrections.

7.  Pull a dual basis of the integral Picard Lie lattice back to regular differentials on $Y_0$. The lossless differential congruence provides arbitrarily high precision for the whole finite basis at the same $y_n$. Apply the bounded-derivation reconstruction with $M_0\subset E_0\subset L$, giving a nonconstant $f_\eta\in Y_0(E_0)$ and the prescribed pullback.

8.  Extend from the generic point of the smooth curve to the proper target by Tag [`0BXZ`](https://stacks.math.columbia.edu/tag/0BXZ), then base change to $\Omega$. Differential faithfulness gives uniqueness.

For a finite diagram of covers, morphisms, and geometric deck transformations, put their algebraic coefficients and Tate maps on one finite extension of $M$. Uniqueness of integral formal realization gives naturality of $\lambda$; differential faithfulness then proves commutation of the reconstructed maps. All deck maps in this step are $\Omega$-linear. No claim is made that every element of $\operatorname{Aut}(\Omega/K)$ preserves the chosen valuation or the auxiliary local field. Descent to $K$ will use the geometric fundamental group, after this reconstruction is complete.


### P05 Arithmetic recovery and general Hom

#### Proper Hom, arithmetic recovery, and descent to the original field

##### Every multiplicative-source homomorphism kills the geometric group

**Source.**

`lem:gm-geometric-zero-proper-core` (alias `lem:gm-full-abelian-zero-core`).

**Module.**

`Hom/ProperCurves.lean`.

For $p$-subtame $K$ and proper hyperbolic $Y/K$, prove that every continuous $G_K$-homomorphism $\beta:\Pi_{\mathbf G_m}\to\Pi_Y$ kills $\Delta_{\mathbf G_m}=\mathbf Z_p(1)$. Openness is not a hypothesis. Let $s(G_K)$ be the image of the section at $1$, and let $z$ be the image of a topological generator of geometric inertia. If $z\ne1$, choose a finite arithmetic quotient detecting it, and let $Q$ be the image of $\Delta_Y$. Let $H$ be the inverse image of the cyclic subgroup generated by $\bar z$. The relation $s(g)zs(g)^{-1}=z^{\chi_p(g)}$ preserves $H$. Consequently the open subgroup $Hs(G_K)$ gives a geometrically connected proper hyperbolic cover $C\to Y$. The relative-cover theorem lifts $\beta$ to $\Pi_C$. The map $$\mathbf Z_p(1)\longrightarrow H^{\mathrm{ab}}=T_pJ_C$$ is nonzero because its cyclic quotient detects $z$.

The multiplicative-source nonvanishing theorem for $\lambda_u$ now gives a nonzero differential map. Geometric curve reconstruction gives a nonconstant $\mathbf G_{m,\Omega}\to C_\Omega$. Properness extends it to $\mathbf P^1_\Omega\to C_\Omega$; separability makes pullback of a nonzero regular differential nonzero, contradicting $H^0(\mathbf P^1_\Omega,\Omega^1)=0$. No descent of this auxiliary map is needed. The crucial strengthening is from vanishing of an abelian image to vanishing of the full geometric image: the cover was chosen to detect any nontrivial $z$ abelianly. Formalize that cover choice explicitly.

##### Killing boundary inertia factors through the proper compactification

**Source.**

`prop:proper-compactification-factorization-core`.

**Module.**

`Hom/ProperCurves.lean`.

Let $U\subset X$ be a dense open in a smooth proper geometrically connected curve over a $p$-subtame field, and let $Y$ be proper hyperbolic. Every $\theta:\Pi_U\to\Pi_Y$ over $G_K$ factors uniquely through $\Pi_X$, with unchanged image. Include the case $U=\operatorname{Spec}K(X)$.

Precompose with $G_{K(X)}$. Inertia at a point of $U$ is already killed. For a boundary point, pass to a finite constant extension making it rational; the extension is etale at this point and preserves its inertia, and the new constant field is still $p$-subtame. The Henselian local field now has residue characteristic zero. Tag [`0BUB`](https://stacks.math.columbia.edu/tag/0BUB), together with a compatible choice of roots of a uniformizer and lifts of the residue automorphisms, gives $\widehat{\mathbf Z}(1)\rtimes G_{K'}$ as its decomposition group. Prove the splitting with the chosen parameter: the exact inertia sequence alone does not supply a canonical splitting. Since the inertia image in $\Pi_Y$ is pro-$p$, this homomorphism factors through $\mathbf Z_p(1)\rtimes G_{K'}=\Pi_{\mathbf G_{m,K'}}$. Multiplicative vanishing kills it.

All closed-point inertia is therefore killed. Tag [`0BTD`](https://stacks.math.columbia.edu/tag/0BTD) identifies its closed normal span with the kernel of $G_{K(X)}\to\pi_1(X)$, giving a factor through $\pi_1(X)$, and the geometric pro-$p$ property further gives a factor through $\Pi_X$. Surjectivity of the generic-point maps (Tag [`0BQM`](https://stacks.math.columbia.edu/tag/0BQM)) proves agreement with the original $\theta$, uniqueness, and equality of images. This argument needs no injectivity of a decomposition group into $\Pi_Y$.

##### Constant-field invariants via a minimal denominator

**Source.**

`lem:constant-coefficient-field-descent`.

**Module.**

`Fields/Basic.lean`.

Let $k$ be perfect, let $\Omega/k$ be algebraically closed, and suppose $B=\Omega\otimes_k F$ is a domain. Prove $$\operatorname{Frac}(B)^{\operatorname{Aut}(\Omega/k)}=F,$$ where the group acts on the first tensor factor. First prove $\Omega^{\operatorname{Aut}(\Omega/k)}=k$. A nontrivial algebraic element has a distinct conjugate because $k$ is perfect; a transcendental element can be moved by extending a transcendence-basis translation. Extend the associated partial field isomorphism to an automorphism of $\Omega$.

For an invariant $b\in\operatorname{Frac}(B)$, choose a nonzero denominator $d=\sum_{i=1}^ra_ie_i$ with $bd\in B$, the $e_i\in F$ linearly independent over $k$, the number of nonzero terms $r$ minimal, and $a_1=1$. For every $\sigma$, the expression $b(\sigma d-d)=\sigma(bd)-bd$ lies in $B$. If $\sigma d-d\ne0$, it would be a denominator with at most $r-1$ terms. Thus $\sigma d=d$. Coefficient independence puts $d$ in $F$ and, by the same argument, puts $bd$ in $F$. Hence $b\in F$. Apply this to $F=k(X)$ for geometrically integral $X$. This proof handles algebraically closed extensions of arbitrary transcendence degree; invariance under only $G_k$ on an algebraic closure is insufficient for the chosen auxiliary $\Omega$.

##### Geometric faithfulness and full arithmetic recovery

**Source.**

`lem:curve-field-descent`.

**Modules.**

`Hom/ArithmeticRecovery.lean`.

For abelian varieties in characteristic zero, a homomorphism $v:A\to B$ is zero if $T_pv=0$ or $dv=0$. Over an algebraic closure let the kernel have dimension $h$ and $M$ connected components. The finite-level Tate identification shows that $T_pv=0$ kills all $A[p^n]$. Torsion counting in the components gives $$p^{2n\dim A}\le M p^{2nh}\quad\text{for every }n.$$ Thus $h=\dim A$ and $v=0$. If $dv=0$, smoothness of characteristic-zero algebraic group kernels (Tag [`047N`](https://stacks.math.columbia.edu/tag/047N)) gives the same dimension equality. Use Tag [`03RP`](https://stacks.math.columbia.edu/tag/03RP)(7) for the torsion counts and prove the compatibility between the actual Jacobian morphism and the Tate morphism.

Consequently two nonconstant curve maps to a proper hyperbolic curve inducing the same Tate map induce the same Jacobian map and the same differential pullback, hence are equal by differential faithfulness. This proves faithfulness of their geometric pro-$p$ outer homomorphisms.

Now let $\theta:\Pi_X\to\Pi_Y$ be open over $G_k$, with $X$ smooth proper, and suppose a nonconstant $f_L:X_L\to Y_L$ induces its geometric outer map. Over an algebraic closure $\Omega$ containing $L$, proper base-change invariance of finite-etale covers (Tag [`0A49`](https://stacks.math.columbia.edu/tag/0A49)) identifies the geometric groups. Arithmetic equivariance of $\theta$ implies that $f_\Omega$ and every $\sigma f_\Omega$ induce the same geometric outer homomorphism. Faithfulness makes them equal. Apply the preceding invariant-field theorem to $f_\Omega^*k(Y)$ to get $k(Y)\hookrightarrow k(X)$. The corresponding rational map extends over the normal proper source curve by Tag [`0BXZ`](https://stacks.math.columbia.edu/tag/0BXZ), and agrees with $f_L$ after base change.

Finally choose one geometric conjugation making the two geometric homomorphisms equal, and let their common image be the open subgroup $H\le\Delta_Y$. For $\gamma\in\Pi_X$, the difference $z=f_*(\gamma)^{-1}\theta(\gamma)\in\Delta_Y$ centralizes $H$. If $z\ne1$, choose open normal $N\triangleleft\Delta_Y$ with $N\subset H$ and $z\notin N$. Let $C\to Y_{\bar k}$ be the corresponding proper hyperbolic cover. Its geometric pro-$p$ group is $N$. The deck transformation given by $z$ acts by conjugation on $N$, hence trivially on $N^{\mathrm{ab}}/p^n\simeq J_C[p^n]$ for all $n$. Tate faithfulness and curve-map faithfulness make that deck transformation the identity, contradicting $z\notin N$. Therefore every such $z$ is $1$. This is the required recovery of the entire arithmetic homomorphism with the *same* geometric conjugator. Do not replace it by a fresh conjugator for each $\gamma$, nor assume slimness as an extra hypothesis.

##### The proper-target curve Hom theorem

**Source.**

`thm:proper-local-curve-hom-core` (alias `lem:subpadic-finite-curve-proper-hom`).

**Module.**

`Hom/ProperCurves.lean`.

First take $X$ proper and reduce open $\theta$ to a surjection. Its Tate abelianization is surjective and $\dim J_Y>0$, so the integral linearization and Abel–Jacobi differential isomorphism give $a_\theta\ne0$. Fix the reconstructed $f_\Omega$ once.

For each open normal $N\triangleleft\Pi_Y$, let $A=\Pi_Y/N$ and let $V\to Y$, $W=\theta^*V\to X$ be the corresponding torsors. They have the same finite Galois constant field $E/K$; viewed over $E$ they are geometrically connected proper curves. Choose an embedding $E\hookrightarrow\Omega$; all expressions $V_\Omega$ and $W_\Omega$ in this comparison are base changes over this chosen $E$, not over $K$. The relative-cover theorem yields a surjection $\theta_V:\Pi_W\to\Pi_V$ and hence a reconstructed $r_V:W_\Omega\to V_\Omega$. Naturality of linearization gives $$(v r_V)^*=a_{\theta_V}v^*=w^*a_\theta=(f_\Omega w)^*.$$ Differential faithfulness implies $v r_V=f_\Omega w$. For each geometric deck element, apply the same reasoning to $a_V^{-1}r_Va_W$ to prove equivariance. An equivariant map between torsors under the same finite group is an isomorphism; prove this on fibres and descend. This identifies the geometric pullback torsors for each $N$.

The subgroups $N\cap\Delta_Y$ are cofinal among open normal geometric subgroups. Apply finite conjugacy inside $\Delta_Y$ to identify the geometric map of $f_\Omega$ with that of $\theta$ using one conjugator. Then the previous descent and arithmetic-recovery theorem gives the required $K$-map and equality of the full arithmetic maps. No coherent family of the $r_V$ was chosen.

For separated open $X$, compactification factorization keeps the image of $\theta$ unchanged and reduces to the proper-source result; properness of $Y$ also extends genuine morphisms across the missing points. For a possibly nonseparated smooth curve, cover by affine opens $U_i$. Normality gives $\Pi_{U_i}\twoheadrightarrow\Pi_X$, so each restriction remains open. The separated theorem applies on each $U_i$, uniqueness gives agreement on overlaps, and the maps glue. The same surjections detect equality of arithmetic maps. Dominance implies open image by the generic-point argument in the next section. These steps prove the full equivalence for all finite-type smooth curve sources, not just proper ones.

#### Uniform curve reduction, normal-source extension, and open targets

##### A regular pencil from two translations

**Source.**

`lem:two-translations-regular-pencil`.

**Module.**

`Fields/Basic.lean`.

If $M/k$ is regular and finitely generated in characteristic zero, $a,b\in M$ are algebraically independent, and $t$ is independent of $M$, prove that $M(t)/k(t,at+b)$ is regular. Put $B_0=k(a,b)$, $k_0=k(t)$, $B=B_0(t)$, and $u=at+b$. The relative algebraic closure $N_0$ of $B_0$ in $M$ is finite (Tag [`037J`](https://stacks.math.columbia.edu/tag/037J)); $M/N_0$ and $M(t)/N_0(t)$ are regular.

If $z\in M(t)$ is algebraic over $k_0(u)$, it lies in $N_0(t)$. Set $L=B(z)$ and choose a primitive element $N_0=B_0(\alpha)$. Let $P$ and $Q$ be the minimal polynomials of $\alpha$ over $B_0$ and $L$. Since $Q$ divides $P$, its coefficients are algebraic over $B_0$; as elements of $N_0(t)$ they lie in $N_0$. If $L_0$ is the field they generate over $B_0$, then $L_0(t)\subset L$ and $$[N_0(t):L_0(t)]\le\deg Q=[N_0(t):L].$$ The reverse inequality follows from the inclusion, so $L=L_0(t)$. Thus translation $\sigma:t\mapsto t+1$, fixing $M$, preserves $L$.

Write $u'=u+a$. Then $u,u'$ are independent over $k_0$ and $B=k_0(u,u')$. The field $A=k_0(u,z)$ is regular over $k_0$, as a subfield of the regular extension $M(t)/k(t)$. Since it is algebraic over $k_0(u)$, $u'$ is transcendental over $A$, and $L=A(u')$ is regular over $k_0(u')$ (Tag [`0G32`](https://stacks.math.columbia.edu/tag/0G32), together with characteristic-zero separability). But $\sigma z\in L$ is algebraic over $k_0(u')$, so $\sigma z\in k_0(u')$ and $z\in k_0(u)$. This proves relative algebraic closedness; characteristic zero supplies separability and hence regularity. Implementation must distinguish the translation of $t$ from fixing $k(t)$ pointwise: $\sigma$ preserves $k(t)$ as a field but acts nontrivially on it.

##### One curve reduction preserves all finite geometric covers

**Source.**

`lem:regular-cover-curve-reduction`.

**Module.**

`Hom/NormalSources.lean`.

For regular finitely generated $F/k$ of transcendence degree $d\ge1$, choose a transcendence basis $x_1,\ldots,x_d$, independent variables $t_i$ for $i<d$, and set $$u_i=x_i+t_ix_d,\quad E=k(t_i,u_i:i<d),\quad
                       \widetilde F=F(t_1,\ldots,t_{d-1}).$$ The inverse coordinate substitution shows that $t_i,u_i,x_d$ are independent, $E/k$ is purely transcendental, and $\widetilde F/E$ has transcendence degree one. Apply the preceding pencil lemma successively. The same construction works after *every* finite constant extension $k'/k$ and *every* finite $M/Fk'$ regular over $k'$. Therefore $$M(\mathbf t)/Ek'\text{ is regular},\qquad
 [M(\mathbf t):\widetilde Fk']=[M:Fk'].$$ Pure transcendental base change preserves the Galois group when the extension is Galois. The variables and intermediate field are chosen once, before any finite cover, which is the essential uniformity assertion.

Each finite geometrically connected cover descends to some finite constant field $k'$. Its function field $M/k'$ is regular. The displayed regularity means the pullback of the cover to the geometric generic point over $E$ remains connected and has the same degree. The finite-cover criterion for surjectivity gives $$\Delta_{\operatorname{Spec}\widetilde F/E}\twoheadrightarrow
                         \Delta_{\operatorname{Spec}F/k}.$$ The construction also proves this for full profinite geometric groups.

If $F=k(X)$ with $X$ normal geometrically integral finite type, choose a nonempty affine $\operatorname{Spec}A\subset X$. A primitive element $\alpha$ for $\widetilde F/E(x_d)$ has separable minimal polynomial $P$. Clear the finitely many denominators in $P$ and in generators of $A$, obtaining $R=E[x_d,1/h]$ with $A\subset R[\alpha]$. Then $$S=R[T,1/P'(T)]/(P(T)),\qquad U=\operatorname{Spec}S$$ is a smooth geometrically integral $E$-curve, by standard-etale presentation (Tag [`00UC`](https://stacks.math.columbia.edu/tag/00UC)), with function field $\widetilde F$ and an actual $k$-map $U\to X$. The same connected-cover argument gives $\Delta_{U/E}\twoheadrightarrow\Delta_{X/k}$. For $d=1$, the tuples are empty and $E=k$; include this case explicitly. Although $U$ is finite type over $E$, it need not be finite type over $k$. The functorial fundamental-group interface must therefore be defined for qcqs schemes and arbitrary scheme maps, allowing this actual $k$-map and generic points; do not demand a finite-type $k$-morphism here.

##### Removing purely transcendental variables from a curve point

**Source.**

`lem:proper-curve-rational-variables`.

**Module.**

`Curves/Basic.lean`.

For a smooth proper geometrically connected curve $C/F$ of positive genus in characteristic zero, prove $C(F(\mathbf t))=C(F)$. A point over $F(t)$ gives a rational map $\mathbf P^1_F\dashrightarrow C$, which extends by Tag [`0BXZ`](https://stacks.math.columbia.edu/tag/0BXZ). If nonconstant, separability makes the pullback of a nonzero regular differential nonzero, contrary to the absence of regular differentials on $\mathbf P^1$. The map is therefore constant; evaluate it at $0\in\mathbf P^1(F)$ to see its value is $F$-rational. Iterate one variable at a time. Include injectivity of the base-change map on points in the exported bijection, rather than writing only a set equality.

##### Extending the generic-point map over a normal source

**Source.**

`lem:normal-cover-extension`.

**Module.**

`Hom/NormalSources.lean`.

Let $X/k$ be normal geometrically integral finite type, $F=k(X)$, and let $C/k$ be smooth proper geometrically connected of genus $g\ge1$. Suppose $q:\operatorname{Spec}F\to C$ induces a geometric abelian homomorphism factoring through $\Delta_F\twoheadrightarrow\Delta_X$. Then $q$ extends uniquely to $X\to C$. Normality alone does not extend an arbitrary rational map from a higher-dimensional source; the abelian-cover factorization is the additional hypothesis that this proof uses.

Take the integral graph closure $\Gamma_0\subset X\times_k C$ and the proper birational projection $\pi:\Gamma_0\to X$. If a geometric fibre has positive dimension, its reduced image as a closed subscheme of $C_\Omega$ is all of $C_\Omega$. Choose an affine $\operatorname{Spec}A\subset\Gamma_0$ meeting its generic point. The integral closure $B$ of $A$ in $F$ is finite over $A$: Noether normalization $R\subset A$, the nondegenerate trace in characteristic zero, and $B\hookrightarrow\operatorname{Hom}_R(A,R)$ give the finiteness (Tags [`00OY`](https://stacks.math.columbia.edu/tag/00OY), [`032L`](https://stacks.math.columbia.edu/tag/032L)). Pull back this finite surjection to the generic point of that geometric fibre, giving a nonzero finite $\Omega(C)$-algebra $T$ of dimension $m$.

Choose $n$ with $p^{2gn}>m$. Descend the finite geometric quotient $Q=\Delta_C^{\mathrm{ab}}/p^n$ to a finite Galois constant extension $k'/k$. It gives a geometrically connected $Q$-cover $V\to C_{k'}$ of degree $p^{2gn}$. The factorization hypothesis ensures that the character of $q^*V$ on $G_{Fk'}$ kills the kernel of $G_{Fk'}\twoheadrightarrow\Pi_{X_{k'}}$. This kernel lies in the geometric group, so the specified geometric factorization suffices. Obtain an actual finite-etale torsor $E\to X_{k'}$.

The normal domain $B_{k'}$ is still a domain by regularity and is normal by finite separable base change. Decompose both pulled-back finite-etale torsors into their connected components. On each component the generic-fibre isomorphism extends uniquely by the normalization description in Tag [`0BQL`](https://stacks.math.columbia.edu/tag/0BQL); matching generic components then gives the full torsor isomorphism over $B_{k'}$. After $k'\hookrightarrow\Omega$, choose a section of the finite etale fibre $E_{\bar x}$ and pull it back to $T$. The isomorphism produces a $T$-point of $V$ over the generic point of $C$, thus a unital injection of fields into the nonzero algebra $\Omega(V_\Omega)\hookrightarrow T$. The vector-space dimension inequality gives $p^{2gn}\le m$, a contradiction. It is enough that $T$ is nonzero; it need not be a field or reduced.

All geometric fibres are zero-dimensional, hence $\pi$ is quasi-finite. Proper plus quasi-finite is finite (Tag [`02LS`](https://stacks.math.columbia.edu/tag/02LS)), and a finite birational map to a normal scheme is an isomorphism (Tag [`0AB1`](https://stacks.math.columbia.edu/tag/0AB1)). Transfer the graph map to $X$. Separatedness of $C$ gives uniqueness. Perform the construction locally on $X$ if a chosen normalization interface requires affine charts; glue by uniqueness. No separatedness of $X$ is needed.

##### Cuspidal inertia and one cover with hyperbolic compactification

**Source.**

`lem:cofinal-proper-covers`.

**Modules.**

`Hom/OpenTargets.lean`.

First prove the exact residue sequence for the *actual* Kummer classes and identify its components with local inertia characters. Tag [`03RR`](https://stacks.math.columbia.edu/tag/03RR) contains the sequence in its proof, but the audited Lean rank declarations do not themselves identify these maps. For $r\ge2$ and $\Lambda=\mathbf Z/p^a\mathbf Z$, the sequence is $$0\to H^1(\bar Y,\mu_{p^a})\to H^1(Y,\mu_{p^a})
 \to\ker(\Lambda^r\xrightarrow{\sum}\Lambda)\to0.$$ Residue $1$ at a chosen cusp and $-1$ at another gives a character detecting order $p^a$ at the chosen inertia, for every $a$. Hence $\mathbf Z_p(1)\to\Delta_Y$ is injective. The coordinate identification with the local Kummer class of a parameter is essential to this inference.

To produce one proper-hyperbolizing cover, let $s=v_p(r-1)$ and choose $a>s$ with $p^a(2g-2+r)>(r-1)+p^s$. A class with residues $(1,\ldots,1,-(r-1))$ gives a connected cyclic cover of degree $p^a$. Its ramification indices are $p^a$ at the first $r-1$ cusps and $p^{a-s}$ at the last. The local differential-degree calculation gives $$2g(\bar V)-2=p^a(2g-2+r)-((r-1)+p^s)>0.$$ If $r=1$, hyperbolicity gives $g\ge1$. A nontrivial degree-$p$ etale cover of $\bar Y$, supplied by its finite $H^1$, has $p$ cusps after restriction; apply the preceding construction and carry inertia injectivity back using the relative-cover theorem. If $r=0$, use $Y$ itself. Take geometric cores, descend the finite quotient after finite constants, and then take the arithmetic core. Hyperbolicity of every resulting proper component is preserved by the differential-degree inequality. Record the single resulting open normal subgroup $N_0\triangleleft\Pi_Y$.

##### Proper-target Hom implies Hom for open targets

**Source.**

`lem:proper-target-hom-reduction-core`.

**Module.**

`Hom/OpenTargets.lean`.

Assume the proper-target full Hom theorem for every connected finite-etale cover $Z\to X$, viewed over its relative constant field. For a surjective $\theta:\Pi_X\to\Pi_Y$, choose the preceding $N_0$ once. For every open normal $N\subset N_0$, let $V\to Y$ and $W=\theta^*V\to X$ have constant field $E$. Proper-target Hom gives a unique dominant $r_V:W\to\bar V$ over $E$. Applying its uniqueness to cover transitions and semilinear arithmetic deck transformations gives commutation and equivariance. Thus $r_{V_0}$ descends to a dominant $\bar f:X\to\bar Y$ and all $r_V$ lie over it.

If $\bar f$ meets the boundary, the pullback of that effective Cartier divisor has a height-one point $x$ (Tag [`00KV`](https://stacks.math.columbia.edu/tag/00KV)); normality makes $\mathcal O_{X,x}$ a DVR (Tag [`00PD`](https://stacks.math.columbia.edu/tag/00PD)). Let $t$ be a parameter at its image cusp, and set $e=\operatorname{ord}_x(\bar f^*t)>0$. The cusp generator $z$ has $z^e\ne1$. Choose one $N\subset N_0$ detecting it. Its order $r$ in the finite quotient does not divide $e$. Normality of $N$ makes all branches above the cusp have this ramification index. At a point $w\in W$ above $x$, etaleness gives ramification index one over $\mathcal O_{X,x}$. If $s$ is a parameter at $r_V(w)$, then locally $t=us^r$ with $u$ a unit. Dominance makes $r_V^*s\ne0$, so $$e=r\operatorname{ord}_w(r_V^*s),$$ a contradiction. Hence $\bar f$ avoids the boundary and defines $f:X\to Y$.

Every $r_V$ now lands in $V$. Equivariance and $E$-linearity identify $W\simeq X\times_YV$ as arithmetic torsors, inducing the identity on the constant quotient. The cofinal family $N\subset N_0$ and the arithmetic torsor-comparison theorem give one geometric conjugator for all of $\Pi_X$. Pull a second candidate back to $W_0$ and use uniqueness for the proper hyperbolic $\bar V_0$ to prove it equals $f$.

**Dominance gives openness.**

Proposed early module: `FundamentalGroup/Basic.lean`. This lemma is scheduled in Stage 1 and does not depend on any Hom theorem; its placement here explains its use in the source’s final argument. For dominant $f:X\to Y$, the relative algebraic closure $M$ of $K(Y)$ in $K(X)$ is finite (Tag [`037J`](https://stacks.math.columbia.edu/tag/037J)). Characteristic zero makes $K(X)/M$ regular. Linear disjointness with every finite separable extension implies that the restriction map from $G_{K(X)}$ has image exactly the open subgroup $G_M\le G_{K(Y)}$. Generic-point surjectivity (Tag [`0BQM`](https://stacks.math.columbia.edu/tag/0BQM)) then shows the induced image in $\Pi_Y$ is open. Prove compactness/closedness of the image before using finite index. This argument applies to arbitrary finite source dimension and is the forward-map theorem for the final equivalence.

##### Final assembly for all normal finite-type sources

**Source.**

`thm:finite-type-hom` and its final proof.

**Modules.**

`Hom/NormalSources.lean`, `Main.lean`.

For a proper hyperbolic target, let $F=K(X)$ and choose the uniform curve reduction $\widetilde F=F(\mathbf t)$, $E$, and $U/E\to X$. The field $E$ is $p$-subtame by closure under finitely generated extensions. Combine the actual group map and the map to $G_E$ to obtain $$\theta_U:\Pi_U\to\Pi_Y\times_{G_K}G_E\simeq\Pi_{Y_E}.$$ Prove this base-change identification from the proper finite-cover equivalence of Tag [`0A49`](https://stacks.math.columbia.edu/tag/0A49) and the arithmetic exact sequences; include the maps to $G_E$. The geometric image is the original geometric image because $\Delta_{U/E}\twoheadrightarrow\Delta_{X/K}$. Thus $\theta_U$ is open. Proper curve Hom produces $q\in Y(\widetilde F)$ realizing it. Removing rational variables puts $q$ in $Y(F)$. The $E$-dominant curve map remains dominant after composition with $Y_E\to Y$; dominance descends through the faithfully flat extension $F\to F(\mathbf t)$. Record this bridge before applying the normal-source extension theorem.

Project the arithmetic equality over $G_{\widetilde F}$ to $\Pi_Y$. Regularity of a pure transcendental extension gives $G_{\widetilde F}\twoheadrightarrow G_F$, so the same conjugator proves full arithmetic equality at the original generic point. In particular the geometric abelianization factors through $\Delta_X$. The normal-source extension theorem gives a dominant $f:X\to Y$, and $G_F\twoheadrightarrow\Pi_X$ detects equality with $\theta$ using that same conjugator. Two candidates restrict to the same map on $U$ by curve Hom uniqueness, hence agree at the generic point and everywhere by target separatedness.

If $\operatorname{trdeg}_K F=0$, geometric integrality implies $F=K$ and $\Delta_X=1$. A proper hyperbolic target has infinite geometric group, as its abelian quotients have orders $p^{2gn}$ with $g\ge2$. Thus no open homomorphism exists, and no dominant morphism to a curve exists. Supply these empty-set equivalences explicitly rather than calling the positive-dimensional construction with an empty transcendence basis.

For a connected finite-etale cover of $X$, prove that normality and integrality persist and its relative constant field is finite separable over $K$. Normality makes those constants regular functions, giving the structural map over that field; characteristic zero and relative algebraic closedness give geometric integrality. Closure of the field class under finite extension therefore makes the proper-target result available for every such cover. Apply the open-target reduction and assemble <a href="#plan-main-equivalence" data-reference-type="eqref" data-reference="plan-main-equivalence">[plan-main-equivalence]</a>. The final theorem is independent of the auxiliary host, its valuation, all finite local models, all chosen precision witnesses, and the chosen proper-hyperbolizing cover, by uniqueness and the specified forward map.


## Frozen sources and existing interfaces

Original source: [mochizuki_hom_simplification.tex](https://chatgpt.com/library?file_id=libfile_eefd1daf97288191833b39e055ea3a89&account_id=personal),
version 78, 197,198 bytes, 3,312 lines. SHA-256:
`a9cd7b75f9174203d40267374f55f62f621a38b3120bc196472caf59d813ff6c`.
The original remains the source of mathematical scope; it is not a compilation
input for maintaining this plan.

| Dependency | Frozen revision |
| --- | --- |
| NYLL manuscript baseline | `21896ca9a10770a5ae31421357b003e76d06c965` |
| NYLL branch inspected in the source audit | `fe40c03df1b2b195053fdd63305571d97c73ce48` |
| Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` |
| Lean | `leanprover/lean4:v4.35.0` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The audit inspected the 18 Lean files explicitly cited by the manuscript.
Source inspection does not certify a combined kernel build. Fixed source
signatures and the conditions needed to use them follow.

### Verified repository inputs and the Stacks-first migration

This appendix records a source-level audit of the repository interfaces cited by the supplied manuscript. Every one of its eighteen explicitly cited Lean files was retrieved and its relevant declarations inspected: seven files belong to NYLL and eleven to AxiomMath/Stacks. The audit checks the actual hypotheses and conclusions and identifies a concrete obstruction to importing the two unmodified developments together. It is not a new kernel verification of either repository, a successful mixed-import build, or a claim that the final $p$-subtame Hom theorem already exists.

The ownership rule is the user’s explicit instruction: *where NYLL and Stacks overlap, adopt Stacks*. Stacks therefore supplies the canonical objects and overlapping theorems. Additional NYLL results are reused after their statements and actual maps have been transported to those objects. A compatibility theorem must identify the original geometric construction; an abstract isomorphism between unnamed objects is insufficient.

#### Frozen revisions and audit status

The manuscript pins NYLL to `21896ca9a10770a5ae31421357b003e76d06c965` and Stacks to `c496df0d9beea9deaeabcea8492605f9a0a2313b`. At the audit on 13 November 2026, Stacks main still had that revision, while NYLL main was `fe40c03df1b2b195053fdd63305571d97c73ce48`. The latter is three commits ahead. The [inspected revision comparison](https://github.com/n-yamaguchi-0729/NYLL/compare/21896ca9a10770a5ae31421357b003e76d06c965...fe40c03df1b2b195053fdd63305571d97c73ce48) contains no change to any NYLL file explicitly cited by the manuscript. Its only mathematical source change is `Nyll/AbelianVarieties/Reduction/GoodModelPointComparison.lean`; the remaining changes concern verification and publication tooling.

Both actual toolchain files specify `leanprover/lean4:v4.35.0`. Both [NYLL’s manifest](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/lake-manifest.json) and [Stacks’ manifest](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/lake-manifest.json) resolve Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`. The older Lean version mentioned in the Stacks README is not the operative toolchain. The implementation must retain exact revisions in its own lockfile, including the revision of the compatibility changes.

Matching toolchains establish only a necessary compatibility condition. They neither remove duplicate declarations nor identify different site presentations. All interfaces below are *inspected source statements*. Compilation of their selected mixed dependency closure remains a separate Stage 0 acceptance condition.

#### A concrete obstruction and its Stacks-first repair

##### Duplicate global declarations

The NYLL file [`Nyll/SchemeTheory/Pi1/FiniteEtale/Basic.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/SchemeTheory/Pi1/FiniteEtale/Basic.lean) defines `RingHom.FiniteEtale` through `Algebra.FiniteEtale`. It also defines `RingHom.FiniteEtale.respectsIso`, `RingHom.FiniteEtale.hasFiniteProducts`, `RingHom.FiniteEtale.hasEqualizers`, `RingHom.FiniteEtale.hasStableEqualizers`, and `RingHom.FiniteEtale.isStableUnderBaseChange`.

Independently, [`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleColimits/EqualizerAlgebra.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleColimits/EqualizerAlgebra.lean) defines the same global predicate as $$\operatorname{RingHom.Finite}(f)\ \wedge\
  \operatorname{RingHom.Etale}(f)$$ and declares the same isomorphism, finite-product and equalizer lemmas. The file [`StacksFrontier/AlgebraicGeometry/FiniteEtaleColimits/EqualizerBaseChange.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/FiniteEtaleColimits/EqualizerBaseChange.lean) declares the same stable-equalizer and base-change results, together with `RingHom.FiniteEtale.isStableUnderCobaseChange`.

These are duplicate public constants, not competing notation. A wrapper module, a different import order or a local namespace cannot resolve them. The selected arithmetic exact-sequence input actually reaches the duplicate Stacks definition. Its inspected import chain, with common prefix `StacksFrontier/AlgebraicGeometry/`, is:

1.  `FundamentalGroup/GeometricArithmeticExactSequence.lean`;

2.  `FundamentalGroup/FundamentalGroupOfLimit.lean`;

3.  `FundamentalGroup/EtaleFundamental/GaloisCategoryAxioms.lean`;

4.  `FiniteEtaleColimits/Basic.lean`;

5.  `QuasicoherentAlgebraEqualizer.lean`;

6.  `FundamentalGroup/FiniteEtaleColimits/EqualizerAlgebra.lean`.

The obstruction therefore concerns required inputs, not merely an optional aggregate import.

##### The first required compatibility change

Keep the Stacks definitions and proofs canonical. In an isolated adaptation of the necessary NYLL dependency closure, remove the duplicated NYLL declarations and import their Stacks owners. Retain genuinely additional NYLL lemmas, proving their compatibility statements against the canonical predicate. This plan does not silently modify public NYLL; the adaptation must preserve source attribution and record each changed dependency.

The elementary transport proof is explicit. For $f:R\to S$, install the induced algebra structure. By `Algebra.finiteEtale_iff`, the NYLL class is equivalent to $$\operatorname{Algebra.Etale}(R,S)\ \wedge\
  \operatorname{Module.Finite}(R,S).$$ The algebra-map comparison lemmas identify these factors with the etale and finite properties of $f$. Interchanging the factors gives the Stacks predicate. Conversely, its conjuncts install the two Mathlib instances and construct the legacy class. No new geometric hypothesis is introduced.

There is a universe issue: NYLL’s original predicate permits two ring universes, whereas the inspected Stacks predicate uses one. The present scheme applications can use a common universe. A genuinely heterogeneous auxiliary lemma requires a proved universe-lift transport or a reviewed generalization of the Stacks interface; it cannot be advertised as an unchanged generic NYLL theorem.

This is the smallest *verified starting repair*, not an exhaustive collision inventory. Stage 0 must enumerate public declaration owners throughout the selected closure and resolve further overlap in favour of Stacks. The gate is a successful mixed-import build with one owner for each shared constant and no competing global instance.

##### Canonical geometric objects and actual-map comparison

The exported cover category is Stacks’ `AlgebraicGeometry.FiniteEtaleOver`; the exported fundamental group is `AlgebraicGeometry.EtaleFundamentalGroup`. Compare the legacy presentations over the category of actual finite etale maps $Y\to X$ and commutative triangles over $X$. The comparison retains the underlying scheme, map and lift $\operatorname{Spec}\Omega\to Y$.

NYLL’s fibre functor is `FintypeCat`-valued, while Stacks’ is type-valued; include the forgetful functor explicitly. Conjugation by the natural fibre identification yields the group comparison. It is continuous in both directions because the topologies are generated by stabilizers of finitely many fibre points. Pullback compatibility follows from the universal property of the actual fibre product.

The adapter must additionally preserve arithmetic projections, basepoints, coefficient reductions, torsor characters and multiplication-cover monodromy. It cannot replace a scheme-induced homomorphism by an arbitrary abstractly isomorphic map.

#### The seven inspected NYLL files

All links here are pinned to the audited NYLL revision. These files are unchanged from the manuscript pin. Their additional results are to be transported; their overlapping underlying objects do not override Stacks.

##### N1: connected covers and labelled finite quotients

The file [`Nyll/EtaleFundamentalGroups/GaloisCovers/OpenSubgroupFundamentalGroup.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/EtaleFundamentalGroups/GaloisCovers/OpenSubgroupFundamentalGroup.lean) contains `AlgebraicGeometry.FiniteEtale.exists_connectedCover_lift_fundamentalGroup_equiv_openSubgroup`. For a connected scheme $S$, a separably closed geometric point $\xi$, and an open subgroup $U$ of the actual fundamental group, it supplies a connected finite etale cover $A\to S$, a lifted point $\xi'$, the equality $\xi'\gg A.\mathrm{hom}=\xi$, and a topological group equivalence $\pi_1(A,\xi')\simeq U$. Its inclusion into $\pi_1(S,\xi)$ equals the actual cover-induced map. The transported theorem must retain that formula.

The file [`Nyll/EtaleFundamentalGroups/GaloisCovers/FiniteQuotientRealization.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/EtaleFundamentalGroups/GaloisCovers/FiniteQuotientRealization.lean) contains `AlgebraicGeometry.FiniteEtale.exists_galoisCover_quotient_mulEquiv`. A continuous surjection $\phi$ to a finite discrete group $G$ gives a Galois cover $W$, a fibre point $w$, and $$e:(\operatorname{Aut}W)^{\mathrm{op}}\simeq G,
 \qquad e\circ q_{W,w}=\phi.$$ Realizing only $\ker\phi$ is too weak for the labelled-cover comparison. Keep the opposite-group convention and make any conversion to a left action explicit.

##### N2: finite cohomology and characters

The file [`Nyll/EtaleFundamentalGroups/Cohomology/FiniteH1Comparison.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/EtaleFundamentalGroups/Cohomology/FiniteH1Comparison.lean) contains, in `EtaleFundamentalGroups.Cohomology`, `finiteH1CharacterEquiv`, `finiteH1CharacterEquiv_apply`, and `finiteH1CharacterEquiv_naturality`. For a finite constant abelian group $A$, these give $$H^1_{\mathrm{et}}(X,A)\simeq
 \operatorname{Hom}_{\mathrm{cont}}(\pi_1(X,\xi),A),$$ identify this equivalence with the original torsor character, and prove naturality under coefficient homomorphisms. The source is actual small-etale derived cohomology. In particular, coefficient reductions $\mathbf Z/p^{n+1}\to\mathbf Z/p^n$ are covered.

Scheme-pullback naturality is a separate interface obligation; the cited naturality theorem alone does not state it. The file also supplies `finiteH1AbelianCharacterEquiv` through the actual topological abelianization. No additional $K(\pi,1)$ hypothesis is needed for these degree-one comparisons.

##### N3: actual Abel–Jacobi pullback

The file [`Nyll/JacobianVarieties/Kummer/AbelJacobiFiniteH1.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/JacobianVarieties/Kummer/AbelJacobiFiniteH1.lean) contains `JacobianVarieties.Kummer.abelJacobi_finiteH1Pullback_bijective`. It assumes an algebraically closed field, a function-field `CurveModel`, geometric integrality, a section, a concrete `RelativePic0Designation`, and its relative Picard representability. It further requires smoothness, properness and geometric connectedness of that object, an actual Abel–Jacobi morphism, and the universal point-divisor identity for the Poincare bundle over every field-valued point.

For a positive integer $n$ invertible in the field, the conclusion is bijectivity of actual constant-$H^1$ pullback with coefficient group `Additive (rootsOfUnity n K)`. Choosing an object informally called a Jacobian does not discharge these inputs. Construct its normalizations, identify it with the canonical Stacks Picard object, and transport the actual morphism.

The manuscript deliberately uses this finite-$H^1$ route. The inspected full-Tate comparison in `Nyll/JacobianVarieties/Kummer/AbelJacobiTate.lean` is not one of its eighteen declared inputs and must not silently replace the chosen dependency path.

##### Three construction interfaces supplying N3

The file [`Nyll/AlgebraicCurves/Models/Construction/OfSmoothProperCurve.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/AlgebraicCurves/Models/Construction/OfSmoothProperCurve.lean) contains `AlgebraicCurve.CurveModel.ofSmoothProperCurve`. For an integral scheme $C$ with a proper map to $\operatorname{Spec}k$ smooth of relative dimension one, it constructs a curve model for $C$’s actual function field, with the induced $k$-algebra structure.

The file [`Nyll/AlgebraicCurves/FunctionFields/Extensions/CurveIffTranscendentalFiniteDimensional.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/AlgebraicCurves/FunctionFields/Extensions/CurveIffTranscendentalFiniteDimensional.lean) contains `AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional`. Under `PerfectField K` and `Algebra.EssFiniteType K F`, it identifies the curve-function-field condition with existence of a transcendental $t\in F$ such that $F/K(t)$ is finite-dimensional and separable. Both the separability conjunct and the essentially-finite-type assumption are real parts of the signature.

Finally, [`Nyll/JacobianVarieties/Picard/Representability/CurveModelPicardRepresentabilityAbelJacobi.lean`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/Nyll/JacobianVarieties/Picard/Representability/CurveModelPicardRepresentabilityAbelJacobi.lean) contains `AlgebraicCurve.CurveModel.exists_representsRelSubPic_abelJacobi_of_isAlgClosed`. For an algebraically closed field, a curve model and a rational section, it supplies the Picard designation, representability, Abel–Jacobi map, smooth/proper/geometrically-connected properties, origin normalization, and universal point-divisor identity. Its representing property provides the comparison with Stacks; a dimension count does not.

#### The eleven inspected Stacks files

All links here are pinned to `c496df0d9beea9deaeabcea8492605f9a0a2313b`. These canonical inputs lie in `StacksFrontier`. Their signatures were inspected; mathematical review of their transitive definitions and compilation of the eventual closure remain necessary.

##### S1: the arithmetic exact sequence

The file [`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GeometricArithmeticExactSequence.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/FundamentalGroup/GeometricArithmeticExactSequence.lean) contains `AlgebraicGeometry.shortExact_etaleFundamentalGroupMap_isAlgClosure`, tagged [`0BTX`](https://stacks.math.columbia.edu/tag/0BTX). Its inputs are a field and actual algebraic closure, a map $f:X\to\operatorname{Spec}k$, quasi-compactness and quasi-separatedness of $X$, connectedness of its actual geometric pullback, and a geometric point of that pullback. It concludes injectivity of the geometric map, equality of its range with the arithmetic projection’s kernel, and surjectivity of that projection.

The rightmost group is $\pi_1(\operatorname{Spec}k)$; its identification with $G_k$ must be supplied. Passing to the geometrically pro-$p$ quotient also needs separate characteristic-kernel and exact-quotient arguments. That quotient’s exact sequence is not literally the cited conclusion.

##### S2: finite cohomology of curves

The file [`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityCurvesFinal.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityCurvesFinal.lean) contains `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus` and `AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`, tagged [`03RQ`](https://stacks.math.columbia.edu/tag/03RQ) and [`03RR`](https://stacks.math.columbia.edu/tag/03RR). They require an algebraically closed field, an actual smooth curve, a `BigEtaleSite` containing it, a relevant `HasExt` instance, and an invertible coefficient order.

The proper case requires projectivity. The affine case requires an affine source, a smooth projective compactification, the actual open immersion and structural-map equality, and the actual complement cardinality. The $H^1$ ranks are $2g$ and $2g+r-1$. The proper statement additionally identifies the Kummer map to degree-zero Picard torsion and the degree map in $H^2$.

These computations do not specify the boundary residue coordinates. A separate theorem must connect the local Kummer character, residue map and inertia action. An unlabelled isomorphism with a finite free module cannot replace that compatibility.

##### Picard representability, smoothness and separation

The file [`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorIsAlgebraicSpace.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorIsAlgebraicSpace.lean) contains `AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor` ([`0D2C`](https://stacks.math.columbia.edu/tag/0D2C)). A flat, finitely presented, proper algebraic-space morphism with the universal structure-sheaf-map isomorphism has an algebraic relative Picard functor.

The file [`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorRepresentingSpace.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorRepresentingSpace.lean) contains `AlgebraicGeometry.Space.PicardSituation.isQuasiSeparated_and_isLocallyOfFinitePresentation_of_represents_picardFunctor` ([`0DNI`](https://stacks.math.columbia.edu/tag/0DNI)). Its input includes the actual representing natural isomorphism, flatness, finite presentation and properness. Its conclusion is quasi-separatedness and local finite presentation of the representing map.

The file [`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorSmooth.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorSmooth.lean) contains `AlgebraicGeometry.Space.isAlgebraicSpaceOver_and_isSmooth_picardFunctor` ([`0DPK`](https://stacks.math.columbia.edu/tag/0DPK)). It adds relative dimension at most one to the representability hypotheses and proves smoothness for every actual representing object.

The separatedness theorem associated with [`0DNJ`](https://stacks.math.columbia.edu/tag/0DNJ) assumes integral geometric fibres. It cannot replace the manuscript’s argument for a reducible semistable fibre. Instead, the inspected file [`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianValuativeSeparated.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Spaces/NoetherianValuativeSeparated.lean) contains `AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_discreteValuativeUniqueness` ([`0ARJ`](https://stacks.math.columbia.edu/tag/0ARJ)). It requires a locally Noetherian target, a locally-finite-type quasi-separated algebraic-space map, and uniqueness of lifts for the relevant DVR valuative squares. The line-bundle argument must provide the uniqueness hypothesis.

##### Multiplication, flatness and torsors

The file [`StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/TorsionDegree.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/TorsionDegree.lean) contains `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id` ([`0BFG`](https://stacks.math.columbia.edu/tag/0BFG)). For an actual abelian-variety group object $A$ and $n\ne0$, multiplication by $n$ is finite locally free of rank $|n|^{2\dim A}$. Apply it to the constructed group object, not merely to a module with the expected number of torsion points.

The file [`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleNoetherianFibreCriterionFibreProduct.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleNoetherianFibreCriterionFibreProduct.lean) contains `AlgebraicGeometry.Space.isFlatOverAtPoint_comp_and_isFlatOnFibreAtFieldValuedPoint_iff` ([`0APR`](https://stacks.math.columbia.edu/tag/0APR)). This pointwise criterion takes a coherent module over three locally Noetherian algebraic spaces, a geometric point, a compatible field-valued point, and nontriviality of the geometric stalk. It compares composite flatness plus fibre flatness with the corresponding two flatness assertions. Global flatness of $[p^n]$ must still be deduced.

The file [`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/TorsorComparisonUnconditional.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/TorsorComparisonUnconditional.lean) contains `AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_comparison` ([`04UT`](https://stacks.math.columbia.edu/tag/04UT)). For an actual algebraic base space and group algebraic space, it supplies the equivalence over that base between geometric fppf torsors and sheaf torsors.

The file [`StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/EtaleLocalSection.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/EtaleLocalSection.lean) contains `AlgebraicGeometry.exists_etaleNeighborhood_lift_of_smooth` ([`055U`](https://stacks.math.columbia.edu/tag/055U)). A smooth scheme map and a point in its image yield an etale neighborhood with a lift to the source. Obtaining the desired section over the strictly Henselian base still requires Henselian lifting and compatibility with the chosen point.

##### Riemann–Roch and duality

The final cited file is [`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/GorensteinCurveRiemannRoch.lean`](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/GorensteinCurveRiemannRoch.lean). It contains `AlgebraicGeometry.curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein` and `AlgebraicGeometry.eulerCharacteristic_eq_and_finrank_cohomology_eq_of_isGorenstein`, covering [`0BS6`](https://stacks.math.columbia.edu/tag/0BS6)(2) and (3). The inputs include properness, the Gorenstein property, equidimensionality, dimension exactly one, and a finite locally free sheaf of prescribed rank. The dualizing sheaf and derived cohomology are the actual Stacks objects.

The manuscript’s canonical differentials require the smooth-curve identification of the dualizing sheaf with $\Omega^1$, comparison of nonnegative derived cohomology with ordinary sheaf cohomology, and the genus/Euler-characteristic convention. Matching dimensions alone does not provide those identifications.

#### NYLL’s actual import policy

No root `AGENTS.md` exists in the inspected public NYLL tree, and none appeared in its recursive `Nyll` source tree. The relevant policy was inspected in [`.github/scripts/proof-manifest-config.json`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/.github/scripts/proof-manifest-config.json) and [`.github/scripts/publication/ci_templates/generate_manifest.py`](https://github.com/n-yamaguchi-0729/NYLL/blob/fe40c03df1b2b195053fdd63305571d97c73ce48/.github/scripts/publication/ci_templates/generate_manifest.py).

| Depth | Configured owners |
|:------|:-----------------------------------------------------------------------------------------------------------------------------------|
| 1 | `ProCGroups`, `ValuedFieldTheory`, `GaloisCohomology`, `SchemeTheory`. |
| 2 | `ClassFieldTheory`, `AlgebraicCurves`, `EtaleFundamentalGroups`, `EtaleCohomology`, `AbelianVarieties`. |
| 3 | `SawinTotallyRealTowers`, `JacobianVarieties`, `Yamaguchi26AbfaithfulGalois`, `Yamaguchi26SolvableCoverings`, `AnabelianGeometry`. |

The auditor rejects imports to deeper owners and component imports of `Nyll` or `Nyll.All`. Furthermore, `ProCGroups` may import only itself or Mathlib. The allowed external roots do not currently include `StacksCore` or `StacksFrontier`. A Stacks-dependent bridge therefore cannot be placed inside the present ProCGroups owner or introduced into NYLL with a claim that the existing policy already permits it.

Record the separate integration package and its explicitly adapted dependency distribution. Any change to the latter’s allowed dependency policy must be visible and justified. Use leaf imports, keep Stacks-dependent compatibility above pure group theory, and preserve the existing public library until the migration is reviewed and verified.

#### Map-level transport certificates required before reuse

The migration is complete only when the imported results can be applied without leaving any comparison assumption in the final theorem. The following certificates make that requirement concrete and prevent an apparently harmless interface from concealing the theorem being proved.

##### Finite covers and fundamental-group homomorphisms

For each connected $X$ and geometric point $x$, construct the comparison of cover categories and the natural identification of fibre functors. For every finite cover $V\to X$, its component must send a lift to the same scheme morphism, and its naturality square must commute for every map of covers. Prove that the resulting group equivalence carries the stabilizer of that lift to its canonical Stacks stabilizer. This transports both open-subgroup realization and the chosen point of a labelled Galois cover, rather than merely transporting their existence statements.

For each scheme morphism $f:X\to Y$, prove the corresponding square of fundamental-group maps. When chosen geometric points do not compose literally, include the specified change-of-basepoint isomorphism. Check the arithmetic projection in the same square. The ambiguity relevant to the final theorem is conjugation by the *geometric* kernel; an arbitrary arithmetic inner conjugator can change the compatibility with $G_K$ and is not an acceptable replacement. Preserve this distinction when quotienting by the maximal pro-$p$ kernel of the geometric group.

##### Finite torsors and cohomology

Compare finite constant-coefficient $H^1$ through the actual finite etale torsors that represent its classes. On each side, supply the theorem identifying the derived cohomology class with that torsor. The fibre comparison then identifies the permutation action and hence the continuous character. Prove the group law is preserved, including the contracted product of torsors, and prove compatibility both with a coefficient map and with pullback of the base scheme.

This route can avoid a new comparison of entire derived categories, but it cannot avoid comparison of the particular $H^1$ maps being used. For the systems of $p^n$-torsion coefficients, the finite-level comparison squares must commute before taking an inverse limit. Neither unrelated finite-level isomorphisms nor equal cardinalities suffice. At the boundary, add the separate local calculation identifying a residue coordinate with the character of the actual Kummer covering.

##### Picard objects and the Abel–Jacobi morphism

Uniqueness of representing objects applies only after the represented functors have been identified. For every test scheme, identify the relevant relative line-bundle classes, their equivalence relation modulo pullbacks from the base, and any rigidification along the chosen section. Prove that this correspondence respects pullback and tensor product. When NYLL’s relative sub-Picard condition is used, identify it with the canonical Stacks degree-zero condition under the actual curve hypotheses; do not infer equality of subfunctors from equality of geometric-point sets alone.

The natural isomorphism of functors then gives the representing-object isomorphism. Its compatibility with tensor product identifies the group laws, and its compatibility with the rigidification identifies the zero section. Applying it to the universal point-divisor family identifies the Abel–Jacobi morphism. Consequently the transported finite-$H^1$ theorem concerns the same morphism subsequently used to define multiplication covers, torsion-point actions and differential pullback.

##### Acceptance without strengthening the final hypotheses

Each certificate is a theorem proved from the fixed definitions and the geometric hypotheses already present in the manuscript. It must not be retained as a typeclass assumption such as an unspecified comparison oracle, an assumed reconstruction package or an abstract faithful action. The implementation can bundle constructed data for convenience, but a separate constructor theorem must produce the bundle from the advertised inputs. The final exported Hom equivalence must invoke those constructors and leave none of these certificates as an additional user hypothesis.

#### The required final acceptance record

Stacks’ inspected [contribution rules](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/CONTRIBUTING.md) prohibit `sorry`, `admit`, `native_decide` and new axioms. They distinguish human-reviewed `StacksCore` from `StacksFrontier` and require source tags to match the proved statement and generality. NYLL’s README similarly distinguishes kernel verification from fidelity to the intended mathematics.

The acceptance record must contain the exact lockfile, the Stacks-first reconciliation revision, a passing mixed-import target, and a dependency audit of the final declarations. It must show that all geometric inputs were discharged for actual constructed objects, that only standard logical axioms remain, and that no desired conclusion was hidden in an interface assumption.

The exported $p$-subtame Hom theorem must take the intrinsic field condition and the stated source/target geometric hypotheses. It must realize the *given* continuous open homomorphism by the *actual* dominant morphism modulo one geometric conjugator, and prove uniqueness. Run necessary diagnostic commands temporarily outside the completed mathematical source modules; do not add permanent acceptance files or reporting tools.


## Final acceptance

The project is complete only when S03 supplies the exact p-subtame equivalence,
its specified forward map, realization of every prescribed open arithmetic
homomorphism by one geometric conjugator, and equality-level uniqueness; I15
then checks the actual public statement and the clean pinned dependency build.
All remaining hypotheses of conditional intermediate reductions must be
proved and discharged. Preserve p=2, imperfect residue fields, nonseparated
normal finite-type sources, dimension zero and open hyperbolic targets.

Record completion directly in the checklist above. Do not create a separate
checklist, progress registry, per-task document, audit package or generated PDF.
