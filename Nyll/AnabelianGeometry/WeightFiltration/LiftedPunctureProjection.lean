/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationPunctureEquiv
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverInjectivity

/-! # Lifted puncture labels commute with the original cover projections


This is a genuinely group-theoretic bridge, not a conditional cross-ratio
endpoint. It does not assume a field isomorphism, coordinate preservation,
root-sign agreement, or surjectivity of a ramified inertia image. Images of
upstairs inertia need only be contained in conjugates of their actual downstairs
inertia groups. The existing connectedCover_actualPlaceInertia_image supplies
this containment at the actual localized prime, including ramified cusps.

The final specialization uses the actual matched-fibre group equivalence and
its original inclusion square; the selected fibre map e is never replaced.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

private theorem puncture_abelian_conjugate
    {G A : Type*} [Group G] [CommGroup A] (f : G →* A) (a x : G) :
    f ((MulAut.conj a) x) = f x := by
  change f (a * x * a⁻¹) = f x
  rw [map_mul, map_mul, map_inv, mul_comm (f a) (f x),
    mul_assoc, mul_inv_cancel, mul_one]

section Boundary
variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal] [hfin : Finite (M.openBoundaryPlaces j)]

include hfin hj hfield in
/-- One common nonidentity element of two conjugate inertia groups already
identifies the downstairs puncture. Equality of the whole groups is unnecessary. -/
theorem boundaryPlace_eq_of_conjugate_inertia_common_ne_one
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    (p q : M.openBoundaryPlaces j)
    (a b x : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))))
    (hx : x ≠ 1)
    (hp : x ∈ (genericPlaceInertia X p.val (Q p)).map (MulAut.conj a).toMonoidHom)
    (hq : x ∈ (genericPlaceInertia X q.val (Q q)).map (MulAut.conj b).toMonoidHom) :
    p = q := by
  classical
  by_contra hpq
  let := Fintype.ofFinite (M.openBoundaryPlaces j)
  have hthree' : 3 ≤ Fintype.card (M.openBoundaryPlaces j) := by
    simpa only [Nat.card_eq_fintype_card] using hthree
  have hlt : ({p, q} : Finset (M.openBoundaryPlaces j)).card <
      (Finset.univ : Finset (M.openBoundaryPlaces j)).card := by
    have hcard := Finset.card_le_two (a := p) (b := q)
    simp only [Finset.card_univ]
    omega
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hrpq : r ≠ p ∧ r ≠ q := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hr
  obtain ⟨y, hy, hyx⟩ := hp
  obtain ⟨z, hz, hzx⟩ := hq
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p] at hy
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q q] at hz
  obtain ⟨t, rfl⟩ := hy
  obtain ⟨u, rfl⟩ := hz
  have hab : boundaryPlaceInertiaHom M j hj hfield Q p t =
      boundaryPlaceInertiaHom M j hj hfield Q q u := by
    change TopologicalAbelianization.mk _ (boundaryPlaceInertiaLift M j hj hfield Q p t) =
      TopologicalAbelianization.mk _ (boundaryPlaceInertiaLift M j hj hfield Q q u)
    calc
      _ = TopologicalAbelianization.mk _ x :=
        (puncture_abelian_conjugate (TopologicalAbelianization.mk _) a
          (boundaryPlaceInertiaLift M j hj hfield Q p t)).symm.trans
            (congrArg (TopologicalAbelianization.mk _) hyx)
      _ = _ :=
        (congrArg (TopologicalAbelianization.mk _) hzx).symm.trans
          (puncture_abelian_conjugate (TopologicalAbelianization.mk _) b
            (boundaryPlaceInertiaLift M j hj hfield Q q u))
  have ht : t = 1 := (boundaryPlaceInertiaHom_eq_of_third M j hj hfield Q
    p q r hpq hrpq.1.symm hrpq.2.symm t u hab).1
  apply hx
  rw [← hyx, ht, map_one, map_one]

end Boundary

section RationalConfiguration
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance (priority := 2000) liftedPunctureSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul


/-- The nontrivial-intersection separation owner on the original rational labels. -/
theorem rationalConfigurationChosenInertia_common_ne_one_imp_eq
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p q : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (a b x : rationalConfigurationGeometricGroup k κ s Ω)
    (hx : x ≠ 1)
    (hp : x ∈ (rationalConfigurationChosenInertia k κ s Ω p).map
      (MulAut.conj a).toMonoidHom)
    (hq : x ∈ (rationalConfigurationChosenInertia k κ s Ω q).map
      (MulAut.conj b).toMonoidHom) :
    p = q := by
  let U := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ (RatFunc κ) Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Finite (M.openBoundaryPlaces j) := rationalConfigurationBoundaryPlaces_finite k κ s
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let : ∀ p : M.openBoundaryPlaces j, (Q p).IsMaximal := fun p => inferInstance
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  change x ∈ (genericPlaceInertia U p.val (Q p)).map
    (MulAut.conj a).toMonoidHom at hp
  change x ∈ (genericPlaceInertia U q.val (Q q)).map
    (MulAut.conj b).toMonoidHom at hq
  exact boundaryPlace_eq_of_conjugate_inertia_common_ne_one M j hj hfield Q
    (rationalConfigurationBoundaryPlaces_card_ge_three k κ s hs) p q a b x hx hp hq

end RationalConfiguration

private theorem puncture_map_conjugate
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (a : G) :
    (A.map (MulAut.conj a).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change f (a * x * a⁻¹) = f a * f x * (f a)⁻¹
  simp only [map_mul, map_inv]

private theorem puncture_map_conjugate_twice
    {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- Naturality of the puncture correspondence follows from the unchanged
inclusion square. The hypotheses concern inertia, not values or coordinates.
In particular only containment, not equality, is needed for the projections. -/
theorem punctureProjection_commutes_of_inertia_inclusion_square
    {G H GS HT : Type*} [Group G] [Group H] [Group GS] [Group HT]
    {P Q R V : Type*}
    (α : G ≃* H) (β : GS ≃* HT) (iS : GS →* G) (iT : HT →* H)
    (hiS : Function.Injective iS)
    (hsquare : ∀ x, iT (β x) = α (iS x))
    (I : P → Subgroup G) (J : Q → Subgroup H)
    (IS : R → Subgroup GS) (IT : V → Subgroup HT)
    (σ : P ≃ Q) (τ : R ≃ V) (pS : R → P) (pT : V → Q)
    (hbase : ∀ p, ∃ a, (I p).map α.toMonoidHom =
      (J (σ p)).map (MulAut.conj a).toMonoidHom)
    (hcover : ∀ r, ∃ a, (IS r).map β.toMonoidHom =
      (IT (τ r)).map (MulAut.conj a).toMonoidHom)
    (hprojS : ∀ r, ∃ a, (IS r).map iS ≤
      (I (pS r)).map (MulAut.conj a).toMonoidHom)
    (hprojT : ∀ v, ∃ a, (IT v).map iT ≤
      (J (pT v)).map (MulAut.conj a).toMonoidHom)
    (hne : ∀ r, ∃ x, x ∈ IS r ∧ x ≠ 1)
    (hsep : ∀ (p q : Q) (a b x : H), x ≠ 1 →
      x ∈ (J p).map (MulAut.conj a).toMonoidHom →
      x ∈ (J q).map (MulAut.conj b).toMonoidHom → p = q) :
    ∀ r, σ (pS r) = pT (τ r) := by
  intro r
  obtain ⟨a, ha⟩ := hprojS r
  obtain ⟨b, hb⟩ := hbase (pS r)
  obtain ⟨c, hc⟩ := hcover r
  obtain ⟨d, hd⟩ := hprojT (τ r)
  have hmaps : ((IS r).map iS).map α.toMonoidHom =
      ((IS r).map β.toMonoidHom).map iT := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact (hsquare x).symm
  have hleft : ((IS r).map iS).map α.toMonoidHom ≤
      (J (σ (pS r))).map (MulAut.conj (α a * b)).toMonoidHom := by
    have h := Subgroup.map_mono (f := α.toMonoidHom) ha
    rw [puncture_map_conjugate, hb, puncture_map_conjugate_twice] at h
    exact h
  have hright : ((IS r).map iS).map α.toMonoidHom ≤
      (J (pT (τ r))).map (MulAut.conj (iT c * d)).toMonoidHom := by
    rw [hmaps, hc, puncture_map_conjugate]
    have h := Subgroup.map_mono (f := (MulAut.conj (iT c)).toMonoidHom) hd
    rw [puncture_map_conjugate_twice] at h
    exact h
  obtain ⟨x, hx, hx1⟩ := hne r
  have hm : α (iS x) ∈ ((IS r).map iS).map α.toMonoidHom :=
    ⟨iS x, ⟨x, hx, rfl⟩, rfl⟩
  have hm1 : α (iS x) ≠ 1 := by
    intro h
    apply hx1
    apply hiS
    apply α.injective
    simpa only [map_one] using h
  exact hsep _ _ _ _ _ hm1 (hleft hm) (hright hm)

end AnabelianGeometry.WeightFiltration

open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The same-e finite-cover specialization. All covering groups and projection
homomorphisms are the actual ones at w and e w. The pointwise inclusion square
and injectivity are proved here, rather than imposed as new assumptions. -/
theorem matchedFiberCoverGroupTransport_punctureProjection
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (AS : FiniteEtale S) (AT : FiniteEtale T)
    (ξs : Spec (.of Ω₁) ⟶ S) (ξt : Spec (.of Ω₂) ⟶ T)
    (α : π₁ᵉᵗ(ξs) ≃ₜ* π₁ᵉᵗ(ξt))
    (e : (fiber ξs).obj AS ≃ (fiber ξt).obj AT)
    (he : ∀ g x, e (g • x) = α g • e x)
    (w : (fiber ξs).obj AS)
    {P Q R V : Type*}
    (I : P → Subgroup π₁ᵉᵗ(ξs)) (J : Q → Subgroup π₁ᵉᵗ(ξt))
    (IS : R → Subgroup π₁ᵉᵗ(actualFiberPointLift ξs AS w))
    (IT : V → Subgroup π₁ᵉᵗ(actualFiberPointLift ξt AT (e w)))
    (σ : P ≃ Q) (τ : R ≃ V) (pS : R → P) (pT : V → Q)
    (hbase : ∀ p, ∃ a, (I p).map α.toMonoidHom =
      (J (σ p)).map (MulAut.conj a).toMonoidHom)
    (hcover : ∀ r, ∃ a, (IS r).map
      (matchedFiberCoverGroupTransport AS AT ξs ξt α e he w).toMonoidHom =
        (IT (τ r)).map (MulAut.conj a).toMonoidHom)
    (hprojS : ∀ r, ∃ a, (IS r).map
      (pointedFundamentalGroupHom AS.hom (actualFiberPointLift ξs AS w) ξs
        (actualFiberPointLift_comp ξs AS w)).toMonoidHom ≤
          (I (pS r)).map (MulAut.conj a).toMonoidHom)
    (hprojT : ∀ v, ∃ a, (IT v).map
      (pointedFundamentalGroupHom AT.hom (actualFiberPointLift ξt AT (e w)) ξt
        (actualFiberPointLift_comp ξt AT (e w))).toMonoidHom ≤
          (J (pT v)).map (MulAut.conj a).toMonoidHom)
    (hne : ∀ r, ∃ x, x ∈ IS r ∧ x ≠ 1)
    (hsep : ∀ (p q : Q) (a b x : π₁ᵉᵗ(ξt)), x ≠ 1 →
      x ∈ (J p).map (MulAut.conj a).toMonoidHom →
      x ∈ (J q).map (MulAut.conj b).toMonoidHom → p = q) :
    ∀ r, σ (pS r) = pT (τ r) := by
  exact AnabelianGeometry.WeightFiltration.punctureProjection_commutes_of_inertia_inclusion_square
    α.toMulEquiv (matchedFiberCoverGroupTransport AS AT ξs ξt α e he w).toMulEquiv
    (pointedFundamentalGroupHom AS.hom (actualFiberPointLift ξs AS w) ξs
      (actualFiberPointLift_comp ξs AS w)).toMonoidHom
    (pointedFundamentalGroupHom AT.hom (actualFiberPointLift ξt AT (e w)) ξt
      (actualFiberPointLift_comp ξt AT (e w))).toMonoidHom
    (pointedFundamentalGroupHom_injective AS (actualFiberPointLift ξs AS w) ξs
      (actualFiberPointLift_comp ξs AS w))
    (matchedFiberCoverGroupTransport_inclusion AS AT ξs ξt α e he w)
    I J IS IT σ τ pS pT hbase hcover hprojS hprojT hne hsep

end AlgebraicGeometry.FiniteEtale

/-!
## Exact remaining assembly, without adding endpoint hypotheses

The intended bare theorem still quantifies only over k, its fixed algebraic
closure κ, the two original finite puncture sets with cardinality at least 3,
their original geometric generic ambient closures, and the original arithmetic
π₁ isomorphism over Gal(κ/k). This file does not prove that theorem.

The strict finite-base comparison and the following assembly are not established here:

1. Keep the original quadratic Isom e and the finite field E containing its
   scalar radical and all original boundary radicals. Use the actual canonical
   constant-field lift, then quadraticScalar_actual_canonicalBase_coverIso.
   Compose the actual fibre identifications, keeping e at every point.

2. Use matchedFiberCoverGroupTransport_arithmetic to get the same arithmetic
   quotient on the two actual square covers. Transport through the actual
   NamedRationalSquareCoverConfiguration isomorphisms, with their retained
   root-field/generic equalities. Restrict to the geometric kernels, or use
   the unique geometric equivalence owner, preserving the inclusion square.

3. Apply the existing pair-scalar/root all-orders construction to this specific
   lifted arithmetic isomorphism. Retain BOTH its lifted τ and inertia-conjugacy
   witnesses along with its all-orders scalar data. Do not call a second
   existential theorem that chooses another τ
   when extracting cyclic cross-ratio classes: the fixed-σ scalar/root theorem
   must be instantiated with this τ. This is an important endpoint API issue.

4. For hprojS/hprojT use connectedCover_actualPlaceInertia_image at the actual
   localized normalization prime: its equality with I ∩ range gives containment
   by inf_le_left. Changing the chosen prime only conjugates inertia; use the
   existing absolute normalization-prime orbit and inertia_smul_map owners.
   The projected label pS/pT is the ACTUAL place restriction, not a freely chosen
   map. boundaryInertia_exists_ne_one gives hne. The wrapper
   rationalConfigurationChosenInertia_common_ne_one_imp_eq gives hsep on the
   original rational boundary labels. The final theorem proves
   σ ∘ pS = pT ∘ τ, including at the
   two ramification labels. No unramified-surjectivity premise is required.

5. Choose ONE lifted point over c₀ and ONE over c. Their τ-images lie over σ c₀
   and σ c by step 4. With the actual root-coordinate model, form t=r_c/r_c₀
   and u=r'_τc/r'_τc₀. Both source points and both target points are fixed here.
   Their squares are the original normalized x and y. The single τ yields
   cyclic data for t/u and their complements by permuting this SAME reference
   triple (the two ramification points and the selected lift of c₀).
   There is no need to claim r'_τc has a preselected sign independently of c₀:
   simultaneous deck translation changes both numerator and denominator, and
   their ratio is unchanged. This is consistent same-pair sign control, not
   an assumption that arbitrary square roots have matching cyclic subgroups.

6. Apply units_eq_of_cyclic_data_and_square_roots over E. Descend x=y along
   the injective coefficient map k → E. Finally matchTriples_configuration
   gives the one projective coordinate equivalence for all original labels.

The first unresolved GEOMETRIC instantiation is steps 2–4 with the actual
model-isomorphism/basepoint identifications. The group-theoretic label-naturality
step is implemented above. The root equations at steps 5–6 must be derived from
NamedRationalSquareCoverConfiguration's original generic equality and the
existing standard-place/root-coordinate owners, not postulated as a new premise.
-/
