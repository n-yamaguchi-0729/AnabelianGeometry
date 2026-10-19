/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticCorrectionRationalCuspInertia
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaMalnormal
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsTorsionFree
import Mathlib.GroupTheory.Index

/-! # Separation of the actual rational cusp decomposition groups

For a projective line over a number field with at least three rational punctures,
we use the decomposition images of the original normalization primes. Their
intersection with the geometric kernel is the original inertia image. A common
nonidentity geometric element in two conjugates determines both the puncture
and the decomposition coset. In particular, these decomposition groups are
self-normalizing, and even one-sided finite relative index forces equality.

The intersection condition is geometric: no triviality of the entire
intersection of two arithmetic decomposition groups is asserted. These results
do not assert separatedness for arbitrary closed-point decomposition groups or
for solvable quotients over finite fields.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open SchemeTheory EtaleFundamentalGroups.Inertia
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction rationalConfigurationAmbientSMulRatFunc

variable
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]

local notation "Δ" => rationalConfigurationGeometricGroup k κ s Ω
local notation "Π" => rationalConfigurationArithmeticGroup k κ s Ω
local notation "B" => CurveModel.openBoundaryPlaces (projectiveLineRatFuncModel κ)
  (rationalConfigurationBaseChangeChart k κ s)
local notation "I" => rationalConfigurationChosenInertia k κ s Ω
local notation "D" => rationalConfigurationChosenDecomposition k κ s Ω
local notation "ι" =>
  ContinuousMonoidHom.toMonoidHom (rationalConfigurationGeometricInclusion k κ s Ω)
local notation "q₀" => ContinuousMonoidHom.toMonoidHom (arithmeticFundamentalGroupHom k κ
  (Scheme.Opens.ι (rationalConfigurationOpen s) ≫ π k 1)
  (rationalConfigurationArithmeticBasePoint k κ s Ω))

include hs

omit [IsAlgClosure k κ] in
private theorem chosenInertia_separation_data :
    (∀ p : B, Subgroup.normalizer (I p : Set Δ) = I p) ∧
    (∀ p : B, ∃ z : Δ, z ∈ I p ∧ ∀ n : ℕ, n ≠ 0 → z ^ n ≠ 1) ∧
    ∀ (p r : B) (a x : Δ), x ≠ 1 → x ∈ I p →
      x ∈ (I r).map (MulAut.conj a).toMonoidHom → p = r ∧ a ∈ I p := by
  let U := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : QuasiCompact j := inferInstanceAs
    (QuasiCompact (rationalConfigurationBaseChangeChart k κ s))
  let : QuasiSeparated j := inferInstanceAs
    (QuasiSeparated (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ (RatFunc κ) Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Finite (M.openBoundaryPlaces j) := rationalConfigurationBoundaryPlaces_finite k κ s
  let : Nontrivial (M.openBoundaryPlaces j) :=
    rationalConfigurationBoundaryPlaces_nontrivial k κ s hs
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let : ∀ p : M.openBoundaryPlaces j, (Q p).IsMaximal := fun p => inferInstance
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  have hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j) :=
    rationalConfigurationBoundaryPlaces_card_ge_three k κ s hs
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact fieldChart_boundaryInertia_self_normalizing M j hj hfield hthree Q p
  · intro p
    let f := boundaryPlaceInertiaLift M j hj hfield Q p
    have hf : Function.Injective f := boundaryPlaceInertiaLift_injective M j hj hfield Q p
    obtain ⟨t, ht⟩ := primeToRoots_exists_ne_one κ κ
    refine ⟨f t, ?_, ?_⟩
    · change f t ∈ genericPlaceInertia U p.val (Q p)
      rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p]
      exact ⟨t, rfl⟩
    · intro n hn h
      exact primeToRoots_pow_ne_one κ κ ht hn
        (hf ((map_pow f t n).trans (h.trans (map_one f).symm)))
  · intro p r a x hx hp hr
    exact boundaryInertia_common_ne_one_imp_label_and_conjugator
      M j hj hfield hthree Q p r a x hx hp hr

private theorem chosenDecomposition_comap_geometric (p : B) :
    (D p).comap ι = I p := by
  have hex := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
  rw [rationalConfigurationChosenDecomposition_eq_normalizer k κ s Ω p hs]
  change (Subgroup.normalizer ((I p).map ι : Set Π)).comap ι = I p
  have hi : Function.Injective ι := hex.1
  rw [Subgroup.comap_normalizer_eq_of_le_range ((I p).map_le_range ι),
    Subgroup.comap_map_eq_self_of_injective hi]
  exact (chosenInertia_separation_data k κ s hs Ω).1 p

/-- The original cusp inertia is exactly the geometric part of the actual
arithmetic decomposition image. -/
theorem rationalConfigurationChosenDecomposition_inf_geometricKernel (p : B) :
    D p ⊓ (q₀).ker = (I p).map ι := by
  have hex := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
  have hmap := congrArg (fun H : Subgroup Δ => H.map ι)
    (chosenDecomposition_comap_geometric k κ s hs Ω p)
  rw [Subgroup.map_comap_eq] at hmap
  have hrange : (ι).range = (q₀).ker := hex.2.2.symm
  rw [hrange, inf_comm] at hmap
  exact hmap

/-- A common nonidentity geometric element identifies the rational cusp and
the arithmetic decomposition coset, even for an arithmetic conjugator. -/
theorem rationalConfigurationChosenDecomposition_common_geometric_ne_one
    (p r : B) (a x : Π) (hx : x ≠ 1) (hxker : x ∈ (q₀).ker)
    (hp : x ∈ D p) (hr : x ∈ (D r).map (MulAut.conj a).toMonoidHom) :
    p = r ∧ a ∈ D p := by
  have hex := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
  have hrange : (ι).range = (q₀).ker := hex.2.2.symm
  obtain ⟨u, hu⟩ := (show x ∈ (ι).range from hrange.symm ▸ hxker)
  have hu1 : u ≠ 1 := by
    intro h
    apply hx
    rw [← hu, h, map_one]
  have huI : u ∈ I p := by
    rw [← chosenDecomposition_comap_geometric k κ s hs Ω p]
    change ι u ∈ D p
    exact hu.symm ▸ hp
  have hDN : D r ≤ Subgroup.normalizer ((I r).map ι : Set Π) :=
    le_of_eq (rationalConfigurationChosenDecomposition_eq_normalizer k κ s Ω r hs)
  obtain ⟨g, d, _hdq, hgd, _hIconj⟩ :=
    arithmeticCorrection_exists_geometric_inertia_conjugator ι q₀ hrange (I r) (D r)
      hDN (rationalConfigurationChosenDecomposition_arithmetic_surjective k κ s Ω r) a
  have hprod : ι g * d.val = a := by
    rw [hgd]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨y, hy, hyx⟩ := hr
  have hpre : ι (g⁻¹ * u * g) = d.val * y * d.val⁻¹ := by
    have h := congrArg (fun z : Π => (ι g)⁻¹ * z * ι g) hyx
    change (ι g)⁻¹ * (a * y * a⁻¹) * ι g = (ι g)⁻¹ * x * ι g at h
    rw [← hprod, ← hu] at h
    have h' : d.val * y * d.val⁻¹ = (ι g)⁻¹ * ι u * ι g := by
      simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using h
    have hmap : ι (g⁻¹ * u * g) = (ι g)⁻¹ * ι u * ι g := by
      simp only [map_mul, map_inv]
    exact hmap.trans h'.symm
  have hvI : g⁻¹ * u * g ∈ I r := by
    rw [← chosenDecomposition_comap_geometric k κ s hs Ω r]
    change ι (g⁻¹ * u * g) ∈ D r
    rw [hpre]
    exact (D r).mul_mem ((D r).mul_mem d.property hy) ((D r).inv_mem d.property)
  have huconj : u ∈ (I r).map (MulAut.conj g).toMonoidHom := by
    refine ⟨g⁻¹ * u * g, hvI, ?_⟩
    change g * (g⁻¹ * u * g) * g⁻¹ = u
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  obtain ⟨hpr, hgI⟩ := (chosenInertia_separation_data k κ s hs Ω).2.2
    p r g u hu1 huI huconj
  refine ⟨hpr, ?_⟩
  have hig : ι g ∈ D p := by
    change g ∈ (D p).comap ι
    rw [chosenDecomposition_comap_geometric k κ s hs Ω p]
    exact hgI
  have hd : d.val ∈ D p := hpr.symm ▸ d.property
  exact hprod ▸ (D p).mul_mem hig hd

/-- Even one-sided finite relative index between conjugate cusp decomposition
groups forces the same cusp and a conjugator in its decomposition group.
This gives, in particular, separation up to commensurability. -/
theorem rationalConfigurationChosenDecomposition_finiteRelIndex_iff
    (p r : B) (a : Π) :
    ((D r).map (MulAut.conj a).toMonoidHom).IsFiniteRelIndex (D p) ↔
      p = r ∧ a ∈ D p := by
  constructor
  · intro hindex
    obtain ⟨z, hz, hzpow⟩ := (chosenInertia_separation_data k κ s hs Ω).2.1 p
    have hzD : ι z ∈ D p := by
      change z ∈ (D p).comap ι
      rw [chosenDecomposition_comap_geometric k κ s hs Ω p]
      exact hz
    obtain ⟨n, hn, _hle, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
      hindex.relIndex_ne_zero hzD
    have hex := arithmetic_exactSequence_of_isSepClosure k κ
      (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
      ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
    have hn1 : (ι z) ^ n ≠ 1 := by
      intro h
      apply hzpow n (Nat.ne_of_gt hn)
      exact hex.1 ((map_pow ι z n).trans (h.trans (map_one ι).symm))
    have hker : (ι z) ^ n ∈ (q₀).ker := by
      have hrange : (ι).range = (q₀).ker := hex.2.2.symm
      rw [← hrange, ← map_pow]
      exact ⟨z ^ n, rfl⟩
    exact rationalConfigurationChosenDecomposition_common_geometric_ne_one
      k κ s hs Ω p r a ((ι z) ^ n) hn1 hker hmem.2 hmem.1
  · rintro ⟨hpr, ha⟩
    subst r
    have hconj : (D p).map (MulAut.conj a).toMonoidHom = D p :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((D p).le_normalizer ha)
    rw [hconj]
    infer_instance

/-- The actual arithmetic decomposition images are self-normalizing. -/
theorem rationalConfigurationChosenDecomposition_self_normalizing (p : B) :
    Subgroup.normalizer (D p : Set Π) = D p := by
  apply le_antisymm
  · intro a ha
    have hconj : (D p).map (MulAut.conj a).toMonoidHom = D p :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
    have hindex : ((D p).map (MulAut.conj a).toMonoidHom).IsFiniteRelIndex (D p) := by
      rw [hconj]
      infer_instance
    exact ((rationalConfigurationChosenDecomposition_finiteRelIndex_iff
      k κ s hs Ω p p a).mp hindex).2
  · exact (D p).le_normalizer

end AnabelianGeometry.WeightFiltration
