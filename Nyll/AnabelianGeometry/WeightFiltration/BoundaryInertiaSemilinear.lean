/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaValues
import Nyll.JacobianVarieties.Kummer.OpenSemilinearCharacter
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceConjugation
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction

/-!
# Moving boundary inertia under actual semilinear source conjugation

Finite characters compare the original boundary inertia maps. The proof
uses their existing residue formula, without transporting normalization primes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open AlgebraicGeometry.FiniteEtale
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra k K] [IsSepClosure k K]
    (U : Scheme) [CompactSpace U] [QuasiSeparatedSpace U]
    (f : U ⟶ Spec (.of k))


variable
    [IsIntegral (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)] [CompactSpace
      ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)]
    {F : Type} [Field F] [Algebra K F]
    (M : CurveModel K F)
    (j : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) ⟶ M.C)
      [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField]
    (hfield : algebraMap F (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      f).functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      f).functionField Ω] [Algebra F Ω]
    [IsScalarTower F (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      f).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      f).functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

/-- A genuine source-induced arithmetic conjugation carries each original
boundary inertia to the transported place and applies the same automorphism
to its constant-root parameter. -/
theorem boundaryPlaceInertiaHom_source_semilinear
    (g : SemilinearAut K F)
    (hS : ∀ p : Place K F,
      p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j)
    (φ : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField ≃+*
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField)
    (hφ : ∀ z : F, φ (j.functionFieldMap hj (M.ffEquiv z)) =
      j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)))
    (a : Ω ≃+* Ω)
    (ha : ∀ z : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField,
      a (algebraMap (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        f).functionField Ω z) = algebraMap (Limits.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k K))) f).functionField Ω (φ z))
    (hsource : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        ((ξ (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField Ω ≫
          (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).fromSpecStalk
          (genericPoint (↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :
            Type))) ≫
          Limits.pullback.snd _ f) =
      (ξ (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField Ω ≫
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).fromSpecStalk
        (genericPoint (↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :
          Type))) ≫
        Limits.pullback.snd _ f)
    (p : M.openBoundaryPlaces j) (t : (primeToRootsSystem K K).inverseLimit) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap (Limits.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k K))) f).functionField Ω))
    let xi := η ≫ (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      f).fromSpecStalk (genericPoint (↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k
      K))) f) : Type))
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    let gA : Aut (fiber (xi ≫ Limits.pullback.snd _ f)) :=
      fiberSourceIso (xi ≫ Limits.pullback.snd _ f) e ≪≫ eqToIso (congrArg fiber hsource)
    geometricAbelianGaloisAction k K U f xi
        (arithmeticFundamentalGroupHom k K f (xi ≫ Limits.pullback.snd _ f) gA)
        (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      boundaryPlaceInertiaHom M j hj hfield Q
        ⟨g • p.val, (hS p.val).mp p.property⟩
        (primeToRootsCoefficientMap K K (SemilinearAut.baseAut g).toRingHom t) := by
  intro η xi e gA
  classical
  let q := (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).fromSpecStalk
    (genericPoint (↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) : Type))
  let G := Aut (fiber xi)
  let P := TopologicalAbelianization G
  let A := geometricAbelianGaloisAction k K U f xi
    (arithmeticFundamentalGroupHom k K f (xi ≫ Limits.pullback.snd _ f) gA)
  let p' : M.openBoundaryPlaces j := ⟨g • p.val, (hS p.val).mp p.property⟩
  let t' := primeToRootsCoefficientMap K K (SemilinearAut.baseAut g).toRingHom t
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :=
    IsNormalIntegral.of_stalks (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) z).2)
  let : IsDominant q := genericPoint_isDominant (Limits.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap k K))) f)
  let : QuasiCompact q :=
    { isCompact_preimage := fun V _ _ => (Set.toFinite (q ⁻¹' V)).isCompact }
  let J := fieldSourceAbsoluteGaloisHom (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap
    k K))) f).functionField Ω q
  have hJ : Function.Surjective J := fieldSourceAbsoluteGaloisHom_surjective (Limits.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField Ω q
  let : TotallyDisconnectedSpace P :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  have hchars (n : ℕ+) :
      let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
      ∀ χ : P →ₜ* rootsOfUnity (n : ℕ) K,
        χ (A (boundaryPlaceInertiaHom M j hj hfield Q p t)) =
          χ (boundaryPlaceInertiaHom M j hj hfield Q p' t') := by
    intro topology χ
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    have hn : IsUnit ((n : ℕ) : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
    let B := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative B) := ⊥
    let : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
    obtain ⟨x, hχ⟩ := (finiteH1AbelianCharacterEquiv B xi).toEquiv.surjective (Additive.ofMul χ)
    change h1AbelianCharacter B xi x = χ at hχ
    obtain ⟨r, hr⟩ := (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).surjective x
    obtain ⟨u', hu'⟩ := QuotientGroup.mk_surjective r.toMul
    have hr' : r = Additive.ofMul (QuotientGroup.mk u') := hu'.symm
    rw [hr'] at hr
    let S := M.openBoundaryPlaces j
    have hSinv (v : Place K F) : v ∈ S ↔ g⁻¹ • v ∈ S := by
      simpa only [smul_inv_smul] using (hS (g⁻¹ • v)).symm
    obtain ⟨u, hu⟩ := Pic0.exists_openKummerUnit_semilinear S S n g⁻¹ hSinv u'
    have hforward : u'.val = Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val := by
      apply Units.ext
      have hv : (u.val : F) = g⁻¹ • (u'.val : F) := congrArg Units.val hu
      change (u'.val : F) = g • (u.val : F)
      rw [hv, smul_inv_smul]
    let c := CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi
      (Additive.ofMul (QuotientGroup.mk u))
    let c' := CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi
      (Additive.ofMul (QuotientGroup.mk u'))
    have hc' : c' = x := hr
    let scalar : Multiplicative B → K := fun z =>
      ((show rootsOfUnity (n : ℕ) K from z).val : K)
    have hsem (z : P) :
        scalar (h1AbelianCharacter B xi c' (A z)) =
          SemilinearAut.baseAut g (scalar (h1AbelianCharacter B xi c z)) := by
      obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk G z
      obtain ⟨ρ, rfl⟩ := hJ v
      have hact := geometricAbelianGaloisAction_fieldSource_conjugate k K U f q φ a ha hsource ρ
      change A (TopologicalAbelianization.mk _ (J ρ)) =
        TopologicalAbelianization.mk _ (J (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) at hact
      rw [hact, h1AbelianCharacter_apply_mk, h1AbelianCharacter_apply_mk]
      change scalar (h1Character B xi
        (CurveModel.OpenKummer.kummerEtaleClass M S n u' j hj
          (M.place_not_mem_openBoundaryPlaces j) hn xi) _) =
        SemilinearAut.baseAut g (scalar (h1Character B xi
          (CurveModel.OpenKummer.kummerEtaleClass M S n u j hj
            (M.place_not_mem_openBoundaryPlaces j) hn xi) _))
      rw [h1Character_openKummer, h1Character_openKummer]
      exact CurveModel.OpenKummer.kummerMonodromyCharacter_generic_semilinear M S n j hj
        (M.place_not_mem_openBoundaryPlaces j) hn g φ hφ a ha u u' hforward ρ
    have hres : finiteResidue M n j hj hn xi c' p' = finiteResidue M n j hj hn xi c p := by
      have hleft := congrFun (finiteResidue_comparison M n j hj hn xi
        (Additive.ofMul (QuotientGroup.mk u'))) p'
      have hright := congrFun (finiteResidue_comparison M n j hj hn xi
        (Additive.ofMul (QuotientGroup.mk u))) p
      change finiteResidue M n j hj hn xi c' p' =
        (p'.val.ord (u'.val : F) : ZMod (n : ℕ)) at hleft
      change finiteResidue M n j hj hn xi c p =
        (p.val.ord (u.val : F) : ZMod (n : ℕ)) at hright
      rw [hleft, hright]
      have hv : p'.val.ord (u'.val : F) = p.val.ord (u.val : F) := by
        change (g • p.val).ord (u'.val : F) = _
        rw [hforward]
        exact SemilinearAut.ord_smul g p.val (u.val : F)
      exact congrArg (fun z : ℤ => (z : ZMod (n : ℕ))) hv
    rw [← hχ, ← hc']
    apply rootsOfUnity.coe_injective
    change scalar (h1AbelianCharacter B xi c'
      (A (boundaryPlaceInertiaHom M j hj hfield Q p t))) =
        scalar (h1AbelianCharacter B xi c'
          (boundaryPlaceInertiaHom M j hj hfield Q p' t'))
    rw [hsem]
    have hl := boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p c t
    have hr := boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p' c' t'
    rw [hl, hr, hres]
    let r₀ : rootsOfUnity (n : ℕ) K := (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
    let r₁ : rootsOfUnity (n : ℕ) K := (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t'
    have hroot : ((r₁ : Kˣ) : K) = SemilinearAut.baseAut g ((r₀ : Kˣ) : K) :=
      primeToRootsResidueAction_scalar K K (SemilinearAut.baseAut g) ⟨n.val, hn⟩ t
    change SemilinearAut.baseAut g (((r₀ : Kˣ) : K) ^
      (finiteResidue M n j hj hn xi c p).val) =
      ((r₁ : Kˣ) : K) ^ (finiteResidue M n j hj hn xi c p).val
    rw [map_pow, hroot]
  let H : ClosedSubgroup P := ⟨⊥, by
    change IsClosed ({1} : Set P)
    exact isClosed_singleton⟩
  apply div_eq_one.mp
  have hm := mem_closedSubgroup_of_rootCharacters K H
    (A (boundaryPlaceInertiaHom M j hj hfield Q p t) /
      boundaryPlaceInertiaHom M j hj hfield Q p' t') (by
        intro n topology χ _
        rw [map_div, hchars n χ, div_self'])
  exact hm

end AnabelianGeometry.WeightFiltration
