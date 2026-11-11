/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.SemilinearSourcePullback
public import Nyll.EtaleCohomology.Frobenius.FiniteRootsAction
public import Nyll.JacobianVarieties.Kummer.OpenSemilinearCharacter
public import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidues
public import Nyll.SchemeTheory.FunctionFields.GenericSourceIso
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Naturality
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Actual open Kummer classes and boundary residues under semilinear pullback

The existing generic root-cover formula determines the derived class itself.
Its original boundary residues are then transported by the actual place action.
Only invertibility of the coefficient exponent is required; no full-Tate or
characteristic-zero comparison is used.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration
open AlgebraicCurve.CurveModel.OpenKummer

namespace AnabelianGeometry.FiniteField

variable {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))

private theorem h1Character_openKummer
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (u : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ
        (quotientCohomologyEquiv M n j hj hn ξ (Additive.ofMul (QuotientGroup.mk u))) =
      kummerMonodromyCharacter M (M.openBoundaryPlaces j) n u j hj
        (M.place_not_mem_openBoundaryPlaces j) hn ξ := by
  intro topology discrete
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact congrArg Additive.toMul ((finiteH1CharacterEquiv A ξ).apply_symm_apply
    (Additive.ofMul (kummerMonodromyCharacter M (M.openBoundaryPlaces j) n u j hj
      (M.place_not_mem_openBoundaryPlaces j) hn ξ)))

/-- The class of the transported original function is the coefficient
transform of the actual scheme pullback of its class. -/
theorem openKummerCohomology_semilinearPullback
    (θ : X ≅ X) (g : SemilinearAut K F)
    (hfield : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion
      (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)))
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (u u' : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n)
    (hu' : u'.val = Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    quotientCohomologyEquiv M n j hj hn ξ (Additive.ofMul (QuotientGroup.mk u')) =
      Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom
          (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive)) 1
        (constantCohomologyPullback θ.hom A 1
          (quotientCohomologyEquiv M n j hj hn ξ (Additive.ofMul (QuotientGroup.mk u)))) := by
  intro ξ A
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) z).2)
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  obtain ⟨a, ha, hpoint⟩ := exists_genericPoint_sourceIso θ Ω
  let τ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let q := X.fromSpecStalk (genericPoint X)
  let s := fun σ : Ω ≃ₐ[X.functionField] Ω => FiniteEtale.fundamentalGroupHom q η
    (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
  let α : A ⟶ A := AddCommGrpCat.ofHom
    (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive
  let c := quotientCohomologyEquiv M n j hj hn ξ (Additive.ofMul (QuotientGroup.mk u))
  let P := constantCohomologyPullback θ.hom A 1 c
  apply finiteH1_ext_genericFieldAction X Ω A
  intro ρ'
  obtain ⟨ρ, rfl⟩ := (KummerTheory.semilinearGaloisConjugateEquiv τ a ha).surjective ρ'
  let σ := KummerTheory.semilinearGaloisConjugate τ a ha ρ
  have hc := congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => χ (s σ))
    (h1Character_naturality α ξ P)
  have hp := h1Character_semilinearSourcePullback q θ.hom τ a ha hpoint A c ρ
  change h1Character A ξ P (s σ) = h1Character A ξ c (s ρ) at hp
  change h1Character A ξ
      (quotientCohomologyEquiv M n j hj hn ξ (Additive.ofMul (QuotientGroup.mk u'))) (s σ) =
    h1Character A ξ (Sheaf.H.map
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α) 1 P) (s σ)
  rw [← hc, h1Character_openKummer]
  change kummerMonodromyCharacter M (M.openBoundaryPlaces j) n u' j hj
      (M.place_not_mem_openBoundaryPlaces j) hn ξ (s σ) =
    restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)
      (h1Character A ξ P (s σ))
  rw [hp, h1Character_openKummer]
  apply rootsOfUnity.coe_injective
  exact kummerMonodromyCharacter_generic_semilinear M (M.openBoundaryPlaces j) n j hj
    (M.place_not_mem_openBoundaryPlaces j) hn g τ hfield a ha u u' hu' ρ

/-- The finite residue of coefficient transport of actual pullback is the
original residue at the original place. The place action is retained literally. -/
theorem finiteResidue_semilinearPullback
    (θ : X ≅ X) (g : SemilinearAut K F)
    (hfield : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion
      (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)))
    (hboundary : ∀ p : Place K F,
      p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j)
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (c : FiniteKummerH1 K X n) (v : M.openBoundaryPlaces j) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    finiteResidue M n j hj hn ξ
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (AddCommGrpCat.ofHom
            (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive)) 1
          (constantCohomologyPullback θ.hom
            (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c))
        ⟨g • v.val, (hboundary v.val).mp v.property⟩ =
      finiteResidue M n j hj hn ξ c v := by
  intro ξ
  obtain ⟨z, rfl⟩ := (quotientCohomologyEquiv M n j hj hn ξ).surjective c
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective z.toMul
  have hz : z = Additive.ofMul (QuotientGroup.mk u) := hu.symm
  rw [hz]
  obtain ⟨u', hu'⟩ := Pic0.exists_openKummerUnit_semilinear
    (M.openBoundaryPlaces j) (M.openBoundaryPlaces j) n g hboundary u
  rw [← openKummerCohomology_semilinearPullback M n j hj hn θ g hfield u u' hu',
    finiteResidue_comparison, finiteResidue_comparison]
  change ((g • v.val).ord (u'.val : F) : ZMod (n : ℕ)) =
    (v.val.ord (u.val : F) : ZMod (n : ℕ))
  rw [hu']
  exact congrArg (fun z : ℤ => (z : ZMod (n : ℕ)))
    (SemilinearAut.ord_smul g v.val (u.val : F))

/-- Positive coefficient Frobenius contributes exactly its cardinality
scalar to the original finite boundary residue square. -/
theorem finiteResidue_arithmeticFrobeniusPullback
    (k : Type u) [Field k] [Fintype k] [Algebra k K] [Algebra.IsAlgebraic k K]
    (r : ℕ) (θ : X ≅ X) (g : SemilinearAut K F)
    (hfield : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion
      (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)))
    (hboundary : ∀ p : Place K F,
      p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j)
    (hg : SemilinearAut.baseAut g =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingEquiv)
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (c : FiniteKummerH1 K X n) (v : M.openBoundaryPlaces j) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    Fintype.card k ^ r •
        finiteResidue M n j hj hn ξ
          (constantCohomologyPullback θ.hom
            (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c)
          ⟨g • v.val, (hboundary v.val).mp v.property⟩ =
      finiteResidue M n j hj hn ξ c v := by
  intro ξ
  have h := finiteResidue_semilinearPullback M n j hj hn θ g hfield hboundary
    (Ω := Ω) c v
  change finiteResidue M n j hj hn ξ
      (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom
          (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive)) 1
        (constantCohomologyPullback θ.hom
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c))
      ⟨g • v.val, (hboundary v.val).mp v.property⟩ =
    finiteResidue M n j hj hn ξ c v at h
  rw [hg, EtaleCohomology.Classical.rootsCohomology_frobeniusPower_coefficient,
    map_nsmul] at h
  exact h

end AnabelianGeometry.FiniteField
