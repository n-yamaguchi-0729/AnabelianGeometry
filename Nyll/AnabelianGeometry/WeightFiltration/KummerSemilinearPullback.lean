/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.SemilinearSourcePullback
public import Nyll.AlgebraicCurves.Models.Kummer.SemilinearGenericCharacter
public import Nyll.SchemeTheory.FunctionFields.GenericSourceIso
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Naturality
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Semilinear naturality of the original proper Kummer cohomology map

An actual scheme automorphism supplies its generic source lift. The proved
semilinear root-character identity then determines the actual derived H¹
class. The coefficient automorphism is explicit: arithmetic Frobenius gives
the cardinality scalar, while scheme pullback has the inverse orientation.

-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

variable {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]

private theorem h1Character_kummerTorsion
    (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ M.C) (x : Pic0.torsion K F n) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ
        (M.kummerTorsionCohomology n hn ξ x) =
      M.kummerTorsionCharacter n hn ξ (Multiplicative.ofAdd x) := by
  intro topology discrete
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact congrArg Additive.toMul ((finiteH1CharacterEquiv A ξ).apply_symm_apply
    (Additive.ofMul (M.kummerTorsionCharacter n hn ξ (Multiplicative.ofAdd x))))

/-- The original Kummer class of a semilinearly transported Picard class is
coefficient transport of the actual scheme pullback of its original class.
The generic source lift is constructed from the given scheme automorphism. -/
theorem properKummerCohomology_semilinearPullback
    (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hθ : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z) =
      M.ffEquiv (SemilinearAut.toRingAut g z))
    {Ω : Type uGeom} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (x : Pic0.torsion K F n) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    M.kummerTorsionCohomology n hn ξ (g • x) =
      Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{uGeom}).map
        (AddCommGrpCat.ofHom
          (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive)) 1
        (constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn ξ x)) := by
  intro ξ A
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (CommRingCat.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  obtain ⟨a, ha, hpoint⟩ := exists_genericPoint_sourceIso θ Ω
  let τ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
  let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
  let q := M.C.fromSpecStalk (genericPoint M.C)
  let j := fun σ : Ω ≃ₐ[M.C.functionField] Ω => FiniteEtale.fundamentalGroupHom q η
    (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ)
  let α : A ⟶ A := AddCommGrpCat.ofHom
    (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive
  let c := M.kummerTorsionCohomology n hn ξ x
  let P := constantCohomologyPullback θ.hom A 1 c
  apply finiteH1_ext_genericFieldAction M.C Ω A
  intro ρ'
  obtain ⟨ρ, rfl⟩ := (KummerTheory.semilinearGaloisConjugateEquiv τ a ha).surjective ρ'
  let σ := KummerTheory.semilinearGaloisConjugate τ a ha ρ
  have hc := congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => χ (j σ))
    (h1Character_naturality α ξ P)
  have hp := h1Character_semilinearSourcePullback q θ.hom τ a ha hpoint A c ρ
  change h1Character A ξ P (j σ) = h1Character A ξ c (j ρ) at hp
  change h1Character A ξ (M.kummerTorsionCohomology n hn ξ (g • x)) (j σ) =
    h1Character A ξ (Sheaf.H.map
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{uGeom}).map α) 1 P) (j σ)
  rw [← hc, h1Character_kummerTorsion]
  change M.kummerTorsionCharacter n hn ξ (Multiplicative.ofAdd (g • x)) (j σ) =
    restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)
      (h1Character A ξ P (j σ))
  rw [hp, h1Character_kummerTorsion]
  apply rootsOfUnity.coe_injective
  exact M.kummerTorsionCharacter_generic_semilinear n hn g τ hθ a ha x ρ

end AnabelianGeometry.FiniteField
