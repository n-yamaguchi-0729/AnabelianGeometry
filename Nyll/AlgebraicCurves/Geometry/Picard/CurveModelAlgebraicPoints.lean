/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Basic
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Algebraic points realizing the degree-zero divisor class group

The actual Picard and Abel--Jacobi existence theorems give a smooth proper
commutative group scheme and an additive equivalence from `Pic0` to its
algebraic points. Its actual relative dimension is retained together with
the group law, so finite torsion and Tate-basis theorems use the same
geometric construction.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace AlgebraicCurve.CurveModel

/-- A pointed proper curve supplies an actual abelian scheme whose algebraic
point group is its degree-zero divisor class group, together with its
relative dimension. No representation is assumed in the input. -/
theorem exists_pic0_addEquiv_abelianPoints
    {K F : Type u} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    ∃ (A : Scheme.{u}) (f : A ⟶ Spec (.of K)) (G : RelativeGroupLaw K f)
      (hc : G.IsCommutative) (d : ℕ),
      AbelianSchemePropertyBundle K f ∧ SmoothOfRelativeDimension d f ∧
        Nonempty (Pic0 K F ≃+ G.AlgPoints hc K) := by
  have : IsProper M.toBase := M.isProper
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  obtain ⟨D, ⟨hD⟩, hs, hp, hg⟩ :=
    exists_representsRelSubPic_of_field K M.toBase ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hg
  obtain ⟨aj, _, hclass⟩ :=
    exists_abelJacobi_of_representsRelSubPic K M.toBase ε D hD
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M.toBase ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M.toBase ε) hD
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    { smooth := hs
      proper := hp
      connectedFibres := fun x => D.toBase.isConnected_preimage_singleton x
      hasGroupLaw := ⟨G⟩ }
  obtain ⟨d, hd⟩ := G.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  let b : Spec (.of K) ⟶ Spec (.of K) := specMap K K
  have hb : b = 𝟙 (Spec (.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have : IsIso b := by rw [hb]; infer_instance
  let eC : M.C ≅ pullback M.toBase b := (asIso (pullback.fst M.toBase b)).symm
  have heC : eC.hom ≫ pullback.snd M.toBase b = M.toBase := by
    change inv (pullback.fst M.toBase b) ≫ pullback.snd M.toBase b = M.toBase
    apply (cancel_mono b).1
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc,
      hb, Category.comp_id]
  obtain ⟨e, _, _⟩ :=
    JacobianVarieties.Picard.exists_pic0_algPoints_equivariant_of_abelJacobi
      M.toBase ε D hD aj hclass M eC heC
  exact ⟨D.P, D.toBase, G, hc, d, hA, hd, ⟨e⟩⟩

end AlgebraicCurve.CurveModel
