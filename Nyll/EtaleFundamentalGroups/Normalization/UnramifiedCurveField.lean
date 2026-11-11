/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.EtaleOfRamification
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.AlgebraicCurves.Models.FunctionFields.FiniteFlatHomAlgHom
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalFieldSourceGeneric
public import Nyll.SchemeTheory.Normalization.GenericFiber.GenericExtension
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# The actual normalization in an unramified curve field

The finite extension is retained as a literal field. Its smooth proper model
has a finite flat map extending the original field inclusion. The local
ramification criterion proves this map étale, and the normalization universal
property identifies that model with the normalization in the original field.
Both the base map and the specified generic field source are preserved.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped IntermediateField

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem transport_normalization_model
    {A B N : Scheme.{u}} (g q : A ⟶ B)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact q] [QuasiSeparated q]
    (h : g = q) (d : N ⟶ B) (p : A ⟶ N)
    (e : g.normalization ≅ N)
    (he : e.hom ≫ d = g.fromNormalization)
    (hep : g.toNormalization ≫ e.hom = p) :
    ∃ e' : q.normalization ≅ N, e'.hom ≫ d = q.fromNormalization ∧
      q.toNormalization ≫ e'.hom = p := by
  subst q
  exact ⟨e, he, hep⟩

/-- The finite étale model of an everywhere-unramified finite separable
extension is the original normalization, including its original generic map.
The finite transcendence presentation is used only to construct the curve
model; the map and its étaleness are proved internally. -/
theorem exists_finiteEtale_normalization_model_of_ramificationIndex_eq_one
    {k K L : Type u} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (M : CurveModel k K)
    (hfg : ∃ t : L, Transcendental k t ∧ FiniteDimensional k⟮t⟯ L)
    (hunramified : ∀ w : Place k L, w.ramificationIndex K = 1) :
    let _ : Algebra M.C.functionField L :=
      ((algebraMap K L).comp M.ffEquiv.symm.toRingHom).toAlgebra
    ∃ (N : CurveModel k L) (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Etale d ∧
      ∃ e : (M.C.genericExtensionMorphism L).normalization ≅ N.C,
        e.hom ≫ d = (M.C.genericExtensionMorphism L).fromNormalization ∧
        (M.C.genericExtensionMorphism L).toNormalization ≫ e.hom =
          Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
            N.C.fromSpecStalk (genericPoint N.C) := by
  intro algML
  obtain ⟨N⟩ := CurveModel.nonempty_of_perfectField k L hfg
  let φ : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
  have hφ : φ.toRingHom.IsIntegral := fun a =>
    Algebra.IsIntegral.isIntegral (R := K) a
  have hfiniteAlong : FiniteAlong k φ := by
    change let _ : Algebra K L := (algebraMap K L).toAlgebra; Module.Finite K L
    rw [toAlgebra_algebraMap]
    infer_instance
  obtain ⟨d, hd, hfinite, hflat, hfp, _, hgeneric, _, _⟩ :=
    M.exists_finite_flat_hom_of_algHom N φ hφ hfiniteAlong
  have : IsFinite d := hfinite
  have : Flat d := hflat
  have : LocallyOfFinitePresentation d := hfp
  have hetale : Etale d :=
    M.finiteFlat_etale_of_ramificationIndex_eq_one N d hgeneric hunramified
  have : Smooth N.toBase := SmoothOfRelativeDimension.smooth 1 N.toBase
  have : IsIntegrallyClosed Γ(Spec (.of k), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral N.C := IsNormalIntegral.of_stalks N.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk N.toBase x).2)
  let eF := Scheme.Spec.mapIso N.ffEquiv.symm.toCommRingCatIso.op
  let η := N.C.fromSpecStalk (genericPoint N.C)
  have : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint N.C.functionField,
      Scheme.fromSpecStalk_closedPoint (X := N.C) (x := genericPoint N.C)⟩
  let p : Spec (.of L) ⟶ N.C := eF.hom ≫ η
  have : IsDominant p := by dsimp only [p]; infer_instance
  have : IsPreimmersion p := by dsimp only [p, η]; infer_instance
  have hp : p ≫ d = M.C.genericExtensionMorphism L := by
    change (Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
      N.C.fromSpecStalk (genericPoint N.C)) ≫ d = _
    rw [Category.assoc, hgeneric, ← Category.assoc, ← Spec.map_comp]
    have hcancel : CommRingCat.ofHom
        (N.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) ≫
          CommRingCat.ofHom N.ffEquiv.symm.toRingHom =
        CommRingCat.ofHom (algebraMap M.C.functionField L) := by
      apply CommRingCat.hom_ext
      ext a
      exact N.ffEquiv.symm_apply_apply _
    exact congrArg (fun a : CommRingCat.of M.C.functionField ⟶ CommRingCat.of L =>
      Spec.map a ≫ M.C.fromSpecStalk (genericPoint M.C)) hcancel
  obtain ⟨e, he, hep⟩ := transport_normalization_model (p ≫ d)
    (M.C.genericExtensionMorphism L) hp d p
    (finiteNormalFieldSourceIso d p)
    (finiteNormalFieldSourceIso_hom_fromNormalization d p)
    (toNormalization_finiteNormalFieldSourceIso_hom d p)
  exact ⟨N, d, hd, hfinite, hetale, e, he, hep⟩

/-- Everywhere-unramified finite separable curve fields give actual finite
étale normalizations. Connectedness is supplied by the same integral model. -/
theorem finiteEtale_normalization_of_ramificationIndex_eq_one
    {k K L : Type u} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (M : CurveModel k K)
    (hfg : ∃ t : L, Transcendental k t ∧ FiniteDimensional k⟮t⟯ L)
    (hunramified : ∀ w : Place k L, w.ramificationIndex K = 1) :
    let _ : Algebra M.C.functionField L :=
      ((algebraMap K L).comp M.ffEquiv.symm.toRingHom).toAlgebra
    IsIntegral (M.C.genericExtensionMorphism L).normalization ∧
      IsFiniteEtale (M.C.genericExtensionMorphism L).fromNormalization := by
  intro algML
  obtain ⟨N, d, _, hfinite, hetale, e, he, _⟩ :=
    exists_finiteEtale_normalization_model_of_ramificationIndex_eq_one
      M hfg hunramified
  have : IsFinite d := hfinite
  have : Etale d := hetale
  refine ⟨IsIntegral.of_isIso e.inv, ?_⟩
  rw [← he]
  exact ⟨⟩

end EtaleFundamentalGroups
