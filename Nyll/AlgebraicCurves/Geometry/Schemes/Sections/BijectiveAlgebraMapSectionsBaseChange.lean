/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafOfModules
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Cohomology.Cech.Comparison.BaseChangeEquiv
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.DZeroModulesEqZeroIffUnique
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Vanishing.SectionsTopEquivH0Modules

/-!
# Global sections after base change from a field

Degree-zero Cech cohomology computes global sections and supplies the base-change
comparison used in the final statement.
-/

@[expose] public section

open _root_.AlgebraicGeometry.OModulePresheaf
  (sectionsEquivH0)

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  TensorProduct

namespace P2mH0BaseChangeField

section Transport

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M N : V.Modules}

/-- The linear equivalence on global sections induced by a module isomorphism. -/
def sectionsEquivOfIso (e : M ≅ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π N ⊤
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
  let := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π N ⊤
  { toFun := fun x => Scheme.Modules.Hom.app e.hom ⊤ x
    invFun := fun y => Scheme.Modules.Hom.app e.inv ⊤ y
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      change Scheme.Modules.Hom.app e.hom ⊤ ((algebraMap R Γ(V, ⊤) r) • x)
        = (algebraMap R Γ(V, ⊤) r) • Scheme.Modules.Hom.app e.hom ⊤ x
      exact Scheme.Modules.Hom.app_smul _ _ _
    left_inv := fun x => by
      change (Scheme.Modules.Hom.app e.hom ⊤ ≫ Scheme.Modules.Hom.app e.inv ⊤) x = x
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    right_inv := fun y => by
      change (Scheme.Modules.Hom.app e.inv ⊤ ≫ Scheme.Modules.Hom.app e.hom ⊤) y = y
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

/-- Global sections of the unit module identify with functions on the scheme. -/
def unitSectionsEquiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit V.ringCatSheaf) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
    Γ(SheafOfModules.unit V.ringCatSheaf, ⊤) ≃ₗ[R] Γ(V, ⊤) :=
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit V.ringCatSheaf) ⊤
  let := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  { toFun := fun x => (show Γ(V, ⊤) from x)
    invFun := fun y => (show Γ(SheafOfModules.unit V.ringCatSheaf, ⊤) from y)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end Transport

theorem bijective_algebraMap_of_linearEquiv {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (e : S ≃ₗ[A] A) : Function.Bijective (algebraMap A S) := by
  set u : S := e.symm 1 with hu
  have hgen : ∀ s : S, s = e s • u := fun s => by
    rw [hu, ← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  set b : A := e 1
  set a : A := e (u * u)
  have hba : b * a = 1 := by
    have h1 : u = (b * a) • u := by
      calc u = u * 1 := (mul_one u).symm
        _ = u * (b • u) := by rw [← hgen 1]
        _ = b • (u * u) := by rw [mul_smul_comm]
        _ = b • (a • u) := by rw [← hgen (u * u)]
        _ = (b * a) • u := by rw [mul_smul]
    have h2 : (1 - b * a) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    have h3 : (1 - b * a) • e u = 0 := by rw [← LinearEquiv.map_smul, h2, map_zero]
    have h4 : e u = 1 := by rw [hu, LinearEquiv.apply_symm_apply]
    rw [h4, smul_eq_mul, mul_one] at h3
    exact (sub_eq_zero.mp h3).symm
  have hbu : IsUnit b := IsUnit.of_mul_eq_one a hba
  have halg : ∀ r : A, algebraMap A S r = (r * b) • u := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← hgen 1]
  constructor
  · intro r r' h
    rw [halg, halg] at h
    have h' := congrArg e h
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, hu, LinearEquiv.apply_symm_apply, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one] at h'
    exact hbu.mul_left_injective h'
  · intro s
    refine ⟨e s * hbu.unit⁻¹, ?_⟩
    rw [halg, mul_assoc, IsUnit.val_inv_mul, mul_one, ← hgen s]

section Main

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem main (k : Type u) [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [QuasiCompact π]
    (hX : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap k Γ(X, ⊤)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback π (Scheme.TwoAffineOpenCover.specMap k A),
      ⊤)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  let 𝒰 := _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.ofCompact X
  let 𝒪 : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let p₁ := Limits.pullback.fst π (specMap k A)
  let p₂ := Limits.pullback.snd π (specMap k A)
  have htriv : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒪 ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
        :=
    fun x => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩
  obtain ⟨-, hflat⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial π 𝒰 𝒪
    htriv A
  obtain ⟨⟨e1⟩, -⟩ := hflat inferInstance
  let := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π 𝒪 ⊤
  let := Scheme.TwoAffineOpenCover.algebraOfHom p₂ ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ ((Scheme.Modules.pullback p₁).obj 𝒪) ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂
    (SheafOfModules.unit (Limits.pullback π (specMap k A)).ringCatSheaf) ⊤
  let e2 : (OModulePresheaf.ofModules π 𝒪).H0 𝒰 ≃ₗ[k] k :=
    (sectionsEquivH0 π 𝒪 𝒰).symm.trans ((unitSectionsEquiv π).trans
      (LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) hX).symm)
  let e3 : A ⊗[k] (OModulePresheaf.ofModules π 𝒪).H0 𝒰 ≃ₗ[A] A :=
    (e2.baseChange k A _ _).trans (AlgebraTensorModule.rid k A A)
  let e4 := (sectionsEquivH0 p₂
    ((Scheme.Modules.pullback p₁).obj 𝒪) (𝒰.baseChange π A)).symm.trans
    ((sectionsEquivOfIso p₂ (Scheme.Modules.pullbackUnitIso p₁)).trans (unitSectionsEquiv p₂))
  exact bijective_algebraMap_of_linearEquiv (e4.symm.trans (e1.trans e3))

end Main

end P2mH0BaseChangeField

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem
  _root_.AlgebraicGeometry.Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field
    (k : Type u) [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated π] [QuasiCompact π]
    (hX : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap k Γ(X, ⊤)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback π (Scheme.TwoAffineOpenCover.specMap k A),
      ⊤)) :=
  P2mH0BaseChangeField.main k π hX A
end Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
