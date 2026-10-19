/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldComparisonAlignment
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint

/-!
# Coefficient embeddings aligned with the actual arithmetic comparison

Every comparison between the field fiber functors is induced by an embedding
of the fixed separable closure into the actual algebraically closed point field.
The embedding is chosen before the geometric model and before any cusp labels.
Consequently its source actions have their literal arithmetic Galois labels,
without a later conjugation of a recovered cusp correspondence.
-/

noncomputable section
open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

universe u

private theorem fieldFiberExtension_point_at_eq
    (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [AκΩ : Algebra κ Ω] [AkΩ : Algebra k Ω]
    [tower : IsScalarTower k κ Ω] [IsSepClosed κ] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of k)) (hz : z = ξ k Ω)
    (A : FiniteEtale (Spec (.of k))) (x : (fib k κ).obj A) :
    (fiberObjEquivHom z A
      (((fieldFiberExtensionIso k κ Ω) ≪≫
        (eqToIso (congrArg fiber hz)).symm).hom.app A x)).left =
      ξ κ Ω ≫ (fiberObjEquivHom (ξ k κ) A x).left := by
  subst z
  exact fieldFiberExtensionIso_point k κ Ω A x

/-- Realize the specified fiber comparison by an actual coefficient embedding.
The chosen embedding accounts for the entire comparison, not just its action
on one finite subfield. -/
theorem exists_fieldEmbedding_realizing_fiberIso
    (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [IsSepClosure k κ] [IsSepClosed κ]
    [IsAlgClosed Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of k)) (t : fiber z ≅ fib k κ) :
    let _AkΩ : Algebra k Ω := (Spec.preimage z).hom.toAlgebra
    ∃ j : κ →ₐ[k] Ω,
      let _AκΩ : Algebra κ Ω := j.toRingHom.toAlgebra
      let _hkκΩ : IsScalarTower k κ Ω :=
        IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
      let hz : z = ξ k Ω := (Spec.map_preimage z).symm
      fieldFiberExtensionIso k κ Ω ≪≫ (eqToIso (congrArg fiber hz)).symm = t.symm := by
  intro AkΩ
  let j₀ : κ →ₐ[k] Ω := IsAlgClosed.lift
  let AκΩ₀ : Algebra κ Ω := j₀.toRingHom.toAlgebra
  let hkκΩ₀ : IsScalarTower k κ Ω :=
    IsScalarTower.of_algebraMap_eq (fun a => (j₀.commutes a).symm)
  let hz : z = ξ k Ω := (Spec.map_preimage z).symm
  let S := fieldFiberExtensionIso k κ Ω ≪≫ (eqToIso (congrArg fiber hz)).symm
  let δ : Aut (fib k κ) := t.symm ≪≫ S.symm
  let ε := suppliedGaloisEquivFundamentalGroup k κ
  let σ := ε.symm δ
  have hσ : ε σ = δ := ε.apply_symm_apply δ
  have hfactor : ε σ ≪≫ S = t.symm := by
    rw [hσ]
    apply Iso.ext
    change (t.inv ≫ S.inv) ≫ S.hom = t.inv
    rw [Category.assoc, S.inv_hom_id, Category.comp_id]
  let j : κ →ₐ[k] Ω := j₀.comp σ.toAlgHom
  refine ⟨j, ?_⟩
  intro AκΩ hkκΩ hz'
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply FintypeCat.hom_ext
  intro x
  apply (fiberObjEquivHom z A).injective
  apply Over.OverMorphism.ext
  have hnew := fieldFiberExtension_point_at_eq k κ Ω z hz' A x
  have hold := fieldFiberExtension_point_at_eq k κ Ω
    (AκΩ := AκΩ₀) (AkΩ := AkΩ) (tower := hkκΩ₀) z hz A ((ε σ).hom.app A x)
  have hact := AlgebraicGeometry.FiniteEtale.suppliedGaloisEquivFundamentalGroup_point k κ σ A x
  have hval : S.hom.app A ((ε σ).hom.app A x) = t.inv.app A x :=
    congrArg (fun e : fib k κ ≅ fiber z => e.hom.app A x) hfactor
  calc
    (fiberObjEquivHom z A
      (((fieldFiberExtensionIso k κ Ω) ≪≫
        (eqToIso (congrArg fiber hz')).symm).hom.app A x)).left =
        Spec.map (CommRingCat.ofHom j.toRingHom) ≫
          (fiberObjEquivHom (ξ k κ) A x).left := hnew
    _ = Spec.map (CommRingCat.ofHom j₀.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          (fiberObjEquivHom (ξ k κ) A x).left) := by
      change Spec.map (CommRingCat.ofHom (j₀.toRingHom.comp σ.toRingHom)) ≫ _ = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom j₀.toRingHom) ≫
        (fiberObjEquivHom (ξ k κ) A ((ε σ).hom.app A x)).left :=
      congrArg (fun q => Spec.map (CommRingCat.ofHom j₀.toRingHom) ≫ q) hact.symm
    _ = (fiberObjEquivHom z A (S.hom.app A ((ε σ).hom.app A x))).left := hold.symm
    _ = (fiberObjEquivHom z A (t.inv.app A x)).left :=
      congrArg (fun y => (fiberObjEquivHom z A y).left) hval

/-- Choose the coefficient embedding from the comparison defining the original
arithmetic quotient. Every actual source action then has its coefficient label
exactly, with no inner correction. -/
theorem exists_arithmeticAlignedCoefficientEmbedding
    (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [IsSepClosure k κ] [IsSepClosed κ]
    [IsAlgClosed Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (xi : Spec (.of Ω) ⟶ X) :
    let _AkΩ : Algebra k Ω := (Spec.preimage (xi ≫ f)).hom.toAlgebra
    ∃ j : κ →ₐ[k] Ω,
      let _AκΩ : Algebra κ Ω := j.toRingHom.toAlgebra
      let _hkκΩ : IsScalarTower k κ Ω :=
        IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
      let hbase : xi ≫ f = ξ k Ω := (Spec.map_preimage (xi ≫ f)).symm
      let t := (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
      (fieldFiberExtensionIso k κ Ω ≪≫
        (eqToIso (congrArg fiber hbase)).symm = t.symm) ∧
      ∀ (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
        (_he : e.hom = Spec.map (CommRingCat.ofHom ρ)) (σ : Gal(κ/k))
        (_hρ : ρ.comp (algebraMap κ Ω) = (algebraMap κ Ω).comp σ.toRingHom)
        (hsource : e.hom ≫ xi = xi),
        arithmeticFundamentalGroupHom k κ f xi
          (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)) = σ := by
  intro AkΩ
  let t := (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
  obtain ⟨j, hj⟩ := exists_fieldEmbedding_realizing_fiberIso k κ Ω (xi ≫ f) t
  refine ⟨j, ?_⟩
  intro AκΩ hkκΩ hbase t'
  have hreal : fieldFiberExtensionIso k κ Ω ≪≫
      (eqToIso (congrArg fiber hbase)).symm = t.symm := hj
  refine ⟨hreal, ?_⟩
  intro e ρ he σ hρ hsource
  let E := fieldFiberExtensionIso k κ Ω
  let q := eqToIso (congrArg fiber hbase)
  let ε := suppliedGaloisEquivFundamentalGroup k κ
  let g : Aut (fiber xi) := fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)
  have ht : q ≪≫ E.symm = t := congrArg Iso.symm hreal
  have hfield := fundamentalGroupHom_sourceAction_eq_extendedGalois
    k κ Ω f xi e ρ he σ hρ hsource hbase
  have hc : t.conjAut (fundamentalGroupHom f xi g) = ε σ := by
    rw [← ht, Iso.trans_conjAut, hfield]
    change E.symm.conjAut (E.conjAut (ε σ)) = ε σ
    apply Aut.ext
    simp only [Iso.conjAut_hom, Iso.symm_self_conj]
  change ε.symm (t.conjAut (fundamentalGroupHom f xi g)) = σ
  rw [hc, ε.symm_apply_apply]

/-- With the aligned coefficient embedding, the native constant-cover point
is the literal restriction of that embedding to E. This uses the same point
as arithmeticConstantFieldCoverGroupTransport. -/
theorem arithmeticConstantFieldLift_coefficient_eq_of_alignedComparison
    (k E κ Ω : Type u) [Field k] [Field E] [Field κ] [Field Ω]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ] [IsSepClosed Ω]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    [Algebra κ Ω] [Algebra k Ω] [IsScalarTower k κ Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (xi : Spec (.of Ω) ⟶ X)
    (hbase : xi ≫ f = ξ k Ω)
    (halign : fieldFiberExtensionIso k κ Ω ≪≫
      (eqToIso (congrArg fiber hbase)).symm =
        ((nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some).symm) :
    arithmeticConstantFieldLift k E κ f xi ≫
        Limits.pullback.fst (originalConstantFieldCover k E).hom f =
      ξ κ Ω ≫ Spec.map (CommRingCat.ofHom (algebraMap E κ)) := by
  let A := originalConstantFieldCover k E
  let P := pullbackFiberIso f xi
  let t := (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
  let x := originalInclusionConstantFiberPoint k E κ
  let w := arithmeticConstantFieldFiberPoint k E κ f xi
  have hw : P.hom.app A w = t.inv.app A x := by
    change P.hom.app A (P.inv.app A (t.inv.app A x)) = t.inv.app A x
    exact FintypeCat.inv_hom_id_apply (P.app A) (t.inv.app A x)
  have hpoint := fieldFiberExtension_point_at_eq k κ Ω (xi ≫ f) hbase A x
  have hval :
      (fieldFiberExtensionIso k κ Ω ≪≫
        (eqToIso (congrArg fiber hbase)).symm).hom.app A x = t.inv.app A x :=
    congrArg (fun e : fib k κ ≅ fiber (xi ≫ f) => e.hom.app A x) halign
  have hp := pullbackFiberIso_hom_fiberObjEquivHom_left
    (f := f) (xi := xi) (A := A) (y := w)
  have hlast : ξ κ Ω ≫ (fiberObjEquivHom (ξ k κ) A x).left =
      ξ κ Ω ≫ Spec.map (CommRingCat.ofHom (algebraMap E κ)) := by
    change ξ κ Ω ≫ (fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)
      (originalInclusionConstantFiberPoint k E κ)).left = _
    rw [originalInclusionConstantFiberPoint_hom]
    rfl
  exact hp.symm.trans
    ((congrArg (fun y => (fiberObjEquivHom (xi ≫ f) A y).left) hw).trans
      (((congrArg (fun y => (fiberObjEquivHom (xi ≫ f) A y).left) hval.symm).trans
        hpoint).trans hlast))

/-- The exact source-action formula for an already aligned coefficient
embedding. This is the form used after constructing a geometric generic point
from the embedding chosen above. -/
theorem arithmeticFundamentalGroupHom_sourceAction_of_alignedComparison
    (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [IsSepClosure k κ] [IsSepClosed κ]
    [Algebra κ Ω] [Algebra k Ω] [IsScalarTower k κ Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (xi : Spec (.of Ω) ⟶ X)
    (hbase : xi ≫ f = ξ k Ω)
    (halign : fieldFiberExtensionIso k κ Ω ≪≫
      (eqToIso (congrArg fiber hbase)).symm =
        ((nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some).symm)
    (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
    (he : e.hom = Spec.map (CommRingCat.ofHom ρ)) (σ : Gal(κ/k))
    (hρ : ρ.comp (algebraMap κ Ω) = (algebraMap κ Ω).comp σ.toRingHom)
    (hsource : e.hom ≫ xi = xi) :
    arithmeticFundamentalGroupHom k κ f xi
      (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)) = σ := by
  let t := (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
  let E := fieldFiberExtensionIso k κ Ω
  let q := eqToIso (congrArg fiber hbase)
  let ε := suppliedGaloisEquivFundamentalGroup k κ
  let g : Aut (fiber xi) := fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)
  have ht : q ≪≫ E.symm = t := congrArg Iso.symm halign
  have hfield := fundamentalGroupHom_sourceAction_eq_extendedGalois
    k κ Ω f xi e ρ he σ hρ hsource hbase
  have hc : t.conjAut (fundamentalGroupHom f xi g) = ε σ := by
    rw [← ht, Iso.trans_conjAut, hfield]
    change E.symm.conjAut (E.conjAut (ε σ)) = ε σ
    apply Aut.ext
    simp only [Iso.conjAut_hom, Iso.symm_self_conj]
  change ε.symm (t.conjAut (fundamentalGroupHom f xi g)) = σ
  rw [hc, ε.symm_apply_apply]

end AnabelianGeometry.WeightFiltration
