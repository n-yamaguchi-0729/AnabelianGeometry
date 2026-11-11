/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldHilbert90
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Nyll.EtaleCohomology.Sites.FieldFiniteEtaleBasis
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Hilbert 90 at field-valued étale objects

The actual restriction comparison transports the existing geometric Hilbert 90
to a field-valued object of any small étale site. Vanishing of degree-one
cohomology also supplies actual lifts of sections in a short exact sequence.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.Abelian

namespace EtaleCohomology

/-- Actual unit-sheaf H1 vanishes at an étale object which is a field spectrum. -/
theorem etaleMultiplicativeGroup_H1_eq_zero_at_field
    {X : Scheme.{u}} (L : Type u) [Field L]
    (f : Spec (.of L) ⟶ X) [Etale f]
    (a : Sheaf.H'.{u} (etaleMultiplicativeGroupSheaf X) 1 (Scheme.Etale.mk f)) :
    a = 0 := by
  let er := etaleCohomologyPresheafRestrictionEquiv (Scheme.Etale.mk f)
    (etaleMultiplicativeGroupSheaf X) 1
  let ec := (Sheaf.functorH (Spec (.of L)).smallEtaleTopology 1).mapIso
    (etaleRestrictionMultiplicativeGroupIso f)
  let e := er.trans ec.addCommGroupIsoToAddEquiv
  apply e.injective
  rw [e.map_zero]
  exact etaleMultiplicativeGroup_H1_eq_zero_of_field L (e a)

/-- Vanishing at an actual étale object makes quotient sections lift. -/
theorem exists_section_lift_of_H1_eq_zero
    (X : Scheme.{u})
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) (V : X.Etale)
    (h : ∀ a : Sheaf.H'.{u} S.X₁ 1 V, a = 0)
    (q : S.X₃.obj.obj (op V)) :
    ∃ b : S.X₂.obj.obj (op V), S.g.hom.app (op V) b = q := by
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let a : P ⟶ S.X₃ :=
    (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₃).symm q
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ a) rfl (h _)
  obtain ⟨b', rfl⟩ := (Ext.mk₀_bijective P S.X₂).surjective b
  have he : b' ≫ S.g = a := by
    apply (Ext.mk₀_bijective P S.X₃).injective
    rw [Ext.mk₀_comp_mk₀] at hb
    exact hb
  refine ⟨freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V S.X₂ b', ?_⟩
  rw [← freeAbelianSheafYonedaHomEquiv_postcomp, he, Equiv.apply_symm_apply]

/-- Sections of a short exact sequence with actual unit-sheaf kernel lift
on every étale object over any field. -/
theorem exists_section_lift_of_units_kernel_at_etale_object_of_field
    (K : Type u) [Field K]
    {B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf (Spec (.of K)) ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (V : (Spec (.of K)).Etale) (q : Q.obj.obj (op V)) :
    ∃ b : B.obj.obj (op V), p.hom.app (op V) b = q := by
  obtain ⟨L, a, e, hfield, hsep, he⟩ := Scheme.Etale.exists_iso_sigmaSpec K V
  have hfinite (x : V.left) : IsFiniteEtale (Spec.map (a x)) := by
    let : Field (L x) := (hfield x).toField
    let : Algebra K (L x) := (a x).hom.toAlgebra
    have : Module.Finite K (L x) := (hsep x).1
    have : Algebra.IsSeparable K (L x) := (hsep x).2
    have : Algebra.FormallyEtale K (L x) :=
      Algebra.FormallyEtale.of_isSeparable K (L x)
    have : Algebra.Etale K (L x) :=
      ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    rw [IsFiniteEtale.SpecMap_iff]
    change (algebraMap K (L x)).FiniteEtale
    rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  let U (x : V.left) : (Spec (.of K)).Etale :=
    MorphismProperty.Over.mk ⊤ (Spec.map (a x)) (by
      have := hfinite x
      infer_instance)
  let eV : etaleSigma U ≅ V := MorphismProperty.Over.isoMk e he
  have hs (x : V.left) : Function.Surjective (p.hom.app (op (U x))) := by
    intro s
    apply exists_section_lift_of_H1_eq_zero (Spec (.of K))
      (ShortComplex.mk i p hz) hS (U x) _ s
    intro b
    let : Field (L x) := (hfield x).toField
    have : Etale (Spec.map (a x)) := by
      have := hfinite x
      infer_instance
    exact etaleMultiplicativeGroup_H1_eq_zero_at_field (L x) (Spec.map (a x)) b
  let T := sheafCompose (Spec (.of K)).smallEtaleTopology (forget AddCommGrpCat.{u})
  obtain ⟨b, hb⟩ := etaleSigma_sections_surjective U (T.map p) hs
    (Q.obj.map eV.hom.op q)
  refine ⟨B.obj.map eV.inv.op b, ?_⟩
  calc
    _ = Q.obj.map eV.inv.op ((T.map p).hom.app (op (etaleSigma U)) b) := by
      exact NatTrans.naturality_apply p.hom eV.inv.op b
    _ = q := by
      rw [hb, ← ConcreteCategory.comp_apply, ← Q.obj.map_comp, ← op_comp,
        eV.inv_hom_id]
      rw [op_id, Q.obj.map_id]
      rfl

/-- Geometric Hilbert 90 holds at every object of the small étale site
of any field, including infinite disjoint unions. -/
theorem etaleMultiplicativeGroup_H1_eq_zero_at_etale_object_of_field
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale)
    (a : Sheaf.H'.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 1 V) :
    a = 0 := by
  let A := etaleMultiplicativeGroupSheaf (Spec (.of K))
  let S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :=
    ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A))
      (cokernel.condition (Injective.ι A))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι A) }
  let P := (freeAbelianSheafYoneda (Spec (.of K)).smallEtaleTopology).obj V
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ P hS a
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨q, hq⟩ := (Ext.mk₀_bijective P S.X₃).surjective b
  obtain ⟨s, hs⟩ := exists_section_lift_of_units_kernel_at_etale_object_of_field K
    S.f S.g S.zero hS V
    (freeAbelianSheafYonedaHomEquiv (Spec (.of K)).smallEtaleTopology V S.X₃ q)
  let f : P ⟶ S.X₂ :=
    (freeAbelianSheafYonedaHomEquiv (Spec (.of K)).smallEtaleTopology V S.X₂).symm s
  have hf : f ≫ S.g = q := by
    apply (freeAbelianSheafYonedaHomEquiv
      (Spec (.of K)).smallEtaleTopology V S.X₃).injective
    rw [freeAbelianSheafYonedaHomEquiv_postcomp]
    change S.g.hom.app (op V)
      (freeAbelianSheafYonedaHomEquiv (Spec (.of K)).smallEtaleTopology V S.X₂
        ((freeAbelianSheafYonedaHomEquiv (Spec (.of K)).smallEtaleTopology
          V S.X₂).symm s)) = _
    rw [Equiv.apply_symm_apply]
    exact hs
  rw [← hb, ← hq, ← hf, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  rfl

end EtaleCohomology
