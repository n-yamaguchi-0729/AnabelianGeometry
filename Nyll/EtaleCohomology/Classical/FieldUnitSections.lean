/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldHilbert90
public import Nyll.EtaleCohomology.Classical.EtaleRestriction

/-!
# Exact unit-kernel sequences on actual field neighborhoods

Hilbert 90 applies on every actual etale field neighborhood, not just at
the terminal object of the original field site. Exact geometric restriction
and its proved unit-sheaf comparison supply the transport.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

/-- On the restriction to an actual etale field, a quotient section of a
short exact sequence with unit-sheaf kernel lifts to a section. -/
theorem exists_restriction_section_lift_of_units_kernel_at_field
    (X : Scheme.{u}) (L : Type u) [Field L]
    (f : Spec (.of L) ⟶ X) [Etale f]
    {B Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf X ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (q : ((etaleRestriction f AddCommGrpCat.{u}).obj Q).obj.obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of L)))))) :
    ∃ b : ((etaleRestriction f AddCommGrpCat.{u}).obj B).obj.obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of L))))),
      ((etaleRestriction f AddCommGrpCat.{u}).map p).hom.app _ b = q := by
  let R := etaleRestriction f AddCommGrpCat.{u}
  let e : R.obj (etaleMultiplicativeGroupSheaf X) ≅
      etaleMultiplicativeGroupSheaf (Spec (.of L)) :=
    etaleRestrictionMultiplicativeGroupIso f
  let i' : etaleMultiplicativeGroupSheaf (Spec (.of L)) ⟶ R.obj B :=
    e.inv ≫ R.map i
  have hz' : i' ≫ R.map p = 0 := by
    change (e.inv ≫ R.map i) ≫ R.map p = 0
    rw [Category.assoc, ← R.map_comp, hz, R.map_zero, comp_zero]
  let S := ShortComplex.mk i p hz
  let S' := ShortComplex.mk i' (R.map p) hz'
  let eS : S.map R ≅ S' := ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by
    change e.hom ≫ (e.inv ≫ R.map i) = R.map i ≫ 𝟙 _
    rw [Iso.hom_inv_id_assoc, Category.comp_id]) (by
    change (𝟙 _) ≫ R.map p = R.map p ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id])
  have hS' : S'.ShortExact :=
    ShortComplex.shortExact_of_iso eS (hS.map_of_exact _)
  exact exists_section_lift_of_units_kernel_of_field L i' (R.map p) hz' hS' q

/-- Actual sections on any etale field neighborhood lift through a
short exact sequence whose kernel is the actual unit sheaf. -/
theorem exists_section_lift_of_units_kernel_at_field
    (X : Scheme.{u}) (L : Type u) [Field L]
    (f : Spec (.of L) ⟶ X) [Etale f]
    {B Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf X ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (q : Q.obj.obj (op (Scheme.Etale.mk f))) :
    ∃ b : B.obj.obj (op (Scheme.Etale.mk f)), p.hom.app _ b = q := by
  let T := Scheme.Etale.mk (𝟙 (Spec (.of L)))
  let V := (etalePostcompose f).obj T
  let e : V ≅ Scheme.Etale.mk f :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by rfl)
  let q' : ((etaleRestriction f AddCommGrpCat.{u}).obj Q).obj.obj (op T) :=
    Q.obj.map e.hom.op q
  obtain ⟨b, hb⟩ := exists_restriction_section_lift_of_units_kernel_at_field
    X L f i p hz hS q'
  refine ⟨B.obj.map e.inv.op b, ?_⟩
  have hn := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (p.hom.naturality e.inv.op) b
  change p.hom.app (op (Scheme.Etale.mk f)) (B.obj.map e.inv.op b) =
    Q.obj.map e.inv.op (p.hom.app (op V) b) at hn
  rw [hn]
  change Q.obj.map e.inv.op (p.hom.app (op V) b) = q
  have hb' : p.hom.app (op V) b = Q.obj.map e.hom.op q := hb
  rw [hb', ← ConcreteCategory.comp_apply, ← Q.obj.map_comp,
    ← op_comp, e.inv_hom_id, op_id, Q.obj.map_id]
  rfl

end EtaleCohomology
