/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Coherence of constant sheaves under a site isomorphism

If a site endofunctor is naturally isomorphic to the identity, the induced
identity comparison on inverse image agrees on constant sheaves with the
comparison from the constant-sheaf adjunction.
-/

@[expose] public section

noncomputable section

universe uC vC uA vA

open CategoryTheory Limits Opposite

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A]

/-- Constant-sheaf adjunction units at terminal objects commute with restriction. -/
theorem constantSheafAdj_unit_restriction {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') (g : T' ⟶ T) (M : A) :
    (constantSheafAdj J A hT).unit.app M ≫
        ((constantSheaf J A).obj M).obj.map g.op =
      (constantSheafAdj J A hT').unit.app M := by
  let η := (sheafificationAdjunction J A).unit.app ((Functor.const Cᵒᵖ).obj M)
  have hunit {U : C} (hU : IsTerminal U) :
      (constantSheafAdj J A hU).unit.app M = η.app (op U) := by
    rw [constantSheafAdj, Adjunction.comp_unit_app]
    change 𝟙 M ≫ η.app (op U) = η.app (op U)
    exact Category.id_comp _
  rw [hunit hT, hunit hT']
  have hη := η.naturality g.op
  change 𝟙 M ≫ η.app (op T') =
    η.app (op T) ≫ ((constantSheaf J A).obj M).obj.map g.op at hη
  exact hη.symm.trans (Category.id_comp _)

/-- The inverse-image identity comparison attached to an actual site
isomorphism agrees with the canonical comparison on constant sheaves. -/
theorem constantSheafCompLeftAdjointIso_hom_of_siteIso
    (F : C ⥤ C) [F.IsContinuous J J] (e : F ≅ 𝟭 C)
    {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
    (L : Sheaf J A ⥤ Sheaf J A) (adj : L ⊣ F.sheafPushforwardContinuous A J J)
    (M : A) :
    (constantSheafCompLeftAdjointIso F A hT hFT L adj).hom.app M =
      (adj.leftAdjointUniq (Adjunction.id.ofNatIsoRight
        (Functor.sheafPushforwardContinuousId' e A J).symm)).hom.app
          ((constantSheaf J A).obj M) := by
  let C₀ : A ⥤ Sheaf J A := constantSheaf J A
  let G : Sheaf J A ⥤ Sheaf J A := F.sheafPushforwardContinuous A J J
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : C₀ ⊣ Γ := constantSheafAdj J A hT
  let b : C₀ ⊣ G ⋙ Γ := constantSheafAdj J A hFT
  let β : G ≅ 𝟭 (Sheaf J A) := Functor.sheafPushforwardContinuousId' e A J
  let d : 𝟭 (Sheaf J A) ⊣ G := Adjunction.id.ofNatIsoRight β.symm
  let τ : L ≅ 𝟭 (Sheaf J A) := adj.leftAdjointUniq d
  have hτ : adj.homEquiv (C₀.obj M) (C₀.obj M) (τ.hom.app (C₀.obj M)) =
      β.inv.app (C₀.obj M) := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj d (C₀.obj M)
    change adj.homEquiv (C₀.obj M) (C₀.obj M) (τ.hom.app (C₀.obj M)) =
      𝟙 _ ≫ β.inv.app (C₀.obj M) at h
    simpa only [Category.id_comp] using h
  have hβ : (β.inv.app (C₀.obj M)).hom.app (op T) =
      ((constantSheaf J A).obj M).obj.map (e.hom.app T).op := by
    change 𝟙 _ ≫ ((constantSheaf J A).obj M).obj.map (e.hom.app T).op = _
    exact Category.id_comp _
  have hright : ((a.comp adj).homEquiv M (C₀.obj M))
      (τ.hom.app (C₀.obj M)) = b.unit.app M := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, hτ, Adjunction.homEquiv_unit]
    change (constantSheafAdj J A hT).unit.app M ≫
      (β.inv.app (C₀.obj M)).hom.app (op T) = (constantSheafAdj J A hFT).unit.app M
    rw [hβ]
    exact constantSheafAdj_unit_restriction J A hT hFT (e.hom.app T) M
  apply ((a.comp adj).homEquiv M (C₀.obj M)).injective
  change ((a.comp adj).homEquiv M (C₀.obj M))
      (((a.comp adj).leftAdjointUniq b).hom.app M) =
    ((a.comp adj).homEquiv M (C₀.obj M)) (τ.hom.app (C₀.obj M))
  exact (Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adj) b M).trans hright.symm


/-- A natural isomorphism of actual site functors intertwines the canonical
constant-sheaf comparisons for their chosen left adjoints. -/
theorem constantSheafCompLeftAdjointIso_hom_comp_of_siteIso
    (F G : C ⥤ C) [F.IsContinuous J J] [G.IsContinuous J J] (e : F ≅ G)
    {T : C} (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T)) (hGT : IsTerminal (G.obj T))
    (LF LG : Sheaf J A ⥤ Sheaf J A)
    (adjF : LF ⊣ F.sheafPushforwardContinuous A J J)
    (adjG : LG ⊣ G.sheafPushforwardContinuous A J J) (M : A) :
    (adjF.leftAdjointUniq (adjG.ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso e A J J).symm)).hom.app
        ((constantSheaf J A).obj M) ≫
      (constantSheafCompLeftAdjointIso G A hT hGT LG adjG).hom.app M =
    (constantSheafCompLeftAdjointIso F A hT hFT LF adjF).hom.app M := by
  let K : A ⥤ Sheaf J A := constantSheaf J A
  let PF : Sheaf J A ⥤ Sheaf J A := F.sheafPushforwardContinuous A J J
  let PG : Sheaf J A ⥤ Sheaf J A := G.sheafPushforwardContinuous A J J
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : K ⊣ Γ := constantSheafAdj J A hT
  let bF : K ⊣ PF ⋙ Γ := constantSheafAdj J A hFT
  let bG : K ⊣ PG ⋙ Γ := constantSheafAdj J A hGT
  let eF : K ⋙ LF ≅ K := (a.comp adjF).leftAdjointUniq bF
  let eG : K ⋙ LG ≅ K := (a.comp adjG).leftAdjointUniq bG
  let β : PF ≅ PG := Functor.sheafPushforwardContinuousIso e A J J
  let d : LG ⊣ PF := adjG.ofNatIsoRight β.symm
  let τ : LF ≅ LG := adjF.leftAdjointUniq d
  have hτ : adjF.homEquiv (K.obj M) (K.obj M)
      (τ.hom.app (K.obj M) ≫ eG.hom.app M) =
      d.homEquiv (K.obj M) (K.obj M) (eG.hom.app M) := by
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  have hG : a.homEquiv M (PG.obj (K.obj M))
      (adjG.homEquiv (K.obj M) (K.obj M) (eG.hom.app M)) = bG.unit.app M := by
    calc
      _ = ((a.comp adjG).homEquiv M (K.obj M)) (eG.hom.app M) := by
        rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
      _ = bG.unit.app M :=
        Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adjG) bG M
  change τ.hom.app (K.obj M) ≫ eG.hom.app M = eF.hom.app M
  apply ((a.comp adjF).homEquiv M (K.obj M)).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.comp_homEquiv, Equiv.trans_apply, hτ,
    Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom,
    Adjunction.homEquiv_naturality_right, hG]
  change (constantSheafAdj J A hGT).unit.app M ≫
      ((constantSheaf J A).obj M).obj.map (e.hom.app T).op =
    (constantSheafAdj J A hFT).unit.app M
  exact constantSheafAdj_unit_restriction J A hGT hFT (e.hom.app T) M

end EtaleCohomology.Sites
