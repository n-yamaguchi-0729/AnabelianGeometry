/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConstantPullbackComparison

/-!
# Composition of canonical constant-sheaf comparisons

The adjunction-unit characterization holds at every terminal object.
Consequently the comparison for the composite adjunction agrees with
successive constant-sheaf comparisons.
-/

@[expose] public section

noncomputable section

universe uC vC uA vA

open CategoryTheory Limits Opposite

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A]

/-- The canonical constant-sheaf comparison has the same adjunction-unit
characterization at every terminal object of the site. -/
theorem constantSheafCompLeftAdjointIso_unit_at_terminal
    (F : C ⥤ C) [F.IsContinuous J J]
    {T U : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
    (hU : IsTerminal U) (hFU : IsTerminal (F.obj U))
    (L : Sheaf J A ⥤ Sheaf J A) (adj : L ⊣ F.sheafPushforwardContinuous A J J)
    (M : A) :
    (constantSheafAdj J A hU).unit.app M ≫
        (adj.homEquiv ((constantSheaf J A).obj M) ((constantSheaf J A).obj M)
          ((constantSheafCompLeftAdjointIso F A hT hFT L adj).hom.app M)).hom.app (op U) =
      (constantSheafAdj J A hFU).unit.app M := by
  let K : A ⥤ Sheaf J A := constantSheaf J A
  let P : Sheaf J A ⥤ Sheaf J A := F.sheafPushforwardContinuous A J J
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : K ⊣ Γ := constantSheafAdj J A hT
  let b : K ⊣ P ⋙ Γ := constantSheafAdj J A hFT
  let ε : K ⋙ L ≅ K := (a.comp adj).leftAdjointUniq b
  let φ : K.obj M ⟶ P.obj (K.obj M) :=
    adj.homEquiv (K.obj M) (K.obj M) (ε.hom.app M)
  let t : U ⟶ T := hT.from U
  let ηT : M ⟶ (K.obj M).obj.obj (op T) := a.unit.app M
  let ηFT : M ⟶ (K.obj M).obj.obj (op (F.obj T)) := b.unit.app M
  let ηU : M ⟶ (K.obj M).obj.obj (op U) := (constantSheafAdj J A hU).unit.app M
  let ηFU : M ⟶ (K.obj M).obj.obj (op (F.obj U)) :=
    (constantSheafAdj J A hFU).unit.app M
  let vT : (K.obj M).obj.obj (op T) ⟶ (K.obj M).obj.obj (op (F.obj T)) :=
    φ.hom.app (op T)
  let vU : (K.obj M).obj.obj (op U) ⟶ (K.obj M).obj.obj (op (F.obj U)) :=
    φ.hom.app (op U)
  let r : (K.obj M).obj.obj (op T) ⟶ (K.obj M).obj.obj (op U) := (K.obj M).obj.map t.op
  let s : (K.obj M).obj.obj (op (F.obj T)) ⟶ (K.obj M).obj.obj (op (F.obj U)) :=
    (K.obj M).obj.map (F.map t).op
  have hTφ : ηT ≫ vT = ηFT := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adj) b M
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit] at h
    exact h
  have hn : r ≫ vU = vT ≫ s := φ.hom.naturality t.op
  have hr : ηT ≫ r = ηU := constantSheafAdj_unit_restriction J A hT hU t M
  have hs : ηFT ≫ s = ηFU :=
    constantSheafAdj_unit_restriction J A hFT hFU (F.map t) M
  change ηU ≫ vU = ηFU
  rw [← hr, Category.assoc, hn, ← Category.assoc, hTφ, hs]

/-- Canonical constant-sheaf comparisons compose with the actual composite
adjunction. This is the coefficient coherence required for functorial pullback. -/
theorem constantSheafCompLeftAdjointIso_hom_comp
    (F G : C ⥤ C) [F.IsContinuous J J] [G.IsContinuous J J]
    [(G ⋙ F).IsContinuous J J]
    {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
    (hGT : IsTerminal (G.obj T)) (hFGT : IsTerminal (F.obj (G.obj T)))
    (LF LG : Sheaf J A ⥤ Sheaf J A)
    (adjF : LF ⊣ F.sheafPushforwardContinuous A J J)
    (adjG : LG ⊣ G.sheafPushforwardContinuous A J J) (M : A) :
    (constantSheafCompLeftAdjointIso (G ⋙ F) A hT hFGT
      (LG ⋙ LF) (adjG.comp adjF)).hom.app M =
      LF.map ((constantSheafCompLeftAdjointIso G A hT hGT LG adjG).hom.app M) ≫
        (constantSheafCompLeftAdjointIso F A hT hFT LF adjF).hom.app M := by
  let K : A ⥤ Sheaf J A := constantSheaf J A
  let PF : Sheaf J A ⥤ Sheaf J A := F.sheafPushforwardContinuous A J J
  let PG : Sheaf J A ⥤ Sheaf J A := G.sheafPushforwardContinuous A J J
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : K ⊣ Γ := constantSheafAdj J A hT
  let bG : K ⊣ PG ⋙ Γ := constantSheafAdj J A hGT
  let bFG : K ⊣ (PF ⋙ PG) ⋙ Γ := constantSheafAdj J A hFGT
  let eG : K ⋙ LG ≅ K := (a.comp adjG).leftAdjointUniq bG
  let eF : K ⋙ LF ≅ K := constantSheafCompLeftAdjointIso F A hT hFT LF adjF
  let adjFG : LG ⋙ LF ⊣ PF ⋙ PG := adjG.comp adjF
  let φ : K.obj M ⟶ PF.obj (K.obj M) :=
    adjF.homEquiv (K.obj M) (K.obj M) (eF.hom.app M)
  have hG : a.homEquiv M (PG.obj (K.obj M))
      (adjG.homEquiv (K.obj M) (K.obj M) (eG.hom.app M)) = bG.unit.app M := by
    calc
      _ = ((a.comp adjG).homEquiv M (K.obj M)) (eG.hom.app M) := by
        rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
      _ = bG.unit.app M :=
        Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adjG) bG M
  have hcomp : ((a.comp adjFG).homEquiv M (K.obj M))
      (LF.map (eG.hom.app M) ≫ eF.hom.app M) =
        bG.unit.app M ≫ φ.hom.app (op (G.obj T)) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right, hG]
    rfl
  apply ((a.comp adjFG).homEquiv M (K.obj M)).injective
  change ((a.comp adjFG).homEquiv M (K.obj M))
      (((a.comp adjFG).leftAdjointUniq bFG).hom.app M) =
    ((a.comp adjFG).homEquiv M (K.obj M)) (LF.map (eG.hom.app M) ≫ eF.hom.app M)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, hcomp]
  exact (constantSheafCompLeftAdjointIso_unit_at_terminal J A F hT hFT hGT hFGT
    LF adjF M).symm

end EtaleCohomology.Sites
