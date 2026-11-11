/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.ConstantPullbackComparison
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Constant pullback composition between different sites

The original adjunction-unit argument extends to functors between distinct
sites. The comparison for a composite left adjoint is then the composition
of its two canonical constant-sheaf comparisons. These equalities supply
the coherence needed for pulling an external cup back along a diagonal
or graph, whose source and target schemes differ.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD uE vE uA vA

open CategoryTheory Limits Opposite

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The canonical comparison between two sites has the same unit
characterization at every terminal object of its source site. -/
theorem constantSheafCompLeftAdjointIso_unit_betweenSites
    (F : C ⥤ D) [F.IsContinuous J K]
    {T U : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
    (hU : IsTerminal U) (hFU : IsTerminal (F.obj U))
    (L : Sheaf J A ⥤ Sheaf K A) (adj : L ⊣ F.sheafPushforwardContinuous A J K)
    (M : A) :
    (constantSheafAdj J A hU).unit.app M ≫
        (adj.homEquiv ((constantSheaf J A).obj M) ((constantSheaf K A).obj M)
          ((constantSheafCompLeftAdjointIso F A hT hFT L adj).hom.app M)).hom.app (op U) =
      (constantSheafAdj K A hFU).unit.app M := by
  let KC : A ⥤ Sheaf J A := constantSheaf J A
  let KD : A ⥤ Sheaf K A := constantSheaf K A
  let P : Sheaf K A ⥤ Sheaf J A := F.sheafPushforwardContinuous A J K
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : KC ⊣ Γ := constantSheafAdj J A hT
  let b : KD ⊣ P ⋙ Γ := constantSheafAdj K A hFT
  let ε : KC ⋙ L ≅ KD := (a.comp adj).leftAdjointUniq b
  let φ : KC.obj M ⟶ P.obj (KD.obj M) :=
    adj.homEquiv (KC.obj M) (KD.obj M) (ε.hom.app M)
  let t : U ⟶ T := hT.from U
  let ηT : M ⟶ (KC.obj M).obj.obj (op T) := a.unit.app M
  let ηFT : M ⟶ (KD.obj M).obj.obj (op (F.obj T)) := b.unit.app M
  let ηU : M ⟶ (KC.obj M).obj.obj (op U) := (constantSheafAdj J A hU).unit.app M
  let ηFU : M ⟶ (KD.obj M).obj.obj (op (F.obj U)) :=
    (constantSheafAdj K A hFU).unit.app M
  let vT : (KC.obj M).obj.obj (op T) ⟶ (KD.obj M).obj.obj (op (F.obj T)) :=
    φ.hom.app (op T)
  let vU : (KC.obj M).obj.obj (op U) ⟶ (KD.obj M).obj.obj (op (F.obj U)) :=
    φ.hom.app (op U)
  let r : (KC.obj M).obj.obj (op T) ⟶ (KC.obj M).obj.obj (op U) :=
    (KC.obj M).obj.map t.op
  let s : (KD.obj M).obj.obj (op (F.obj T)) ⟶ (KD.obj M).obj.obj (op (F.obj U)) :=
    (KD.obj M).obj.map (F.map t).op
  have hTφ : ηT ≫ vT = ηFT := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adj) b M
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit] at h
    exact h
  have hn : r ≫ vU = vT ≫ s := φ.hom.naturality t.op
  have hr : ηT ≫ r = ηU := constantSheafAdj_unit_restriction J A hT hU t M
  have hs : ηFT ≫ s = ηFU :=
    constantSheafAdj_unit_restriction K A hFT hFU (F.map t) M
  change ηU ≫ vU = ηFU
  calc
    ηU ≫ vU = (ηT ≫ r) ≫ vU :=
      congrArg (fun f : M ⟶ (KC.obj M).obj.obj (op U) => f ≫ vU) hr.symm
    _ = ηT ≫ (r ≫ vU) := Category.assoc ηT r vU
    _ = ηT ≫ (vT ≫ s) :=
      congrArg (fun f : (KC.obj M).obj.obj (op T) ⟶
        (KD.obj M).obj.obj (op (F.obj U)) => ηT ≫ f) hn
    _ = (ηT ≫ vT) ≫ s := (Category.assoc ηT vT s).symm
    _ = ηFT ≫ s :=
      congrArg (fun f : M ⟶ (KD.obj M).obj.obj (op (F.obj T)) => f ≫ s) hTφ
    _ = ηFU := hs

/-- An isomorphism between two site functors preserves the actual
constant comparisons of their chosen left adjoints. -/
theorem constantSheafCompLeftAdjointIso_hom_comp_siteIso_betweenSites
    (F G : C ⥤ D) [F.IsContinuous J K] [G.IsContinuous J K] (e : F ≅ G)
    {T : C} (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T)) (hGT : IsTerminal (G.obj T))
    (LF LG : Sheaf J A ⥤ Sheaf K A)
    (adjF : LF ⊣ F.sheafPushforwardContinuous A J K)
    (adjG : LG ⊣ G.sheafPushforwardContinuous A J K) (M : A) :
    (adjF.leftAdjointUniq (adjG.ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso e A J K).symm)).hom.app
        ((constantSheaf J A).obj M) ≫
      (constantSheafCompLeftAdjointIso G A hT hGT LG adjG).hom.app M =
    (constantSheafCompLeftAdjointIso F A hT hFT LF adjF).hom.app M := by
  let KC : A ⥤ Sheaf J A := constantSheaf J A
  let KD : A ⥤ Sheaf K A := constantSheaf K A
  let PF : Sheaf K A ⥤ Sheaf J A := F.sheafPushforwardContinuous A J K
  let PG : Sheaf K A ⥤ Sheaf J A := G.sheafPushforwardContinuous A J K
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : KC ⊣ Γ := constantSheafAdj J A hT
  let bF : KD ⊣ PF ⋙ Γ := constantSheafAdj K A hFT
  let bG : KD ⊣ PG ⋙ Γ := constantSheafAdj K A hGT
  let eF : KC ⋙ LF ≅ KD := (a.comp adjF).leftAdjointUniq bF
  let eG : KC ⋙ LG ≅ KD := (a.comp adjG).leftAdjointUniq bG
  let β : PF ≅ PG := Functor.sheafPushforwardContinuousIso e A J K
  let d : LG ⊣ PF := adjG.ofNatIsoRight β.symm
  let τ : LF ≅ LG := adjF.leftAdjointUniq d
  have hτ : adjF.homEquiv (KC.obj M) (KD.obj M)
      (τ.hom.app (KC.obj M) ≫ eG.hom.app M) =
      d.homEquiv (KC.obj M) (KD.obj M) (eG.hom.app M) := by
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  have hG : a.homEquiv M (PG.obj (KD.obj M))
      (adjG.homEquiv (KC.obj M) (KD.obj M) (eG.hom.app M)) = bG.unit.app M := by
    calc
      _ = ((a.comp adjG).homEquiv M (KD.obj M)) (eG.hom.app M) := by
        rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
      _ = bG.unit.app M :=
        Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adjG) bG M
  change τ.hom.app (KC.obj M) ≫ eG.hom.app M = eF.hom.app M
  apply ((a.comp adjF).homEquiv M (KD.obj M)).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.comp_homEquiv, Equiv.trans_apply, hτ,
    Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom,
    Adjunction.homEquiv_naturality_right, hG]
  change (constantSheafAdj K A hGT).unit.app M ≫
      ((constantSheaf K A).obj M).obj.map (e.hom.app T).op =
    (constantSheafAdj K A hFT).unit.app M
  exact constantSheafAdj_unit_restriction K A hGT hFT (e.hom.app T) M

variable {E : Type uE} [Category.{vE} E] (Ltop : GrothendieckTopology E)
  [HasWeakSheafify Ltop A]

/-- The canonical constant comparison for a composite between three
sites is the composition of the two original constant comparisons. -/
theorem constantSheafCompLeftAdjointIso_hom_comp_betweenSites
    (F : D ⥤ E) (G : C ⥤ D)
    [F.IsContinuous K Ltop] [G.IsContinuous J K] [(G ⋙ F).IsContinuous J Ltop]
    {T : C} {U : D} (hT : IsTerminal T) (hU : IsTerminal U)
    (hGT : IsTerminal (G.obj T)) (hFU : IsTerminal (F.obj U))
    (hFGT : IsTerminal (F.obj (G.obj T)))
    (LF : Sheaf K A ⥤ Sheaf Ltop A) (LG : Sheaf J A ⥤ Sheaf K A)
    (adjF : LF ⊣ F.sheafPushforwardContinuous A K Ltop)
    (adjG : LG ⊣ G.sheafPushforwardContinuous A J K) (M : A) :
    (constantSheafCompLeftAdjointIso (G ⋙ F) A hT hFGT
      (LG ⋙ LF) (adjG.comp adjF)).hom.app M =
      LF.map ((constantSheafCompLeftAdjointIso G A hT hGT LG adjG).hom.app M) ≫
        (constantSheafCompLeftAdjointIso F A hU hFU LF adjF).hom.app M := by
  let KC : A ⥤ Sheaf J A := constantSheaf J A
  let KD : A ⥤ Sheaf K A := constantSheaf K A
  let KE : A ⥤ Sheaf Ltop A := constantSheaf Ltop A
  let PF : Sheaf Ltop A ⥤ Sheaf K A := F.sheafPushforwardContinuous A K Ltop
  let PG : Sheaf K A ⥤ Sheaf J A := G.sheafPushforwardContinuous A J K
  let Γ : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)
  let a : KC ⊣ Γ := constantSheafAdj J A hT
  let bG : KD ⊣ PG ⋙ Γ := constantSheafAdj K A hGT
  let bFG : KE ⊣ (PF ⋙ PG) ⋙ Γ := constantSheafAdj Ltop A hFGT
  let eG : KC ⋙ LG ≅ KD := (a.comp adjG).leftAdjointUniq bG
  let eF : KD ⋙ LF ≅ KE := constantSheafCompLeftAdjointIso F A hU hFU LF adjF
  let adjFG : LG ⋙ LF ⊣ PF ⋙ PG := adjG.comp adjF
  let φ : KD.obj M ⟶ PF.obj (KE.obj M) :=
    adjF.homEquiv (KD.obj M) (KE.obj M) (eF.hom.app M)
  have hG : a.homEquiv M (PG.obj (KD.obj M))
      (adjG.homEquiv (KC.obj M) (KD.obj M) (eG.hom.app M)) = bG.unit.app M := by
    calc
      _ = ((a.comp adjG).homEquiv M (KD.obj M)) (eG.hom.app M) := by
        rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
      _ = bG.unit.app M :=
        Adjunction.homEquiv_leftAdjointUniq_hom_app (a.comp adjG) bG M
  have hcomp : ((a.comp adjFG).homEquiv M (KE.obj M))
      (LF.map (eG.hom.app M) ≫ eF.hom.app M) =
        bG.unit.app M ≫ φ.hom.app (op (G.obj T)) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right, hG]
    rfl
  apply ((a.comp adjFG).homEquiv M (KE.obj M)).injective
  change ((a.comp adjFG).homEquiv M (KE.obj M))
      (((a.comp adjFG).leftAdjointUniq bFG).hom.app M) =
    ((a.comp adjFG).homEquiv M (KE.obj M)) (LF.map (eG.hom.app M) ≫ eF.hom.app M)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, hcomp]
  exact (constantSheafCompLeftAdjointIso_unit_betweenSites K Ltop A F
    hU hFU hGT hFGT LF adjF M).symm

end EtaleCohomology.Sites
