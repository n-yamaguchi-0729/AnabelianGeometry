/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Actual constant sections under inverse image

The original adjunction-uniqueness section proof works for every coefficient
category admitting the two sheafifications. Its original abelian specialization
and the module-coefficient source comparison share this single proof.
-/

@[expose] public section

noncomputable section

universe u uA vA

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology.Sites

variable {A : Type uA} [Category.{vA} A]

private theorem constantSheafAdj_homEquiv_section (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology A]
    (T : X.Etale) (hT : IsTerminal T) (M : A)
    (E : Sheaf X.smallEtaleTopology A)
    (g : (constantSheaf X.smallEtaleTopology A).obj M ⟶ E) :
    (constantSheafAdj X.smallEtaleTopology A hT).homEquiv M E g =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op T) ≫
        g.hom.app (op T) := by
  have hunit : (constantSheafAdj X.smallEtaleTopology A hT).unit.app M =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op T) := by
    rw [constantSheafAdj, Adjunction.comp_unit_app]
    change 𝟙 M ≫
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op T) = _
    exact Category.id_comp _
  change (constantSheafAdj X.smallEtaleTopology A hT).unit.app M ≫
    g.hom.app (op T) = _
  exact congrArg (fun t : M ⟶
    ((constantSheaf X.smallEtaleTopology A).obj M).obj.obj (op T) =>
      t ≫ g.hom.app (op T)) hunit

/-- The adjoint of the canonical constant comparison preserves the original
constant section for every left adjoint to actual direct image. -/
theorem constantSheafCompLeftAdjointIso_hom_section
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology A] [HasWeakSheafify Y.smallEtaleTopology A]
    (L : Sheaf Y.smallEtaleTopology A ⥤
      Sheaf X.smallEtaleTopology A)
    (adj : L ⊣ (etaleBaseChange f).sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology) (M : A) (U : Y.Etale) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op U) ≫
        (adj.homEquiv _ _
          ((Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) A
            terminalIsTerminal
              (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
                L adj).hom.app M)).hom.app (op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op ((etaleBaseChange f).obj U)) := by
  let F := etaleBaseChange f
  let ηY : (Functor.const Y.Etaleᵒᵖ).obj M ⟶
      ((constantSheaf Y.smallEtaleTopology A).obj M).obj :=
    toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let ηX : (Functor.const X.Etaleᵒᵖ).obj M ⟶
      ((constantSheaf X.smallEtaleTopology A).obj M).obj :=
    toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  let c := adj.homEquiv _ _
    ((Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) A
      terminalIsTerminal (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
        L adj).hom.app M)
  have hc : ηY.app (op (⊤_ Y.Etale)) ≫ c.hom.app (op (⊤_ Y.Etale)) =
      ηX.app (op (F.obj (⊤_ Y.Etale))) := by
    let adjY : constantSheaf Y.smallEtaleTopology A ⊣
        (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)) :=
      constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal
    let adjX : constantSheaf X.smallEtaleTopology A ⊣
        (etaleBaseChange f).sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology ⋙
          (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)) :=
      constantSheafAdj X.smallEtaleTopology A
        (terminalIsTerminal.isTerminalObj F (⊤_ Y.Etale))
    have hcomp : adjY.homEquiv M _ c = adjX.unit.app M := by
      change adjY.homEquiv M _
        (adj.homEquiv ((constantSheaf Y.smallEtaleTopology A).obj M)
          ((constantSheaf X.smallEtaleTopology A).obj M)
          (((adjY.comp adj).leftAdjointUniq adjX).hom.app M)) = adjX.unit.app M
      calc
        _ = ((adjY.comp adj).homEquiv M
            ((constantSheaf X.smallEtaleTopology A).obj M))
              (((adjY.comp adj).leftAdjointUniq adjX).hom.app M) := by
          rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
        _ = adjX.unit.app M :=
          Adjunction.homEquiv_leftAdjointUniq_hom_app (adjY.comp adj) adjX M
    have hsource : adjY.homEquiv M _ c =
        ηY.app (op (⊤_ Y.Etale)) ≫ c.hom.app (op (⊤_ Y.Etale)) :=
      constantSheafAdj_homEquiv_section Y (⊤_ Y.Etale) terminalIsTerminal M _ c
    have htarget : adjX.unit.app M = ηX.app (op (F.obj (⊤_ Y.Etale))) :=
      (adjX.homEquiv_id M).symm.trans
        ((constantSheafAdj_homEquiv_section X (F.obj (⊤_ Y.Etale))
          (terminalIsTerminal.isTerminalObj F (⊤_ Y.Etale)) M _ (𝟙 _)).trans
            (Category.comp_id _))
    exact hsource.symm.trans (hcomp.trans htarget)
  let j : U ⟶ ⊤_ Y.Etale := terminal.from U
  have hY : ηY.app (op U) = ηY.app (op (⊤_ Y.Etale)) ≫
      ((constantSheaf Y.smallEtaleTopology A).obj M).obj.map j.op := by
    exact (Category.id_comp _).symm.trans (ηY.naturality j.op)
  have hX : ηX.app (op (F.obj U)) = ηX.app (op (F.obj (⊤_ Y.Etale))) ≫
      ((constantSheaf X.smallEtaleTopology A).obj M).obj.map (F.map j).op := by
    exact (Category.id_comp _).symm.trans (ηX.naturality (F.map j).op)
  change ηY.app (op U) ≫ c.hom.app (op U) = ηX.app (op (F.obj U))
  rw [hY, Category.assoc, c.hom.naturality j.op, ← Category.assoc, hc]
  exact hX.symm


theorem constantSheafHom_pullback_section
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology A] [HasWeakSheafify Y.smallEtaleTopology A]
    (L : Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A)
    (adj : L ⊣ (etaleBaseChange f).sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology)
    (M : A) (F : Sheaf Y.smallEtaleTopology A)
    (a : (constantSheaf Y.smallEtaleTopology A).obj M ⟶ F)
    (V : Y.Etale) (U : X.Etale) (l : U ⟶ (etaleBaseChange f).obj V) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op U) ≫
        (((constantSheafCompLeftAdjointIso (etaleBaseChange f) A terminalIsTerminal
        (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale)) L adj).app M).inv ≫
          L.map a).hom.app (op U) =
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op V) ≫
        a.hom.app (op V) ≫
          (adj.unit.app F).hom.app (op V) ≫
            (L.obj F).obj.map l.op := by
  let P := (etaleBaseChange f).sheafPushforwardContinuous A
    Y.smallEtaleTopology X.smallEtaleTopology
  let CY := (constantSheaf Y.smallEtaleTopology A).obj M
  let CX := (constantSheaf X.smallEtaleTopology A).obj M
  let e : L.obj CY ≅ CX := (constantSheafCompLeftAdjointIso (etaleBaseChange f) A terminalIsTerminal
        (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale)) L adj).app M
  let b : CX ⟶ L.obj F := e.inv ≫ L.map a
  let q : CY ⟶ P.obj CX := adj.homEquiv CY CX e.hom
  let ηX := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  let ηY := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  have hq : q ≫ P.map b = a ≫ adj.unit.app F := by
    change (adj.unit.app CY ≫ P.map e.hom) ≫ P.map b = a ≫ adj.unit.app F
    have heb : e.hom ≫ b = L.map a := e.hom_inv_id_assoc (L.map a)
    rw [Category.assoc, ← Functor.map_comp, heb]
    exact (adj.unit.naturality a).symm
  have hb : q.hom.app (op V) ≫ b.hom.app (op ((etaleBaseChange f).obj V)) =
      a.hom.app (op V) ≫ (adj.unit.app F).hom.app (op V) :=
    congrArg (fun z : CY ⟶ P.obj (L.obj F) => z.hom.app (op V)) hq
  have hc : ηY.app (op V) ≫ q.hom.app (op V) =
      ηX.app (op ((etaleBaseChange f).obj V)) :=
    constantSheafCompLeftAdjointIso_hom_section f L adj M V
  have hη : ηX.app (op U) =
      ηX.app (op ((etaleBaseChange f).obj V)) ≫ CX.obj.map l.op :=
    (Category.id_comp _).symm.trans (ηX.naturality l.op)
  change ηX.app (op U) ≫ b.hom.app (op U) =
    ηY.app (op V) ≫ a.hom.app (op V) ≫ (adj.unit.app F).hom.app (op V) ≫
      (L.obj F).obj.map l.op
  calc
    _ = ηX.app (op ((etaleBaseChange f).obj V)) ≫ CX.obj.map l.op ≫
        b.hom.app (op U) :=
      (congrArg (fun z : M ⟶ CX.obj.obj (op U) => z ≫ b.hom.app (op U)) hη).trans
        (Category.assoc _ _ _)
    _ = ηX.app (op ((etaleBaseChange f).obj V)) ≫
        b.hom.app (op ((etaleBaseChange f).obj V)) ≫ (L.obj F).obj.map l.op :=
      congrArg (fun z => ηX.app (op ((etaleBaseChange f).obj V)) ≫ z)
        (b.hom.naturality l.op)
    _ = (ηY.app (op V) ≫ q.hom.app (op V)) ≫
        b.hom.app (op ((etaleBaseChange f).obj V)) ≫ (L.obj F).obj.map l.op :=
      congrArg (fun z : M ⟶ CX.obj.obj (op ((etaleBaseChange f).obj V)) =>
        z ≫ b.hom.app (op ((etaleBaseChange f).obj V)) ≫ (L.obj F).obj.map l.op) hc.symm
    _ = ηY.app (op V) ≫
        (q.hom.app (op V) ≫ b.hom.app (op ((etaleBaseChange f).obj V))) ≫
          (L.obj F).obj.map l.op :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => ηY.app (op V) ≫ z) (Category.assoc _ _ _).symm)
    _ = _ :=
      (congrArg (fun z => ηY.app (op V) ≫ z ≫ (L.obj F).obj.map l.op) hb).trans
        (congrArg (fun z => ηY.app (op V) ≫ z) (Category.assoc _ _ _))

end EtaleCohomology.Sites
