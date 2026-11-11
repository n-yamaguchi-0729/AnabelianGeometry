/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
public import Nyll.EtaleCohomology.Classical.AbelianPushforwardComposition
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.OpenUnitEquationSections
public import Nyll.EtaleCohomology.Classical.UnitDirectImageSquares
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Actual pullback of equation units through open squares

The original direct-image square, its original cartesian-pasting map,
and an actual local factor pull an equation unit to the literal
structure-sheaf pullback of that equation. Only the actual projections
of the pullbacks are used; the scheme morphism may be nondominant.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- An equation invertible on an open remains invertible on the actual
inverse-image open after restriction to any source chart. -/
theorem openEquation_pullback_basicOpen
    {X Y : Scheme.{u}} (f : Y ⟶ X) (O : X.Opens) (P : Y.Opens)
    (hP : P ≤ f ⁻¹ᵁ O) (U : X.Opens) (W : Y.Opens)
    (hW : W ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) (hs : U ⊓ O ≤ X.basicOpen s) :
    W ⊓ P ≤ Y.basicOpen (f.appLE U W hW s) := by
  rw [Scheme.basicOpen_appLE]
  intro y hy
  exact ⟨hy.1, hs ⟨hW hy.1, hP hy.2⟩⟩

/-- Actual direct-image restriction through the square sends the
actual equation unit to the unit of its original structure-sheaf
pullback. -/
theorem openEquationDirectImageUnitSection_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (O : X.Opens) (P : Y.Opens)
    (g : (P : Scheme) ⟶ (O : Scheme)) (hg : g ≫ O.ι = P.ι ≫ f)
    (U : X.Opens) (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : U ⊓ O ≤ X.basicOpen s)
    (hs' : W ⊓ P ≤ Y.basicOpen (f.appLE U W hW s)) :
    ((etaleAbelianPushforward P.ι).obj (etaleMultiplicativeGroupSheaf P)).obj.map
        (etaleBaseChangeLift f (f.resLE U W hW) (f.resLE_comp_ι hW)).op
          ((etaleUnitDirectImageSquareMap O.ι f P.ι g hg).hom.app
            (op ((zariskiToEtale X).obj U))
              (openEquationDirectImageUnitSection X O U s hs)) =
      openEquationDirectImageUnitSection Y P W (f.appLE U W hW s) hs' := by
  let V : X.Etale := (zariskiToEtale X).obj U
  let A : Y.Etale := (zariskiToEtale Y).obj W
  let l : (W : Scheme) ⟶ (U : Scheme) := f.resLE U W hW
  let m : A ⟶ (etaleBaseChange f).obj V :=
    etaleBaseChangeLift f l (f.resLE_comp_ι hW)
  let m₀ : (W : Scheme) ⟶ pullback U.ι f := m.left
  let k₀ : pullback U.ι (P.ι ≫ f) ⟶ pullback U.ι O.ι :=
    etaleUnitDirectImageOverSchemeMap O.ι (P.ι ≫ f) g hg V
  let e := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) P.ι f).app V
  let e' : pullback U.ι (P.ι ≫ f) ≅ pullback (pullback.snd U.ι f) P.ι :=
    (Scheme.Etale.forget (P : Scheme) ⋙ CategoryTheory.Over.forget (P : Scheme)).mapIso e
  let k : pullback W.ι P.ι ⟶ pullback (pullback.snd U.ι f) P.ι :=
    ((etaleBaseChange P.ι).map m).left
  let b : pullback W.ι P.ι ⟶ pullback U.ι O.ι := k ≫ e'.inv ≫ k₀
  have hk₀ : k₀ ≫ pullback.fst U.ι O.ι = pullback.fst U.ι (P.ι ≫ f) :=
    pullback.lift_fst _ _ _
  have heh : e'.hom ≫ pullback.fst (pullback.snd U.ι f) P.ι ≫
      pullback.fst U.ι f = pullback.fst U.ι (P.ι ≫ f) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) P.ι f V
  have hei : e'.inv ≫ e'.hom = 𝟙 _ := e'.inv_hom_id
  have he : e'.inv ≫ pullback.fst U.ι (P.ι ≫ f) =
      pullback.fst (pullback.snd U.ι f) P.ι ≫ pullback.fst U.ι f := by
    calc
      e'.inv ≫ pullback.fst U.ι (P.ι ≫ f) =
          e'.inv ≫ (e'.hom ≫ pullback.fst (pullback.snd U.ι f) P.ι ≫
            pullback.fst U.ι f) := congrArg (fun a => e'.inv ≫ a) heh.symm
      _ = pullback.fst (pullback.snd U.ι f) P.ι ≫ pullback.fst U.ι f := by
        rw [← Category.assoc, hei, Category.id_comp]
  have hk : k ≫ pullback.fst (pullback.snd U.ι f) P.ι =
      pullback.fst W.ι P.ι ≫ m₀ := pullback.lift_fst _ _ _
  have hm : m₀ ≫ pullback.fst U.ι f = l := pullback.lift_fst _ _ _
  have hb : b ≫ pullback.fst U.ι O.ι = pullback.fst W.ι P.ι ≫ l := by
    calc
      b ≫ pullback.fst U.ι O.ι =
          k ≫ e'.inv ≫ pullback.fst U.ι (P.ι ≫ f) := by
        change (k ≫ e'.inv ≫ k₀) ≫ pullback.fst U.ι O.ι = _
        rw [Category.assoc, Category.assoc, hk₀]
      _ = k ≫ pullback.fst (pullback.snd U.ι f) P.ι ≫ pullback.fst U.ι f := by
        rw [he]
      _ = (k ≫ pullback.fst (pullback.snd U.ι f) P.ι) ≫ pullback.fst U.ι f :=
        (Category.assoc _ _ _).symm
      _ = pullback.fst W.ι P.ι ≫ l := by rw [hk, Category.assoc, hm]
  have hr : openSectionBaseChangeRing O.ι U ≫ b.appTop =
      f.appLE U W hW ≫ openSectionBaseChangeRing P.ι W := by
    calc
      openSectionBaseChangeRing O.ι U ≫ b.appTop =
          U.topIso.inv ≫ (b ≫ pullback.fst U.ι O.ι).appTop :=
        Category.assoc U.topIso.inv (pullback.fst U.ι O.ι).appTop b.appTop
      _ = U.topIso.inv ≫ (pullback.fst W.ι P.ι ≫ l).appTop :=
        congrArg (fun a : pullback W.ι P.ι ⟶ (U : Scheme) =>
          U.topIso.inv ≫ a.appTop) hb
      _ = f.appLE U W hW ≫ openSectionBaseChangeRing P.ι W := by
        let tU : Γ((U : Scheme), ⊤) ≅ Γ(X, U) := U.topIso
        let tW : Γ((W : Scheme), ⊤) ≅ Γ(Y, W) := W.topIso
        let a : Γ(X, U) ⟶ Γ(Y, W) := f.appLE U W hW
        let p : Γ((W : Scheme), ⊤) ⟶ Γ(pullback W.ι P.ι, ⊤) :=
          (pullback.fst W.ι P.ι).appTop
        have hres : l.appTop = tU.hom ≫ a ≫ tW.inv :=
          Scheme.Hom.resLE_app_top f hW
        have hcancel : tU.inv ≫ (tU.hom ≫ a ≫ tW.inv) = a ≫ tW.inv :=
          (Category.assoc tU.inv tU.hom (a ≫ tW.inv)).symm.trans
            ((congrArg (fun q : Γ(X, U) ⟶ Γ(X, U) => q ≫ a ≫ tW.inv)
              tU.inv_hom_id).trans (Category.id_comp (a ≫ tW.inv)))
        have hcomp : tU.inv ≫ l.appTop = a ≫ tW.inv :=
          (congrArg (fun q : Γ((U : Scheme), ⊤) ⟶ Γ((W : Scheme), ⊤) =>
            tU.inv ≫ q) hres).trans hcancel
        change tU.inv ≫ l.appTop ≫ p = a ≫ tW.inv ≫ p
        exact (Category.assoc tU.inv l.appTop p).symm.trans
          ((congrArg (fun q : Γ(X, U) ⟶ Γ((W : Scheme), ⊤) => q ≫ p) hcomp).trans
            (Category.assoc a tW.inv p))
  change ((etaleAbelianPushforward P.ι).obj (etaleMultiplicativeGroupSheaf P)).obj.map m.op
      (((etaleAbelianPushforwardCompIso P.ι f).inv.app
          (etaleMultiplicativeGroupSheaf P)).hom.app (op V)
        ((etaleUnitDirectImageOverMap O.ι (P.ι ≫ f) g hg).hom.app (op V)
          (openEquationDirectImageUnitSection X O U s hs))) = _
  rw [etaleAbelianPushforwardCompIso_inv_app]
  apply Additive.toMul.injective
  apply Units.ext
  let uX : Additive ((Γ(pullback U.ι O.ι, ⊤) : Type u)ˣ) :=
    openEquationDirectImageUnitSection X O U s hs
  let uY : Additive ((Γ(pullback W.ι P.ι, ⊤) : Type u)ˣ) :=
    openEquationDirectImageUnitSection Y P W (f.appLE U W hW s) hs'
  have huX : (uX.toMul : Γ(pullback U.ι O.ι, ⊤)) =
      openSectionBaseChangeRing O.ι U s :=
    openEquationDirectImageUnitSection_val X O U s hs
  have huY : (uY.toMul : Γ(pullback W.ι P.ι, ⊤)) =
      openSectionBaseChangeRing P.ι W (f.appLE U W hW s) :=
    openEquationDirectImageUnitSection_val Y P W (f.appLE U W hW s) hs'
  change b.appTop uX.toMul.val = uY.toMul.val
  exact (congrArg (fun z : Γ(pullback U.ι O.ι, ⊤) => b.appTop z) huX).trans
    ((ConcreteCategory.congr_hom hr s).trans huY.symm)

end EtaleCohomology
