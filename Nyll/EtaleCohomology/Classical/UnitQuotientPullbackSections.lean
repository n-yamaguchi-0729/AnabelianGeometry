/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianPullbackLocalSections
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.OpenUnitQuotientEquations
public import Nyll.EtaleCohomology.Classical.UnitDirectImageSquares
public import Nyll.EtaleCohomology.Classical.UnitQuotientFunctoriality
public import Nyll.EtaleCohomology.Classical.UnitSquareEquationPullback
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original unit-quotient H⁰ pullback on local equations

The actual quotient comparison preserves the original direct-image
section map under the original adjunction. Consequently an original
local equation of a native H⁰ class pulls back to its actual
structure-sheaf equation, including along closed graph maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

section Square

variable {X Y U V : Scheme.{u}} (i : U ⟶ X) (f : Y ⟶ X)
  (j : V ⟶ Y) (g : V ⟶ U) (h : g ≫ i = j ≫ f)

/-- The direct-image adjoint of the original quotient comparison
retains the original quotient projection and square of actual units. -/
theorem etaleUnitQuotientPullbackSquareMap_adjunct_π :
    (etaleUnitShortComplex i).g ≫
        (etaleAbelianPullbackPushforwardAdjunction f).homEquiv
          (etaleUnitQuotient i) (etaleUnitQuotient j)
            (etaleUnitQuotientPullbackSquareMap i f j g h) =
      etaleUnitDirectImageSquareMap i f j g h ≫
        (etaleAbelianPushforward f).map (etaleUnitShortComplex j).g := by
  have hs := (etaleAbelianPullbackPushforwardAdjunction f).homEquiv_naturality_left_square
    (etaleUnitShortComplex i).g (etaleUnitQuotientPullbackSquareMap i f j g h)
      (etaleUnitDirectImagePullbackSquareMap i f j g h) (etaleUnitShortComplex j).g
        (etaleUnitQuotientPullbackSquareMap_π i f j g h)
  have hAdj :
      (etaleAbelianPullbackPushforwardAdjunction f).homEquiv
          ((etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U))
          ((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V))
          (etaleUnitDirectImagePullbackSquareMap i f j g h) =
        etaleUnitDirectImageSquareMap i f j g h :=
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _
  exact hs.trans (congrArg
    (fun k : ((etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U)) ⟶
        (etaleAbelianPushforward f).obj
          ((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V)) =>
      k ≫ (etaleAbelianPushforward f).map (etaleUnitShortComplex j).g) hAdj)

/-- An actual local lift of an original quotient H⁰ class pulls back by
the original unit square and its actual quotient projection. -/
theorem etaleUnitQuotientCohomologySquareMap_zero_local_lift
    {A : X.Etale} {B : Y.Etale} (l : B.left ⟶ A.left)
    (hl : l ≫ A.hom = B.hom ≫ f)
    (a : Sheaf.H.{u} (etaleUnitQuotient i) 0)
    (b : ((etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U)).obj.obj (op A))
    (hb :
      let hX := MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X
      (etaleUnitShortComplex i).g.hom.app (op A) b =
        (etaleUnitQuotient i).obj.map (hX.from A).op
          (Sheaf.H.equiv₀ (etaleUnitQuotient i) hX a)) :
    let hY := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y;
    (etaleUnitQuotient j).obj.map (hY.from B).op
        (Sheaf.H.equiv₀ (etaleUnitQuotient j) hY
          (etaleUnitQuotientCohomologySquareMap i f j g h 0 a)) =
      (etaleUnitShortComplex j).g.hom.app (op B)
        (((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V)).obj.map
          (etaleBaseChangeLift f l hl).op
            ((etaleUnitDirectImageSquareMap i f j g h).hom.app (op A) b)) := by
  intro hY
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let φ := etaleUnitQuotientPullbackSquareMap i f j g h
  let m := etaleBaseChangeLift f l hl
  let adj := (etaleAbelianPullbackPushforwardAdjunction f).homEquiv
    (etaleUnitQuotient i) (etaleUnitQuotient j) φ
  have hs : (etaleUnitQuotient j).obj.map (hY.from B).op
        (Sheaf.H.equiv₀ (etaleUnitQuotient j) hY
          (etaleUnitQuotientCohomologySquareMap i f j g h 0 a)) =
      (etaleUnitQuotient j).obj.map m.op
        (adj.hom.app (op A)
          ((etaleUnitQuotient i).obj.map (hX.from A).op
            (Sheaf.H.equiv₀ (etaleUnitQuotient i) hX a))) :=
    etaleAbelianCohomologyPullbackCoeff_zero_local_sections f
      (etaleUnitQuotient i) (etaleUnitQuotient j) φ l hl a
  have hb' : (etaleUnitShortComplex i).g.hom.app (op A) b =
      (etaleUnitQuotient i).obj.map (hX.from A).op
        (Sheaf.H.equiv₀ (etaleUnitQuotient i) hX a) := hb
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun k => k.hom.app (op A))
      (etaleUnitQuotientPullbackSquareMap_adjunct_π i f j g h)) b
  have hn := ConcreteCategory.congr_hom ((etaleUnitShortComplex j).g.hom.naturality m.op)
    ((etaleUnitDirectImageSquareMap i f j g h).hom.app (op A) b)
  exact hs.trans
    ((congrArg ((etaleUnitQuotient j).obj.map m.op)
      ((congrArg (adj.hom.app (op A)) hb'.symm).trans hp)).trans hn.symm)

end Square

/-- An original local Cartier equation is pulled to its literal original
structure-sheaf equation by the native quotient H⁰ square. -/
theorem etaleUnitQuotientCohomologySquareMap_zero_equation
    {X Y : Scheme.{u}} (f : Y ⟶ X) (O : X.Opens) (P : Y.Opens)
    (g : P.toScheme ⟶ O.toScheme) (hg : g ≫ O.ι = P.ι ≫ f)
    (U : X.Opens) (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : U ⊓ O ≤ X.basicOpen s)
    (hs' : W ⊓ P ≤ Y.basicOpen (f.appLE U W hW s))
    (a : Sheaf.H.{u} (etaleUnitQuotient O.ι) 0)
    (ha :
      let hX := MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X
      (etaleUnitQuotient O.ι).obj.map
          (hX.from ((zariskiToEtale X).obj U)).op
            (Sheaf.H.equiv₀ (etaleUnitQuotient O.ι) hX a) =
        openEquationUnitQuotientSection X O U s hs) :
    let hY := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y;
    (etaleUnitQuotient P.ι).obj.map
        (hY.from ((zariskiToEtale Y).obj W)).op
          (Sheaf.H.equiv₀ (etaleUnitQuotient P.ι) hY
            (etaleUnitQuotientCohomologySquareMap O.ι f P.ι g hg 0 a)) =
      openEquationUnitQuotientSection Y P W (f.appLE U W hW s) hs' := by
  intro hY
  have hlift := etaleUnitQuotientCohomologySquareMap_zero_local_lift
    O.ι f P.ι g hg (A := (zariskiToEtale X).obj U) (B := (zariskiToEtale Y).obj W)
      (f.resLE U W hW) (f.resLE_comp_ι hW) a
      (openEquationDirectImageUnitSection X O U s hs) ha.symm
  exact hlift.trans (congrArg
    ((etaleUnitShortComplex P.ι).g.hom.app (op ((zariskiToEtale Y).obj W)))
      (openEquationDirectImageUnitSection_square f O P g hg U W hW s hs hs'))

end EtaleCohomology
