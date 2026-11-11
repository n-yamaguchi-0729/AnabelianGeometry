/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.UnitDirectImageSquares
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The original unit quotient in commuting squares

Actual direct-image unit maps induce actual cokernel maps. When the
original unit inclusions are monic, the actual short exact sequences
and their original cohomology boundaries are compatible with arbitrary
scheme pullback. The generic-unit sequence and the unit sequence of a
dense Cartier complement are instances of this same construction.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits

namespace EtaleCohomology

variable {X U : Scheme.{u}} (i : U ⟶ X)

/-- The actual quotient of direct-image units by original regular units. -/
def etaleUnitQuotient : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  cokernel (etaleMultiplicativeGroupToPushforward i)

/-- The original unit inclusion and its actual cokernel projection. -/
def etaleUnitShortComplex : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk (etaleMultiplicativeGroupToPushforward i)
    (cokernel.π _) (cokernel.condition _)

/-- A monic original unit map gives its actual short exact cokernel sequence. -/
theorem etaleUnitShortComplex_shortExact
    [Mono (etaleMultiplicativeGroupToPushforward i)] :
    (etaleUnitShortComplex i).ShortExact := by
  unfold etaleUnitShortComplex
  exact { exact := ShortComplex.exact_cokernel _ }

section Over

variable {V : Scheme.{u}} (j : V ⟶ X) (g : V ⟶ U) (h : g ≫ i = j)

/-- Restriction of direct-image units kills the original unit map in the quotient. -/
theorem unitQuotientOver_zero :
    etaleMultiplicativeGroupToPushforward i ≫
        (etaleUnitDirectImageOverMap i j g h ≫ (etaleUnitShortComplex j).g) = 0 := by
  change etaleMultiplicativeGroupToPushforward i ≫
    (etaleUnitDirectImageOverMap i j g h ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward j)) = 0
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg
      (fun k : etaleMultiplicativeGroupSheaf X ⟶
          (etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V) =>
        k ≫ cokernel.π (etaleMultiplicativeGroupToPushforward j))
      (etaleUnitDirectImageOverMap_unit i j g h)).trans
        (cokernel.condition (etaleMultiplicativeGroupToPushforward j)))

/-- The actual quotient map induced by restriction of direct-image units. -/
def etaleUnitQuotientOverMap : etaleUnitQuotient i ⟶ etaleUnitQuotient j :=
  cokernel.desc (etaleMultiplicativeGroupToPushforward i)
    (etaleUnitDirectImageOverMap i j g h ≫ (etaleUnitShortComplex j).g)
      (unitQuotientOver_zero i j g h)

/-- This comparison retains the actual original quotient projection. -/
theorem etaleUnitQuotientOverMap_π :
    (etaleUnitShortComplex i).g ≫ etaleUnitQuotientOverMap i j g h =
      etaleUnitDirectImageOverMap i j g h ≫ (etaleUnitShortComplex j).g :=
  cokernel.π_desc _ _ _

/-- The actual comparison of original unit sequences over the same base. -/
def etaleUnitOverComplex : etaleUnitShortComplex i ⟶ etaleUnitShortComplex j where
  τ₁ := 𝟙 (etaleMultiplicativeGroupSheaf X)
  τ₂ := etaleUnitDirectImageOverMap i j g h
  τ₃ := etaleUnitQuotientOverMap i j g h
  comm₁₂ := by
    change 𝟙 (etaleMultiplicativeGroupSheaf X) ≫
      etaleMultiplicativeGroupToPushforward j =
        etaleMultiplicativeGroupToPushforward i ≫ etaleUnitDirectImageOverMap i j g h
    exact (Category.id_comp _).trans (etaleUnitDirectImageOverMap_unit i j g h).symm
  comm₂₃ := (etaleUnitQuotientOverMap_π i j g h).symm

/-- The original boundary is unchanged after the constructed comparison
with a larger direct image of units. -/
theorem etaleUnitBoundary_zero_over
    [Mono (etaleMultiplicativeGroupToPushforward i)]
    [Mono (etaleMultiplicativeGroupToPushforward j)]
    (a : Sheaf.H.{u} (etaleUnitQuotient i) 0) :
    Sheaf.H.δ (etaleUnitShortComplex_shortExact i) 0 1 rfl a =
      Sheaf.H.δ (etaleUnitShortComplex_shortExact j) 0 1 rfl
        (Sheaf.H.map (etaleUnitQuotientOverMap i j g h) 0 a) := by
  have hn := Sheaf.H.δ_naturality 0 1 rfl
    (etaleUnitShortComplex_shortExact i) (etaleUnitShortComplex_shortExact j)
    (etaleUnitOverComplex i j g h) a
  change Sheaf.H.δ (etaleUnitShortComplex_shortExact j) 0 1 rfl
      (Sheaf.H.map (etaleUnitQuotientOverMap i j g h) 0 a) =
    Sheaf.H.map (𝟙 (etaleMultiplicativeGroupSheaf X)) 1
      (Sheaf.H.δ (etaleUnitShortComplex_shortExact i) 0 1 rfl a) at hn
  exact (Sheaf.H.map_id_apply
    (Sheaf.H.δ (etaleUnitShortComplex_shortExact i) 0 1 rfl a)).symm.trans hn.symm

end Over

section Square

variable {Y V : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ Y)
  (g : V ⟶ U) (h : g ≫ i = j ≫ f)

/-- The commuting-square unit map vanishes after projection to the target quotient. -/
theorem unitQuotientPullback_zero :
    (etaleAbelianPullback f).map (etaleMultiplicativeGroupToPushforward i) ≫
        (etaleUnitDirectImagePullbackSquareMap i f j g h ≫
          (etaleUnitShortComplex j).g) = 0 := by
  change (etaleAbelianPullback f).map (etaleMultiplicativeGroupToPushforward i) ≫
    (etaleUnitDirectImagePullbackSquareMap i f j g h ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward j)) = 0
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg
      (fun k : (etaleAbelianPullback f).obj (etaleMultiplicativeGroupSheaf X) ⟶
          (etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V) =>
        k ≫ cokernel.π (etaleMultiplicativeGroupToPushforward j))
      (etaleUnitDirectImagePullbackSquareMap_unit i f j g h)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg
            (fun k : etaleMultiplicativeGroupSheaf Y ⟶
                cokernel (etaleMultiplicativeGroupToPushforward j) =>
              etaleMultiplicativeGroupPullback f ≫ k)
            (cokernel.condition (etaleMultiplicativeGroupToPushforward j))).trans
              (comp_zero))))

/-- The actual inverse-image comparison on the original unit cokernels. -/
def etaleUnitQuotientPullbackSquareMap :
    (etaleAbelianPullback f).obj (etaleUnitQuotient i) ⟶ etaleUnitQuotient j :=
  (PreservesCokernel.iso (etaleAbelianPullback f)
    (etaleMultiplicativeGroupToPushforward i)).hom ≫
      cokernel.desc ((etaleAbelianPullback f).map (etaleMultiplicativeGroupToPushforward i))
        (etaleUnitDirectImagePullbackSquareMap i f j g h ≫ (etaleUnitShortComplex j).g)
          (unitQuotientPullback_zero i f j g h)

/-- The constructed inverse-image comparison preserves the actual
quotient projections. -/
theorem etaleUnitQuotientPullbackSquareMap_π :
    (etaleAbelianPullback f).map (etaleUnitShortComplex i).g ≫
        etaleUnitQuotientPullbackSquareMap i f j g h =
      etaleUnitDirectImagePullbackSquareMap i f j g h ≫ (etaleUnitShortComplex j).g := by
  let L := etaleAbelianPullback f
  let α := etaleMultiplicativeGroupToPushforward i
  let r : L.obj ((etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U)) ⟶
      etaleUnitQuotient j :=
    etaleUnitDirectImagePullbackSquareMap i f j g h ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward j)
  let e : L.obj (cokernel α) ≅ cokernel (L.map α) := PreservesCokernel.iso L α
  let d : cokernel (L.map α) ⟶ etaleUnitQuotient j :=
    cokernel.desc (L.map α) r (unitQuotientPullback_zero i f j g h)
  change L.map (cokernel.π α) ≫ (e.hom ≫ d) = r
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg
      (fun k : L.obj ((etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U)) ⟶
          cokernel (L.map α) => k ≫ d)
      (PreservesCokernel.π_iso_hom L α)).trans (cokernel.π_desc _ _ _))

/-- The original pullback of the unit short complex maps to the original
unit sequence on the source of an arbitrary commuting square. -/
def etaleUnitPullbackSquareComplex :
    (etaleUnitShortComplex i).map (etaleAbelianPullback f) ⟶ etaleUnitShortComplex j where
  τ₁ := etaleMultiplicativeGroupPullback f
  τ₂ := etaleUnitDirectImagePullbackSquareMap i f j g h
  τ₃ := etaleUnitQuotientPullbackSquareMap i f j g h
  comm₁₂ := (etaleUnitDirectImagePullbackSquareMap_unit i f j g h).symm
  comm₂₃ := (etaleUnitQuotientPullbackSquareMap_π i f j g h).symm

/-- Pullback on the original cohomology of the constructed unit quotient. -/
def etaleUnitQuotientCohomologySquareMap (n : ℕ) :
    Sheaf.H.{u} (etaleUnitQuotient i) n →+ Sheaf.H.{u} (etaleUnitQuotient j) n :=
  (Sheaf.H.map (etaleUnitQuotientPullbackSquareMap i f j g h) n).comp
    (etaleAbelianCohomologyPullbackMap f (etaleUnitQuotient i) n)

private theorem unitBoundary_zero_exactPullback
    [Mono (etaleMultiplicativeGroupToPushforward i)]
    (a : Sheaf.H.{u} (etaleUnitQuotient i) 0) :
    etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf X) 1
        (Sheaf.H.δ (etaleUnitShortComplex_shortExact i) 0 1 rfl a) =
      Sheaf.H.δ ((etaleUnitShortComplex_shortExact i).map_of_exact
        (etaleAbelianPullback f)) 0 1 rfl
          (etaleAbelianCohomologyPullbackMap f (etaleUnitQuotient i) 0 a) := by
  let L := etaleAbelianPullback f
  let S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleUnitShortComplex i
  have hS : S.ShortExact := etaleUnitShortComplex_shortExact i
  let a' : Sheaf.H.{u} S.X₃ 0 := a
  let CX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let CY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let c : CY ⟶ L.obj CX := ((etaleAbelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).inv
  have hm : (a'.comp hS.extClass (zero_add 1)).mapExactFunctor L =
      (a'.mapExactFunctor L).comp (hS.map_of_exact L).extClass (zero_add 1) :=
    (Ext.mapExactFunctor_comp L a' hS.extClass (zero_add 1)).trans
      (congrArg
        (fun q : Ext.{u} (L.obj S.X₃) (L.obj S.X₁) 1 =>
          (a'.mapExactFunctor L).comp q (zero_add 1))
        (Ext.mapExactFunctor_extClass L hS))
  change (Ext.mk₀ c).comp ((a'.comp hS.extClass (zero_add 1)).mapExactFunctor L)
      (zero_add 1) =
    ((Ext.mk₀ c).comp (a'.mapExactFunctor L) (zero_add 0)).comp
      (hS.map_of_exact L).extClass (zero_add 1)
  exact (congrArg
    (fun q : Ext.{u} (L.obj CX) (L.obj S.X₁) 1 =>
      (Ext.mk₀ c).comp q (zero_add 1)) hm).trans
      (Ext.comp_assoc_of_second_deg_zero (Ext.mk₀ c) (a'.mapExactFunctor L)
        (hS.map_of_exact L).extClass (zero_add 1)).symm

/-- Arbitrary scheme pullback commutes with the original unit boundary
through the constructed square of actual unit direct images. -/
theorem etaleUnitBoundary_zero_pullback_square
    [Mono (etaleMultiplicativeGroupToPushforward i)]
    [Mono (etaleMultiplicativeGroupToPushforward j)]
    (a : Sheaf.H.{u} (etaleUnitQuotient i) 0) :
    etaleMultiplicativeGroupCohomologyPullback f 1
        (Sheaf.H.δ (etaleUnitShortComplex_shortExact i) 0 1 rfl a) =
      Sheaf.H.δ (etaleUnitShortComplex_shortExact j) 0 1 rfl
        (etaleUnitQuotientCohomologySquareMap i f j g h 0 a) := by
  let hX := etaleUnitShortComplex_shortExact i
  let hY := etaleUnitShortComplex_shortExact j
  let b := etaleAbelianCohomologyPullbackMap f (etaleUnitQuotient i) 0 a
  have hδ := Sheaf.H.δ_naturality 0 1 rfl
    (hX.map_of_exact (etaleAbelianPullback f)) hY
    (etaleUnitPullbackSquareComplex i f j g h) b
  change Sheaf.H.δ hY 0 1 rfl
      (Sheaf.H.map (etaleUnitQuotientPullbackSquareMap i f j g h) 0 b) =
    Sheaf.H.map (etaleMultiplicativeGroupPullback f) 1
      (Sheaf.H.δ (hX.map_of_exact (etaleAbelianPullback f)) 0 1 rfl b) at hδ
  exact (congrArg (Sheaf.H.map (etaleMultiplicativeGroupPullback f) 1)
    (unitBoundary_zero_exactPullback i f a)).trans hδ.symm

end Square

end EtaleCohomology
