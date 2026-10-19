/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RationalSquareBoundaryLabelConverse
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCrossRatio
import Nyll.AlgebraicCurves.Models.Rational.RationalBoundaryConfigurationIso

/-! # The named square configuration has an actual restricted-label projection

The model-place clause and literal membership clause are exactly outputs of
namedRationalSquareCover_exists_rationalConfiguration. They determine the
projection on labels, rather than introducing a free map between finite sets.
No comparison of source and target coordinates is a premise.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.KummerTheory
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AlgebraicGeometry.ProjSpace

local instance namedSquareProjectionChart_isOpenImmersion
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ⟶
          (projectiveLineRatFuncModel E).C from
            rationalConfigurationBaseChangeChart k E s) :=
  rationalConfigurationBaseChangeChart_isOpenImmersion k E s

private theorem projectiveRatFuncPlace_actual_center
    {k : Type} [Field k] (z : Projectivization k (k × k)) :
    ((projectiveLineRatFuncModel k).placeEquiv.symm (projectiveRatFuncPlace z)).val =
      projectiveRationalPoint z := by
  let M : CurveModel k (RatFunc k) := projectiveLineRatFuncModel k
  let x : closedPoints M.C :=
    ⟨projectiveRationalPoint z,
      isClosed_singleton_rationalPuncturePoint z.rep z.rep_nonzero⟩
  have hx : M.placeEquiv x = projectiveRatFuncPlace z :=
    (M.placeEquiv_apply x).trans
      (projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint k z)
  exact (congrArg (fun V : Place k (RatFunc k) => (M.placeEquiv.symm V).val)
    hx.symm).trans (congrArg Subtype.val (M.placeEquiv.symm_apply_apply x))

section NamedProjection
variable {k : Type} [Field k] {U : Scheme}
variable (j : U ⟶ (projectiveLineRatFuncModel k).C) [IsOpenImmersion j]
variable (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
variable (eF : RatFunc k ≃ₐ[k] RatFunc k)
variable (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel k).C,
  ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel k).C,
    (projectiveLineRatFuncModel k).placeOfPoint ⟨p.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel k).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF))
variable (t : Finset (Projectivization k (k × k)))
variable (ht : ∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range (pullback.fst p j))

include ht in
omit [IsOpenImmersion j] in
/-- The literal model place of every retained upstairs label is omitted by
that same model open. This uses the output membership equality, not a newly
chosen equivalence of the labels with its boundary. -/
theorem namedSquareLabel_mem_actual_boundary (z : t) :
    projectiveRatFuncPlace z.val ∈ (projectiveLineRatFuncModel k).openBoundaryPlaces
      (pullback.fst p j) := by
  change ((projectiveLineRatFuncModel k).placeEquiv.symm
    (projectiveRatFuncPlace z.val)).val ∉ Set.range (pullback.fst p j)
  rw [projectiveRatFuncPlace_actual_center]
  exact (ht z.val).mp z.property

/-- The projection is literal restriction along the actual quadratic field
map supplied by the named model, with boundary membership proved. -/
def namedSquareBoundaryProjection (z : t) :
    (projectiveLineRatFuncModel k).openBoundaryPlaces j :=
  ⟨(projectiveRatFuncPlace z.val).restrictAlong
      (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF),
    (CurveModel.openBoundaryPlaces_pullback_iff_restrictAlong
      (projectiveLineRatFuncModel k) (projectiveLineRatFuncModel k) p
      (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF)
      hplaces j (projectiveRatFuncPlace z.val)).mp
        (namedSquareLabel_mem_actual_boundary j p t ht z)⟩

@[simp] theorem namedSquareBoundaryProjection_val (z : t) :
    (namedSquareBoundaryProjection j p eF hplaces t ht z).val =
      (projectiveRatFuncPlace z.val).restrictAlong
        (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF) := rfl

/-- A selected finite root label projects to its original place, for either
sign. The HasValue statement is the original literal residue-value fact. -/
theorem namedSquareBoundaryProjection_eq_of_root
    (z : t) (V : (projectiveLineRatFuncModel k).openBoundaryPlaces j)
    (f : RatFunc k) (hf : eF RatFunc.X = f)
    (a r : k) (hr : r ^ 2 = a) (hV : V.val.HasValue f a)
    (hz : projectiveRatFuncPlace z.val = RationalFunctionField.placeOfPoint k r ∨
      projectiveRatFuncPlace z.val = RationalFunctionField.placeOfPoint k (-r)) :
    namedSquareBoundaryProjection j p eF hplaces t ht z = V := by
  apply Subtype.ext
  exact (ratFuncPairSquare_fiber_iff_root_or_neg eF f hf V.val
    (projectiveRatFuncPlace z.val) a r hr hV).mpr hz

end NamedProjection

/-- For a base-changed original configuration the codomain is its ORIGINAL
label set s, not a newly selected projective coordinate or rational point. -/
def namedSquareOriginalLabelProjection
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (s : Finset (Projectivization k (k × k)))
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (eF : RatFunc E ≃ₐ[E] RatFunc E)
    (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
      ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
        (projectiveLineRatFuncModel E).placeOfPoint ⟨p.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF))
    (t : Finset (Projectivization E (E × E)))
    (ht : ∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range
      (pullback.fst p (rationalConfigurationBaseChangeChart k E s))) : t → s :=
  fun z => (rationalConfigurationBoundaryPlaceEquiv k E s).symm
    (namedSquareBoundaryProjection (rationalConfigurationBaseChangeChart k E s)
      p eF hplaces t ht z)

/-- The projected original label has exactly the restricted actual place. -/
theorem namedSquareOriginalLabelProjection_place
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (s : Finset (Projectivization k (k × k)))
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (eF : RatFunc E ≃ₐ[E] RatFunc E)
    (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
      ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
        (projectiveLineRatFuncModel E).placeOfPoint ⟨p.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF))
    (t : Finset (Projectivization E (E × E)))
    (ht : ∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range
      (pullback.fst p (rationalConfigurationBaseChangeChart k E s))) (z : t) :
    (rationalConfigurationBoundaryPlace k E s
      (namedSquareOriginalLabelProjection k E s p eF hplaces t ht z)).val =
        (projectiveRatFuncPlace z.val).restrictAlong
          (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF) := by
  change ((rationalConfigurationBoundaryPlaceEquiv k E s)
    ((rationalConfigurationBoundaryPlaceEquiv k E s).symm _)).val = _
  exact congrArg Subtype.val ((rationalConfigurationBoundaryPlaceEquiv k E s).apply_symm_apply
    (namedSquareBoundaryProjection (rationalConfigurationBaseChangeChart k E s)
      p eF hplaces t ht z))

end AlgebraicGeometry.ProjSpace
