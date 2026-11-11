/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CurveFiniteEtaleModel
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitFinitePullback
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteCechDescent
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteDeckSections
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteProjectionSections
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Degree of the original divisor descended from a specified vertex

The retained Čech equation is evaluated on the same original finite cover.
The actual quotient-section comparison turns augmentation into native
pullback and turns the rational vertex into a principal divisor. Taking
degree gives the cover degree times the descended degree, with the sign
and the specified original divisor vertex retained.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Abelian
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups EtaleCohomology

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) [IsNormalIntegral M.C]
  (Y : FiniteEtale M.C) [IsConnected Y]
  {T : M.C.Etale} (hT : IsTerminal T)
  (f : (finiteEtaleInclusion M.C).obj Y ⟶ T)

/-- For the original descended divisor, the cover degree times its
degree is minus the exponent times the degree of the specified vertex. -/
theorem degree_finiteCechDescendedDivisor
    (n : ℕ)
    (a : (constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ etaleGenericUnitQuotient M.C)
    (t : (freeAbelianSheafYoneda M.C.smallEtaleTopology).obj
      ((finiteEtaleInclusion M.C).obj Y) ⟶ (etaleGenericUnitShortComplex M.C).X₂)
    (v : (freeAbelianSheafYoneda M.C.smallEtaleTopology).obj
      ((finiteEtaleInclusion M.C).obj Y) ⟶ etaleGenericUnitQuotient M.C)
    (ha : abelianCechUnitAugmentation M.C.smallEtaleTopology hT f ≫ a =
      (t ≫ (etaleGenericUnitShortComplex M.C).g :
        (freeAbelianSheafYoneda M.C.smallEtaleTopology).obj
          ((finiteEtaleInclusion M.C).obj Y) ⟶ etaleGenericUnitQuotient M.C) - n • v) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    ((let _ : Algebra M.C.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
      Module.finrank M.C.functionField Y.left.functionField) : ℤ) *
        Divisor.degree (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) =
      -(n : ℤ) * Divisor.degree
        ((M.finiteEtaleModel Y).genericUnitDivisorH0Equiv
          (finiteEtaleGenericUnitQuotientSectionsEquiv Y
            (freeAbelianSheafYonedaHomEquiv M.C.smallEtaleTopology
              ((finiteEtaleInclusion M.C).obj Y) (etaleGenericUnitQuotient M.C) v))) := by
  intro hY algKY
  let N := M.finiteEtaleModel Y
  have : HasPrincipalDivisors K Y.left.functionField :=
    (isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      N.toBase N.ffEquiv N.ffEquiv_algebraMap).toHasPrincipalDivisors
  let e := freeAbelianSheafYonedaHomAddEquiv M.C.smallEtaleTopology
    ((finiteEtaleInclusion M.C).obj Y) (etaleGenericUnitQuotient M.C)
  let q := finiteEtaleGenericUnitQuotientSectionsEquiv Y
  let s := freeAbelianSheafYonedaHomEquiv M.C.smallEtaleTopology
    ((finiteEtaleInclusion M.C).obj Y) (etaleGenericUnitShortComplex M.C).X₂ t
  let b := (genericPointUnitsH0Equiv Y.left).symm (finiteEtaleGenericUnitSectionsEquiv Y s)
  have he := congrArg (fun z => q (e z)) ha
  rw [e.map_sub, map_nsmul e n v, q.map_sub, map_nsmul q n (e v)] at he
  have hleft : q (e (abelianCechUnitAugmentation M.C.smallEtaleTopology hT f ≫ a)) =
      finiteGenericUnitH0Pullback Y (Ext.mk₀ a) :=
    finiteEtaleGenericUnitQuotientSectionsEquiv_augmentation Y hT f a
  have hright : q (e (t ≫ (etaleGenericUnitShortComplex M.C).g)) =
      Sheaf.H.map (etaleGenericUnitShortComplex Y.left).g 0 b := by
    change q (freeAbelianSheafYonedaHomEquiv M.C.smallEtaleTopology
      ((finiteEtaleInclusion M.C).obj Y) (etaleGenericUnitQuotient M.C)
      (t ≫ (etaleGenericUnitShortComplex M.C).g)) = _
    have hpost := freeAbelianSheafYonedaHomEquiv_postcomp
      M.C.smallEtaleTopology ((finiteEtaleInclusion M.C).obj Y)
      (F := (etaleGenericUnitShortComplex M.C).X₂) (G := etaleGenericUnitQuotient M.C)
      t (etaleGenericUnitShortComplex M.C).g
    exact (congrArg q hpost).trans (finiteEtaleGenericUnitQuotientSectionsEquiv_projection Y s)
  rw [hleft, hright] at he
  have hp : (N.genericUnitsDivisorH0Map b).IsPrincipal := by
    apply Divisor.mem_principal.mp
    rw [← N.genericUnitsDivisorH0Map_range]
    exact ⟨b, rfl⟩
  have hz : Divisor.degree (N.genericUnitDivisorH0Equiv
      (Sheaf.H.map (etaleGenericUnitShortComplex Y.left).g 0 b)) = 0 :=
    Divisor.degree_eq_zero_of_isPrincipal hp
  let degreeMap : Sheaf.H (etaleGenericUnitQuotient Y.left) 0 →+ ℤ :=
    Divisor.degree.comp N.genericUnitDivisorH0Equiv.toAddMonoidHom
  have hd := congrArg degreeMap he
  have hz' : degreeMap (Sheaf.H.map (etaleGenericUnitShortComplex Y.left).g 0 b) = 0 := hz
  have hlinear := (map_sub degreeMap
    (Sheaf.H.map (etaleGenericUnitShortComplex Y.left).g 0 b) (n • q (e v))).trans
    (congrArg₂ (fun x y : ℤ => x - y) hz' (map_nsmul degreeMap n (q (e v))))
  have hcover := M.degree_genericUnitDivisorH0Equiv_finitePullback Y (Ext.mk₀ a)
  have hresult := hcover.symm.trans (hd.trans hlinear)
  have hvertex : degreeMap (q (e v)) = Divisor.degree
      ((M.finiteEtaleModel Y).genericUnitDivisorH0Equiv
        (finiteEtaleGenericUnitQuotientSectionsEquiv Y
          (freeAbelianSheafYonedaHomEquiv M.C.smallEtaleTopology
            ((finiteEtaleInclusion M.C).obj Y) (etaleGenericUnitQuotient M.C) v))) := rfl
  rw [hvertex] at hresult
  simpa only [zero_sub, nsmul_eq_mul, neg_mul] using hresult

end AlgebraicCurve.CurveModel
