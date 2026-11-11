/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.AlgebraicPoints.IntegralConstantPoints
public import Nyll.AnabelianGeometry.FiniteField.NativeLangFiber
public import Nyll.EtaleFundamentalGroups.GeometricFiber.LangTranslations
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Constant displacements in the original native Lang fiber

The difference of two points of the same original Lang fiber lies in its
actual finite scheme kernel. It therefore comes from the prescribed constant
closure even when the native fiber is taken at a geometric generic point.
This produces one common constant displacement before evaluating at either
of two normalization primes.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale NeronModelInfra SchemeTheory
open GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw

namespace AnabelianGeometry.FiniteField

variable (k : Type u) [Field k] [Fintype k]
  (A : Scheme.{u}) [A.Over (Spec (.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (.of k))) (hc : G.IsCommutative)

local notation "f" => (A ↘ Spec (CommRingCat.of k))
local notation "langMap" => originalFiniteFieldLangMap k A G hc

/-- The original scheme Lang map acts additively on points over an arbitrary
coefficient field, including the geometric function field. -/
def originalLangPointHom (Ω : Type u) [Field Ω] [Algebra k Ω] :
    G.AlgPoints hc Ω →+ G.AlgPoints hc Ω :=
  AddMonoidHom.mk'
    (fun x => AlgPoints.ofPoint (NeronModelInfra.schemeHomOverComp
      (AlgPoints.toPoint x) langMap))
    (fun x y => by
      apply AlgPoints.toPoint_injective
      exact originalFiniteFieldLangMap_mul k A G hc (Spec.algebraMap k Ω)
        (AlgPoints.toPoint x) (AlgPoints.toPoint y))

/-- Over an algebraic constant field this is the literal Frobenius
displacement in the existing group of points. -/
theorem originalLangPointHom_eq_frobenius_sub
    (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (x : G.AlgPoints hc Ω) :
    originalLangPointHom k A G hc Ω x =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω • x - x :=
  originalFiniteFieldLangMap_point k A G hc Ω x

/-- A point of the actual finite Lang kernel over the generic coefficient
field is the extension of one point over the fixed constant closure. -/
theorem exists_constant_of_originalLang_zero
    (hA : AbelianSchemePropertyBundle k f)
    (κ Ω : Type u) [Field κ] [Field Ω] [Algebra k κ] [Algebra k Ω]
    [Algebra κ Ω] [IsScalarTower k κ Ω] [IsAlgClosed κ]
    (x : G.AlgPoints hc Ω) (hx : originalLangPointHom k A G hc Ω x = 0) :
    ∃ t : G.AlgPoints hc κ,
      originalLangPointHom k A G hc κ t = 0 ∧
      AlgPoints.map (IsScalarTower.toAlgHom k κ Ω) t = x := by
  have hlangMap : IsFinite (langMap).val :=
    (originalFiniteFieldLangMap_finite_etale k A G hc (AlgebraicClosure k) hA).1
  have : IsFinite (G.endKerStr langMap) := inferInstance
  have hone (L : Type u) [Field L] [Algebra k L] :
      Spec.algebraMap k L ≫ (G.one (𝟙 _)).val =
        (G.one (Spec.algebraMap k L)).val :=
    congrArg Subtype.val (G.one_natural (𝟙 _) (Spec.algebraMap k L)
      (Spec.algebraMap k L) (Category.comp_id _))
  have hzero : (AlgPoints.toPoint x).val ≫ (langMap).val =
      (G.one (Spec.algebraMap k Ω)).val :=
    congrArg (fun t : G.AlgPoints hc Ω => (AlgPoints.toPoint t).val) hx
  let p : Spec (.of Ω) ⟶ G.endKer langMap :=
    pullback.lift (AlgPoints.toPoint x).val (Spec.algebraMap k Ω)
      (hzero.trans (hone Ω).symm)
  let p' : SchemeHomOver (Spec.algebraMap k Ω) (G.endKerStr langMap) :=
    ⟨p, pullback.lift_snd _ _ _⟩
  obtain ⟨y, hy⟩ := exists_integralSchemePoint_factor k κ Ω
    (G.endKer langMap) (G.endKerStr langMap) p'
  let t : G.AlgPoints hc κ :=
    AlgPoints.ofPoint ⟨y.val ≫ G.endKerι langMap, by
      rw [Category.assoc, G.endKerι_comp_base]
      exact y.property⟩
  refine ⟨t, ?_, ?_⟩
  · apply AlgPoints.toPoint_injective
    apply Subtype.ext
    change (y.val ≫ G.endKerι langMap) ≫ (langMap).val =
      (G.one (Spec.algebraMap k κ)).val
    rw [Category.assoc, G.endKerι_comp, ← Category.assoc, y.property]
    exact hone κ
  · apply AlgPoints.toPoint_injective
    apply Subtype.ext
    change Spec.algebraMap κ Ω ≫ (y.val ≫ G.endKerι langMap) =
      (AlgPoints.toPoint x).val
    rw [← Category.assoc, hy]
    exact pullback.lift_fst _ _ _

variable (hA : AbelianSchemePropertyBundle k (A ↘ Spec (CommRingCat.of k)))
  {C : Scheme.{u}} (c : C ⟶ Spec (.of k)) (a : SchemeHomOver c (A ↘ Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]

local notation "V" =>
  Functor.obj (FiniteEtale.pullback a.val) (originalLangCover k A G hc hA)

/-- The native coordinate satisfies the original scheme Lang equation over
any geometric coefficient field; no algebraicity over the constants is used. -/
theorem langNativeCoordinate_lang
    (y : SchemeHomOver (Spec.algebraMap k Ω) c) (z : (fiber y.val).obj V) :
    originalLangPointHom k A G hc Ω (langNativeCoordinate k A G hc hA c a Ω y z) =
      AlgPoints.ofPoint (L := G) (hc := hc) (NeronModelInfra.schemeHomOverComp y a) := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change ((fiberObjEquivHom y.val V z).left ≫ pullback.fst (langMap).val a.val) ≫ (langMap).val =
    y.val ≫ a.val
  let p := (fiberObjEquivHom y.val V z).left
  have hpb : pullback.fst (langMap).val a.val ≫ (langMap).val =
      pullback.snd (langMap).val a.val ≫ a.val := pullback.condition
  calc
    (p ≫ pullback.fst (langMap).val a.val) ≫ (langMap).val =
        p ≫ (pullback.fst (langMap).val a.val ≫ (langMap).val) :=
      Category.assoc _ _ _
    _ = p ≫ (pullback.snd (langMap).val a.val ≫ a.val) :=
      congrArg (fun t => p ≫ t) hpb
    _ = (p ≫ pullback.snd (langMap).val a.val) ≫ a.val :=
      (Category.assoc _ _ _).symm
    _ = y.val ≫ a.val :=
      congrArg (· ≫ a.val) (Over.w (fiberObjEquivHom y.val V z))

/-- Two points of the same original native Lang fiber differ by a single
point of the finite Lang kernel in the prescribed constant closure. -/
theorem exists_langNativeCoordinate_difference_constant
    (κ : Type u) [Field κ] [Algebra k κ] [Algebra κ Ω]
    [IsScalarTower k κ Ω] [IsAlgClosed κ]
    (y : SchemeHomOver (Spec.algebraMap k Ω) c) (z w : (fiber y.val).obj V) :
    ∃ t : G.AlgPoints hc κ,
      originalLangPointHom k A G hc κ t = 0 ∧
      AlgPoints.map (IsScalarTower.toAlgHom k κ Ω) t =
        langNativeCoordinate k A G hc hA c a Ω y w -
          langNativeCoordinate k A G hc hA c a Ω y z := by
  apply exists_constant_of_originalLang_zero k A G hc hA κ Ω
  rw [map_sub, langNativeCoordinate_lang, langNativeCoordinate_lang, sub_self]

end AnabelianGeometry.FiniteField
