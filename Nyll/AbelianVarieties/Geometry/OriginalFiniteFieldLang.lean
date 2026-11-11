/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangPoints
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-! # The original finite-field Lang morphism and its constant extensions -/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

namespace GoodReductionJacobian.RelativeGroupLaw

variable (k : Type u) [Field k] [Fintype k]
  (A : Scheme.{u}) [A.Over (Spec (.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (.of k))) (hc : G.IsCommutative)

local notation "f" => (A ↘ Spec (CommRingCat.of k))

/-- Frobenius over the original finite field. -/
def originalFiniteFieldFrobeniusOver : SchemeHomOver f f :=
  ⟨A.finiteFieldFrobenius k, A.finiteFieldFrobenius_comp_over k⟩

/-- The original finite-field Lang morphism, before any constant extension. -/
def originalFiniteFieldLangMap : SchemeHomOver f f :=
  G.langMap hc (originalFiniteFieldFrobeniusOver k A)

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "g" => pullback.snd f b

/-- The previously constructed geometric Lang morphism is a base change of
the original Lang morphism, with the original projection retained. -/
theorem finiteFieldLangMap_comp_fst :
    (finiteFieldLangMap k Ω A G hc).val ≫ pullback.fst f b =
      pullback.fst f b ≫ (originalFiniteFieldLangMap k A G hc).val := by
  let x : SchemeHomOver (g ≫ b) f := baseChangePointToBase b (schemeHomOverId g)
  have hF : baseChangePointToBase b (finiteFieldFrobeniusOver k Ω A) =
      NeronModelInfra.schemeHomOverComp x (originalFiniteFieldFrobeniusOver k A) := by
    apply Subtype.ext
    simpa only [baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
      schemeHomOverId_coe, Category.id_comp, x, originalFiniteFieldFrobeniusOver,
      finiteFieldFrobeniusOver] using Scheme.constantBaseChangeFrobenius_fst k Ω A
  have h := congrArg (baseChangePointToBase b)
    ((G.baseChange b).langMap_eq_mul_inv (hc.baseChange b)
      (finiteFieldFrobeniusOver k Ω A))
  rw [baseChangePointToBase_mul, baseChangePointToBase_inv, hF] at h
  have h' := h.trans
    (G.comp_langMap hc (originalFiniteFieldFrobeniusOver k A) x).symm
  simpa only [baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
    schemeHomOverId_coe, Category.id_comp, x, finiteFieldLangMap,
    originalFiniteFieldLangMap] using congrArg Subtype.val h'

/-- The square identifying the geometric Lang map is cartesian. -/
theorem finiteFieldLangMap_isPullback :
    IsPullback (finiteFieldLangMap k Ω A G hc).val (pullback.fst f b)
      (pullback.fst f b) (originalFiniteFieldLangMap k A G hc).val := by
  have houter : IsPullback
      ((finiteFieldLangMap k Ω A G hc).val ≫ g) (pullback.fst f b) b
      ((originalFiniteFieldLangMap k A G hc).val ≫ f) := by
    rw [(finiteFieldLangMap k Ω A G hc).property,
      (originalFiniteFieldLangMap k A G hc).property]
    exact (IsPullback.of_hasPullback f b).flip
  exact IsPullback.of_right houter (finiteFieldLangMap_comp_fst k A G hc Ω)
    (IsPullback.of_hasPullback f b).flip

/-- Finite étaleness descends to the original Lang morphism; no connectedness
of a later pullback cover is imposed. -/
theorem originalFiniteFieldLangMap_finite_etale [IsAlgClosed Ω]
    (hA : AbelianSchemePropertyBundle k f) :
    IsFinite (originalFiniteFieldLangMap k A G hc).val ∧
      Etale (originalFiniteFieldLangMap k A G hc).val := by
  have : Flat b := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  have hp : (show MorphismProperty Scheme.{u} from
      @Surjective ⊓ @Flat ⊓ @QuasiCompact) (pullback.fst f b) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have he : Etale (originalFiniteFieldLangMap k A G hc).val :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := (show MorphismProperty Scheme.{u} from @Surjective ⊓ @Flat ⊓ @QuasiCompact))
      (finiteFieldLangMap_isPullback k A G hc Ω) hp
      (etale_finiteFieldLangMap k Ω A G hc hA)
  have : IsProper f := hA.proper
  have : IsProper ((originalFiniteFieldLangMap k A G hc).val ≫ f) := by
    rw [(originalFiniteFieldLangMap k A G hc).property]
    exact hA.proper
  have : IsProper (originalFiniteFieldLangMap k A G hc).val := IsProper.of_comp _ f
  have : LocallyQuasiFinite (originalFiniteFieldLangMap k A G hc).val :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, he⟩

private local instance constantSpecOver : (Spec (.of Ω)).Over (Spec (.of k)) := ⟨b⟩

/-- Evaluation of the original Lang map is the actual coefficient-Frobenius
coboundary on algebraic points. -/
theorem originalFiniteFieldLangMap_point (z : G.AlgPoints hc Ω) :
    (AlgPoints.ofPoint (NeronModelInfra.schemeHomOverComp (AlgPoints.toPoint z)
      (originalFiniteFieldLangMap k A G hc)) : G.AlgPoints hc Ω) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω • z - z := by
  have hF :
      (AlgPoints.ofPoint (NeronModelInfra.schemeHomOverComp (AlgPoints.toPoint z)
        (originalFiniteFieldFrobeniusOver k A)) : G.AlgPoints hc Ω) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k Ω • z := by
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    change (AlgPoints.toPoint z).val ≫ A.finiteFieldFrobenius k =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k Ω).toRingHom) ≫
        (AlgPoints.toPoint z).val
    have hn := Scheme.finiteFieldFrobenius_naturality (Spec (.of Ω)) k A
      (AlgPoints.toPoint z).val
    rw [Scheme.finiteFieldFrobenius_spec] at hn
    exact hn.symm
  have h := congrArg (AlgPoints.ofPoint (L := G) (hc := hc))
    (G.comp_langMap hc (originalFiniteFieldFrobeniusOver k A) (AlgPoints.toPoint z))
  rw [AlgPoints.ofPoint_mul (L := G) (hc := hc),
    AlgPoints.ofPoint_inv (L := G) (hc := hc),
    AlgPoints.ofPoint_toPoint (L := G) (hc := hc), hF] at h
  simpa only [originalFiniteFieldLangMap, sub_eq_add_neg] using h

end GoodReductionJacobian.RelativeGroupLaw
