/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareExactCrossRatio
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareOriginalPairValues
import Nyll.AnabelianGeometry.WeightFiltration.CoherentLiftedCyclicClasses
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionValues

/-! # Arithmetic reconstruction from a named rational square -/

noncomputable section
open scoped RatFunc
open AlgebraicGeometry.FiniteEtale
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.KummerTheory
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

section Named
variable (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
variable (s t : Finset (Projectivization k (k × k)))
variable (S T : Finset (Projectivization E (E × E)))
variable (qS : (projectiveLineRatFuncModel E).C ⟶
  (projectiveLineRatFuncModel E).C)
variable (eS : RatFunc E ≃ₐ[E] RatFunc E)
variable (hplacesS : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
  ∃ hy : qS.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
    (projectiveLineRatFuncModel E).placeOfPoint ⟨qS.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eS) (ratFuncPairSquareHom_isIntegral eS))
variable (hS : ∀ z, z ∈ S ↔ projectiveRationalPoint z ∉ Set.range
  (pullback.fst qS (rationalConfigurationBaseChangeChart k E s)))
variable (qT : (projectiveLineRatFuncModel E).C ⟶
  (projectiveLineRatFuncModel E).C)
variable (eT : RatFunc E ≃ₐ[E] RatFunc E)
variable (hplacesT : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
  ∃ hy : qT.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
    (projectiveLineRatFuncModel E).placeOfPoint ⟨qT.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eT) (ratFuncPairSquareHom_isIntegral eT))
variable (hT : ∀ z, z ∈ T ↔ projectiveRationalPoint z ∉ Set.range
  (pullback.fst qT (rationalConfigurationBaseChangeChart k E t)))
variable (σ : s ≃ t) (τ : S ≃ T)
variable (hcomm : ∀ z : S,
  namedSquareOriginalLabelProjection k E t qT eT hplacesT T hT (τ z) =
    σ (namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS z))
include qS hplacesS hS qT hplacesT hT hcomm

theorem namedSquareModels_match_configuration_of_arithmeticEquivalences
    (κ : Type) [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [IsAlgClosure k κ] [Algebra E κ] [IsAlgClosure E κ]
    (hs : 3 ≤ s.card) (ht : 3 ≤ t.card) (hScard : 3 ≤ S.card) (hTcard : 3 ≤ T.card)
    (ΩS ΩT : Type) [Field ΩS] [Field ΩT] [IsAlgClosed ΩS] [IsAlgClosed ΩT]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField ΩS]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField ΩT]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField ΩS]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField ΩT]
    (αP : rationalConfigurationArithmeticGroup k κ s ΩS ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t ΩT)
    (hαP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t ΩT) (αP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s ΩS) γ)
    (αΔ : rationalConfigurationGeometricGroup k κ s ΩS ≃ₜ*
      rationalConfigurationGeometricGroup k κ t ΩT)
    (hαΔ : ∀ v, rationalConfigurationGeometricInclusion k κ t ΩT (αΔ v) =
      αP (rationalConfigurationGeometricInclusion k κ s ΩS v))
    (hIσ : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t ΩT,
      (rationalConfigurationChosenInertia k κ s ΩS
        (rationalConfigurationBoundaryPlace k κ s p)).map αΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t ΩT
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom)
    (ΘS ΘT : Type) [Field ΘS] [Field ΘT] [IsAlgClosed ΘS] [IsAlgClosed ΘT]
    [Algebra (rationalConfigurationGeometricScheme E κ S).functionField ΘS]
    [Algebra (rationalConfigurationGeometricScheme E κ T).functionField ΘT]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ S).functionField ΘS]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ T).functionField ΘT]
    (βP : rationalConfigurationArithmeticGroup E κ S ΘS ≃ₜ*
      rationalConfigurationArithmeticGroup E κ T ΘT)
    (hβP : ∀ γ,
      arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen T).ι ≫ π E 1)
        (rationalConfigurationArithmeticBasePoint E κ T ΘT) (βP γ) =
      arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen S).ι ≫ π E 1)
        (rationalConfigurationArithmeticBasePoint E κ S ΘS) γ)
    (βΔ : rationalConfigurationGeometricGroup E κ S ΘS ≃ₜ*
      rationalConfigurationGeometricGroup E κ T ΘT)
    (hβΔ : ∀ v, rationalConfigurationGeometricInclusion E κ T ΘT (βΔ v) =
      βP (rationalConfigurationGeometricInclusion E κ S ΘS v))
    (hIτ : ∀ p : S, ∃ a : rationalConfigurationGeometricGroup E κ T ΘT,
      (rationalConfigurationChosenInertia E κ S ΘS
        (rationalConfigurationBoundaryPlace E κ S p)).map βΔ.toMonoidHom =
      (rationalConfigurationChosenInertia E κ T ΘT
        (rationalConfigurationBoundaryPlace E κ T (τ p))).map
          (MulAut.conj a).toMonoidHom)
    (a b c₀ : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (VS₀ VSinf VT₀ VTinf : Place k (RatFunc k))
    (f g : RatFunc k) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfS : eS RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f)
    (hfT : eT RatFunc.X = algebraMap (RatFunc k) (RatFunc E) g)
    (harithS : ∀ V : Place k (RatFunc k), V.ord f =
      (if V = VS₀ then 1 else 0) - (if V = VSinf then 1 else 0))
    (harithT : ∀ V : Place k (RatFunc k), V.ord g =
      (if V = VT₀ then 1 else 0) - (if V = VTinf then 1 else 0))
    (hgeomS : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (hgeomT : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) g) =
        (if W = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0))
    (rS : s → E) (rT : t → E)
    (hrS : ∀ x : s, rS x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f))
    (hrT : ∀ x : t, rT x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt g)) :
    ∀ c : s,
      matchTriples a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
        (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
        (fun h => h₀a (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => h₀b (σ.injective (Subtype.ext h)))
        (fun h => h₀a (σ.injective (Subtype.ext h))) c.val = (σ c).val := by
  have hbase := bare_rationalConfiguration_crossRatio_cyclic_classes_fixed_inertia
    k κ s t hs ht ΩS ΩT αP hαP αΔ hαΔ σ hIσ
  have hlift := bare_rationalConfiguration_crossRatio_cyclic_classes_fixed_inertia
    E κ S T hScard hTcard ΘS ΘT βP hβP βΔ hβΔ τ hIτ
  let fS := algebraMap (RatFunc k) (RatFunc E) f
  let fT := algebraMap (RatFunc k) (RatFunc E) g
  let vS : s → E := fun x => (rationalConfigurationBoundaryPlace k E s x).val.evalAt fS
  let vT : t → E := fun x => (rationalConfigurationBoundaryPlace k E t x).val.evalAt fT
  obtain ⟨hzS, hpS, hvS, hratioS⟩ := namedSquare_original_pair_values_over_extension
    k κ E s a b c₀ hab h₀b VS₀ VSinf f hf harithS hgeomS
  obtain ⟨hzT, hpT, hvT, hratioT⟩ := namedSquare_original_pair_values_over_extension
    k κ E t (σ a) (σ b) (σ c₀) (σ.injective.ne hab) (σ.injective.ne h₀b)
      VT₀ VTinf g hg harithT hgeomT
  have hrootS := rationalConfigurationBoundaryPlace_coefficient_square_values k E s f hf rS hrS
  have hrootT := rationalConfigurationBoundaryPlace_coefficient_square_values k E t g hg rT hrT
  exact namedSquareModels_match_configuration
    k E s t S T qS eS hplacesS hS qT eT hplacesT hT σ τ hcomm hbase hlift
    a b c₀ hab h₀a h₀b fS fT hfS hfT vS rS vT rT
    (fun x _ => hrootS x) (fun x _ => hrootT x)
    hzS hzT hpS hpT hvS hvT hratioS
    (fun c hcb => hratioT (σ c) (σ.injective.ne hcb))

end Named
end AnabelianGeometry.WeightFiltration
