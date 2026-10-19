/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.ProjectiveLine.SameLiftedCrossRatioRigidity
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareMatchedRootLabels
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareSelectedLabels

/-! # Cross-ratio rigidity for named square models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.KummerTheory
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

section Named
variable (k E : Type) [Field k] [Field E] [NumberField E] [Algebra k E]
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
variable (hcomm : ∀ z : S, (namedSquareOriginalLabelProjection k E t qT eT hplacesT T hT) (τ z)
  = σ ((namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) z))
include hcomm qS hplacesS hS qT hplacesT hT

theorem namedSquareModels_crossRatio_eq
    (hbase : ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (hlift : ∀ (a b c₀ c : S), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : Eˣ,
        (A : E) = crossRatio a.val b.val c₀.val c.val ∧
        (B : E) = crossRatio (τ a).val (τ b).val (τ c₀).val (τ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (a b c₀ c : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hc₀ : c ≠ c₀)
    (A B C₀ C : S) (hA : (namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) A = a)
      (hB : (namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) B = b)
    (hC₀ : (namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) C₀ = c₀) (hC :
      (namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) C = c)
    (fS fT : RatFunc E) (hfS : eS RatFunc.X = fS) (hfT : eT RatFunc.X = fT)
    (aS₀ aS aT₀ aT rS₀ rS rT₀ rT : E)
    (hrS₀ : rS₀ ^ 2 = aS₀) (hrS : rS ^ 2 = aS)
    (hrT₀ : rT₀ ^ 2 = aT₀) (hrT : rT ^ 2 = aT)
    (hzeroS : (rationalConfigurationBoundaryPlace k E s a).val.HasValue fS 0)
    (hpoleS : (rationalConfigurationBoundaryPlace k E s b).val.ord fS < 0)
    (hvalueS₀ : (rationalConfigurationBoundaryPlace k E s c₀).val.HasValue fS aS₀)
    (hvalueS : (rationalConfigurationBoundaryPlace k E s c).val.HasValue fS aS)
    (hzeroT : (rationalConfigurationBoundaryPlace k E t (σ a)).val.HasValue fT 0)
    (hpoleT : (rationalConfigurationBoundaryPlace k E t (σ b)).val.ord fT < 0)
    (hvalueT₀ : (rationalConfigurationBoundaryPlace k E t (σ c₀)).val.HasValue fT aT₀)
    (hvalueT : (rationalConfigurationBoundaryPlace k E t (σ c)).val.HasValue fT aT)
    (hratioS : aS / aS₀ = algebraMap k E (crossRatio a.val b.val c₀.val c.val))
    (hratioT : aT / aT₀ = algebraMap k E
      (crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val)) :
    crossRatio a.val b.val c₀.val c.val =
      crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val := by
  have hsquareS : (crossRatio A.val B.val C₀.val C.val) ^ 2 =
      algebraMap k E (crossRatio a.val b.val c₀.val c.val) := by
    have h := namedSquare_matchedLabel_crossRatio_sq k E s qS eS hplacesS S hS
      (fun z : S => z) (namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) (fun _ =>
        rfl) A B C₀ C fS hfS
      aS₀ aS rS₀ rS hrS₀ hrS
      (by simpa only [hA] using hzeroS)
      (by simpa only [hB] using hpoleS)
      (by simpa only [hC₀] using hvalueS₀)
      (by simpa only [hC] using hvalueS)
    exact h.trans hratioS
  have hsquareT :
      (crossRatio (τ A).val (τ B).val (τ C₀).val (τ C).val) ^ 2 =
        algebraMap k E (crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val) := by
    have h := namedSquare_matchedLabel_crossRatio_sq k E t qT eT hplacesT T hT
      τ (fun z : S => σ ((namedSquareOriginalLabelProjection k E s qS eS hplacesS S hS) z))
        hcomm A B C₀ C fT hfT
      aT₀ aT rT₀ rT hrT₀ hrT
      (by simpa only [hA] using hzeroT)
      (by simpa only [hB] using hpoleT)
      (by simpa only [hC₀] using hvalueT₀)
      (by simpa only [hC] using hvalueT)
    exact h.trans hratioT
  exact crossRatio_eq_of_same_lifted_cyclic_data σ τ (namedSquareOriginalLabelProjection k E s
    qS eS hplacesS S hS) hbase hlift
    a b c₀ c hab h₀a h₀b hca hcb hc₀ A B C₀ C hA hB hC₀ hC hsquareS hsquareT

theorem namedSquareModels_crossRatio_eq_of_selected_roots
    (hbase : ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (hlift : ∀ (a b c₀ c : S), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : Eˣ,
        (A : E) = crossRatio a.val b.val c₀.val c.val ∧
        (B : E) = crossRatio (τ a).val (τ b).val (τ c₀).val (τ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (a b c₀ c : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hc₀ : c ≠ c₀)
    (fS fT : RatFunc E) (hfS : eS RatFunc.X = fS) (hfT : eT RatFunc.X = fT)
    (aS₀ aS aT₀ aT rS₀ rS rT₀ rT : E)
    (hrS₀ : rS₀ ^ 2 = aS₀) (hrS : rS ^ 2 = aS)
    (hrT₀ : rT₀ ^ 2 = aT₀) (hrT : rT ^ 2 = aT)
    (hzeroS : (rationalConfigurationBoundaryPlace k E s a).val.HasValue fS 0)
    (hpoleS : (rationalConfigurationBoundaryPlace k E s b).val.ord fS < 0)
    (hvalueS₀ : (rationalConfigurationBoundaryPlace k E s c₀).val.HasValue fS aS₀)
    (hvalueS : (rationalConfigurationBoundaryPlace k E s c).val.HasValue fS aS)
    (hzeroT : (rationalConfigurationBoundaryPlace k E t (σ a)).val.HasValue fT 0)
    (hpoleT : (rationalConfigurationBoundaryPlace k E t (σ b)).val.ord fT < 0)
    (hvalueT₀ : (rationalConfigurationBoundaryPlace k E t (σ c₀)).val.HasValue fT aT₀)
    (hvalueT : (rationalConfigurationBoundaryPlace k E t (σ c)).val.HasValue fT aT)
    (hratioS : aS / aS₀ = algebraMap k E (crossRatio a.val b.val c₀.val c.val))
    (hratioT : aT / aT₀ = algebraMap k E
      (crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val)) :
    crossRatio a.val b.val c₀.val c.val =
      crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val := by
  obtain ⟨A, _hAplace, hA⟩ := namedSquare_exists_label_of_selected_root
    k E s qS eS hplacesS S hS a fS hfS 0 0 (by ring) hzeroS
  obtain ⟨B, _hBplace, hB⟩ := namedSquare_exists_label_of_pole
    k E s qS eS hplacesS S hS b fS hfS hpoleS
  obtain ⟨C₀, _hC₀place, hC₀⟩ := namedSquare_exists_label_of_selected_root
    k E s qS eS hplacesS S hS c₀ fS hfS aS₀ rS₀ hrS₀ hvalueS₀
  obtain ⟨C, _hCplace, hC⟩ := namedSquare_exists_label_of_selected_root
    k E s qS eS hplacesS S hS c fS hfS aS rS hrS hvalueS
  exact namedSquareModels_crossRatio_eq
    k E s t S T qS eS hplacesS hS qT eT hplacesT hT σ τ hcomm hbase hlift
    a b c₀ c hab h₀a h₀b hca hcb hc₀ A B C₀ C hA hB hC₀ hC
    fS fT hfS hfT aS₀ aS aT₀ aT rS₀ rS rT₀ rT hrS₀ hrS hrT₀ hrT
    hzeroS hpoleS hvalueS₀ hvalueS hzeroT hpoleT hvalueT₀ hvalueT hratioS hratioT

theorem namedSquareModels_match_configuration
    (hbase : ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (hlift : ∀ (a b c₀ c : S), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : Eˣ,
        (A : E) = crossRatio a.val b.val c₀.val c.val ∧
        (B : E) = crossRatio (τ a).val (τ b).val (τ c₀).val (τ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (a b c₀ : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (fS fT : RatFunc E) (hfS : eS RatFunc.X = fS) (hfT : eT RatFunc.X = fT)
    (vS rS : s → E) (vT rT : t → E)
    (hrS : ∀ x : s, x ≠ b → rS x ^ 2 = vS x)
    (hrT : ∀ x : t, x ≠ σ b → rT x ^ 2 = vT x)
    (hzeroS : vS a = 0) (hzeroT : vT (σ a) = 0)
    (hpoleS : (rationalConfigurationBoundaryPlace k E s b).val.ord fS < 0)
    (hpoleT : (rationalConfigurationBoundaryPlace k E t (σ b)).val.ord fT < 0)
    (hvalueS : ∀ x : s, x ≠ b →
      (rationalConfigurationBoundaryPlace k E s x).val.HasValue fS (vS x))
    (hvalueT : ∀ x : t, x ≠ σ b →
      (rationalConfigurationBoundaryPlace k E t x).val.HasValue fT (vT x))
    (hratioS : ∀ c : s, c ≠ b → vS c / vS c₀ =
      algebraMap k E (crossRatio a.val b.val c₀.val c.val))
    (hratioT : ∀ c : s, c ≠ b → vT (σ c) / vT (σ c₀) = algebraMap k E
      (crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val)) :
    ∀ c : s,
      matchTriples a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
        (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
        (fun h => h₀a (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => h₀b (σ.injective (Subtype.ext h)))
        (fun h => h₀a (σ.injective (Subtype.ext h))) c.val = (σ c).val := by
  have hzS : (rationalConfigurationBoundaryPlace k E s a).val.HasValue fS 0 := by
    simpa only [hzeroS] using hvalueS a hab
  have hzT : (rationalConfigurationBoundaryPlace k E t (σ a)).val.HasValue fT 0 := by
    simpa only [hzeroT] using hvalueT (σ a) (σ.injective.ne hab)
  obtain ⟨A, _hAplace, hA⟩ := namedSquare_exists_label_of_selected_root
    k E s qS eS hplacesS S hS a fS hfS 0 0 (by ring) hzS
  obtain ⟨B, _hBplace, hB⟩ := namedSquare_exists_label_of_pole
    k E s qS eS hplacesS S hS b fS hfS hpoleS
  obtain ⟨C₀, _hC₀place, hC₀⟩ := namedSquare_exists_label_of_selected_root
    k E s qS eS hplacesS S hS c₀ fS hfS (vS c₀) (rS c₀)
      (hrS c₀ h₀b) (hvalueS c₀ h₀b)
  apply matchTriples_of_crossRatios_away_from_reference σ a b c₀ hab h₀a h₀b
  intro c hca hcb hc₀
  obtain ⟨C, _hCplace, hC⟩ := namedSquare_exists_label_of_selected_root
    k E s qS eS hplacesS S hS c fS hfS (vS c) (rS c)
      (hrS c hcb) (hvalueS c hcb)
  exact namedSquareModels_crossRatio_eq
    k E s t S T qS eS hplacesS hS qT eT hplacesT hT σ τ hcomm hbase hlift
    a b c₀ c hab h₀a h₀b hca hcb hc₀ A B C₀ C hA hB hC₀ hC fS fT hfS hfT
    (vS c₀) (vS c) (vT (σ c₀)) (vT (σ c))
    (rS c₀) (rS c) (rT (σ c₀)) (rT (σ c))
    (hrS c₀ h₀b) (hrS c hcb)
    (hrT (σ c₀) (σ.injective.ne h₀b)) (hrT (σ c) (σ.injective.ne hcb))
    hzS hpoleS (hvalueS c₀ h₀b) (hvalueS c hcb)
    hzT hpoleT (hvalueT (σ c₀) (σ.injective.ne h₀b))
    (hvalueT (σ c) (σ.injective.ne hcb)) (hratioS c hcb) (hratioT c hcb)

end Named
end AnabelianGeometry.WeightFiltration
