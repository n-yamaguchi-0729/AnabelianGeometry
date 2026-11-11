/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
public import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncCoordinate
public import Nyll.SchemeTheory.ProjectiveSpace.LinearCoordinateChange
public import Nyll.SchemeTheory.ProjectiveSpace.CrossRatioSeparation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual unit chart of a rational configuration

Two distinct omitted rational points provide independent linear forms. Their
ratio embeds the original configuration open into the actual multiplicative
coordinate chart. Polynomial-generator calculations make the construction
valid over finite fields as well as infinite fields.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjSpace
open HomogeneousLocalization MvPolynomial
open AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.FiniteField

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type} [Field k]

local notation "V₂" => Fin 2 → k
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) k

private theorem substitution_inverse (e : V₂ ≃ₗ[k] V₂) :
    (linearSubstitution e.toLinearMap).comp (linearSubstitution e.symm.toLinearMap) =
      GradedRingHom.id 𝒜 := by
  have hx (i : Fin 2) :
      linearSubstitution e.toLinearMap
        (linearSubstitution e.symm.toLinearMap (X i)) = X i := by
    have hcoeff (j : Fin 2) :
        e.symm (coordinateBasisVector 0) i * e (coordinateBasisVector j) 0 +
          e.symm (coordinateBasisVector 1) i * e (coordinateBasisVector j) 1 =
            coordinateBasisVector j i := by
      have h := eval_coordinateForm e.symm.toLinearMap i (e (coordinateBasisVector j))
      have heval :
          e.symm (coordinateBasisVector 0) i * e (coordinateBasisVector j) 0 +
            e.symm (coordinateBasisVector 1) i * e (coordinateBasisVector j) 1 =
              e.symm (e (coordinateBasisVector j)) i := by
        simpa only [coordinateForm, MvPolynomial.eval_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_C, MvPolynomial.eval_X, LinearEquiv.coe_coe] using h
      exact heval.trans
        (congrArg (fun v : V₂ => v i) (e.symm_apply_apply (coordinateBasisVector j)))
    calc
      linearSubstitution e.toLinearMap
          (linearSubstitution e.symm.toLinearMap (X i)) =
          C (e.symm (coordinateBasisVector 0) i * e (coordinateBasisVector 0) 0 +
            e.symm (coordinateBasisVector 1) i * e (coordinateBasisVector 0) 1) * X 0 +
          C (e.symm (coordinateBasisVector 0) i * e (coordinateBasisVector 1) 0 +
            e.symm (coordinateBasisVector 1) i * e (coordinateBasisVector 1) 1) * X 1 := by
        simp only [linearSubstitution_X, coordinateForm, map_add, map_mul,
          linearSubstitution_C, LinearEquiv.coe_coe]
        ring
      _ = C (coordinateBasisVector 0 i) * X 0 + C (coordinateBasisVector 1 i) * X 1 := by
        rw [hcoeff 0, hcoeff 1]
      _ = X i := by
        fin_cases i <;>
          norm_num [coordinateBasisVector, Pi.single_apply]
  apply GradedRingHom.ext
  intro p
  change linearSubstitution e.toLinearMap
    (linearSubstitution e.symm.toLinearMap p) = p
  induction p using MvPolynomial.induction_on with
  | C a => rw [linearSubstitution_C, linearSubstitution_C]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp, hx]

private def linearProjMap (e : V₂ ≃ₗ[k] V₂) : Proj 𝒜 ⟶ Proj 𝒜 :=
  Proj.map (linearSubstitution e.toLinearMap)
    (irrelevant_le_map_of_graded_rightInverse _ _ (substitution_inverse e))

private theorem projMap_congr (f g : 𝒜 →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map g (HomogeneousIdeal.irrelevant 𝒜))
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  cases h
  rfl

private theorem linearProjMap_comp_symm (e : V₂ ≃ₗ[k] V₂) :
    linearProjMap e ≫ linearProjMap e.symm = 𝟙 _ := by
  unfold linearProjMap
  exact (Proj.map_comp _ _ _ _).symm.trans
    ((projMap_congr _ _ _ _ (substitution_inverse e)).trans Proj.map_id)

private def linearProjIso (e : V₂ ≃ₗ[k] V₂) : Proj 𝒜 ≅ Proj 𝒜 where
  hom := linearProjMap e
  inv := linearProjMap e.symm
  hom_inv_id := linearProjMap_comp_symm e
  inv_hom_id := linearProjMap_comp_symm e.symm

private theorem away_comp_base {d : ℕ} (hd : 0 < d)
    (s : MvPolynomial (Fin 2) k) (hs : s ∈ 𝒜 d) :
    Proj.awayι 𝒜 s hs hd ≫ π k 1 =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers s)).comp
          (grad0Equiv k 1).toRingHom)) := by
  unfold π
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem linearProjMap_base_chart (e : V₂ ≃ₗ[k] V₂)
    {d : ℕ} (hd : 0 < d) (s : MvPolynomial (Fin 2) k) (hs : s ∈ 𝒜 d) :
    Proj.awayι 𝒜 (linearSubstitution e.toLinearMap s)
        ((linearSubstitution e.toLinearMap).map_mem hs) hd ≫ linearProjMap e ≫ π k 1 =
      Proj.awayι 𝒜 (linearSubstitution e.toLinearMap s)
        ((linearSubstitution e.toLinearMap).map_mem hs) hd ≫ π k 1 := by
  unfold linearProjMap
  rw [← Category.assoc,
    Proj.awayι_comp_map (linearSubstitution e.toLinearMap)
      (irrelevant_le_map_of_graded_rightInverse _ _ (substitution_inverse e)) hd s hs,
    Category.assoc,
    away_comp_base hd s hs,
    away_comp_base hd (linearSubstitution e.toLinearMap s)
      ((linearSubstitution e.toLinearMap).map_mem hs),
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (linearSubstitution_awayMap_fromZero e.toLinearMap s)

private theorem linearProjMap_base (e : V₂ ≃ₗ[k] V₂) :
    linearProjMap e ≫ π k 1 = π k 1 := by
  refine (Proj.mapAffineOpenCover (linearSubstitution e.toLinearMap)
    (irrelevant_le_map_of_graded_rightInverse _ _ (substitution_inverse e))).openCover.hom_ext
      _ _ fun i => ?_
  obtain ⟨⟨d, hd⟩, s, hs⟩ := i
  exact linearProjMap_base_chart e hd s hs

private theorem polynomialChart_range :
    Set.range (projectiveLinePolynomialChart k) =
      (Proj.basicOpen 𝒜 (X (1 : Fin 2)) : Set (Proj 𝒜)) := by
  have : IsIso
      (Spec.map (CommRingCat.ofHom (projectiveLinePolynomialChartEquiv k).symm.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map
      (projectiveLinePolynomialChartEquiv k).symm.toRingEquiv.toCommRingCatIso.hom))
  change ((projectiveLinePolynomialChart k).opensRange : Set (Proj 𝒜)) = _
  unfold projectiveLinePolynomialChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

private theorem polynomialChart_zero_preimage :
    projectiveLinePolynomialChart k ⁻¹ᵁ Proj.basicOpen 𝒜 (X (0 : Fin 2)) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) :
        (Spec (CommRingCat.of (Polynomial k))).Opens) := by
  have helem : HomogeneousLocalization.Away.isLocalizationElem
      (X_mem_one k 1 1) (X_mem_one k 1 0) = ratio k 1 1 0 := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.isLocalizationElem, ratio,
      HomogeneousLocalization.Away.val_mk, pow_one]
  unfold projectiveLinePolynomialChart
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 (X_mem_one k 1 1) one_pos (X_mem_one k 1 0) one_pos,
    helem, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen ((projectiveLinePolynomialChartEquiv k).symm
      (ratio k 1 1 0)) = _
  rw [← projectiveLinePolynomialChartEquiv_X, AlgEquiv.symm_apply_apply]

/-- Two actual omitted rational points give an open immersion of the original
configuration into the original polynomial unit chart, over the same field.
The construction works in every characteristic, including over finite fields. -/
theorem exists_rationalConfiguration_unitChart
    (s : Finset (Projectivization k (k × k))) (a b : s) (hab : a ≠ b) :
    ∃ j : (rationalConfigurationOpen s : Scheme) ⟶
        Spec (CommRingCat.of (Localization.Away (Polynomial.X : Polynomial k))),
      IsOpenImmersion j ∧
        j ≫ Spec.algebraMap k (Localization.Away (Polynomial.X : Polynomial k)) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  have hneq : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hdet : a.val.rep.2 * (-b.val.rep.1) - (-a.val.rep.1) * b.val.rep.2 ≠ 0 := by
    have hb : bracket a.val.rep b.val.rep ≠ 0 :=
      fun h => hneq ((bracket_rep_eq_zero_iff a.val b.val).mp h)
    convert hb using 1
    unfold bracket
    ring
  let e := finCoordinateEquiv
    (coordinateLinearEquiv a.val.rep.2 (-a.val.rep.1) b.val.rep.2 (-b.val.rep.1) hdet)
  have hb₀ : coordinateBasisVector (K := k) 0 = pairCoordinates (1, 0) := by
    ext i
    fin_cases i <;> rfl
  have hb₁ : coordinateBasisVector (K := k) 1 = pairCoordinates (0, 1) := by
    ext i
    fin_cases i <;> rfl
  have he₀ : e (coordinateBasisVector 0) = ![a.val.rep.2, b.val.rep.2] := by
    calc
      e (coordinateBasisVector 0) = pairCoordinates
          (coordinateLinearEquiv a.val.rep.2 (-a.val.rep.1)
            b.val.rep.2 (-b.val.rep.1) hdet (1, 0)) :=
        (congrArg e hb₀).trans (finCoordinateEquiv_pairCoordinates _ _)
      _ = _ := by
        change ![a.val.rep.2 * 1 + (-a.val.rep.1) * 0,
          b.val.rep.2 * 1 + (-b.val.rep.1) * 0] = _
        simp only [mul_one, mul_zero, add_zero]
  have he₁ : e (coordinateBasisVector 1) = ![-a.val.rep.1, -b.val.rep.1] := by
    calc
      e (coordinateBasisVector 1) = pairCoordinates
          (coordinateLinearEquiv a.val.rep.2 (-a.val.rep.1)
            b.val.rep.2 (-b.val.rep.1) hdet (0, 1)) :=
        (congrArg e hb₁).trans (finCoordinateEquiv_pairCoordinates _ _)
      _ = _ := by
        change ![a.val.rep.2 * 0 + (-a.val.rep.1) * 1,
          b.val.rep.2 * 0 + (-b.val.rep.1) * 1] = _
        simp only [mul_zero, mul_one, zero_add]
  have hform₀ : linearSubstitution e.toLinearMap (X 0) = punctureForm a.val.rep := by
    rw [linearSubstitution_X]
    change C (e (coordinateBasisVector 0) 0) * X 0 +
      C (e (coordinateBasisVector 1) 0) * X 1 = _
    rw [congrFun he₀ 0, congrFun he₁ 0]
    change C a.val.rep.2 * X 0 + C (-a.val.rep.1) * X 1 = _
    rw [map_neg, neg_mul, ← sub_eq_add_neg]
    rfl
  have hform₁ : linearSubstitution e.toLinearMap (X 1) = punctureForm b.val.rep := by
    rw [linearSubstitution_X]
    change C (e (coordinateBasisVector 0) 1) * X 0 +
      C (e (coordinateBasisVector 1) 1) * X 1 = _
    rw [congrFun he₀ 1, congrFun he₁ 1]
    change C b.val.rep.2 * X 0 + C (-b.val.rep.1) * X 1 = _
    rw [map_neg, neg_mul, ← sub_eq_add_neg]
    rfl
  let E := linearProjIso e
  let m := (rationalConfigurationOpen s).ι ≫ E.hom
  have havoid (v : s) (u : (rationalConfigurationOpen s : Scheme)) :
      punctureForm v.val.rep ∉ u.val.asHomogeneousIdeal := by
    intro h
    apply (mem_rationalConfigurationOpen_iff s u.val).mp u.property v.val v.property
    exact eq_of_punctureForm_mem v.val.rep v.val.rep_nonzero _ _ h
      (punctureForm_mem_rationalPuncturePoint v.val.rep v.val.rep_nonzero)
  have hm₀ (u : (rationalConfigurationOpen s : Scheme)) :
      m u ∈ Proj.basicOpen 𝒜 (X (0 : Fin 2)) := by
    change u.val ∈ linearProjMap e ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0)
    rw [linearProjMap, Proj.map_preimage_basicOpen, hform₀]
    exact havoid a u
  have hm₁ (u : (rationalConfigurationOpen s : Scheme)) :
      m u ∈ Proj.basicOpen 𝒜 (X (1 : Fin 2)) := by
    change u.val ∈ linearProjMap e ⁻¹ᵁ Proj.basicOpen 𝒜 (X 1)
    rw [linearProjMap, Proj.map_preimage_basicOpen, hform₁]
    exact havoid b u
  have hchart : Set.range m ⊆ Set.range (projectiveLinePolynomialChart k) := by
    rintro _ ⟨u, rfl⟩
    rw [polynomialChart_range]
    exact hm₁ u
  let t := IsOpenImmersion.lift (projectiveLinePolynomialChart k) m hchart
  have ht : t ≫ projectiveLinePolynomialChart k = m := IsOpenImmersion.lift_fac _ _ _
  have hmopen : IsOpenImmersion m := inferInstanceAs
    (IsOpenImmersion ((rationalConfigurationOpen s).ι ≫ E.hom))
  have : IsOpenImmersion (t ≫ projectiveLinePolynomialChart k) := ht.symm ▸ hmopen
  have : IsOpenImmersion t := IsOpenImmersion.of_comp t (projectiveLinePolynomialChart k)
  let R := Localization.Away (Polynomial.X : Polynomial k)
  let loc := Spec.algebraMap (Polynomial k) R
  let unitOpen : (Spec (CommRingCat.of (Polynomial k))).Opens := by
    exact PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)
  have hloc : Set.range loc = (unitOpen : Set (Spec (CommRingCat.of (Polynomial k)))) := by
    change Set.range (PrimeSpectrum.comap (algebraMap (Polynomial k) R)) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k)))
    exact PrimeSpectrum.localization_away_comap_range R (Polynomial.X : Polynomial k)
  have hunit : Set.range t ⊆ Set.range loc := by
    rintro _ ⟨u, rfl⟩
    rw [hloc]
    have hpre : projectiveLinePolynomialChart k ⁻¹ᵁ Proj.basicOpen 𝒜 (X (0 : Fin 2)) =
        unitOpen := polynomialChart_zero_preimage
    change t u ∈ unitOpen
    rw [← hpre]
    change projectiveLinePolynomialChart k (t u) ∈ Proj.basicOpen 𝒜 (X 0)
    exact (congrArg (fun f => f u) ht) ▸ hm₀ u
  let j := IsOpenImmersion.lift loc t hunit
  have hj : j ≫ loc = t := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (j ≫ loc) := hj.symm ▸ inferInstance
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j loc
  refine ⟨j, inferInstance, ?_⟩
  have hcoef : loc ≫ Spec.algebraMap k (Polynomial k) = Spec.algebraMap k R :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap k (Polynomial k)))
      (CommRingCat.ofHom (algebraMap (Polynomial k) R))).symm.trans
        (congrArg (fun f : k →+* R => Spec.map (CommRingCat.ofHom f))
          (IsScalarTower.algebraMap_eq k (Polynomial k) R).symm)
  calc
    j ≫ Spec.algebraMap k R = (j ≫ loc) ≫ Spec.algebraMap k (Polynomial k) :=
      (congrArg (j ≫ ·) hcoef).symm.trans (Category.assoc _ _ _).symm
    _ = t ≫ Spec.algebraMap k (Polynomial k) := congrArg (· ≫ _) hj
    _ = (t ≫ projectiveLinePolynomialChart k) ≫ π k 1 :=
      (congrArg (t ≫ ·) (projectiveLinePolynomialChart_comp_π k)).symm.trans
        (Category.assoc _ _ _).symm
    _ = m ≫ π k 1 := congrArg (· ≫ _) ht
    _ = (rationalConfigurationOpen s).ι ≫ π k 1 :=
      (Category.assoc _ _ _).trans
        (congrArg ((rationalConfigurationOpen s).ι ≫ ·) (linearProjMap_base e))

end AnabelianGeometry.FiniteField
