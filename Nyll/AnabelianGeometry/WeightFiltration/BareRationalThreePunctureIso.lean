/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchIso
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationPunctureEquiv
import Mathlib.Data.Finset.Card

/-! # Scheme isomorphisms for three rational punctures -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine EtaleFundamentalGroups AlgebraicGeometry.FiniteEtale
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

theorem rationalConfiguration_schemeIso_of_card_eq_three
    (k : Type) [Field k] [Infinite k]
    (s t : Finset (Projectivization k (k × k))) (hs : s.card = 3) (σ : s ≃ t) :
    ∃ f : (k × k) ≃ₗ[k] (k × k),
      (∀ c : s, projectiveLinearEquiv f c.val = (σ c).val) ∧
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅
          (rationalConfigurationOpen t : Scheme),
        I.hom ≫ (rationalConfigurationOpen t).ι =
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  classical
  obtain ⟨a₀, b₀, c₀, hab₀, hac₀, hbc₀, hs⟩ := Finset.card_eq_three.mp hs
  have ha : a₀ ∈ s := by rw [hs]; exact Finset.mem_insert_self _ _
  have hb : b₀ ∈ s := by
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hc : c₀ ∈ s := by
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let a : s := ⟨a₀, ha⟩
  let b : s := ⟨b₀, hb⟩
  let c : s := ⟨c₀, hc⟩
  have hab : a ≠ b := fun h => hab₀ (congrArg Subtype.val h)
  have hca : c ≠ a := fun h => hac₀ (congrArg Subtype.val h).symm
  have hcb : c ≠ b := fun h => hbc₀ (congrArg Subtype.val h).symm
  have hfirst (p q r : Projectivization k (k × k))
      (hpq : p ≠ q) (hrq : r ≠ q) (hrp : r ≠ p) :
      normalizeTriple p q r hpq hrq hrp p = affinePoint 0 := by
    change normalizeCoordinates p.rep q.rep r.rep _ _ _ p = affinePoint 0
    calc
      normalizeCoordinates p.rep q.rep r.rep _ _ _ p =
          normalizeCoordinates p.rep q.rep r.rep _ _ _
            (Projectivization.mk k p.rep p.rep_nonzero) :=
        congrArg (normalizeCoordinates p.rep q.rep r.rep _ _ _) p.mk_rep.symm
      _ = affinePoint 0 := normalizeCoordinates_first _ _ _ _ _ _ p.rep_nonzero
  have hthird (p q r : Projectivization k (k × k))
      (hpq : p ≠ q) (hrq : r ≠ q) (hrp : r ≠ p) :
      normalizeTriple p q r hpq hrq hrp r = affinePoint 1 := by
    change normalizeCoordinates p.rep q.rep r.rep _ _ _ r = affinePoint 1
    calc
      normalizeCoordinates p.rep q.rep r.rep _ _ _ r =
          normalizeCoordinates p.rep q.rep r.rep _ _ _
            (Projectivization.mk k r.rep r.rep_nonzero) :=
        congrArg (normalizeCoordinates p.rep q.rep r.rep _ _ _) r.mk_rep.symm
      _ = affinePoint 1 := normalizeCoordinates_third _ _ _ _ _ _ r.rep_nonzero
  have hmatch : ∀ z : s,
      matchTriples a.val b.val c.val (σ a).val (σ b).val (σ c).val
        (fun h => hab (Subtype.ext h)) (fun h => hcb (Subtype.ext h))
        (fun h => hca (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => hcb (σ.injective (Subtype.ext h)))
        (fun h => hca (σ.injective (Subtype.ext h))) z.val = (σ z).val := by
    intro z
    have hz : z = a ∨ z = b ∨ z = c := by
      have hzmem := (congrArg
        (fun u : Finset (Projectivization k (k × k)) => z.val ∈ u) hs).mp z.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
      rcases hzmem with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    rcases hz with rfl | rfl | rfl
    · apply (normalizeTriple (σ a).val (σ b).val (σ c).val
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => hcb (σ.injective (Subtype.ext h)))
        (fun h => hca (σ.injective (Subtype.ext h)))).injective
      change (normalizeTriple (σ a).val (σ b).val (σ c).val
          (fun h => hab (σ.injective (Subtype.ext h)))
          (fun h => hcb (σ.injective (Subtype.ext h)))
          (fun h => hca (σ.injective (Subtype.ext h))))
        ((normalizeTriple (σ a).val (σ b).val (σ c).val
          (fun h => hab (σ.injective (Subtype.ext h)))
          (fun h => hcb (σ.injective (Subtype.ext h)))
          (fun h => hca (σ.injective (Subtype.ext h)))).symm
          (normalizeTriple a.val b.val c.val
            (fun h => hab (Subtype.ext h)) (fun h => hcb (Subtype.ext h))
            (fun h => hca (Subtype.ext h)) a.val)) = _
      rw [Equiv.apply_symm_apply, hfirst, hfirst]
    · exact matchTriples_second _ _ _ _ _ _ _ _ _ _ _ _
    · apply (normalizeTriple (σ a).val (σ b).val (σ c).val
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => hcb (σ.injective (Subtype.ext h)))
        (fun h => hca (σ.injective (Subtype.ext h)))).injective
      change (normalizeTriple (σ a).val (σ b).val (σ c).val
          (fun h => hab (σ.injective (Subtype.ext h)))
          (fun h => hcb (σ.injective (Subtype.ext h)))
          (fun h => hca (σ.injective (Subtype.ext h))))
        ((normalizeTriple (σ a).val (σ b).val (σ c).val
          (fun h => hab (σ.injective (Subtype.ext h)))
          (fun h => hcb (σ.injective (Subtype.ext h)))
          (fun h => hca (σ.injective (Subtype.ext h)))).symm
          (normalizeTriple a.val b.val c.val
            (fun h => hab (Subtype.ext h)) (fun h => hcb (Subtype.ext h))
            (fun h => hca (Subtype.ext h)) c.val)) = _
      rw [Equiv.apply_symm_apply, hthird, hthird]
  exact ⟨matchTriplesLinearEquiv a.val b.val c.val (σ a).val (σ b).val (σ c).val
      (fun h => hab (Subtype.ext h)) (fun h => hcb (Subtype.ext h))
      (fun h => hca (Subtype.ext h))
      (fun h => hab (σ.injective (Subtype.ext h)))
      (fun h => hcb (σ.injective (Subtype.ext h)))
      (fun h => hca (σ.injective (Subtype.ext h))),
    rationalConfiguration_schemeIso_of_matchTriples k s t σ a b c hab hca hcb hmatch⟩

theorem bare_rationalConfiguration_schemeIso_of_card_eq_three
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : s.card = 3) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t,
        (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom) ∧
        ∃ f : (k × k) ≃ₗ[k] (k × k),
          (∀ c : s, projectiveLinearEquiv f c.val = (σ c).val) ∧
          ∃ I : (rationalConfigurationOpen s : Scheme) ≅
              (rationalConfigurationOpen t : Scheme),
            I.hom ≫ (rationalConfigurationOpen t).ι =
              (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
            I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
              (rationalConfigurationOpen s).ι ≫ π k 1 := by
  obtain ⟨eΔ, hΔ, σ, hI⟩ := bare_rationalConfiguration_punctureEquiv
    k κ s t (by rw [hs]) ht Ω₁ Ω₂ eP hP
  exact ⟨eΔ, hΔ, σ, hI, rationalConfiguration_schemeIso_of_card_eq_three k s t hs σ⟩

end AnabelianGeometry.WeightFiltration
