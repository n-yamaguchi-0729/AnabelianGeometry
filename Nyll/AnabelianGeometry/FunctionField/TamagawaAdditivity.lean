/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FunctionField.MinimalPencils
public import Nyll.AnabelianGeometry.FunctionField.ThreePointPencil
public import Nyll.AnabelianGeometry.FunctionField.MinimalPencilGeneration
public import Nyll.AnabelianGeometry.FunctionField.TamagawaPencilComparison
public import Nyll.AnabelianGeometry.FunctionField.PlacewiseAdditivity
public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseAlgClosedTranscendental
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.CanonicalDivisorGenusRiemannRoch
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.AlgebraicCurves.Models.Points.InfinitePlace
public import Mathlib.Data.Set.Card

/-!
# Tamagawa's additive reconstruction from three principal-unit subgroups

The hypotheses are the actual hypotheses of Lemma 4.7 in Tamagawa (1997):
curve function fields over algebraically closed fields, a multiplicative
equivalence preserving the orders at corresponding places, and preservation
of principal units at a set containing three distinct places.

The constant-field ring homomorphism, minimal-pencil transport, and the
multiplicative generating family are constructed inside the proof. None of
their conclusions is assumed in the endpoint statement.

-/

@[expose] public section

noncomputable section

namespace AnabelianGeometry.FunctionField

open AlgebraicCurve Filter Polynomial
open scoped IntermediateField

variable {K₁ K₂ F₁ F₂ : Type*}
  [Field K₁] [Field K₂] [Field F₁] [Field F₂]
  [Algebra K₁ F₁] [Algebra K₂ F₂]

/-- Constants correspond before any additivity has been proved. -/
theorem mem_constants_iff_of_preserves_ord
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (v P).ord (φ x) = P.ord x)
    (hC₁ : ConstantsAreBase K₁ F₁) (hC₂ : ConstantsAreBase K₂ F₂)
    (x : F₁) :
    φ x ∈ Set.range (algebraMap K₂ F₂) ↔ x ∈ Set.range (algebraMap K₁ F₁) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := constantMapOfPreservesOrd_surjective φ v hord hC₁ hC₂ b
    refine ⟨a, φ.injective ?_⟩
    rw [← constantMapOfPreservesOrd_spec φ v hord hC₂ a, ha]
    exact hb
  · rintro ⟨a, rfl⟩
    exact exists_constant_image_of_preserves_ord φ v hord hC₂ a

/-- Values on the entire subfield of a normalized minimal function are
preserved at all but finitely many places. The only distinguished-place input
is preservation of principal units at its zero and pole. -/
theorem eventually_hasValue_of_normalized_minimal
    [IsCurveOver K₁ F₁] [IsCurveOver K₂ F₂]
    [IsAlgClosed K₁] [IsAlgClosed K₂]
    [FiniteDimensional K₁ (LSpace (0 : Divisor K₁ F₁))]
    [FiniteDimensional K₂ (LSpace (0 : Divisor K₂ F₂))]
    (hC₁ : ConstantsAreBase K₁ F₁) (hC₂ : ConstantsAreBase K₂ F₂)
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (v P).ord (φ x) = P.ord x)
    (σ : K₁ →+* K₂)
    (hσ : ∀ a, algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a))
    (P₀ PInf : Place K₁ F₁)
    (hunit₀ : ∀ u, P₀.HasValue u 1 → (v P₀).HasValue (φ u) 1)
    (hunitInf : ∀ u, PInf.HasValue u 1 → (v PInf).HasValue (φ u) 1)
    {x : F₁} (hx : IsMinimal (K := K₁) x)
    (hx₀ : P₀.HasValue x 0) (hxInf : PInf.HasValue x⁻¹ 0)
    {y : F₁} (hy : y ∈ K₁⟮x⟯) :
    ∀ᶠ P in cofinite, ∃ a : K₁, P.HasValue y a ∧ (v P).HasValue (φ y) (σ a) := by
  have hconst := mem_constants_iff_of_preserves_ord φ v hord hC₁ hC₂
  have hx₂ := isMinimal_map hC₁ hC₂ φ v hord hconst hx
  have hnc : φ x ∉ Set.range (algebraMap K₂ F₂) := hx₂.not_constant hC₂
  have hx0 : x ≠ 0 := by
    intro h
    exact hx.not_constant hC₁ ⟨0, (map_zero _).trans h.symm⟩
  obtain ⟨D₁, hD₁, _⟩ := hx
  obtain ⟨D₂, hD₂, hdim₂⟩ := hx₂
  have hD : ∀ P, D₂ (v P) = D₁ P := by
    intro P
    rw [hD₂, hord, hD₁]
  have hvalue₀ : ∀ t a, P₀.HasValue t a → (v P₀).HasValue (φ t) (σ a) := by
    intro t a ht
    exact hasValue_of_preserves_ord_and_principalUnits φ σ.toMonoidWithZeroHom hσ
      P₀ (v P₀) (hord P₀) hunit₀ ht
  have hvalueInf : ∀ t a, PInf.HasValue t a → (v PInf).HasValue (φ t) (σ a) := by
    intro t a ht
    exact hasValue_of_preserves_ord_and_principalUnits φ σ.toMonoidWithZeroHom hσ
      PInf (v PInf) (hord PInf) hunitInf ht
  have hlinear (a : K₁) :
      φ (x + algebraMap K₁ F₁ a) = φ x + algebraMap K₂ F₂ (σ a) := by
    have h := map_affine_of_two_point_pencil φ σ.toMonoidWithZeroHom v hord
      D₁ D₂ hD (pole_divisor_nonneg hD₁) hdim₂ P₀ PInf hvalue₀ hvalueInf
      (mem_lSpace_pole_divisor hD₁) hnc hx0 hx₀ hxInf 1 a
    simpa only [RingHom.coe_toMonoidWithZeroHom, map_one, one_mul] using h
  have hpoly (p : K₁[X]) : φ (aeval x p) = aeval (φ x) (p.map σ) :=
    map_aeval_of_map_linear_factors φ σ hσ x hlinear p
  have hrat (P : Place K₁ F₁) : P.IsRational :=
    P.isRational_iff_deg_eq_one.mpr (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  exact eventually_hasValue_on_adjoin_of_map_aeval hrat φ σ hσ v hord x hpoly hy

/-- Tamagawa (1997), Lemma 4.7, in the place presentation of smooth proper
curve function fields. `HasValue u 1` means precisely `u ∈ 1 + 𝔪_P`.
The distinguished set may be infinite; three distinct members suffice. -/
theorem map_add_of_preserves_orders_and_three_principal_units
    [IsCurveOver K₁ F₁] [IsCurveOver K₂ F₂]
    [IsAlgClosed K₁] [IsAlgClosed K₂]
    [Algebra.EssFiniteType K₁ F₁] [Algebra.EssFiniteType K₂ F₂]
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (v P).ord (φ x) = P.ord x)
    (S : Set (Place K₁ F₁))
    (hS : ∃ P₀ ∈ S, ∃ P₁ ∈ S, ∃ PInf ∈ S, P₀ ≠ P₁ ∧ P₀ ≠ PInf ∧ P₁ ≠ PInf)
    (hunit : ∀ P ∈ S, ∀ u, P.HasValue u 1 ↔ (v P).HasValue (φ u) 1)
    (a b : F₁) : φ (a + b) = φ a + φ b := by
  classical
  obtain ⟨P₀, hP₀, P₁, hP₁, PInf, hPInf, h01, h0Inf, h1Inf⟩ := hS
  have : Nonempty (Place K₁ F₁) := ⟨P₀⟩
  have : Nonempty (Place K₂ F₂) := ⟨v P₀⟩
  have : FiniteDimensional K₁ (LSpace (0 : Divisor K₁ F₁)) :=
    finiteDimensional_lSpace_zero K₁ F₁
  have : FiniteDimensional K₂ (LSpace (0 : Divisor K₂ F₂)) :=
    finiteDimensional_lSpace_zero K₂ F₂
  obtain ⟨t₁, ht₁, hfd₁, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K₁) (F := F₁)
  obtain ⟨t₂, ht₂, hfd₂, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K₂) (F := F₂)
  have : FiniteDimensional K₁⟮t₁⟯ F₁ := hfd₁
  have : FiniteDimensional K₂⟮t₂⟯ F₂ := hfd₂
  have hC₁ : ConstantsAreBase K₁ F₁ :=
    constantsAreBase_of_isAlgClosed_of_transcendental t₁ ht₁
  have hC₂ : ConstantsAreBase K₂ F₂ :=
    constantsAreBase_of_isAlgClosed_of_transcendental t₂ ht₂
  obtain ⟨M₁⟩ := CurveModel.nonempty_of_perfectField K₁ F₁ ⟨t₁, ht₁, hfd₁⟩
  have : Infinite (Place K₁ F₁) := CurveModel.infinite_place M₁
  have hconst := mem_constants_iff_of_preserves_ord φ v hord hC₁ hC₂
  obtain ⟨x, hx, hx₀, hx₁, hxInf⟩ := exists_three_point_minimal P₀ P₁ PInf h01 h0Inf h1Inf
  have hx₂ := isMinimal_map hC₁ hC₂ φ v hord hconst hx
  obtain ⟨D₁, hD₁, _⟩ := hx
  obtain ⟨D₂, hD₂, hdim₂⟩ := hx₂
  have hD : ∀ P, D₂ (v P) = D₁ P := by
    intro P
    rw [hD₂, hord, hD₁]
  have hunits : ∀ P ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)),
      ∀ u, P.HasValue u 1 → (v P).HasValue (φ u) 1 := by
    intro P hP u hu
    have hPS : P ∈ S := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with rfl | rfl | rfl
      · exact hP₀
      · exact hP₁
      · exact hPInf
    exact (hunit P hPS u).mp hu
  obtain ⟨σ, hσ⟩ := exists_constant_ringHom_of_three_point_pencil φ v hord hC₂
    D₁ D₂ hD (pole_divisor_nonneg hD₁) hdim₂ P₀ P₁ PInf hunits
    (mem_lSpace_pole_divisor hD₁) hx₀ hx₁ hxInf
  let T : Finset (Place K₁ F₁) := {P₀, P₁}
  have hT : 1 < T.card := by
    simpa only [T, Finset.card_pair h01] using (by decide : 1 < (2 : ℕ))
  have hTS : (↑T : Set (Place K₁ F₁)) ⊆ S := by
    intro P hP
    simp only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hP₀
    · exact hP₁
  obtain ⟨W, g, hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K₁ F₁
  let G : Set F₁ := normalizedMinimalSubfieldGenerators (↑T : Set (Place K₁ F₁))
  have hG : Submonoid.closure G = ⊤ :=
    closure_normalizedMinimalSubfieldGenerators_eq_top hC₁ W g hRR T hT
      Set.univ Set.infinite_univ
  apply map_add_of_multiplicative_generators φ.toMonoidWithZeroHom σ v v.injective G hG
    ?_ a b
  intro y hy
  obtain ⟨z, hz, ⟨R, hR, Q, hQ, hzR, hzQ⟩, hyz⟩ := hy
  exact eventually_hasValue_of_normalized_minimal hC₁ hC₂ φ v hord σ hσ R Q
    (fun u hu => (hunit R (hTS hR) u).mp hu)
    (fun u hu => (hunit Q (hTS hQ) u).mp hu) hz hzR hzQ hyz

/-- The cardinality formulation of Tamagawa (1997), Lemma 4.7.
`Set.encard` covers finite and infinite distinguished subsets uniformly. -/
theorem tamagawa_additivity
    [IsCurveOver K₁ F₁] [IsCurveOver K₂ F₂]
    [IsAlgClosed K₁] [IsAlgClosed K₂]
    [Algebra.EssFiniteType K₁ F₁] [Algebra.EssFiniteType K₂ F₂]
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (v P).ord (φ x) = P.ord x)
    (S : Set (Place K₁ F₁)) (hS : 3 ≤ S.encard)
    (hunit : ∀ P ∈ S, ∀ u, P.HasValue u 1 ↔ (v P).HasValue (φ u) 1) :
    ∀ a b : F₁, φ (a + b) = φ a + φ b := by
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_encard_eq hS
  obtain ⟨P₀, P₁, PInf, h01, h0Inf, h1Inf, hTeq⟩ := Set.encard_eq_three.mp hT
  rw [hTeq] at hTS
  have hP₀ : P₀ ∈ S := hTS (Set.mem_insert _ _)
  have hP₁ : P₁ ∈ S := hTS (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hPInf : PInf ∈ S :=
    hTS (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact map_add_of_preserves_orders_and_three_principal_units φ v hord S
    ⟨P₀, hP₀, P₁, hP₁, PInf, hPInf, h01, h0Inf, h1Inf⟩ hunit

end AnabelianGeometry.FunctionField
