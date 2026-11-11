/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.GenusZeroConstantModel
public import Nyll.SchemeTheory.LocalGeometry.RationalSectionFieldPoints
public import Nyll.SchemeTheory.LocalGeometry.RationalSectionCenters
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GeometricCoverRebase
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The geometric boundary over an original rational point

If the original complement is a single rational point, every geometric
boundary point is its specified scalar extension. Consequently its actual
geometric boundary has cardinality one. A larger geometric boundary supplies
an original omitted point different from the given rational point, as needed
for affineness of the actual one-point filling.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AnabelianGeometry.FiniteField

/-- The actual geometric boundary of a nonempty open of a geometrically
integral smooth proper curve is finite. Its points inject into the finite
complement on the literal base change through their original centers. -/
theorem finite_geometricBoundaryPoint
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    {C U : Scheme} (c : C ⟶ Spec (.of k))
    [GeometricallyIntegral c] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] :
    Finite (GeometricBoundaryPoint k κ c j) := by
  let φ := Spec.algebraMap k κ
  let Y := Limits.pullback φ c
  let cκ : Y ⟶ Spec (.of κ) := Limits.pullback.fst φ c
  let pr : Y ⟶ C := Limits.pullback.snd φ c
  have hI : IsIntegral Y :=
    GeometricallyIntegral.geometrically_isIntegral (f := c) φ
      pr cκ (CategoryTheory.IsPullback.of_hasPullback φ c).flip
  let V : Y.Opens := ⟨pr ⁻¹' Set.range j,
    j.isOpenEmbedding.isOpen_range.preimage pr.continuous⟩
  have hV : (V : Set Y).Nonempty := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    obtain ⟨y, hy⟩ := pr.surjective (j u)
    exact ⟨y, ⟨u, hy.symm⟩⟩
  have hfinite : ((V : Set Y)ᶜ).Finite := AlgebraicCurve.finite_compl_of_isOpen cκ V hV
  have : Finite ↥((V : Set Y)ᶜ) := hfinite.to_subtype
  let s (b : GeometricBoundaryPoint k κ c j) : Spec (.of κ) ⟶ Y :=
    Limits.pullback.lift (𝟙 _) b.val.val
      ((Category.id_comp φ).trans b.val.property.symm)
  have hs (b : GeometricBoundaryPoint k κ c j) : s b ≫ cκ = 𝟙 _ :=
    Limits.pullback.lift_fst _ _ _
  have hspr (b : GeometricBoundaryPoint k κ c j) : s b ≫ pr = b.val.val :=
    Limits.pullback.lift_snd _ _ _
  let center (b : GeometricBoundaryPoint k κ c j) : ↥((V : Set Y)ᶜ) :=
    ⟨s b (IsLocalRing.closedPoint κ), by
      change pr (s b (IsLocalRing.closedPoint κ)) ∉ Set.range j
      change (s b ≫ pr) (IsLocalRing.closedPoint κ) ∉ Set.range j
      rw [hspr]
      exact b.property⟩
  apply Finite.of_injective center
  intro b b' hbb'
  have hsEq : s b = s b' := Scheme.rationalSections_eq_of_center_eq
    cκ (s b) (s b') (hs b) (hs b') (congrArg Subtype.val hbb')
  apply Subtype.ext
  apply Subtype.ext
  exact (hspr b).symm.trans ((congrArg (fun a => a ≫ pr) hsEq).trans (hspr b'))

/-- A dominating finite étale proper cover cannot lose geometric boundary
points after rebasing each cover to its specified compatible constants.
The bound concerns the single connected full-constant component, rather
than the disconnected base change over the original ground field. -/
theorem boundaryCard_le_of_cover_domination_constant_rebase
    (k E₁ E₂ κ : Type) [Field k] [Field E₁] [Field E₂] [Field κ] [IsAlgClosed κ]
    [Algebra k E₁] [Algebra k E₂] [Algebra k κ]
    [Algebra E₁ κ] [Algebra E₂ κ]
    [IsScalarTower k E₁ κ] [IsScalarTower k E₂ κ]
    [FiniteDimensional k E₁] [FiniteDimensional k E₂]
    [Algebra.IsSeparable k E₁] [Algebra.IsSeparable k E₂]
    {X : Scheme} [ConnectedSpace X] (c : X ⟶ Spec (.of k))
    (W₁ W₂ : AlgebraicGeometry.FiniteEtale X)
    (c₁ : W₁.left ⟶ Spec (.of E₁)) (c₂ : W₂.left ⟶ Spec (.of E₂))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁]
    [GeometricallyIntegral c₁] [GeometricallyIntegral c₂]
    (hbase₁ : c₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₁)) = W₁.hom ≫ c)
    (hbase₂ : c₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₂)) = W₂.hom ≫ c)
    (t : W₁.left ⟶ W₂.left) (ht : t ≫ W₂.hom = W₁.hom)
    (φ : Spec (.of E₁) ⟶ Spec (.of E₂))
    (hcoeff : Spec.map (CommRingCat.ofHom (algebraMap E₁ κ)) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap E₂ κ)))
    (hstruct : t ≫ c₂ = c₁ ≫ φ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Nat.card (GeometricBoundaryPoint E₂ κ c₂ (W₂.hom ⁻¹ᵁ U).ι) ≤
      Nat.card (GeometricBoundaryPoint E₁ κ c₁ (W₁.hom ⁻¹ᵁ U).ι) := by
  have hW₁ : IsFiniteEtale W₁.hom := W₁.prop
  have hI₁ : IsIntegral W₁.left := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  have hsurj : Surjective W₁.hom := IsFiniteEtale.surjective (show W₁.left ⟶ X from W₁.hom)
  have hV₁ : Nonempty (W₁.hom ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := W₁.hom.surjective x
    exact ⟨⟨y, show W₁.hom y ∈ U from hy.symm ▸ hx⟩⟩
  have hfinite : Finite (GeometricBoundaryPoint E₁ κ c₁ (W₁.hom ⁻¹ᵁ U).ι) :=
    finite_geometricBoundaryPoint E₁ κ c₁ (W₁.hom ⁻¹ᵁ U).ι
  let mapB : GeometricBoundaryPoint E₁ κ c₁ (W₁.hom ⁻¹ᵁ U).ι →
      GeometricBoundaryPoint E₂ κ c₂ (W₂.hom ⁻¹ᵁ U).ι := fun p =>
    ⟨⟨p.val.val ≫ t, by
      rw [Category.assoc, hstruct, ← Category.assoc, p.val.property]
      exact hcoeff⟩, by
      have hp := p.property
      simp only [Scheme.Opens.range_ι] at hp ⊢
      change W₂.hom (t (p.val.val (IsLocalRing.closedPoint κ))) ∉ U
      have hpoint := congrArg (fun a => a (p.val.val (IsLocalRing.closedPoint κ))) ht
      change W₂.hom (t (p.val.val (IsLocalRing.closedPoint κ))) =
        W₁.hom (p.val.val (IsLocalRing.closedPoint κ)) at hpoint
      rw [hpoint]
      exact hp⟩
  apply Nat.card_le_card_of_surjective mapB
  intro p₂
  obtain ⟨p₁, hpt, hpc⟩ :=
    AlgebraicGeometry.FiniteEtale.exists_geometricPoint_lift_after_constant_rebase
      k E₁ E₂ κ c W₁ W₂ c₁ c₂ hbase₁ hbase₂ t ht φ hcoeff hstruct
        p₂.val.val p₂.val.property
  have hproj : p₁ ≫ W₁.hom = p₂.val.val ≫ W₂.hom := by
    rw [← ht, ← Category.assoc, hpt]
  have hp₁ : p₁ (IsLocalRing.closedPoint κ) ∉ Set.range (W₁.hom ⁻¹ᵁ U).ι := by
    have hp₂ := p₂.property
    simp only [Scheme.Opens.range_ι] at hp₂ ⊢
    change (p₁ ≫ W₁.hom) (IsLocalRing.closedPoint κ) ∉ U
    rw [hproj]
    exact hp₂
  refine ⟨⟨⟨p₁, hpc⟩, hp₁⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hpt

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
  {C U : Scheme} (c : C ⟶ Spec (.of k)) (j : U ⟶ C)
  (P : Spec (.of k) ⟶ C) (hP : P ≫ c = 𝟙 _)

include hP

/-- A singleton rational complement has exactly one actual geometric
boundary point, with its prescribed constant-field embedding retained. -/
theorem geometricBoundary_card_eq_one_of_boundary_singleton
    (hboundary : (Set.range j)ᶜ = ({P (IsLocalRing.closedPoint k)} : Set C)) :
    Nat.card (GeometricBoundaryPoint k κ c j) = 1 := by
  let b := Spec.algebraMap k κ
  let q : SchemeHomOver b c := ⟨b ≫ P, by rw [Category.assoc, hP, Category.comp_id]⟩
  have hqcenter : q.val (IsLocalRing.closedPoint κ) = P (IsLocalRing.closedPoint k) :=
    congrArg P (Subsingleton.elim _ _)
  have hqboundary : q.val (IsLocalRing.closedPoint κ) ∉ Set.range j := by
    change q.val (IsLocalRing.closedPoint κ) ∈ (Set.range j)ᶜ
    rw [hboundary, Set.mem_singleton_iff]
    exact hqcenter
  let qB : GeometricBoundaryPoint k κ c j := ⟨q, hqboundary⟩
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨qB, ?_⟩
  intro y
  apply Subtype.ext
  apply Subtype.ext
  apply Scheme.fieldPoint_eq_comp_rationalSection_of_center_eq c P hP b y.val.val y.val.property
  have hy : y.val.val (IsLocalRing.closedPoint κ) ∈ (Set.range j)ᶜ := y.property
  rw [hboundary, Set.mem_singleton_iff] at hy
  exact hy

/-- More than one geometric boundary point supplies an actual other
boundary point of the original compactification. -/
theorem exists_other_boundaryPoint_of_one_lt_geometricBoundary
    (hboundary : P (IsLocalRing.closedPoint k) ∉ Set.range j)
    (hcard : 1 < Nat.card (GeometricBoundaryPoint k κ c j)) :
    ∃ q : C, q ∉ Set.range j ∧ q ≠ P (IsLocalRing.closedPoint k) := by
  by_contra hother
  have hsingleton : (Set.range j)ᶜ = ({P (IsLocalRing.closedPoint k)} : Set C) := by
    apply Set.ext
    intro q
    constructor
    · intro hq
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      exact hother ⟨q, hq, hne⟩
    · intro hq
      exact (Set.mem_singleton_iff.mp hq).symm ▸ hboundary
  have hcardOne := geometricBoundary_card_eq_one_of_boundary_singleton k κ c j P hP hsingleton
  rw [hcardOne] at hcard
  exact (lt_irrefl 1) hcard

end AnabelianGeometry.FiniteField
