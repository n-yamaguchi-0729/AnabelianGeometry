/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.GeometricBoundaryCount
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GeometricCoverRebase
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
public import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
public import Nyll.SchemeTheory.LocalGeometry.Points
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback

/-!
# Boundary domination for compactified open covers

The transition on the original open covers is finite étale. Its extension
to the proper curves may ramify at omitted points. On each compatible pair
of full-constant geometric components, the open transition is surjective;
the proper extension is therefore dominant and surjective as well. This
retains a single component and proves boundary growth in every characteristic.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.FiniteField

/-- Boundary cardinality cannot decrease under an actual domination of
finite étale open covers with compatible full constants. Only the open
transition is étale; its proper extension may ramify at the boundary. -/
theorem boundaryCard_le_of_compactified_open_cover_domination
    (k E₁ E₂ κ : Type) [Field k] [Field E₁] [Field E₂] [Field κ] [IsAlgClosed κ]
    [Algebra k E₁] [Algebra k E₂] [Algebra k κ] [Algebra E₁ κ] [Algebra E₂ κ]
    [IsScalarTower k E₁ κ] [IsScalarTower k E₂ κ]
    [FiniteDimensional k E₁] [FiniteDimensional k E₂]
    [Algebra.IsSeparable k E₁] [Algebra.IsSeparable k E₂]
    {X C₁ C₂ : Scheme} (f : X ⟶ Spec (.of k))
    (W₁ W₂ : FiniteEtale X) [Nonempty W₁.left] [Nonempty W₂.left]
    (c₁ : C₁ ⟶ Spec (.of E₁)) (c₂ : C₂ ⟶ Spec (.of E₂))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (j₁ : W₁.left ⟶ C₁) (j₂ : W₂.left ⟶ C₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hbase₁ : (j₁ ≫ c₁) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₁)) = W₁.hom ≫ f)
    (hbase₂ : (j₂ ≫ c₂) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₂)) = W₂.hom ≫ f)
    (t : W₁ ⟶ W₂) (d : C₁ ⟶ C₂) (hd : j₁ ≫ d = t.left ≫ j₂)
    (φ : Spec (.of E₁) ⟶ Spec (.of E₂))
    (hcoeff : Spec.map (CommRingCat.ofHom (algebraMap E₁ κ)) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap E₂ κ)))
    (hstruct : d ≫ c₂ = c₁ ≫ φ)
    (hboundary : ∀ z : C₁, d z ∉ Set.range j₂ ↔ z ∉ Set.range j₁) :
    Nat.card (GeometricBoundaryPoint E₂ κ c₂ j₂) ≤
      Nat.card (GeometricBoundaryPoint E₁ κ c₁ j₁) := by
  let ψ₁ := Spec.map (CommRingCat.ofHom (algebraMap E₁ κ))
  let ψ₂ := Spec.map (CommRingCat.ofHom (algebraMap E₂ κ))
  have : GeometricallyIntegral (j₁ ≫ c₁) :=
    GeometricallyIntegral.comp_of_isOpenImmersion j₁ c₁
  have : GeometricallyIntegral (j₂ ≫ c₂) :=
    GeometricallyIntegral.comp_of_isOpenImmersion j₂ c₂
  obtain ⟨r, hr, hrsurj, hrfst, hrsnd⟩ :=
    exists_surjective_geometricCover_rebase_map k E₁ E₂ κ f W₁ W₂
      (j₁ ≫ c₁) (j₂ ≫ c₂) hbase₁ hbase₂ t.left t.w φ hcoeff
      (by rw [← Category.assoc, ← hd, Category.assoc, hstruct, ← Category.assoc])
  have : IsFiniteEtale r := hr
  have : Surjective r := ⟨hrsurj⟩
  let a₁ := EtaleFundamentalGroups.coefficientModelMap ψ₁ c₁ j₁
  let a₂ := EtaleFundamentalGroups.coefficientModelMap ψ₂ c₂ j₂
  have : IsOpenImmersion a₁ := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion)
    (EtaleFundamentalGroups.coefficientBaseChange_isPullback ψ₁ c₁ j₁).flip inferInstance
  have : IsOpenImmersion a₂ := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion)
    (EtaleFundamentalGroups.coefficientBaseChange_isPullback ψ₂ c₂ j₂).flip inferInstance
  have : IsIntegral (show Scheme from pullback ψ₂ c₂) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c₂) ψ₂
      (pullback.snd ψ₂ c₂) (pullback.fst ψ₂ c₂)
      (IsPullback.of_hasPullback ψ₂ c₂).flip
  have : IsIntegral (show Scheme from pullback ψ₂ (j₂ ≫ c₂)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := j₂ ≫ c₂) ψ₂
      (pullback.snd ψ₂ (j₂ ≫ c₂)) (pullback.fst ψ₂ (j₂ ≫ c₂))
      (IsPullback.of_hasPullback ψ₂ (j₂ ≫ c₂)).flip
  have : IsDominant a₂ :=
    ⟨a₂.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace a₂⟩
  let dκ : pullback ψ₁ c₁ ⟶ pullback ψ₂ c₂ :=
    pullback.lift (pullback.fst ψ₁ c₁) (pullback.snd ψ₁ c₁ ≫ d) (by
      rw [Category.assoc, hstruct, ← Category.assoc, ← pullback.condition,
        Category.assoc, hcoeff])
  have hfst : dκ ≫ pullback.fst ψ₂ c₂ = pullback.fst ψ₁ c₁ := pullback.lift_fst _ _ _
  have hsnd : dκ ≫ pullback.snd ψ₂ c₂ = pullback.snd ψ₁ c₁ ≫ d := pullback.lift_snd _ _ _
  have hopen : a₁ ≫ dκ = r ≫ a₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hfst, a₁, a₂,
        EtaleFundamentalGroups.coefficientModelMap, pullback.lift_fst]
      exact hrfst.symm
    · simp only [Category.assoc, hsnd, a₁, a₂,
        EtaleFundamentalGroups.coefficientModelMap, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hd]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ j₂) hrsnd.symm).trans (Category.assoc _ _ _))
  have : IsDominant (a₁ ≫ dκ) := hopen.symm ▸ inferInstance
  have : IsDominant dκ := IsDominant.of_comp a₁ dκ
  have : IsProper (dκ ≫ pullback.fst ψ₂ c₂) := hfst.symm ▸ inferInstance
  have : IsProper dκ := IsProper.of_comp dκ (pullback.fst ψ₂ c₂)
  have : Surjective dκ :=
    surjective_of_isDominant_of_isClosed_range dκ dκ.isClosedMap.isClosed_range
  have : Finite (GeometricBoundaryPoint E₁ κ c₁ j₁) :=
    finite_geometricBoundaryPoint E₁ κ c₁ j₁
  let mapB : GeometricBoundaryPoint E₁ κ c₁ j₁ →
      GeometricBoundaryPoint E₂ κ c₂ j₂ := fun p =>
    ⟨⟨p.val.val ≫ d, by
      rw [Category.assoc, hstruct, ← Category.assoc, p.val.property]
      exact hcoeff⟩, (hboundary _).mpr p.property⟩
  apply Nat.card_le_card_of_surjective mapB
  intro p₂
  let s₂ : Spec (.of κ) ⟶ pullback ψ₂ c₂ :=
    pullback.lift (𝟙 _) p₂.val.val ((Category.id_comp ψ₂).trans p₂.val.property.symm)
  obtain ⟨s₁, hs₁⟩ := exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed dκ s₂
  let p₁ := s₁ ≫ pullback.snd ψ₁ c₁
  have hp : p₁ ≫ d = p₂.val.val := by
    rw [Category.assoc, ← hsnd, ← Category.assoc, hs₁]
    exact pullback.lift_snd _ _ _
  have hpc : p₁ ≫ c₁ = ψ₁ := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      ← hfst, ← Category.assoc, hs₁, pullback.lift_fst, Category.id_comp]
  have hpb : p₁ (IsLocalRing.closedPoint κ) ∉ Set.range j₁ := by
    apply (hboundary _).mp
    have heval := congrArg (fun z : Spec (.of κ) ⟶ C₂ => z (IsLocalRing.closedPoint κ)) hp
    exact heval.symm ▸ p₂.property
  refine ⟨⟨⟨p₁, hpc⟩, hpb⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hp

end AnabelianGeometry.FiniteField
