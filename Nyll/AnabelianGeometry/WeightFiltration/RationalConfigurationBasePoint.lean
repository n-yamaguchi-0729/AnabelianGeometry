/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GeometricBasePoint
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.SchemeIsomorphism
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationNakamura
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Weak rational-configuration reconstruction at arbitrary geometric points

The canonical generic points used in the reconstruction proof impose no
restriction on the original pointed arithmetic isomorphism. The changes of
base point are constructed on the actual fibre functors and corrected to
preserve the arithmetic maps before the reconstruction theorem is applied.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ArithmeticIsomorphisms AnabelianGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

/-- The complement of a finite rational configuration remains connected after
every field extension. This uses its actual projective-line base-change chart. -/
theorem rationalConfigurationOpen_geometricallyConnected
    (k : Type) [Field k] [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    GeometricallyConnected ((rationalConfigurationOpen s).ι ≫ π k 1) := by
  rw [GeometricallyConnected.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  exact h.flip.isoPullback.hom.homeomorph.connectedSpace_iff.mpr
    (rationalConfigurationBaseChange_connectedSpace k K s)

/-- Weak reconstruction for arbitrary geometric base points on the two
rational-configuration opens. No generic-point or function-field algebra is
supplied as input. -/
theorem exists_projectiveTransformation_of_pointed_arithmeticFundamentalGroupEquiv
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (x : Spec (.of Ωs) ⟶ (rationalConfigurationOpen s : Scheme))
    (y : Spec (.of Ωt) ⟶ (rationalConfigurationOpen t : Scheme))
    (α : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y))
    (hα : ∀ g,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
          y (α g) =
        arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
          x g) :
    ∃ (σ : s ≃ t) (f : (k × k) ≃ₗ[k] (k × k)),
      (∀ p : s, projectiveLinearEquiv f p.val = (σ p).val) ∧
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme),
        I.hom ≫ (rationalConfigurationOpen t).ι =
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  let fs := (rationalConfigurationOpen s).ι ≫ π k 1
  let ft := (rationalConfigurationOpen t).ι ≫ π k 1
  let : GeometricallyConnected fs := rationalConfigurationOpen_geometricallyConnected k s
  let : GeometricallyConnected ft := rationalConfigurationOpen_geometricallyConnected k t
  let Ω₁ := AlgebraicClosure (rationalConfigurationGeometricScheme k κ s).functionField
  let Ω₂ := AlgebraicClosure (rationalConfigurationGeometricScheme k κ t).functionField
  let xs := rationalConfigurationArithmeticBasePoint k κ s Ω₁
  let yt := rationalConfigurationArithmeticBasePoint k κ t Ω₂
  obtain ⟨ts, hts⟩ := exists_arithmetic_preserving_fiberIso k κ fs x xs
  obtain ⟨tt, htt⟩ := exists_arithmetic_preserving_fiberIso k κ ft y yt
  let es := continuousConjAut ts
  let et := continuousConjAut tt
  let β : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(yt) := es.symm.trans (α.trans et)
  have hβ (g : π₁ᵉᵗ(xs)) :
      arithmeticFundamentalGroupHom k κ ft yt (β g) =
        arithmeticFundamentalGroupHom k κ fs xs g := by
    exact (htt (α (es.symm g))).trans ((hα (es.symm g)).trans
      ((hts (es.symm g)).symm.trans
        (congrArg (arithmeticFundamentalGroupHom k κ fs xs) (es.apply_symm_apply g))))
  exact exists_projectiveTransformation_of_arithmeticFundamentalGroupEquiv
    k κ s t hs ht Ω₁ Ω₂ β hβ

/-- The weak Isom equivalence for punctured projective lines with rational
punctures over a number field, at arbitrary geometric base points. This is an
existence equivalence; it does not assert that every input group isomorphism
is induced by the reconstructed scheme isomorphism. -/
theorem arithmeticFundamentalGroupEquiv_iff_schemeIso_of_rationalConfiguration
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (x : Spec (.of Ωs) ⟶ (rationalConfigurationOpen s : Scheme))
    (y : Spec (.of Ωt) ⟶ (rationalConfigurationOpen t : Scheme)) :
    (∃ α : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y), ∀ g,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
          y (α g) =
        arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
          x g) ↔
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme),
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨_σ, _f, _hf, I, _hambient, hover⟩ :=
      exists_projectiveTransformation_of_pointed_arithmeticFundamentalGroupEquiv
        k κ s t hs ht x y α hα
    exact ⟨I, hover⟩
  · rintro ⟨I, hI⟩
    let : GeometricallyConnected ((rationalConfigurationOpen t).ι ≫ π k 1) :=
      rationalConfigurationOpen_geometricallyConnected k t
    obtain ⟨α, _hrealization, hα⟩ := exists_arithmetic_groupEquiv_of_schemeIso k κ
      ((rationalConfigurationOpen s).ι ≫ π k 1)
      ((rationalConfigurationOpen t).ι ≫ π k 1) I hI x y
    exact ⟨α, hα⟩

end AnabelianGeometry.WeightFiltration
