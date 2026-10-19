/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.RationalPunctureCoordinateChange
import Nyll.SchemeTheory.ProjectiveSpace.Normalization
import Nyll.SchemeTheory.ProjectiveSpace.Configuration

/-! # The actual projective scheme isomorphism matching a configuration -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.ProjectiveLine

universe u
variable {K : Type u} [Field K]

/-- The linear representative of the existing normalization map. -/
def normalizeTripleLinearEquiv (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) : (K × K) ≃ₗ[K] (K × K) :=
  coordinateLinearEquiv
    (a.rep.2 * bracket c.rep b.rep) (-a.rep.1 * bracket c.rep b.rep)
    (b.rep.2 * bracket c.rep a.rep) (-b.rep.1 * bracket c.rep a.rep)
    (by
      rw [normalization_determinant]
      exact mul_ne_zero (mul_ne_zero
        (fun h => hab ((bracket_rep_eq_zero_iff a b).mp h))
        (fun h => hcb ((bracket_rep_eq_zero_iff c b).mp h)))
        (fun h => hca ((bracket_rep_eq_zero_iff c a).mp h)))

theorem projectiveLinearEquiv_normalizeTripleLinearEquiv
    (a b c : Projectivization K (K × K)) (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) :
    projectiveLinearEquiv (normalizeTripleLinearEquiv a b c hab hcb hca) =
      normalizeTriple a b c hab hcb hca := rfl

/-- The same matching map, before projectivization. -/
def matchTriplesLinearEquiv (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') : (K × K) ≃ₗ[K] (K × K) :=
  (normalizeTripleLinearEquiv a b c hab hcb hca).trans
    (normalizeTripleLinearEquiv a' b' c' hab' hcb' hca').symm

theorem projectiveLinearEquiv_matchTriplesLinearEquiv
    (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') :
    projectiveLinearEquiv
      (matchTriplesLinearEquiv a b c a' b' c' hab hcb hca hab' hcb' hca') =
      matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca' := by
  ext p
  induction p using Projectivization.ind with
  | h v hv => rfl

end AnabelianGeometry.ProjectiveLine

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.ProjectiveLine
universe u v
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The actual scheme isomorphism from the same matching linear map. -/
def matchTriplesSchemeIso (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') : Proj 𝒜 ≅ Proj 𝒜 :=
  pairLinearCoordinateIso
    (matchTriplesLinearEquiv a b c a' b' c' hab hcb hca hab' hcb' hca')

theorem matchTriplesSchemeIso_apply (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a')
    (p : Projectivization K (K × K)) :
    (matchTriplesSchemeIso a b c a' b' c' hab hcb hca hab' hcb' hca').hom
      (projectiveRationalPoint p) =
      projectiveRationalPoint (matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca' p) := by
  rw [matchTriplesSchemeIso, pairLinearCoordinateIso_projectiveRationalPoint,
    projectiveLinearEquiv_matchTriplesLinearEquiv]

theorem matchTriplesSchemeIso_hom_comp_π (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') :
    (matchTriplesSchemeIso a b c a' b' c' hab hcb hca hab' hcb' hca').hom ≫ π K 1 = π K 1 :=
  linearCoordinateIso_hom_comp_π _

/-- Cross-ratio equality gives one actual base-preserving scheme map for every label. -/
theorem matchTriplesSchemeIso_configuration {ι : Type v}
    (x y : ι → Projectivization K (K × K)) (hx : Function.Injective x)
    (hy : Function.Injective y) (i₀ iInf i₁ : ι)
    (hZeroInf : i₀ ≠ iInf) (hOneInf : i₁ ≠ iInf) (h₁₀ : i₁ ≠ i₀)
    (h : ∀ i, crossRatio (x i₀) (x iInf) (x i₁) (x i) =
      crossRatio (y i₀) (y iInf) (y i₁) (y i)) (i : ι) :
    (matchTriplesSchemeIso (x i₀) (x iInf) (x i₁) (y i₀) (y iInf) (y i₁)
      (hx.ne hZeroInf) (hx.ne hOneInf) (hx.ne h₁₀)
      (hy.ne hZeroInf) (hy.ne hOneInf) (hy.ne h₁₀)).hom
      (projectiveRationalPoint (x i)) = projectiveRationalPoint (y i) := by
  rw [matchTriplesSchemeIso_apply,
    matchTriples_configuration x y hx hy i₀ iInf i₁ hZeroInf hOneInf h₁₀ h i]

end AlgebraicGeometry.ProjSpace
