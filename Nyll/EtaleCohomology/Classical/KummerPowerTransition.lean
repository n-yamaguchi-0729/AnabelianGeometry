/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Exponent transitions in the actual Kummer sequence

The power map μ_(n*m) → μ_n is induced on the original kernels. It extends
to the original Kummer complexes with the m-th power map on the middle Gm
and the identity on the right Gm. The actual connecting maps therefore
commute with the power transition in every degree, retaining the identity
on H¹(Gm) used for the eventual H² coefficient reduction.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

private theorem powerTransition_square (X : Scheme.{u}) (n m : ℕ) :
    etaleMultiplicativeGroupPower X (n * m) ≫ 𝟙 _ =
      etaleMultiplicativeGroupPower X m ≫ etaleMultiplicativeGroupPower X n := by
  rw [Category.comp_id, etaleMultiplicativeGroupPower,
    etaleMultiplicativeGroupPower, etaleMultiplicativeGroupPower,
    Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
    smul_smul, Nat.mul_comm m n]

/-- The actual m-th power homomorphism on the original roots-of-unity
kernels for the exponents n*m and n. -/
def etaleKummerPowerTransition (X : Scheme.{u}) (n m : ℕ) :
    etaleRootsOfUnitySheaf X (n * m) ⟶ etaleRootsOfUnitySheaf X n :=
  kernel.map (etaleMultiplicativeGroupPower X (n * m))
    (etaleMultiplicativeGroupPower X n) (etaleMultiplicativeGroupPower X m)
    (𝟙 _) (by exact powerTransition_square X n m)

/-- Inclusion in Gm identifies the kernel transition with the original
m-th power map, without replacing the kernel sheaves. -/
theorem etaleKummerPowerTransition_ι (X : Scheme.{u}) (n m : ℕ) :
    etaleKummerPowerTransition X n m ≫
      kernel.ι (etaleMultiplicativeGroupPower X n) =
    kernel.ι (etaleMultiplicativeGroupPower X (n * m)) ≫
      etaleMultiplicativeGroupPower X m :=
  kernel.lift_ι _ _ _

/-- The original Kummer power transition as a morphism of the original
short complexes. The right-hand unit map is the identity. -/
def etaleKummerPowerTransitionComplex (X : Scheme.{u}) (n m : ℕ) :
    etaleKummerComplex X (n * m) ⟶ etaleKummerComplex X n where
  τ₁ := etaleKummerPowerTransition X n m
  τ₂ := etaleMultiplicativeGroupPower X m
  τ₃ := 𝟙 _
  comm₁₂ := etaleKummerPowerTransition_ι X n m
  comm₂₃ := by exact (powerTransition_square X n m).symm

/-- Every actual Kummer connecting homomorphism commutes with exponent
reduction. In degree one, the input H¹(Gm) class is unchanged. -/
theorem etaleKummerPowerTransition_connecting
    (X : Scheme.{u}) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnX : IsUnit (n : Γ(X, ⊤))) (hmX : IsUnit (m : Γ(X, ⊤)))
    (i : ℕ) (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) i) :
    Sheaf.H.map (etaleKummerPowerTransition X n m) (i + 1)
      (Sheaf.H.δ (etaleKummerComplex_shortExact X (Nat.mul_pos hn hm)
        (by simpa only [Nat.cast_mul] using hnX.mul hmX)) i (i + 1) rfl a) =
    Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) i (i + 1) rfl a := by
  let hnmX : IsUnit ((n * m : ℕ) : Γ(X, ⊤)) := by
    simpa only [Nat.cast_mul] using hnX.mul hmX
  have h := Sheaf.H.δ_naturality i (i + 1) rfl
    (etaleKummerComplex_shortExact X (Nat.mul_pos hn hm) hnmX)
    (etaleKummerComplex_shortExact X hn hnX)
    (etaleKummerPowerTransitionComplex X n m) a
  change Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) i (i + 1) rfl
    (Sheaf.H.map (𝟙 (etaleMultiplicativeGroupSheaf X)) i a) = _ at h
  rw [Sheaf.H.map_id_apply] at h
  exact h.symm

end EtaleCohomology
