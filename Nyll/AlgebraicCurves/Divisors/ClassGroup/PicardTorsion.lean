/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in the original Picard degree sequence

The original inclusion of degree-zero divisor classes identifies their
n-torsion with the actual kernel of multiplication by n on the full
Picard group, for positive n. The original integer-valued degree forces
every such Picard class to have degree zero.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve.Pic0

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The original inclusion of degree-zero divisor classes restricts to
the original multiplication kernel on the full Picard group. -/
def torsionToPicardPowerKernel (n : ℕ) :
    torsion K F n →+ (nsmulAddMonoidHom (α := Pic K F) n).ker where
  toFun x := ⟨H1Gm.ofPic0 K F x.val, by
    change n • H1Gm.ofPic0 K F x.val = 0
    have hx : n • x.val = 0 := by
      simpa only [natCast_zsmul] using (mem_torsion.mp x.property)
    rw [← map_nsmul, hx, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (H1Gm.ofPic0 K F))
  map_add' x y := Subtype.ext (map_add (H1Gm.ofPic0 K F) x.val y.val)

/-- The restricted inclusion retains the actual original Picard class. -/
theorem torsionToPicardPowerKernel_val (n : ℕ) (x : torsion K F n) :
    (torsionToPicardPowerKernel K F n x).val = H1Gm.ofPic0 K F x.val := rfl

/-- Every positive-order torsion class has zero original integer degree. -/
theorem degree_eq_zero_of_nsmul_eq_zero [HasPrincipalDivisors K F]
    {n : ℕ} (hn : 0 < n) {x : Pic K F} (hx : n • x = 0) :
    H1Gm.degree K F x = 0 := by
  have hdeg : n • H1Gm.degree K F x = 0 :=
    (map_nsmul (H1Gm.degree K F) n x).symm.trans
      ((congrArg (H1Gm.degree K F) hx).trans (map_zero (H1Gm.degree K F)))
  have hmul : (n : ℤ) * H1Gm.degree K F x = 0 := by
    simpa only [nsmul_eq_mul] using hdeg
  exact (mul_eq_zero.mp hmul).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

/-- The actual degree-zero inclusion identifies original n-torsion with
the actual multiplication kernel on the original Picard group. -/
def torsionPicardPowerKernelEquiv [HasPrincipalDivisors K F]
    {n : ℕ} (hn : 0 < n) :
    torsion K F n ≃+ (nsmulAddMonoidHom (α := Pic K F) n).ker :=
  AddEquiv.ofBijective (torsionToPicardPowerKernel K F n) ⟨
    fun x y h => Subtype.ext
      (H1Gm.ofPic0_injective K F (congrArg Subtype.val h)),
    fun x => by
      have hdeg : H1Gm.degree K F x.val = 0 :=
        degree_eq_zero_of_nsmul_eq_zero K F hn x.property
      obtain ⟨y, hy⟩ := (H1Gm.exact_ofPic0_degree K F).ge hdeg
      have hny : n • y = 0 := by
        apply H1Gm.ofPic0_injective K F
        rw [map_nsmul, hy, map_zero]
        exact x.property
      refine ⟨⟨y, mem_torsion.mpr ?_⟩, Subtype.ext hy⟩
      simpa only [natCast_zsmul] using hny⟩

/-- The forward torsion comparison is the original Picard inclusion. -/
theorem torsionPicardPowerKernelEquiv_val [HasPrincipalDivisors K F]
    {n : ℕ} (hn : 0 < n) (x : torsion K F n) :
    (torsionPicardPowerKernelEquiv K F hn x).val =
      H1Gm.ofPic0 K F x.val := rfl

/-- The inverse torsion comparison has exactly the original full
Picard class as the image under the degree-zero inclusion. -/
theorem torsionPicardPowerKernelEquiv_symm_val [HasPrincipalDivisors K F]
    {n : ℕ} (hn : 0 < n)
    (x : (nsmulAddMonoidHom (α := Pic K F) n).ker) :
    H1Gm.ofPic0 K F ((torsionPicardPowerKernelEquiv K F hn).symm x).val = x.val :=
  congrArg Subtype.val ((torsionPicardPowerKernelEquiv K F hn).apply_symm_apply x)

end AlgebraicCurve.Pic0
