/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.StalkModulusComparison
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.SchemeTheory.Divisors.SubschemeStalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Multiplicities of the actual Cartier modulus at closed points

The defining ideal in an actual curve stalk is nonzero. Its image in the place
valuation ring is therefore a power of the maximal ideal. This constructs the
multiplicity and identifies the actual modulus stalk with the corresponding
truncated valuation ring. Congruence to one is exactly restriction to one under
the original closed immersion's stalk map.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A Cartier ideal has nonzero stalk ideal on an integral scheme. -/
theorem IsInvertible.stalkIdeal_ne_bot {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I.IsInvertible) (x : X) : I.stalkIdeal x ≠ ⊥ := by
  obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI x
  let V := X.affineBasicOpen f
  have hxV : x ∈ V.1 := hxf
  have : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  have hgmem : g ∈ I.ideal V := hIg.symm ▸ Ideal.subset_span (Set.mem_singleton g)
  have hmem : X.presheaf.germ V.1 x hxV g ∈ I.stalkIdeal x :=
    I.map_ideal_le_stalkIdeal x V hxV
      (Ideal.mem_map_of_mem (X.presheaf.germ V.1 x hxV).hom hgmem)
  intro hbot
  have hzero : X.presheaf.germ V.1 x hxV g = 0 := by
    have h : X.presheaf.germ V.1 x hxV g ∈ (⊥ : Ideal (X.presheaf.stalk x)) := hbot ▸ hmem
    exact h
  exact (nonZeroDivisors.ne_zero hg)
    ((germ_injective_of_isIntegral X x hxV)
      (hzero.trans (map_zero (X.presheaf.germ V.1 x hxV).hom).symm))

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

include hI in
/-- Existence of the full multiplicity follows from the actual Cartier stalk ideal. -/
theorem exists_stalkIdeal_eq_maximalIdeal_pow (x : closedPoints M.C) :
    ∃ n : ℕ, I.stalkIdeal x.1 = IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n := by
  let e := M.stalkValuationEquiv x
  have hmap : (I.stalkIdeal x.1).map e ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr (hI.stalkIdeal_ne_bot x.1)
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (M.placeOfPoint x).toValuationSubring
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap hπ
  have hn' : (I.stalkIdeal x.1).map e =
      IsLocalRing.maximalIdeal (M.placeOfPoint x).toValuationSubring ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact hn
  refine ⟨n, ?_⟩
  ext a
  calc
    a ∈ I.stalkIdeal x.1 ↔ e a ∈ (I.stalkIdeal x.1).map e :=
      Ideal.apply_mem_of_equiv_iff.symm
    _ ↔ e a ∈ (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n).map e := by
      rw [hn', M.stalkValuationEquiv_map_maximalIdeal_pow x n]
    _ ↔ a ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n :=
      Ideal.apply_mem_of_equiv_iff

/-- The order of the actual Cartier ideal at a closed point. -/
def cartierMultiplicity (x : closedPoints M.C) : ℕ :=
  Classical.choose (M.exists_stalkIdeal_eq_maximalIdeal_pow I hI x)

/-- The constructed multiplicity describes the full defining ideal, not its radical. -/
theorem stalkIdeal_eq_maximalIdeal_pow (x : closedPoints M.C) :
    I.stalkIdeal x.1 =
      IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ M.cartierMultiplicity I hI x :=
  Classical.choose_spec (M.exists_stalkIdeal_eq_maximalIdeal_pow I hI x)

/-- The local ring of the actual Cartier modulus is the truncated place ring
at the constructed multiplicity. -/
def cartierStalkQuotientEquiv (z : I.subscheme)
    (hz : IsClosed ({I.subschemeι z} : Set M.C)) :
    I.subscheme.presheaf.stalk z ≃+*
      ((M.placeOfPoint ⟨I.subschemeι z, hz⟩).toValuationSubring ⧸
        IsLocalRing.maximalIdeal (M.placeOfPoint ⟨I.subschemeι z, hz⟩).toValuationSubring ^
          M.cartierMultiplicity I hI ⟨I.subschemeι z, hz⟩) :=
  (I.subschemeStalkQuotientEquiv z).symm.trans
    ((Ideal.quotEquivOfEq (M.stalkIdeal_eq_maximalIdeal_pow I hI ⟨I.subschemeι z, hz⟩)).trans
      (M.stalkModulusQuotientEquiv ⟨I.subschemeι z, hz⟩
        (M.cartierMultiplicity I hI ⟨I.subschemeι z, hz⟩)))

/-- Place congruence with the actual Cartier multiplicity is restriction to
one in the actual modulus stalk under the original immersion. -/
theorem congruentOne_iff_modulusStalk_eq_one (z : I.subscheme)
    (hz : IsClosed ({I.subschemeι z} : Set M.C))
    (a : (M.C.presheaf.stalk (I.subschemeι z))ˣ) :
    (M.placeOfPoint ⟨I.subschemeι z, hz⟩).CongruentOne
        (M.cartierMultiplicity I hI ⟨I.subschemeι z, hz⟩)
        (M.ffEquiv.symm
          (algebraMap (M.C.presheaf.stalk (I.subschemeι z)) M.C.functionField a)) ↔
      I.subschemeι.stalkMap z (a : M.C.presheaf.stalk (I.subschemeι z)) = 1 := by
  rw [M.congruentOne_stalkUnit_iff,
    ← M.stalkIdeal_eq_maximalIdeal_pow I hI ⟨I.subschemeι z, hz⟩]
  have hker := I.subschemeι.ker_stalkMap_eq_stalkIdeal z
  rw [I.ker_subschemeι] at hker
  rw [← hker, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

end AlgebraicCurve.CurveModel
