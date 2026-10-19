/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Rational.RatFuncRationalPlaceIntegralBase
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Places.ValuationRings.EqComapToValuationSubringEq
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # RationalBoundaryCyclotomicFixedPlace -/

noncomputable section
open AlgebraicCurve
open scoped RatFunc Pointwise
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

/-- The same rational place is fixed by a coefficient automorphism fixing
its prescribed arithmetic rational-function subfield. -/
theorem ratFunc_rationalPlace_semilinear_fixed
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (W : Place K (RatFunc K))
    (hord : ∀ x : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc K) x) = V.ord x)
    (g : SemilinearAut K (RatFunc K))
    (hg : ∀ x : RatFunc k,
      SemilinearAut.toRingAut g (algebraMap (RatFunc k) (RatFunc K) x) =
        algebraMap (RatFunc k) (RatFunc K) x) :
    g • W = W := by
  have hW := ratFunc_place_comap_eq_of_ord_eq V W hord
  apply Place.eq_of_comap_toValuationSubring_eq_of_isRational
    (ratFunc_constantExtension_reverse_adjoin_eq_top (k := k) (κ := K))
    V hV (g • W) W ?_ hW
  calc
    (g • W).toValuationSubring.comap (algebraMap (RatFunc k) (RatFunc K)) =
        W.toValuationSubring.comap (algebraMap (RatFunc k) (RatFunc K)) := by
      ext x
      simp only [ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hinv : g⁻¹ • algebraMap (RatFunc k) (RatFunc K) x =
          algebraMap (RatFunc k) (RatFunc K) x := by
        apply (SemilinearAut.toRingAut g).injective
        change g • (g⁻¹ • algebraMap (RatFunc k) (RatFunc K) x) =
          g • algebraMap (RatFunc k) (RatFunc K) x
        rw [smul_inv_smul, SemilinearAut.smul_def, hg]
      rw [hinv]
    _ = V.toValuationSubring := hW

end AnabelianGeometry.KummerTheory

namespace EtaleFundamentalGroups.Inertia

private theorem cyclic_endomorphisms_commute
    {G : Type*} [Group G] [IsCyclic G] (f h : G →* G) (x : G) :
    f (h x) = h (f x) := by
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨a, ha⟩ := (Subgroup.mem_zpowers_iff).mp (hz (f z))
  obtain ⟨b, hb⟩ := (Subgroup.mem_zpowers_iff).mp (hz (h z))
  obtain ⟨c, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hz x)
  simp only [map_zpow, ← ha, ← hb, ← zpow_mul]
  rw [mul_left_comm a b c]

/-- Coefficient actions commute on the literal roots limit, coordinatewise. -/
theorem primeToRootsCoefficientMap_commute
    (k E : Type*) [Field k] [Field E] (f h : E →+* E)
    (t : (primeToRootsSystem k E).inverseLimit) :
    primeToRootsCoefficientMap k E f (primeToRootsCoefficientMap k E h t) =
      primeToRootsCoefficientMap k E h (primeToRootsCoefficientMap k E f t) := by
  apply (primeToRootsSystem k E).ext
  intro n
  let : NeZero n.val := ⟨(InvertibleExponent.pos k n).ne'⟩
  exact cyclic_endomorphisms_commute
    (restrictRootsOfUnity f.toMonoidHom n.val)
    (restrictRootsOfUnity h.toMonoidHom n.val) (t.val n)

/-- The fixed base-point correction disappears from the actual root action. -/
theorem primeToRootsCoefficientMap_conjugate
    (k E : Type*) [Field k] [Field E] (α σ : E ≃+* E)
    (t : (primeToRootsSystem k E).inverseLimit) :
    primeToRootsCoefficientMap k E (α * σ * α⁻¹).toRingHom t =
      primeToRootsCoefficientMap k E σ.toRingHom t := by
  have h := primeToRootsCoefficientMap_commute k E α.toRingHom σ.toRingHom
    (primeToRootsCoefficientMap k E α.symm.toRingHom t)
  have hc : primeToRootsCoefficientMap k E α.toRingHom
      (primeToRootsCoefficientMap k E α.symm.toRingHom t) = t :=
    (primeToRootsResidueEquiv k E α).apply_symm_apply t
  change primeToRootsCoefficientMap k E α.toRingHom
    (primeToRootsCoefficientMap k E σ.toRingHom
      (primeToRootsCoefficientMap k E α.symm.toRingHom t)) = _
  rw [h, hc]

end EtaleFundamentalGroups.Inertia
