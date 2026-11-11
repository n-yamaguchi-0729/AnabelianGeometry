/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsProcyclic
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCommonUnit
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates

/-!
# Compatible coordinates on all prime-to-characteristic roots

A topological generator of the actual roots inverse limit supplies primitive
roots at every invertible exponent. Its original power transitions make the
finite additive coordinates compatible with reduction. No compatible family
of primitive roots is assumed.

-/

@[expose] public section

noncomputable section

open ProCGroups.InverseSystems ProCGroups.Generation

namespace EtaleFundamentalGroups.Inertia

/-- Every coordinate of an actual topological generator is a primitive root
at its original invertible exponent. -/
theorem primeToRoots_projection_isPrimitiveRoot
    (K : Type*) [Field K] [IsAlgClosed K]
    (t : (primeToRootsSystem K K).inverseLimit)
    (ht : TopologicallyGenerates ({t} : Set (primeToRootsSystem K K).inverseLimit))
    (n : InvertibleExponent K) :
    IsPrimitiveRoot
      (show rootsOfUnity n.val K from (primeToRootsSystem K K).projection n t).val n.val := by
  have : NeZero n.val := ⟨(InvertibleExponent.pos K n).ne'⟩
  have : NeZero (n.val : K) := ⟨n.property.ne_zero⟩
  let π : (primeToRootsSystem K K).inverseLimit →ₜ* (primeToRootsSystem K K).X n :=
    { toMonoidHom := projectionHom (primeToRootsSystem K K) n
      continuous_toFun := (primeToRootsSystem K K).continuous_projection n }
  have hπ : π.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (primeToRoots_projection_surjective K K n)
  have hcl : (Subgroup.zpowers (π t)).topologicalClosure = ⊤ :=
    (topologicalClosure_zpowers_image_eq_range π t ht).trans hπ
  have hz : Subgroup.zpowers (π t) = ⊤ := by
    apply top_unique
    rw [← hcl]
    exact (Subgroup.zpowers (π t)).topologicalClosure_minimal le_rfl (isClosed_discrete _)
  apply IsPrimitiveRoot.coe_submonoidClass_iff.mpr
  exact IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_card_of_zpowers_eq_top hz).trans
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity K n.val))

/-- One generator of the original roots inverse limit, chosen once for all
finite coefficient coordinates. -/
def primeToRootsGenerator (K : Type*) [Field K] :
    (primeToRootsSystem K K).inverseLimit :=
  (primeToRoots_exists_topological_generator K K).choose

/-- The chosen compatible roots generate the original compact roots group. -/
theorem primeToRootsGenerator_generates (K : Type*) [Field K] :
    TopologicallyGenerates ({primeToRootsGenerator K} :
      Set (primeToRootsSystem K K).inverseLimit) :=
  (primeToRoots_exists_topological_generator K K).choose_spec

/-- Finite additive coordinates supplied by one generator of the actual
prime-to-characteristic roots inverse limit. -/
def primeToRootsCoordinate (K : Type*) [Field K] [IsAlgClosed K]
    (n : InvertibleExponent K) : ZMod n.val ≃+ Additive (rootsOfUnity n.val K) := by
  have : NeZero n.val := ⟨(InvertibleExponent.pos K n).ne'⟩
  exact AnabelianGeometry.CuspidalInertia.primitiveRootAddEquiv
    (primeToRoots_projection_isPrimitiveRoot K (primeToRootsGenerator K)
      (primeToRootsGenerator_generates K) n)

/-- The original roots power transition is ordinary residue-class reduction
in the compatible coordinates constructed above. -/
theorem primeToRootsCoordinate_reduction
    (K : Type*) [Field K] [IsAlgClosed K]
    {m n : InvertibleExponent K} (h : m ≤ n) (a : ZMod n.val) :
    (rootsOfUnityPowerTransition K (show m.val ∣ n.val from h)).toAdditive
        (primeToRootsCoordinate K n a) =
      primeToRootsCoordinate K m (ZMod.castHom h (ZMod m.val) a) := by
  have : NeZero n.val := ⟨(InvertibleExponent.pos K n).ne'⟩
  have : NeZero m.val := ⟨(InvertibleExponent.pos K m).ne'⟩
  have hcast : ZMod.castHom h (ZMod m.val) a = (a.val : ZMod m.val) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [map_natCast]
  let t := primeToRootsGenerator K
  have hroot : (show rootsOfUnity n.val K from t.val n).val ^ (n.val / m.val) =
      (show rootsOfUnity m.val K from t.val m).val :=
    congrArg (fun z : rootsOfUnity m.val K => (z : Kˣ)) (t.property m n h)
  apply Subtype.ext
  change KummerTheory.primitiveRootCoordinate
      (primeToRoots_projection_isPrimitiveRoot K t (primeToRootsGenerator_generates K) n) a ^
        (n.val / m.val) =
    KummerTheory.primitiveRootCoordinate
      (primeToRoots_projection_isPrimitiveRoot K t (primeToRootsGenerator_generates K) m)
        (ZMod.castHom h (ZMod m.val) a)
  rw [hcast, KummerTheory.primitiveRootCoordinate_eq_pow_val,
    KummerTheory.primitiveRootCoordinate_natCast, pow_right_comm]
  exact congrArg (fun z : Kˣ => z ^ a.val) hroot

end EtaleFundamentalGroups.Inertia
