/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSeparableRoots
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationQuotientRoots
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCharZeroIndex
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCoefficientComparison
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Common constant roots for normalization inertia

The canonical constant-field map identifies the full roots limit with the
normalization's separable roots target. Every place uses the same constant
roots and the same positive integer exponents.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups.InverseSystems

attribute [local instance] Ideal.Quotient.field

universe u v

variable (k : Type v) (A : Type u) (Ω : Type v)
  [Field k] [CharZero k] [IsSepClosed k]
  [CommRing A] [IsLocalRing A] [Algebra k A]
  [CommRing Ω] [Algebra A Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
  [CharZero (IsLocalRing.ResidueField A)]

/-- Common constant roots identify the actual normalization's full separable roots target. -/
def normalizationConstantRootsEquiv :
    (primeToRootsSystem k k).inverseLimit ≃ₜ*
      (normalizationSeparableRootsGroup A Ω Q).carrier := by
  let E := (normalizationCommAlgCat A Ω).carrier ⧸ Q
  let f : k →+* E := (Ideal.Quotient.mk Q).comp
    ((algebraMap A (normalizationCommAlgCat A Ω)).comp (algebraMap k A))
  have hf (n : InvertibleExponent k) :
      Function.Bijective (restrictRootsOfUnity f.toMonoidHom n.val).toFun := by
    let : NeZero n.val := ⟨(InvertibleExponent.pos k n).ne'⟩
    let : NeZero (n.val : k) := ⟨n.property.ne_zero⟩
    exact RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
      f n.val (HasEnoughRootsOfUnity.exists_primitiveRoot k n.val)
  let c :=
    (primeToRootsCoefficientSystemIso k k E f.toMonoidHom hf).inverseLimitContinuousMulEquiv
  let r := primeToRootsCharZeroIndexEquiv k (IsLocalRing.ResidueField A) E
  let s := nativeSeparableRootsInclusionEquiv (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
  exact c.trans (r.trans s.symm)

/-- The comparison retains the actual constant-field residue at each root coordinate. -/
theorem normalizationConstantRootsEquiv_scalar
    (x : (primeToRootsSystem k k).inverseLimit)
    (n : InvertibleExponent (IsLocalRing.ResidueField A)) :
    normalizationSeparableRootsScalar A Ω Q n (normalizationConstantRootsEquiv k A Ω Q x) =
      Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω)
        (algebraMap k A (((primeToRootsSystem k k).projection
          (InvertibleExponent.charZeroOrderIso (IsLocalRing.ResidueField A) k n) x).val : k))) := by
  have h := nativeSeparableRootsInclusionEquiv_scalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
    n (normalizationConstantRootsEquiv k A Ω Q x)
  refine h.symm.trans ?_
  unfold normalizationConstantRootsEquiv
  let s := nativeSeparableRootsInclusionEquiv (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
  change nativeFullRootsScalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) n (s (s.symm _)) = _
  refine (congrArg (nativeFullRootsScalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) n) (s.apply_symm_apply _)).trans ?_
  rfl

end EtaleFundamentalGroups.Inertia
