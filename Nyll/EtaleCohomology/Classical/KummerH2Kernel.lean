/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Nyll.EtaleCohomology.Classical.FieldKummer
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The degree-two Kummer kernel from actual sheaf cohomology

For an invertible exponent, the quotient of the original H¹(Gm) by n
identifies with the kernel of the original coefficient map H²(μn) → H²(Gm).
The equivalence is induced by the actual connecting homomorphism. No Picard
comparison or vanishing of H²(Gm) is assumed here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits

namespace EtaleCohomology

private theorem cohomology_power_apply
    (X : Scheme.{u}) (n i : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) i) :
    Sheaf.H.map (etaleMultiplicativeGroupPower X n) i a = n • a := by
  change ((Sheaf.functorH X.smallEtaleTopology i).map
    (n • 𝟙 (etaleMultiplicativeGroupSheaf X))) a = n • a
  rw [(Sheaf.functorH X.smallEtaleTopology i).map_nsmul,
    (Sheaf.functorH X.smallEtaleTopology i).map_id]
  rfl

/-- The degree-one Kummer boundary vanishes exactly on classes divisible by the exponent. -/
theorem kummerBoundary_one_eq_zero_iff
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl a = 0 ↔
      ∃ b : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1, n • b = a := by
  let hS := etaleKummerComplex_shortExact X hn hnX
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₃ hS a rfl ha
    exact ⟨b, (cohomology_power_apply X n 1 b).symm.trans hb⟩
  · rintro ⟨b, rfl⟩
    rw [← cohomology_power_apply X n 1 b]
    change (b.comp (Ext.mk₀ (etaleMultiplicativeGroupPower X n))
      (add_zero 1)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- The degree-one Kummer boundary lies in the kernel of the original coefficient map. -/
theorem kummerBoundary_one_mem_kernel
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl a ∈
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker := by
  let hS := etaleKummerComplex_shortExact X hn hnX
  change (a.comp hS.extClass rfl).comp
    (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower X n))) (add_zero 2) = 0
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

/-- The actual Kummer boundary identifies H¹(Gm)/n with the kernel of the
actual coefficient homomorphism H²(μn) → H²(Gm). -/
def etaleKummerH1QuotientEquivH2Kernel
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤))) :
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom n :
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 →+
          Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1).range) ≃+
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker := by
  let A := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1
  let N : AddSubgroup A := (nsmulAddMonoidHom n : A →+ A).range
  let hS := etaleKummerComplex_shortExact X hn hnX
  let δ := Sheaf.H.δ hS 1 2 rfl
  let φ : A →+
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker :=
    δ.codRestrict _ (kummerBoundary_one_mem_kernel X hn hnX)
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁ hS a ha (n₀ := 1) rfl
    exact ⟨b, Subtype.ext hb⟩
  have hker : N = φ.ker := by
    ext a
    constructor
    · rintro ⟨b, hb⟩
      apply Subtype.ext
      exact (kummerBoundary_one_eq_zero_iff X hn hnX a).mpr ⟨b, hb⟩
    · intro ha
      exact (kummerBoundary_one_eq_zero_iff X hn hnX a).mp
        (congrArg Subtype.val ha)
  have : N.Normal := ⟨fun a ha b => by
    simpa only [add_comm b a, add_assoc, add_neg_cancel, add_zero] using ha⟩
  exact QuotientAddGroup.liftEquiv N (φ := φ) hsurj hker

/-- On an original H¹ class the quotient equivalence is the original
Kummer connecting homomorphism. -/
theorem etaleKummerH1QuotientEquivH2Kernel_mk
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    (etaleKummerH1QuotientEquivH2Kernel X hn hnX
      (QuotientAddGroup.mk a)).val =
        Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl a := rfl

end EtaleCohomology
