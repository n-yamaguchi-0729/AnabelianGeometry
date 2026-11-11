/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.KummerH2Functoriality
public import Nyll.EtaleCohomology.Classical.KummerPowerTransition
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual reductions of the finite-level Kummer kernels

The original finite coefficient reduction restricts to the kernel of the
map to H²(Gm). Under the actual Kummer boundary equivalence this is the
canonical reduction on native H¹(Gm) quotients. In particular these
restricted original finite-level reductions are surjective.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology.Classical

namespace EtaleCohomology

private theorem kummerH2_powerTransition_of_eq
    (X : Scheme.{u}) {n m N : ℕ} (hN : N = n * m)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X N) 2) :
    etaleRootsOfUnityH2ToMultiplicativeGroup X n
        (Sheaf.H.map (eqToHom (congrArg (etaleRootsOfUnitySheaf X) hN) ≫
          etaleKummerPowerTransition X n m) 2 a) =
      Sheaf.H.map (etaleMultiplicativeGroupPower X m) 2
        (etaleRootsOfUnityH2ToMultiplicativeGroup X N a) := by
  subst N
  simpa only [eqToHom_refl, Category.id_comp] using
    etaleRootsOfUnityH2ToMultiplicativeGroup_powerTransition X n m a

private theorem kummerBoundary_powerTransition_of_eq
    (X : Scheme.{u}) {n m N : ℕ} (hN : N = n * m)
    (hn : 0 < n) (hm : 0 < m) (hNpos : 0 < N)
    (hnX : IsUnit (n : Γ(X, ⊤))) (hmX : IsUnit (m : Γ(X, ⊤)))
    (hNX : IsUnit (N : Γ(X, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    Sheaf.H.map (eqToHom (congrArg (etaleRootsOfUnitySheaf X) hN) ≫
        etaleKummerPowerTransition X n m) 2
      (Sheaf.H.δ (etaleKummerComplex_shortExact X hNpos hNX) 1 2 rfl a) =
      Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl a := by
  subst N
  simpa only [eqToHom_refl, Category.id_comp] using
    etaleKummerPowerTransition_connecting X hn hm hnX hmX 1 a

attribute [local instance] kummerFunctorialityH1AddZero
  kummerFunctorialityH1IsAddCommutative kummerFunctorialityH1QuotientAddZero

/-- Consecutive native H¹(Gm) quotients use the unchanged representing
class under their exponent reduction. -/
def ellPowerKummerH1QuotientReduction (X : Scheme.{u}) (ℓ n : ℕ) :
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
        (ℓ ^ ((n + 1) + 1))).range) →+
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
        (ℓ ^ (n + 1))).range) := by
  let A := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1
  refine QuotientAddGroup.map (nsmulAddMonoidHom (α := A) (ℓ ^ ((n + 1) + 1))).range
    (nsmulAddMonoidHom (α := A) (ℓ ^ (n + 1))).range (AddMonoidHom.id A) ?_
  rintro a ⟨b, hb⟩
  refine ⟨ℓ • b, ?_⟩
  change (ℓ ^ (n + 1)) • (ℓ • b) = a
  change (ℓ ^ ((n + 1) + 1)) • b = a at hb
  rw [← mul_smul, ← pow_succ]
  exact hb

/-- The quotient reduction retains the actual H¹(Gm) representative. -/
theorem ellPowerKummerH1QuotientReduction_mk (X : Scheme.{u}) (ℓ n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    ellPowerKummerH1QuotientReduction X ℓ n
        (QuotientAddGroup.mk
          (s := (nsmulAddMonoidHom
            (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
            (ℓ ^ ((n + 1) + 1))).range) a) =
      QuotientAddGroup.mk
        (s := (nsmulAddMonoidHom
          (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
          (ℓ ^ (n + 1))).range) a := rfl

/-- An original representative at the smaller exponent also represents
a lift at the next exponent. -/
theorem ellPowerKummerH1QuotientReduction_surjective (X : Scheme.{u}) (ℓ n : ℕ) :
    Function.Surjective (ellPowerKummerH1QuotientReduction X ℓ n) := by
  intro a
  refine Quotient.inductionOn' a ?_
  intro b
  exact ⟨QuotientAddGroup.mk
    (s := (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
      (ℓ ^ ((n + 1) + 1))).range) b,
    ellPowerKummerH1QuotientReduction_mk X ℓ n b⟩

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Original finite coefficient reduction commutes with the original map
to H²(Gm), using the actual power map on the latter group. -/
theorem finiteLevelH2ToMultiplicativeGroup_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 2) :
    finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n (finiteLevelReduction X ℓ n 2 a) =
      Sheaf.H.map (etaleMultiplicativeGroupPower X ℓ) 2
        (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ (n + 1) a) := by
  rw [finiteLevelH2ToMultiplicativeGroup_apply,
    finiteLevelKummerCohomologyEquiv_reduction,
    finiteLevelH2ToMultiplicativeGroup_apply]
  exact kummerH2_powerTransition_of_eq X (pow_succ ℓ (n + 1))
    (finiteLevelKummerCohomologyEquiv c ℓ hℓ (n + 1) 2 a)

/-- The original finite-level reduction restricted to its actual Kummer
kernel; the ambient finite coefficient groups are unchanged. -/
def finiteLevelKummerH2KernelReduction (n : ℕ) :
    (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ (n + 1)).ker →+
      (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker :=
  (((finiteLevelReduction X ℓ n 2).comp
    (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ (n + 1)).ker.subtype).codRestrict
      (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker fun a => by
        change finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n
          (finiteLevelReduction X ℓ n 2 a.val) = 0
        rw [finiteLevelH2ToMultiplicativeGroup_reduction, a.property, map_zero])

/-- The restricted reduction retains the original finite-level map. -/
theorem finiteLevelKummerH2KernelReduction_val (n : ℕ)
    (a : (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ (n + 1)).ker) :
    (finiteLevelKummerH2KernelReduction c ℓ hℓ n a).val =
      finiteLevelReduction X ℓ n 2 a.val := rfl

/-- The actual finite-level Kummer equivalences commute with the original
coefficient reductions and the native H¹(Gm) quotient reductions. -/
theorem finiteLevelKummerH1QuotientEquivH2Kernel_reduction (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
        (ℓ ^ ((n + 1) + 1))).range) :
    finiteLevelKummerH2KernelReduction c ℓ hℓ n
        (finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ (n + 1) a) =
      finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n
        (ellPowerKummerH1QuotientReduction X ℓ n a) := by
  refine Quotient.inductionOn' a ?_
  intro b
  rw [ellPowerKummerH1QuotientReduction_mk X ℓ n b]
  apply Subtype.ext
  apply (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).injective
  rw [finiteLevelKummerH2KernelReduction_val,
    finiteLevelKummerH1QuotientEquivH2Kernel_mk_val,
    finiteLevelKummerH1QuotientEquivH2Kernel_mk_val,
    finiteLevelKummerCohomologyEquiv_reduction,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact kummerBoundary_powerTransition_of_eq X (pow_succ ℓ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1)) (Fact.out : ℓ.Prime).pos
    (pow_pos (Fact.out : ℓ.Prime).pos ((n + 1) + 1))
    (etaleKummerExponentUnit_of_base c
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))
    (etaleKummerExponentUnit_of_base c hℓ)
    (etaleKummerExponentUnit_of_base c
      (by simpa only [Nat.cast_pow] using hℓ.pow ((n + 1) + 1))) b

/-- Every original finite-level Kummer-kernel class lifts under the
original coefficient reduction. -/
theorem finiteLevelKummerH2KernelReduction_surjective (n : ℕ) :
    Function.Surjective (finiteLevelKummerH2KernelReduction c ℓ hℓ n) := by
  intro a
  obtain ⟨b, hb⟩ := (finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n).surjective a
  obtain ⟨d, hd⟩ := ellPowerKummerH1QuotientReduction_surjective X ℓ n b
  refine ⟨finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ (n + 1) d, ?_⟩
  rw [finiteLevelKummerH1QuotientEquivH2Kernel_reduction, hd, hb]

end EtaleCohomology
