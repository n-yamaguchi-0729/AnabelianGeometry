/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FieldKummer
public import Nyll.EtaleCohomology.Classical.KummerH2Kernel
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The original finite-level degree-two Kummer kernel

The existing coherent primitive-root coordinates identify the original
finite cyclic cohomology with the actual Kummer cohomology. Restricting
this identification to the kernel of the original map to H²(Gm) gives
the native H¹(Gm) quotient at every finite level. The map on an original
H¹ class is the actual Kummer boundary in the same root coordinates.
No Picard comparison or vanishing of H²(Gm) is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology.Classical

namespace EtaleCohomology

/-- Restrict an additive equivalence to the kernel of a following homomorphism. -/
def addEquivKernelComp
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (e : A ≃+ B) (f : B →+ C) :
    (f.comp e.toAddMonoidHom).ker ≃+ f.ker where
  toFun a := ⟨e a.val, a.property⟩
  invFun a := ⟨e.symm a.val, by
    change f (e (e.symm a.val)) = 0
    rw [e.apply_symm_apply]
    exact a.property⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
  map_add' a b := Subtype.ext (e.map_add a.val b.val)

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Invertibility of an exponent in the base field gives invertibility
in the original global sections through the actual structural map. -/
theorem etaleKummerExponentUnit_of_base
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hnK : IsUnit (n : K)) :
    IsUnit (n : Γ(X, ⊤)) := by
  let φ : K →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop).hom
  simpa only [map_natCast] using hnK.map φ

variable [IsAlgClosed K] (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The actual finite coefficient H² map to H²(Gm), using the existing
coherent roots and the original Kummer inclusion. -/
def finiteLevelH2ToMultiplicativeGroup (n : ℕ) :
    finiteLevelCohomology X ℓ n 2 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 2 :=
  (etaleRootsOfUnityH2ToMultiplicativeGroup X (ℓ ^ (n + 1))).comp
    (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).toAddMonoidHom

/-- The finite coefficient map retains the original Kummer inclusion. -/
theorem finiteLevelH2ToMultiplicativeGroup_apply (n : ℕ)
    (a : finiteLevelCohomology X ℓ n 2) :
    finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n a =
      etaleRootsOfUnityH2ToMultiplicativeGroup X (ℓ ^ (n + 1))
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2 a) := rfl

/-- The coherent coefficient comparison restricts to the actual kernels
of the respective maps to the original H²(Gm). -/
def finiteLevelKummerH2KernelEquiv (n : ℕ) :
    (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker ≃+
      (etaleRootsOfUnityH2ToMultiplicativeGroup X (ℓ ^ (n + 1))).ker :=
  addEquivKernelComp (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2)
    (etaleRootsOfUnityH2ToMultiplicativeGroup X (ℓ ^ (n + 1)))

/-- The kernel comparison keeps the original finite-to-Kummer map. -/
theorem finiteLevelKummerH2KernelEquiv_val (n : ℕ)
    (a : (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker) :
    (finiteLevelKummerH2KernelEquiv c ℓ hℓ n a).val =
      finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2 a.val := rfl

/-- Native H¹(Gm) modulo the actual finite exponent identifies with the
kernel inside the original finite-level H². -/
def finiteLevelKummerH1QuotientEquivH2Kernel (n : ℕ) :
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
        (ℓ ^ (n + 1))).range) ≃+
      (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker :=
  (etaleKummerH1QuotientEquivH2Kernel X
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (etaleKummerExponentUnit_of_base c
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))).trans
        (finiteLevelKummerH2KernelEquiv c ℓ hℓ n).symm

/-- On an original H¹ class, the finite-level comparison is the original
Kummer boundary in the existing coherent primitive-root coordinates. -/
theorem finiteLevelKummerH1QuotientEquivH2Kernel_mk_val (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    (finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n
      (QuotientAddGroup.mk a)).val =
      (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).symm
        (Sheaf.H.δ (etaleKummerComplex_shortExact X
          (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base c
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) 1 2 rfl a) := rfl

end EtaleCohomology
