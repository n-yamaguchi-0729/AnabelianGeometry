/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.SchemeTheory.Morphisms.ProperIntegralGlobalSections
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Native degree-one Kummer comparison for proper integral schemes

The actual global-section calculation supplies roots of every original
global unit. The original Kummer coefficient inclusion therefore identifies
H¹ of its original kernel with the original torsion subgroup of H¹(Gm).
The existing coherent roots identify the original finite cyclic H¹ with
that subgroup and retain its original coefficient reductions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]

include c in
/-- The actual power map on original degree-zero multiplicative-group
cohomology is surjective, as a consequence of properness. -/
theorem properIntegralMultiplicativeGroupH0_nsmul_surjective
    {n : ℕ} (hn : 0 < n) :
    Function.Surjective
      (fun a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0 => n • a) := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let e : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0 ≃+
      Additive ((Γ(X, ⊤) : Type u)ˣ) :=
    (Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf X) hT).trans
      (etaleMultiplicativeGroupSectionsEquiv X T)
  intro a
  obtain ⟨b, hb⟩ := properIntegralGlobalUnits_pow_surjective c hn (e a).toMul
  refine ⟨e.symm (Additive.ofMul b), ?_⟩
  apply e.injective
  rw [map_nsmul, e.apply_symm_apply]
  change Additive.ofMul (b ^ n) = e a
  exact congrArg Additive.ofMul hb

/-- The original coefficient inclusion identifies actual H¹(μn) with
actual n-torsion in H¹(Gm), with global roots supplied by properness. -/
def properIntegralKummerH1EquivPowerKernel
    {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K)) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1 ≃+
      (nsmulAddMonoidHom n : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 →+
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1).ker :=
  etaleKummerH1EquivPowerKernel X hn (etaleKummerExponentUnit_of_base c hnK)
    (properIntegralMultiplicativeGroupH0_nsmul_surjective c hn)

/-- This comparison retains the original Kummer-kernel inclusion. -/
theorem properIntegralKummerH1EquivPowerKernel_apply
    {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1) :
    (properIntegralKummerH1EquivPowerKernel c hn hnK a).val =
      Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 1 a := rfl

omit [IsIntegral X] in
private theorem kummerH1_powerTransition_of_eq
    {n m N : ℕ} (hN : N = n * m)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X N) 1) :
    etaleRootsOfUnityH1ToMultiplicativeGroup X n
        (Sheaf.H.map (eqToHom (congrArg (etaleRootsOfUnitySheaf X) hN) ≫
          etaleKummerPowerTransition X n m) 1 a) =
      m • etaleRootsOfUnityH1ToMultiplicativeGroup X N a := by
  subst N
  simpa only [eqToHom_refl, Category.id_comp] using
    etaleRootsOfUnityH1ToMultiplicativeGroup_power_transition X n m a

/-- Multiplication by ℓ gives the original torsion transition on
H¹(Gm), with the original consecutive exponents. -/
def ellPowerKummerH1PowerKernelTransition (X : Scheme.{u}) (ℓ n : ℕ) :
    (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
      (ℓ ^ ((n + 1) + 1))).ker →+
    (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
      (ℓ ^ (n + 1))).ker where
  toFun a := ⟨ℓ • a.val, by
    change (ℓ ^ (n + 1)) • (ℓ • a.val) = 0
    rw [← mul_smul, ← pow_succ]
    exact a.property⟩
  map_zero' := Subtype.ext (smul_zero ℓ)
  map_add' a b := Subtype.ext (smul_add ℓ a.val b.val)

/-- The torsion transition uses the same original ambient H¹ class. -/
theorem ellPowerKummerH1PowerKernelTransition_val (X : Scheme.{u}) (ℓ n : ℕ)
    (a : (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
      (ℓ ^ ((n + 1) + 1))).ker) :
    (ellPowerKummerH1PowerKernelTransition X ℓ n a).val = ℓ • a.val := rfl

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original finite cyclic H¹ is the actual power kernel of H¹(Gm),
using the existing coherent primitive-root coefficient map. -/
def properIntegralFiniteLevelH1EquivPowerKernel (n : ℕ) :
    finiteLevelCohomology X ℓ n 1 ≃+
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
        (ℓ ^ (n + 1))).ker :=
  (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 1).trans
    (properIntegralKummerH1EquivPowerKernel c
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))

/-- Each original finite H¹ class maps through the original finite
coefficient comparison and the original Kummer-kernel inclusion. -/
theorem properIntegralFiniteLevelH1EquivPowerKernel_apply (n : ℕ)
    (a : finiteLevelCohomology X ℓ n 1) :
    (properIntegralFiniteLevelH1EquivPowerKernel c ℓ hℓ n a).val =
      etaleRootsOfUnityH1ToMultiplicativeGroup X (ℓ ^ (n + 1))
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 1 a) := rfl

/-- The original finite coefficient reductions become the actual
torsion multiplication transitions of native H¹(Gm). -/
theorem properIntegralFiniteLevelH1EquivPowerKernel_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 1) :
    properIntegralFiniteLevelH1EquivPowerKernel c ℓ hℓ n
        (finiteLevelReduction X ℓ n 1 a) =
      ellPowerKummerH1PowerKernelTransition X ℓ n
        (properIntegralFiniteLevelH1EquivPowerKernel c ℓ hℓ (n + 1) a) := by
  apply Subtype.ext
  rw [properIntegralFiniteLevelH1EquivPowerKernel_apply,
    finiteLevelKummerCohomologyEquiv_reduction,
    ellPowerKummerH1PowerKernelTransition_val,
    properIntegralFiniteLevelH1EquivPowerKernel_apply]
  exact kummerH1_powerTransition_of_eq (pow_succ ℓ (n + 1))
    (finiteLevelKummerCohomologyEquiv c ℓ hℓ (n + 1) 1 a)

end EtaleCohomology
