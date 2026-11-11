/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModuleMaps
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleInvModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealIsoPullbackModuleComparison
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPullbackInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierAdicCyclePullback
public import Nyll.EtaleCohomology.Classical.CartierCyclePullback
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteComponentCohomology
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.InvertibleCartierComparison
public import Nyll.EtaleCohomology.Classical.InvertibleCycleTensor
public import Nyll.SchemeTheory.Divisors.FlatPullback
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite Cartier classes on actual tensor-root covers

A tensor root of the pulled-back signed divisor bundle annihilates its
original finite cycle class. The integral case follows from the original
Kummer boundary and the actual ideal-module pullback comparisons.

For a Noetherian cover with domain stalks, its original finite cohomology
decomposes into the cohomology of its actual integral components. Pulling
the given root to those components proves vanishing on the whole cover;
the cover is not assumed connected or integral.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

private def signedCartierBundlePullbackIso
    {Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    (D E : Scheme.EffectiveCartierDivisor X) :
    (Scheme.Modules.pullback f).obj (D.1.invModule ⊗ E.1.module) ≅
      (D.1.comap f).invModule ⊗ (E.1.comap f).module := by
  let eD : (Scheme.Modules.pullback f).obj D.1.invModule ≅
      (D.1.comap f).invModule := Classical.choice
    (D.2.isInvertible.nonempty_pullback_invModule_iso f
      (D.2.comap_of_flat f).isInvertible)
  have : IsIso (E.1.pullbackModuleComparison f) :=
    E.2.isInvertible.isIso_pullbackModuleComparison f
      (E.2.comap_of_flat f).isInvertible
  exact Scheme.Modules.pullbackTensorObjIso f D.1.invModule E.1.module ≪≫
    tensorIso eD (asIso (E.1.pullbackModuleComparison f))

/-- An actual tensor root retains the original pulled-back signed
Cartier class as the corresponding multiple of that same root's native
H¹(Gm) class, before applying the Kummer boundary. -/
theorem signedCartierMultiplicativeGroupH1_pullback_eq_nsmul_of_tensorPowIso
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [Flat f]
    (N : ℕ) (D E : Scheme.EffectiveCartierDivisor X)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (e : (Scheme.Modules.pullback f).obj (D.1.invModule ⊗ E.1.module) ≅
      L.tensorPow N) :
    etaleMultiplicativeGroupCohomologyPullback f 1
      (effectiveCartierMultiplicativeGroupH1 D -
        effectiveCartierMultiplicativeGroupH1 E) =
      N • invertibleModuleMultiplicativeGroupH1 hL := by
  let D' : Scheme.EffectiveCartierDivisor Y := ⟨D.1.comap f, D.2.comap_of_flat f⟩
  let E' : Scheme.EffectiveCartierDivisor Y := ⟨E.1.comap f, E.2.comap_of_flat f⟩
  let eRoot : D'.1.invModule ⊗ E'.1.module ≅ L.tensorPow N :=
    (signedCartierBundlePullbackIso f D E).symm ≪≫ e
  rw [map_sub, effectiveCartierMultiplicativeGroupH1_pullback f D D'.2,
    effectiveCartierMultiplicativeGroupH1_pullback f E E'.2,
    ← invertibleModuleMultiplicativeGroupH1_eq_signedCartier
      (hL.tensorPow N) D' E' eRoot.symm,
    invertibleModuleMultiplicativeGroupH1_tensorPow]

/-- On an integral flat pullback, an actual root of the signed divisor
bundle kills the signed class in the original finite cohomology. -/
theorem finiteSignedCartierCycleClass_pullback_eq_zero_of_tensorPowIso
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [Flat f]
    (n : ℕ) (D E : Scheme.EffectiveCartierDivisor X)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (e : (Scheme.Modules.pullback f).obj (D.1.invModule ⊗ E.1.module) ≅
      L.tensorPow (ℓ ^ (n + 1))) :
    finiteLevelCohomologyPullback ℓ f n 2
      (finiteEffectiveCartierCycleClass c ℓ hℓ n D -
        finiteEffectiveCartierCycleClass c ℓ hℓ n E) = 0 := by
  let D' : Scheme.EffectiveCartierDivisor Y := ⟨D.1.comap f, D.2.comap_of_flat f⟩
  let E' : Scheme.EffectiveCartierDivisor Y := ⟨E.1.comap f, E.2.comap_of_flat f⟩
  let hB := D'.2.isInvertible.isInvertible_invModule.tensor
    E'.2.isInvertible.isInvertible_module
  let eRoot : D'.1.invModule ⊗ E'.1.module ≅ L.tensorPow (ℓ ^ (n + 1)) :=
    (signedCartierBundlePullbackIso f D E).symm ≪≫ e
  rw [map_sub, finiteEffectiveCartierCycleClass_pullback f c ℓ hℓ n D D'.2,
    finiteEffectiveCartierCycleClass_pullback f c ℓ hℓ n E E'.2]
  let eK := finiteLevelKummerCohomologyEquiv (f ≫ c) ℓ hℓ n 2
  apply eK.injective
  let hn := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  let hnY := etaleKummerExponentUnit_of_base (f ≫ c)
    (show IsUnit ((ℓ ^ (n + 1) : ℕ) : K) by
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
  have hD : eK (finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n D') =
      effectiveCartierCycleClass D' hn hnY :=
    finiteEffectiveCartierCycleClass_kummer (f ≫ c) ℓ hℓ n D'
  have hE : eK (finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n E') =
      effectiveCartierCycleClass E' hn hnY :=
    finiteEffectiveCartierCycleClass_kummer (f ≫ c) ℓ hℓ n E'
  calc
    eK (finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n D' -
        finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n E') =
      eK (finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n D') -
        eK (finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n E') :=
      map_sub eK _ _
    _ = effectiveCartierCycleClass D' hn hnY -
        effectiveCartierCycleClass E' hn hnY :=
      congrArg₂ (fun a b => a - b) hD hE
    _ = 0 :=
      (invertibleModuleCycleClass_eq_signedCartier hB D' E'
        (Iso.refl _) hn hnY).symm.trans
          (invertibleModuleCycleClass_eq_zero_of_tensorPowIso hB hL eRoot hn hnY)
    _ = eK 0 := (map_zero eK).symm

/-- The same actual root kills the original finite class on a possibly
disconnected cover. Its actual component decomposition supplies every
integral comparison used in the proof. -/
theorem finiteSignedCartierCycleClass_pullback_eq_zero_of_tensorPowIso_components
    {Y : Scheme.{u}} [IsNoetherian Y]
    (hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (f : Y ⟶ X) [Flat f] (n : ℕ)
    (D E : Scheme.EffectiveCartierDivisor X)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (e : (Scheme.Modules.pullback f).obj (D.1.invModule ⊗ E.1.module) ≅
      L.tensorPow (ℓ ^ (n + 1))) :
    finiteLevelCohomologyPullback ℓ f n 2
      (finiteEffectiveCartierCycleClass c ℓ hℓ n D -
        finiteEffectiveCartierCycleClass c ℓ hℓ n E) = 0 := by
  apply (finiteLevelComponentCohomologyEquiv Y hdom ℓ n 2).injective
  apply funext
  intro Z
  let i := Y.reducedIrreducibleComponentι Z.1 Z.2
  have : IsOpenImmersion i :=
    Y.reducedIrreducibleComponentι_isOpenImmersion hdom Z.1 Z.2
  let LZ := (Scheme.Modules.pullback i).obj L
  have hLZ : Scheme.Modules.IsInvertible LZ := Scheme.Modules.IsInvertible.pullback i hL
  let eZ : (Scheme.Modules.pullback (i ≫ f)).obj (D.1.invModule ⊗ E.1.module) ≅
      LZ.tensorPow (ℓ ^ (n + 1)) :=
    ((Scheme.Modules.pullbackComp i f).app (D.1.invModule ⊗ E.1.module)).symm ≪≫
      (Scheme.Modules.pullback i).mapIso e ≪≫
        Scheme.Modules.pullbackTensorPowIso i L (ℓ ^ (n + 1))
  rw [map_zero, Pi.zero_apply, finiteLevelComponentCohomologyEquiv_eq_pullback]
  change finiteLevelCohomologyPullback ℓ i n 2
    (finiteLevelCohomologyPullback ℓ f n 2 _) = 0
  rw [← LinearMap.comp_apply, ← finiteLevelCohomologyPullback_comp]
  exact finiteSignedCartierCycleClass_pullback_eq_zero_of_tensorPowIso
    c ℓ hℓ (i ≫ f) n D E LZ hLZ eZ

end EtaleCohomology
