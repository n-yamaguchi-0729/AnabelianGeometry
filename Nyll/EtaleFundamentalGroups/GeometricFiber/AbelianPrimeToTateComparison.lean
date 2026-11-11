/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitTateFamilies
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromyKernel
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPowerDetection
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Mathlib.Algebra.CharP.Defs

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitTorsionFiber
public import Nyll.ProCGroups.Abelian.RestrictedTateModule

/-!
# The actual prime-to-p fundamental group and Tate module

The kernel of all invertible multiplication coordinates is the actual residual
core for finite groups of order prime to the characteristic. One inclusion
uses the actual finite torsion groups and Cauchy's theorem. The other uses the
actual image of the multiplication-cover fundamental group and powers in
finite Sigma quotients. No p-primary part is discarded by hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open ProCGroups ProCGroups.ProC
open scoped BigOperators

namespace GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication

variable {K : Type u} [Field K]

section Indices

variable (p : ℕ) [CharP K p]

private theorem sigmaNumber_of_unitIndex (n : unitIndices K) :
    FiniteGroupClass.IsSigmaNumber ({p}ᶜ : Set ℕ) (n.1 : ℕ) := by
  intro q _ hnot hdiv
  have hqp : q = p := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hnot
  subst q
  exact (isUnit_iff_ne_zero.mp n.2) ((CharP.cast_eq_zero_iff K p (n.1 : ℕ)).mpr hdiv)

variable [Fact p.Prime]

/-- The invertible positive indices are precisely those prime to the characteristic. -/
theorem mem_unitIndices_iff_coprime (n : ℕ+) :
    n ∈ unitIndices K ↔ (n : ℕ).Coprime p := by
  change IsUnit ((n : ℕ) : K) ↔ _
  rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff K p]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.symm.trans Nat.coprime_comm

private theorem isUnit_of_sigmaNumber (n : ℕ)
    (hn : FiniteGroupClass.IsSigmaNumber ({p}ᶜ : Set ℕ) n) : IsUnit (n : K) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hp : p ∉ ({p}ᶜ : Set ℕ) := not_not.mpr rfl
  exact hn p (Fact.out : p.Prime) hp ((CharP.cast_eq_zero_iff K p n).mp hz)

end Indices

section Sigma

variable [IsSepClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  (sigma : Set ℕ) (hI : ∀ n : sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K))

local instance (n : ℕ+) : TopologicalSpace (torsionLevel (G.AlgPoints hc K) n) :=
  FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n

local instance (n : ℕ+) : DiscreteTopology (torsionLevel (G.AlgPoints hc K) n) := ⟨rfl⟩

/-- Actual multiplication monodromy at exactly the positive Sigma-indices. -/
def toSigmaTate (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val)) :
    RestrictedTateModule (G.AlgPoints hc K) (sigmaTorsionIndices sigma) :=
  ⟨fun n => monodromy G hc ⟨n.val, hI n⟩ g,
    fun n m => monodromy_compatible G hc ⟨n.val, hI n⟩ ⟨m.val, hI m⟩ g⟩

/-- The actual Sigma-monodromy map retains the inverse-limit topology. -/
def toSigmaTateHom :
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc K) (sigmaTorsionIndices sigma)) where
  toFun g := Multiplicative.ofAdd (toSigmaTate G hc sigma hI g)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    exact monodromy_one G hc ⟨n.val, hI n⟩
  map_mul' g h := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    exact monodromy_mul G hc ⟨n.val, hI n⟩ g h
  continuous_toFun :=
    (continuous_pi (fun n => monodromy_continuous G hc ⟨n.val, hI n⟩)).subtype_mk
      (fun g n m => monodromy_compatible G hc ⟨n.val, hI n⟩ ⟨m.val, hI m⟩ g)

/-- The kernel is the actual pro-Sigma residual core. Its two inclusions use
multiplication-cover powers and the finite Sigma torsion groups, respectively. -/
theorem toSigmaTateHom_ker_eq_residualCore [GeometricallyConnected f] :
    (toSigmaTateHom G hc sigma hI).toMonoidHom.ker =
      proCResidualCore (FiniteGroupClass.sigmaGroup sigma)
        π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val) := by
  apply le_antisymm
  · intro g hg
    apply mem_proCResidualCore_of_forall_sigmaPower sigma g
    intro n hn hs
    let index : sigmaTorsionIndices sigma := ⟨⟨n, hn⟩, hs⟩
    apply (monodromy_eq_zero_iff_exists_pow G hc ⟨index.val, hI index⟩ g).mp
    exact congrArg (fun x : Multiplicative
      (RestrictedTateModule (G.AlgPoints hc K) (sigmaTorsionIndices sigma)) =>
        (Multiplicative.toAdd x).val index) hg
  · intro g hg
    change Multiplicative.ofAdd (toSigmaTate G hc sigma hI g) = 1
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    let index : unitIndices K := ⟨n.val, hI n⟩
    have _ : Finite (torsionLevel (G.AlgPoints hc K) n.val) :=
      finite_torsionLevel G hc index
    have hpow (x : Multiplicative (torsionLevel (G.AlgPoints hc K) n.val)) :
        x ^ (n.val : ℕ) = 1 := by
      change (n.val : ℕ) • Multiplicative.toAdd x = 0
      apply Subtype.ext
      exact (Multiplicative.toAdd x).property
    have hle := proCResidualCore_le_ker_of_finite_exponent sigma
      (monodromyHom G hc index) (n.val : ℕ) n.property hpow
    exact congrArg Multiplicative.toAdd (hle hg)

/-- Every compatible Sigma-torsion family is realized by the original
multiplication monodromy, using compactness and products of Sigma-indices. -/
theorem toSigmaTate_surjective [GeometricallyConnected f] :
    Function.Surjective (toSigmaTate G hc sigma hI) := by
  classical
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  intro x
  let P := π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val)
  let Z : sigmaTorsionIndices sigma → Set P := fun n =>
    {g | monodromy G hc ⟨n.val, hI n⟩ g = x.val n}
  have hclosed : ∀ n, IsClosed (Z n) := fun n =>
    isClosed_eq (monodromy_continuous G hc ⟨n.val, hI n⟩) continuous_const
  have hfinite : ∀ s : Finset (sigmaTorsionIndices sigma), (⋂ n ∈ s, Z n).Nonempty := by
    intro s
    let N : sigmaTorsionIndices sigma := ∏ n ∈ s, n
    obtain ⟨g, hg⟩ := monodromy_surjective G hc ⟨N.val, hI N⟩ (x.val N)
    refine ⟨g, Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i : sigmaTorsionIndices sigma => i) hn
    have hN : N = n * m := hm
    change monodromy G hc ⟨n.val, hI n⟩ g = x.val n
    calc
      monodromy G hc ⟨n.val, hI n⟩ g =
          torsionTransition (G.AlgPoints hc K) n.val m.val
            (monodromy G hc ⟨(n * m).val, hI (n * m)⟩ g) :=
        (monodromy_compatible G hc ⟨n.val, hI n⟩ ⟨m.val, hI m⟩ g).symm
      _ = torsionTransition (G.AlgPoints hc K) n.val m.val (x.val (n * m)) := by
        have hi : monodromy G hc ⟨(n * m).val, hI (n * m)⟩ g = x.val (n * m) := by
          rw [← hN]
          exact hg
        exact congrArg (torsionTransition (G.AlgPoints hc K) n.val m.val) hi
      _ = x.val n := x.property n m
  obtain ⟨g, hg⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨g, ?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp hg n

/-- The actual pro-Sigma fundamental group of a proper smooth commutative
group is its restricted Tate module whenever the Sigma-indices are invertible. -/
def fundamentalGroupSigmaEquivTate [GeometricallyConnected f] :
    (π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val) ⧸
      proCResidualCore (FiniteGroupClass.sigmaGroup sigma)
        π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc K) (sigmaTorsionIndices sigma)) := by
  let P := π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val)
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) P
  let φ := toSigmaTateHom G hc sigma hI
  have hker : φ.toMonoidHom.ker = R := toSigmaTateHom_ker_eq_residualCore G hc sigma hI
  let ψ := ProCGroups.QuotientGroup.liftₜ R φ hker.ge
  have hinj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R y
    apply (QuotientGroup.eq_iff_div_mem (N := R)).mpr
    rw [← hker]
    change φ (a / b) = 1
    change φ a = φ b at hxy
    rw [map_div, hxy]
    exact div_self' (φ b)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg⟩ := toSigmaTate_surjective G hc sigma hI y.toAdd
    exact ⟨QuotientGroup.mk' R g, congrArg Multiplicative.ofAdd hg⟩
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    ψ.toMonoidHom ψ.continuous_toFun ⟨hinj, hsurj⟩

/-- The Sigma comparison evaluates the original unit-fibre action at every index. -/
@[simp] theorem fundamentalGroupSigmaEquivTate_apply_mk [GeometricallyConnected f]
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val)) :
    fundamentalGroupSigmaEquivTate G hc sigma hI
      (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.sigmaGroup sigma)
        π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val)) g) =
      toSigmaTateHom G hc sigma hI g := rfl

/-- The actual pro-Sigma Tate comparison at an arbitrary geometric point.
The only basepoint transport is the original fiber-functor isomorphism. -/
def fundamentalGroupSigmaEquivTateAt [GeometricallyConnected f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ A) :
    (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) π₁ᵉᵗ(xi)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc K) (sigmaTorsionIndices sigma)) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 _)).val
  let t : fiber xi ≅ fiber e := Classical.choice (nonempty_fiber_iso xi e)
  exact (residualQuotientContinuousMulEquiv
    (FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary
    (fundamentalGroupIsoOfFiberIso xi e t)).trans
      (fundamentalGroupSigmaEquivTate G hc sigma hI)

end Sigma

variable [IsSepClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  (p : ℕ) [Fact p.Prime] [CharP K p]

local instance (n : ℕ+) : TopologicalSpace (torsionLevel (G.AlgPoints hc K) n) :=
  FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n

local instance (n : ℕ+) : DiscreteTopology (torsionLevel (G.AlgPoints hc K) n) := ⟨rfl⟩

/-- The kernel of the actual compatible-family map is precisely the actual
prime-to-p residual core of the original fundamental group. -/
theorem toTateHom_ker_eq_residualCore :
    (toTateHom G hc).toMonoidHom.ker =
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ))
        π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) := by
  apply le_antisymm
  · intro g hg
    apply mem_proCResidualCore_of_forall_sigmaPower ({p}ᶜ : Set ℕ) g
    intro n hn hs
    let index : unitIndices K := ⟨⟨n, hn⟩, isUnit_of_sigmaNumber (K := K) p n hs⟩
    apply (monodromy_eq_zero_iff_exists_pow G hc index g).mp
    exact congrArg (fun x : Multiplicative
      (RestrictedTateModule (G.AlgPoints hc K) (unitIndices K)) =>
        (Multiplicative.toAdd x).1 index) hg
  · intro g hg
    change Multiplicative.ofAdd (toTate G hc g) = 1
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    have _ : Finite (torsionLevel (G.AlgPoints hc K) n.1) := finite_torsionLevel G hc n
    have hpow (x : Multiplicative (torsionLevel (G.AlgPoints hc K) n.1)) :
        x ^ (n.1 : ℕ) = 1 := by
      change (n.1 : ℕ) • Multiplicative.toAdd x = 0
      apply Subtype.ext
      exact (Multiplicative.toAdd x).2
    have hle := proCResidualCore_le_ker_of_finite_exponent
      ({p}ᶜ : Set ℕ) (monodromyHom G hc n) (n.1 : ℕ)
      (sigmaNumber_of_unitIndex (K := K) p n) hpow
    exact congrArg Multiplicative.toAdd (hle hg)

/-- The maximal prime-to-p quotient of the actual etale fundamental group is
the inverse limit of the actual torsion points at all prime-to-p indices. -/
def fundamentalGroupPrimeToEquivTate :
    (π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) ⧸
      proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ))
        π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc K) (unitIndices K)) := by
  let P := π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)
  let R : Subgroup P := proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) P
  let phi := toTateHom G hc
  have hker : phi.toMonoidHom.ker = R := toTateHom_ker_eq_residualCore G hc p
  let psi : P ⧸ R →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc K) (unitIndices K)) :=
    ProCGroups.QuotientGroup.liftₜ R phi hker.ge
  have hinj : Function.Injective psi := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R y
    apply (QuotientGroup.eq_iff_div_mem (N := R)).mpr
    rw [← hker]
    change phi (a / b) = 1
    change phi a = phi b at hxy
    rw [map_div, hxy]
    exact div_self' (phi b)
  have hsurj : Function.Surjective psi := by
    intro y
    obtain ⟨g, hg⟩ := toTate_surjective G hc (Multiplicative.toAdd y)
    exact ⟨QuotientGroup.mk' R g, congrArg Multiplicative.ofAdd hg⟩
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    psi.toMonoidHom psi.continuous_toFun ⟨hinj, hsurj⟩

/-- Every coordinate is the action on the actual unit of the actual multiplication fibre. -/
theorem fundamentalGroupPrimeToEquivTate_projection
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) (n : unitIndices K) :
    RestrictedTateModule.projection (G.AlgPoints hc K) (unitIndices K) n
      (Multiplicative.toAdd (fundamentalGroupPrimeToEquivTate G hc p
        (QuotientGroup.mk'
          (proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ))
            π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) g))) = monodromy G hc n g := by
  rfl

/-- At any separably closed geometric basepoint, the same actual prime-to-p
Tate module describes the maximal prime-to-p quotient. The basepoint comparison
is chosen internally from the actual fibre-functor comparison theorem. -/
def fundamentalGroupPrimeToEquivTateAt
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ A) :
    (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)) π₁ᵉᵗ(xi)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc K) (unitIndices K)) := by
  have _ : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  let t : fiber xi ≅ fiber e := Classical.choice (nonempty_fiber_iso xi e)
  let b : π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(e) := fundamentalGroupIsoOfFiberIso xi e t
  let C := FiniteGroupClass.sigmaGroup ({p}ᶜ : Set ℕ)
  have hmap : (proCResidualCore C π₁ᵉᵗ(xi)).map b.toMulEquiv.toMonoidHom =
      proCResidualCore C π₁ᵉᵗ(e) :=
    map_proCResidualCore_eq_of_surjective
      (FiniteGroupClass.sigmaGroup_fullFormation ({p}ᶜ : Set ℕ))
      b.toMulEquiv.toMonoidHom b.continuous_toFun b.surjective
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (FiniteGroupClass.sigmaGroup_formation ({p}ᶜ : Set ℕ)))
  exact (ProCGroups.QuotientGroup.congrₜ
    (proCResidualCore C π₁ᵉᵗ(xi)) (proCResidualCore C π₁ᵉᵗ(e)) b hmap).trans
      (fundamentalGroupPrimeToEquivTate G hc p)

end GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
