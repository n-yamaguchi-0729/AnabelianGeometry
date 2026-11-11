/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The valuative argument uses the FLT-derived implementation in Reduction/Inertia.lean.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC. Apache-2.0.
Pinned source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Algebra.Algebra.Tower
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.AbelianVarieties.Reduction.Inertia
public import Nyll.AbelianVarieties.Tate.TorsionFree
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.KernelPoints
public import Nyll.AbelianVarieties.Geometry.Torsion.Degree
public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.EqCompEq

/-!
# All-order specialization through a valuation ring

Properness identifies points over a valuation ring with points over its fraction
field. Composing the inverse with residue reduction gives an actual additive
specialization map, including residue-characteristic torsion. Actual inertia
acts trivially on this reduced point.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open
  AbelianVarieties.NOSProofs.TorsionInertia.GoodReductionJacobian.RelativeGroupLaw.InertiaOnTorsion

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (V : ValuationSubring Ω) [Algebra R V] [Algebra R Ω] [IsScalarTower R V Ω]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsProper f]
  (L : RelativeGroupLaw R f) (hc : L.IsCommutative)

/-- Properness and separatedness give unique extension of algebraic points
across the chosen valuation ring, with the original coefficient maps. -/
theorem valuationPointMap_bijective :
    Function.Bijective
      (AlgPoints.map (L := L) (hc := hc) (IsScalarTower.toAlgHom R V Ω)) := by
  let i := IsScalarTower.toAlgHom R V Ω
  let s := Spec.map (CommRingCat.ofHom (algebraMap R V))
  let t := Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  let j := Spec.map (CommRingCat.ofHom (algebraMap V Ω))
  have hbase : j ≫ s = t := AlgPoints.specMap_comp_algebraMap i
  constructor
  · intro a b hab
    let S : ValuativeCommSq f :=
      ⟨V, Ω, (AlgPoints.toPoint (AlgPoints.map i a)).1, s,
        ⟨(AlgPoints.toPoint (AlgPoints.map i a)).2.trans hbase.symm⟩⟩
    let la : S.commSq.LiftStruct := ⟨(AlgPoints.toPoint a).1, rfl,
      (AlgPoints.toPoint a).2⟩
    let lb : S.commSq.LiftStruct := ⟨(AlgPoints.toPoint b).1,
      congrArg (fun x : L.AlgPoints hc Ω => (AlgPoints.toPoint x).1) hab.symm,
      (AlgPoints.toPoint b).2⟩
    apply AlgPoints.ext
    apply Subtype.ext
    exact congrArg CategoryTheory.CommSq.LiftStruct.l
      ((IsSeparated.valuativeCriterion f S).elim la lb)
  · intro x
    let S : ValuativeCommSq f :=
      ⟨V, Ω, (AlgPoints.toPoint x).1, s, ⟨(AlgPoints.toPoint x).2.trans hbase.symm⟩⟩
    have hE : ValuativeCriterion.Existence f :=
      (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
    obtain ⟨l⟩ := (hE S).exists_lift
    refine ⟨AlgPoints.ofPoint ⟨l.l, l.fac_right⟩, ?_⟩
    apply AlgPoints.ext
    exact Subtype.ext l.fac_left

/-- Restriction to the fraction field as an additive equivalence; its inverse
is the unique proper extension, not a choice of a torsion lift. -/
def valuationPointEquiv : L.AlgPoints hc V ≃+ L.AlgPoints hc Ω :=
  AddEquiv.ofBijective (AlgPoints.map (IsScalarTower.toAlgHom R V Ω))
    (valuationPointMap_bijective V L hc)

variable [Algebra R (IsLocalRing.ResidueField V)]
  [IsScalarTower R V (IsLocalRing.ResidueField V)]

/-- The original proper group scheme's additive reduction map through `V`. -/
def valuationSpecialization :
    L.AlgPoints hc Ω →+ L.AlgPoints hc (IsLocalRing.ResidueField V) :=
  (AlgPoints.map (IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V))).comp
    (valuationPointEquiv V L hc).symm.toAddMonoidHom

/-- An integral point specializes to its actual residue-field point. -/
@[simp] theorem valuationSpecialization_map (x : L.AlgPoints hc V) :
    valuationSpecialization V L hc
        (AlgPoints.map (IsScalarTower.toAlgHom R V Ω) x) =
      AlgPoints.map (IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V)) x := by
  exact congrArg
    (AlgPoints.map (IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V)))
    ((valuationPointEquiv V L hc).symm_apply_apply x)

/-- Specialization preserves torsion of every order, including powers of the
residue characteristic; no invertibility hypothesis on the order is used. -/
theorem valuationSpecialization_torsion (n : ℕ) (x : L.AlgPoints hc Ω)
    (hx : n • x = 0) : n • valuationSpecialization V L hc x = 0 := by
  rw [← map_nsmul, hx, map_zero]


/-- Reduction distinguishes generic torsion points whose order is invertible
in the local base ring. The proof uses the actual proper extensions and the
formally unramified multiplication map. -/
theorem valuationSpecialization_eq_of_nsmul_eq_zero [IsLocalRing R]
    (n : ℕ) (hn : IsUnit (n : R)) (x y : L.AlgPoints hc Ω)
    (hx : n • x = 0) (hy : n • y = 0)
    (hxy : valuationSpecialization V L hc x = valuationSpecialization V L hc y) :
    x = y := by
  obtain ⟨a, rfl⟩ := (valuationPointMap_bijective V L hc).surjective x
  obtain ⟨b, rfl⟩ := (valuationPointMap_bijective V L hc).surjective y
  have ha : n • a = 0 := by
    apply (valuationPointMap_bijective V L hc).injective
    rw [map_nsmul, map_zero]
    exact hx
  have hb : n • b = 0 := by
    apply (valuationPointMap_bijective V L hc).injective
    rw [map_nsmul, map_zero]
    exact hy
  have : FormallyUnramified (L.schemeNsmul n) :=
    formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing L hc n hn
  have : LocallyOfFiniteType (L.schemeNsmul n) := by
    have : LocallyOfFiniteType (L.schemeNsmul n ≫ f) := by
      rw [L.schemeNsmul_over]
      infer_instance
    exact locallyOfFiniteType_of_comp _ f
  apply congrArg (AlgPoints.map (IsScalarTower.toAlgHom R V Ω))
  apply AlgPoints.ext
  apply Subtype.ext
  refine AlgebraicGeometry.eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
    (L.schemeNsmul n) V (AlgPoints.toPoint a).1 (AlgPoints.toPoint b).1 ?_ ?_
  · rw [coe_comp_schemeNsmul_of_isTorsionPoint L ((AlgPoints.nsmul_eq_zero_iff n a).mp ha),
      coe_comp_schemeNsmul_of_isTorsionPoint L ((AlgPoints.nsmul_eq_zero_iff n b).mp hb)]
  · rw [valuationSpecialization_map, valuationSpecialization_map] at hxy
    exact congrArg
      (fun z : L.AlgPoints hc (IsLocalRing.ResidueField V) => (AlgPoints.toPoint z).1) hxy

/-- Every residue point killed by a nonzero integer is the specialization of
an actual generic point killed by that same integer. This includes powers of
the residue characteristic; no invertibility assumption is imposed. -/
theorem exists_torsion_valuationSpecialization_eq [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (n : ℕ) (hn : n ≠ 0) (y : L.AlgPoints hc (IsLocalRing.ResidueField V))
    (hy : n • y = 0) :
    ∃ x : L.AlgPoints hc Ω, n • x = 0 ∧ valuationSpecialization V L hc x = y := by
  have hkernel := isFinite_and_flat_schemeKerStr_of_ne_zero L hc hA n hn
  have : IsFinite (L.schemeKerStr n) := hkernel.1
  have : Flat (L.schemeKerStr n) := hkernel.2
  let tV := Spec.map (CommRingCat.ofHom (algebraMap R V))
  let tκ := Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField V)))
  let ytors : L.torsionSubset tκ n :=
    ⟨AlgPoints.toPoint y, (AlgPoints.nsmul_eq_zero_iff n y).mp hy⟩
  let yker := L.torsionSubsetEquivSchemeKerPoints tκ n ytors
  obtain ⟨zker, hreduce⟩ :=
    SchemeTheory.Affine.FiniteScheme.exists_valuationPointLift V (L.schemeKerStr n) yker
  let ztors := (L.torsionSubsetEquivSchemeKerPoints tV n).symm zker
  let z : L.AlgPoints hc V := AlgPoints.ofPoint ztors.1
  have hz : n • z = 0 := (AlgPoints.nsmul_eq_zero_iff n z).mpr ztors.2
  have hzreduce : AlgPoints.map
      (IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V)) z = y := by
    apply AlgPoints.ext
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫
      (zker.1 ≫ CategoryTheory.Limits.pullback.fst (L.schemeNsmul n)
        (L.one (𝟙 (Spec (CommRingCat.of R)))).1) = (AlgPoints.toPoint y).1
    rw [← Category.assoc, hreduce]
    exact L.torsionSubsetEquivSchemeKerPoints_comp_fst tκ n ytors
  refine ⟨AlgPoints.map (IsScalarTower.toAlgHom R V Ω) z, ?_, ?_⟩
  · rw [← map_nsmul, hz, map_zero]
  · rw [valuationSpecialization_map]
    exact hzreduce

/-- The actual reduction map on compatible prime-power torsion sequences. -/
def valuationTateSpecialization (p : ℕ) [Fact p.Prime] :
    TateModule p (L.AlgPoints hc Ω) →ₗ[ℤ_[p]]
      TateModule p (L.AlgPoints hc (IsLocalRing.ResidueField V)) :=
  TateModule.map p (valuationSpecialization V L hc)

/-- Every actual residue Tate sequence lifts compatibly to the generic fibre.
Finite torsion kernels and finite-level specialization supply the nonempty
finite lift sets. -/
theorem valuationTateSpecialization_surjective [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (valuationTateSpecialization V L hc p) := by
  apply TateModule.map_surjective_of_surjective_on_torsion p
    (valuationSpecialization V L hc)
  · intro n
    exact finite_torsionBy_algPoints L hc hA Ω (p ^ n)
      (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  · intro n y hy
    have hynat : p ^ n • y = 0 := by
      simpa only [natCast_zsmul] using hy
    obtain ⟨x, hx, hsp⟩ := exists_torsion_valuationSpecialization_eq V L hc hA
      (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) y hynat
    refine ⟨x, ?_, hsp⟩
    simpa only [natCast_zsmul] using hx

/-- At a prime invertible in the local base, the actual Tate specialization
is injective, by rigidity at each finite torsion level. -/
theorem valuationTateSpecialization_injective_of_isUnit [IsLocalRing R]
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) :
    Function.Injective (valuationTateSpecialization V L hc p) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  refine valuationSpecialization_eq_of_nsmul_eq_zero V L hc (p ^ n)
    (by simpa only [Nat.cast_pow] using hp.pow n) _ _ ?_ ?_ ?_
  · simpa only [natCast_zsmul] using TateModule.torsion x n
  · simpa only [natCast_zsmul] using TateModule.torsion y n
  · exact congrArg
      (fun z : TateModule p (L.AlgPoints hc (IsLocalRing.ResidueField V)) =>
        (z : ℕ → L.AlgPoints hc (IsLocalRing.ResidueField V)) n) hxy

/-- Good reduction gives a bijection on the actual prime-power Tate modules
when the prime is invertible in the Noetherian local base. -/
theorem valuationTateSpecialization_bijective_of_isUnit
    [IsLocalRing R] [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) :
    Function.Bijective (valuationTateSpecialization V L hc p) :=
  ⟨valuationTateSpecialization_injective_of_isUnit V L hc p hp,
    valuationTateSpecialization_surjective V L hc hA p⟩

section Inertia

variable (K : Type u) [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω]

/-- The actual inertia action on the generic point has the same residue under
proper specialization. This holds on all points, without a prime-to-residue
restriction or a good-reduction Tate comparison hypothesis. -/
theorem valuationSpecialization_inertia
    (d : V.decompositionSubgroup K) (hd : d ∈ V.inertiaSubgroup K)
    (x : L.AlgPoints hc Ω) :
    valuationSpecialization V L hc
        (AlgPoints.map ((d : Ω ≃ₐ[K] Ω).restrictScalars R).toAlgHom x) =
      valuationSpecialization V L hc x := by
  let a : V →ₐ[R] V :=
    { toRingHom := decompRingHom V d
      commutes' r := by
        apply Subtype.ext
        change (d : Ω ≃ₐ[K] Ω) (algebraMap V Ω (algebraMap R V r)) =
          algebraMap V Ω (algebraMap R V r)
        rw [← IsScalarTower.algebraMap_apply R V Ω,
          IsScalarTower.algebraMap_apply R K Ω]
        exact (d : Ω ≃ₐ[K] Ω).commutes (algebraMap R K r) }
  let b : Ω →ₐ[R] Ω := ((d : Ω ≃ₐ[K] Ω).restrictScalars R).toAlgHom
  let i := IsScalarTower.toAlgHom R V Ω
  let r := IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V)
  have hgeneric : b.comp i = i.comp a := by
    ext z
    rfl
  have hresidue : r.comp a = r := by
    apply AlgHom.ext
    intro z
    exact congrArg (fun g : V →+* IsLocalRing.ResidueField V => g z)
      (residue_comp_decompRingHom V d hd)
  obtain ⟨z, rfl⟩ := (valuationPointMap_bijective V L hc).surjective x
  have hpoints : AlgPoints.map b (AlgPoints.map i z) =
      AlgPoints.map i (AlgPoints.map a z) := by
    rw [← AddMonoidHom.comp_apply, ← AlgPoints.map_comp, hgeneric,
      AlgPoints.map_comp, AddMonoidHom.comp_apply]
  change valuationSpecialization V L hc (AlgPoints.map b (AlgPoints.map i z)) =
    valuationSpecialization V L hc (AlgPoints.map i z)
  rw [hpoints, valuationSpecialization_map, valuationSpecialization_map]
  change AlgPoints.map r (AlgPoints.map a z) = AlgPoints.map r z
  rw [← AddMonoidHom.comp_apply, ← AlgPoints.map_comp, hresidue]

variable (p : ℕ) [Fact p.Prime]

/-- The representation of the actual chosen inertia subgroup on the generic
Tate module, via its original automorphisms of the coefficient field. -/
def valuationInertiaTateRepresentation :
    Representation ℤ_[p] (V.inertiaSubgroup K) (TateModule p (L.AlgPoints hc Ω)) :=
  (TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[R] Ω)).comp
    ((AlgEquiv.restrictScalarsHom R).comp
      ((V.decompositionSubgroup K).subtype.comp (V.inertiaSubgroup K).subtype))

/-- Specialization annihilates inertia differences on actual compatible
sequences, including when the indexing prime is the residue characteristic. -/
theorem valuationTateSpecialization_inertia
    (d : V.inertiaSubgroup K) :
    (valuationTateSpecialization V L hc p).comp
        (valuationInertiaTateRepresentation V L hc K p d) =
      valuationTateSpecialization V L hc p := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact valuationSpecialization_inertia V L hc K d.val d.property
    ((x : ℕ → L.AlgPoints hc Ω) n)

/-- Descent of the actual Tate specialization to the actual inertia coinvariants. -/
def valuationInertiaCoinvariantSpecialization :
    (valuationInertiaTateRepresentation V L hc K p).Coinvariants →ₗ[ℤ_[p]]
      TateModule p (L.AlgPoints hc (IsLocalRing.ResidueField V)) :=
  Representation.Coinvariants.lift
    (valuationInertiaTateRepresentation V L hc K p)
    (valuationTateSpecialization V L hc p)
    (valuationTateSpecialization_inertia V L hc K p)

/-- Tate specialization factors further through the torsion-free quotient of
inertia coinvariants. -/
def valuationInertiaTorsionFreeSpecialization :
    ((valuationInertiaTateRepresentation V L hc K p).Coinvariants ⧸
      Submodule.torsion ℤ_[p]
        (valuationInertiaTateRepresentation V L hc K p).Coinvariants) →ₗ[ℤ_[p]]
      TateModule p (L.AlgPoints hc (IsLocalRing.ResidueField V)) :=
  Submodule.liftQ _ (valuationInertiaCoinvariantSpecialization V L hc K p) (by
    intro x hx
    obtain ⟨a, ha⟩ := hx
    change (a : ℤ_[p]) • x = 0 at ha
    have himage : (a : ℤ_[p]) • valuationInertiaCoinvariantSpecialization V L hc K p x = 0 := by
      rw [← map_smul, ha, map_zero]
    exact (smul_eq_zero_iff_right (nonZeroDivisors.coe_ne_zero a)).mp himage)

/-- The two quotient steps retain the original Tate specialization on every sequence. -/
@[simp] theorem valuationInertiaTorsionFreeSpecialization_mk
    (x : TateModule p (L.AlgPoints hc Ω)) :
    valuationInertiaTorsionFreeSpecialization V L hc K p
        (Submodule.mkQ _
          (Representation.Coinvariants.mk
            (valuationInertiaTateRepresentation V L hc K p) x)) =
      valuationTateSpecialization V L hc p x := rfl

omit [Algebra R V] [IsScalarTower R V Ω] [IsProper f]
  [Algebra R (IsLocalRing.ResidueField V)]
  [IsScalarTower R V (IsLocalRing.ResidueField V)] in
/-- The kernel of the two actual inertia quotient maps is the prime-power
saturation of the submodule generated by inertia differences. This formula
also applies when the indexing prime is the residue characteristic. -/
theorem valuationInertiaTorsionFree_mk_eq_zero_iff
    (x : TateModule p (L.AlgPoints hc Ω)) :
    Submodule.mkQ
        (Submodule.torsion ℤ_[p]
          (valuationInertiaTateRepresentation V L hc K p).Coinvariants)
        (Representation.Coinvariants.mk
          (valuationInertiaTateRepresentation V L hc K p) x) = 0 ↔
      ∃ n : ℕ, (p : ℤ_[p]) ^ n • x ∈
        Representation.Coinvariants.ker (valuationInertiaTateRepresentation V L hc K p) := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hx
    change (a : ℤ_[p]) • Representation.Coinvariants.mk
      (valuationInertiaTateRepresentation V L hc K p) x = 0 at ha
    have ha0 : (a : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero a
    rw [PadicInt.unitCoeff_spec ha0, mul_smul] at ha
    refine ⟨(a : ℤ_[p]).valuation, ?_⟩
    apply (Representation.Coinvariants.mk_eq_zero
      (valuationInertiaTateRepresentation V L hc K p)).mp
    rw [map_smul]
    exact (PadicInt.unitCoeff ha0).isUnit.smul_eq_zero.mp ha
  · rintro ⟨n, hn⟩
    have hp0 : (p : ℤ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    refine ⟨⟨(p : ℤ_[p]) ^ n,
      mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hp0)⟩, ?_⟩
    change (p : ℤ_[p]) ^ n • Representation.Coinvariants.mk
      (valuationInertiaTateRepresentation V L hc K p) x = 0
    rw [← map_smul]
    exact (Representation.Coinvariants.mk_eq_zero
      (valuationInertiaTateRepresentation V L hc K p)).mpr hn

omit [Algebra R V] [IsScalarTower R V Ω] [IsProper f]
  [Algebra R (IsLocalRing.ResidueField V)]
  [IsScalarTower R V (IsLocalRing.ResidueField V)] in
/-- Every inertia-invariant linear map from the actual generic Tate module
to a torsion-free module factors uniquely through the two canonical quotients.
The factor is constructed from the coinvariant and submodule quotient maps. -/
theorem valuationInertiaTorsionFree_existsUnique_lift
    {N : Type*} [AddCommGroup N] [Module ℤ_[p] N] [Module.IsTorsionFree ℤ_[p] N]
    (F : TateModule p (L.AlgPoints hc Ω) →ₗ[ℤ_[p]] N)
    (hF : ∀ d : V.inertiaSubgroup K,
      F.comp (valuationInertiaTateRepresentation V L hc K p d) = F) :
    ∃! F' : ((valuationInertiaTateRepresentation V L hc K p).Coinvariants ⧸
        Submodule.torsion ℤ_[p]
          (valuationInertiaTateRepresentation V L hc K p).Coinvariants) →ₗ[ℤ_[p]] N,
      ∀ x : TateModule p (L.AlgPoints hc Ω),
        F' (Submodule.mkQ _ (Representation.Coinvariants.mk
          (valuationInertiaTateRepresentation V L hc K p) x)) = F x := by
  let F₀ := Representation.Coinvariants.lift
    (valuationInertiaTateRepresentation V L hc K p) F hF
  have hkill : Submodule.torsion ℤ_[p]
      (valuationInertiaTateRepresentation V L hc K p).Coinvariants ≤ LinearMap.ker F₀ := by
    intro x hx
    obtain ⟨a, ha⟩ := hx
    change (a : ℤ_[p]) • x = 0 at ha
    change F₀ x = 0
    apply (smul_eq_zero_iff_right (nonZeroDivisors.coe_ne_zero a)).mp
    rw [← map_smul, ha, map_zero]
  let F₁ := Submodule.liftQ _ F₀ hkill
  refine ⟨F₁, ?_, ?_⟩
  · intro x
    rfl
  · intro F₂ hF₂
    apply LinearMap.ext
    intro z
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective
      (valuationInertiaTateRepresentation V L hc K p) c
    exact hF₂ x

/-- Actual reduction on torsion-free inertia coinvariants is surjective at
all primes. Good reduction supplies lifts at each finite torsion level;
invertibility of the indexing prime is not required. -/
theorem valuationInertiaTorsionFreeSpecialization_surjective
    [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    Function.Surjective (valuationInertiaTorsionFreeSpecialization V L hc K p) := by
  intro y
  obtain ⟨x, hx⟩ := valuationTateSpecialization_surjective V L hc hA p y
  refine ⟨Submodule.mkQ _ (Representation.Coinvariants.mk
    (valuationInertiaTateRepresentation V L hc K p) x), ?_⟩
  rw [valuationInertiaTorsionFreeSpecialization_mk]
  exact hx

/-- A generic Tate sequence whose prime-power multiple is an inertia relation
specializes to zero, including at the residue characteristic. -/
theorem valuationTateSpecialization_eq_zero_of_prime_pow_mem_inertia
    (n : ℕ) (x : TateModule p (L.AlgPoints hc Ω))
    (hx : (p : ℤ_[p]) ^ n • x ∈
      Representation.Coinvariants.ker (valuationInertiaTateRepresentation V L hc K p)) :
    valuationTateSpecialization V L hc p x = 0 := by
  have hq := (valuationInertiaTorsionFree_mk_eq_zero_iff V L hc K p x).mpr ⟨n, hx⟩
  have h := congrArg (valuationInertiaTorsionFreeSpecialization V L hc K p) hq
  simpa only [valuationInertiaTorsionFreeSpecialization_mk, map_zero] using h

/-- At an invertible prime, the actual inertia action on the Tate module
is trivial, since specialization is injective and inertia preserves it. -/
theorem valuationInertiaTateRepresentation_eq_one_of_isUnit [IsLocalRing R]
    (hp : IsUnit (p : R)) (d : V.inertiaSubgroup K) :
    valuationInertiaTateRepresentation V L hc K p d = 1 := by
  apply LinearMap.ext
  intro x
  apply valuationTateSpecialization_injective_of_isUnit V L hc p hp
  exact LinearMap.congr_fun (valuationTateSpecialization_inertia V L hc K p d) x

/-- The actual specialization from inertia coinvariants is bijective at an
invertible prime for an abelian scheme over a Noetherian local base. -/
theorem valuationInertiaCoinvariantSpecialization_bijective_of_isUnit
    [IsLocalRing R] [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (hp : IsUnit (p : R)) :
    Function.Bijective (valuationInertiaCoinvariantSpecialization V L hc K p) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective
      (valuationInertiaTateRepresentation V L hc K p) a
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective
      (valuationInertiaTateRepresentation V L hc K p) b
    apply congrArg (Representation.Coinvariants.mk
      (valuationInertiaTateRepresentation V L hc K p))
    exact valuationTateSpecialization_injective_of_isUnit V L hc p hp hab
  · intro y
    obtain ⟨x, hx⟩ := valuationTateSpecialization_surjective V L hc hA p y
    exact ⟨Representation.Coinvariants.mk
      (valuationInertiaTateRepresentation V L hc K p) x, hx⟩

/-- Quotienting the actual inertia coinvariants by their torsion retains the
prime-to-residue Tate comparison, with the original specialization map. -/
theorem valuationInertiaTorsionFreeSpecialization_bijective_of_isUnit
    [IsLocalRing R] [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (hp : IsUnit (p : R)) :
    Function.Bijective (valuationInertiaTorsionFreeSpecialization V L hc K p) := by
  have h := valuationInertiaCoinvariantSpecialization_bijective_of_isUnit V L hc K p hA hp
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ b
    exact congrArg (Submodule.mkQ _) (h.injective hab)
  · intro y
    obtain ⟨x, hx⟩ := h.surjective y
    exact ⟨Submodule.mkQ _ x, hx⟩

/-- The integral prime-to-residue comparison from actual torsion-free inertia
coinvariants to the Tate module of the special fibre. -/
def valuationInertiaTorsionFreeEquivOfIsUnit
    [IsLocalRing R] [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (hp : IsUnit (p : R)) :
    ((valuationInertiaTateRepresentation V L hc K p).Coinvariants ⧸
      Submodule.torsion ℤ_[p]
        (valuationInertiaTateRepresentation V L hc K p).Coinvariants) ≃ₗ[ℤ_[p]]
      TateModule p (L.AlgPoints hc (IsLocalRing.ResidueField V)) :=
  LinearEquiv.ofBijective (valuationInertiaTorsionFreeSpecialization V L hc K p)
    (valuationInertiaTorsionFreeSpecialization_bijective_of_isUnit V L hc K p hA hp)

/-- The comparison sends an original generic Tate sequence to its actual
specialization, after the two canonical quotient maps. -/
@[simp] theorem valuationInertiaTorsionFreeEquivOfIsUnit_mk
    [IsLocalRing R] [IsNoetherianRing R] [IsAlgClosed Ω]
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (hp : IsUnit (p : R)) (x : TateModule p (L.AlgPoints hc Ω)) :
    valuationInertiaTorsionFreeEquivOfIsUnit V L hc K p hA hp
        (Submodule.mkQ _ (Representation.Coinvariants.mk
          (valuationInertiaTateRepresentation V L hc K p) x)) =
      valuationTateSpecialization V L hc p x := rfl

end Inertia

section Naturality

variable {J' : Scheme.{u}} {f' : J' ⟶ Spec (CommRingCat.of R)} [IsProper f']
  (L' : RelativeGroupLaw R f') (hc' : L'.IsCommutative)
  (φ : SchemeHomOver f f') (hφ : L.IsHom L' φ)

/-- Specialization commutes with an actual morphism of proper commutative
group schemes, because its generic image has the same unique integral extension. -/
theorem valuationSpecialization_postcomp (x : L.AlgPoints hc Ω) :
    valuationSpecialization V L' hc' (AlgPoints.postcomp φ hφ Ω x) =
      AlgPoints.postcomp φ hφ (IsLocalRing.ResidueField V)
        (valuationSpecialization V L hc x) := by
  obtain ⟨z, rfl⟩ := (valuationPointMap_bijective V L hc).surjective x
  rw [AlgPoints.postcomp_map (L := L) (hc := hc) (L' := L') (hc' := hc') φ hφ
      (IsScalarTower.toAlgHom R V Ω) z,
    valuationSpecialization_map, valuationSpecialization_map]
  exact (AlgPoints.postcomp_map (L := L) (hc := hc) (L' := L') (hc' := hc') φ hφ
    (IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V)) z).symm

/-- The original generic and residue Tate maps induced by a group-scheme
morphism form a commuting square with actual specialization. -/
theorem valuationTateSpecialization_postcomp (p : ℕ) [Fact p.Prime] :
    (valuationTateSpecialization V L' hc' p).comp
        (TateModule.map p (AlgPoints.postcomp φ hφ Ω)) =
      (TateModule.map p (AlgPoints.postcomp φ hφ (IsLocalRing.ResidueField V))).comp
        (valuationTateSpecialization V L hc p) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact valuationSpecialization_postcomp V L hc L' hc' φ hφ
    ((x : ℕ → L.AlgPoints hc Ω) n)

end Naturality

end GoodReductionJacobian.RelativeGroupLaw
