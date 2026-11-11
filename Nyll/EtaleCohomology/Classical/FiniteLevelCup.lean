/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.CupCoefficientChange
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic

/-!
# Cup products on the original finite-level cohomology

The existing constant-module comparison transports the native Yoneda cup
to the original finite abelian coefficient sheaves. The original reductions
preserve this product and its unit, including every finite level. These
equalities supply the compatible families needed for integral adic cup.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology.Classical

variable (X : Scheme.{u})

/-- The native constant regular module cohomology is the original finite
cohomology group, through the existing coefficient-forgetting comparison. -/
def finiteLevelConstantModuleEquiv (ℓ n i : ℕ) :
    etaleCohomology X (ULift.{u} (ZMod (ℓ ^ (n + 1))))
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{u} (ULift.{u} (ZMod (ℓ ^ (n + 1)))))).obj
            (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
              (ULift.{u} (ZMod (ℓ ^ (n + 1)))))) i ≃+
      finiteLevelCohomology X ℓ n i :=
  etaleConstantCohomologyForgetEquiv (ULift.{u} (ZMod (ℓ ^ (n + 1)))) (X := X)
    (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
      (ULift.{u} (ZMod (ℓ ^ (n + 1))))) i

/-- The original finite coefficient reduction, retaining its ring structure. -/
def ellPowerReductionRingHom (ℓ n : ℕ) :
    ULift.{u} (ZMod (ℓ ^ (n + 1 + 1))) →+* ULift.{u} (ZMod (ℓ ^ (n + 1))) where
  toFun := ellPowerReduction ℓ n
  map_zero' := (ellPowerReduction ℓ n).map_zero
  map_add' := (ellPowerReduction ℓ n).map_add
  map_one' := congrArg ULift.up
    (map_one (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))))
  map_mul' a b := congrArg ULift.up
    (map_mul (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
      (ZMod (ℓ ^ (n + 1)))) a.down b.down)

/-- The native module coefficient map is the original finite-level
cohomological reduction under the existing comparison. -/
theorem finiteLevelConstantModuleEquiv_reduction (ℓ n i : ℕ)
    (x : etaleCohomology X (ULift.{u} (ZMod (ℓ ^ (n + 1 + 1))))
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} (ZMod (ℓ ^ (n + 1 + 1)))))).obj
          (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1 + 1))))
            (ULift.{u} (ZMod (ℓ ^ (n + 1 + 1)))))) i) :
    finiteLevelConstantModuleEquiv X ℓ n i
        (etaleCohomologyCoefficientMap X (ellPowerReductionRingHom ℓ n) i x) =
      finiteLevelReduction X ℓ n i (finiteLevelConstantModuleEquiv X ℓ (n + 1) i x) :=
  etaleCohomologyCoefficientMap_forget X (ellPowerReductionRingHom ℓ n) i x

/-- The native cup product on the original finite-level groups. -/
def finiteLevelCup (ℓ n a b c : ℕ) (h : a + b = c) :
    finiteLevelCohomology X ℓ n a →+
      finiteLevelCohomology X ℓ n b →+ finiteLevelCohomology X ℓ n c := by
  let R := ULift.{u} (ZMod (ℓ ^ (n + 1)))
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let ea := finiteLevelConstantModuleEquiv X ℓ n a
  let eb := finiteLevelConstantModuleEquiv X ℓ n b
  let ec := finiteLevelConstantModuleEquiv X ℓ n c
  let p := etaleCohomologyCup X R C a b c h
  refine
    { toFun := fun x =>
        (ec.toAddMonoidHom.comp (p (ea.symm x)).toAddMonoidHom).comp eb.symm.toAddMonoidHom
      map_zero' := ?_
      map_add' := ?_ }
  · apply AddMonoidHom.ext
    intro y
    change ec (p (ea.symm 0) (eb.symm y)) = 0
    simp only [map_zero, LinearMap.zero_apply]
  · intro x y
    apply AddMonoidHom.ext
    intro z
    change ec (p (ea.symm (x + y)) (eb.symm z)) =
      ec (p (ea.symm x) (eb.symm z)) + ec (p (ea.symm y) (eb.symm z))
    rw [map_add, map_add, LinearMap.add_apply, map_add]

/-- The finite-level cup retains its native module-cohomology calculation. -/
theorem finiteLevelCup_apply (ℓ n a b c : ℕ) (h : a + b = c)
    (x : finiteLevelCohomology X ℓ n a) (y : finiteLevelCohomology X ℓ n b) :
    finiteLevelCup X ℓ n a b c h x y =
      finiteLevelConstantModuleEquiv X ℓ n c
        (etaleCohomologyCup X (ULift.{u} (ZMod (ℓ ^ (n + 1))))
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u} (ULift.{u} (ZMod (ℓ ^ (n + 1)))))).obj
              (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
                (ULift.{u} (ZMod (ℓ ^ (n + 1)))))) a b c h
          ((finiteLevelConstantModuleEquiv X ℓ n a).symm x)
          ((finiteLevelConstantModuleEquiv X ℓ n b).symm y)) := rfl

/-- The original reductions preserve the actual finite-level cup product. -/
theorem finiteLevelCup_reduction (ℓ n a b c : ℕ) (h : a + b = c)
    (x : finiteLevelCohomology X ℓ (n + 1) a)
    (y : finiteLevelCohomology X ℓ (n + 1) b) :
    finiteLevelReduction X ℓ n c (finiteLevelCup X ℓ (n + 1) a b c h x y) =
      finiteLevelCup X ℓ n a b c h
        (finiteLevelReduction X ℓ n a x) (finiteLevelReduction X ℓ n b y) := by
  let R := ULift.{u} (ZMod (ℓ ^ (n + 1 + 1)))
  let S := ULift.{u} (ZMod (ℓ ^ (n + 1)))
  let f : R →+* S := ellPowerReductionRingHom ℓ n
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CS := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)
  let ea := finiteLevelConstantModuleEquiv X ℓ (n + 1) a
  let eb := finiteLevelConstantModuleEquiv X ℓ (n + 1) b
  let da := finiteLevelConstantModuleEquiv X ℓ n a
  let db := finiteLevelConstantModuleEquiv X ℓ n b
  let dc := finiteLevelConstantModuleEquiv X ℓ n c
  have ha : da.symm (finiteLevelReduction X ℓ n a x) =
      etaleCohomologyCoefficientMap X f a (ea.symm x) := by
    apply da.injective
    rw [AddEquiv.apply_symm_apply]
    exact ((finiteLevelConstantModuleEquiv_reduction X ℓ n a (ea.symm x)).trans
      (congrArg (finiteLevelReduction X ℓ n a) (ea.apply_symm_apply x))).symm
  have hb : db.symm (finiteLevelReduction X ℓ n b y) =
      etaleCohomologyCoefficientMap X f b (eb.symm y) := by
    apply db.injective
    rw [AddEquiv.apply_symm_apply]
    exact ((finiteLevelConstantModuleEquiv_reduction X ℓ n b (eb.symm y)).trans
      (congrArg (finiteLevelReduction X ℓ n b) (eb.apply_symm_apply y))).symm
  calc
    _ = dc (etaleCohomologyCoefficientMap X f c
        (etaleCohomologyCup X R CR a b c h (ea.symm x) (eb.symm y))) :=
      (finiteLevelConstantModuleEquiv_reduction X ℓ n c
        (etaleCohomologyCup X R CR a b c h (ea.symm x) (eb.symm y))).symm
    _ = dc (etaleCohomologyCup X S CS a b c h
        (etaleCohomologyCoefficientMap X f a (ea.symm x))
        (etaleCohomologyCoefficientMap X f b (eb.symm y))) :=
      congrArg dc (etaleCohomologyCup_coefficientMap X f a b c h (ea.symm x) (eb.symm y))
    _ = _ := by
      rw [finiteLevelCup_apply, ha, hb]

/-- The original finite-level cup unit. -/
def finiteLevelCupUnit (ℓ n : ℕ) : finiteLevelCohomology X ℓ n 0 :=
  finiteLevelConstantModuleEquiv X ℓ n 0
    (etaleCohomologyCupUnit X (ULift.{u} (ZMod (ℓ ^ (n + 1)))))

/-- The original reductions preserve the finite-level cup unit. -/
theorem finiteLevelCupUnit_reduction (ℓ n : ℕ) :
    finiteLevelReduction X ℓ n 0 (finiteLevelCupUnit X ℓ (n + 1)) =
      finiteLevelCupUnit X ℓ n := by
  simp only [finiteLevelCupUnit, ← finiteLevelConstantModuleEquiv_reduction,
    etaleCohomologyCoefficientMap_unit]

/-- The original finite-level cup is associative. -/
theorem finiteLevelCup_assoc
    (ℓ n a b c ab bc abc : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (habc : a + b + c = abc)
    (x : finiteLevelCohomology X ℓ n a) (y : finiteLevelCohomology X ℓ n b)
    (z : finiteLevelCohomology X ℓ n c) :
    finiteLevelCup X ℓ n ab c abc (by omega) (finiteLevelCup X ℓ n a b ab hab x y) z =
      finiteLevelCup X ℓ n a bc abc (by omega) x (finiteLevelCup X ℓ n b c bc hbc y z) := by
  simp only [finiteLevelCup_apply, AddEquiv.symm_apply_apply]
  exact congrArg (finiteLevelConstantModuleEquiv X ℓ n abc)
    (etaleCohomologyCup_assoc X (ULift.{u} (ZMod (ℓ ^ (n + 1)))) _
      a b c ab bc abc hab hbc habc _ _ _)

/-- The finite-level unit acts on the left. -/
theorem finiteLevelCup_unit_left (ℓ n i : ℕ) (x : finiteLevelCohomology X ℓ n i) :
    finiteLevelCup X ℓ n 0 i i (zero_add i) (finiteLevelCupUnit X ℓ n) x = x := by
  simp only [finiteLevelCup_apply, finiteLevelCupUnit, AddEquiv.symm_apply_apply,
    etaleCohomologyCup_unit_left, AddEquiv.apply_symm_apply]

/-- The finite-level unit acts on the right. -/
theorem finiteLevelCup_unit_right (ℓ n i : ℕ) (x : finiteLevelCohomology X ℓ n i) :
    finiteLevelCup X ℓ n i 0 i (add_zero i) x (finiteLevelCupUnit X ℓ n) = x := by
  simp only [finiteLevelCup_apply, finiteLevelCupUnit, AddEquiv.symm_apply_apply,
    etaleCohomologyCup_unit_right, AddEquiv.apply_symm_apply]

end EtaleCohomology.Classical
