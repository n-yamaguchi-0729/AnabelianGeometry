/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdditiveCoefficientAction
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.EndomorphismPullbackComposition
public import Nyll.EtaleCohomology.Classical.PullbackIdentity
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Pullback on the original classical adic cohomology groups

Actual constant-coefficient pullback commutes with coefficient reduction and
with the scalar endomorphisms defining the original ℓ-adic module structures.
It therefore acts on the existing compatible families and, by scalar extension,
on the existing rational cohomology. The original groups and tensor products
are retained throughout.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace EtaleCohomology.Classical

open EtaleFundamentalGroups.Cohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Actual pullback on the original finite-level groups is linear for the
existing action of the ℓ-adic integers. -/
def finiteLevelCohomologyPullback (n i : ℕ) :
    finiteLevelCohomology Y ℓ n i →ₗ[ℤ_[ℓ]] finiteLevelCohomology X ℓ n i where
  toAddHom := (constantCohomologyPullback f (ellPowerCoefficients ℓ n) i).toAddHom
  map_smul' r x := by
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
    let a : ellPowerCoefficients.{u} ℓ n ⟶ ellPowerCoefficients.{u} ℓ n :=
      AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) r)
    change constantCohomologyPullback f (ellPowerCoefficients ℓ n) i
        (Sheaf.H.map ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map a) i x) =
      Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map a) i
        (constantCohomologyPullback f (ellPowerCoefficients ℓ n) i x)
    exact (constantCohomologyPullback_naturality f
      (ellPowerCoefficients ℓ n) (ellPowerCoefficients ℓ n) a i x).symm

/-- The finite-level operator is the original inverse-image map followed by
the canonical constant-sheaf comparison. -/
theorem finiteLevelCohomologyPullback_apply (n i : ℕ)
    (x : finiteLevelCohomology Y ℓ n i) :
    finiteLevelCohomologyPullback ℓ f n i x =
      Sheaf.H.map ((etaleAbelianPullbackConstantIso f).hom.app
        (ellPowerCoefficients ℓ n)) i
        (etaleAbelianCohomologyPullbackMap f
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
            (ellPowerCoefficients ℓ n)) i x) := rfl

/-- Original coefficient reduction commutes with actual pullback. -/
theorem finiteLevelCohomologyPullback_reduction (n i : ℕ)
    (x : finiteLevelCohomology Y ℓ (n + 1) i) :
    finiteLevelCohomologyPullback ℓ f n i (finiteLevelReduction Y ℓ n i x) =
      finiteLevelReduction X ℓ n i (finiteLevelCohomologyPullback ℓ f (n + 1) i x) :=
  (constantCohomologyPullback_naturality f
    (ellPowerCoefficients ℓ (n + 1)) (ellPowerCoefficients ℓ n)
    (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) i x).symm

/-- Pullback on the existing integral ℓ-adic compatible families. -/
def ellAdicCohomologyPullback (i : ℕ) :
    ellAdicCohomology Y ℓ i →ₗ[ℤ_[ℓ]] ellAdicCohomology X ℓ i where
  toFun a := ⟨fun n => finiteLevelCohomologyPullback ℓ f n i (a.val n), fun n =>
    (finiteLevelCohomologyPullback_reduction ℓ f n i (a.val (n + 1))).symm.trans
      (congrArg (finiteLevelCohomologyPullback ℓ f n i) (a.property n))⟩
  map_add' a b := Subtype.ext (funext fun n =>
    (finiteLevelCohomologyPullback ℓ f n i).map_add (a.val n) (b.val n))
  map_smul' r a := Subtype.ext (funext fun n =>
    (finiteLevelCohomologyPullback ℓ f n i).map_smul r (a.val n))

/-- Every projection retains the original finite-level pullback. -/
theorem ellAdicProjection_pullback (i n : ℕ) (a : ellAdicCohomology Y ℓ i) :
    ellAdicProjection X ℓ i n (ellAdicCohomologyPullback ℓ f i a) =
      finiteLevelCohomologyPullback ℓ f n i (ellAdicProjection Y ℓ i n a) := rfl

/-- Scalar extension of the original integral pullback to the original
classical rational ℓ-adic cohomology. -/
def rationalEllAdicCohomologyPullback (i : ℕ) :
    rationalEllAdicCohomology ℓ Y i →ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ X i :=
  (ellAdicCohomologyPullback ℓ f i).baseChange ℚ_[ℓ]

/-- On pure tensors, rational pullback is the original integral pullback. -/
theorem rationalEllAdicCohomologyPullback_tmul (i : ℕ) (q : ℚ_[ℓ])
    (a : ellAdicCohomology Y ℓ i) :
    rationalEllAdicCohomologyPullback ℓ f i (q ⊗ₜ[ℤ_[ℓ]] a) =
      q ⊗ₜ[ℤ_[ℓ]] ellAdicCohomologyPullback ℓ f i a := rfl

variable (X)

/-- Identity pullback on the actual finite coefficient groups. -/
theorem finiteLevelCohomologyPullback_id (n i : ℕ) :
    finiteLevelCohomologyPullback ℓ (𝟙 X) n i = 1 := by
  apply LinearMap.ext
  intro x
  exact etaleAbelianConstantCohomologyPullbackMap_id X (ellPowerCoefficients ℓ n) i x

/-- Identity pullback on the original integral inverse limit. -/
theorem ellAdicCohomologyPullback_id (i : ℕ) :
    ellAdicCohomologyPullback ℓ (𝟙 X) i = 1 := by
  apply LinearMap.ext
  intro a
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact LinearMap.congr_fun (finiteLevelCohomologyPullback_id ℓ X n i) (a.val n)

/-- Identity pullback after the existing rational scalar extension. -/
theorem rationalEllAdicCohomologyPullback_id (i : ℕ) :
    rationalEllAdicCohomologyPullback ℓ (𝟙 X) i = 1 := by
  change (ellAdicCohomologyPullback ℓ (𝟙 X) i).baseChange ℚ_[ℓ] = 1
  rw [ellAdicCohomologyPullback_id]
  exact LinearMap.baseChange_one (R := ℤ_[ℓ]) (M := ellAdicCohomology X ℓ i)

variable {X} (g h : X ⟶ X)

/-- Existing composition of constant-coefficient inverse image acts on the
same finite-level groups used in the classical ℓ-adic construction. -/
theorem finiteLevelCohomologyPullback_comp_end (n i : ℕ) :
    finiteLevelCohomologyPullback ℓ (g ≫ h) n i =
      finiteLevelCohomologyPullback ℓ g n i * finiteLevelCohomologyPullback ℓ h n i := by
  apply LinearMap.ext
  intro x
  change finiteLevelCohomologyPullback ℓ (g ≫ h) n i x =
    finiteLevelCohomologyPullback ℓ g n i (finiteLevelCohomologyPullback ℓ h n i x)
  simp only [finiteLevelCohomologyPullback_apply]
  exact etaleAbelianConstantCohomologyEndomorphismPullbackMap_comp g h
    (ellPowerCoefficients ℓ n) i x

/-- Integral pullback composes on the original compatible families. -/
theorem ellAdicCohomologyPullback_comp_end (i : ℕ) :
    ellAdicCohomologyPullback ℓ (g ≫ h) i =
      ellAdicCohomologyPullback ℓ g i * ellAdicCohomologyPullback ℓ h i := by
  apply LinearMap.ext
  intro a
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact LinearMap.congr_fun (finiteLevelCohomologyPullback_comp_end ℓ g h n i) (a.val n)

/-- Rational pullback retains the original composition law. -/
theorem rationalEllAdicCohomologyPullback_comp_end (i : ℕ) :
    rationalEllAdicCohomologyPullback ℓ (g ≫ h) i =
      rationalEllAdicCohomologyPullback ℓ g i * rationalEllAdicCohomologyPullback ℓ h i := by
  change (ellAdicCohomologyPullback ℓ (g ≫ h) i).baseChange ℚ_[ℓ] =
    (ellAdicCohomologyPullback ℓ g i).baseChange ℚ_[ℓ] *
      (ellAdicCohomologyPullback ℓ h i).baseChange ℚ_[ℓ]
  rw [ellAdicCohomologyPullback_comp_end]
  exact LinearMap.baseChange_mul _ _

/-- Every power of finite-level pullback is pullback by the original
scheme endomorphism power. -/
theorem finiteLevelCohomologyPullback_pow (n i m : ℕ) :
    (finiteLevelCohomologyPullback ℓ g n i) ^ m =
      finiteLevelCohomologyPullback ℓ ((End.of g) ^ m).asHom n i := by
  induction m with
  | zero => exact (finiteLevelCohomologyPullback_id ℓ X n i).symm
  | succ m ih =>
      rw [pow_succ', pow_succ, End.mul_asHom,
        finiteLevelCohomologyPullback_comp_end, ih]

/-- Every power of integral pullback retains its original geometric map. -/
theorem ellAdicCohomologyPullback_pow (i m : ℕ) :
    (ellAdicCohomologyPullback ℓ g i) ^ m =
      ellAdicCohomologyPullback ℓ ((End.of g) ^ m).asHom i := by
  induction m with
  | zero => exact (ellAdicCohomologyPullback_id ℓ X i).symm
  | succ m ih =>
      rw [pow_succ', pow_succ, End.mul_asHom, ellAdicCohomologyPullback_comp_end, ih]

/-- Every integral power commutes with every original finite projection. -/
theorem ellAdicProjection_pullback_pow (i n m : ℕ) (a : ellAdicCohomology X ℓ i) :
    ellAdicProjection X ℓ i n (((ellAdicCohomologyPullback ℓ g i) ^ m) a) =
      ((finiteLevelCohomologyPullback ℓ g n i) ^ m) (ellAdicProjection X ℓ i n a) := by
  have hL := congrArg (fun t : Module.End ℤ_[ℓ] (ellAdicCohomology X ℓ i) =>
    ellAdicProjection X ℓ i n (t a)) (ellAdicCohomologyPullback_pow ℓ g i m)
  have hF := congrArg (fun t : Module.End ℤ_[ℓ] (finiteLevelCohomology X ℓ n i) =>
    t (ellAdicProjection X ℓ i n a)) (finiteLevelCohomologyPullback_pow ℓ g n i m)
  exact hL.trans hF.symm

/-- Rational powers are the scalar extensions of the same integral powers. -/
theorem rationalEllAdicCohomologyPullback_pow (i m : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ g i) ^ m =
      rationalEllAdicCohomologyPullback ℓ ((End.of g) ^ m).asHom i := by
  exact (LinearMap.baseChange_pow (R := ℤ_[ℓ]) (A := ℚ_[ℓ])
    (M := ellAdicCohomology X ℓ i) (ellAdicCohomologyPullback ℓ g i) m).symm.trans
      (congrArg (fun t : Module.End ℤ_[ℓ] (ellAdicCohomology X ℓ i) =>
        t.baseChange ℚ_[ℓ]) (ellAdicCohomologyPullback_pow ℓ g i m))

/-- Rational powers act on pure tensors through the original integral powers. -/
theorem rationalEllAdicCohomologyPullback_pow_tmul (i m : ℕ) (q : ℚ_[ℓ])
    (a : ellAdicCohomology X ℓ i) :
    ((rationalEllAdicCohomologyPullback ℓ g i) ^ m) (q ⊗ₜ[ℤ_[ℓ]] a) =
      q ⊗ₜ[ℤ_[ℓ]] ((ellAdicCohomologyPullback ℓ g i) ^ m) a := by
  have hp := LinearMap.baseChange_pow (R := ℤ_[ℓ]) (A := ℚ_[ℓ])
    (M := ellAdicCohomology X ℓ i) (ellAdicCohomologyPullback ℓ g i) m
  exact congrArg (fun t : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ X i) =>
    t (q ⊗ₜ[ℤ_[ℓ]] a)) hp.symm

end EtaleCohomology.Classical
