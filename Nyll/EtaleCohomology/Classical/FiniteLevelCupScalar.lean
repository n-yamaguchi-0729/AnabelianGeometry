/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdditiveCoefficientAction
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.Algebra.Module.End
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The original adic scalar action is bilinear for finite-level cup

The constant-module comparison carries scalar endomorphisms to the actual
constant abelian scalar maps. Applying this calculation to the original
reduction from the adic integers proves bilinearity without replacing any
of the coefficient module structures.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology.Classical

private theorem constantSheaf_map_smul_id
    (X : Scheme.{u}) (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (r : R) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (r • 𝟙 M) =
      r • 𝟙 ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  let K := constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) terminalIsTerminal
  let η := adj.unit.app M
  apply (adj.homEquiv M (K.obj M)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change η ≫ (K.map (r • 𝟙 M)).hom.app (op (⊤_ X.Etale)) =
    η ≫ (r • 𝟙 (K.obj M)).hom.app (op (⊤_ X.Etale))
  calc
    _ = (r • 𝟙 M) ≫ η := (adj.unit.naturality (r • 𝟙 M)).symm
    _ = _ := by
      ext x
      change η (r • x) = r • η x
      exact η.hom.map_smul r x

private theorem constantModuleForget_smul
    (X : Scheme.{u}) (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (r : R) (i : ℕ)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) i) :
    etaleConstantCohomologyForgetEquiv R (X := X) M i (r • x) =
      Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom (smulAddHom R M r))) i
        (etaleConstantCohomologyForgetEquiv R (X := X) M i x) := by
  let U := forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let K := constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let d := (etaleConstantModuleForgetIso X R).app M
  let s : M ⟶ M := r • 𝟙 M
  let t := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom (smulAddHom R M r))
  have hn : coefficientAction (K.obj M) r ≫ d.hom = d.hom ≫ t := by
    have h := (etaleConstantModuleForgetIso X R).hom.naturality s
    change U.map (K.map (r • 𝟙 M)) ≫ d.hom = d.hom ≫ t at h
    rw [constantSheaf_map_smul_id] at h
    exact h
  change Sheaf.H.{u} (U.obj (K.obj M)) i at x
  change Sheaf.H.map d.hom i (Sheaf.H.map (coefficientAction (K.obj M) r) i x) =
    Sheaf.H.map t i (Sheaf.H.map d.hom i x)
  exact (Sheaf.H.map_comp_apply (coefficientAction (K.obj M) r) d.hom x).symm.trans
    ((congrArg (fun z : U.obj (K.obj M) ⟶
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) =>
          Sheaf.H.map z i x) hn).trans (Sheaf.H.map_comp_apply d.hom t x))

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The native finite-level comparison carries multiplication by the
actual residue of an adic integer to the original adic scalar action. -/
theorem finiteLevelConstantModuleEquiv_smul (n i : ℕ) (r : ℤ_[ℓ])
    (x : etaleCohomology X (ULift.{u} (ZMod (ℓ ^ (n + 1))))
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} (ZMod (ℓ ^ (n + 1)))))).obj
          (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
            (ULift.{u} (ZMod (ℓ ^ (n + 1)))))) i) :
    finiteLevelConstantModuleEquiv X ℓ n i
        (ULift.up (PadicInt.toZModPow (n + 1) r) • x) =
      r • finiteLevelConstantModuleEquiv X ℓ n i x := by
  let R := ULift.{u} (ZMod (ℓ ^ (n + 1)))
  let M := ModuleCat.of R R
  let s : R := ULift.up (PadicInt.toZModPow (n + 1) r)
  let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
  have hscalar : (AddCommGrpCat.ofHom (smulAddHom R R s)) =
      AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) r) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    rfl
  change finiteLevelConstantModuleEquiv X ℓ n i (s • x) =
    Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) r))) i
        (finiteLevelConstantModuleEquiv X ℓ n i x)
  rw [← hscalar]
  exact constantModuleForget_smul X R M s i x

private theorem finiteLevelConstantModuleEquiv_symm_smul
    (n i : ℕ) (r : ℤ_[ℓ]) (x : finiteLevelCohomology X ℓ n i) :
    (finiteLevelConstantModuleEquiv X ℓ n i).symm (r • x) =
      ULift.up (PadicInt.toZModPow (n + 1) r) •
        (finiteLevelConstantModuleEquiv X ℓ n i).symm x := by
  let e := finiteLevelConstantModuleEquiv X ℓ n i
  apply e.injective
  rw [AddEquiv.apply_symm_apply, finiteLevelConstantModuleEquiv_smul,
    AddEquiv.apply_symm_apply]

/-- Finite-level cup is linear in its first variable for the original
action of the adic integers. -/
theorem finiteLevelCup_smul_left (n a b c : ℕ) (h : a + b = c)
    (r : ℤ_[ℓ]) (x : finiteLevelCohomology X ℓ n a)
    (y : finiteLevelCohomology X ℓ n b) :
    finiteLevelCup X ℓ n a b c h (r • x) y =
      r • finiteLevelCup X ℓ n a b c h x y := by
  simp only [finiteLevelCup_apply, finiteLevelConstantModuleEquiv_symm_smul,
    map_smul, LinearMap.smul_apply, finiteLevelConstantModuleEquiv_smul]

/-- Finite-level cup is linear in its second variable for the original
action of the adic integers. -/
theorem finiteLevelCup_smul_right (n a b c : ℕ) (h : a + b = c)
    (r : ℤ_[ℓ]) (x : finiteLevelCohomology X ℓ n a)
    (y : finiteLevelCohomology X ℓ n b) :
    finiteLevelCup X ℓ n a b c h x (r • y) =
      r • finiteLevelCup X ℓ n a b c h x y := by
  simp only [finiteLevelCup_apply, finiteLevelConstantModuleEquiv_symm_smul,
    map_smul, finiteLevelConstantModuleEquiv_smul]

end EtaleCohomology.Classical
