/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Scalar approximation on the original finite coefficients

The original adic scalar action on finite étale cohomology is the action
of the corresponding integer approximation. This follows from equality
of the actual scalar endomorphisms of the original constant coefficients,
followed by the additive cohomology functor.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology.Classical

/-- At the actual finite coefficient level, an adic integer acts by its
integer approximation modulo the same prime power. -/
theorem finiteLevelCohomology_smul_eq_appr
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (n i : ℕ)
    (r : ℤ_[ℓ]) (a : finiteLevelCohomology X ℓ n i) :
    r • a = r.appr (n + 1) • a := by
  let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
  let H : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH X.smallEtaleTopology i
  have he : AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients ℓ n) r) =
      r.appr (n + 1) • 𝟙 (ellPowerCoefficients ℓ n) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    apply ULift.down_injective
    change (r.appr (n + 1) : ZMod (ℓ ^ (n + 1))) * b.down =
      r.appr (n + 1) • b.down
    rw [nsmul_eq_mul]
  change H.map (AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients ℓ n) r)) a =
    r.appr (n + 1) • a
  have hm : H.map (AddCommGrpCat.ofHom
      (smulAddHom ℤ_[ℓ] (ellPowerCoefficients ℓ n) r)) a =
        (r.appr (n + 1) • 𝟙 (H.obj (ellPowerCoefficients ℓ n))) a := by
    simpa only [Functor.map_nsmul, H.map_id] using
      congrArg (fun f : ellPowerCoefficients.{u} ℓ n ⟶ ellPowerCoefficients.{u} ℓ n =>
        H.map f a) he
  have hv : (r.appr (n + 1) • 𝟙 (H.obj (ellPowerCoefficients ℓ n))) a =
      r.appr (n + 1) • a := rfl
  exact hm.trans hv

end EtaleCohomology.Classical
