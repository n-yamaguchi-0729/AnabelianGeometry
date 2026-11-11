/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.RationalAdic

/-!
# Finite-level arithmetic of the actual adic scalar action

The original coefficient action is multiplication by the corresponding
finite approximation. Additivity of the constant-sheaf and cohomology
functors identifies its derived action with the same integer multiple.

-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology.Classical

/-- Scalar multiplication on actual finite-level cohomology is multiplication
by the original finite approximation of the adic scalar. -/
theorem finiteLevel_smul_eq_appr_nsmul
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (n i : ℕ)
    (c : ℤ_[ℓ]) (a : finiteLevelCohomology X ℓ n i) :
    c • a = c.appr (n + 1) • a := by
  let A := ellPowerCoefficients.{u} ℓ n
  let : Module ℤ_[ℓ] A := ellPowerPadicModule ℓ n
  let F := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH X.smallEtaleTopology i
  have hscalar : AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] A c) =
      c.appr (n + 1) • 𝟙 A := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply ULift.ext
    change (c.appr (n + 1) : ZMod (ℓ ^ (n + 1))) * x.down =
      c.appr (n + 1) • x.down
    exact (nsmul_eq_mul _ _).symm
  change F.map (AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] A c)) a = c.appr (n + 1) • a
  rw [hscalar, F.map_nsmul, F.map_id]
  rfl

end EtaleCohomology.Classical
