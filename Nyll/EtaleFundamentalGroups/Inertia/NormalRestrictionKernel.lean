/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Normal.Basic

/-!
# The exact field subgroup of a normal restriction kernel

Restriction to the prescribed normal field has kernel equal to the image
of its absolute automorphisms under restriction of scalars.
-/

namespace EtaleFundamentalGroups.Inertia

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] [Normal F L]

/-- The literal normal-restriction kernel is the scalar-restriction image. -/
theorem normalRestriction_ker_eq_restrictScalars_range :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L).ker =
      (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).range := by
  ext σ
  constructor
  · intro hσ
    let τ : Gal(Ω/L) :=
      { σ with
        commutes' := fun x =>
          (σ.restrictNormal_commutes L x).symm.trans
            (congrArg (algebraMap L Ω)
              (AlgEquiv.ext_iff.mp (MonoidHom.mem_ker.mp hσ) x)) }
    exact ⟨τ, AlgEquiv.ext (fun _ => rfl)⟩
  · rintro ⟨τ, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L Ω).injective
    calc
      algebraMap L Ω ((τ.restrictScalars F).restrictNormal L x) =
          (τ.restrictScalars F) (algebraMap L Ω x) :=
        (τ.restrictScalars F).restrictNormal_commutes L x
      _ = algebraMap L Ω x := τ.commutes x

end EtaleFundamentalGroups.Inertia
