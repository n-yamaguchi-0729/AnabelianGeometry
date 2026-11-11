/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafOfModules
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafTensor

/-!
# Comparing tensor products of module presheaves with tensor-sheaf sections

The comparison uses the same local tensor-section map, restriction maps and
base-morphism scalar structures as the two input module presheaves.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct Opposite

namespace AlgebraicGeometry.OModulePresheaf.TensorComparison

variable {R : Type u} [CommRing R] {V : Scheme.{u}}
  (π : V ⟶ Spec (.of R)) (M N : V.Modules)

/-- The actual linear comparison from tensor products of sections to tensor-sheaf sections. -/
abbrev cmp (U : V.Opens) : Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) →ₗ[Γ(V, U)] Γ(M ⊗ N, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U)

/-- The comparison sends a pure tensor to its actual tensor section. -/
theorem cmp_tmul (U : V.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    cmp M N U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  exact TensorProduct.lift.tmul (f' := Scheme.Modules.tensorSectionsBilin M N U) s t

/-- The existing semilinear restriction map on the tensor product of sections. -/
def resTw {U U' : V.Opens} (h : U ≤ U') :
    Γ(M, U') ⊗[Γ(V, U')] Γ(N, U') →ₛₗ[(V.presheaf.map (homOfLE h).op).hom] Γ(M, U) ⊗[Γ(V, U)] Γ(N,
      U) :=
  (ofModules π M).tensorResₛₗ (ofModules π N) h

/-- Restriction of a pure tensor uses the two original section restrictions. -/
theorem resTw_tmul {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) (y : Γ(N, U')) :
    resTw π M N h (x ⊗ₜ y) = M.presheaf.map (homOfLE h).op x ⊗ₜ N.presheaf.map (homOfLE h).op y :=
      rfl

/-- The comparison commutes with the semilinear tensor restriction. -/
theorem cmp_resTw {U U' : V.Opens} (h : U ≤ U') (t : Γ(M, U') ⊗[Γ(V, U')] Γ(N, U')) :
    cmp M N U (resTw π M N h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [resTw_tmul, cmp_tmul, cmp_tmul]
    exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The comparison commutes with restriction in the actual twisted presheaf. -/
theorem cmp_res {U U' : V.Opens} (h : U ≤ U') (t : ((ofModules π M).twist N).obj U') :
    cmp M N U (((ofModules π M).twist N).res h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U'
      t) :=
  cmp_resTw π M N h t

/-- The affine-section morphism from the twist to sections of the tensor-product sheaf. -/
def cmpHom : AffHom ((ofModules π M).twist N) (ofModules π (M ⊗ N)) where
  app U :=
    { toFun := cmp M N U.1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r t => map_smul (cmp M N U.1)
        ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t }
  app_smul U a t := map_smul (cmp M N U.1) a t
  naturality h := LinearMap.ext fun t => cmp_res π M N h t

/-- The affine comparison has the original tensor-section comparison as its value. -/
theorem cmpHom_app (U : V.affineOpens) (t : ((ofModules π M).twist N).obj U.1) :
    (cmpHom π M N).app U t = cmp M N U.1 t := rfl

end AlgebraicGeometry.OModulePresheaf.TensorComparison

end
