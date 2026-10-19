/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFiniteLabels
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois invariance of the original quadratic boundary-coordinate field

The field is the original adjoin of the selected scalar radical and selected
boundary roots. Every ambient automorphism sends each generator to that same
generator or its negative. The field, roots, and labels are never replaced.
-/
noncomputable section

namespace AnabelianGeometry.WeightFiltration

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
variable {ι : Type} (β : κˣ) (r : ι → κ)
variable (a : kˣ) (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a)
variable (v : ι → k) (hr : ∀ i, r i ^ 2 = algebraMap k κ (v i))

include hβ hr

/-- Every ambient automorphism preserves the original finite-coordinate field. -/
theorem quadraticBoundaryCoordinateField_aut_mem
    (α : Gal(κ/k)) {x : κ} (hx : x ∈ quadraticBoundaryCoordinateField k κ β r) :
    α x ∈ quadraticBoundaryCoordinateField k κ β r := by
  have hle : quadraticBoundaryCoordinateField k κ β r ≤
      (quadraticBoundaryCoordinateField k κ β r).comap α.toAlgHom := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    change α z ∈ quadraticBoundaryCoordinateField k κ β r
    rcases Set.mem_insert_iff.mp hz with h | ⟨i, rfl⟩
    · rw [h]
      exact quadraticScalarField_le_quadraticBoundaryCoordinateField k κ β r
        (quadraticScalarField_conjugate_mem k κ a β hβ α)
    · apply square_root_mem_quadraticBoundaryCoordinateField k κ β r v hr i (α (r i))
      rw [← map_pow, hr i, α.commutes]
  exact hle hx

/-- Invariance is an equality, with inverse supplied by the same automorphism. -/
theorem quadraticBoundaryCoordinateField_map_eq (α : Gal(κ/k)) :
    (quadraticBoundaryCoordinateField k κ β r).map α.toAlgHom =
      quadraticBoundaryCoordinateField k κ β r := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact quadraticBoundaryCoordinateField_aut_mem k κ β r a hβ v hr α hy
  · intro x hx
    exact ⟨α.symm x,
      quadraticBoundaryCoordinateField_aut_mem k κ β r a hβ v hr α.symm hx,
      α.apply_symm_apply x⟩

/-- Restrict the actual automorphism to the unchanged coordinate field.
The inclusion into the fixed ambient field commutes definitionally. -/
def quadraticBoundaryCoordinateField_restrictAut (α : Gal(κ/k)) :
    Gal((quadraticBoundaryCoordinateField k κ β r)/k) where
  toFun x := ⟨α x.val,
    quadraticBoundaryCoordinateField_aut_mem k κ β r a hβ v hr α x.property⟩
  invFun x := ⟨α.symm x.val,
    quadraticBoundaryCoordinateField_aut_mem k κ β r a hβ v hr α.symm x.property⟩
  left_inv x := Subtype.ext (α.symm_apply_apply x.val)
  right_inv x := Subtype.ext (α.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul α x.val y.val)
  map_add' x y := Subtype.ext (map_add α x.val y.val)
  commutes' c := Subtype.ext (α.commutes c)

@[simp] theorem quadraticBoundaryCoordinateField_restrictAut_coe
    (α : Gal(κ/k)) (x : quadraticBoundaryCoordinateField k κ β r) :
    (quadraticBoundaryCoordinateField_restrictAut k κ β r a hβ v hr α x : κ) =
      α (x : κ) := rfl

/-- The original adjoin is normal inside the already fixed algebraic closure.
No normal-closure replacement is made. -/
theorem quadraticBoundaryCoordinateField_normal [IsAlgClosure k κ] :
    Normal k (quadraticBoundaryCoordinateField k κ β r) := by
  apply IntermediateField.normal_iff_forall_map_le'.mpr
  intro α
  exact (quadraticBoundaryCoordinateField_map_eq k κ β r a hβ v hr α).le

/-- In characteristic zero the same field is Galois over the original base. -/
theorem quadraticBoundaryCoordinateField_isGalois [CharZero k] [IsAlgClosure k κ] :
    IsGalois k (quadraticBoundaryCoordinateField k κ β r) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable
    k (quadraticBoundaryCoordinateField k κ β r) κ
  to_normal := quadraticBoundaryCoordinateField_normal k κ β r a hβ v hr

/-- The actual finite-base fixing subgroup is normal, without changing fields. -/
theorem quadraticBoundaryCoordinateField_fixingSubgroup_normal
    [CharZero k] [IsAlgClosure k κ] :
    (quadraticBoundaryCoordinateField k κ β r).fixingSubgroup.Normal := by
  let : IsGalois k (quadraticBoundaryCoordinateField k κ β r) :=
    quadraticBoundaryCoordinateField_isGalois k κ β r a hβ v hr
  infer_instance

/-- An arbitrary coefficient-comparison conjugator cannot change membership
in the original finite-base fixing subgroup. The proof uses the literal
ambient automorphisms and the original field membership. -/
theorem quadraticBoundaryCoordinateField_conj_mem_fixingSubgroup_iff
    (α σ : Gal(κ/k)) :
    α * σ * α⁻¹ ∈ (quadraticBoundaryCoordinateField k κ β r).fixingSubgroup ↔
      σ ∈ (quadraticBoundaryCoordinateField k κ β r).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have he := h (α x)
      (quadraticBoundaryCoordinateField_aut_mem k κ β r a hβ v hr α hx)
    change α (σ (α.symm (α x))) = α x at he
    rw [α.symm_apply_apply] at he
    exact α.injective he
  · intro h x hx
    have he := h (α.symm x)
      (quadraticBoundaryCoordinateField_aut_mem k κ β r a hβ v hr α.symm hx)
    change α (σ (α.symm x)) = x
    rw [he, α.apply_symm_apply]

end AnabelianGeometry.WeightFiltration
