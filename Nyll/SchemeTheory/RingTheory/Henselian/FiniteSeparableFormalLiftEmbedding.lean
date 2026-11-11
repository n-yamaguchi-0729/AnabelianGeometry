/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Henselian.FormalSimpleRoot
public import Mathlib.FieldTheory.PrimitiveElement

/-! # Formal lifting with a prescribed residue embedding

For a finite separable extension, a formal deformation of the base embedding
into a third coefficient field has a unique lift with the prescribed residue
embedding. A primitive element and its separable minimal polynomial construct
the lift. Uniqueness then proves compatibility with actual field embeddings.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

variable {R F L : Type*} [Field R] [Field F] [Field L] [Algebra R F]
  [FiniteDimensional R F] [Algebra.IsSeparable R F]

/-- A formal deformation of a base embedding lifts uniquely to the given
finite separable extension, with its actual prescribed residue embedding
into a third field. No lift is assumed as input. -/
theorem existsUnique_formalLift_finiteSeparable_embedding
    (ι : F →+* L) (τ : R →+* PowerSeries L)
    (hτ : constantCoeff.comp τ = ι.comp (algebraMap R F)) :
    ∃! σ : F →+* PowerSeries L,
      σ.comp (algebraMap R F) = τ ∧ constantCoeff.comp σ = ι := by
  let pb := Field.powerBasisOfFiniteOfSeparable R F
  let p := minpoly R pb.gen
  have hp : p.Monic := minpoly.monic pb.isIntegral_gen
  have hmap : (p.map τ).map constantCoeff =
      (p.map (algebraMap R F)).map ι := by
    rw [Polynomial.map_map, hτ, Polynomial.map_map]
  have hroot₀ : (p.map (algebraMap R F)).eval pb.gen = 0 := by
    rw [Polynomial.eval_map]
    exact minpoly.aeval R pb.gen
  have hder₀ : (p.map (algebraMap R F)).derivative.eval pb.gen ≠ 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval_map]
    exact (Algebra.IsSeparable.isSeparable R pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval R pb.gen)
  have hroot : ((p.map τ).map constantCoeff).eval (ι pb.gen) = 0 := by
    rw [hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hroot₀, map_zero]
  have hder : ((p.map τ).map constantCoeff).derivative.eval (ι pb.gen) ≠ 0 := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact (map_ne_zero ι).mpr hder₀
  obtain ⟨A, hA, hUnique⟩ := existsUnique_monic_root_of_constantCoeff
    (p.map τ) (hp.map τ) (ι pb.gen) hroot hder
  let : Algebra R (PowerSeries L) := τ.toAlgebra
  let : Algebra R L := (ι.comp (algebraMap R F)).toAlgebra
  have hAeval : Polynomial.aeval A (minpoly R pb.gen) = 0 := by
    change Polynomial.eval₂ τ A p = 0
    simpa only [Polynomial.eval_map] using hA.1
  let φ : F →ₐ[R] PowerSeries L := pb.lift A hAeval
  let i : F →ₐ[R] L :=
    { toRingHom := ι
      commutes' := fun _ => rfl }
  let ρ : PowerSeries L →ₐ[R] L :=
    { toRingHom := constantCoeff
      commutes' := fun x => RingHom.congr_fun hτ x }
  have hρ : ρ.comp φ = i := by
    apply pb.algHom_ext
    change constantCoeff (φ pb.gen) = ι pb.gen
    rw [PowerBasis.lift_gen]
    exact hA.2
  refine ⟨φ.toRingHom, ⟨?_, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro x
    exact φ.commutes x
  · exact congrArg AlgHom.toRingHom hρ
  · intro σ hσ
    let ψ : F →ₐ[R] PowerSeries L :=
      { toRingHom := σ
        commutes' := fun x => RingHom.congr_fun hσ.1 x }
    have hψroot : (p.map τ).eval (ψ pb.gen) = 0 := by
      rw [Polynomial.eval_map]
      change Polynomial.aeval (ψ pb.gen) (minpoly R pb.gen) = 0
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have hψres : constantCoeff (ψ pb.gen) = ι pb.gen :=
      RingHom.congr_fun hσ.2 pb.gen
    have hψgen : ψ pb.gen = φ pb.gen := by
      rw [PowerBasis.lift_gen]
      exact hUnique (ψ pb.gen) ⟨hψroot, hψres⟩
    exact congrArg AlgHom.toRingHom (pb.algHom_ext hψgen)

/-- Formal lifts over the same base deformation commute with an actual
embedding of coefficient fields. Only the source extension must be finite
separable; the target formal lift is compared by its restriction and residue. -/
theorem formalLift_comp_embedding [Algebra R L]
    (τ : R →+* PowerSeries R)
    (σF : F →+* PowerSeries F) (σL : L →+* PowerSeries L)
    (ι : F →ₐ[R] L)
    (hF : σF.comp (algebraMap R F) = (map (algebraMap R F)).comp τ)
    (hF0 : constantCoeff.comp σF = RingHom.id F)
    (hL : σL.comp (algebraMap R L) = (map (algebraMap R L)).comp τ)
    (hL0 : constantCoeff.comp σL = RingHom.id L) :
    σL.comp ι.toRingHom = (map ι.toRingHom).comp σF := by
  have hi : ι.toRingHom.comp (algebraMap R F) = algebraMap R L := by
    apply RingHom.ext
    intro r
    exact ι.commutes r
  let τL : R →+* PowerSeries L := (map (algebraMap R L)).comp τ
  have hτL : constantCoeff.comp τL = ι.toRingHom.comp (algebraMap R F) := by
    change constantCoeff.comp ((map (algebraMap R L)).comp τ) = _
    rw [← hL, ← RingHom.comp_assoc, hL0, RingHom.id_comp, hi]
  obtain ⟨φ, _, hUnique⟩ :=
    existsUnique_formalLift_finiteSeparable_embedding ι.toRingHom τL hτL
  have hleft : (σL.comp ι.toRingHom).comp (algebraMap R F) = τL ∧
      constantCoeff.comp (σL.comp ι.toRingHom) = ι.toRingHom := by
    constructor
    · rw [RingHom.comp_assoc, hi, hL]
    · rw [← RingHom.comp_assoc, hL0, RingHom.id_comp]
  have hright : ((map ι.toRingHom).comp σF).comp (algebraMap R F) = τL ∧
      constantCoeff.comp ((map ι.toRingHom).comp σF) = ι.toRingHom := by
    constructor
    · rw [RingHom.comp_assoc, hF, ← RingHom.comp_assoc, ← PowerSeries.map_comp, hi]
    · apply RingHom.ext
      intro x
      change ι (constantCoeff (σF x)) = ι x
      exact congrArg ι (RingHom.congr_fun hF0 x)
  exact (hUnique (σL.comp ι.toRingHom) hleft).trans
    (hUnique ((map ι.toRingHom).comp σF) hright).symm

end PowerSeries
