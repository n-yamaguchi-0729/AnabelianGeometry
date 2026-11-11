/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldGaloisDescent
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Hilbert 90 for actual etale sheaf extensions over a field

A lift over a finite Galois field extension of a Galois-invariant quotient
section can be corrected to an invariant lift when the kernel is the actual
unit sheaf. The correction is obtained from its actual difference cocycle,
the proved equivariance of unit sections, and Noether's Hilbert 90.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

/-- Hilbert 90 gives an actual section primitive for every unit-sheaf
cocycle, using the proved equivariance with field units. -/
theorem exists_fieldGalois_units_cocycle_primitive
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c : Gal(L/K) → (etaleMultiplicativeGroupSheaf (Spec (.of K))).obj.obj
      (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L)))))
    (hcoc : ∀ σ τ, c (σ * τ) =
      (fieldGaloisSheafAction K L (etaleMultiplicativeGroupSheaf (Spec (.of K))) σ).asIso.hom
        (c τ) + c σ) :
    ∃ a, ∀ σ : Gal(L/K),
      (fieldGaloisSheafAction K L
        (etaleMultiplicativeGroupSheaf (Spec (.of K))) σ).asIso.hom a - a =
        c σ := by
  let X := Spec (.of K)
  let V := (finiteEtaleInclusion X).obj (FiniteEtale.mk (ξ K L))
  let A := etaleMultiplicativeGroupSheaf X
  let ρA := fieldGaloisSheafAction K L A
  let U : A.obj.obj (op V) ≃+ Additive Lˣ :=
    etaleMultiplicativeGroupSpecSectionsEquiv X (.of L) (ξ K L)
  let b : Gal(L/K) → Lˣ := fun σ => (U (c σ)).toMul
  have hunits (σ : Gal(L/K)) (u : Lˣ) : Units.map σ.toMonoidHom u = σ • u := by
    apply Units.ext
    rfl
  have hb : groupCohomology.IsMulCocycle₁ b := by
    intro σ τ
    change (U (c (σ * τ))).toMul = σ • (U (c τ)).toMul * (U (c σ)).toMul
    rw [hcoc, U.map_add]
    change (U ((ρA σ).asIso.hom (c τ))).toMul * (U (c σ)).toMul = _
    have hn := congrArg Additive.toMul (fieldGaloisSheafAction_units K L σ (c τ))
    change (U ((ρA σ).asIso.hom (c τ))).toMul = Units.map σ.toMonoidHom (U (c τ)).toMul at hn
    rw [hn, hunits]
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units b hb
  let a : A.obj.obj (op V) := U.symm (Additive.ofMul β)
  have ha (σ : Gal(L/K)) : (ρA σ).asIso.hom a = c σ + a := by
    apply U.injective
    rw [U.map_add]
    have hn := fieldGaloisSheafAction_units K L σ a
    change U ((ρA σ).asIso.hom a) = Additive.ofMul (Units.map σ.toMonoidHom (U a).toMul) at hn
    rw [hn]
    have hua : U a = Additive.ofMul β := U.apply_symm_apply _
    rw [hua]
    apply Additive.toMul.injective
    change Units.map σ.toMonoidHom β = b σ * β
    rw [hunits]
    exact (div_mul_cancel (σ • β) β).symm.trans
      (congrArg (fun z : Lˣ => z * β) (hβ σ))
  exact ⟨a, fun σ => (sub_eq_iff_eq_add).mpr (ha σ)⟩

/-- Hilbert 90 corrects a local lift in an actual short exact sequence with
unit-sheaf kernel to a Galois-invariant lift of the same quotient section. -/
theorem exists_fieldGalois_invariant_lift
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf (Spec (.of K)) ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (e : B.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
      (FiniteEtale.mk (ξ K L)))))
    (he : ∀ σ : Gal(L/K),
      (fieldGaloisSheafAction K L Q σ).asIso.hom
        (p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
          (FiniteEtale.mk (ξ K L)))) e) =
        p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
          (FiniteEtale.mk (ξ K L)))) e) :
    ∃ e' : B.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
        (FiniteEtale.mk (ξ K L)))),
      p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
        (FiniteEtale.mk (ξ K L)))) e' =
          p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
            (FiniteEtale.mk (ξ K L)))) e ∧
      ∀ σ : Gal(L/K), (fieldGaloisSheafAction K L B σ).asIso.hom e' = e' := by
  exact exists_fieldGalois_invariant_lift_of_cocycle_primitives K L i p hz hS
    (exists_fieldGalois_units_cocycle_primitive K L) e he

/-- Over any field, global sections of an actual short
exact sequence with unit-sheaf kernel surject onto quotient sections.
A finite Galois local lift is corrected by Hilbert 90 and then descended. -/
theorem exists_section_lift_of_units_kernel_of_field
    (K : Type u) [Field K]
    {B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf (Spec (.of K)) ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (q : Q.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) :
    ∃ b : B.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))),
      p.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) b = q := by
  exact exists_section_lift_of_fieldGalois_cocycle_primitives K i p hz hS
    (fun L _ _ _ _ => exists_fieldGalois_units_cocycle_primitive K L) q

/-- The actual derived etale H1 of Gm over any field
vanishes. Its extension representative is split using the proved geometric
Galois descent and Hilbert 90, not an assumed comparison with Galois H1. -/
theorem etaleMultiplicativeGroup_H1_eq_zero_of_field
    (K : Type u) [Field K]
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 1) : a = 0 := by
  exact etaleH1_eq_zero_of_fieldGalois_cocycle_primitives K
    (etaleMultiplicativeGroupSheaf (Spec (.of K)))
    (fun L _ _ _ _ => exists_fieldGalois_units_cocycle_primitive K L) a

end EtaleCohomology
