/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusFixedSchemeDegree
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IEqProper
public import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
public import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree

/-!
# The actual Frobenius fixed Cartier divisor and its degree

The graph--diagonal ideal defines a relative effective Cartier divisor on the
original geometric curve. Its degree in the existing relative-divisor type is
the number of points over the finite extension. The full ideal is retained;
no intersection-number definition replaces the scheme or its multiplicities.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

namespace AlgebraicGeometry.RelEffCartierDiv

universe u

/-- A finite closed subscheme of a proper scheme over a field is an existing
relative divisor, of its actual finite-flat rank, with its full kernel ideal. -/
theorem exists_I_eq_comap_ker_of_isFinite
    {K : Type u} [Field K] {C Z : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsProper c]
    (i : Z ⟶ C) [IsClosedImmersion i] [IsFinite (i ≫ c)] :
    ∃ D : RelEffCartierDiv c ((i ≫ c).finrank (IsLocalRing.closedPoint K))
        (𝟙 (Spec (.of K))),
      D.I = i.ker.comap (pullback.fst c (𝟙 (Spec (.of K)))) := by
  let p := pullback.fst c (𝟙 (Spec (.of K)))
  let j := i ≫ inv p
  have hj : j ≫ p = i := by
    simp only [j, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (i ≫ inv p))
  have hker : i.ker.comap p = j.ker := ker_comap_eq_ker p i j hj
  have hfinite := (i ≫ c).finite_preimage_singleton (IsLocalRing.closedPoint K)
  have huniv : (Set.univ : Set Z).Finite :=
    hfinite.subset fun _ _ => Subsingleton.elim _ _
  have hsupport : (j.ker.support :
      Set (pullback c (𝟙 (Spec (.of K))) : Scheme.{u})).Finite := by
    rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq]
    exact (huniv.image j).subset (by
      rintro _ ⟨z, rfl⟩
      exact ⟨z, Set.mem_univ _, rfl⟩)
  obtain ⟨r, D, hD⟩ := exists_I_eq_of_isProper_of_support_finite
    (𝟙 (Spec (.of K))) j.ker hsupport
  have hsame : D.I.subschemeι.ker = j.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD]
  let e : Z ⟶ D.I.subscheme := IsClosedImmersion.lift D.I.subschemeι j hsame.le
  have : IsIso e := IsClosedImmersion.isIso_lift D.I.subschemeι j hsame
  have he : e ≫ D.I.subschemeι = j := IsClosedImmersion.lift_fac _ _ _
  have : IsFinite (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (.of K)))) := D.isFinite
  have : Flat (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (.of K)))) := D.flat
  have hcomp : e ≫ (D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (.of K)))) = i ≫ c := by
    rw [← Category.assoc, he, ← Category.comp_id (pullback.snd c (𝟙 (Spec (.of K)))),
      ← pullback.condition, ← Category.assoc]
    exact congrArg (fun a => a ≫ c) hj
  have hr : r = (i ≫ c).finrank (IsLocalRing.closedPoint K) := by
    rw [← hcomp, Scheme.Hom.finrank_comp_left_of_isIso]
    exact (D.finrank_eq _).symm
  subst r
  exact ⟨D, hD.trans hker.symm⟩

end AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicGeometry.Scheme

universe u

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    (m : ℕ) [NeZero m]

/-- The original graph--diagonal ideal is an invertible Cartier ideal, and
its divisor in the existing degree-indexed type has exactly the finite-field
point count as degree. This statement includes the empty fixed locus. -/
theorem constantBaseChangeFrobenius_exists_fixedCartierDivisor_degree_pointCount :
    let E := LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω m
    let Y := pullback (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)
    let g := pullback.snd (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)
    let v := ((End.of (constantBaseChangeFrobenius k Ω X)) ^ m).asHom
    let Γ := graphOver g v (constantBaseChangeFrobenius_pow_snd k Ω X m)
    let Δ := graphOver g (𝟙 Y) (Category.id_comp g)
    let I := Δ.ker.comap Γ
    ∃ D : RelEffCartierDiv g
        (Nat.card (SchemeHomOver (Spec.algebraMap k E) (X ↘ Spec (.of k))))
        (𝟙 (Spec (.of Ω))),
      D.I = I.comap (pullback.fst g (𝟙 (Spec (.of Ω)))) ∧ I.IsInvertible := by
  intro E Y g v Γ Δ I
  have : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} h => SmoothOfRelativeDimension 1 h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} h => SmoothOfRelativeDimension 1 h)
      (IsPullback.of_hasPullback (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)) inferInstance
  have : IsClosedImmersion Δ := isClosedImmersion_graphOver g (𝟙 Y) (Category.id_comp g)
  let i := equalizer.ι v (𝟙 Y)
  have : IsClosedImmersion i := by
    change IsClosedImmersion (equalizer.ι v (𝟙 Y))
    rw [← (isPullback_equalizer_graphOver g v
      (constantBaseChangeFrobenius_pow_snd k Ω X m)).isoPullback_hom_fst]
    infer_instance
  have hgeometric := constantBaseChangeFrobenius_globalFixedScheme_finite_etale
    k X Ω m (Nat.pos_of_ne_zero (NeZero.ne m))
  have : IsFinite (i ≫ g) := hgeometric.1
  have hex := RelEffCartierDiv.exists_I_eq_comap_ker_of_isFinite g i
  have hdegree := constantBaseChangeFrobenius_fixedScheme_finrank_eq_pointCount k Ω X m
  rw [hdegree] at hex
  obtain ⟨D, hD⟩ := hex
  have hI : I = i.ker := diagonalIdeal_comap_graphOver_eq_equalizer_ker g v
    (constantBaseChangeFrobenius_pow_snd k Ω X m)
  have hD' : D.I = I.comap (pullback.fst g (𝟙 (Spec (.of Ω)))) := hD.trans
    (congrArg (fun J : Y.IdealSheafData => J.comap
      (pullback.fst g (𝟙 (Spec (.of Ω))))) hI.symm)
  refine ⟨D, hD', ?_⟩
  apply Scheme.IdealSheafData.isInvertible_of_isInvertible_comap
    (pullback.fst g (𝟙 (Spec (.of Ω)))) I
  rw [← hD']
  exact D.isInvertible_I

end AlgebraicGeometry.Scheme
