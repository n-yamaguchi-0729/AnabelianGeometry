/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPushforward
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.HenselianLocal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Étale cohomology over separably closed fields

A separably closed field is strictly henselian. Exactness of global
sections on its small étale site therefore makes the constant integer
sheaf projective and kills every positive-degree `Sheaf.H`, in every
characteristic. The terminal-object comparison gives the same vanishing
for the cohomology presheaf. Closed pushforward then gives acyclicity
for sheaves supported at an algebraically closed point.

The strictly henselian vanishing theorem is Stacks Project, Lemma 59.55.1:
https://stacks.math.columbia.edu/tag/03QO.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
namespace EtaleCohomology

private theorem residueField_isSepClosed_of_field
    (K : Type u) [Field K] [IsSepClosed K] :
    IsSepClosed (IsLocalRing.ResidueField K) := by
  let e : K ≃+* IsLocalRing.ResidueField K :=
    RingEquiv.ofBijective (IsLocalRing.residue K)
      ⟨(IsLocalRing.residue K).injective, IsLocalRing.residue_surjective⟩
  constructor
  intro p hp
  have hs := (IsSepClosed.splits_of_separable
    (p.map e.symm.toRingHom) hp.map).map e.toRingHom
  have he : e.toRingHom.comp e.symm.toRingHom =
      RingHom.id (IsLocalRing.ResidueField K) :=
    RingEquiv.toRingHom_comp_symm_toRingHom e
  simpa only [Polynomial.map_map, he, Polynomial.map_id] using hs

/-- Every actual positive-degree cohomology class of an arbitrary abelian
sheaf over a separably closed field vanishes, in every characteristic. -/
theorem fieldSheafCohomology_eq_zero_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) (c : Sheaf.H.{u} F (n + 1)) : c = 0 := by
  have : IsSepClosed (IsLocalRing.ResidueField K) :=
    residueField_isSepClosed_of_field K
  have : Subsingleton (Sheaf.H.{u} F (n + 1)) :=
    etaleAbelianCohomology_succ_subsingleton_of_henselianLocalRing K F n
  exact Subsingleton.elim c 0

/-- The actual cohomology presheaf at the terminal étale object of an
algebraically closed field vanishes in every positive degree and every
characteristic. -/
theorem fieldCohomologyPresheaf_eq_zero_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ)
    (c : Sheaf.H'.{u} F (n + 1) (Scheme.Etale.mk (𝟙 (Spec (.of K))))) :
    c = 0 := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of K)))) :=
    MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) (Spec (.of K))
  let e := sheafCohomologyTerminalEquiv _ hT F (n + 1)
  exact (e.apply_symm_apply c).symm.trans
    ((congrArg e (fieldSheafCohomology_eq_zero_of_isSepClosed K F n (e.symm c))).trans
      e.map_zero)

/-- Actual derived global sheaf cohomology over an algebraically closed
field vanishes in every positive degree and every characteristic, for any
abelian sheaf. -/
theorem fieldSheafCohomology_eq_zero_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) (c : Sheaf.H.{u} F (n + 1)) : c = 0 :=
  fieldSheafCohomology_eq_zero_of_isSepClosed K F n c

/-- A sheaf supported by a closed algebraically closed
point in any characteristic is acyclic for actual positive-degree étale cohomology. -/
theorem closedPointPushforward_cohomology_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (i : Spec (.of K) ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) (c : Sheaf.H.{u} ((etaleAbelianPushforward i).obj F) (n + 1)) :
    c = 0 := by
  let e := etaleAbelianCohomologyClosedPushforwardEquiv i F (n + 1)
  apply e.injective
  rw [e.map_zero]
  exact fieldSheafCohomology_eq_zero_of_isAlgClosed K F n (e c)

end EtaleCohomology
