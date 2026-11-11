/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Tsen.EtaleCohomologyOfTsen
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.EtaleTsenH2
public import Nyll.EtaleCohomology.Classical.SigmaCohomology
public import Nyll.EtaleCohomology.Classical.HigherDirectImageResolution
public import Nyll.EtaleCohomology.Classical.FieldHilbert90EtaleObjects
public import Nyll.EtaleCohomology.Classical.PushforwardH1Vanishing
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Basic

/-!
# Actual Tsen vanishing for higher direct images

The field-level Tsen theorem extends to all étale objects by finite étale
decomposition and then annihilates the actual higher direct images.
-/

@[expose] public section

noncomputable section

universe u
open AlgebraicGeometry CategoryTheory Limits
namespace AlgebraicCurve

/-- Actual bounded-torsion cohomology above degree one vanishes at
every étale object of the function-field site, not only its terminal object. -/
theorem fieldEtale_cohomology_eq_zero_at_etale_object_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (S : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u})
    (m : ℤ) (hm0 : m ≠ 0) (hm : m • 𝟙 S = 0)
    (n : ℕ) (V : (Spec (.of F)).Etale)
    (v : Sheaf.H'.{u} S (n + 2) V) : v = 0 := by
  refine EtaleCohomology.etaleCohomologyPresheaf_eq_zero_of_field_objects
    F S (n + 2) (by
  intro L instField a instFiniteEtale b
  let : Algebra F L := a.hom.toAlgebra
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hf : (algebraMap F L).FiniteEtale := by
    exact (IsFiniteEtale.SpecMap_iff).mp instFiniteEtale
  have hFL : Algebra.FiniteEtale F L :=
    RingHom.finiteEtale_algebraMap_iff.mp hf
  rw [Algebra.finiteEtale_iff] at hFL
  have : FiniteDimensional F L := hFL.2
  obtain ⟨y, hy, hyfin, _⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin L
  let R := EtaleCohomology.etaleRestriction (Spec.map a) AddCommGrpCat.{u}
  have hmR : m • 𝟙 (R.obj S) = 0 := by
    have he := congrArg (fun f : S ⟶ S => R.map f) hm
    rw [R.map_zsmul, R.map_id, R.map_zero] at he
    exact he
  let e := EtaleCohomology.etaleCohomologyPresheafRestrictionEquiv
    (Scheme.Etale.mk (Spec.map a)) S (n + 2)
  apply e.injective
  rw [e.map_zero]
  exact fieldEtale_cohomology_eq_zero_of_tsen K y hy hyfin
    (R.obj S) m hm0 hmR n (e b)) V v

/-- Tsen vanishing at every base-changed étale object annihilates the
actual higher direct images above degree one from the function field. -/
theorem fieldEtale_rightDerived_pushforward_isZero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {Y : Scheme.{u}} (f : Spec (.of F) ⟶ Y)
    (S : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u})
    (m : ℤ) (hm0 : m ≠ 0) (hm : m • 𝟙 S = 0) (n : ℕ) :
    IsZero (((EtaleCohomology.etaleAbelianPushforward f).rightDerived (n + 2)).obj S) :=
  EtaleCohomology.etaleRightDerivedPushforward_isZero_of_cohomologyPresheaf_eq_zero
    f S (n + 2) (fun V v =>
      fieldEtale_cohomology_eq_zero_at_etale_object_of_tsen K x hx hfin S m hm0 hm n V v)

/-- Actual Tsen vanishing for Gm holds at every étale object of the
function-field site, including infinite disjoint unions. -/
theorem fieldEtale_units_H2_eq_zero_at_etale_object_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (V : (Spec (.of F)).Etale)
    (v : Sheaf.H'.{u} (EtaleCohomology.etaleMultiplicativeGroupSheaf
      (Spec (.of F))) 2 V) : v = 0 := by
  refine EtaleCohomology.etaleCohomologyPresheaf_eq_zero_of_field_objects
    F (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of F))) 2 (by
  intro L instField a instFiniteEtale b
  let : Algebra F L := a.hom.toAlgebra
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hf : (algebraMap F L).FiniteEtale := by
    exact (IsFiniteEtale.SpecMap_iff).mp instFiniteEtale
  have hFL : Algebra.FiniteEtale F L :=
    RingHom.finiteEtale_algebraMap_iff.mp hf
  rw [Algebra.finiteEtale_iff] at hFL
  have : FiniteDimensional F L := hFL.2
  obtain ⟨y, hy, hyfin, _⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin L
  let er := EtaleCohomology.etaleCohomologyPresheafRestrictionEquiv
    (Scheme.Etale.mk (Spec.map a))
      (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of F))) 2
  let ec := (Sheaf.functorH (Spec (.of L)).smallEtaleTopology 2).mapIso
    (EtaleCohomology.etaleRestrictionMultiplicativeGroupIso (Spec.map a))
  let e := er.trans ec.addCommGroupIsoToAddEquiv
  apply e.injective
  rw [e.map_zero]
  exact AlgebraicCurve.etaleMultiplicativeGroup_H2_eq_zero_of_tsen
    K y hy hyfin (e b)) V v

/-- The actual direct image of function-field units has zero degree-two
cohomology on every target étale object. The proof combines geometric
Hilbert 90, Tsen, and the proved low-degree direct-image comparison. -/
theorem fieldEtale_pushforward_units_H2_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {Y : Scheme.{u}} (f : Spec (.of F) ⟶ Y) (V : Y.Etale)
    (v : Sheaf.H'.{u}
      ((EtaleCohomology.etaleAbelianPushforward f).obj
        (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of F)))) 2 V) :
    v = 0 := by
  exact EtaleCohomology.etalePushforward_cohomologyPresheaf_two_eq_zero f
    (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (.of F))) V
    (fun W a => EtaleCohomology.etaleMultiplicativeGroup_H1_eq_zero_at_etale_object_of_field
      F W a)
    (fun a => fieldEtale_units_H2_eq_zero_at_etale_object_of_tsen K x hx hfin
      ((EtaleCohomology.etaleBaseChange f).obj V) a) v

end AlgebraicCurve
