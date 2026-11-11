/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.GenericSourceAbelianKernel
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationClosureInertia
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceClosureComparison
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceClosure
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
public import Nyll.GaloisCohomology.Topology.GaloisRestrictionScalars
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Topology.Homeomorph.Lemmas
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# The actual abelian kernel for an arbitrary generic field source

A dominant preimmersion from a field spectrum supplies its specified
isomorphism with the original function field. That isomorphism and the
actual separable-closure comparison transport the original generic
Galois map and every normalization-stalk inertia group.

Consequently the proved canonical kernel theorem gives the kernel in the
supplied field itself. Both the generic-source map and all local groups
retain their literal coefficient maps. No kernel or inertia comparison is
an assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem subgroup_map_topologicalClosure
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) (S : Subgroup G) :
    S.topologicalClosure.map f.toMonoidHom =
      (S.map f.toMonoidHom).topologicalClosure := by
  apply le_antisymm
  · have h : S.topologicalClosure ≤
        (S.map f.toMonoidHom).topologicalClosure.comap f.toMonoidHom := by
      apply Subgroup.topologicalClosure_minimal
      · intro g hg
        exact (Subgroup.le_topologicalClosure _) ⟨g, hg, rfl⟩
      · exact (Subgroup.isClosed_topologicalClosure _).preimage f.continuous_toFun
    rintro z ⟨g, hg, rfl⟩
    exact h hg
  · apply Subgroup.topologicalClosure_minimal
    · rintro z ⟨g, hg, rfl⟩
      exact ⟨g, (Subgroup.le_topologicalClosure S) hg, rfl⟩
    · exact ((Subgroup.isClosed_topologicalClosure S).isCompact.image
        f.continuous_toFun).isClosed

variable {X : Scheme.{u}} [IsIntegral X] {F : Type u} [Field F]
  (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
  (Ω : Type u) [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

/-- Full inertia at all actual normalization primes of the original stalk,
using its specified inclusion in the supplied generic field. -/
def sourceAbsoluteStalkInertiaImage (x : X) : Subgroup Gal(Ω/F) := by
  let A := X.presheaf.stalk x
  let : Algebra A F := genericFieldSourceStalkAlgebra p x
  have : IsFractionRing A F := genericFieldSourceStalk_isFractionRing p x
  let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
    IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
  exact ⨆ Q : MaximalSpectrum (integralClosure A Ω), Q.asIdeal.inertia Gal(Ω/F)

/-- The actual generic-field isomorphism and its separable-closure
extension give a topological isomorphism of the original absolute groups. -/
def genericSourceAbsoluteGaloisEquiv :
    Gal(SeparableClosure X.functionField/X.functionField) ≃ₜ* Gal(Ω/F) := by
  let : Algebra X.functionField F := genericFieldSourceFunctionFieldAlgebra p
  let : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
  have : IsScalarTower X.functionField F Ω := genericFieldSourceClosure_isScalarTower p Ω
  have : IsSepClosure X.functionField Ω := genericFieldSourceClosure_isSepClosure p Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed F
  let e := IsSepClosure.equiv X.functionField (SeparableClosure X.functionField) Ω
  let s := AlgEquiv.extendScalarsHomOfSurjective
    (R := X.functionField) (S := F) (A := Ω) (genericFieldSourceRingEquiv p).surjective
  have hs : Continuous s.symm :=
    InfiniteGalois.restrictScalarsHom_continuous X.functionField F Ω
  let e₀ : Gal(SeparableClosure X.functionField/X.functionField) ≃ₜ*
      Gal(Ω/X.functionField) :=
    { toMulEquiv := AlgEquiv.autCongr e
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_continuous e
      continuous_invFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_symm_continuous e }
  let e₁ : Gal(Ω/X.functionField) ≃ₜ* Gal(Ω/F) :=
    { toMulEquiv := s
      continuous_toFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2 (f := s.symm.toEquiv) hs
      continuous_invFun := hs }
  exact e₀.trans e₁

/-- The comparison retains literal conjugation on the supplied ambient
field; changing the base scalar only changes the fixed-coefficient proof. -/
theorem genericSourceAbsoluteGaloisEquiv_apply
    (σ : Gal(SeparableClosure X.functionField/X.functionField)) (z : Ω) :
    let _ : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
    let _ : IsSepClosure X.functionField Ω := genericFieldSourceClosure_isSepClosure p Ω
    genericSourceAbsoluteGaloisEquiv p Ω σ z =
      (IsSepClosure.equiv X.functionField (SeparableClosure X.functionField) Ω)
        (σ ((IsSepClosure.equiv X.functionField
          (SeparableClosure X.functionField) Ω).symm z)) := rfl

/-- The original supplied generic-point map has exactly the transported
canonical kernel. The comparison is proved on actual geometric points. -/
theorem genericSourceAbsoluteGaloisEquiv_ker :
    let _ : IsSepClosed Ω := IsSepClosure.sep_closed F
    ((fieldSourceAbsoluteGaloisHom X.functionField (SeparableClosure X.functionField)
      (X.fromSpecStalk (genericPoint X))).toMonoidHom.ker).map
        (genericSourceAbsoluteGaloisEquiv p Ω).toMonoidHom =
      (fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom.ker := by
  intro sepClosed
  let : Algebra X.functionField F := genericFieldSourceFunctionFieldAlgebra p
  let : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
  have : IsScalarTower X.functionField F Ω := genericFieldSourceClosure_isScalarTower p Ω
  have : IsSepClosure X.functionField Ω := genericFieldSourceClosure_isSepClosure p Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed F
  let e := IsSepClosure.equiv X.functionField (SeparableClosure X.functionField) Ω
  let E := genericSourceAbsoluteGaloisEquiv p Ω
  let q₀ := fieldSourceAbsoluteGaloisHom X.functionField (SeparableClosure X.functionField)
    (X.fromSpecStalk (genericPoint X))
  let q := fieldSourceAbsoluteGaloisHom F Ω p
  have hpoint : (ξ F Ω ≫ p) ≫ 𝟙 X =
      ξ X.functionField Ω ≫ X.fromSpecStalk (genericPoint X) := by
    rw [Category.comp_id, ← genericFieldSourceIso_hom_fromSpecStalk p,
      ← Category.assoc]
    change (ξ F Ω ≫ Spec.map
      (CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom)) ≫
        X.fromSpecStalk (genericPoint X) = _
    rw [← Spec.map_comp]
    rfl
  let EId : FiniteEtale X ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤
      (Iso.refl X)
  have : (pullback (𝟙 X)).IsEquivalence := EId.isEquivalence_functor
  let T := (fundamentalGroupEquivOfPullbackEquivalence (𝟙 X) (ξ F Ω ≫ p)).trans
    (continuousConjAut (eqToIso (congrArg fiber hpoint)))
  let T₀ := fieldSourceClosureGroupEquiv (X.fromSpecStalk (genericPoint X)) e
  have hmap (σ : Gal(SeparableClosure X.functionField/X.functionField)) :
      T (q (E σ)) = T₀ (q₀ σ) := by
    have h := fieldSourceAbsoluteGaloisHom_naturality X.functionField F Ω
      (𝟙 X) p (X.fromSpecStalk (genericPoint X)) hpoint (E σ)
    have hσ : (E σ).restrictScalars X.functionField = AlgEquiv.autCongr e σ := by
      apply AlgEquiv.ext
      intro z
      rfl
    rw [hσ] at h
    exact h.trans
      (fieldSourceClosureGroupEquiv_galois (X.fromSpecStalk (genericPoint X)) e σ).symm
  apply Subgroup.ext
  intro τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    change q (E σ) = 1
    apply T.injective
    rw [map_one, hmap]
    change T₀ (q₀ σ) = 1
    rw [show q₀ σ = 1 from hσ, map_one]
  · intro hτ
    obtain ⟨σ, rfl⟩ := E.surjective τ
    refine ⟨σ, ?_, rfl⟩
    change q₀ σ = 1
    apply T₀.injective
    rw [map_one, ← hmap]
    change T (q (E σ)) = 1
    rw [show q (E σ) = 1 from hτ, map_one]

/-- The actual generic-field comparison carries every original stalk
inertia onto the full supplied-source stalk inertia. The normalization
prime is transported by the literal ambient-field equivalence. -/
theorem absoluteStalkInertiaImage_map_genericSource (x : X) :
    (absoluteStalkInertiaImage X x).map
        (genericSourceAbsoluteGaloisEquiv p Ω).toMonoidHom =
      sourceAbsoluteStalkInertiaImage p Ω x := by
  let : Algebra X.functionField F := genericFieldSourceFunctionFieldAlgebra p
  let : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
  have : IsScalarTower X.functionField F Ω := genericFieldSourceClosure_isScalarTower p Ω
  have : IsSepClosure X.functionField Ω := genericFieldSourceClosure_isSepClosure p Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed F
  let A := X.presheaf.stalk x
  let Ω₀ := SeparableClosure X.functionField
  let : Algebra A Ω₀ := X.stalkExtensionAlgebra x Ω₀
  have : IsScalarTower A X.functionField Ω₀ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A F := genericFieldSourceStalkAlgebra p x
  have : IsFractionRing A F := genericFieldSourceStalk_isFractionRing p x
  let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A X.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : MulSemiringAction Gal(Ω₀/X.functionField) (integralClosure A Ω₀) :=
    IsIntegralClosure.MulSemiringAction A X.functionField Ω₀ (integralClosure A Ω₀)
  let : MulSemiringAction Gal(Ω/X.functionField) (integralClosure A Ω) :=
    IsIntegralClosure.MulSemiringAction A X.functionField Ω (integralClosure A Ω)
  let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
    IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
  let e := IsSepClosure.equiv X.functionField Ω₀ Ω
  let eN := (e.restrictScalars A).mapIntegralClosure
  let s := AlgEquiv.extendScalarsHomOfSurjective
    (R := X.functionField) (S := F) (A := Ω) (genericFieldSourceRingEquiv p).surjective
  have haction (σ : Gal(Ω/X.functionField)) (a : integralClosure A Ω) :
      (s σ) • a = σ • a := by
    apply Subtype.ext
    exact (algebraMap_galRestrict_apply A (K := F) (L := Ω)
      (B := integralClosure A Ω) (s σ) a).trans
        (algebraMap_galRestrict_apply A (K := X.functionField) (L := Ω)
          (B := integralClosure A Ω) σ a).symm
  have hscalar (Q : Ideal (integralClosure A Ω)) :
      (Q.inertia Gal(Ω/X.functionField)).map s.toMonoidHom = Q.inertia Gal(Ω/F) := by
    apply Subgroup.ext
    intro τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩ a
      exact (congrArg (fun b : integralClosure A Ω => b - a ∈ Q)
        (haction σ a)).mpr (hσ a)
    · intro hτ
      obtain ⟨σ, rfl⟩ := s.surjective τ
      refine ⟨σ, ?_, rfl⟩
      intro a
      exact (congrArg (fun b : integralClosure A Ω => b - a ∈ Q)
        (haction σ a)).mp (hτ a)
  have hprime (Q : Ideal (integralClosure A Ω)) :
      ((Q.comap eN.toRingHom).inertia Gal(Ω₀/X.functionField)).map
          (genericSourceAbsoluteGaloisEquiv p Ω).toMonoidHom =
        Q.inertia Gal(Ω/F) := by
    change ((Q.comap eN.toRingHom).inertia Gal(Ω₀/X.functionField)).map
      (s.toMonoidHom.comp (AlgEquiv.autCongr e).toMonoidHom) = _
    rw [← Subgroup.map_map,
      normalizationInertia_map_autCongr A X.functionField Ω₀ Ω e Q, hscalar]
  change (⨆ Q : MaximalSpectrum (integralClosure A Ω₀),
    Q.asIdeal.inertia Gal(Ω₀/X.functionField)).map
      (genericSourceAbsoluteGaloisEquiv p Ω).toMonoidHom =
    ⨆ Q : MaximalSpectrum (integralClosure A Ω), Q.asIdeal.inertia Gal(Ω/F)
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro Q₀
    let Q : Ideal (integralClosure A Ω) := Q₀.asIdeal.comap eN.symm.toRingHom
    have : Q₀.asIdeal.IsMaximal := Q₀.isMaximal
    have hQ : Q.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective eN.symm.toRingHom eN.symm.surjective
    have hcontract : Q.comap eN.toRingHom = Q₀.asIdeal := by
      apply Ideal.ext
      intro a
      change eN.symm (eN a) ∈ Q₀.asIdeal ↔ a ∈ Q₀.asIdeal
      rw [eN.symm_apply_apply]
    have h := hprime Q
    rw [hcontract] at h
    rw [h]
    exact le_iSup
      (fun R : MaximalSpectrum (integralClosure A Ω) => R.asIdeal.inertia Gal(Ω/F))
      ⟨Q, hQ⟩
  · apply iSup_le
    intro Q
    have : Q.asIdeal.IsMaximal := Q.isMaximal
    have hQ : (Q.asIdeal.comap eN.toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective eN.toRingHom eN.surjective
    rw [← hprime Q.asIdeal]
    exact le_iSup
      (fun R : MaximalSpectrum (integralClosure A Ω₀) =>
        (R.asIdeal.inertia Gal(Ω₀/X.functionField)).map
          (genericSourceAbsoluteGaloisEquiv p Ω).toMonoidHom)
      ⟨Q.asIdeal.comap eN.toRingHom, hQ⟩

variable [IsNormalIntegral X]

/-- On the actual smooth curve, the kernel of its supplied generic-source
map has precisely the closed abelian subgroup generated by its original
closed-point normalization inertia groups. -/
theorem fieldSourceAbsoluteGaloisHom_ker_closedPoint_image
    {k : Type u} [Field k] (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] :
    let _ : IsSepClosed Ω := IsSepClosure.sep_closed F
    ((fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom.ker).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F)) =
      (⨆ x : closedPoints X, (sourceAbsoluteStalkInertiaImage p Ω x.val).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F))).topologicalClosure := by
  intro sepClosed
  let E := genericSourceAbsoluteGaloisEquiv p Ω
  let Eab := ProCGroups.Abelian.TopologicalAbelianization.congr E
  let a₀ := ProCGroups.Abelian.TopologicalAbelianization.mk
    Gal(SeparableClosure X.functionField/X.functionField)
  let a := ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F)
  have hsquare : a.comp E.toMonoidHom = Eab.toMonoidHom.comp a₀ := by
    apply MonoidHom.ext
    intro σ
    rfl
  rw [← genericSourceAbsoluteGaloisEquiv_ker p Ω, Subgroup.map_map]
  change ((fieldSourceAbsoluteGaloisHom X.functionField
    (SeparableClosure X.functionField) (X.fromSpecStalk (genericPoint X))).toMonoidHom.ker).map
      (a.comp E.toMonoidHom) = _
  rw [hsquare, ← Subgroup.map_map,
    canonicalFieldSourceAbsoluteGaloisHom_ker_closedPoint_image X c]
  have hclosure := subgroup_map_topologicalClosure
    (ContinuousMonoidHom.toContinuousMonoidHom Eab)
    (⨆ x : closedPoints X, (absoluteStalkInertiaImage X x.val).map a₀)
  apply hclosure.trans
  congr 1
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro x
  change ((absoluteStalkInertiaImage X x.val).map a₀).map Eab.toMonoidHom = _
  rw [Subgroup.map_map, ← hsquare, ← Subgroup.map_map,
    absoluteStalkInertiaImage_map_genericSource p Ω x.val]

end EtaleFundamentalGroups.Inertia
