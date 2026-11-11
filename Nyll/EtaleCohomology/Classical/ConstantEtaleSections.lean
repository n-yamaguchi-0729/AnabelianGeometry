/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianUnderlying
public import Nyll.EtaleCohomology.Sites.ConnectedConstants
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.ModuleRestriction
public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Nyll.SchemeTheory.Etale.OverField.Decomposition
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Constant sheaf sections on étale objects over a field

The actual constant abelian sheaf is compared to the existing Type-valued
constant sheaf through `etaleConstantAbelianUnderlyingIso`. The Type-valued
sections on an étale object over a field are then computed by the existing
decomposition into spectra of fields and the existing section gluing for
`etaleSigma`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  Opposite TopologicalSpace

namespace EtaleCohomology

/-- Sections of a Type-valued sheaf on a disjoint union of étale objects are
equivalent to the family of their component restrictions. -/
def etaleSigmaSectionsEquiv {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale) (F : Sheaf X.smallEtaleTopology (Type u)) :
    F.obj.obj (op (etaleSigma U)) ≃ (∀ i, F.obj.obj (op (U i))) := by
  let e : F.obj.obj (op (etaleSigma U)) → (∀ i, F.obj.obj (op (U i))) :=
    fun s i => F.obj.map (etaleSigmaInj U i).op s
  apply Equiv.ofBijective e
  constructor
  · intro s t h
    apply etaleSigmaSection_ext U F
    intro i
    exact congrArg (fun p => p i) h
  · intro s
    refine ⟨etaleSigmaSection U F s, ?_⟩
    funext i
    exact etaleSigmaSection_restrict U F s i

/-- Additive sections on an étale disjoint union are the product of the
additive sections on its components. -/
def etaleSigmaAbelianSectionsAddEquiv {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (F.obj.obj (op (etaleSigma U))) ≃+ (∀ i, F.obj.obj (op (U i))) := by
  let h : (F.obj.obj (op (etaleSigma U))) →+ (∀ i, F.obj.obj (op (U i))) :=
    { toFun := fun s i => F.obj.map (etaleSigmaInj U i).op s
      map_zero' := by
        funext i
        exact (F.obj.map (etaleSigmaInj U i).op).hom.map_zero
      map_add' := by
        intro s t
        funext i
        exact (F.obj.map (etaleSigmaInj U i).op).hom.map_add s t
    }
  exact AddEquiv.ofBijective h
    (etaleSigmaSectionsEquiv U ((etaleAbelianUnderlying X).obj F)).bijective

/-- The sheafification unit induces restriction of the actual constant sheaf. -/
def fieldEtaleRestrictionConstantHom {U X : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (A : Type u) :
    (constantSheaf U.smallEtaleTopology (Type u)).obj A ⟶
      (etaleRestriction f (Type u)).obj
        ((constantSheaf X.smallEtaleTopology (Type u)).obj A) :=
  ⟨sheafifyLift U.smallEtaleTopology
    (whiskerLeft (etalePostcompose f).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)))
    ((etaleRestriction f (Type u)).obj
      ((constantSheaf X.smallEtaleTopology (Type u)).obj A)).property⟩

private theorem fieldEtaleRestrictionConstantHom_fac {U X : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (A : Type u) :
    toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A) ≫
      (fieldEtaleRestrictionConstantHom f A).hom =
    whiskerLeft (etalePostcompose f).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)) :=
  toSheafify_sheafifyLift U.smallEtaleTopology _ _

/-- Étale restriction preserves the actual constant sheaf. -/
instance fieldEtaleRestrictionConstantHom_isIso {U X : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (A : Type u) :
    IsIso (fieldEtaleRestrictionConstantHom f A) := by
  let η := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)
  have hInjective : Presheaf.IsLocallyInjective U.smallEtaleTopology
      (whiskerLeft (etalePostcompose f).op η) :=
    Presheaf.isLocallyInjective_whisker U.smallEtaleTopology X.smallEtaleTopology
      (etalePostcompose f) η
  have hSurjective : Presheaf.IsLocallySurjective U.smallEtaleTopology
      (whiskerLeft (etalePostcompose f).op η) :=
    Presheaf.isLocallySurjective_whisker U.smallEtaleTopology X.smallEtaleTopology
      (etalePostcompose f) η
  apply (U.smallEtaleTopology.W_sheafToPresheaf_map_iff_isIso _).mp
  apply (U.smallEtaleTopology.W.precomp_iff _ _
    (U.smallEtaleTopology.W_toSheafify ((Functor.const U.Etaleᵒᵖ).obj A))).mp
  change U.smallEtaleTopology.W
    (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A) ≫
      (fieldEtaleRestrictionConstantHom f A).hom)
  rw [fieldEtaleRestrictionConstantHom_fac]
  exact U.smallEtaleTopology.W_of_isLocallyBijective (whiskerLeft (etalePostcompose f).op η)

/-- The constant sheaf is unchanged by restriction to an étale source. -/
def fieldEtaleRestrictionConstantIso {U X : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (A : Type u) :
    (constantSheaf U.smallEtaleTopology (Type u)).obj A ≅
      (etaleRestriction f (Type u)).obj
        ((constantSheaf X.smallEtaleTopology (Type u)).obj A) :=
  asIso (fieldEtaleRestrictionConstantHom f A)

/-- On a field-valued point of an étale object over a field, sections of the
actual Type-valued constant sheaf are its coefficient set. -/
def fieldEtaleConstantSectionsEquiv {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) [Etale f] (A : Type u) :
    (((constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)).obj A).obj.obj
      (op ((etalePostcompose f).obj (etaleBaseObject (Spec (.of L)))))) ≃ A := by
  let W := etaleBaseObject (Spec (.of L))
  let cK := (constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)).obj A
  let cL := (constantSheaf (Spec (.of L)).smallEtaleTopology (Type u)).obj A
  let eRes := fieldEtaleRestrictionConstantIso f A
  let η := (constantSheafAdj (Spec (.of L)).smallEtaleTopology (Type u)
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) (Spec (.of L)))).unit.app A
  have hη : IsIso η := etaleConstantSheaf_unit_isIso (Spec (.of L)) A
  let eη : cL.obj.obj (op W) ≃ A :=
    (Equiv.ofBijective η ((CategoryTheory.isIso_iff_bijective η).mp hη)).symm
  let eResEval : cL.obj.obj (op W) ≃
      ((etaleRestriction f (Type u)).obj cK).obj.obj (op W) :=
    Equiv.ofBijective (eRes.hom.hom.app (op W))
      ((CategoryTheory.isIso_iff_bijective _).mp inferInstance)
  exact eResEval.symm.trans eη

/-- The connected field-component evaluation sends a canonical constant
section to its coefficient. -/
theorem fieldEtaleConstantSectionsEquiv_apply_toSheafify
    {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) [Etale f] (A : Type u) (a : A) :
    fieldEtaleConstantSectionsEquiv f A
      ((toSheafify (Spec (.of K)).smallEtaleTopology
        ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app
          (op ((etalePostcompose f).obj (etaleBaseObject (Spec (.of L))))) a) = a := by
  let W := etaleBaseObject (Spec (.of L))
  let cK := (constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)).obj A
  let cL := (constantSheaf (Spec (.of L)).smallEtaleTopology (Type u)).obj A
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) (Spec (.of L))
  let η := (constantSheafAdj (Spec (.of L)).smallEtaleTopology (Type u) hT).unit.app A
  have hη : IsIso η := etaleConstantSheaf_unit_isIso (Spec (.of L)) A
  let eηBase : A ≃ cL.obj.obj (op W) :=
    Equiv.ofBijective η ((CategoryTheory.isIso_iff_bijective η).mp hη)
  let eRes := fieldEtaleRestrictionConstantIso f A
  let eResEval : cL.obj.obj (op W) ≃
      ((etaleRestriction f (Type u)).obj cK).obj.obj (op W) :=
    Equiv.ofBijective (eRes.hom.hom.app (op W))
      ((CategoryTheory.isIso_iff_bijective _).mp inferInstance)
  let ηL := (toSheafify (Spec (.of L)).smallEtaleTopology
    ((Functor.const (Spec (.of L)).Etaleᵒᵖ).obj A)).app (op W)
  have hηL : η = ηL := by
    change (constantPresheafAdj (Type u) hT).unit.app A ≫ ηL = ηL
    rw [constantPresheafAdj_unit_app_eq_id]
    exact Category.id_comp _
  have hEtaFun : eηBase a = ηL a := by
    change η a = ηL a
    exact congrArg (fun q => q a) hηL
  have hsection : eResEval (eηBase a) =
      ((toSheafify (Spec (.of K)).smallEtaleTopology
        ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app
          (op ((etalePostcompose f).obj W))) a := by
    have h := congrArg (fun τ => τ.app (op W))
      (fieldEtaleRestrictionConstantHom_fac f A)
    have hval := congrArg (fun τ => τ a) h
    change eResEval (ηL a) = _ at hval
    rw [← hEtaFun] at hval
    exact hval
  change (eResEval.symm.trans eηBase.symm)
    (((toSheafify (Spec (.of K)).smallEtaleTopology
      ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app
        (op ((etalePostcompose f).obj W))) a) = a
  rw [← hsection]
  change eηBase.symm (eResEval.symm (eResEval (eηBase a))) = a
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The canonical additive constant-section map on a field component is
bijective. -/
theorem fieldEtaleConstantAbelianUnit_bijective
    {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) [Etale f] (A : AddCommGrpCat.{u}) :
    Function.Bijective ((toSheafify (Spec (.of K)).smallEtaleTopology
      ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app
        (op ((etalePostcompose f).obj (etaleBaseObject (Spec (.of L)))))).hom := by
  let X := Spec (.of K)
  let W := (etalePostcompose f).obj (etaleBaseObject (Spec (.of L)))
  let cA := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let ηA := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op W)
  let cT := (constantSheaf X.smallEtaleTopology (Type u)).obj
    ((forget AddCommGrpCat.{u}).obj A)
  let cmp := ((etaleConstantAbelianUnderlyingIso X).hom.app A).hom.app (op W)
  let eCmp : cA.obj.obj (op W) ≃ cT.obj.obj (op W) :=
    Equiv.ofBijective cmp ((CategoryTheory.isIso_iff_bijective _).mp inferInstance)
  let eEval := fieldEtaleConstantSectionsEquiv f ((forget AddCommGrpCat.{u}).obj A)
  let e := eCmp.trans eEval
  let ηT := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj ((forget AddCommGrpCat.{u}).obj A))).app (op W)
  let : X.smallEtaleTopology.PreservesSheafification (forget AddCommGrpCat.{u}) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget AddCommGrpCat.{u})
  have hnat := constantAbelianForgetToSheafify X.smallEtaleTopology
    (forget AddCommGrpCat.{u}) A
  have hsec (a : A) : (ConcreteCategory.hom cmp) (ηA.hom a) = ηT.hom a := by
    have h := congrArg (fun τ => τ.app (op W)) hnat
    exact congrArg (fun g => g a) h
  have hcomp (a : A) : e (ηA.hom a) = a := by
    change eEval ((ConcreteCategory.hom cmp) (ηA.hom a)) = a
    rw [hsec a]
    exact fieldEtaleConstantSectionsEquiv_apply_toSheafify f
      ((forget AddCommGrpCat.{u}).obj A) a
  constructor
  · intro a b hab
    have h := congrArg e hab
    rw [hcomp a, hcomp b] at h
    exact h
  · intro b
    refine ⟨e b, ?_⟩
    apply e.injective
    rw [hcomp]

/-- Additive sections of the actual constant abelian sheaf on a field
component are canonically the coefficient group. -/
noncomputable def fieldEtaleConstantAbelianSectionsAddEquiv
    {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) [Etale f] (A : AddCommGrpCat.{u}) :
    (((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op ((etalePostcompose f).obj (etaleBaseObject (Spec (.of L)))))) ≃+ A := by
  let η := (toSheafify (Spec (.of K)).smallEtaleTopology
    ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app
      (op ((etalePostcompose f).obj (etaleBaseObject (Spec (.of L)))))
  have hη := fieldEtaleConstantAbelianUnit_bijective f A
  change Function.Bijective η.hom at hη
  exact (AddEquiv.ofBijective η.hom hη).symm

/-- The field-component equivalence is natural for every morphism between
field-valued étale objects over the same base field. Both evaluations recover
the unique coefficient of the canonical sheafification-unit section. -/
theorem fieldEtaleConstantAbelianSectionsAddEquiv_naturality
    {K L M : Type u} [Field K] [Field L] [Field M]
    (f : Spec (.of L) ⟶ Spec (.of K)) [Etale f]
    (g : Spec (.of M) ⟶ Spec (.of K)) [Etale g]
    (m : (etalePostcompose f).obj (etaleBaseObject (Spec (.of L))) ⟶
      (etalePostcompose g).obj (etaleBaseObject (Spec (.of M))))
    (A : AddCommGrpCat.{u})
    (s : ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op ((etalePostcompose g).obj (etaleBaseObject (Spec (.of M)))))) :
    (fieldEtaleConstantAbelianSectionsAddEquiv f A)
      ((((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map
        m.op).hom s) =
      (fieldEtaleConstantAbelianSectionsAddEquiv g A) s := by
  let Ef := fieldEtaleConstantAbelianSectionsAddEquiv f A
  let Eg := fieldEtaleConstantAbelianSectionsAddEquiv g A
  let Wf := (etalePostcompose f).obj (etaleBaseObject (Spec (.of L)))
  let Wg := (etalePostcompose g).obj (etaleBaseObject (Spec (.of M)))
  let cA := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A
  let η := toSheafify (Spec (.of K)).smallEtaleTopology
    ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)
  have hEf (a : A) : Ef.symm a = (η.app (op Wf)).hom a := rfl
  have hEg (a : A) : Eg.symm a = (η.app (op Wg)).hom a := rfl
  have hnat (a : A) :
      (cA.obj.map m.op).hom (Eg.symm a) = Ef.symm a := by
    rw [hEg, hEf]
    dsimp only [cA, constantSheaf, Functor.comp_obj, Functor.comp_map]
    change (ConcreteCategory.hom
        (((presheafToSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj
          ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).obj.map m.op))
        ((ConcreteCategory.hom (η.app (op Wg))) a) =
      (ConcreteCategory.hom (η.app (op Wf))) a
    have h := congrArg (fun τ => τ a) (η.naturality m.op)
    simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at h
    have hid : (ConcreteCategory.hom (𝟙 A)) a = a := rfl
    rw [hid] at h
    simpa only [Functor.const_obj_map, ConcreteCategory.comp_apply,
      sheafify, sheafifyMap] using h.symm
  calc
    _ = Ef ((((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map
        m.op).hom (Eg.symm (Eg s))) := by rw [Eg.symm_apply_apply]
    _ = Ef (Ef.symm (Eg s)) := by rw [hnat]
    _ = Eg s := Ef.apply_symm_apply _

/-- A field-spectrum decomposition indexed by the actual points of the étale scheme. -/
structure FieldEtaleSigmaData (K : Type u) [Field K]
    (V : (Spec (.of K)).Etale) where
  /-- The field attached to each point of the étale scheme. -/
  L : V.left → CommRingCat
  /-- The base-field homomorphism for each component. -/
  a : ∀ x, CommRingCat.of K ⟶ L x
  /-- The decomposition into the spectra of the component fields. -/
  e : (∐ fun x => Spec (L x)) ≅ V.left
  /-- Each component ring is a field. -/
  hfield : ∀ x, IsField (L x)
  /-- Each component is a finite separable extension of the base field. -/
  hsep : ∀ x, letI := (a x).hom.toAlgebra
    Module.Finite K (L x) ∧ Algebra.IsSeparable K (L x)
  /-- The decomposition respects the original morphism to the base spectrum. -/
  he : e.hom ≫ V.hom = Sigma.desc (fun x => Spec.map (a x))
  /-- Each component maps its point to the original point indexing that component. -/
  hpoint : ∀ x, ∃ z : Spec (L x),
    e.hom (Sigma.ι (fun x => Spec (L x)) x z) = x

/-- Choose the proved field-spectrum decomposition with its original point labels. -/
noncomputable def fieldEtaleSigmaDataOf (K : Type u) [Field K]
    (V : (Spec (.of K)).Etale) : FieldEtaleSigmaData K V :=
  Classical.choice (show Nonempty _ from by
    obtain ⟨L, a, e, hfield, hsep, he, hpoint⟩ :=
      Scheme.Etale.exists_iso_sigmaSpec_with_point_labels K V
    exact ⟨⟨L, a, e, hfield, hsep, he, hpoint⟩⟩)

/-- Each field-spectrum component is finite étale over the original base field. -/
theorem fieldEtaleSigmaComponent_isFiniteEtale
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (x : V.left) :
    IsFiniteEtale (Spec.map (D.a x)) := by
  let : Field (D.L x) := (D.hfield x).toField
  let : Algebra K (D.L x) := (D.a x).hom.toAlgebra
  have hmod : Module.Finite K (D.L x) := (D.hsep x).1
  have hsep : Algebra.IsSeparable K (D.L x) := (D.hsep x).2
  have hform : Algebra.FormallyEtale K (D.L x) :=
    Algebra.FormallyEtale.of_isSeparable K (D.L x)
  have hetale : Algebra.Etale K (D.L x) := by
    exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  rw [IsFiniteEtale.SpecMap_iff]
  change (algebraMap K (D.L x)).FiniteEtale
  rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
  exact ⟨hetale, hmod⟩

/-- A field-spectrum component as an object of the original étale site. -/
def fieldEtaleSigmaComponent {K : Type u} [Field K]
    {V : (Spec (.of K)).Etale} (D : FieldEtaleSigmaData K V) (x : V.left) :
    (Spec (.of K)).Etale :=
  MorphismProperty.Over.mk ⊤ (Spec.map (D.a x)) (by
    have hfinite := fieldEtaleSigmaComponent_isFiniteEtale D x
    infer_instance)

/-- The family of actual field-spectrum components. -/
def fieldEtaleSigmaObjects {K : Type u} [Field K]
    {V : (Spec (.of K)).Etale} (D : FieldEtaleSigmaData K V) :
    V.left → (Spec (.of K)).Etale :=
  fun x => fieldEtaleSigmaComponent D x

/-- The component coproduct recovers the original étale object. -/
def fieldEtaleSigmaIso {K : Type u} [Field K]
    {V : (Spec (.of K)).Etale} (D : FieldEtaleSigmaData K V) :
    etaleSigma (fieldEtaleSigmaObjects D) ≅ V := by
  exact MorphismProperty.Over.isoMk D.e D.he

private def fieldEtaleSigmaComponentInclusion {K : Type u} [Field K]
    {V : (Spec (.of K)).Etale} (D : FieldEtaleSigmaData K V) (x : V.left) :
    fieldEtaleSigmaComponent D x ⟶ V :=
  etaleSigmaInj (fieldEtaleSigmaObjects D) x ≫ (fieldEtaleSigmaIso D).hom

/-- The selected summand component really contains its indexing point. -/
private theorem fieldEtaleSigmaComponentInclusion_hits_label
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (x : V.left) :
    ∃ z : (fieldEtaleSigmaComponent D x).left,
      (fieldEtaleSigmaComponentInclusion D x).left z = x := by
  obtain ⟨z, hz⟩ := D.hpoint x
  refine ⟨z, ?_⟩
  exact hz

private theorem fieldEtaleSigmaComponent_residuePointIso
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (x : V.left) :
    ∃ q : Spec (V.left.residueField x) ⟶ Spec (D.L x),
      IsIso q ∧ q ≫ (fieldEtaleSigmaComponentInclusion D x).left =
        V.left.fromSpecResidueField x := by
  let j := (fieldEtaleSigmaComponentInclusion D x).left
  let ρ := V.left.fromSpecResidueField x
  let : Field (D.L x) := (D.hfield x).toField
  let : Algebra K (D.L x) := (D.a x).hom.toAlgebra
  let : Algebra.IsSeparable K (D.L x) := (D.hsep x).2
  let : Module.Finite K (D.L x) := (D.hsep x).1
  let : Algebra.FormallyUnramified K (D.L x) :=
    Algebra.FormallyUnramified.of_isSeparable K (D.L x)
  have hredRing : _root_.IsReduced (D.L x) :=
    Algebra.FormallyUnramified.isReduced_of_field K (D.L x)
  obtain ⟨z, hz⟩ := fieldEtaleSigmaComponentInclusion_hits_label D x
  have hcod : Subsingleton ((fieldEtaleSigmaComponent D x).left) := by
    change Subsingleton (PrimeSpectrum (D.L x))
    exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced).2 (D.hfield x)
  let ρz := (fieldEtaleSigmaComponent D x).left.fromSpecResidueField z
  have hzClosed : IsClosed ({z} : Set (fieldEtaleSigmaComponent D x).left) := by
    have hzall : ({z} : Set (fieldEtaleSigmaComponent D x).left) = Set.univ := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact hcod.elim _ _
    rw [hzall]
    exact isClosed_univ
  have hρzClosed : IsClosedImmersion ρz :=
    isClosed_singleton_iff_isClosedImmersion.mp hzClosed
  have hρzSurjFun : Function.Surjective ρz := by
    intro y
    refine ⟨default, ?_⟩
    exact hcod.elim _ _
  let hρzSurj : Surjective ρz := ⟨hρzSurjFun⟩
  have hredTarget : IsReduced (fieldEtaleSigmaComponent D x).left := by
    change IsReduced (Spec (D.L x))
    exact (affine_isReduced_iff (D.L x)).2 hredRing
  have hρzIso : IsIso ρz :=
    @isIso_of_isClosedImmersion_of_surjective _ _ ρz hρzClosed hρzSurj hredTarget
  have hj : IsOpenImmersion j := by
    change IsOpenImmersion
      (Sigma.ι (fun y : V.left => Spec (D.L y)) x ≫ D.e.hom)
    have hι : IsOpenImmersion (Sigma.ι (fun y : V.left => Spec (D.L y)) x) :=
      (sigmaOpenCover (fun y : V.left => Spec (D.L y))).map_prop x
    infer_instance
  let β := V.left.residueFieldCongr hz
  let γIso : CommRingCat.of (V.left.residueField x) ≅
      CommRingCat.of ((fieldEtaleSigmaComponent D x).left.residueField z) :=
    β.symm ≪≫ asIso (j.residueFieldMap z)
  let q' := Spec.map γIso.inv ≫ ρz
  have hres : Spec.map γIso.hom ≫ ρ = ρz ≫ j := by
    have h1 := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := j) z
    have h2 : Spec.map β.symm.hom ≫ ρ =
        V.left.fromSpecResidueField (j z) :=
      Scheme.residueFieldCongr_fromSpecResidueField (X := V.left) hz.symm
    calc
      Spec.map γIso.hom ≫ ρ =
          Spec.map (j.residueFieldMap z) ≫ Spec.map β.symm.hom ≫ ρ := by
            simp only [γIso, Iso.trans_hom, Iso.symm_hom, Spec.map_comp,
              asIso_hom, Category.assoc]
      _ = Spec.map (j.residueFieldMap z) ≫ V.left.fromSpecResidueField (j z) := by
            rw [h2]
      _ = ρz ≫ j := h1
  have hq' : q' ≫ j = ρ := by
    calc
      q' ≫ j = Spec.map γIso.inv ≫ (Spec.map γIso.hom ≫ ρ) := by
        dsimp [q']
        rw [Category.assoc, hres]
      _ = ρ := by
        have hmaps : Spec.map γIso.inv ≫ Spec.map γIso.hom = 𝟙 _ := by
          rw [← Spec.map_comp, Iso.hom_inv_id]
          rw [Spec.map_id]
        rw [← Category.assoc, hmaps, Category.id_comp]
  have hq : q' ≫ j = ρ := hq'
  have hqIso : IsIso q' := by infer_instance
  exact ⟨q', hqIso, hq⟩

/-- Each actual residue-field point is étale over the original base field. -/
theorem fieldEtaleSigma_residuePoint_etale
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (x : V.left) :
    Etale (V.left.fromSpecResidueField x ≫ V.hom) := by
  let j := (fieldEtaleSigmaComponentInclusion D x).left
  let ρ := V.left.fromSpecResidueField x
  let f : Spec (D.L x) ⟶ Spec (.of K) := Spec.map (D.a x)
  have hf : Etale f := by
    have hfinite := fieldEtaleSigmaComponent_isFiniteEtale D x
    infer_instance
  have hji : j ≫ V.hom = f := (fieldEtaleSigmaComponentInclusion D x).w
  obtain ⟨q, hqIso, hq⟩ := fieldEtaleSigmaComponent_residuePointIso D x
  have hqf : Etale (q ≫ f) := by infer_instance
  have hcomp : q ≫ f = ρ ≫ V.hom := by
    calc
      q ≫ f = q ≫ (j ≫ V.hom) := by rw [← hji]; rfl
      _ = ρ ≫ V.hom := congrArg (fun t => t ≫ V.hom) hq
  rw [← hcomp]
  exact hqf

/-- The original residue-field point of an étale object over a field is
étale over that base field. -/
theorem fieldEtaleResiduePoint_etale (K : Type u) [Field K]
    (V : (Spec (.of K)).Etale) (x : V.left) :
    Etale (V.left.fromSpecResidueField x ≫ V.hom) :=
  fieldEtaleSigma_residuePoint_etale (fieldEtaleSigmaDataOf K V) x

/-- The actual residue-field point as an étale object over the base field. -/
def fieldEtaleSigmaResiduePointObject
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (x : V.left) : (Spec (.of K)).Etale :=
  let f := V.left.fromSpecResidueField x ≫ V.hom
  (etalePostcompose (hf := fieldEtaleSigma_residuePoint_etale D x) f).obj
    (etaleBaseObject (Spec (V.left.residueField x)))

/-- On an étale object over a field, sections of the Type-valued constant
sheaf are functions on its field-spectrum components. The decomposition and
the coefficient-set comparison require no algebraic-closedness hypothesis. -/
noncomputable def fieldEtaleConstantSectionsEquiv_of_exists_iso_sigmaSpec
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale) (A : Type u) :
    ((constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)).obj A).obj.obj (op V) ≃
      (V.left → A) := by
  let D := fieldEtaleSigmaDataOf K V
  let U := fieldEtaleSigmaObjects D
  let eV := fieldEtaleSigmaIso D
  let cK := (constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)).obj A
  let eVsec : cK.obj.obj (op V) ≃ cK.obj.obj (op (etaleSigma U)) :=
    Equiv.ofBijective (cK.obj.map eV.hom.op)
      ((CategoryTheory.isIso_iff_bijective _).mp inferInstance)
  let eSigma := etaleSigmaSectionsEquiv U cK
  let eComp (x : V.left) : cK.obj.obj (op (U x)) ≃ A := by
    let : Field (D.L x) := (D.hfield x).toField
    let : Algebra K (D.L x) := (D.a x).hom.toAlgebra
    let f : Spec (D.L x) ⟶ Spec (.of K) := Spec.map (D.a x)
    have hfinite := fieldEtaleSigmaComponent_isFiniteEtale D x
    have : Etale f := by infer_instance
    have hU : U x = (etalePostcompose f).obj (etaleBaseObject (Spec (D.L x))) := rfl
    subst U
    exact fieldEtaleConstantSectionsEquiv f A
  exact eVsec.trans (eSigma.trans (Equiv.piCongrRight eComp))

/-- Constant abelian sections on a field component recover the coefficient group. -/
noncomputable def fieldEtaleConstantAbelianComponentAddEquiv
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (x : V.left) (A : AddCommGrpCat.{u}) :
    (((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op (fieldEtaleSigmaComponent D x))) ≃+ A := by
  let : Field (D.L x) := (D.hfield x).toField
  let : Algebra K (D.L x) := (D.a x).hom.toAlgebra
  let f : Spec (D.L x) ⟶ Spec (.of K) := Spec.map (D.a x)
  have hfinite := fieldEtaleSigmaComponent_isFiniteEtale D x
  have : Etale f := by infer_instance
  exact fieldEtaleConstantAbelianSectionsAddEquiv f A

/-- Component restriction identifies constant abelian sections with functions on the points. -/
noncomputable def fieldEtaleConstantAbelianSigmaAddEquiv
    {K : Type u} [Field K] {V : (Spec (.of K)).Etale}
    (D : FieldEtaleSigmaData K V) (A : AddCommGrpCat.{u}) :
    (((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op V)) ≃+ (V.left → A) := by
  let U := fieldEtaleSigmaObjects D
  let eV := fieldEtaleSigmaIso D
  let cA := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A
  let eVsec : cA.obj.obj (op V) ≃+ cA.obj.obj (op (etaleSigma U)) :=
    AddEquiv.ofBijective (cA.obj.map eV.hom.op).hom
      ((ConcreteCategory.isIso_iff_bijective (cA.obj.map eV.hom.op)).mp inferInstance)
  let eSigma := etaleSigmaAbelianSectionsAddEquiv U cA
  let eComp (x : V.left) := fieldEtaleConstantAbelianComponentAddEquiv D x A
  exact eVsec.trans (eSigma.trans (AddEquiv.piCongrRight eComp))

/-- On an étale object over a field, additive sections of the actual constant
abelian sheaf are functions on its field-spectrum components. -/
noncomputable def fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale) (A : AddCommGrpCat.{u}) :
    (((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op V)) ≃+ (V.left → A) :=
  fieldEtaleConstantAbelianSigmaAddEquiv (fieldEtaleSigmaDataOf K V) A

/-- The component value at `x` is the value obtained by restricting the
section to its actual residue-field point. -/
theorem fieldEtaleConstantAbelianSectionsAddEquiv_residuePoint
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale) (A : AddCommGrpCat.{u})
    (s : ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op V)) (x : V.left) :
    let D := fieldEtaleSigmaDataOf K V
    let ρ := V.left.fromSpecResidueField x
    let f : Spec (V.left.residueField x) ⟶ Spec (.of K) := ρ ≫ V.hom
    let R : (Spec (.of K)).Etale := fieldEtaleSigmaResiduePointObject D x
    let r : R ⟶ V := MorphismProperty.Over.homMk (A := R) (B := V) ρ (by
      change ρ ≫ V.hom = f
      rfl)
    (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K V A s) x =
      @fieldEtaleConstantAbelianSectionsAddEquiv K (V.left.residueField x)
        inferInstance inferInstance f (fieldEtaleResiduePoint_etale K V x) A
        ((((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map
          r.op).hom s) := by
  intro D ρ g R r
  let : Field (D.L x) := (D.hfield x).toField
  let cA := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A
  let U := fieldEtaleSigmaComponent D x
  let inc := fieldEtaleSigmaComponentInclusion D x
  let j := inc.left
  let f : Spec (D.L x) ⟶ Spec (.of K) := Spec.map (D.a x)
  have hf : Etale f := by
    have hfinite := fieldEtaleSigmaComponent_isFiniteEtale D x
    infer_instance
  have hU : U = (etalePostcompose (hf := hf) f).obj
      (etaleBaseObject (Spec (D.L x))) := rfl
  obtain ⟨q, hqIso, hq⟩ := fieldEtaleSigmaComponent_residuePointIso D x
  have hji : j ≫ V.hom = f := inc.w
  have hg : Etale g := fieldEtaleSigma_residuePoint_etale D x
  let m : R ⟶ U := MorphismProperty.Over.homMk (A := R) (B := U) q (by
    change q ≫ f = g
    dsimp [g]
    calc
      q ≫ f = q ≫ (j ≫ V.hom) := by rw [← hji]; rfl
      _ = ρ ≫ V.hom := congrArg (fun t => t ≫ V.hom) hq)
  have hmcomp : m ≫ inc = r := by
    apply MorphismProperty.Over.Hom.ext
    change q ≫ j = ρ
    exact hq
  have hEval :
      (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K V A s) x =
        fieldEtaleConstantAbelianComponentAddEquiv D x A
          ((cA.obj.map inc.op).hom s) := by
    let U' := fieldEtaleSigmaObjects D
    let eV := fieldEtaleSigmaIso D
    let eVsec : cA.obj.obj (op V) ≃+ cA.obj.obj (op (etaleSigma U')) :=
      AddEquiv.ofBijective (cA.obj.map eV.hom.op).hom
        ((ConcreteCategory.isIso_iff_bijective (cA.obj.map eV.hom.op)).mp inferInstance)
    let eSigma := etaleSigmaAbelianSectionsAddEquiv U' cA
    let eComp (y : V.left) := fieldEtaleConstantAbelianComponentAddEquiv D y A
    have hequiv : fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K V A =
        eVsec.trans (eSigma.trans (AddEquiv.piCongrRight eComp)) := rfl
    rw [hequiv]
    change eComp x ((cA.obj.map (etaleSigmaInj U' x).op).hom
      ((cA.obj.map eV.hom.op).hom s)) = _
    change eComp x (ConcreteCategory.hom
      (cA.obj.map eV.hom.op ≫ cA.obj.map (etaleSigmaInj U' x).op) s) = _
    rw [← Functor.map_comp]
    rfl
  let mNat : R ⟶ (etalePostcompose (hf := hf) f).obj
      (etaleBaseObject (Spec (D.L x))) := m
  let tNat : ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op ((etalePostcompose (hf := hf) f).obj
        (etaleBaseObject (Spec (D.L x))))) := (cA.obj.map inc.op).hom s
  have hnat := @fieldEtaleConstantAbelianSectionsAddEquiv_naturality
    K (V.left.residueField x) (D.L x) inferInstance inferInstance
    (D.hfield x).toField g hg f hf mNat A tNat
  have hnat' :
      fieldEtaleConstantAbelianComponentAddEquiv D x A ((cA.obj.map inc.op).hom s) =
        @fieldEtaleConstantAbelianSectionsAddEquiv K (V.left.residueField x)
          inferInstance inferInstance g hg A
          ((cA.obj.map m.op).hom ((cA.obj.map inc.op).hom s)) := by
    change (@fieldEtaleConstantAbelianSectionsAddEquiv K (D.L x)
      inferInstance (D.hfield x).toField f hf A) ((cA.obj.map inc.op).hom s) = _
    exact hnat.symm
  have hop : inc.op ≫ m.op = r.op := by
    change (m ≫ inc).op = r.op
    rw [hmcomp]
  calc
    _ = fieldEtaleConstantAbelianComponentAddEquiv D x A
        ((cA.obj.map inc.op).hom s) := hEval
    _ = @fieldEtaleConstantAbelianSectionsAddEquiv K (V.left.residueField x)
        inferInstance inferInstance g hg A
        ((cA.obj.map m.op).hom ((cA.obj.map inc.op).hom s)) := hnat'
    _ = @fieldEtaleConstantAbelianSectionsAddEquiv K (V.left.residueField x)
        inferInstance inferInstance g hg A
        ((cA.obj.map r.op).hom s) := by
          congr 1
          change (ConcreteCategory.hom
            (cA.obj.map inc.op ≫ cA.obj.map m.op)) s =
            (ConcreteCategory.hom (cA.obj.map r.op)) s
          rw [← Functor.map_comp, hop]

/-- The pointwise function description is natural under every morphism of
étale objects over a field. The residue-field map gives the comparison arrow
between the two actual residue points. -/
theorem fieldEtaleConstantAbelianSectionsAddEquiv_morphism_naturality
    (K : Type u) [Field K] (V W : (Spec (.of K)).Etale)
    (m : V ⟶ W) (A : AddCommGrpCat.{u})
    (s : ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op W)) (x : V.left) :
    (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K V A
      ((((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.map
        m.op).hom s)) x =
      (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K W A s)
        (m.left x) := by
  let cA := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A
  let ρV := V.left.fromSpecResidueField x
  let y := m.left x
  let ρW := W.left.fromSpecResidueField y
  let fV : Spec (V.left.residueField x) ⟶ Spec (.of K) := ρV ≫ V.hom
  let fW : Spec (W.left.residueField y) ⟶ Spec (.of K) := ρW ≫ W.hom
  have hfV : Etale fV := fieldEtaleSigma_residuePoint_etale
    (fieldEtaleSigmaDataOf K V) x
  have hfW : Etale fW := fieldEtaleSigma_residuePoint_etale
    (fieldEtaleSigmaDataOf K W) y
  let RV : (Spec (.of K)).Etale := fieldEtaleSigmaResiduePointObject
    (fieldEtaleSigmaDataOf K V) x
  let RW : (Spec (.of K)).Etale := fieldEtaleSigmaResiduePointObject
    (fieldEtaleSigmaDataOf K W) y
  let rV : RV ⟶ V := MorphismProperty.Over.homMk (A := RV) (B := V) ρV (by
    change ρV ≫ V.hom = fV
    rfl)
  let rW : RW ⟶ W := MorphismProperty.Over.homMk (A := RW) (B := W) ρW (by
    change ρW ≫ W.hom = fW
    rfl)
  let δ : Spec (V.left.residueField x) ⟶ Spec (W.left.residueField y) :=
    Spec.map (m.left.residueFieldMap x)
  have hres : δ ≫ ρW = ρV ≫ m.left :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := m.left) x
  have hδ : δ ≫ fW = fV := by
    dsimp [fW, fV]
    calc
      δ ≫ (ρW ≫ W.hom) = (δ ≫ ρW) ≫ W.hom := by rw [Category.assoc]
      _ = (ρV ≫ m.left) ≫ W.hom := congrArg (fun q => q ≫ W.hom) hres
      _ = ρV ≫ (m.left ≫ W.hom) := by rw [Category.assoc]
      _ = ρV ≫ V.hom := by rw [MorphismProperty.Over.w m]
  let δOver : RV ⟶ RW := MorphismProperty.Over.homMk (A := RV) (B := RW) δ hδ
  have hcomp : δOver ≫ rW = rV ≫ m := by
    apply MorphismProperty.Over.Hom.ext
    change δ ≫ ρW = ρV ≫ m.left
    exact hres
  have hop : rW.op ≫ δOver.op = m.op ≫ rV.op := by
    have h := congrArg Quiver.Hom.op hcomp
    simpa only [op_comp] using h
  have hmap : cA.obj.map rW.op ≫ cA.obj.map δOver.op =
      cA.obj.map m.op ≫ cA.obj.map rV.op := by
    have h := congrArg (fun k => cA.obj.map k) hop
    simpa only [Functor.map_comp] using h
  have hsections :
      (cA.obj.map δOver.op).hom ((cA.obj.map rW.op).hom s) =
        (cA.obj.map rV.op).hom ((cA.obj.map m.op).hom s) :=
    congrArg (fun k => (ConcreteCategory.hom k) s) hmap
  have hnat := @fieldEtaleConstantAbelianSectionsAddEquiv_naturality
    K (V.left.residueField x) (W.left.residueField y)
    inferInstance inferInstance inferInstance fV hfV fW hfW δOver A
    ((cA.obj.map rW.op).hom s)
  have hEvalV := fieldEtaleConstantAbelianSectionsAddEquiv_residuePoint
    K V A ((cA.obj.map m.op).hom s) x
  have hEvalW := fieldEtaleConstantAbelianSectionsAddEquiv_residuePoint
    K W A s y
  rw [hEvalV, hEvalW]
  calc
    @fieldEtaleConstantAbelianSectionsAddEquiv K (V.left.residueField x)
        inferInstance inferInstance fV hfV A
        ((cA.obj.map rV.op).hom ((cA.obj.map m.op).hom s))
      = @fieldEtaleConstantAbelianSectionsAddEquiv K (V.left.residueField x)
          inferInstance inferInstance fV hfV A
          ((cA.obj.map δOver.op).hom ((cA.obj.map rW.op).hom s)) := by
            rw [← hsections]
    _ = @fieldEtaleConstantAbelianSectionsAddEquiv K (W.left.residueField y)
        inferInstance inferInstance fW hfW A
        ((cA.obj.map rW.op).hom s) := hnat

/-- The additive field-object equivalence sends a canonical constant section
to the constant function. -/
theorem fieldEtaleConstantAbelianSectionsAddEquiv_apply_toSheafify
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale) (A : AddCommGrpCat.{u})
    (a : A) :
    fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K V A
      (((toSheafify (Spec (.of K)).smallEtaleTopology
        ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app (op V)).hom a) =
      fun _ => a := by
  let D := fieldEtaleSigmaDataOf K V
  let U := fieldEtaleSigmaObjects D
  let eV := fieldEtaleSigmaIso D
  let cA := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A
  let η := toSheafify (Spec (.of K)).smallEtaleTopology
    ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)
  let eVsec : cA.obj.obj (op V) ≃+ cA.obj.obj (op (etaleSigma U)) :=
    AddEquiv.ofBijective (cA.obj.map eV.hom.op).hom
      ((ConcreteCategory.isIso_iff_bijective (cA.obj.map eV.hom.op)).mp inferInstance)
  let eSigma := etaleSigmaAbelianSectionsAddEquiv U cA
  let eComp (x : V.left) := fieldEtaleConstantAbelianComponentAddEquiv D x A
  have hunit (x : V.left) :
      (eComp x).symm a =
        ((toSheafify (Spec (.of K)).smallEtaleTopology
          ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).app (op (U x))).hom a := by
    rfl
  have hrestrict (x : V.left) :
      (cA.obj.map (etaleSigmaInj U x ≫ eV.hom).op)
        ((η.app (op V)).hom a) =
      ((η.app (op (U x))).hom a) := by
    let g := etaleSigmaInj U x ≫ eV.hom
    dsimp only [cA, constantSheaf, Functor.comp_obj, Functor.comp_map]
    change (ConcreteCategory.hom
        (((presheafToSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj
          ((Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A)).obj.map g.op))
        ((ConcreteCategory.hom (η.app (op V))) a) =
      (ConcreteCategory.hom (η.app (op (U x)))) a
    have h := congrArg (fun τ => τ a) (η.naturality g.op)
    simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at h
    have hid : (ConcreteCategory.hom (𝟙 A)) a = a := rfl
    rw [hid] at h
    simpa only [Functor.const_obj_map, ConcreteCategory.comp_apply,
      sheafify, sheafifyMap, g] using h.symm
  have hrestrict' (x : V.left) :
      (cA.obj.map (eV.hom.op ≫ (etaleSigmaInj U x).op)).hom
        ((η.app (op V)).hom a) =
      ((η.app (op (U x))).hom a) := by
    change (cA.obj.map (etaleSigmaInj U x ≫ eV.hom).op).hom
      ((η.app (op V)).hom a) = _
    exact hrestrict x
  have hequiv : fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K V A =
      eVsec.trans (eSigma.trans (AddEquiv.piCongrRight eComp)) := rfl
  rw [hequiv]
  change (fun x => eComp x ((cA.obj.map (etaleSigmaInj U x).op).hom
    ((cA.obj.map eV.hom.op).hom ((η.app (op V)).hom a)))) = fun _ => a
  funext x
  change eComp x (ConcreteCategory.hom
    (cA.obj.map eV.hom.op ≫ cA.obj.map (etaleSigmaInj U x).op)
    ((η.app (op V)).hom a)) = a
  rw [← Functor.map_comp]
  rw [hrestrict', ← hunit]
  exact (eComp x).apply_symm_apply a

/-- The underlying set of sections of the actual constant abelian sheaf on an
étale field object is the set of functions on its field-spectrum components. -/
noncomputable def fieldEtaleConstantAbelianSectionsUnderlyingEquiv
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale)
    (A : AddCommGrpCat.{u}) :
    (((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj
      (op V)) ≃ (V.left → A) := by
  let cK := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A
  let tK := (constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)).obj
    ((forget AddCommGrpCat.{u}).obj A)
  let e := (etaleConstantAbelianUnderlyingIso (Spec (.of K))).app A
  let eV : cK.obj.obj (op V) ≃ tK.obj.obj (op V) := by
    change ((etaleAbelianUnderlying (Spec (.of K))).obj cK).obj.obj (op V) ≃
      tK.obj.obj (op V)
    exact Equiv.ofBijective (e.hom.hom.app (op V))
      ((CategoryTheory.isIso_iff_bijective _).mp inferInstance)
  exact eV.trans (fieldEtaleConstantSectionsEquiv_of_exists_iso_sigmaSpec K V
    ((forget AddCommGrpCat.{u}).obj A))

end EtaleCohomology
