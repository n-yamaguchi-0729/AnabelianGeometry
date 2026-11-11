/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.MultiplicativeGroupStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAffineGenericDescent
public import Nyll.SchemeTheory.Affine.SpecBaseChangeSectionsMap
public import Nyll.SchemeTheory.Sheaves.StalkRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.SchemeTheory.Sheaves.UnitStalks

/-!
# Actual generic sections and the geometric-stalk tensor diagram

The tensor diagram and the ring presheaf of actual generic pullbacks have
a canonical comparison. Every pointed neighborhood admits an affine
refinement where this comparison is bijective. Consequently the comparison
on actual geometric stalks is bijective, without assuming a comparison
between their colimits.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable (R : Type u) [CommRing R]

/-- The presheaf of actual neighborhood section algebras under the base ring. -/
def etaleNeighborhoodAlgebras :
    (Spec (CommRingCat.of R)).Etaleᵒᵖ ⥤ Under (CommRingCat.of R) where
  obj V := geometricNeighborhoodAlgebra R V.unop
  map g := geometricNeighborhoodAlgebraMap R g.unop
  map_id V := by
    apply Under.UnderMorphism.ext
    exact Scheme.Hom.id_appTop
  map_comp g h := by
    apply Under.UnderMorphism.ext
    change (h.unop.left ≫ g.unop.left).appTop =
      g.unop.left.appTop ≫ h.unop.left.appTop
    exact Scheme.Hom.comp_appTop h.unop.left g.unop.left

/-- The tensor-product ring presheaf underlying the existing generic diagram. -/
def etaleGenericTensorSections :
    (Spec (CommRingCat.of R)).Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  etaleNeighborhoodAlgebras R ⋙
    CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R)) ⋙
      Under.forget (CommRingCat.of (FractionRing R))

/-- The canonical comparison with sections of actual generic pullbacks. -/
def etaleGenericTensorSectionsMap :
    etaleGenericTensorSections R ⟶
      etaleBaseChangedSections
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) where
  app V := specPullbackSectionsTensorMap (A := FractionRing R) V.unop.hom
  naturality {V W} g := by
    let K := FractionRing R
    let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let : Algebra R Γ(V.unop.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.unop.hom.appTop).hom.toAlgebra
    let : Algebra R Γ(W.unop.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.unop.hom.appTop).hom.toAlgebra
    let k := ((EtaleCohomology.etaleBaseChange j).map g.unop).left
    let α : Γ(V.unop.left, ⊤) →ₐ[R] Γ(W.unop.left, ⊤) :=
      { toRingHom := g.unop.left.appTop.hom
        commutes' := fun r =>
          ConcreteCategory.congr_hom
            (Under.w (geometricNeighborhoodAlgebraMap R g.unop)) r }
    let m : CommRingCat.of (K ⊗[R] Γ(V.unop.left, ⊤)) ⟶
        CommRingCat.of (K ⊗[R] Γ(W.unop.left, ⊤)) :=
      CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) α).toRingHom
    change m ≫ specPullbackSectionsTensorMap (A := K) W.unop.hom =
      specPullbackSectionsTensorMap (A := K) V.unop.hom ≫ k.appTop
    have hL :
        (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom :
          CommRingCat.of K ⟶ CommRingCat.of (K ⊗[R] Γ(V.unop.left, ⊤))) ≫ m =
          (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom :
            CommRingCat.of K ⟶ CommRingCat.of (K ⊗[R] Γ(W.unop.left, ⊤))) := by
      apply CommRingCat.hom_ext
      ext a
      change Algebra.TensorProduct.map (AlgHom.id K K) α
        (a ⊗ₜ[R] (1 : Γ(V.unop.left, ⊤))) = a ⊗ₜ[R] (1 : Γ(W.unop.left, ⊤))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    have hR :
        (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom :
          Γ(V.unop.left, ⊤) ⟶ CommRingCat.of (K ⊗[R] Γ(V.unop.left, ⊤))) ≫ m =
          g.unop.left.appTop ≫
            (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom :
              Γ(W.unop.left, ⊤) ⟶ CommRingCat.of (K ⊗[R] Γ(W.unop.left, ⊤))) := by
      apply CommRingCat.hom_ext
      ext a
      rfl
    have hfst : k ≫ pullback.fst V.unop.hom j =
        pullback.fst W.unop.hom j ≫ g.unop.left := by
      dsimp only [k, EtaleCohomology.etaleBaseChange]
      exact pullback.lift_fst _ _ _
    have hsnd : k ≫ pullback.snd V.unop.hom j =
        pullback.snd W.unop.hom j := by
      dsimp only [k, EtaleCohomology.etaleBaseChange]
      exact pullback.lift_snd _ _ _
    have hs :
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
            (pullback.snd W.unop.hom j).appTop =
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
            (pullback.snd V.unop.hom j).appTop) ≫ k.appTop :=
      (congrArg (fun l : pullback W.unop.hom j ⟶ Spec (CommRingCat.of K) =>
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ l.appTop) hsnd.symm).trans
          ((congrArg (fun l => (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ l)
            (Scheme.Hom.comp_appTop k (pullback.snd V.unop.hom j))).trans
              (Category.assoc _ _ _).symm)
    have hf : g.unop.left.appTop ≫ (pullback.fst W.unop.hom j).appTop =
        (pullback.fst V.unop.hom j).appTop ≫ k.appTop :=
      (Scheme.Hom.comp_appTop (pullback.fst W.unop.hom j) g.unop.left).symm.trans
        ((congrArg (fun l : pullback W.unop.hom j ⟶ V.unop.left => l.appTop)
          hfst.symm).trans
            (Scheme.Hom.comp_appTop k (pullback.fst V.unop.hom j)))
    apply (CommRingCat.isPushout_tensorProduct R K Γ(V.unop.left, ⊤)).hom_ext
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun l => l ≫ specPullbackSectionsTensorMap (A := K) W.unop.hom)
          hL).trans
          ((specPullbackSectionsTensorMap_left (A := K) W.unop.hom).trans
            (hs.trans
              ((congrArg (fun l => l ≫ k.appTop)
                (specPullbackSectionsTensorMap_left (A := K) V.unop.hom).symm).trans
                  (Category.assoc _ _ _)))))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun l => l ≫ specPullbackSectionsTensorMap (A := K) W.unop.hom)
          hR).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun l => g.unop.left.appTop ≫ l)
              (specPullbackSectionsTensorMap_right (A := K) W.unop.hom)).trans
                (hf.trans
                  ((congrArg (fun l => l ≫ k.appTop)
                    (specPullbackSectionsTensorMap_right (A := K) V.unop.hom).symm).trans
                      (Category.assoc _ _ _))))))

variable [IsDomain R] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

omit [IsDomain R] in
/-- Affine pointed refinements establish bijectivity of the actual
generic-sections comparison on the geometric stalk. -/
theorem etaleGenericTensorSectionsMap_stalk_bijective :
    Function.Bijective
      (((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiber
        (A := CommRingCat.{u})).map (etaleGenericTensorSectionsMap R)) := by
  apply CategoryTheory.GrothendieckTopology.Point.ringPresheafFiber_map_bijective_of_refinements
  intro W t
  obtain ⟨V, v, g, hV, hgv⟩ :=
    geometricStalk_exists_affine_refinement (Spec.map (CommRingCat.ofHom φ)) W t
  let : IsAffine V.left := hV
  refine ⟨V, g, v, hgv, ?_⟩
  let f : V.left ⟶ Spec (CommRingCat.of R) := V.hom
  have : IsAffineHom f := isAffineHom_of_isAffine f
  have : QuasiCompact f := inferInstance
  have : QuasiSeparated f := inferInstance
  exact specPullbackSectionsTensorMap_bijective (A := FractionRing R) f

variable [IsIntegrallyClosed R]

/-- The already constructed strict generic field cocone, viewed on the
full pointed-neighborhood tensor diagram in commutative rings. -/
def geometricGenericFieldRingCocone :
    Cocone
      ((Functor.Elements.π
          (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber).op ⋙
        etaleGenericTensorSections R) :=
  (Under.forget (CommRingCat.of (FractionRing R))).mapCocone
    (((CommRingCat.tensorProd (CommRingCat.of R)
        (CommRingCat.of (FractionRing R))).mapCocone
      (geometricStalkAlgebraCocone φ)).extend
        (geometricStalkGenericFieldVertexIso φ).hom)

/-- The actual fraction-field cocone is colimiting on all pointed neighborhoods,
by the existing small filtered presentation and finality. -/
def geometricGenericFieldRingCoconeIsColimit :
    IsColimit (geometricGenericFieldRingCocone R φ) := by
  apply (Functor.Final.isColimitWhiskerEquiv
    (FinallySmall.fromFilteredFinalModel
      (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ)
    (geometricGenericFieldRingCocone R φ)).toFun
  exact isColimitOfPreserves (Under.forget (CommRingCat.of (FractionRing R)))
    (geometricStalkGenericFieldCoconeIsColimit φ)

/-- The tensor-presheaf stalk is the actual fraction field of the geometric stalk. -/
def etaleGenericTensorStalkIso :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiber
        (A := CommRingCat.{u})).obj (etaleGenericTensorSections R) ≅
      CommRingCat.of
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
  IsColimit.coconePointUniqueUpToIso
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).isColimitPresheafFiberCocone
      (etaleGenericTensorSections R))
    (geometricGenericFieldRingCoconeIsColimit R φ)

/-- The actual ring stalk of sections on generic pullbacks is the fraction
field of the actual geometric stalk. -/
def geometricGenericSectionsStalkEquiv :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiber
        (A := CommRingCat.{u})).obj
      (etaleBaseChangedSections
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ≃+*
      FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
  (RingEquiv.ofBijective
    (((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiber
      (A := CommRingCat.{u})).map (etaleGenericTensorSectionsMap R)).hom
    (etaleGenericTensorSectionsMap_stalk_bijective R φ)).symm.trans
      (etaleGenericTensorStalkIso R φ).commRingCatIsoToRingEquiv

/-- On genuine neighborhood sections the tensor-stalk comparison sends a
simple tensor to the scalar times the actual germ. -/
theorem etaleGenericTensorStalkIso_tmul
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (k : FractionRing R) (a : Γ(W.left, ⊤)) :
    let : Algebra R Γ(W.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom.toAlgebra
    (etaleGenericTensorStalkIso R φ).hom
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber
        W t (etaleGenericTensorSections R)
          ((k ⊗ₜ[R] a) :
            FractionRing R ⊗[R] Γ(W.left, ⊤))) =
      geometricStalkFractionFieldMap φ k *
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
        (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t a) := by
  intro hRW
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).isColimitPresheafFiberCocone
      (etaleGenericTensorSections R))
    (geometricGenericFieldRingCoconeIsColimit R φ)
    (op ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.elementsMk W t))
  have he := ConcreteCategory.congr_hom h
    ((k ⊗ₜ[R] a) : FractionRing R ⊗[R] Γ(W.left, ⊤))
  refine he.trans ?_
  let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
    (geometricStalkStructureMap φ).toAlgebra
  let : Algebra (FractionRing R)
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
    (geometricStalkFractionFieldMap φ).toAlgebra
  let α : Γ(W.left, ⊤) →ₐ[R] geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
    { toRingHom := (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t).hom
      commutes' := fun r => RingHom.congr_fun (geometricStalkGerm_comp_structure φ W t) r }
  change geometricStalkGenericFieldEquiv φ
    (Algebra.TensorProduct.map (AlgHom.id (FractionRing R) (FractionRing R)) α
      ((k ⊗ₜ[R] a) : FractionRing R ⊗[R] Γ(W.left, ⊤))) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact geometricStalkGenericFieldEquiv_tmul φ k
    (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t a)

/-- On genuine neighborhood sections the tensor-stalk comparison is the
canonical fraction-field inclusion of their actual germs. -/
theorem etaleGenericTensorStalkIso_one_tmul
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (a : Γ(W.left, ⊤)) :
    let : Algebra R Γ(W.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom.toAlgebra
    (etaleGenericTensorStalkIso R φ).hom
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber
        W t (etaleGenericTensorSections R)
          (((1 : FractionRing R) ⊗ₜ[R] a) :
            FractionRing R ⊗[R] Γ(W.left, ⊤))) =
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
        (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t a) := by
  intro hRW
  simpa only [map_one, one_mul] using
    etaleGenericTensorStalkIso_tmul R φ W t (1 : FractionRing R) a

/-- The comparison sends the actual restriction from the geometric local ring
to its canonical inclusion in the fraction field. -/
theorem geometricGenericSectionsStalkEquiv_map
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) :
    geometricGenericSectionsStalkEquiv R φ
      (((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiber
        (A := CommRingCat.{u})).map
        (etaleSectionsToBaseChanged
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) a) =
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) a := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let P := etaleSections (Spec (CommRingCat.of R))
  let T := etaleGenericTensorSections R
  let Q := etaleBaseChangedSections j
  let η := etaleGenericTensorSectionsMap R
  obtain ⟨W, t, x, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) a
  let : Algebra R Γ(W.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom.toAlgebra
  let y : T.obj (op W) :=
    (((1 : FractionRing R) ⊗ₜ[R] (x : Γ(W.left, ⊤))) :
      FractionRing R ⊗[R] Γ(W.left, ⊤))
  have hη :
      (Φ.presheafFiber (A := CommRingCat.{u})).map η
          (Φ.toPresheafFiber W t T y) =
        Φ.toPresheafFiber W t Q (η.app (op W) y) :=
    ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality η W t) y
  have hright : η.app (op W) y = (pullback.fst W.hom j).appTop x :=
    ConcreteCategory.congr_hom
      (specPullbackSectionsTensorMap_right (A := FractionRing R) W.hom) x
  have hf :
      (Φ.presheafFiber (A := CommRingCat.{u})).map
          (etaleSectionsToBaseChanged j) (Φ.toPresheafFiber W t P x) =
        Φ.toPresheafFiber W t Q ((pullback.fst W.hom j).appTop x) :=
    ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_naturality (etaleSectionsToBaseChanged j) W t) x
  have h :
      (Φ.presheafFiber (A := CommRingCat.{u})).map η
          (Φ.toPresheafFiber W t T y) =
        (Φ.presheafFiber (A := CommRingCat.{u})).map
          (etaleSectionsToBaseChanged j) (Φ.toPresheafFiber W t P x) :=
    hη.trans ((congrArg (Φ.toPresheafFiber W t Q) hright).trans hf.symm)
  change geometricGenericSectionsStalkEquiv R φ
    ((Φ.presheafFiber (A := CommRingCat.{u})).map
      (etaleSectionsToBaseChanged j) (Φ.toPresheafFiber W t P x)) = _
  rw [← h]
  let e := RingEquiv.ofBijective
    ((Φ.presheafFiber (A := CommRingCat.{u})).map η).hom
    (etaleGenericTensorSectionsMap_stalk_bijective R φ)
  change (etaleGenericTensorStalkIso R φ).hom
    (e.symm (e (Φ.toPresheafFiber W t T y))) = _
  rw [RingEquiv.symm_apply_apply]
  exact etaleGenericTensorStalkIso_one_tmul R φ W t x

/-- On actual generic-pullback sections, a tensor representative retains
both the original rational scalar and the actual neighborhood germ. -/
theorem geometricGenericSectionsStalkEquiv_tensor
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (k : FractionRing R) (a : Γ(W.left, ⊤)) :
    let : Algebra R Γ(W.left, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom.toAlgebra
    geometricGenericSectionsStalkEquiv R φ
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber
        W t (etaleBaseChangedSections
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
        ((specPullbackSectionsTensorMap (A := FractionRing R) W.hom)
          ((k ⊗ₜ[R] a) : FractionRing R ⊗[R] Γ(W.left, ⊤)))) =
      geometricStalkFractionFieldMap φ k *
        algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
          (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W t a) := by
  intro hRW
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let T := etaleGenericTensorSections R
  let Q := etaleBaseChangedSections
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  let η := etaleGenericTensorSectionsMap R
  let y : T.obj (op W) :=
    ((k ⊗ₜ[R] a) : FractionRing R ⊗[R] Γ(W.left, ⊤))
  have hη := ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality η W t) y
  change geometricGenericSectionsStalkEquiv R φ
    (ConcreteCategory.hom (η.app (op W) ≫ Φ.toPresheafFiber W t Q) y) = _
  rw [← hη]
  let e := RingEquiv.ofBijective
    ((Φ.presheafFiber (A := CommRingCat.{u})).map η).hom
    (etaleGenericTensorSectionsMap_stalk_bijective R φ)
  change (etaleGenericTensorStalkIso R φ).hom
    (e.symm (e (Φ.toPresheafFiber W t T y))) = _
  rw [RingEquiv.symm_apply_apply]
  exact etaleGenericTensorStalkIso_tmul R φ W t k a

/-- A rational scalar viewed as a section on an actual generic pullback
maps to its actual fraction-field image at every pointed neighborhood. -/
theorem geometricGenericSectionsStalkEquiv_scalar
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (k : FractionRing R) :
    geometricGenericSectionsStalkEquiv R φ
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber
        W t (etaleBaseChangedSections
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
        (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          (pullback.snd W.hom
            (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).appTop) k)) =
      geometricStalkFractionFieldMap φ k := by
  let hRW : Algebra R Γ(W.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom.toAlgebra
  have hleft := ConcreteCategory.congr_hom
    (specPullbackSectionsTensorMap_left (A := FractionRing R) W.hom) k
  change (specPullbackSectionsTensorMap (A := FractionRing R) W.hom)
      (@TensorProduct.tmul R _ (FractionRing R) (Γ(W.left, ⊤)) _ _ _
        (@Algebra.toModule R (Γ(W.left, ⊤)) _ _ hRW) k (1 : Γ(W.left, ⊤))) = _ at hleft
  rw [← hleft, geometricGenericSectionsStalkEquiv_tensor, map_one, map_one, mul_one]

/-- Rational units on actual generic pullbacks have the prescribed fraction-field germs. -/
theorem geometricGenericUnitStalk_scalar
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (a : Additive (FractionRing R)ˣ) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Φ := Scheme.pointSmallEtale s
    let P := etaleBaseChangedSections j
    let z : (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj (op W) :=
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
    (Units.map (geometricGenericSectionsStalkEquiv R φ).toMonoidHom).toAdditive
      (geometricMultiplicativeGroupPushforwardStalkEquiv s j
        (Φ.toPresheafFiber W t
          (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z)) =
      Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom a.toMul) := by
  intro s j Φ P z
  change (Units.map (geometricGenericSectionsStalkEquiv R φ).toMonoidHom).toAdditive
    (CategoryTheory.GrothendieckTopology.Point.unitStalkMap Φ P
      (Φ.toPresheafFiber W t
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z)) = _
  rw [CategoryTheory.GrothendieckTopology.Point.unitStalkMap_germ]
  apply Additive.toMul.injective
  apply Units.ext
  exact geometricGenericSectionsStalkEquiv_scalar R φ W t a.toMul.val

end EtaleFundamentalGroups.StrictHenselian
