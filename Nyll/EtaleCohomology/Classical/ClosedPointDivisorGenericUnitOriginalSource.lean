/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCoordinates
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitSourceTransport
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegralAffineEtaleBasis
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Chart comparison on a common original source

The coordinate calculation is transported back to an arbitrary integral
affine object of the original small étale site. Its coordinate spectrum and
its map to the original scheme are independent of the chosen target chart.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology.DivisorGenericUnitGlobal

/-- The coordinate spectrum of an affine object, identified with that same
object in the original small étale site. -/
def affineCoordinateSourceIso
    {X : Scheme.{u}} (V : X.Etale) [IsAffine V.left] :
    Scheme.Etale.mk ((Scheme.isoSpec V.left).inv ≫ V.hom) ≅ V :=
  MorphismProperty.Over.isoMk (Scheme.isoSpec V.left).symm rfl

private theorem map_op_comp_eq_apply {Cat : Type*} [Category Cat]
    (F : Catᵒᵖ ⥤ AddCommGrpCat.{u}) {A B C D : Cat}
    (f : A ⟶ B) (g : B ⟶ D) (p : A ⟶ C) (q : C ⟶ D)
    (h : f ≫ g = p ≫ q) (s : F.obj (op D)) :
    F.map f.op (F.map g.op s) = F.map p.op (F.map q.op s) := by
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun k : A ⟶ D => F.map k.op) h) s
  simpa only [op_comp, Functor.map_comp, CategoryTheory.comp_apply] using hh

private theorem hom_eq_comp_apply {A B C D : AddCommGrpCat.{u}}
    {l : A ⟶ D} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hl : l = f ≫ g ≫ h) (s : A) : l s = h (g (f s)) := by
  exact (ConcreteCategory.congr_hom hl s).trans
    ((CategoryTheory.comp_apply f (g ≫ h) s).trans
      (CategoryTheory.comp_apply g h (f s)))

private theorem map_op_iso_cancel_apply {Cat : Type*} [Category Cat]
    (F : Catᵒᵖ ⥤ AddCommGrpCat.{u}) {A B : Cat} (e : A ≅ B)
    (s : F.obj (op B)) : F.map e.inv.op (F.map e.hom.op s) = s := by
  have hmap : F.map e.hom.op ≫ F.map e.inv.op = 𝟙 (F.obj (op B)) := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id, F.map_id]
  exact (CategoryTheory.comp_apply _ _ s).symm.trans
    ((ConcreteCategory.congr_hom hmap s).trans (ConcreteCategory.id_apply s))

private theorem slice_section_transport
    {X U : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (j : U ⟶ X) [Etale j]
    (f : (etaleRestriction j AddCommGrpCat.{u}).obj F ⟶
      (etaleRestriction j AddCommGrpCat.{u}).obj G)
    (l : (Over.forget (Scheme.Etale.mk j)).op ⋙ F.obj ⟶
      (Over.forget (Scheme.Etale.mk j)).op ⋙ G.obj)
    (hl : Functor.whiskerLeft (etaleSliceEquiv (Scheme.Etale.mk j)).inverse.op l = f.hom)
    (T : Over (Scheme.Etale.mk j)) (B : U.Etale)
    (c : T ≅ (etaleSliceEquiv (Scheme.Etale.mk j)).inverse.obj B)
    {V W : X.Etale} (p : V ⟶ T.left)
    (r : W ⟶ (etalePostcompose j).obj B)
    (cS : W ≅ V)
    (h : cS.inv ≫ r = p ≫ c.hom.left)
    (s : F.obj.obj (op T.left)) :
    G.obj.map p.op (l.app (op T) s) =
      G.obj.map cS.inv.op
        (G.obj.map r.op
          (f.hom.app (op B) (F.obj.map c.inv.left.op s))) := by
  let P : (Over (Scheme.Etale.mk j))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (Over.forget (Scheme.Etale.mk j)).op ⋙ F.obj
  let Q : (Over (Scheme.Etale.mk j))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (Over.forget (Scheme.Etale.mk j)).op ⋙ G.obj
  have hc : P.map c.inv.op ≫ P.map c.hom.op = 𝟙 (P.obj (op T)) :=
    (P.mapIso c.op).inv_hom_id
  have hn := l.naturality c.hom.op
  have ha : l.app (op ((etaleSliceEquiv (Scheme.Etale.mk j)).inverse.obj B)) = f.hom.app (op B) :=
    congr_app hl (op B)
  have hlmap : l.app (op T) =
      F.obj.map c.inv.left.op ≫ f.hom.app (op B) ≫ G.obj.map c.hom.left.op := by
    change l.app (op T) = P.map c.inv.op ≫ f.hom.app (op B) ≫ Q.map c.hom.op
    calc
      _ = (P.map c.inv.op ≫ P.map c.hom.op) ≫ l.app (op T) := by
        rw [hc, Category.id_comp]
      _ = P.map c.inv.op ≫ l.app (op ((etaleSliceEquiv (Scheme.Etale.mk j)).inverse.obj B)) ≫
          Q.map c.hom.op := by rw [Category.assoc, hn]
      _ = _ := congrArg (fun h => P.map c.inv.op ≫ h ≫ Q.map c.hom.op) ha
  have hl := hom_eq_comp_apply (F.obj.map c.inv.left.op)
    (f.hom.app (op B))
    (G.obj.map c.hom.left.op)
    hlmap s
  exact (congrArg (fun z => G.obj.map p.op z) hl).trans
    (map_op_comp_eq_apply G.obj p c.hom.left cS.inv r h.symm
      (f.hom.app (op B) (F.obj.map c.inv.left.op s)))

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (V : X.Etale) [IsAffine V.left] [IsIntegral V.left]
  (m : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))

/-- Regard the original integral affine source as an integral affine
object over the chosen chart, retaining its underlying scheme. -/
def integralAffineChartSource :
    (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory := by
  refine ⟨(etaleSliceForward (Scheme.Etale.mk (e.hom ≫ U.ι))).obj
    (Over.mk m), ?_⟩
  change IsAffine V.left ∧ IsIntegral V.left
  exact ⟨inferInstance, inferInstance⟩

omit [IsDedekindDomain R] [IsIntegral X] [JacobsonSpace X] in
/-- The original coordinate map to the scheme is the composite of its
coordinate map to the chart and the chart inclusion. -/
theorem integralAffineChartSource_coordinate_comp :
    Spec.map (integralAffineCoordinateBaseMap R
        (integralAffineChartSource R U e V m)) ≫ (e.hom ≫ U.ι) =
      (Scheme.isoSpec V.left).inv ≫ V.hom := by
  let A := integralAffineChartSource R U e V m
  rw [integralAffineCoordinateSpecMap_eq R A, Category.assoc]
  have hm : A.obj.hom ≫ (e.hom ≫ U.ι) = V.hom := m.w
  rw [hm]
  rfl

/-- The coordinate algebra on the original affine source, with its literal
ring of global sections as target. -/
@[instance_reducible]
def integralAffineChartCoordinateAlgebra : Algebra R Γ(V.left, ⊤) :=
  (integralAffineCoordinateBaseMap R (integralAffineChartSource R U e V m)).hom.toAlgebra

omit [IsDedekindDomain R] [IsIntegral X] [JacobsonSpace X] in
/-- The shared coordinate algebra retains the original structural ring map. -/
theorem integralAffineChartCoordinateAlgebra_algebraMap :
    let _ : Algebra R Γ(V.left, ⊤) := integralAffineChartCoordinateAlgebra R U e V m
    algebraMap R Γ(V.left, ⊤) =
      (integralAffineCoordinateBaseMap R (integralAffineChartSource R U e V m)).hom := by
  intro algRS
  rfl

omit [IsDedekindDomain R] [IsIntegral X] [JacobsonSpace X] in
/-- The original coordinate map gives the shared algebra its étale structure. -/
theorem integralAffineChartCoordinateAlgebra_etale :
    let _ : Algebra R Γ(V.left, ⊤) := integralAffineChartCoordinateAlgebra R U e V m
    Algebra.Etale R Γ(V.left, ⊤) := by
  intro algRS
  exact RingHom.etale_algebraMap.mp
    (integralAffineCoordinateBaseMap_etale R (integralAffineChartSource R U e V m))

/-- The original structural map followed by the coordinate fraction-ring map. -/
@[instance_reducible]
def integralAffineChartCoordinateAmbientAlgebra :
    Algebra R (FractionRing Γ(V.left, ⊤)) := by
  let S : Type u := Γ(V.left, ⊤)
  let _ : Algebra R S := integralAffineChartCoordinateAlgebra R U e V m
  exact ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra

omit [IsDedekindDomain R] [IsIntegral X] [JacobsonSpace X] in
/-- The shared ambient algebra extends the shared coordinate algebra. -/
theorem integralAffineChartCoordinateAmbientAlgebra_isScalarTower :
    let algRS : Algebra R Γ(V.left, ⊤) := integralAffineChartCoordinateAlgebra R U e V m
    let algRE : Algebra R (FractionRing Γ(V.left, ⊤)) :=
      integralAffineChartCoordinateAmbientAlgebra R U e V m
    @IsScalarTower R Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤)) algRS.toSMul
      (inferInstance : Algebra Γ(V.left, ⊤) (FractionRing Γ(V.left, ⊤))).toSMul
      algRE.toSMul := by
  intro algRS algRE
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The existing coordinate fraction-field lift, with the original source's
literal coordinate ring as target. -/
@[instance_reducible]
def integralAffineChartCoordinateFractionFieldAlgebra :
    Algebra (FractionRing R) (FractionRing Γ(V.left, ⊤)) :=
  integralAffineCoordinateFractionFieldAlgebra R (integralAffineChartSource R U e V m)

omit [IsIntegral X] [JacobsonSpace X] in
/-- The shared fraction-field lift extends the shared ambient algebra. -/
theorem integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower :
    let _ : Algebra R Γ(V.left, ⊤) := integralAffineChartCoordinateAlgebra R U e V m
    let algRE : Algebra R (FractionRing Γ(V.left, ⊤)) :=
      integralAffineChartCoordinateAmbientAlgebra R U e V m
    let algKE : Algebra (FractionRing R) (FractionRing Γ(V.left, ⊤)) :=
      integralAffineChartCoordinateFractionFieldAlgebra R U e V m
    @IsScalarTower R (FractionRing R) (FractionRing Γ(V.left, ⊤))
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul := by
  intro algRS algRE algKE
  exact integralAffineCoordinateFractionFieldAlgebra_isScalarTower R
    (integralAffineChartSource R U e V m)

omit [IsDedekindDomain R] [IsIntegral X] [JacobsonSpace X] in
/-- The shared coordinate algebra gives the same map to the original scheme. -/
theorem integralAffineChartCoordinate_comp :
    let _ : Algebra R Γ(V.left, ⊤) := integralAffineChartCoordinateAlgebra R U e V m
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤))) ≫ (e.hom ≫ U.ι) =
      (Scheme.isoSpec V.left).inv ≫ V.hom := by
  intro algRS
  exact (congrArg
    (fun φ : R →+* Γ(V.left, ⊤) => Spec.map (CommRingCat.ofHom φ) ≫ (e.hom ≫ U.ι))
    (integralAffineChartCoordinateAlgebra_algebraMap R U e V m)).trans
      (integralAffineChartSource_coordinate_comp R U e V m)

/-- After normalization on the fixed coordinate spectrum of the original
source, the actual slice component reads the source's original divisor.
Only the chart factorization is used to construct the normalization. -/
theorem affineChartDivisorGenericUnitIso_originalSource (hR : ¬ IsField R) :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    let A := integralAffineChartSource R U e V m
    let S : CommRingCat.{u} := Γ(V.left, ⊤)
    let _ : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
    let algRS : Algebra R S := integralAffineChartCoordinateAlgebra R U e V m
    let _ : Algebra.Etale R S := integralAffineChartCoordinateAlgebra_etale R U e V m
    let algRE : Algebra R (FractionRing S) :=
      integralAffineChartCoordinateAmbientAlgebra R U e V m
    let _ : @IsScalarTower R S (FractionRing S) algRS.toSMul
        (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
      integralAffineChartCoordinateAmbientAlgebra_isScalarTower R U e V m
    let algKE : Algebra (FractionRing R) (FractionRing S) :=
      integralAffineChartCoordinateFractionFieldAlgebra R U e V m
    let _ : @IsScalarTower R (FractionRing R) (FractionRing S)
        (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
      integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower R U e V m
    let q : Spec S ⟶ X := (Scheme.isoSpec V.left).inv ≫ V.hom
    let hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι) = q :=
      integralAffineChartCoordinate_comp R U e V m
    let p : Scheme.Etale.mk q ⟶ V :=
      (affineCoordinateSourceIso V).hom
    let DX := closedPointDivisorSheaf X
    let a : (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj DX ≅
        (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) :=
      affineChartDivisorGenericUnitIso R U e hR
    let k : (etaleRestriction q AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
        affineEtaleFractionRingUnitQuotient S :=
      affineChartGenericUnitSourceIso R (e.hom ≫ U.ι) S q hq
    let l : (Over.forget (Scheme.Etale.mk (e.hom ≫ U.ι))).op ⋙ DX.obj ⟶
        (Over.forget (Scheme.Etale.mk (e.hom ≫ U.ι))).op ⋙ (etaleGenericUnitQuotient X).obj :=
      etaleRestrictionHomToSlice (F := DX) (G := (etaleGenericUnitQuotient X))
        (Scheme.Etale.mk (e.hom ≫ U.ι)) a.hom
    ∀ (s : DX.obj.obj (op V)),
      k.hom.hom.app (op ((zariskiToEtale (Spec S)).obj ⊤))
        ((etaleRestrictionTopObjectSectionIso q (etaleGenericUnitQuotient X)).inv
          ((etaleGenericUnitQuotient X).obj.map p.op (l.app (op (Over.mk m)) s))) =
      divisorGenericUnitQuotientGlobalSectionEquiv S
        (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
          (affineChartDivisorSourceSection R U e S q hq
            (DX.obj.map p.op s))) := by
  intro hShape A S hS algRS hE algRE hRS algKE hKS q hq p DX a k l s
  let c : Over.mk m ≅
      (etaleSliceEquiv (Scheme.Etale.mk (e.hom ≫ U.ι))).inverse.obj A.obj :=
    (etaleSliceEquiv (Scheme.Etale.mk (e.hom ≫ U.ι))).unitIso.app (Over.mk m)
  let E : A.obj ≅ affineEtaleSpecObject (R := R) (S := S) :=
    integralAffineCoordinateEtaleObjIso R A
  let j := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let r := (etalePostcompose (e.hom ≫ U.ι)).map E.inv
  let tS : DX.obj.obj (op ((etalePostcompose (e.hom ≫ U.ι)).obj
      (affineEtaleSpecObject (R := R) (S := S)))) := DX.obj.map r.op (DX.obj.map c.inv.left.op s)
  have hEinv : E.inv.left = (Scheme.isoSpec V.left).inv := by
    rfl
  have hleft : r ≫ c.inv.left = (affineChartDivisorSourceObjectIso R U e S q hq).hom ≫ p := by
    apply MorphismProperty.Over.Hom.ext
    have hc : c.inv.left.left = 𝟙 V.left := by rfl
    exact (congrArg₂
      (fun (f : Spec S ⟶ V.left) (g : V.left ⟶ V.left) => f ≫ g)
      hEinv hc).trans
        ((Category.comp_id (Scheme.isoSpec V.left).inv).trans
          (Category.id_comp (Scheme.isoSpec V.left).inv).symm)
  have hright : (affineChartDivisorSourceObjectIso R U e S q hq).inv ≫ r = p ≫ c.hom.left := by
    apply MorphismProperty.Over.Hom.ext
    have hc : c.hom.left.left = 𝟙 V.left := by rfl
    exact (congrArg (fun f : Spec S ⟶ V.left =>
      𝟙 (Spec S) ≫ f) hEinv).trans
        ((Category.id_comp (Scheme.isoSpec V.left).inv).trans
          (((Category.comp_id (Scheme.isoSpec V.left).inv).symm).trans
            (congrArg (fun g : V.left ⟶ V.left =>
              (Scheme.isoSpec V.left).inv ≫ g) hc.symm)))
  have hD : tS =
      DX.obj.map (affineChartDivisorSourceObjectIso R U e S q hq).hom.op (DX.obj.map p.op s) := by
    exact map_op_comp_eq_apply DX.obj r c.inv.left
      (affineChartDivisorSourceObjectIso R U e S q hq).hom p hleft s
  have hl : l =
      etaleRestrictionHomToSlice (F := DX) (G := (etaleGenericUnitQuotient X))
        (Scheme.Etale.mk (e.hom ≫ U.ι)) a.hom := rfl
  have hwhisker :
      Functor.whiskerLeft (etaleSliceEquiv (Scheme.Etale.mk (e.hom ≫ U.ι))).inverse.op l =
      a.hom.hom :=
    (congrArg (Functor.whiskerLeft (etaleSliceEquiv (Scheme.Etale.mk (e.hom ≫ U.ι))).inverse.op)
      hl).trans (etaleRestrictionHomToSlice_whisker (F := DX) (G := (etaleGenericUnitQuotient X))
        (Scheme.Etale.mk (e.hom ≫ U.ι)) a.hom)
  have hQ := slice_section_transport (X := X) (F := DX) (G := (etaleGenericUnitQuotient X))
    (e.hom ≫ U.ι) a.hom l hwhisker (Over.mk m) A.obj c
    (V := Scheme.Etale.mk q)
    (W := (etalePostcompose (e.hom ≫ U.ι)).obj (affineEtaleSpecObject (R := R) (S := S)))
    p r (affineChartDivisorSourceObjectIso R U e S q hq) hright s
  have hs := affineChartDivisorGenericUnitIso_coordinate R U e hR A (DX.obj.map c.inv.left.op s)
  have ht := affineChartGenericUnitSourceIso_transport R U e S q hq
    ((etaleGenericUnitQuotient X).obj.map r.op
      (a.hom.hom.app (op A.obj) (DX.obj.map c.inv.left.op s)))
  have hd : affineChartDivisorSourceSection R U e S (j ≫ (e.hom ≫ U.ι)) rfl tS =
      affineChartDivisorSourceSection R U e S q hq (DX.obj.map p.op s) := by
    have hDback : DX.obj.map (affineChartDivisorSourceObjectIso R U e S q hq).inv.op tS =
        DX.obj.map p.op s :=
      (congrArg (fun z =>
        DX.obj.map (affineChartDivisorSourceObjectIso R U e S q hq).inv.op z) hD).trans
          (map_op_iso_cancel_apply DX.obj (affineChartDivisorSourceObjectIso R U e S q hq)
            (DX.obj.map p.op s))
    exact (affineChartDivisorSourceSection_transport R U e S q hq tS).symm.trans
      (congrArg (affineChartDivisorSourceSection R U e S q hq) hDback)
  have hk : k = affineChartGenericUnitSourceIso R (e.hom ≫ U.ι) S q hq := rfl
  have ha : a = affineChartDivisorGenericUnitIso R U e hR := rfl
  have hr : r = (etalePostcompose (e.hom ≫ U.ι)).map
      (integralAffineCoordinateEtaleObjIso R A).inv := rfl
  have hsection := congrArg₂
    (fun (rr : (etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S)) ⟶
          (etalePostcompose (e.hom ≫ U.ι)).obj A.obj)
      (aa : (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj DX ≅
        (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)) =>
      (etaleGenericUnitQuotient X).obj.map rr.op
        (aa.hom.hom.app (op A.obj) (DX.obj.map c.inv.left.op s))) hr ha
  have hA := congrArg
    (fun z : (etaleGenericUnitQuotient X).obj.obj (op ((etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S)))) =>
      (affineChartGenericUnitSourceIso R (e.hom ≫ U.ι) S
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι))
        rfl).hom.hom.app (op ((zariskiToEtale (Spec S)).obj ⊤))
          ((etaleRestrictionTopObjectSectionIso
            (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι))
            (etaleGenericUnitQuotient X)).inv z)) hsection
  have hk0 :
      affineChartGenericUnitSourceIso R (e.hom ≫ U.ι) S
          (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl =
        (let S' : Type u := Γ(A.obj.left, ⊤)
         let _ : CommRing S' := inferInstance
         let _ : IsDedekindDomain S' := integralAffineCoordinate_isDedekindDomain R A
         let algRS' : Algebra R S' := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
         let _ : Algebra.Etale R S' :=
           RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
         let algRE' : Algebra R (FractionRing S') :=
           ((algebraMap S' (FractionRing S')).comp (algebraMap R S')).toAlgebra
         let _ : @IsScalarTower R S' (FractionRing S') algRS'.toSMul
             (inferInstance : Algebra S' (FractionRing S')).toSMul algRE'.toSMul :=
           IsScalarTower.of_algebraMap_eq (fun _ => rfl)
         let algKE' : Algebra (FractionRing R) (FractionRing S') :=
           integralAffineCoordinateFractionFieldAlgebra R A
         let _ : @IsScalarTower R (FractionRing R) (FractionRing S')
             (inferInstance : Algebra R (FractionRing R)).toSMul algKE'.toSMul
             algRE'.toSMul := integralAffineCoordinateFractionFieldAlgebra_isScalarTower R A
         affineChartGenericUnitSourceIso R (e.hom ≫ U.ι) S'
           (Spec.map (CommRingCat.ofHom (algebraMap R S')) ≫ (e.hom ≫ U.ι)) rfl) := rfl
  have hK0 := congrArg
    (fun b : (etaleRestriction
          (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι))
          AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
        affineEtaleFractionRingUnitQuotient S =>
      b.hom.hom.app (op ((zariskiToEtale (Spec S)).obj ⊤))
        ((etaleRestrictionTopObjectSectionIso
          (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι))
          (etaleGenericUnitQuotient X)).inv
          ((etaleGenericUnitQuotient X).obj.map
            ((etalePostcompose (e.hom ≫ U.ι)).map
              (integralAffineCoordinateEtaleObjIso R A).inv).op
            ((affineChartDivisorGenericUnitIso R U e hR).hom.hom.app
              (op A.obj) (DX.obj.map c.inv.left.op s))))) hk0
  have h1 := congrArg₂
    (fun (b : (etaleRestriction q AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
        affineEtaleFractionRingUnitQuotient S)
      (z : (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk q))) =>
      b.hom.hom.app (op ((zariskiToEtale (Spec S)).obj ⊤))
        ((etaleRestrictionTopObjectSectionIso q (etaleGenericUnitQuotient X)).inv z)) hk hQ
  have h2 := h1.trans ht
  have h3 := h2.trans hA
  have h4 := h3.trans hK0
  have h5 := h4.trans hs
  have h6 := h5.trans (congrArg
    (fun z => divisorGenericUnitQuotientGlobalSectionEquiv S
      (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR z)) hd)
  exact h6

end EtaleCohomology.DivisorGenericUnitGlobal
