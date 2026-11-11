/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothAffineDedekind
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitAffineOverlap
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleIntegralAffineCover
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Topology.JacobsonSpace

/-!
# The original global divisor and generic-unit quotient sheaves

The actual affine comparisons agree on integral affine sources. Covering
an arbitrary source by such schemes and applying sheaf separatedness gives
agreement on every overlap in the original small étale site. These maps
then glue to an isomorphism for a smooth integral curve over a field.

Every chart and every compatibility statement in this construction is
derived from the original curve. The global map retains the original local
comparison on each nonempty affine open.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology

namespace DivisorGenericUnitGlobal

private theorem presheafHom_component_naturality
    {Cat : Type*} [Category Cat] (F G : Catᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : Cat) (f : (presheafHom F G).obj (op U))
    {V W : Cat} (m : V ⟶ U) (l : W ⟶ V) :
    F.map l.op ≫ f.app (op (Over.mk (l ≫ m))) =
      f.app (op (Over.mk m)) ≫ G.map l.op := by
  exact f.naturality
    (Over.homMk (U := Over.mk (l ≫ m)) (V := Over.mk m) l rfl).op

private theorem presheafHom_restriction_eq_of_components
    {Cat : Type*} [Category Cat] (F G : Catᵒᵖ ⥤ AddCommGrpCat.{u})
    {U W V : Cat} (mR : V ⟶ U) (mB : V ⟶ W)
    (a : (presheafHom F G).obj (op U)) (b : (presheafHom F G).obj (op W))
    (h : ∀ (Y : Cat) (nR : Y ⟶ U) (nB : Y ⟶ W),
      a.app (op (Over.mk nR)) = b.app (op (Over.mk nB))) :
    (presheafHom F G).map mR.op a = (presheafHom F G).map mB.op b := by
  apply NatTrans.ext
  funext T0
  obtain ⟨T⟩ := T0
  obtain ⟨Y, t, rfl⟩ := Over.mk_surjective T
  rw [presheafHom_map_app t mR (t ≫ mR) rfl,
    presheafHom_map_app t mB (t ≫ mB) rfl]
  exact h Y (t ≫ mR) (t ≫ mB)

private theorem presheafHom_components_eq_of_cover
    {Cat : Type*} [Category Cat] (J : GrothendieckTopology Cat)
    (F G : Sheaf J AddCommGrpCat.{u}) {U W V : Cat}
    (mR : V ⟶ U) (mB : V ⟶ W)
    (a : (presheafHom F.obj G.obj).obj (op U))
    (b : (presheafHom F.obj G.obj).obj (op W))
    {ι : Type*} (A : ι → Cat) (l : ∀ i, A i ⟶ V)
    (hcover : Sieve.ofArrows A l ∈ J V)
    (h : ∀ i (nR : A i ⟶ U) (nB : A i ⟶ W),
      a.app (op (Over.mk nR)) = b.app (op (Over.mk nB))) :
    a.app (op (Over.mk mR)) = b.app (op (Over.mk mB)) := by
  apply G.property.hom_ext_ofArrows l hcover
  intro i
  have ha := presheafHom_component_naturality F.obj G.obj U a mR (l i)
  have hb := presheafHom_component_naturality F.obj G.obj W b mB (l i)
  exact ha.symm.trans
    ((congrArg (fun z => F.obj.map (l i).op ≫ z)
      (h i (l i ≫ mR) (l i ≫ mB))).trans hb)

/-- Sheaf separatedness extends the proven integral affine overlap
calculation to every common source of two actual Dedekind charts. -/
theorem affineChartDivisorGenericUnitIso_overlap
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (U W : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (d : Spec (CommRingCat.of B) ≅ (W : Scheme))
    (hR : ¬ IsField R) (hB : ¬ IsField B)
    (V : X.Etale)
    (mR : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
    (mB : V ⟶ Scheme.Etale.mk (d.hom ≫ W.ι)) :
    (etaleRestrictionHomToSlice
        (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
        (Scheme.Etale.mk (e.hom ≫ U.ι))
        (affineChartDivisorGenericUnitIso R U e hR).hom).app (op (Over.mk mR)) =
      (etaleRestrictionHomToSlice
        (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
        (Scheme.Etale.mk (d.hom ≫ W.ι))
        (affineChartDivisorGenericUnitIso B W d hB).hom).app (op (Over.mk mB)) := by
  let F := closedPointDivisorSheaf X
  let G := etaleGenericUnitQuotient X
  let a := etaleRestrictionHomToSlice (F := F) (G := G) (Scheme.Etale.mk (e.hom ≫ U.ι))
    (affineChartDivisorGenericUnitIso R U e hR).hom
  let b := etaleRestrictionHomToSlice (F := F) (G := G) (Scheme.Etale.mk (d.hom ≫ W.ι))
    (affineChartDivisorGenericUnitIso B W d hB).hom
  obtain ⟨A, l, hA, hcover⟩ :=
    exists_integral_affine_etale_cover_of_dedekind_chart R (e.hom ≫ U.ι) V mR
  have hlocal := fun (x : V.left)
      (nR : A x ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
      (nB : A x ⟶ Scheme.Etale.mk (d.hom ≫ W.ι)) =>
    let _ : IsAffine (A x).left := (hA x).1
    let _ : IsIntegral (A x).left := (hA x).2
    affineChartDivisorGenericUnitIso_affine_overlap R B U W e d hR hB (A x) nR nB
  have h := presheafHom_components_eq_of_cover X.smallEtaleTopology F G
    mR mB a b A l hcover hlocal
  exact h

/-- The original local maps give equal sections of the sheaf of morphisms
after restriction to any common object of the two charts. -/
theorem affineChartDivisorGenericUnitIso_overlap_restriction
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (U W : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (d : Spec (CommRingCat.of B) ≅ (W : Scheme))
    (hR : ¬ IsField R) (hB : ¬ IsField B)
    (V : X.Etale)
    (mR : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
    (mB : V ⟶ Scheme.Etale.mk (d.hom ≫ W.ι)) :
    (presheafHom (closedPointDivisorSheaf X).obj (etaleGenericUnitQuotient X).obj).map
        mR.op (etaleRestrictionHomToSlice (Scheme.Etale.mk (e.hom ≫ U.ι))
          (affineChartDivisorGenericUnitIso R U e hR).hom) =
      (presheafHom (closedPointDivisorSheaf X).obj (etaleGenericUnitQuotient X).obj).map
        mB.op (etaleRestrictionHomToSlice (Scheme.Etale.mk (d.hom ≫ W.ι))
          (affineChartDivisorGenericUnitIso B W d hB).hom) := by
  have hsource := fun (Y : X.Etale)
      (nR : Y ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
      (nB : Y ⟶ Scheme.Etale.mk (d.hom ≫ W.ι)) =>
    affineChartDivisorGenericUnitIso_overlap R B U W e d hR hB Y nR nB
  have h := presheafHom_restriction_eq_of_components
    (closedPointDivisorSheaf X).obj (etaleGenericUnitQuotient X).obj mR mB
    (etaleRestrictionHomToSlice (Scheme.Etale.mk (e.hom ≫ U.ι))
      (affineChartDivisorGenericUnitIso R U e hR).hom)
    (etaleRestrictionHomToSlice (Scheme.Etale.mk (d.hom ≫ W.ι))
      (affineChartDivisorGenericUnitIso B W d hB).hom) hsource
  exact h

/-- Nonempty affine opens, with their original inclusion in the scheme. -/
abbrev NonemptyAffineOpen (X : Scheme.{u}) : Type u :=
  {U : X.Opens // IsAffineOpen U ∧ Nonempty U}

/-- The actual coordinate spectrum of a nonempty affine open, regarded as
an object of the original small étale site. -/
def nonemptyAffineEtaleChart {X : Scheme.{u}} (U : NonemptyAffineOpen X) : X.Etale :=
  Scheme.Etale.mk (U.property.1.isoSpec.inv ≫ U.val.ι)

/-- The actual coordinate spectra of nonempty affine opens cover the
original scheme and hence the terminal object of its small étale site. -/
theorem nonemptyAffineEtaleChart_coversTop (X : Scheme.{u}) :
    X.smallEtaleTopology.CoversTop (nonemptyAffineEtaleChart (X := X)) := by
  apply smallEtale_coversTop_of_jointly_surjective
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let A : NonemptyAffineOpen X := ⟨U, hU, ⟨⟨x, hxU⟩⟩⟩
  refine ⟨A, hU.isoSpec.hom (⟨x, hxU⟩ : U), ?_⟩
  have hx : hU.isoSpec.inv (hU.isoSpec.hom (⟨x, hxU⟩ : U)) =
      (⟨x, hxU⟩ : U) := by
    change (hU.isoSpec.hom ≫ hU.isoSpec.inv) (⟨x, hxU⟩ : U) = _
    rw [hU.isoSpec.hom_inv_id]
    rfl
  change U.ι (hU.isoSpec.inv (hU.isoSpec.hom (⟨x, hxU⟩ : U))) = x
  rw [hx]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]

/-- The existing native chart comparison on a nonempty affine open of the
smooth curve, with its Dedekind and Jacobson properties actually proved. -/
def smoothCurveChartDivisorGenericUnitIso (U : NonemptyAffineOpen X) :
    (etaleRestriction (nonemptyAffineEtaleChart U).hom AddCommGrpCat.{u}).obj
        (closedPointDivisorSheaf X) ≅
      (etaleRestriction (nonemptyAffineEtaleChart U).hom AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X) := by
  have hSmooth : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hJacobson : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hNonempty : Nonempty U.val := U.property.2
  have hDedekind : IsDedekindDomain Γ(X, U.val) :=
    SmoothOfRelativeDimension.isDedekindDomain_sections f U.property.1
  exact affineChartDivisorGenericUnitIso Γ(X, U.val) U.val U.property.1.isoSpec.symm
    (SmoothOfRelativeDimension.not_isField_sections f U.property.1)

/-- Compatibility of the actual chart maps is proved on every original
overlap, using the integral affine cover calculation above. -/
theorem smoothCurveChartDivisorGenericUnitIso_compatible :
    (etaleRestrictionHomFamily nonemptyAffineEtaleChart
      (fun U : NonemptyAffineOpen X =>
        (smoothCurveChartDivisorGenericUnitIso f U).hom)).IsCompatible := by
  have hSmooth : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hJacobson : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro V U W mR mB
  have hUNonempty : Nonempty U.val := U.property.2
  have hWNonempty : Nonempty W.val := W.property.2
  have hUDedekind : IsDedekindDomain Γ(X, U.val) :=
    SmoothOfRelativeDimension.isDedekindDomain_sections f U.property.1
  have hWDedekind : IsDedekindDomain Γ(X, W.val) :=
    SmoothOfRelativeDimension.isDedekindDomain_sections f W.property.1
  exact affineChartDivisorGenericUnitIso_overlap_restriction
    Γ(X, U.val) Γ(X, W.val) U.val W.val
    U.property.1.isoSpec.symm W.property.1.isoSpec.symm
    (SmoothOfRelativeDimension.not_isField_sections f U.property.1)
    (SmoothOfRelativeDimension.not_isField_sections f W.property.1) V mR mB

end DivisorGenericUnitGlobal

open DivisorGenericUnitGlobal

/-- The original closed-point divisor sheaf of a smooth integral curve
is the actual cokernel of units in generic units on its small étale site. -/
def smoothCurveClosedPointDivisorGenericUnitIso
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f] :
    closedPointDivisorSheaf X ≅ etaleGenericUnitQuotient X :=
  etaleGlueIso nonemptyAffineEtaleChart (nonemptyAffineEtaleChart_coversTop X)
    (smoothCurveChartDivisorGenericUnitIso f)
    (smoothCurveChartDivisorGenericUnitIso_compatible f)

/-- The global comparison keeps the original native chart map on every
nonempty affine open of the smooth curve. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_hom_restrict
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]
    (U : NonemptyAffineOpen X) :
    (etaleRestriction (nonemptyAffineEtaleChart U).hom AddCommGrpCat.{u}).map
        (smoothCurveClosedPointDivisorGenericUnitIso f).hom =
      (smoothCurveChartDivisorGenericUnitIso f U).hom :=
  etaleGlueIso_hom_restrict nonemptyAffineEtaleChart (nonemptyAffineEtaleChart_coversTop X)
    (smoothCurveChartDivisorGenericUnitIso f)
    (smoothCurveChartDivisorGenericUnitIso_compatible f) U

end EtaleCohomology
