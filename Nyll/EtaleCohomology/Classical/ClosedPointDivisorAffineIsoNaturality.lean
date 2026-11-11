/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOpenAffine
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorRestrictionCoefficients
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSectionExt
public import Nyll.EtaleCohomology.Sites.EtaleIntegralAffineCover
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Original divisor charts transported along a scheme isomorphism

The original divisor comparison along an affine chart commutes with an
arbitrary scheme isomorphism of the ambient schemes. The proof checks the
actual residue-fiber coefficients on affine sources and then uses sheaf
separatedness on the original small site.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology.DivisorGenericUnitGlobal

private theorem divisorCoefficient_map
    {X : Scheme.{u}} (x : closedPoints X) (V W : X.Etale) (m : V ⟶ W)
    (s : (closedPointDivisorSheaf X).obj.obj (op W))
    (z : closedPointResidueFiber X x V) :
    closedPointDivisorSummandSectionsAddEquiv X x V
      ((closedPointDivisorSheafComponentProjection X x).hom.app (op V)
        ((closedPointDivisorSheaf X).obj.map m.op s)) z =
    closedPointDivisorSummandSectionsAddEquiv X x W
      ((closedPointDivisorSheafComponentProjection X x).hom.app (op W) s)
      ⟨m.left z.1, by
        have hm := congrArg (fun f => f z.1)
          (MorphismProperty.Over.w
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
        exact hm.trans z.2⟩ := by
  let p := closedPointDivisorSheafComponentProjection X x
  have hp := ConcreteCategory.congr_hom (p.hom.naturality m.op) s
  change p.hom.app (op V) ((closedPointDivisorSheaf X).obj.map m.op s) =
    (closedPointDivisorSummand X x).obj.map m.op (p.hom.app (op W) s) at hp
  exact (congrArg (fun t => closedPointDivisorSummandSectionsAddEquiv X x V t z) hp).trans
    (closedPointDivisorSummandSectionsAddEquiv_naturality X x V W m
      (p.hom.app (op W) s) z)

variable (R : Type u) [CommRing R]
  {Y X : Scheme.{u}} [JacobsonSpace Y] [JacobsonSpace X]
  (e : Y ≅ X) (q : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion q]

private theorem affineOpenDivisorIso_iso_naturality_app
    (V : (Spec (CommRingCat.of R)).Etale) [IsAffine V.left] :
    (((etaleRestriction q AddCommGrpCat.{u}).map
        (closedPointDivisorIsoRestrictionIso e).hom ≫
      (affineOpenDivisorIso R q).hom).hom.app (op V)) =
    (((etaleRestrictionCompIso q e.hom AddCommGrpCat.{u}).hom.app
        (closedPointDivisorSheaf X) ≫
      (affineOpenDivisorIso R (q ≫ e.hom)).hom).hom.app (op V)) := by
  let DX := closedPointDivisorSheaf X
  let VY := (etalePostcompose q).obj V
  let Vn := (etalePostcompose e.hom).obj VY
  let Vd := (etalePostcompose (q ≫ e.hom)).obj V
  let c : Vd ≅ Vn :=
    (MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (f := q) inferInstance (g := e.hom) inferInstance).app V
  have hqc : QuasiCompact (terminal.from V.left) :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact V.left).mp inferInstance
  have hc : ((etaleRestrictionCompIso q e.hom AddCommGrpCat.{u}).hom.app DX).hom.app
      (op V) = DX.obj.map c.hom.op := by
    change DX.obj.map c.hom.op ≫ 𝟙 _ = _
    exact Category.comp_id _
  apply ConcreteCategory.hom_ext
  intro s
  apply closedPointDivisorSection_ext_of_quasiCompact (Spec (CommRingCat.of R)) V
  intro y z
  let yY : closedPoints Y := affineOpenClosedPoint R q y
  have hy : q y.1 = yY.1 := affineOpenClosedPoint_coe R q y
  let x : closedPoints X := (e.hom.homeomorph.sets
    e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv yY
  have hx : (q ≫ e.hom) y.1 = x.1 := congrArg e.hom hy
  let zY : closedPointResidueFiber Y yY VY :=
    ⟨z.1, (congrArg q z.2).trans hy⟩
  let zX : closedPointResidueFiber X x Vd :=
    ⟨z.1, (congrArg (q ≫ e.hom) z.2).trans hx⟩
  let t := (closedPointDivisorIsoRestrictionIso e).hom.hom.app (op VY) s
  have hl := affineOpenDivisorIso_coefficient R q y yY hy V t z
  have he := closedPointDivisorIsoRestrictionIso_coefficient e yY VY s zY
  have hr := affineOpenDivisorIso_coefficient R (q ≫ e.hom) y x hx V
    (DX.obj.map c.hom.op s) z
  have hn := divisorCoefficient_map x Vd Vn c.hom s zX
  change closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) y V
      ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
        (op V) ((affineOpenDivisorIso R q).hom.hom.app (op V) t)) z =
    closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) y V
      ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
        (op V) ((affineOpenDivisorIso R (q ≫ e.hom)).hom.hom.app (op V)
          (((etaleRestrictionCompIso q e.hom AddCommGrpCat.{u}).hom.app DX).hom.app
            (op V) s))) z
  rw [hc]
  exact (hl.trans he).trans (hr.trans hn).symm

/-- The actual original divisor-sheaf comparisons commute with carrying
one affine chart along a scheme isomorphism. -/
theorem affineOpenDivisorIso_iso_naturality [IsDedekindDomain R] :
    (etaleRestriction q AddCommGrpCat.{u}).map
        (closedPointDivisorIsoRestrictionIso e).hom ≫
      (affineOpenDivisorIso R q).hom =
    (etaleRestrictionCompIso q e.hom AddCommGrpCat.{u}).hom.app
        (closedPointDivisorSheaf X) ≫
      (affineOpenDivisorIso R (q ≫ e.hom)).hom := by
  let F := (etaleRestriction q AddCommGrpCat.{u}).obj
    ((etaleRestriction e.hom AddCommGrpCat.{u}).obj (closedPointDivisorSheaf X))
  let G := closedPointDivisorSheaf (Spec (CommRingCat.of R))
  let a : F ⟶ G := (etaleRestriction q AddCommGrpCat.{u}).map
    (closedPointDivisorIsoRestrictionIso e).hom ≫ (affineOpenDivisorIso R q).hom
  let b : F ⟶ G := (etaleRestrictionCompIso q e.hom AddCommGrpCat.{u}).hom.app
    (closedPointDivisorSheaf X) ≫ (affineOpenDivisorIso R (q ≫ e.hom)).hom
  apply (sheafToPresheaf (Spec (CommRingCat.of R)).smallEtaleTopology
    AddCommGrpCat.{u}).map_injective
  apply NatTrans.ext
  funext V0
  obtain ⟨V⟩ := V0
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) (Spec (CommRingCat.of R))
  obtain ⟨A, l, hA, hcover⟩ :=
    exists_integral_affine_etale_cover_of_dedekind_chart R (𝟙 _) V (hT.from V)
  apply G.property.hom_ext_ofArrows l hcover
  intro z
  have hAffine : IsAffine (A z).left := (hA z).1
  have hlocal := affineOpenDivisorIso_iso_naturality_app R e q (A z)
  exact (a.hom.naturality (l z).op).symm.trans
    ((congrArg (fun t => F.obj.map (l z).op ≫ t) hlocal).trans
      (b.hom.naturality (l z).op))

end EtaleCohomology.DivisorGenericUnitGlobal
