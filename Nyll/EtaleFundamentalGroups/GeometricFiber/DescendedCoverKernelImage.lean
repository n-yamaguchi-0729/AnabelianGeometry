/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GlobalModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverImage
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExactSequence

/-!
# The actual arithmetic kernel of a recovered finite-stage cover

A finite-stage recovery isomorphism identifies the standard constant extension
of the descended cover with the original connected cover. Transporting the
same chosen geometric point through this actual scheme isomorphism gives a
strict pointed square. Consequently the image of the descended arithmetic
kernel is exactly the image of the prescribed geometric subgroup.

-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

/-- The literal coefficient projection used by the finite-stage descent owner. -/
def finiteStageCoefficientMap
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
    (E : IntermediateField k κ) (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f :=
  Limits.pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])

/-- Recovery over the literal coefficient projection also recovers the
standard constant extension of the source scheme, with its covering map. -/
private theorem exists_finiteStageCoverRecoveryIso
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
    (E : IntermediateField k κ) (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (N : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))
    (W : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f))
    (rec : (FiniteEtale.pullback (finiteStageCoefficientMap k κ E X f)).obj N ≅ W) :
    let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let ψ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let c : N.left ⟶ Spec (.of E) := N.hom ≫ Limits.pullback.fst φE f
    let u := coefficientModelMap ψ (Limits.pullback.fst φE f) N.hom ≫
      (constantFieldTowerIso k κ E X f).hom
    ∃ R : Limits.pullback ψ c ≅ W.left, R.hom ≫ W.hom = u := by
  intro φE ψ c u
  let d := finiteStageCoefficientMap k κ E X f
  let T := constantFieldTowerIso k κ E X f
  have hT : T.hom ≫ d = Limits.pullback.snd ψ (Limits.pullback.fst φE f) :=
    constantFieldTowerIso_hom_coefficientMap k κ E X f
  have hb := coefficientBaseChange_isPullback ψ (Limits.pullback.fst φE f) N.hom
  have hp : IsPullback u (Limits.pullback.snd ψ c) d N.hom := by
    apply hb.of_iso (Iso.refl _) T (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · exact (Category.comp_id _).trans hT.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  let eW : ((FiniteEtale.pullback d).obj N).left ≅ W.left :=
    (FiniteEtale.forget _ ⋙ Over.forget _).mapIso rec
  have heW : eW.hom ≫ W.hom = Limits.pullback.snd N.hom d := rec.hom.w
  refine ⟨hp.flip.isoPullback ≪≫ eW, ?_⟩
  change (hp.flip.isoPullback.hom ≫ eW.hom) ≫ W.hom = u
  calc
    (hp.flip.isoPullback.hom ≫ eW.hom) ≫ W.hom =
        hp.flip.isoPullback.hom ≫ (eW.hom ≫ W.hom) := Category.assoc _ _ _
    _ = hp.flip.isoPullback.hom ≫ Limits.pullback.snd N.hom d :=
      congrArg (fun h => hp.flip.isoPullback.hom ≫ h) heW
    _ = u := hp.flip.isoPullback_hom_snd

end EtaleFundamentalGroups

namespace AlgebraicGeometry.FiniteEtale

open EtaleFundamentalGroups

/-- An actual scheme isomorphism onto a chosen finite cover preserves its
pointed image. Abstract source schemes keep the calculation opaque to the
larger constant-field recovery construction. -/
private theorem pointedMap_range_of_schemeIso_cover
    {S Y : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (W : FiniteEtale S) [IsConnected W]
    (w : (fiber xi).obj W) (R : Y ≅ W.left)
    (x : Spec (.of Ω) ⟶ Y) (u : Y ⟶ S)
    (hgeo : x ≫ u = xi) (hu : R.hom ≫ W.hom = u)
    (hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left) :
    (pointedFundamentalGroupHom u x xi hgeo).toMonoidHom.range =
      MulAction.stabilizer π₁ᵉᵗ(xi) w := by
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let g := fiberObjEquivHom xi W w
  let xiW : Spec (.of Ω) ⟶ W.left := g.left
  have hxiW : xiW ≫ W.hom = xi := g.w
  have hx : x ≫ R.hom = xiW := hxR
  let iG : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(xi) :=
    pointedFundamentalGroupHom u x xi hgeo
  let iW : π₁ᵉᵗ(xiW) →ₜ* π₁ᵉᵗ(xi) :=
    pointedFundamentalGroupHom W.hom xiW xi hxiW
  let eR : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(xiW) :=
    pointedFundamentalGroupHom R.hom x xiW hx
  have hWR : iW.comp eR = iG := by
    simpa only [iW, eR, iG, hu] using
      (pointedFundamentalGroupHom_comp R.hom W.hom x xiW xi hx hxiW)
  have hy : xiW ≫ R.inv = x := by
    rw [← hx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let sR : π₁ᵉᵗ(xiW) →ₜ* π₁ᵉᵗ(x) :=
    pointedFundamentalGroupHom R.inv xiW x hy
  have hright : eR.comp sR = ContinuousMonoidHom.id π₁ᵉᵗ(xiW) := by
    change (pointedFundamentalGroupHom R.hom x xiW hx).comp
      (pointedFundamentalGroupHom R.inv xiW x hy) = _
    rw [pointedFundamentalGroupHom_comp]
    simpa only [Iso.inv_hom_id] using (pointedFundamentalGroupHom_id xiW)
  have heR : Function.Surjective eR := by
    intro v
    exact ⟨sR v, DFunLike.congr_fun hright v⟩
  have hG : iG.toMonoidHom.range = iW.toMonoidHom.range := by
    ext b
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨eR v, DFunLike.congr_fun hWR v⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨v', rfl⟩ := heR v
      exact ⟨v', (DFunLike.congr_fun hWR v').symm⟩
  have hw : (fiberObjEquivHom xi W).symm (Over.homMk xiW hxiW) = w := by
    apply (fiberObjEquivHom xi W).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have hW : iW.toMonoidHom.range = MulAction.stabilizer π₁ᵉᵗ(xi) w := by
    rw [pointedFundamentalGroupHom_range_eq_stabilizer, hw]
  exact hG.trans hW

/-- A pointed commutative square transports an exact vertical image through
its horizontal map. This uses only canonical functoriality and subgroup maps;
the arithmetic exact sequence is supplied at the actual application site. -/
private theorem pointedSquare_map_of_kernel_eq_range
    {YK XK Y X : Scheme.{u}}
    {Ω : Type u} [Field Ω]
    (pY : YK ⟶ Y) (pX : XK ⟶ X) (u : YK ⟶ XK) (a : Y ⟶ X)
    (x : Spec (.of Ω) ⟶ YK) (xi : Spec (.of Ω) ⟶ XK)
    (hgeo : x ≫ u = xi)
    (hpoint : (x ≫ pY) ≫ a = xi ≫ pX)
    (hscheme : u ≫ pX = pY ≫ a)
    (K : Subgroup π₁ᵉᵗ(x ≫ pY))
    (hK : K = (fundamentalGroupHom pY x).toMonoidHom.range) :
    K.map (pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ pX) hpoint).toMonoidHom =
      (pointedFundamentalGroupHom u x xi hgeo).toMonoidHom.range.map
        (fundamentalGroupHom pX xi).toMonoidHom := by
  let J : π₁ᵉᵗ(x ≫ pY) →ₜ* π₁ᵉᵗ(xi ≫ pX) :=
    pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ pX) hpoint
  let iY : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(x ≫ pY) := fundamentalGroupHom pY x
  let iX : π₁ᵉᵗ(xi) →ₜ* π₁ᵉᵗ(xi ≫ pX) := fundamentalGroupHom pX xi
  let iG : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(xi) :=
    pointedFundamentalGroupHom u x xi hgeo
  have hsq : J.comp iY = iX.comp iG := by
    change (pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ pX) hpoint).comp
        (pointedFundamentalGroupHom pY x (x ≫ pY) rfl) =
      (pointedFundamentalGroupHom pX xi (xi ≫ pX) rfl).comp
        (pointedFundamentalGroupHom u x xi hgeo)
    rw [pointedFundamentalGroupHom_comp, pointedFundamentalGroupHom_comp]
    simp only [hscheme]
  have hsq' : J.toMonoidHom.comp iY.toMonoidHom =
      iX.toMonoidHom.comp iG.toMonoidHom :=
    congrArg (fun h : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(xi ≫ pX) => h.toMonoidHom) hsq
  have hK' : K = iY.toMonoidHom.range := hK
  change K.map J.toMonoidHom = iG.toMonoidHom.range.map iX.toMonoidHom
  rw [hK', ← MonoidHom.range_comp, hsq', MonoidHom.range_comp]

/-- A finite-stage model, recovered as the same connected cover with the same
chosen fiber point, has arithmetic-kernel image equal to that point's geometric
stabilizer embedded in the original arithmetic fundamental group. -/
theorem recoveredCover_arithmeticKernel_image
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (W : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f))
    [IsConnected W] (w : (fiber xi).obj W)
    (E : IntermediateField k κ)
    (N : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))
    (rec : (FiniteEtale.pullback (finiteStageCoefficientMap k κ E X f)).obj N ≅ W) :
    let _ : IsSepClosure E κ :=
      ⟨IsSepClosure.sep_closed k, Algebra.isSeparable_tower_top_of_isSeparable k E κ⟩
    let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let φκ := Spec.map (CommRingCat.ofHom (algebraMap k κ))
    let ψ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let c : N.left ⟶ Spec (.of E) := N.hom ≫ Limits.pullback.fst φE f
    let a : N.left ⟶ X := N.hom ≫ Limits.pullback.snd φE f
    let u : Limits.pullback ψ c ⟶ Limits.pullback φκ f :=
      coefficientModelMap ψ (Limits.pullback.fst φE f) N.hom ≫
      (constantFieldTowerIso k κ E X f).hom
    ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c) ∧
      ∃ (R : Limits.pullback ψ c ≅ W.left)
        (x : Spec (.of Ω) ⟶ Limits.pullback ψ c),
        R.hom ≫ W.hom = u ∧
        x ≫ R.hom = (fiberObjEquivHom xi W w).left ∧
        ∃ hpoint : (x ≫ Limits.pullback.snd ψ c) ≫ a = xi ≫ Limits.pullback.snd φκ f,
          ((arithmeticFundamentalGroupHom E κ c
            (x ≫ Limits.pullback.snd ψ c)).toMonoidHom.ker).map
              (pointedFundamentalGroupHom a (x ≫ Limits.pullback.snd ψ c)
                (xi ≫ Limits.pullback.snd φκ f) hpoint).toMonoidHom =
            (MulAction.stabilizer π₁ᵉᵗ(xi) w).map
              (fundamentalGroupHom (Limits.pullback.snd φκ f) xi).toMonoidHom := by
  intro hsep φE φκ ψ c a u
  let : IsAffineHom (Limits.pullback.snd φE f) :=
    MorphismProperty.pullback_snd
      (P := (show MorphismProperty Scheme.{u} from @IsAffineHom)) φE f inferInstance
  let : CompactSpace (show Scheme.{u} from Limits.pullback φE f) :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd φE f)
  let : QuasiSeparatedSpace (show Scheme.{u} from Limits.pullback φE f) :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd φE f)
  let : IsFiniteEtale (show N.left ⟶ Limits.pullback φE f from N.hom) := N.prop
  let : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace
      (show N.left ⟶ Limits.pullback φE f from N.hom)
  let : QuasiSeparatedSpace N.left := quasiSeparatedSpace_of_quasiSeparated
      (show N.left ⟶ Limits.pullback φE f from N.hom)
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  obtain ⟨R0, hR0⟩ := exists_finiteStageCoverRecoveryIso k κ E X f N W rec
  let R : Limits.pullback ψ c ≅ W.left := R0
  have hR : R.hom ≫ (show W.left ⟶ Limits.pullback φκ f from W.hom) = u := hR0
  let : ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c) :=
    R.hom.homeomorph.connectedSpace_iff.mpr
    (inferInstance : ConnectedSpace W.left)
  let g := fiberObjEquivHom xi W w
  let xiW : Spec (.of Ω) ⟶ W.left := g.left
  have hxiW : xiW ≫ W.hom = xi := g.w
  let x : Spec (.of Ω) ⟶ Limits.pullback ψ c := xiW ≫ R.inv
  have hxR : x ≫ R.hom = xiW := by simp only [x, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  have hgeo : x ≫ u = xi := by
    rw [← hR, ← Category.assoc, hxR, hxiW]
  have hscheme : u ≫ Limits.pullback.snd φκ f = Limits.pullback.snd ψ c ≫ a := by
    let v : Limits.pullback ψ c ⟶ Limits.pullback ψ (Limits.pullback.fst φE f) :=
      coefficientModelMap ψ (Limits.pullback.fst φE f) N.hom
    have hT :
        (constantFieldTowerIso k κ E X f).hom ≫ Limits.pullback.snd φκ f =
          Limits.pullback.snd ψ (Limits.pullback.fst φE f) ≫
            Limits.pullback.snd φE f :=
      constantFieldTowerIso_hom_snd k κ E X f
    have hc : v ≫ Limits.pullback.snd ψ (Limits.pullback.fst φE f) =
        Limits.pullback.snd ψ c ≫ N.hom :=
      (coefficientBaseChange_isPullback ψ (Limits.pullback.fst φE f) N.hom).w
    exact (Category.assoc v _ _).trans
      ((congrArg (fun t => v ≫ t) hT).trans
        ((Category.assoc v _ _).symm.trans
          ((congrArg (fun t => t ≫ Limits.pullback.snd φE f) hc).trans
            (Category.assoc _ _ _))))
  have hpoint : (x ≫ Limits.pullback.snd ψ c) ≫ a = xi ≫ Limits.pullback.snd φκ f :=
    (Category.assoc x _ _).trans
      ((congrArg (fun t => x ≫ t) hscheme.symm).trans
        ((Category.assoc x u _).symm.trans
          (congrArg (fun t => t ≫ Limits.pullback.snd φκ f) hgeo)))
  refine ⟨inferInstance, R, x, hR, hxR, hpoint, ?_⟩
  have hker : (arithmeticFundamentalGroupHom E κ c
      (x ≫ Limits.pullback.snd ψ c)).toMonoidHom.ker =
        (fundamentalGroupHom (Limits.pullback.snd ψ c) x).toMonoidHom.range :=
    (arithmetic_exactSequence_of_isSepClosure E κ N.left c x).2.2
  have hmap := pointedSquare_map_of_kernel_eq_range
    (Limits.pullback.snd ψ c) (Limits.pullback.snd φκ f) u a x xi
    hgeo hpoint hscheme
    (arithmeticFundamentalGroupHom E κ c
      (x ≫ Limits.pullback.snd ψ c)).toMonoidHom.ker hker
  have hrange := pointedMap_range_of_schemeIso_cover xi W w R x u hgeo hR hxR
  exact hmap.trans (congrArg (fun H : Subgroup π₁ᵉᵗ(xi) =>
    H.map (fundamentalGroupHom (Limits.pullback.snd φκ f) xi).toMonoidHom) hrange)

/-- Every specified open geometric subgroup is the image of the arithmetic
kernel of an actual finite-stage descended cover, at the same original point.
The subgroup is arbitrary; no normality assumption is made. -/
theorem exists_descendedCover_arithmeticKernel_image_openSubgroup
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (V : OpenSubgroup π₁ᵉᵗ(xi)) :
    ∃ E : IntermediateField k κ, FiniteDimensional k E ∧
      ∃ N : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f),
        let _ : IsSepClosure E κ :=
          ⟨IsSepClosure.sep_closed k, Algebra.isSeparable_tower_top_of_isSeparable k E κ⟩
        let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
        let φκ := Spec.map (CommRingCat.ofHom (algebraMap k κ))
        let ψ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
        let c : N.left ⟶ Spec (.of E) := N.hom ≫ Limits.pullback.fst φE f
        let a : N.left ⟶ X := N.hom ≫ Limits.pullback.snd φE f
        a ≫ f = c ≫ φE ∧ ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c) ∧
          ∃ (x : Spec (.of Ω) ⟶ Limits.pullback ψ c)
            (hpoint : (x ≫ Limits.pullback.snd ψ c) ≫ a = xi ≫ Limits.pullback.snd φκ f),
            ((arithmeticFundamentalGroupHom E κ c
              (x ≫ Limits.pullback.snd ψ c)).toMonoidHom.ker).map
                (pointedFundamentalGroupHom a (x ≫ Limits.pullback.snd ψ c)
                  (xi ≫ Limits.pullback.snd φκ f) hpoint).toMonoidHom =
              (V : Subgroup π₁ᵉᵗ(xi)).map
                (fundamentalGroupHom (Limits.pullback.snd φκ f) xi).toMonoidHom := by
  obtain ⟨W, hW, w, hw⟩ :=
    exists_connected_object_point_stabilizer_eq_any_universe (fiber xi) V
  let : IsConnected W := hW
  obtain ⟨E, hfin, N, ⟨rec⟩⟩ :=
    FiniteEtale.exists_finiteIntermediateField_scheme_model k κ X f W
  obtain ⟨hconn, _, x, _, _, hpoint, hkernel⟩ :=
    recoveredCover_arithmeticKernel_image k κ X f xi W w E N rec
  refine ⟨E, hfin, N, ?_, hconn, x, hpoint, ?_⟩
  · simp only [Category.assoc]
    exact congrArg (fun h => N.hom ≫ h) Limits.pullback.condition.symm
  · simpa only [hw] using hkernel

end AlgebraicGeometry.FiniteEtale
