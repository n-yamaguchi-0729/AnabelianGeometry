/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.DescendedCoverKernelImage
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverInjectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower

/-!
# The actual recovered cover and arithmetic conjugation

This file exports only the equivalence with the same fiber stabilizer,
its evaluation under the original covering map, and the action on abelianized
classes. It introduces no new Galois action or weight construction.

-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

/-- An actual isomorphism onto the chosen cover gives its point stabilizer,
with the value of the equivalence fixed by the original covering map. -/
private theorem exists_stabilizerEquiv_of_schemeIso_cover
    {S Y : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (W : FiniteEtale S) [IsConnected W]
    (w : (fiber xi).obj W) (R : Y ≅ W.left)
    (x : Spec (.of Ω) ⟶ Y) (u : Y ⟶ S)
    (hgeo : x ≫ u = xi) (hu : R.hom ≫ W.hom = u)
    (hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left) :
    ∃ e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w,
      ∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v := by
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let : ConnectedSpace Y := R.hom.homeomorph.connectedSpace_iff.mpr
    (inferInstance : ConnectedSpace W.left)
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
  have hleft : sR.comp eR = ContinuousMonoidHom.id π₁ᵉᵗ(x) := by
    change (pointedFundamentalGroupHom R.inv xiW x hy).comp
      (pointedFundamentalGroupHom R.hom x xiW hx) = _
    rw [pointedFundamentalGroupHom_comp]
    simpa only [Iso.hom_inv_id] using (pointedFundamentalGroupHom_id x)
  have heR : Function.Bijective eR := by
    constructor
    · intro v v' hv
      calc
        v = sR (eR v) := (DFunLike.congr_fun hleft v).symm
        _ = sR (eR v') := congrArg sR hv
        _ = v' := DFunLike.congr_fun hleft v'
    · intro v
      exact ⟨sR v, DFunLike.congr_fun hright v⟩
  have hiW : Function.Injective iW :=
    pointedFundamentalGroupHom_injective W xiW xi hxiW
  have hiG : Function.Injective iG := by
    intro v v' hv
    apply heR.1
    apply hiW
    exact (DFunLike.congr_fun hWR v).trans
      (hv.trans (DFunLike.congr_fun hWR v').symm)
  have hG : iG.toMonoidHom.range = iW.toMonoidHom.range := by
    ext b
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨eR v, DFunLike.congr_fun hWR v⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨v', rfl⟩ := heR.2 v
      exact ⟨v', (DFunLike.congr_fun hWR v').symm⟩
  have hw : (fiberObjEquivHom xi W).symm (Over.homMk xiW hxiW) = w := by
    apply (fiberObjEquivHom xi W).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have hrange : iG.toMonoidHom.range = MulAction.stabilizer π₁ᵉᵗ(xi) w := by
    rw [hG, pointedFundamentalGroupHom_range_eq_stabilizer, hw]
  have hmem (v : π₁ᵉᵗ(x)) : iG v ∈ MulAction.stabilizer π₁ᵉᵗ(xi) w := by
    rw [← hrange]
    exact ⟨v, rfl⟩
  let q := iG.toMonoidHom.codRestrict (MulAction.stabilizer π₁ᵉᵗ(xi) w) hmem
  have hq : Function.Bijective q := by
    constructor
    · intro v v' hv
      exact hiG (congrArg Subtype.val hv)
    · intro v
      have hv : v.val ∈ iG.toMonoidHom.range := hrange.symm ▸ v.property
      obtain ⟨t, ht⟩ := hv
      exact ⟨t, Subtype.ext ht⟩
  let e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w :=
    ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2 q
      (iG.continuous_toFun.subtype_mk hmem) hq
  exact ⟨e, fun _ => rfl⟩

/-- In an actual pointed scheme square, the existing arithmetic action is
conjugation under the original map. The compactification and coefficient
recovery data remain outside this opaque comparison. -/
private theorem pointedSquare_arithmeticAction
    (E κ : Type u) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    (C : Scheme.{u}) [CompactSpace C] [QuasiSeparatedSpace C]
    (c : C ⟶ Spec (.of E))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c)]
    {S X : Scheme.{u}} (p : S ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c)
    (xi : Spec (.of Ω) ⟶ S)
    (u : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ⟶ S)
    (a : C ⟶ X) (hgeo : x ≫ u = xi)
    (hpoint : (x ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) ≫ a = xi ≫ p)
    (hscheme : u ≫ p = Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≫ a)
    (H : Subgroup π₁ᵉᵗ(xi)) (e : π₁ᵉᵗ(x) ≃ₜ* H)
    (he : ∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v) :
    let pY := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
    let iX := fundamentalGroupHom p xi
    let iY := fundamentalGroupHom pY x
    let J := pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ p) hpoint
    (∀ v, iX (e v : π₁ᵉᵗ(xi)) = J (iY v)) ∧
      ∀ (γ : π₁ᵉᵗ(x ≫ pY)) (v : π₁ᵉᵗ(x)),
        ∃ v' : π₁ᵉᵗ(x),
          TopologicalAbelianization.congr e
            (geometricAbelianGaloisAction E κ C c x
              (arithmeticFundamentalGroupHom E κ c (x ≫ pY) γ)
              (TopologicalAbelianization.mk _ v)) =
            TopologicalAbelianization.mk _ (e v') ∧
          iX (e v' : π₁ᵉᵗ(xi)) = J γ * iX (e v : π₁ᵉᵗ(xi)) * (J γ)⁻¹ := by
  intro pY iX iY J
  let iG : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(xi) :=
    pointedFundamentalGroupHom u x xi hgeo
  have hsq : J.comp iY = iX.comp iG := by
    change (pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ p) hpoint).comp
        (pointedFundamentalGroupHom pY x (x ≫ pY) rfl) =
      (pointedFundamentalGroupHom p xi (xi ≫ p) rfl).comp
        (pointedFundamentalGroupHom u x xi hgeo)
    rw [pointedFundamentalGroupHom_comp, pointedFundamentalGroupHom_comp]
    simp only [hscheme, pY]
  have heval (v : π₁ᵉᵗ(x)) : iX (e v : π₁ᵉᵗ(xi)) = J (iY v) := by
    rw [he v]
    exact (DFunLike.congr_fun hsq v).symm
  refine ⟨heval, ?_⟩
  intro γ v
  let E₀ := geometricFundamentalGroupKernelEquiv E κ C c x
  let n := MulAut.conjNormal γ (E₀ v)
  let v' := E₀.symm n
  have hv' : iY v' = γ * iY v * γ⁻¹ := by
    calc
      iY v' = (E₀ v' : π₁ᵉᵗ(x ≫ pY)) := rfl
      _ = (n : π₁ᵉᵗ(x ≫ pY)) :=
        congrArg Subtype.val (E₀.apply_symm_apply n)
      _ = γ * iY v * γ⁻¹ := rfl
  have haction := geometricAbelianGaloisAction_mk_of_conjugate
    E κ C c x γ v v' hv'
  refine ⟨v', ?_, ?_⟩
  · rw [haction, TopologicalAbelianization.congr_apply_mk]
  · calc
      iX (e v' : π₁ᵉᵗ(xi)) = J (iY v') := heval v'
      _ = J γ * J (iY v) * (J γ)⁻¹ := by
        rw [hv', map_mul, map_mul, map_inv]
      _ = J γ * iX (e v : π₁ᵉᵗ(xi)) * (J γ)⁻¹ := by rw [heval]

/-- The actual recovery at a prescribed point gives the original stabilizer and
arithmetic action. This form applies directly to the refined recovery `RF`
and the point already used by the compactification weight theorem. -/
theorem recoveredPoint_stabilizerEquiv_arithmeticAction
    (E κ : Type u) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    (C : Scheme.{u}) [CompactSpace C] [QuasiSeparatedSpace C]
    (c : C ⟶ Spec (.of E))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c)]
    {S X : Scheme.{u}} [ConnectedSpace S] (p : S ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (W : FiniteEtale S) [IsConnected W]
    (w : (fiber xi).obj W)
    (u : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ⟶ S)
    (a : C ⟶ X)
    (hscheme : u ≫ p = Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≫ a)
    (R : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≅ W.left)
    (hR : R.hom ≫ W.hom = u)
    (x : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c)
    (hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left) :
    ∃ (hgeo : x ≫ u = xi)
      (hpoint : (x ≫ Limits.pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) ≫ a = xi ≫ p)
      (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
      let pY := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
      let iX := fundamentalGroupHom p xi
      let iY := fundamentalGroupHom pY x
      let J := pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ p) hpoint
      (∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v) ∧
      (∀ v, iX (e v : π₁ᵉᵗ(xi)) = J (iY v)) ∧
      ∀ (γ : π₁ᵉᵗ(x ≫ pY)) (v : π₁ᵉᵗ(x)),
        ∃ v' : π₁ᵉᵗ(x),
          TopologicalAbelianization.congr e
            (geometricAbelianGaloisAction E κ C c x
              (arithmeticFundamentalGroupHom E κ c (x ≫ pY) γ)
              (TopologicalAbelianization.mk _ v)) =
            TopologicalAbelianization.mk _ (e v') ∧
          iX (e v' : π₁ᵉᵗ(xi)) = J γ * iX (e v : π₁ᵉᵗ(xi)) * (J γ)⁻¹ := by
  have hgeo : x ≫ u = xi := by
    rw [← hR, ← Category.assoc, hxR]
    exact (fiberObjEquivHom xi W w).w
  have hpoint : (x ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) ≫ a = xi ≫ p := by
    rw [Category.assoc, ← hscheme, ← Category.assoc, hgeo]
  obtain ⟨e, he⟩ := exists_stabilizerEquiv_of_schemeIso_cover
    xi W w R x u hgeo hR hxR
  obtain ⟨heval, haction⟩ := pointedSquare_arithmeticAction E κ C c
    p x xi u a hgeo hpoint hscheme (MulAction.stabilizer π₁ᵉᵗ(xi) w) e he
  exact ⟨hgeo, hpoint, e, he, heval, haction⟩


/-- Package the action comparison over an abstract arithmetic source scheme.
The point is reconstructed from the original fiber element and the actual
recovery isomorphism, so no point or action comparison is assumed. -/
private theorem exists_recoveredPoint_arithmeticAction
    (E κ : Type u) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    (C : Scheme.{u}) [CompactSpace C] [QuasiSeparatedSpace C]
    (c : C ⟶ Spec (.of E))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c)]
    {S X : Scheme.{u}} [ConnectedSpace S] (p : S ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (W : FiniteEtale S) [IsConnected W]
    (w : (fiber xi).obj W)
    (u : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ⟶ S)
    (a : C ⟶ X)
    (hscheme : u ≫ p = Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≫ a)
    (R : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≅ W.left)
    (hR : R.hom ≫ W.hom = u) :
    ∃ (x : Spec (.of Ω) ⟶
          Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c)
      (_hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left)
      (hgeo : x ≫ u = xi)
      (hpoint : (x ≫ Limits.pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) ≫ a = xi ≫ p)
      (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
      let pY := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
      let iX := fundamentalGroupHom p xi
      let iY := fundamentalGroupHom pY x
      let J := pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ p) hpoint
      (∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v) ∧
      (∀ v, iX (e v : π₁ᵉᵗ(xi)) = J (iY v)) ∧
      ∀ (γ : π₁ᵉᵗ(x ≫ pY)) (v : π₁ᵉᵗ(x)),
        ∃ v' : π₁ᵉᵗ(x),
          TopologicalAbelianization.congr e
            (geometricAbelianGaloisAction E κ C c x
              (arithmeticFundamentalGroupHom E κ c (x ≫ pY) γ)
              (TopologicalAbelianization.mk _ v)) =
            TopologicalAbelianization.mk _ (e v') ∧
          iX (e v' : π₁ᵉᵗ(xi)) = J γ * iX (e v : π₁ᵉᵗ(xi)) * (J γ)⁻¹ := by
  let g := fiberObjEquivHom xi W w
  let xiW : Spec (.of Ω) ⟶ W.left := g.left
  let x : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c :=
    xiW ≫ R.inv
  have hxR : x ≫ R.hom = xiW := by
    simp only [x, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hgeo : x ≫ u = xi := by
    rw [← hR, ← Category.assoc, hxR]
    exact g.w
  have hpoint : (x ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) ≫ a = xi ≫ p := by
    rw [Category.assoc, ← hscheme, ← Category.assoc, hgeo]
  obtain ⟨e, he⟩ := exists_stabilizerEquiv_of_schemeIso_cover
    xi W w R x u hgeo hR hxR
  obtain ⟨heval, haction⟩ := pointedSquare_arithmeticAction E κ C c
    p x xi u a hgeo hpoint hscheme (MulAction.stabilizer π₁ᵉᵗ(xi) w) e he
  exact ⟨x, hxR, hgeo, hpoint, e, he, heval, haction⟩

/-- The same recovered cover identifies its geometric group with the original
point stabilizer. Its Galois action is exactly arithmetic conjugation under
the original inclusion, as witnessed on every abelianized geometric element. -/
theorem recoveredCover_stabilizerEquiv_arithmeticAction_with_recovery
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (W : FiniteEtale
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f))
    [IsConnected W] (w : (fiber xi).obj W)
    (E : IntermediateField k κ)
    (N : FiniteEtale
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))
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
    ∃ hc : CompactSpace N.left, ∃ hq : QuasiSeparatedSpace N.left,
      let _ : CompactSpace N.left := hc
      let _ : QuasiSeparatedSpace N.left := hq
      ∃ hconn : ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c),
        let _ : ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c) := hconn
        ∃ (R : Limits.pullback ψ c ≅ W.left)
          (_hR : R.hom ≫ (show W.left ⟶ Limits.pullback φκ f from W.hom) = u)
          (x : Spec (.of Ω) ⟶ Limits.pullback ψ c)
          (_hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left)
          (hgeo : x ≫ u = xi)
          (hpoint : (x ≫ Limits.pullback.snd ψ c) ≫ a = xi ≫ Limits.pullback.snd φκ f)
          (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
          let iX := fundamentalGroupHom (Limits.pullback.snd φκ f) xi
          let iY := fundamentalGroupHom (Limits.pullback.snd ψ c) x
          let J := pointedFundamentalGroupHom a (x ≫ Limits.pullback.snd ψ c)
            (xi ≫ Limits.pullback.snd φκ f) hpoint
          (∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v) ∧
          (∀ v, iX (e v : π₁ᵉᵗ(xi)) = J (iY v)) ∧
          ∀ (γ : π₁ᵉᵗ(x ≫ Limits.pullback.snd ψ c)) (v : π₁ᵉᵗ(x)),
            ∃ v' : π₁ᵉᵗ(x),
              TopologicalAbelianization.congr e
                (geometricAbelianGaloisAction E κ N.left c x
                  (arithmeticFundamentalGroupHom E κ c
                    (x ≫ Limits.pullback.snd ψ c) γ)
                  (TopologicalAbelianization.mk _ v)) =
                TopologicalAbelianization.mk _ (e v') ∧
              iX (e v' : π₁ᵉᵗ(xi)) =
                J γ * iX (e v : π₁ᵉᵗ(xi)) * (J γ)⁻¹ := by
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
  obtain ⟨hconn, R0, _, hR0, _⟩ :=
    recoveredCover_arithmeticKernel_image k κ X f xi W w E N rec
  let R : Limits.pullback ψ c ≅ W.left := R0
  have hR : R.hom ≫ (show W.left ⟶ Limits.pullback φκ f from W.hom) = u := hR0
  let : ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c) := hconn
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
    exact (Category.assoc v (constantFieldTowerIso k κ E X f).hom
      (Limits.pullback.snd φκ f)).trans
      ((congrArg
        (fun t : Limits.pullback ψ (Limits.pullback.fst φE f) ⟶ X => v ≫ t) hT).trans
        ((Category.assoc v (Limits.pullback.snd ψ (Limits.pullback.fst φE f))
          (Limits.pullback.snd φE f)).symm.trans
          ((congrArg
            (fun t : Limits.pullback ψ c ⟶ Limits.pullback φE f =>
              t ≫ Limits.pullback.snd φE f) hc).trans
            (Category.assoc (Limits.pullback.snd ψ c) N.hom
              (Limits.pullback.snd φE f)))))
  refine ⟨inferInstance, inferInstance, hconn, R, hR, ?_⟩
  exact exists_recoveredPoint_arithmeticAction E κ N.left c
    (Limits.pullback.snd φκ f) xi W w u a hscheme R hR

/-- The original public action comparison, forgetting only the additional
recovery isomorphism and its exact point equation. -/
theorem recoveredCover_stabilizerEquiv_arithmeticAction
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme.{u} from
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (W : FiniteEtale
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f))
    [IsConnected W] (w : (fiber xi).obj W)
    (E : IntermediateField k κ)
    (N : FiniteEtale
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))
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
    ∃ hc : CompactSpace N.left, ∃ hq : QuasiSeparatedSpace N.left,
      let _ : CompactSpace N.left := hc
      let _ : QuasiSeparatedSpace N.left := hq
      ∃ hconn : ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c),
        let _ : ConnectedSpace (show Scheme.{u} from Limits.pullback ψ c) := hconn
        ∃ (x : Spec (.of Ω) ⟶ Limits.pullback ψ c)
          (hgeo : x ≫ u = xi)
          (hpoint : (x ≫ Limits.pullback.snd ψ c) ≫ a = xi ≫ Limits.pullback.snd φκ f)
          (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
          let iX := fundamentalGroupHom (Limits.pullback.snd φκ f) xi
          let iY := fundamentalGroupHom (Limits.pullback.snd ψ c) x
          let J := pointedFundamentalGroupHom a (x ≫ Limits.pullback.snd ψ c)
            (xi ≫ Limits.pullback.snd φκ f) hpoint
          (∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v) ∧
          (∀ v, iX (e v : π₁ᵉᵗ(xi)) = J (iY v)) ∧
          ∀ (γ : π₁ᵉᵗ(x ≫ Limits.pullback.snd ψ c)) (v : π₁ᵉᵗ(x)),
            ∃ v' : π₁ᵉᵗ(x),
              TopologicalAbelianization.congr e
                (geometricAbelianGaloisAction E κ N.left c x
                  (arithmeticFundamentalGroupHom E κ c
                    (x ≫ Limits.pullback.snd ψ c) γ)
                  (TopologicalAbelianization.mk _ v)) =
                TopologicalAbelianization.mk _ (e v') ∧
              iX (e v' : π₁ᵉᵗ(xi)) =
                J γ * iX (e v : π₁ᵉᵗ(xi)) * (J γ)⁻¹ := by
  obtain ⟨hc, hq, hconn, _, _, x, _, hgeo, hpoint, e, he, heval, haction⟩ :=
    recoveredCover_stabilizerEquiv_arithmeticAction_with_recovery
      k κ X f xi W w E N rec
  exact ⟨hc, hq, hconn, x, hgeo, hpoint, e, he, heval, haction⟩

end AlgebraicGeometry.FiniteEtale
