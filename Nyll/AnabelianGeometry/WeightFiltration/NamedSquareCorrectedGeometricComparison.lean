/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.CommonArithmeticPointGeometricEquiv
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldCoverGroupTransport
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport

/-! # Named Square Corrected Geometric Comparison -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

/-- A pointed geometric comparison induces the specified inner conjugate on the
original arithmetic fundamental groups. -/
def originalAmbientCorrectedComparison
    {GS GT XS XT : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    (us : GS ⟶ XS) (ut : GT ⟶ XT)
    (xs : Spec (.of Ωs) ⟶ GS) (xt : Spec (.of Ωt) ⟶ GT)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs : xs ≫ us = zs) (ht : xt ≫ ut = zt)
    (αP : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (β : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (c : π₁ᵉᵗ(zt)) : Prop :=
  ∀ g, pointedFundamentalGroupHom ut xt zt ht (β g) =
    c * αP (pointedFundamentalGroupHom us xs zs hs g) * c⁻¹

theorem commonPoint_geometricMap_eq_transport
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (XS XT : Scheme) [CompactSpace XS] [QuasiSeparatedSpace XS]
    [CompactSpace XT] [QuasiSeparatedSpace XT]
    (fs : XS ⟶ Spec (.of k)) (ft : XT ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs : Scheme)]
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs₀ xs₁ : Spec (.of Ωs) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs)
    (xt₀ xt₁ : Spec (.of Ωt) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs₀ : xs₀ ≫ Limits.pullback.snd _ fs = zs)
    (hs₁ : xs₁ ≫ Limits.pullback.snd _ fs = zs)
    (ht₀ : xt₀ ≫ Limits.pullback.snd _ ft = zt)
    (ht₁ : xt₁ ≫ Limits.pullback.snd _ ft = zt)
    (αP : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (α : π₁ᵉᵗ(xs₀) ≃ₜ* π₁ᵉᵗ(xt₀))
    (β : π₁ᵉᵗ(xs₁) ≃ₜ* π₁ᵉᵗ(xt₁))
    (hα : ∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀
        (α g) = αP (pointedFundamentalGroupHom
          (Limits.pullback.snd _ fs) xs₀ zs hs₀ g))
    (hβ : ∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁
        (β g) = αP (pointedFundamentalGroupHom
          (Limits.pullback.snd _ fs) xs₁ zs hs₁ g)) :
    let eS := commonArithmeticPointGeometricEquiv k κ XS fs xs₀ xs₁ zs hs₀ hs₁
    let eT := commonArithmeticPointGeometricEquiv k κ XT ft xt₀ xt₁ zt ht₀ ht₁
    β = eS.symm.trans (α.trans eT) := by
  intro eS eT
  apply ContinuousMulEquiv.ext
  intro g
  apply (commonArithmeticPoint_projection_exact k κ XT ft xt₁ zt ht₁).1
  have hS := commonArithmeticPointGeometricEquiv_projection
    k κ XS fs xs₀ xs₁ zs hs₀ hs₁ (eS.symm g)
  change pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₁ zs hs₁
    (eS (eS.symm g)) = _ at hS
  rw [eS.apply_symm_apply] at hS
  calc
    pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁ (β g) =
        αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₁ zs hs₁ g) := hβ g
    _ = αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₀ zs hs₀
        (eS.symm g)) := congrArg αP hS
    _ = pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀
        (α (eS.symm g)) := (hα (eS.symm g)).symm
    _ = pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁
        ((eS.symm.trans (α.trans eT)) g) :=
      (commonArithmeticPointGeometricEquiv_projection
        k κ XT ft xt₀ xt₁ zt ht₀ ht₁ (α (eS.symm g))).symm

theorem commonPoint_exists_original_geometricMap
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (XS XT : Scheme) [CompactSpace XS] [QuasiSeparatedSpace XS]
    [CompactSpace XT] [QuasiSeparatedSpace XT]
    (fs : XS ⟶ Spec (.of k)) (ft : XT ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs : Scheme)]
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs₀ xs₁ : Spec (.of Ωs) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs)
    (xt₀ xt₁ : Spec (.of Ωt) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs₀ : xs₀ ≫ Limits.pullback.snd _ fs = zs)
    (hs₁ : xs₁ ≫ Limits.pullback.snd _ fs = zs)
    (ht₀ : xt₀ ≫ Limits.pullback.snd _ ft = zt)
    (ht₁ : xt₁ ≫ Limits.pullback.snd _ ft = zt)
    (αP : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (β : π₁ᵉᵗ(xs₁) ≃ₜ* π₁ᵉᵗ(xt₁))
    (hβ : ∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁
        (β g) = αP (pointedFundamentalGroupHom
          (Limits.pullback.snd _ fs) xs₁ zs hs₁ g)) :
    let eS := commonArithmeticPointGeometricEquiv k κ XS fs xs₀ xs₁ zs hs₀ hs₁
    let eT := commonArithmeticPointGeometricEquiv k κ XT ft xt₀ xt₁ zt ht₀ ht₁
    ∃ α : π₁ᵉᵗ(xs₀) ≃ₜ* π₁ᵉᵗ(xt₀),
      (∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀ (α g) =
        αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₀ zs hs₀ g)) ∧
      β = eS.symm.trans (α.trans eT) := by
  intro eS eT
  let α := eS.trans (β.trans eT.symm)
  have hα (g : π₁ᵉᵗ(xs₀)) :
      pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀ (α g) =
        αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₀ zs hs₀ g) := by
    have hT := commonArithmeticPointGeometricEquiv_projection
      k κ XT ft xt₀ xt₁ zt ht₀ ht₁ (α g)
    change pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁
      (eT (eT.symm (β (eS g)))) = _ at hT
    rw [eT.apply_symm_apply] at hT
    calc
      pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀ (α g) =
          pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁ (β (eS g)) :=
        hT.symm
      _ = αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₁ zs hs₁ (eS g)) :=
        hβ (eS g)
      _ = αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₀ zs hs₀ g) :=
        congrArg αP (commonArithmeticPointGeometricEquiv_projection
          k κ XS fs xs₀ xs₁ zs hs₀ hs₁ g)
  exact ⟨α, hα, commonPoint_geometricMap_eq_transport k κ XS XT fs ft
    xs₀ xs₁ xt₀ xt₁ zs zt hs₀ hs₁ ht₀ ht₁ αP α β hα hβ⟩

private theorem exists_geometricEquiv_at_common_points
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (XS XT : Scheme) [CompactSpace XS] [QuasiSeparatedSpace XS]
    [CompactSpace XT] [QuasiSeparatedSpace XT]
    (fs : XS ⟶ Spec (.of k)) (ft : XT ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs : Scheme)]
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs : Spec (.of Ωs) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs)
    (xt : Spec (.of Ωt) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs : xs ≫ Limits.pullback.snd _ fs = zs)
    (ht : xt ≫ Limits.pullback.snd _ ft = zt)
    (α : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft zt (α g) =
      arithmeticFundamentalGroupHom k κ fs zs g) :
    ∃ β : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt),
      ∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt zt ht (β g) =
        α (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs zs hs g) := by
  subst zs
  subst zt
  obtain ⟨β, hβ, _⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv
    k κ XS XT fs ft xs xt α hα
  exact ⟨β, hβ⟩

theorem finiteBase_exists_corrected_geometricMap_original_square
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ] [IsSepClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {XS XT : Scheme} [ConnectedSpace XS] [ConnectedSpace XT]
    (fs : XS ⟶ Spec (.of k)) (ft : XT ⟶ Spec (.of k))
    [CompactSpace (Limits.pullback (originalConstantFieldCover k E).hom fs : Scheme)]
    [QuasiSeparatedSpace (Limits.pullback (originalConstantFieldCover k E).hom fs : Scheme)]
    [CompactSpace (Limits.pullback (originalConstantFieldCover k E).hom ft : Scheme)]
    [QuasiSeparatedSpace (Limits.pullback (originalConstantFieldCover k E).hom ft : Scheme)]
    [ConnectedSpace (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) : Scheme)]
    [ConnectedSpace (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (α : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft zt (α g) =
      arithmeticFundamentalGroupHom k κ fs zs g) :
    let ys := arithmeticConstantFieldLift k E κ fs zs
    let yt := arithmeticConstantFieldLift k E κ ft zt
    let cs := Limits.pullback.fst (originalConstantFieldCover k E).hom fs
    let ct := Limits.pullback.fst (originalConstantFieldCover k E).hom ft
    let iS := pointedFundamentalGroupHom
      ((pullback fs).obj (originalConstantFieldCover k E)).hom ys zs
      (arithmeticConstantFieldLift_comp k E κ fs zs)
    let iT := pointedFundamentalGroupHom
      ((pullback ft).obj (originalConstantFieldCover k E)).hom yt zt
      (arithmeticConstantFieldLift_comp k E κ ft zt)
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft zs zt α hα
    ∀ (xs : Spec (.of Ωs) ⟶ Limits.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cs)
      (xt : Spec (.of Ωt) ⟶ Limits.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ct)
      (hs : xs ≫ Limits.pullback.snd _ cs = ys)
      (ht : xt ≫ Limits.pullback.snd _ ct = yt)
      (c : π₁ᵉᵗ(yt)),
      (∀ g, arithmeticFundamentalGroupHom E κ ct yt
          (ProCGroups.innerCorrectedGroupEquiv αE c g) =
        arithmeticFundamentalGroupHom E κ cs ys g) →
      ∃ β : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt),
        (∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ct) xt yt ht (β g) =
          ProCGroups.innerCorrectedGroupEquiv αE c
            (pointedFundamentalGroupHom (Limits.pullback.snd _ cs) xs ys hs g)) ∧
        ∀ g, iT (pointedFundamentalGroupHom (Limits.pullback.snd _ ct) xt yt ht (β g)) =
          iT c * α (iS (pointedFundamentalGroupHom
            (Limits.pullback.snd _ cs) xs ys hs g)) * (iT c)⁻¹ := by
  intro ys yt cs ct iS iT αE xs xt hs ht c hstrict
  obtain ⟨β, hβ⟩ := exists_geometricEquiv_at_common_points E κ
    (Limits.pullback (originalConstantFieldCover k E).hom fs)
    (Limits.pullback (originalConstantFieldCover k E).hom ft)
    cs ct xs xt ys yt hs ht (ProCGroups.innerCorrectedGroupEquiv αE c) hstrict
  refine ⟨β, hβ, ?_⟩
  intro g
  apply (congrArg iT (hβ g)).trans
  change iT (c * αE _ * c⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  have hincl := arithmeticConstantFieldCoverGroupTransport_inclusion
    k E κ fs ft zs zt α hα
    (pointedFundamentalGroupHom (Limits.pullback.snd _ cs) xs ys hs g)
  exact congrArg (fun z => iT c * z * (iT c)⁻¹) hincl

theorem finiteBase_corrected_geometricMap_original_square
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ] [IsSepClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {XS XT : Scheme} [ConnectedSpace XS] [ConnectedSpace XT]
    (fs : XS ⟶ Spec (.of k)) (ft : XT ⟶ Spec (.of k))
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (α : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft zt (α g) =
      arithmeticFundamentalGroupHom k κ fs zs g) :
    let ys := arithmeticConstantFieldLift k E κ fs zs
    let yt := arithmeticConstantFieldLift k E κ ft zt
    let cs := Limits.pullback.fst (originalConstantFieldCover k E).hom fs
    let ct := Limits.pullback.fst (originalConstantFieldCover k E).hom ft
    let iS := pointedFundamentalGroupHom
      ((pullback fs).obj (originalConstantFieldCover k E)).hom ys zs
      (arithmeticConstantFieldLift_comp k E κ fs zs)
    let iT := pointedFundamentalGroupHom
      ((pullback ft).obj (originalConstantFieldCover k E)).hom yt zt
      (arithmeticConstantFieldLift_comp k E κ ft zt)
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft zs zt α hα
    ∀ (xs : Spec (.of Ωs) ⟶ Limits.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cs)
      (xt : Spec (.of Ωt) ⟶ Limits.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ct)
      (hs : xs ≫ Limits.pullback.snd _ cs = ys)
      (ht : xt ≫ Limits.pullback.snd _ ct = yt)
      (c : π₁ᵉᵗ(yt)) (β : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)),
      (∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ct) xt yt ht (β g) =
        ProCGroups.innerCorrectedGroupEquiv αE c
          (pointedFundamentalGroupHom (Limits.pullback.snd _ cs) xs ys hs g)) →
        ∀ g, iT (pointedFundamentalGroupHom (Limits.pullback.snd _ ct) xt yt ht (β g)) =
          iT c * α (iS (pointedFundamentalGroupHom
            (Limits.pullback.snd _ cs) xs ys hs g)) * (iT c)⁻¹ := by
  intro ys yt cs ct iS iT αE xs xt hs ht c β hβ g
  apply (congrArg iT (hβ g)).trans
  change iT (c * αE _ * c⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  have hincl := arithmeticConstantFieldCoverGroupTransport_inclusion
    k E κ fs ft zs zt α hα
    (pointedFundamentalGroupHom (Limits.pullback.snd _ cs) xs ys hs g)
  exact congrArg (fun z => iT c * z * (iT c)⁻¹) hincl

end AnabelianGeometry.WeightFiltration
