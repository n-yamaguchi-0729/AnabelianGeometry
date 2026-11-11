/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PointedAbelianDetection
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
public import Nyll.EtaleFundamentalGroups.GaloisCovers.IsomorphismTransport

/-!
# Pointed finite models detect the actual source action

The native detecting cover is reoriented by the actual symmetry of the
constant-field pullback. Its rational lift and both coordinates of the
original generic point are retained. A nontrivial source action on the
original geometric abelianization therefore moves an actual field-valued
point of this same rationally pointed abelian cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Closing an actual source isomorphism commutes with the original
fundamental-group map, with the specified equality of points. -/
theorem fundamentalGroupHom_sourceAutomorphism
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (e : Spec (.of Ω) ≅ Spec (.of Ω)) (hx : e.hom ≫ x = x) :
    let hy : e.hom ≫ (x ≫ f) = x ≫ f := by rw [← Category.assoc, hx]
    fundamentalGroupHom f x (Aut.of (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hx))) =
      Aut.of (fiberSourceIso (x ≫ f) e ≪≫ eqToIso (congrArg fiber hy)) := by
  intro hy
  let ρ := (Spec.preimage e.hom).hom
  have he : Spec.map (CommRingCat.ofHom ρ) = e.hom := Spec.map_preimage e.hom
  let g : π₁ᵉᵗ(x) := Aut.of (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hx))
  have hpoint (W : FiniteEtale X) (w : (fiber x).obj W) :
      (fiberObjEquivHom x W (g.asIso.hom.app W w)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom x W w).left := by
    rw [he]
    exact fiberSourceIso_aut_point x e hx W w
  apply Aut.ext
  ext W w
  apply (fiberObjEquivHom (x ≫ f) W).injective
  ext1
  exact (fundamentalGroupHom_point_of_point_action f x g ρ hpoint W w).trans
    ((congrArg (fun h => h ≫ (fiberObjEquivHom (x ≫ f) W w).left) he).trans
      (fiberSourceIso_aut_point (x ≫ f) e hy W w).symm)

/-- Nontriviality in the original arithmetic geometric kernel transfers to
the actual geometric source action, through the native exact-sequence
equivalence and its original map. -/
theorem geometric_sourceAbelianization_ne_one_of_kernel
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (C : Scheme.{u}) [CompactSpace C] [QuasiSeparatedSpace C]
    (c : C ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k κ))
    let Cκ := Limits.pullback b c
    ∀ [ConnectedSpace Cκ] (x : Spec (.of Ω) ⟶ Cκ)
      (e : Spec (.of Ω) ≅ Spec (.of Ω)) (hx : e.hom ≫ x = x),
    let π := arithmeticFundamentalGroupHom k κ c (x ≫ pullback.snd b c)
    let hz : e.hom ≫ (x ≫ pullback.snd b c) = x ≫ pullback.snd b c := by
      rw [← Category.assoc, hx]
    let d : π₁ᵉᵗ(x ≫ pullback.snd b c) :=
      Aut.of (fiberSourceIso (x ≫ pullback.snd b c) e ≪≫ eqToIso (congrArg fiber hz))
    ∀ hd : π d = 1,
      TopologicalAbelianization.mk π.toMonoidHom.ker ⟨d, hd⟩ ≠ 1 →
      TopologicalAbelianization.mk π₁ᵉᵗ(x)
        (Aut.of (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hx))) ≠ 1 := by
  intro b Cκ hCκ x e hx π hz d hd hnon hzero
  let E := geometricFundamentalGroupKernelEquiv k κ C c x
  let g : π₁ᵉᵗ(x) := Aut.of (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hx))
  have hE : E g = (⟨d, hd⟩ : π.toMonoidHom.ker) := by
    apply Subtype.ext
    exact fundamentalGroupHom_sourceAutomorphism (pullback.snd b c) x e hx
  apply hnon
  have h := congrArg (TopologicalAbelianization.congr E) hzero
  exact (congrArg (TopologicalAbelianization.mk π.toMonoidHom.ker) hE).symm.trans
    ((TopologicalAbelianization.congr_apply_mk E g).symm.trans
      (h.trans (map_one (TopologicalAbelianization.congr E))))

end AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups

universe u

/-- A nontrivial native geometric abelian source action is detected on an
actual pointed abelian cover over finite constants. Both original point
coordinates, including the coefficient embedding, survive reorientation. -/
theorem exists_pointed_finiteConstant_cover_moved_by_source
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
    [Algebra.IsAlgebraic k κ] [IsSepClosed κ]
    (C : Scheme.{u}) [CompactSpace C] [QuasiSeparatedSpace C]
    (c : C ⟶ Spec (.of k))
    (ε : Spec (.of k) ⟶ C) (hε : ε ≫ c = 𝟙 _)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k κ))
    let Cκ := pullback b c
    ∀ [ConnectedSpace Cκ] (x : Spec (.of Ω) ⟶ Cκ)
      (e : Spec (.of Ω) ≅ Spec (.of Ω)) (hx : e.hom ≫ x = x),
      TopologicalAbelianization.mk π₁ᵉᵗ(x)
        (Aut.of (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hx))) ≠ 1 →
    ∃ E : IntermediateField k κ, FiniteDimensional k E ∧
      let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
      let CE := pullback c bE
      let εE : Spec (.of E) ⟶ CE := pullback.lift (bE ≫ ε) (𝟙 _)
        (by rw [Category.assoc, hε, Category.comp_id, Category.id_comp])
      ∃ hCE : ConnectedSpace CE,
        let _ : ConnectedSpace CE := hCE
        ∃ (N : FiniteEtale CE) (_ : IsGalois N) (_ : IsMulCommutative (Aut N))
          (s : Spec (.of E) ⟶ N.left) (p : Spec (.of Ω) ⟶ N.left),
          s ≫ N.hom = εE ∧
          p ≫ N.hom ≫ pullback.fst c bE = x ≫ pullback.snd b c ∧
          p ≫ N.hom ≫ pullback.snd c bE =
            x ≫ pullback.fst b c ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom) ∧
          e.hom ≫ p ≠ p := by
  intro b Cκ hCκ x e hx hg
  let g : π₁ᵉᵗ(x) := Aut.of (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hx))
  obtain ⟨E, hE, hCES, N, hN, hcommN, s, hs, y, hy⟩ :=
    exists_pointed_finiteConstant_cover_detecting_abelianization k κ C c ε hε x g hg
  let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let CES := pullback bE c
  let CE := pullback c bE
  let εES : Spec (.of E) ⟶ CES := pullback.lift (𝟙 _) (bE ≫ ε)
    (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
  let εE : Spec (.of E) ⟶ CE := pullback.lift (bE ≫ ε) (𝟙 _)
    (by rw [Category.assoc, hε, Category.comp_id, Category.id_comp])
  let t : Cκ ⟶ CES := pullback.map b c bE c
    (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 C) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  have : ConnectedSpace CES := hCES
  have : IsGalois N := hN
  have : IsMulCommutative (Aut N) := hcommN
  let a := pullbackSymmetry c bE
  have hCE : ConnectedSpace CE := a.hom.homeomorph.connectedSpace_iff.mpr hCES
  let M := (FiniteEtale.pullback a.hom).obj N
  have : IsGalois M := (isGalois_pullback_and_card_aut_of_isIso a.hom N).1
  have : IsMulCommutative (Aut M) :=
    isMulCommutative_aut_pullback_of_isConnected a.hom N
  let r : M.left ⟶ N.left := pullback.fst N.hom a.hom
  have hεE : εE ≫ a.hom = εES := by
    apply pullback.hom_ext
    · simp only [εE, εES, a, Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullback.lift_snd, pullback.lift_fst]
    · simp only [εE, εES, a, Category.assoc, pullbackSymmetry_hom_comp_snd,
        pullback.lift_fst, pullback.lift_snd]
  let sM : Spec (.of E) ⟶ M.left := pullback.lift s εE (hs.trans hεE.symm)
  let pS : Spec (.of Ω) ⟶ N.left := (fiberObjEquivHom (x ≫ t) N y).left
  have hpS : pS ≫ N.hom = x ≫ t := (fiberObjEquivHom (x ≫ t) N y).w
  let xE : Spec (.of Ω) ⟶ CE := (x ≫ t) ≫ a.inv
  have hxE : xE ≫ a.hom = x ≫ t :=
    (Category.assoc (x ≫ t) a.inv a.hom).trans
      ((congrArg (fun f : CES ⟶ CES => (x ≫ t) ≫ f) a.inv_hom_id).trans
        (Category.comp_id (x ≫ t)))
  let pM : Spec (.of Ω) ⟶ M.left := pullback.lift pS xE (hpS.trans hxE.symm)
  have hpM : pM ≫ r = pS := pullback.lift_fst _ _ _
  have hpMx : pM ≫ M.hom = xE := pullback.lift_snd _ _ _
  have hxEf : xE ≫ pullback.fst c bE = x ≫ pullback.snd b c := by
    simp only [xE, a, t, Category.assoc, pullbackSymmetry_inv_comp_fst,
      pullback.map, pullback.lift_snd, Category.comp_id]
  have hxEs : xE ≫ pullback.snd c bE =
      x ≫ pullback.fst b c ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom) := by
    simp only [xE, a, t, Category.assoc, pullbackSymmetry_inv_comp_snd,
      pullback.map, pullback.lift_fst]
  have hmoveS : e.hom ≫ pS ≠ pS := by
    intro hfix
    apply hy
    apply (fiberObjEquivHom (x ≫ t) N).injective
    ext1
    have hact := fundamentalGroupHom_point_of_point_action t x g
      (Spec.preimage e.hom).hom
      (fun W w => (fiberSourceIso_aut_point x e hx W w).trans
        (congrArg (fun f => f ≫ (fiberObjEquivHom x W w).left)
          (Spec.map_preimage e.hom).symm)) N y
    exact hact.trans ((congrArg (fun f => f ≫ pS) (Spec.map_preimage e.hom)).trans hfix)
  refine ⟨E, hE, hCE, M, inferInstance, inferInstance, sM, pM,
    pullback.lift_snd _ _ _, ?_, ?_, ?_⟩
  · exact (Category.assoc pM M.hom (pullback.fst c bE)).symm.trans
      ((congrArg (fun q : Spec (.of Ω) ⟶ CE => q ≫ pullback.fst c bE) hpMx).trans hxEf)
  · exact (Category.assoc pM M.hom (pullback.snd c bE)).symm.trans
      ((congrArg (fun q : Spec (.of Ω) ⟶ CE => q ≫ pullback.snd c bE) hpMx).trans hxEs)
  · intro hfix
    apply hmoveS
    have h := congrArg (fun q => q ≫ r) hfix
    simpa only [Category.assoc, hpM] using h

end EtaleFundamentalGroups
