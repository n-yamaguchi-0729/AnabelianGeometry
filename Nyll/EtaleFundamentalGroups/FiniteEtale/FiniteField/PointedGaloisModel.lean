/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PointModel
public import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedBaseChange
public import Nyll.EtaleFundamentalGroups.GaloisCovers.PointedGaloisFiber
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteTowerModel
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GaloisModel
public import Nyll.EtaleFundamentalGroups.GaloisCovers.IsomorphismTransport
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Finite constant models preserving abelian deck groups and rational lifts

The first result descends an original geometric abelian Galois cover with
its native deck group. The second enlarges an existing finite model until
an original geometric lift becomes rational. Connectedness is descended
from the original geometric cover; the actual pullback then preserves its
Galois and abelian properties.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- Finite coefficient descent of an original abelian Galois cover preserves
abelianity of its actual deck group. -/
theorem exists_finiteIntermediateField_abelian_galois_scheme_model
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (c : X ⟶ Spec (.of k)) :
    let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let XL := Limits.pullback φL c
    ∀ [ConnectedSpace XL] (Z : FiniteEtale XL)
      [IsGalois Z] [IsMulCommutative (Aut Z)],
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
      let XE := Limits.pullback φE c
      ∃ hXE : ConnectedSpace XE,
        let _ : ConnectedSpace XE := hXE
        ∃ Y : FiniteEtale XE,
          IsGalois Y ∧ IsMulCommutative (Aut Y) ∧ Nat.card (Aut Y) = Nat.card (Aut Z) ∧
          Nonempty ((FiniteEtale.pullback
            (Limits.pullback.map φL c φE c
              (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 X) (𝟙 _)
              (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
              (by rw [Category.comp_id, Category.id_comp]))).obj Y ≅ Z) := by
  intro φL XL hXL Z hZ hcommZ
  obtain ⟨E, hE, hXE, Y, hY, hcard, ⟨e⟩⟩ :=
    FiniteEtale.exists_finiteIntermediateField_galois_scheme_model k L X c Z
  let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let XE := Limits.pullback φE c
  have hconnectedE : ConnectedSpace XE := hXE
  have hGaloisY : IsGalois Y := hY
  let b : XL ⟶ XE := Limits.pullback.map φL c φE c
    (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  have hsurj : Surjective b := by
    have hb : (constantFieldTowerIso k L E X c).inv ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom E.val.toRingHom))
          (Limits.pullback.fst φE c) = b :=
      constantFieldTowerIso_inv_snd k L E X c
    rw [← hb]
    infer_instance
  let F := FiniteEtale.pullback b
  have hfaithful : F.Faithful := FiniteEtale.pullback_faithful_of_isDominant b
  let A := Aut.autMulEquivOfIso e
  have hcommY : IsMulCommutative (Aut Y) := .of_comm fun σ τ => by
    apply Aut.ext
    apply Iso.ext
    apply F.map_injective
    have h : F.mapAut Y (σ * τ) = F.mapAut Y (τ * σ) := by
      apply A.injective
      rw [map_mul, map_mul, map_mul, map_mul, mul_comm']
    exact congrArg (fun ζ : Aut (F.obj Y) => ζ.asIso.hom) h
  exact ⟨E, hE, hXE, Y, hY, hcommY, hcard, ⟨e⟩⟩

/-- Once a Galois cover is geometrically connected, adjoining the finitely
many coefficients of an original lift gives a rationally pointed Galois
base change with the same abelian deck group and original recovery map. -/
theorem exists_finiteIntermediateField_pointed_galois_baseChange
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} [ConnectedSpace X]
    (c : X ⟶ Spec (.of k)) (Y : FiniteEtale X)
    [IsGalois Y] [IsMulCommutative (Aut Y)]
    (ε : Spec (.of k) ⟶ X) (hε : ε ≫ c = 𝟙 _)
    (q : Spec (.of L) ⟶ Y.left)
    (hq : q ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ ε) :
    let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let XL := Limits.pullback φL c
    let YL := (FiniteEtale.pullback (Limits.pullback.snd φL c)).obj Y
    ∀ [ConnectedSpace XL] [IsConnected YL],
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
      let XE := Limits.pullback φE c
      let jE : XE ⟶ X := Limits.pullback.snd φE c
      let YE := (FiniteEtale.pullback jE).obj Y
      let εE : Spec (.of E) ⟶ XE := Limits.pullback.lift (𝟙 _) (φE ≫ ε)
        (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
      ∃ hXE : ConnectedSpace XE,
        let _ : ConnectedSpace XE := hXE
        IsGalois YE ∧ IsMulCommutative (Aut YE) ∧
        ∃ s : Spec (.of E) ⟶ YE.left,
          s ≫ YE.hom = εE ∧
          Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ s ≫
            Limits.pullback.fst Y.hom jE = q := by
  intro φL XL YL hXL hYL
  obtain ⟨E, hE, s, hs, hrec⟩ :=
    exists_finiteIntermediateField_pointedBaseChange k L c Y ε hε q hq
  let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let XE := Limits.pullback φE c
  let jE : XE ⟶ X := Limits.pullback.snd φE c
  let YE := (FiniteEtale.pullback jE).obj Y
  let b : XL ⟶ XE := Limits.pullback.map φL c φE c
    (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  have hsurj : Surjective b := by
    have hb : (constantFieldTowerIso k L E X c).inv ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom E.val.toRingHom))
          (Limits.pullback.fst φE c) = b :=
      constantFieldTowerIso_inv_snd k L E X c
    rw [← hb]
    infer_instance
  have hXE : ConnectedSpace XE := b.surjective.connectedSpace b.continuous
  have hb : b ≫ jE = Limits.pullback.snd φL c := by
    exact (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let P := (FiniteEtale.pullback b).obj YE
  let e : P ≅ YL := FiniteEtale.finiteEtalePullbackCompObjIso b jE
    (Limits.pullback.snd φL c) hb Y
  have hconnectedYL : ConnectedSpace YL.left :=
    FiniteEtale.connectedSpace_left_of_isConnected YL
  let forget := FiniteEtale.forget XL ⋙ Over.forget XL
  have hconnectedP : ConnectedSpace P.left :=
    (forget.mapIso e).hom.homeomorph.connectedSpace_iff.mpr hconnectedYL
  let p : P.left ⟶ YE.left := Limits.pullback.fst YE.hom b
  have hsurjP : Surjective p := inferInstanceAs (Surjective (Limits.pullback.fst YE.hom b))
  have hconnectedYE : ConnectedSpace YE.left := p.surjective.connectedSpace p.continuous
  have hYE : IsConnected YE := FiniteEtale.isConnected_of_connectedSpace_left YE
  have hsurjE : Surjective jE := inferInstanceAs (Surjective (Limits.pullback.snd φE c))
  exact ⟨E, hE, hXE,
    (isGalois_pullback_and_bijective_mapAut_of_isConnected jE Y).1,
    isMulCommutative_aut_pullback_of_isConnected jE Y, s, hs, hrec⟩

/-- Every original geometric abelian Galois cover has a finite constant
model with an actual rational lift of the chosen base point. The recovery
isomorphism uses the literal inclusion of that finite constant field. -/
theorem exists_finiteIntermediateField_pointed_abelian_galois_model
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] [IsSepClosed L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (c : X ⟶ Spec (.of k))
    (ε : Spec (.of k) ⟶ X) (hε : ε ≫ c = 𝟙 _) :
    let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let XL := Limits.pullback φL c
    ∀ [ConnectedSpace XL] (Z : FiniteEtale XL)
      [IsGalois Z] [IsMulCommutative (Aut Z)],
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      let φF := Spec.map (CommRingCat.ofHom (algebraMap k F))
      let XF := Limits.pullback φF c
      let εF : Spec (.of F) ⟶ XF := Limits.pullback.lift (𝟙 _) (φF ≫ ε)
        (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
      ∃ hXF : ConnectedSpace XF,
        let _ : ConnectedSpace XF := hXF
        ∃ N : FiniteEtale XF,
          IsGalois N ∧ IsMulCommutative (Aut N) ∧
          Nonempty ((FiniteEtale.pullback
            (Limits.pullback.map φL c φF c
              (Spec.map (CommRingCat.ofHom F.val.toRingHom)) (𝟙 X) (𝟙 _)
              (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
              (by rw [Category.comp_id, Category.id_comp]))).obj N ≅ Z) ∧
          ∃ s : Spec (.of F) ⟶ N.left, s ≫ N.hom = εF := by
  intro φL XL hXL Z hZ hcommZ
  obtain ⟨H, hH, hXH, Y, hY, hcommY, _, ⟨eY⟩⟩ :=
    exists_finiteIntermediateField_abelian_galois_scheme_model k L X c Z
  have hfiniteH : FiniteDimensional k H := hH
  let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
  let ψH := Spec.map (CommRingCat.ofHom (algebraMap H L))
  let XH := Limits.pullback φH c
  let cH : XH ⟶ Spec (.of H) := Limits.pullback.fst φH c
  have hconnectedH : ConnectedSpace XH := hXH
  have hGaloisY : IsGalois Y := hY
  have habelianY : IsMulCommutative (Aut Y) := hcommY
  let bH : XL ⟶ XH := Limits.pullback.map φL c φH c ψH (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  let U := Limits.pullback ψH cH
  let jL : U ⟶ XH := Limits.pullback.snd ψH cH
  let eX : U ≅ XL := constantFieldTowerIso k L H X c
  have hU : ConnectedSpace U :=
    eX.hom.homeomorph.connectedSpace_iff.mpr hXL
  let P := (FiniteEtale.pullback jL).obj Y
  let Z' := (FiniteEtale.pullback eX.hom).obj Z
  have hZ' : IsGalois Z' :=
    (FiniteEtale.isGalois_pullback_and_card_aut_of_isIso eX.hom Z).1
  let eP : P ≅ Z' :=
    (FiniteEtale.finiteEtalePullbackCompObjIso eX.hom bH jL
      (constantFieldTowerIso_hom_coefficientMap k L H X c) Y).symm ≪≫
        (FiniteEtale.pullback eX.hom).mapIso eY
  have hP : IsGalois P := FiniteEtale.isGalois_of_iso eP.symm
  let εH : Spec (.of H) ⟶ XH := Limits.pullback.lift (𝟙 _) (φH ≫ ε)
    (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
  have hεH : εH ≫ cH = 𝟙 _ := Limits.pullback.lift_fst _ _ _
  have hconnectedY : ConnectedSpace Y.left :=
    FiniteEtale.connectedSpace_left_of_isConnected Y
  have hEtaleY : IsFiniteEtale Y.hom := Y.prop
  have hpreconnectedH : PreconnectedSpace ↑((Functor.fromPUnit XH).obj Y.right) := by
    change PreconnectedSpace XH
    infer_instance
  have hnonemptyY : Nonempty ((Functor.id Scheme).obj Y.left) := by
    change Nonempty Y.left
    infer_instance
  have hsurjY : Surjective Y.hom := IsFiniteEtale.surjective Y.hom
  obtain ⟨y, hy⟩ := Y.hom.surjective ((ψH ≫ εH) (IsLocalRing.closedPoint L))
  obtain ⟨q, hq, _⟩ := FiniteEtale.exists_geometricPoint_lift_through
    Y (ψH ≫ εH) y hy
  obtain ⟨E, hE, hXE, hYE, hcommYE, s, hs, _⟩ :=
    exists_finiteIntermediateField_pointed_galois_baseChange H L cH Y εH hεH q hq
  have hfiniteE : FiniteDimensional H E := hE
  let η := Spec.map (CommRingCat.ofHom (algebraMap H E))
  let XE := Limits.pullback η cH
  let jE : XE ⟶ XH := Limits.pullback.snd η cH
  let YE := (FiniteEtale.pullback jE).obj Y
  let εE : Spec (.of E) ⟶ XE := Limits.pullback.lift (𝟙 _) (η ≫ εH)
    (by rw [Category.id_comp, Category.assoc, hεH, Category.comp_id])
  have hconnectedE : ConnectedSpace XE := hXE
  have hGaloisYE : IsGalois YE := hYE
  have habelianYE : IsMulCommutative (Aut YE) := hcommYE
  let F : IntermediateField k L := E.restrictScalars k
  have hfiniteF : FiniteDimensional k F := FiniteDimensional.trans k H E
  let φF := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let XF := Limits.pullback φF c
  let εF : Spec (.of E) ⟶ XF := Limits.pullback.lift (𝟙 _) (φF ≫ ε)
    (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
  let eF : XE ≅ XF := finiteIntermediateTowerIso k L H E X c
  have hXF : ConnectedSpace XF := eF.hom.homeomorph.connectedSpace_iff.mp hXE
  let N := (FiniteEtale.pullback eF.inv).obj YE
  have hN : IsGalois N := (FiniteEtale.isGalois_pullback_and_card_aut_of_isIso eF.inv YE).1
  have hcommN : IsMulCommutative (Aut N) :=
    isMulCommutative_aut_pullback_of_isConnected eF.inv YE
  have hεF : εE ≫ eF.hom = εF := by
    have hfst : eF.hom ≫ Limits.pullback.fst φF c =
        Limits.pullback.fst η cH := finiteIntermediateTowerIso_hom_fst k L H E X c
    have hsnd : eF.hom ≫ Limits.pullback.snd φF c =
        jE ≫ Limits.pullback.snd φH c := finiteIntermediateTowerIso_hom_snd k L H E X c
    have hcoeff : η ≫ φH = φF := by rw [← Spec.map_comp]; rfl
    apply Limits.pullback.hom_ext
    · calc
        (εE ≫ eF.hom) ≫ Limits.pullback.fst φF c =
            εE ≫ (eF.hom ≫ Limits.pullback.fst φF c) := Category.assoc _ _ _
        _ = εE ≫ Limits.pullback.fst η cH :=
          congrArg (fun f : XE ⟶ Spec (.of E) => εE ≫ f) hfst
        _ = 𝟙 (Spec (.of E)) := Limits.pullback.lift_fst _ _ _
        _ = εF ≫ Limits.pullback.fst φF c := (Limits.pullback.lift_fst _ _ _).symm
    · calc
        (εE ≫ eF.hom) ≫ Limits.pullback.snd φF c =
            εE ≫ (eF.hom ≫ Limits.pullback.snd φF c) := Category.assoc _ _ _
        _ = εE ≫ (jE ≫ Limits.pullback.snd φH c) :=
          congrArg (fun f : XE ⟶ X => εE ≫ f) hsnd
        _ = (εE ≫ jE) ≫ Limits.pullback.snd φH c := (Category.assoc _ _ _).symm
        _ = (η ≫ εH) ≫ Limits.pullback.snd φH c :=
          congrArg (fun f : Spec (.of E) ⟶ XH => f ≫ Limits.pullback.snd φH c)
            (Limits.pullback.lift_snd _ _ _)
        _ = η ≫ (εH ≫ Limits.pullback.snd φH c) := Category.assoc _ _ _
        _ = η ≫ (φH ≫ ε) :=
          congrArg (fun f : Spec (.of H) ⟶ X => η ≫ f) (Limits.pullback.lift_snd _ _ _)
        _ = (η ≫ φH) ≫ ε := (Category.assoc _ _ _).symm
        _ = φF ≫ ε := congrArg (fun f : Spec (.of E) ⟶ Spec (.of k) => f ≫ ε) hcoeff
        _ = εF ≫ Limits.pullback.snd φF c := (Limits.pullback.lift_snd _ _ _).symm
  let cE := finiteIntermediateTowerProjection k L H E X c
  have hstage : cE ≫ jE = jL := by
    exact (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let eStage : (FiniteEtale.pullback cE).obj YE ≅ Z' :=
    FiniteEtale.finiteEtalePullbackCompObjIso cE jE jL hstage Y ≪≫ eP
  let eRecovery := finiteIntermediateTowerModelRecoveryIso k L H E X c YE Z eStage
  have hpoint : s ≫ YE.hom = εF ≫ eF.inv := by
    have hs' : s ≫ YE.hom = εE := hs
    calc
      s ≫ YE.hom = εE := hs'
      _ = εE ≫ 𝟙 XE := (Category.comp_id εE).symm
      _ = εE ≫ (eF.hom ≫ eF.inv) :=
        congrArg (fun f : XE ⟶ XE => εE ≫ f) eF.hom_inv_id.symm
      _ = (εE ≫ eF.hom) ≫ eF.inv := (Category.assoc _ _ _).symm
      _ = εF ≫ eF.inv := congrArg (fun f : Spec (.of E) ⟶ XF => f ≫ eF.inv) hεF
  let sN : Spec (.of E) ⟶ N.left := Limits.pullback.lift s εF hpoint
  exact ⟨F, hfiniteF, hXF, N, hN, hcommN, ⟨eRecovery⟩,
    sN, Limits.pullback.lift_snd _ _ _⟩

end EtaleFundamentalGroups
