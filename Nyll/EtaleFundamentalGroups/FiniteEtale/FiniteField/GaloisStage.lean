/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldLimit
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredStageRecovery
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemePairDescent
public import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Connected.Basic

/-!
# Preserving the Galois group at a finite coefficient stage

Let a finite étale cover of a qcqs scheme become Galois over an algebraic
coefficient extension. All of its geometric deck transformations descend
simultaneously to one finite coefficient stage. Faithfully flat descent
proves that the descended maps are automorphisms. Their recovery equations
make the map from the original finite set of automorphisms injective.

Connectedness descends along the actual coefficient projections. Degree
invariance and the bound on automorphisms of a connected cover then prove
that the finite-stage cover is Galois and has exactly the original group
order. In particular, a prime-to-characteristic order is preserved without
passing to a larger Galois closure.

The input cover here is an existing model over the base field. Applying
this result after finite coefficient descent of an arbitrary geometric
cover gives the Galois model used in specialization.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- A cover that is geometrically Galois becomes Galois at an actual finite
coefficient stage, with the same automorphism-group order and a recovery
isomorphism for the literal coefficient inclusion. -/
theorem exists_finiteIntermediateField_galois_stage
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k)) (Y : FiniteEtale X) :
    let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let U : Scheme.{u} := pullback φL f
    let P := (FiniteEtale.pullback (pullback.snd φL f)).obj Y
    ∀ [ConnectedSpace U] [IsGalois P],
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      let H := IntermediateField.adjoin k (s : Set L)
      let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
      let U₀ : Scheme.{u} := pullback φH f
      ∃ hU₀ : ConnectedSpace U₀,
        let : ConnectedSpace U₀ := hU₀
        ∃ N : FiniteEtale U₀, IsGalois N ∧ Nat.card (Aut N) = Nat.card (Aut P) ∧
          Nonempty ((FiniteEtale.pullback
            ((constantFieldInverseLimitCone k L X f).π.app (op s))).obj N ≅ P) := by
  intro φL U P hU hP
  let y : Y.left ⟶ X := Y.hom
  have : IsFiniteEtale y := Y.prop
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace y
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated y
  let V : Scheme.{u} := pullback φL (y ≫ f)
  let l : V ⟶ U := coefficientModelMap φL f y
  have hlFst : l ≫ pullback.fst φL f = pullback.fst φL (y ≫ f) :=
    pullback.lift_fst _ _ _
  have hlSnd : l ≫ pullback.snd φL f = pullback.snd φL (y ≫ f) ≫ y :=
    pullback.lift_snd _ _ _
  have hCoeff := coefficientBaseChange_isPullback φL f y
  have : IsFiniteEtale l := MorphismProperty.of_isPullback
    (P := @IsFiniteEtale) hCoeff.flip inferInstance
  let Q : FiniteEtale U := FiniteEtale.mk l
  let e : Q ≅ P := MorphismProperty.Over.isoMk hCoeff.flip.isoPullback
    hCoeff.flip.isoPullback_hom_snd
  let F : FiniteEtale U ⥤ Scheme.{u} := FiniteEtale.forget U ⋙ Over.forget U
  let a (σ : Aut P) : Aut Q := (Aut.autMulEquivOfIso e).symm σ
  let α (σ : Aut P) : Aut V := F.mapAut Q (a σ)
  have hα (σ : Aut P) : (α σ).asIso.hom ≫ l = l :=
    MorphismProperty.Over.w (a σ).asIso.hom
  have hαL (σ : Aut P) :
      (α σ).asIso.hom ≫ pullback.fst φL (y ≫ f) = pullback.fst φL (y ≫ f) := by
    simpa only [Category.assoc, hlFst] using
      congrArg (fun h : V ⟶ U => h ≫ pullback.fst φL f) (hα σ)
  have hαX (σ : Aut P) :
      (α σ).asIso.hom ≫ pullback.snd φL (y ≫ f) ≫ y =
        pullback.snd φL (y ≫ f) ≫ y := by
    simpa only [Category.assoc, hlSnd] using
      congrArg (fun h : V ⟶ U => h ≫ pullback.snd φL f) (hα σ)
  obtain ⟨s, hs, g, hg⟩ := exists_finiteIntermediateField_schemePairHom_family
    k L X f (fun _ : Aut P => Y.left) (fun _ : Aut P => Y.left)
    (fun _ : Aut P => y) (fun _ : Aut P => y)
    (fun σ : Aut P => (α σ).asIso.hom) hαX hαL
  let H := IntermediateField.adjoin k (s : Set L)
  let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
  let ψ := Spec.map (CommRingCat.ofHom H.val.toRingHom)
  let U₀ : Scheme.{u} := pullback φH f
  let V₀ : Scheme.{u} := pullback φH (y ≫ f)
  let l₀ : V₀ ⟶ U₀ := coefficientModelMap φH f y
  have hl₀Fst : l₀ ≫ pullback.fst φH f = pullback.fst φH (y ≫ f) :=
    pullback.lift_fst _ _ _
  have hl₀Snd : l₀ ≫ pullback.snd φH f = pullback.snd φH (y ≫ f) ≫ y :=
    pullback.lift_snd _ _ _
  let cX : U ⟶ U₀ := (constantFieldInverseLimitCone k L X f).π.app (op s)
  let cY : V ⟶ V₀ := (constantFieldInverseLimitCone k L Y.left (y ≫ f)).π.app (op s)
  have hX : IsPullback cX (pullback.fst φL f) (pullback.fst φH f) ψ :=
    constantFieldInverseLimitCone_π_app_isPullback k L X f s
  have hY : IsPullback cY (pullback.fst φL (y ≫ f))
      (pullback.fst φH (y ≫ f)) ψ :=
    constantFieldInverseLimitCone_π_app_isPullback k L Y.left (y ≫ f) s
  have : Surjective cX := MorphismProperty.of_isPullback
    (P := @Surjective) hX.flip inferInstance
  have : Surjective cY := MorphismProperty.of_isPullback
    (P := @Surjective) hY.flip inferInstance
  have hU₀ : ConnectedSpace U₀ := cX.surjective.connectedSpace cX.continuous
  have : ConnectedSpace P.left := FiniteEtale.connectedSpace_left_of_isConnected P
  have : ConnectedSpace V := (F.mapIso e).hom.homeomorph.connectedSpace_iff.mpr
    (inferInstance : ConnectedSpace P.left)
  have : ConnectedSpace V₀ := cY.surjective.connectedSpace cY.continuous
  have : IsFiniteEtale l₀ := MorphismProperty.of_isPullback
    (P := @IsFiniteEtale) (coefficientBaseChange_isPullback φH f y).flip inferInstance
  let N : FiniteEtale U₀ := FiniteEtale.mk l₀
  have : ConnectedSpace N.left := inferInstanceAs (ConnectedSpace V₀)
  have : IsConnected N := FiniteEtale.isConnected_of_connectedSpace_left N
  have hgIso (σ : Aut P) : IsIso (g σ) := by
    have : IsIso (α σ).asIso.hom := (α σ).asIso.isIso_hom
    exact isIso_of_constantFieldStageHom k L Y.left Y.left (y ≫ f) (y ≫ f) s
      (α σ).asIso.hom (g σ) (hαL σ) (hg σ).1 (hg σ).2.2
  have hgBase (σ : Aut P) : g σ ≫ l₀ = l₀ := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, hl₀Fst] using (hg σ).1
    · simpa only [Category.assoc, hl₀Snd] using (hg σ).2.1
  let γ (σ : Aut P) : V₀ ≅ V₀ := by
    have : IsIso (g σ) := hgIso σ
    exact asIso (g σ)
  have hγHom (σ : Aut P) : (γ σ).hom = g σ := by
    have : IsIso (g σ) := hgIso σ
    exact asIso_hom (g σ)
  let τ (σ : Aut P) : Aut N :=
    Aut.of (MorphismProperty.Over.isoMk (A := N) (B := N) (γ σ) (hgBase σ))
  let forgetAutHom (t : Aut N) : V₀ ⟶ V₀ := t.asIso.hom.left
  have hτHom (σ : Aut P) : forgetAutHom (τ σ) = g σ := by
    exact (MorphismProperty.Over.isoMk_hom_left (A := N) (B := N) (γ σ)
      (hgBase σ)).trans (hγHom σ)
  have hτ : Function.Injective τ := by
    intro σ σ' hσσ'
    have hgg : g σ = g σ' := by
      simpa only [hτHom] using congrArg forgetAutHom hσσ'
    have hrec : (α σ).asIso.hom ≫ cY = (α σ').asIso.hom ≫ cY :=
      (hg σ).2.2.symm.trans
        ((congrArg (fun h : V₀ ⟶ V₀ => cY ≫ h) hgg).trans (hg σ').2.2)
    have hcYs : cY ≫ pullback.snd φH (y ≫ f) = pullback.snd φL (y ≫ f) :=
      Over.w ((constantFieldInverseLimitOverCone k L Y.left (y ≫ f)).π.app (op s))
    have hαeq : (α σ).asIso.hom = (α σ').asIso.hom := by
      apply pullback.hom_ext
      · exact (hαL σ).trans (hαL σ').symm
      · simpa only [Category.assoc, hcYs] using
          congrArg (fun h : V ⟶ V₀ => h ≫ pullback.snd φH (y ≫ f)) hrec
    apply (Aut.autMulEquivOfIso e).symm.injective
    apply Aut.ext
    apply Iso.ext
    exact F.map_injective hαeq
  have hLower : Nat.card (Aut P) ≤ Nat.card (Aut N) :=
    Nat.card_le_card_of_injective τ hτ
  have hNat : cY ≫ l₀ = l ≫ cX :=
    coefficientModelMap_stage_naturality k L X f s Y.left y
  have hOuter : IsPullback (l ≫ pullback.fst φL f) cY ψ
      (l₀ ≫ pullback.fst φH f) := by
    rw [hlFst, hl₀Fst]
    exact hY.flip
  have hSquare : IsPullback cY l l₀ cX :=
    (IsPullback.of_right hOuter hNat.symm hX.flip).flip
  let eN : Q ≅ (FiniteEtale.pullback cX).obj N :=
    MorphismProperty.Over.isoMk hSquare.isoPullback hSquare.isoPullback_hom_snd
  let u : U := Classical.choice (inferInstance : Nonempty U)
  let Ω := AlgebraicClosure (U.residueField u)
  let ξ : Spec (.of Ω) ⟶ U :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u) Ω)) ≫
      U.fromSpecResidueField u
  let ω := IsLocalRing.closedPoint Ω
  have hRankQ : Q.hom.finrank (ξ ω) = Y.hom.finrank ((ξ ≫ pullback.snd φL f) ω) := by
    exact Scheme.Hom.finrank_of_isPullback (pullback.snd φL (y ≫ f)) l
      y (pullback.snd φL f) hCoeff.flip (ξ ω)
  have hRankP : P.hom.finrank (ξ ω) = Y.hom.finrank ((ξ ≫ pullback.snd φL f) ω) := by
    exact Scheme.Hom.finrank_of_isPullback (pullback.fst y (pullback.snd φL f))
      (pullback.snd y (pullback.snd φL f)) y (pullback.snd φL f)
      (IsPullback.of_hasPullback y (pullback.snd φL f)) (ξ ω)
  have hRankN : Q.hom.finrank (ξ ω) = N.hom.finrank ((ξ ≫ cX) ω) :=
    Scheme.Hom.finrank_of_isPullback cY l l₀ cX hSquare (ξ ω)
  have hDegree : Nat.card (Aut P) = N.hom.finrank ((ξ ≫ cX) ω) :=
    ((FiniteEtale.isGalois_iff_card_aut_eq_finrank ξ P).mp hP).trans
      (hRankP.trans (hRankQ.symm.trans hRankN))
  have hUpper : Nat.card (Aut N) ≤ N.hom.finrank ((ξ ≫ cX) ω) := by
    have h := card_aut_le_card_fiber_of_connected (FiniteEtale.fiber (ξ ≫ cX)) N
    rwa [FiniteEtale.natCard_fiber_eq_finrank (ξ ≫ cX) N] at h
  have hCard : Nat.card (Aut N) = Nat.card (Aut P) :=
    Nat.le_antisymm (hUpper.trans_eq hDegree.symm) hLower
  have hN : IsGalois N :=
    (FiniteEtale.isGalois_iff_card_aut_eq_finrank (ξ ≫ cX) N).mpr (hCard.trans hDegree)
  exact ⟨s, hs, hU₀, N, hN, hCard, ⟨eN.symm ≪≫ e⟩⟩

end EtaleFundamentalGroups
