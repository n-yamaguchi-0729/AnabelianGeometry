/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Nyll.SchemeTheory.LocalGeometry.Points
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The connected geometric cover after rebasing onto full constants

A finite étale cover with a geometrically integral structure over a finite
constant extension gives a connected finite étale cover of the original
geometric base. Its source is the literal base change over the new constants,
not the generally disconnected base change over the old constants. Both
original coordinate maps are retained.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

/-- Rebase the original finite étale cover through its geometrically
integral constant-field structure and retain its actual two projections.
In particular this selects one connected geometric component without
counting all old-constant components together. -/
theorem exists_geometricCover_rebase
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra k κ] [Algebra E κ] [IsScalarTower k E κ]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of k)) (W : FiniteEtale X)
    (cE : W.left ⟶ Spec (.of E)) [GeometricallyIntegral cE]
    (hbase : cE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) = W.hom ≫ c) :
    let _φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let φκ := Spec.map (CommRingCat.ofHom (algebraMap k κ))
    let ψ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    IsIntegral (show Scheme.{u} from Limits.pullback ψ cE) ∧
      ∃ a : Limits.pullback ψ cE ⟶ Limits.pullback φκ c,
        IsFiniteEtale a ∧
        a ≫ pullback.fst φκ c = pullback.fst ψ cE ∧
        a ≫ pullback.snd φκ c = pullback.snd ψ cE ≫ W.hom := by
  intro φE φκ ψ
  have hφ : IsFiniteEtale φE := constantField_specMap_isFiniteEtale k E
  have hW : IsFiniteEtale W.hom := W.prop
  let t : W.left ⟶ Limits.pullback φE c := pullback.lift cE W.hom hbase
  have ht₁ : t ≫ pullback.fst φE c = cE := pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd φE c = W.hom := pullback.lift_snd _ _ _
  have : IsFinite (t ≫ pullback.snd φE c) := ht₂.symm ▸ hW.toIsFinite
  have : Etale (t ≫ pullback.snd φE c) := ht₂.symm ▸ hW.toEtale
  have htFinite : IsFinite t := IsFinite.of_comp t (pullback.snd φE c)
  have htEtale : Etale t := Etale.of_comp t (pullback.snd φE c)
  have ht : IsFiniteEtale t := ⟨⟩
  let b : Limits.pullback ψ cE ⟶ Limits.pullback ψ (pullback.fst φE c) :=
    pullback.lift (pullback.fst ψ cE) (pullback.snd ψ cE ≫ t)
      (by rw [Category.assoc, ht₁]; exact pullback.condition)
  have hb₁ : b ≫ pullback.fst ψ (pullback.fst φE c) = pullback.fst ψ cE :=
    pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd ψ (pullback.fst φE c) = pullback.snd ψ cE ≫ t :=
    pullback.lift_snd _ _ _
  have hb : IsPullback b (pullback.snd ψ cE) (pullback.snd ψ (pullback.fst φE c)) t := by
    refine IsPullback.of_right ?_ hb₂ (.of_hasPullback ψ (pullback.fst φE c))
    rw [hb₁, ht₁]
    exact .of_hasPullback ψ cE
  have hbFinite : IsFiniteEtale b :=
    MorphismProperty.of_isPullback (P := @IsFiniteEtale) hb.flip ht
  have hcoeff : ψ ≫ φE = φκ := by
    change Spec.map (CommRingCat.ofHom (algebraMap E κ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) =
        Spec.map (CommRingCat.ofHom (algebraMap k κ))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext a
    exact (IsScalarTower.algebraMap_apply k E κ a).symm
  let T : Limits.pullback ψ (pullback.fst φE c) ≅ Limits.pullback φκ c :=
    pullbackRightPullbackFstIso φE c ψ ≪≫ pullback.congrHom hcoeff rfl
  have hT₁ : T.hom ≫ pullback.fst φκ c = pullback.fst ψ (pullback.fst φE c) := by
    simp only [T, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]
  have hT₂ : T.hom ≫ pullback.snd φκ c =
      pullback.snd ψ (pullback.fst φE c) ≫ pullback.snd φE c := by
    simp only [T, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd]
  have hIntegral : IsIntegral (show Scheme.{u} from Limits.pullback ψ cE) :=
    GeometricallyIntegral.geometrically_isIntegral (f := cE) ψ
      (pullback.snd ψ cE) (pullback.fst ψ cE) (IsPullback.of_hasPullback ψ cE).flip
  have : IsFiniteEtale T.hom := ⟨⟩
  refine ⟨hIntegral, b ≫ T.hom, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hT₁, hb₁]
  · rw [Category.assoc, hT₂, ← Category.assoc, hb₂, Category.assoc, ht₂]

/-- Domination of original finite étale covers remains surjective on the
selected connected geometric components after compatible rebasing of their
constant fields. The two original coefficient maps determine the actual
component map; its finiteness, étaleness and surjectivity are conclusions. -/
theorem exists_surjective_geometricCover_rebase_map
    (k E₁ E₂ κ : Type u) [Field k] [Field E₁] [Field E₂] [Field κ]
    [Algebra k E₁] [Algebra k E₂] [Algebra k κ]
    [Algebra E₁ κ] [Algebra E₂ κ]
    [IsScalarTower k E₁ κ] [IsScalarTower k E₂ κ]
    [FiniteDimensional k E₁] [FiniteDimensional k E₂]
    [Algebra.IsSeparable k E₁] [Algebra.IsSeparable k E₂]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of k))
    (W₁ W₂ : FiniteEtale X)
    (c₁ : W₁.left ⟶ Spec (.of E₁)) (c₂ : W₂.left ⟶ Spec (.of E₂))
    [GeometricallyIntegral c₁] [GeometricallyIntegral c₂]
    (hbase₁ : c₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₁)) = W₁.hom ≫ c)
    (hbase₂ : c₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₂)) = W₂.hom ≫ c)
    (t : W₁.left ⟶ W₂.left) (ht : t ≫ W₂.hom = W₁.hom)
    (φ : Spec (.of E₁) ⟶ Spec (.of E₂))
    (hcoeff : Spec.map (CommRingCat.ofHom (algebraMap E₁ κ)) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap E₂ κ)))
    (hstruct : t ≫ c₂ = c₁ ≫ φ) :
    let ψ₁ := Spec.map (CommRingCat.ofHom (algebraMap E₁ κ))
    let ψ₂ := Spec.map (CommRingCat.ofHom (algebraMap E₂ κ))
    ∃ tκ : Limits.pullback ψ₁ c₁ ⟶ Limits.pullback ψ₂ c₂,
      IsFiniteEtale tκ ∧ Function.Surjective tκ ∧
      tκ ≫ pullback.fst ψ₂ c₂ = pullback.fst ψ₁ c₁ ∧
      tκ ≫ pullback.snd ψ₂ c₂ = pullback.snd ψ₁ c₁ ≫ t := by
  intro ψ₁ ψ₂
  obtain ⟨hI₁, a₁, ha₁, ha₁fst, ha₁snd⟩ :=
    exists_geometricCover_rebase k E₁ κ c W₁ c₁ hbase₁
  obtain ⟨hI₂, a₂, ha₂, ha₂fst, ha₂snd⟩ :=
    exists_geometricCover_rebase k E₂ κ c W₂ c₂ hbase₂
  let tκ : Limits.pullback ψ₁ c₁ ⟶ Limits.pullback ψ₂ c₂ :=
    pullback.lift (pullback.fst ψ₁ c₁) (pullback.snd ψ₁ c₁ ≫ t) (by
      rw [Category.assoc, hstruct, ← Category.assoc,
        ← pullback.condition, Category.assoc, hcoeff])
  have hfst : tκ ≫ pullback.fst ψ₂ c₂ = pullback.fst ψ₁ c₁ :=
    pullback.lift_fst _ _ _
  have hsnd : tκ ≫ pullback.snd ψ₂ c₂ = pullback.snd ψ₁ c₁ ≫ t :=
    pullback.lift_snd _ _ _
  have : IsIntegral (Limits.pullback ψ₁ c₁) := hI₁
  have : IsIntegral (Limits.pullback ψ₂ c₂) := hI₂
  have : IsFiniteEtale a₂ := ha₂
  have ha : tκ ≫ a₂ = a₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ha₂fst, hfst, ha₁fst]
    · rw [Category.assoc, ha₂snd, ← Category.assoc, hsnd,
        Category.assoc, ht, ha₁snd]
  have : IsFinite (tκ ≫ a₂) := ha.symm ▸ ha₁.toIsFinite
  have : Etale (tκ ≫ a₂) := ha.symm ▸ ha₁.toEtale
  have : IsFinite tκ := IsFinite.of_comp tκ a₂
  have : Etale tκ := Etale.of_comp tκ a₂
  have hfinite : IsFiniteEtale tκ := ⟨⟩
  have hsurj : Surjective tκ := IsFiniteEtale.surjective tκ
  exact ⟨tκ, hfinite, tκ.surjective, hfst, hsnd⟩

/-- A geometric point on the dominated cover lifts while retaining the
chosen full-constant embedding of the dominating cover. Applying this at
omitted points proves boundary growth on the selected connected component,
rather than on the union of all old-constant components. -/
theorem exists_geometricPoint_lift_after_constant_rebase
    (k E₁ E₂ κ : Type u) [Field k] [Field E₁] [Field E₂] [Field κ] [IsAlgClosed κ]
    [Algebra k E₁] [Algebra k E₂] [Algebra k κ]
    [Algebra E₁ κ] [Algebra E₂ κ]
    [IsScalarTower k E₁ κ] [IsScalarTower k E₂ κ]
    [FiniteDimensional k E₁] [FiniteDimensional k E₂]
    [Algebra.IsSeparable k E₁] [Algebra.IsSeparable k E₂]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of k))
    (W₁ W₂ : FiniteEtale X)
    (c₁ : W₁.left ⟶ Spec (.of E₁)) (c₂ : W₂.left ⟶ Spec (.of E₂))
    [GeometricallyIntegral c₁] [GeometricallyIntegral c₂]
    (hbase₁ : c₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₁)) = W₁.hom ≫ c)
    (hbase₂ : c₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E₂)) = W₂.hom ≫ c)
    (t : W₁.left ⟶ W₂.left) (ht : t ≫ W₂.hom = W₁.hom)
    (φ : Spec (.of E₁) ⟶ Spec (.of E₂))
    (hcoeff : Spec.map (CommRingCat.ofHom (algebraMap E₁ κ)) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap E₂ κ)))
    (hstruct : t ≫ c₂ = c₁ ≫ φ)
    (p₂ : Spec (.of κ) ⟶ W₂.left)
    (hp₂ : p₂ ≫ c₂ = Spec.map (CommRingCat.ofHom (algebraMap E₂ κ))) :
    ∃ p₁ : Spec (.of κ) ⟶ W₁.left,
      p₁ ≫ t = p₂ ∧
      p₁ ≫ c₁ = Spec.map (CommRingCat.ofHom (algebraMap E₁ κ)) := by
  let ψ₁ := Spec.map (CommRingCat.ofHom (algebraMap E₁ κ))
  let ψ₂ := Spec.map (CommRingCat.ofHom (algebraMap E₂ κ))
  obtain ⟨tκ, hfinite, hsurj, hfst, hsnd⟩ :=
    exists_surjective_geometricCover_rebase_map k E₁ E₂ κ c W₁ W₂
      c₁ c₂ hbase₁ hbase₂ t ht φ hcoeff hstruct
  have : IsFiniteEtale tκ := hfinite
  have : Surjective tκ := ⟨hsurj⟩
  let s₂ : Spec (.of κ) ⟶ Limits.pullback ψ₂ c₂ :=
    pullback.lift (𝟙 _) p₂ ((Category.id_comp ψ₂).trans hp₂.symm)
  obtain ⟨s₁, hs₁⟩ :=
    exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed tκ s₂
  refine ⟨s₁ ≫ pullback.snd ψ₁ c₁, ?_, ?_⟩
  · rw [Category.assoc, ← hsnd, ← Category.assoc, hs₁]
    exact pullback.lift_snd _ _ _
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      ← hfst, ← Category.assoc, hs₁, pullback.lift_fst, Category.id_comp]

end AlgebraicGeometry.FiniteEtale
