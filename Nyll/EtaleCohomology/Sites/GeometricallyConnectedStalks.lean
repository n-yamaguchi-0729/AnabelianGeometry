/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.CechSections
public import Nyll.EtaleCohomology.Sites.PullbackStalkComposition
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleCohomology.Sites.SeparablyClosedBasePullback
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Common stalk values over geometrically connected fibres

Every section of actual inverse image is Čech-compatible. On each geometric
fibre, the actual inverse image from a separably closed field is fully
faithful, so the section has one original stalk value at all geometric
lifts. Composition of the actual stalk maps proves the Čech equation.
No flatness or quasi-compactness hypothesis is needed for this calculation.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private lemma stalkUnit_eqToIso
    {X Z : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    {f g : Z ⟶ X} (h : f = g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Z // s ≫ f = t})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction f Λ).unit.app F) ≫
      etalePushforwardStalkComponent f t s ((etalePullback f Λ).obj F)) ≫
      (Scheme.pointSmallEtale s.val).sheafFiber.map ((pullback_eq_iso Λ h).hom.app F) =
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction g Λ).unit.app F) ≫
      etalePushforwardStalkComponent g t
        ⟨s.val, by rw [← h]; exact s.property⟩ ((etalePullback g Λ).obj F) := by
  cases h
  let k : (Scheme.pointSmallEtale t).sheafFiber.obj F ⟶
      (Scheme.pointSmallEtale s.val).sheafFiber.obj ((etalePullback f Λ).obj F) :=
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction f Λ).unit.app F) ≫
      etalePushforwardStalkComponent f t s ((etalePullback f Λ).obj F)
  change k ≫ (Scheme.pointSmallEtale s.val).sheafFiber.map (𝟙 _) = k
  rw [(Scheme.pointSmallEtale s.val).sheafFiber.map_id, Category.comp_id]

private theorem unit_stalkComponent_isIso_of_lift
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) := by
  rcases s with ⟨s, rfl⟩
  exact etalePullbackUnit_stalkComponent_isIso q s Λ F

private theorem globalSectionsMap_germ_of_lift
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etalePullbackGlobalSectionsMap q Λ F ≫
        etaleGlobalSectionsGerm s.val Λ ((etalePullback q Λ).obj F) =
      etaleGlobalSectionsGerm t Λ F ≫
        (Scheme.pointSmallEtale t).sheafFiber.map
          ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
        etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F) := by
  rcases s with ⟨s, rfl⟩
  exact etalePullbackGlobalSectionsMap_germ q s Λ F

private def fibrePullbackIso {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] (t : Spec (CommRingCat.of Ω) ⟶ X)
    (Λ : Type u) [CommRing Λ] :
    etalePullback q Λ ⋙ etalePullback (pullback.snd t q) Λ ≅
      etalePullback t Λ ⋙ etalePullback (pullback.fst t q) Λ :=
  (etalePullbackCompIso (pullback.snd t q) q Λ).symm ≪≫
    pullback_eq_iso Λ (pullback.condition (f := t) (g := q)).symm ≪≫
      etalePullbackCompIso (pullback.fst t q) t Λ

private theorem fibrePullbackIso_stalk_unit_comp
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (r : Spec (CommRingCat.of Ω) ⟶ pullback t q)
    (hr₁ : r ≫ pullback.fst t q = 𝟙 _) (hr₂ : r ≫ pullback.snd t q = s.val)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) ≫
      ((Scheme.pointSmallEtale s.val).sheafFiber.map
          ((etalePullbackPushforwardAdjunction (pullback.snd t q) Λ).unit.app
            ((etalePullback q Λ).obj F)) ≫
        etalePushforwardStalkComponent (pullback.snd t q) s.val ⟨r, hr₂⟩
          ((etalePullback (pullback.snd t q) Λ).obj ((etalePullback q Λ).obj F))) ≫
      (Scheme.pointSmallEtale r).sheafFiber.map ((fibrePullbackIso q t Λ).hom.app F) =
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction t Λ).unit.app F) ≫
      etalePushforwardStalkComponent t t ⟨𝟙 _, Category.id_comp _⟩
        ((etalePullback t Λ).obj F)) ≫
      ((Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of Ω)))).sheafFiber.map
          ((etalePullbackPushforwardAdjunction (pullback.fst t q) Λ).unit.app
            ((etalePullback t Λ).obj F)) ≫
        etalePushforwardStalkComponent (pullback.fst t q) (𝟙 _) ⟨r, hr₁⟩
          ((etalePullback (pullback.fst t q) Λ).obj ((etalePullback t Λ).obj F))) := by
  let a := pullback.snd t q
  let π := pullback.fst t q
  let h : a ≫ q = π ≫ t := pullback.condition.symm
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} Λ)
  let R := (Scheme.pointSmallEtale r).sheafFiber (A := ModuleCat.{u} Λ)
  let c₁ := T.map ((etalePullbackPushforwardAdjunction (a ≫ q) Λ).unit.app F) ≫
    etalePushforwardStalkComponent (a ≫ q) t
      ⟨r, by rw [← Category.assoc, hr₂]; exact s.property⟩
      ((etalePullback (a ≫ q) Λ).obj F)
  let c₂ := T.map ((etalePullbackPushforwardAdjunction (π ≫ t) Λ).unit.app F) ≫
    etalePushforwardStalkComponent (π ≫ t) t
      ⟨r, by rw [← Category.assoc, hr₁, Category.id_comp]⟩
      ((etalePullback (π ≫ t) Λ).obj F)
  let e₁ := R.map ((etalePullbackCompIso a q Λ).hom.app F)
  let d₁ := R.map ((etalePullbackCompIso a q Λ).inv.app F)
  let e := R.map ((pullback_eq_iso Λ h).hom.app F)
  let e₂ := R.map ((etalePullbackCompIso π t Λ).hom.app F)
  have hc₁ := etalePullbackUnit_stalkComponent_comp a q t s ⟨r, hr₂⟩ Λ F
  have hc₂ := etalePullbackUnit_stalkComponent_comp π t t
    ⟨𝟙 _, Category.id_comp t⟩ ⟨r, hr₁⟩ Λ F
  have he : c₁ ≫ e = c₂ := stalkUnit_eqToIso Λ h t
    ⟨r, by rw [← Category.assoc, hr₂]; exact s.property⟩ F
  have hinv : e₁ ≫ d₁ = 𝟙 _ := by
    rw [← R.map_comp, (etalePullbackCompIso a q Λ).hom_inv_id_app, R.map_id]
  have hchain : R.map ((fibrePullbackIso q t Λ).hom.app F) = d₁ ≫ e ≫ e₂ := by
    change R.map (_ ≫ _ ≫ _) = _
    rw [R.map_comp, R.map_comp]
    rfl
  rw [← Category.assoc, ← hc₁, hchain]
  rw [Category.assoc, ← Category.assoc e₁, hinv, Category.id_comp, ← Category.assoc, he]
  exact hc₂

/-- A section over a geometrically connected fibre has one original stalk
value at every geometric lift over the same separably closed field. -/
theorem exists_common_stalk_lift_of_geometricallyConnected
    {X Y : Scheme.{u}} (q : Y ⟶ X) [GeometricallyConnected q]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (α : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    ∃ b : ToType ((Scheme.pointSmallEtale t).sheafFiber.obj F),
      ∀ s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t},
        ((Scheme.pointSmallEtale t).sheafFiber.map
            ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
          etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) b =
        etaleGlobalSectionsGerm s.val Λ ((etalePullback q Λ).obj F) α := by
  let Z := pullback t q
  let a : Z ⟶ Y := pullback.snd t q
  let π : Z ⟶ Spec (CommRingCat.of Ω) := pullback.fst t q
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace
    t a π (IsPullback.of_hasPullback t q).flip
  let Fq := (etalePullback q Λ).obj F
  let Ft := (etalePullback t Λ).obj F
  let Fa := (etalePullback a Λ).obj Fq
  let Fπ := (etalePullback π Λ).obj Ft
  let c : Fa ≅ Fπ := (fibrePullbackIso q t Λ).app F
  let αa := etalePullbackGlobalSectionsMap a Λ Fq α
  let απ := c.hom.hom.app (op (Scheme.Etale.mk (𝟙 Z))) αa
  let P := etalePullbackGlobalSectionsMap π Λ Ft
  have : IsIso P := etalePullbackGlobalSectionsMap_isIso_of_isSepClosed_base Ω π Λ Ft
  let β := inv P απ
  have hβ : P β = απ := ConcreteCategory.congr_hom (IsIso.inv_hom_id P) απ
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} Λ)
  let I := (Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of Ω)))).sheafFiber
    (A := ModuleCat.{u} Λ)
  let e : T.obj F ⟶ I.obj Ft := T.map ((etalePullbackPushforwardAdjunction t Λ).unit.app F) ≫
    etalePushforwardStalkComponent t t ⟨𝟙 _, Category.id_comp t⟩ Ft
  have : IsIso e := unit_stalkComponent_isIso_of_lift t t ⟨𝟙 _, Category.id_comp t⟩ Λ F
  let b : ToType (T.obj F) := inv e (etaleGlobalSectionsGerm (𝟙 _) Λ Ft β)
  have hb : e b = etaleGlobalSectionsGerm (𝟙 _) Λ Ft β :=
    ConcreteCategory.congr_hom (IsIso.inv_hom_id e) _
  refine ⟨b, ?_⟩
  intro s
  let r : Spec (CommRingCat.of Ω) ⟶ Z :=
    pullback.lift (𝟙 _) s.val ((Category.id_comp t).trans s.property.symm)
  have hr₁ : r ≫ π = 𝟙 _ := pullback.lift_fst _ _ _
  have hr₂ : r ≫ a = s.val := pullback.lift_snd _ _ _
  let S := (Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} Λ)
  let R := (Scheme.pointSmallEtale r).sheafFiber (A := ModuleCat.{u} Λ)
  let eqs : T.obj F ⟶ S.obj Fq := T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
    etalePushforwardStalkComponent q t s Fq
  let da : S.obj Fq ⟶ R.obj Fa := S.map ((etalePullbackPushforwardAdjunction a Λ).unit.app Fq) ≫
    etalePushforwardStalkComponent a s.val ⟨r, hr₂⟩ Fa
  let dπ : I.obj Ft ⟶ R.obj Fπ := I.map ((etalePullbackPushforwardAdjunction π Λ).unit.app Ft) ≫
    etalePushforwardStalkComponent π (𝟙 _) ⟨r, hr₁⟩ Fπ
  have : IsIso da := unit_stalkComponent_isIso_of_lift a s.val ⟨r, hr₂⟩ Λ Fq
  have hcomp : eqs ≫ da ≫ R.map c.hom = e ≫ dπ :=
    fibrePullbackIso_stalk_unit_comp q t s r hr₁ hr₂ Λ F
  have hga : etaleGlobalSectionsGerm r Λ Fa αa = da (etaleGlobalSectionsGerm s.val Λ Fq α) :=
    ConcreteCategory.congr_hom (globalSectionsMap_germ_of_lift a s.val ⟨r, hr₂⟩ Λ Fq) α
  have hgπ : etaleGlobalSectionsGerm r Λ Fπ (P β) =
      dπ (etaleGlobalSectionsGerm (𝟙 _) Λ Ft β) :=
    ConcreteCategory.congr_hom (globalSectionsMap_germ_of_lift π (𝟙 _) ⟨r, hr₁⟩ Λ Ft) β
  have hn : R.map c.hom (etaleGlobalSectionsGerm r Λ Fa αa) =
      etaleGlobalSectionsGerm r Λ Fπ απ :=
    (Scheme.pointSmallEtale r).toPresheafFiber_naturality_apply c.hom.hom
      (Scheme.Etale.mk (𝟙 Z)) (Over.homMk r (Category.comp_id r)) αa
  change eqs b = _
  apply (ModuleCat.mono_iff_injective (da ≫ R.map c.hom)).mp inferInstance
  exact (ConcreteCategory.congr_hom hcomp b).trans
    ((congrArg dπ hb).trans
      (hgπ.symm.trans ((congrArg (etaleGlobalSectionsGerm r Λ Fπ) hβ).trans
        (hn.symm.trans (congrArg (R.map c.hom) hga)))))

private theorem globalSections_eq_of_geometric_germs_eq
    {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (a b : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hab : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ X),
      etaleGlobalSectionsGerm t Λ F a = etaleGlobalSectionsGerm t Λ F b) : a = b := by
  classical
  let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hlocal (x : X) : ∃ (V : X.Etale) (g : V ⟶ X₀) (v : V.left),
      F.obj.map g.op a = F.obj.map g.op b ∧ g.left v = x := by
    let Ω := SeparableClosure (X.residueField x)
    let t : Spec (CommRingCat.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫
        X.fromSpecResidueField x
    have ht : t default = x := by
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply x _
    let u : (Scheme.pointSmallEtale t).fiber.obj X₀ :=
      Over.homMk t (Category.comp_id t)
    obtain ⟨V, g, y, _, hy⟩ :=
      ((Scheme.pointSmallEtale t).toPresheafFiber_eq_iff' (P := F.obj) X₀ u a b).mp
        (hab Ω t)
    change Over.mk t ⟶ Over.mk V.hom at y
    have hg : g.left = V.hom := (Category.comp_id g.left).symm.trans g.w
    refine ⟨V, g, y.left (default : Spec (CommRingCat.of Ω)), hy, ?_⟩
    rw [hg]
    exact (Scheme.Hom.comp_apply y.left V.hom (default : Spec (CommRingCat.of Ω))).symm.trans
      ((congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ X => f default) y.w).trans ht)
  choose V g v hg hv using hlocal
  have hcover : Sieve.ofArrows V g ∈ X.smallEtaleTopology X₀ := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, v x, hv x⟩
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  apply F.isSeparated X₀ (Sieve.ofArrows V g) hcover
  intro U f hf
  obtain ⟨x, k, rfl⟩ := (Sieve.mem_ofArrows_iff V g f).mp hf
  rw [op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply, hg x]

/-- Over a geometrically connected morphism, every section of actual
inverse image satisfies the original Čech equation. -/
theorem etaleCechSections_eq_of_geometricallyConnected
    {X Y : Scheme.{u}} (q : Y ⟶ X) [GeometricallyConnected q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (α : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    etaleCechFirstSectionsMap q Λ F α = etaleCechSecondSectionsMap q Λ F α := by
  let Z := pullback q q
  let p₁ : Z ⟶ Y := pullback.fst q q
  let p₂ : Z ⟶ Y := pullback.snd q q
  let Fq := (etalePullback q Λ).obj F
  let F₁ := (etalePullback p₁ Λ).obj Fq
  let F₂ := (etalePullback p₂ Λ).obj Fq
  apply globalSections_eq_of_geometric_germs_eq Λ F₂
  intro Ω _ _ w
  let t := (w ≫ p₁) ≫ q
  let s₁ : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} := ⟨w ≫ p₁, rfl⟩
  let s₂ : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} := ⟨w ≫ p₂, by
    dsimp [t, p₁, p₂]
    rw [Category.assoc, Category.assoc, pullback.condition]⟩
  obtain ⟨b, hb⟩ := exists_common_stalk_lift_of_geometricallyConnected q t Λ F α
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} Λ)
  let S₁ := (Scheme.pointSmallEtale s₁.val).sheafFiber (A := ModuleCat.{u} Λ)
  let S₂ := (Scheme.pointSmallEtale s₂.val).sheafFiber (A := ModuleCat.{u} Λ)
  let Ψ := (Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u} Λ)
  let e₁ : T.obj F ⟶ S₁.obj Fq :=
    T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₁ Fq
  let e₂ : T.obj F ⟶ S₂.obj Fq :=
    T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₂ Fq
  let d₁ : S₁.obj Fq ⟶ Ψ.obj F₁ :=
    S₁.map ((etalePullbackPushforwardAdjunction p₁ Λ).unit.app Fq) ≫
      etalePushforwardStalkComponent p₁ s₁.val ⟨w, rfl⟩ F₁
  let d₂ : S₂.obj Fq ⟶ Ψ.obj F₂ :=
    S₂.map ((etalePullbackPushforwardAdjunction p₂ Λ).unit.app Fq) ≫
      etalePushforwardStalkComponent p₂ s₂.val ⟨w, rfl⟩ F₂
  let c : F₁ ⟶ F₂ := (etaleCechPullbackIso q Λ).hom.app F
  have hcomp : e₁ ≫ d₁ ≫ Ψ.map c = e₂ ≫ d₂ :=
    etaleCechPullbackIso_stalk_unit_comp q Λ t s₁ s₂ w rfl rfl F
  have hg₁ : etalePullbackGlobalSectionsMap p₁ Λ Fq ≫ etaleGlobalSectionsGerm w Λ F₁ =
      etaleGlobalSectionsGerm s₁.val Λ Fq ≫ d₁ :=
    globalSectionsMap_germ_of_lift p₁ s₁.val ⟨w, rfl⟩ Λ Fq
  have hg₂ : etalePullbackGlobalSectionsMap p₂ Λ Fq ≫ etaleGlobalSectionsGerm w Λ F₂ =
      etaleGlobalSectionsGerm s₂.val Λ Fq ≫ d₂ :=
    globalSectionsMap_germ_of_lift p₂ s₂.val ⟨w, rfl⟩ Λ Fq
  have hn : c.hom.app (op (Scheme.Etale.mk (𝟙 Z))) ≫ etaleGlobalSectionsGerm w Λ F₂ =
      etaleGlobalSectionsGerm w Λ F₁ ≫ Ψ.map c :=
    ((Scheme.pointSmallEtale w).toPresheafFiber_naturality c.hom
      (Scheme.Etale.mk (𝟙 Z)) (Over.homMk w (Category.comp_id w))).symm
  have hfirst : etaleCechFirstSectionsMap q Λ F ≫ etaleGlobalSectionsGerm w Λ F₂ =
      (etaleGlobalSectionsGerm s₁.val Λ Fq ≫ d₁) ≫ Ψ.map c := by
    change (etalePullbackGlobalSectionsMap p₁ Λ Fq ≫ c.hom.app _) ≫ _ = _
    rw [Category.assoc, hn, ← Category.assoc, hg₁]
  have hg : Ψ.map c (d₁ (etaleGlobalSectionsGerm s₁.val Λ Fq α)) =
      d₂ (etaleGlobalSectionsGerm s₂.val Λ Fq α) :=
    (congrArg (fun v => Ψ.map c (d₁ v)) (hb s₁)).symm.trans
      ((ConcreteCategory.congr_hom hcomp b).trans (congrArg d₂ (hb s₂)))
  exact (ConcreteCategory.congr_hom hfirst α).trans
    (hg.trans (ConcreteCategory.congr_hom hg₂ α).symm)

end EtaleCohomology
