/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.Basic
public import Nyll.EtaleFundamentalGroups.GaloisCategories.AutFunctorComparison
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
public import Nyll.SchemeTheory.Pi1.Affine.Over
public import Mathlib.Algebra.Group.PUnit

/-!
# Full outer isomorphisms induced by scheme isomorphisms

The trivial arithmetic quotient specializes the existing outer-isomorphism
construction to conjugation by the entire target group. A connected-scheme
isomorphism then gives a canonical full outer isomorphism of its geometric-point
fundamental groups. The construction uses the actual pullback of finite étale
covers; changing the comparison of fiber functors leaves its outer class unchanged.
Composition and inversion agree with those of scheme isomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w

attribute [local instance]
  finiteEtaleStableUnderBaseChangeAlongFunctoriality
  finiteEtaleHasPullbacksAlongFunctoriality

/-- Continuous group isomorphisms modulo inner automorphisms of the full target group. -/
abbrev FullOuterEquiv (G : Type u) (H : Type v)
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] : Type (max u v) :=
  OuterEquiv (1 : G →* PUnit.{1}) (1 : H →* PUnit.{1})

namespace FullOuterEquiv

section Groups

variable {G : Type u} {H : Type v} {K : Type w}
  [Group G] [Group H] [Group K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

/-- The full outer class of an actual continuous group isomorphism. -/
def mk (e : G ≃ₜ* H) : FullOuterEquiv G H :=
  OuterEquiv.mk ⟨e, fun _ => Subsingleton.elim _ _⟩

/-- Every full outer class has an actual continuous group-isomorphism representative. -/
theorem mk_surjective : Function.Surjective (mk (G := G) (H := H)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro e
  exact ⟨e.1, rfl⟩

/-- Full outer classes agree exactly when their representatives differ by conjugation. -/
theorem mk_eq_mk_iff (e f : G ≃ₜ* H) :
    mk e = mk f ↔ ∃ c : H, ∀ g : G, f g = c * e g * c⁻¹ := by
  let e₀ : OverQuotientEquiv (1 : G →* PUnit.{1}) (1 : H →* PUnit.{1}) :=
    ⟨e, fun _ => Subsingleton.elim _ _⟩
  let f₀ : OverQuotientEquiv (1 : G →* PUnit.{1}) (1 : H →* PUnit.{1}) :=
    ⟨f, fun _ => Subsingleton.elim _ _⟩
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ := (OuterEquiv.mk_eq_mk_iff e₀ f₀).mp h
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact (OuterEquiv.mk_eq_mk_iff e₀ f₀).mpr ⟨c, Subsingleton.elim _ _, hc⟩

/-- The existing outer composition is represented by composition of continuous maps. -/
@[simp]
theorem mk_trans (e : G ≃ₜ* H) (f : H ≃ₜ* K) :
    mk (e.trans f) = OuterEquiv.trans (mk e) (mk f) :=
  rfl

end Groups

section Schemes

variable {X Y Z : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω]

/-- The actual group isomorphism induced by a scheme isomorphism and a specified
comparison between its pullback fiber functor and the target fiber functor. -/
def schemeIsoGroupEquiv (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (I : X ≅ Y) (t : pullback I.hom ⋙ fiber x ≅ fiber y) :
    π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y) := by
  let E : FiniteEtale Y ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ I.symm
  have : (pullback I.hom).IsEquivalence := E.isEquivalence_functor
  exact (fundamentalGroupEquivOfPullbackEquivalence I.hom x).trans
    (continuousConjAut ((pullbackFiberIso I.hom x).symm ≪≫ t))

/-- Its forward map is the map of automorphism groups of the actual pullback functor. -/
theorem schemeIsoGroupEquiv_apply (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (I : X ≅ Y) (t : pullback I.hom ⋙ fiber x ≅ fiber y) (a : π₁ᵉᵗ(x)) :
    schemeIsoGroupEquiv x y I t a = autHomOfCompIso (pullback I.hom) t a := by
  let b : Aut (pullback I.hom ⋙ fiber x) :=
    ((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback I.hom)).mapAut (fiber x) a
  change ((pullbackFiberIso I.hom x).symm ≪≫ t).conjAut
    ((pullbackFiberIso I.hom x).conjAut b) = t.conjAut b
  rw [← Iso.trans_conjAut, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

/-- Changing the specified fiber comparison does not change the full outer class. -/
theorem mk_schemeIsoGroupEquiv_eq (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (I : X ≅ Y) (t t' : pullback I.hom ⋙ fiber x ≅ fiber y) :
    mk (schemeIsoGroupEquiv x y I t) = mk (schemeIsoGroupEquiv x y I t') := by
  apply (mk_eq_mk_iff _ _).2
  refine ⟨Aut.of (t.symm ≪≫ t'), fun a => ?_⟩
  rw [schemeIsoGroupEquiv_apply, schemeIsoGroupEquiv_apply]
  exact autHomOfCompIso_eq_conj (pullback I.hom) t t' a

variable [IsSepClosed Ω']

/-- The canonical full outer fundamental-group isomorphism of a scheme isomorphism. -/
def ofSchemeIso (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y) (I : X ≅ Y) :
    FullOuterEquiv π₁ᵉᵗ(x) π₁ᵉᵗ(y) :=
  mk (schemeIsoGroupEquiv x y I
    (pullbackFiberIso I.hom x ≪≫ (nonempty_fiber_iso (x ≫ I.hom) y).some))

/-- Any comparison of the actual pullback fiber functor computes the canonical class. -/
theorem ofSchemeIso_eq_mk (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (I : X ≅ Y) (t : pullback I.hom ⋙ fiber x ≅ fiber y) :
    ofSchemeIso x y I = mk (schemeIsoGroupEquiv x y I t) :=
  mk_schemeIsoGroupEquiv_eq x y I _ t

/-- Realizing the original group map up to full conjugation is exactly equality
with the canonical outer class of the scheme isomorphism. -/
theorem ofSchemeIso_eq_mk_iff (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (I : X ≅ Y) (t : pullback I.hom ⋙ fiber x ≅ fiber y) (e : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y)) :
    ofSchemeIso x y I = mk e ↔
      ∃ c : π₁ᵉᵗ(y), ∀ a : π₁ᵉᵗ(x),
        autHomOfCompIso (pullback I.hom) t a = c * e a * c⁻¹ := by
  rw [ofSchemeIso_eq_mk x y I t]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (mk_eq_mk_iff e (schemeIsoGroupEquiv x y I t)).mp h.symm
    exact ⟨c, fun a => (schemeIsoGroupEquiv_apply x y I t a).symm.trans (hc a)⟩
  · rintro ⟨c, hc⟩
    apply Eq.symm
    apply (mk_eq_mk_iff e (schemeIsoGroupEquiv x y I t)).2
    exact ⟨c, fun a => (schemeIsoGroupEquiv_apply x y I t a).trans (hc a)⟩

/-- Composition of scheme isomorphisms gives composition of their full outer classes. -/
theorem ofSchemeIso_trans [ConnectedSpace Z]
    {Ω'' : Type u} [Field Ω''] [IsSepClosed Ω'']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y) (z : Spec (.of Ω'') ⟶ Z)
    (I : X ≅ Y) (J : Y ≅ Z) :
    ofSchemeIso x z (I ≪≫ J) =
      OuterEquiv.trans (ofSchemeIso x y I) (ofSchemeIso y z J) := by
  let tI : pullback I.hom ⋙ fiber x ≅ fiber y :=
    pullbackFiberIso I.hom x ≪≫ (nonempty_fiber_iso (x ≫ I.hom) y).some
  let tJ : pullback J.hom ⋙ fiber y ≅ fiber z :=
    pullbackFiberIso J.hom y ≪≫ (nonempty_fiber_iso (y ≫ J.hom) z).some
  let pc : pullback (I.hom ≫ J.hom) ≅ pullback J.hom ⋙ pullback I.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) I.hom J.hom
  let t : (pullback J.hom ⋙ pullback I.hom) ⋙ fiber x ≅ fiber z :=
    Functor.associator (pullback J.hom) (pullback I.hom) (fiber x) ≪≫
      Functor.isoWhiskerLeft (pullback J.hom) tI ≪≫ tJ
  rw [ofSchemeIso_eq_mk x y I tI, ofSchemeIso_eq_mk y z J tJ, ← mk_trans]
  apply (ofSchemeIso_eq_mk_iff x z (I ≪≫ J)
    (Functor.isoWhiskerRight pc (fiber x) ≪≫ t) _).2
  refine ⟨1, fun a => ?_⟩
  simp only [one_mul, inv_one, mul_one, ContinuousMulEquiv.trans_apply]
  rw [schemeIsoGroupEquiv_apply, schemeIsoGroupEquiv_apply]
  exact (autHomOfCompIso_isoFunctor pc t a).trans
    (autHomOfCompIso_comp (pullback J.hom) (pullback I.hom) tI tJ a)

omit [ConnectedSpace Y] [Field Ω'] [IsSepClosed Ω'] in
/-- The identity scheme isomorphism induces the identity full outer class. -/
@[simp]
theorem ofSchemeIso_refl (x : Spec (.of Ω) ⟶ X) :
    ofSchemeIso x x (Iso.refl X) = OuterEquiv.refl (1 : π₁ᵉᵗ(x) →* PUnit.{1}) := by
  let pc : pullback (𝟙 X) ≅ 𝟭 (FiniteEtale X) :=
    MorphismProperty.Over.pullbackId
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X
  let t : pullback (𝟙 X) ⋙ fiber x ≅ fiber x :=
    Functor.isoWhiskerRight pc (fiber x) ≪≫ Functor.leftUnitor (fiber x)
  change ofSchemeIso x x (Iso.refl X) = mk (ContinuousMulEquiv.refl π₁ᵉᵗ(x))
  apply (ofSchemeIso_eq_mk_iff x x (Iso.refl X) t _).2
  refine ⟨1, fun a => ?_⟩
  simp only [one_mul, inv_one, mul_one, ContinuousMulEquiv.refl_apply]
  refine (autHomOfCompIso_isoFunctor pc (Functor.leftUnitor (fiber x)) a).trans ?_
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext A
  rfl

/-- Inverting a scheme isomorphism inverts its canonical full outer class. -/
@[simp]
theorem ofSchemeIso_symm (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y)
    (I : X ≅ Y) :
    ofSchemeIso y x I.symm = OuterEquiv.symm (ofSchemeIso x y I) := by
  have h := ofSchemeIso_trans x y x I I.symm
  rw [Iso.self_symm_id, ofSchemeIso_refl] at h
  have hc := congrArg (fun q => OuterEquiv.trans (OuterEquiv.symm (ofSchemeIso x y I)) q) h
  simpa only [OuterEquiv.trans_refl, ← OuterEquiv.trans_assoc,
    OuterEquiv.symm_trans_self, OuterEquiv.refl_trans] using hc.symm

end Schemes

end FullOuterEquiv

/-- Full inner classes admitting a representative over the specified arithmetic
quotient maps. The relation is still conjugation by the entire target group. -/
abbrev MarkedFullOuterEquiv {G : Type u} {H : Type v} {Γ : Type w}
    [Group G] [Group H] [Group Γ] [TopologicalSpace G] [TopologicalSpace H]
    (p : G →* Γ) (q : H →* Γ) : Type (max u v) :=
  {o : FullOuterEquiv G H // ∃ e : OverQuotientEquiv p q, FullOuterEquiv.mk e.1 = o}

end AnabelianGeometry.ArithmeticIsomorphisms
