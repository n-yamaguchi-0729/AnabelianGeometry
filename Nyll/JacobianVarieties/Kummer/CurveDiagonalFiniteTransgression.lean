/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianCechResidualDescent
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.AdicCupH1Anticommutativity
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupCechKernelProduct
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalarApproximation

/-!
# Finite transgressions for the normalized diagonal
-/

public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Abelian
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

/-- A section killing both classes eliminates their signed residual pullback. -/
private theorem eq_of_signed_residual_pullback
    {R : Type*} {A : Type*} {B : Type*}
    [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (r : R) (a b x y : A) (z : B)
    (hfg : f (g z) = z) (ha : f a = 0) (hb : f b = 0)
    (hx : x = -(r • a)) (hy : y = -b) (h : x - y = g z) : r • a = b := by
  have hz : z = 0 := by
    have hf := congrArg f h
    rw [map_sub, hx, hy, map_neg, map_smul, ha, smul_zero, neg_zero,
      map_neg, hb, neg_zero, sub_self, hfg] at hf
    exact hf.symm
  rw [hx, hy, hz, map_zero] at h
  exact neg_injective (sub_eq_zero.mp h)

/-- Finite cohomology pullback retains an actual section identity. -/
private theorem finiteLevelPullback_section_apply
    {X Y : Scheme.{u}} (s : X ⟶ Y) (q : Y ⟶ X) (hsq : s ≫ q = 𝟙 X)
    (ℓ : ℕ) [Fact ℓ.Prime] (n i : ℕ) (a : finiteLevelCohomology X ℓ n i) :
    finiteLevelCohomologyPullback ℓ s n i
      (finiteLevelCohomologyPullback ℓ q n i a) = a := by
  have hcomp := finiteLevelCohomologyPullback_comp s q ℓ n i
  have hsec := congrArg (fun f : X ⟶ X => finiteLevelCohomologyPullback ℓ f n i) hsq
  have hid := finiteLevelCohomologyPullback_id ℓ X n i
  exact (LinearMap.congr_fun (hcomp.symm.trans (hsec.trans hid)) a).trans
    (Module.End.one_apply (R := ℤ_[ℓ]) a)

private theorem ext_transgression_cancel_coefficients
    {A : Type*} [Category A] [Abelian A] [HasExt.{u} A]
    {U V W W' : A} (d : Ext.{u} U V 1) (a : Ext.{u} V W 1) (e : W' ≅ W) :
    ((d.comp (a.comp (Ext.mk₀ e.inv) (add_zero 1)) (show 1 + 1 = 2 from rfl)).comp
      (Ext.mk₀ e.hom) (add_zero 2)) = d.comp a (show 1 + 1 = 2 from rfl) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]

/-- The signed root transgression through the finite Kummer coefficient isomorphism. -/
theorem signedRootFinite_transgression
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    {T V : X.Etale} (hT : IsTerminal T) (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (D E : Scheme.EffectiveCartierDivisor X)
    (a : Ext.{u} (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f))
      (etaleRootsOfUnitySheaf X (ℓ ^ (n + 1))) 1)
    (ha : (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        a (show 1 + 1 = 2 from rfl) +
      (effectiveCartierCycleClass D (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base c
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))) -
        effectiveCartierCycleClass E (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base c
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) = 0) :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (a.comp (Ext.mk₀ (ellPowerConstantKummerKernelIso c ℓ hℓ n).inv) (add_zero 1))
          (show 1 + 1 = 2 from rfl) =
      -(finiteEffectiveCartierCycleClass c ℓ hℓ n D -
        finiteEffectiveCartierCycleClass c ℓ hℓ n E) := by
  let e := ellPowerConstantKummerKernelIso c ℓ hℓ n
  apply (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).injective
  rw [map_neg, map_sub, finiteEffectiveCartierCycleClass_kummer,
    finiteEffectiveCartierCycleClass_kummer]
  change ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
    (a.comp (Ext.mk₀ e.inv) (add_zero 1)) rfl).comp (Ext.mk₀ e.hom) (add_zero 2) = _
  have hcancel := ext_transgression_cancel_coefficients
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass a e
  exact hcancel.trans (eq_neg_of_add_eq_zero_left ha)

private theorem cup_sum_swap_of_pointwise_eq {I A B C : Type*} [AddCommGroup C]
    (S : Finset I) (x : I → B) (a b : I → A) (pullback : A → B) (cup : B → B → C)
    (h : ∀ j, a j = b j) (hswap : ∀ x y, cup x y = -cup y x) :
    (∑ j ∈ S, cup (pullback (a j)) (x j)) =
      -(∑ j ∈ S, cup (x j) (pullback (b j))) := by
  calc
    _ = ∑ j ∈ S, -(cup (x j) (pullback (b j))) :=
      Finset.sum_congr rfl fun j _ =>
        (congrArg (fun z => cup (pullback z) (x j)) (h j)).trans
          (hswap (pullback (b j)) (x j))
    _ = _ := Finset.sum_neg_distrib _

/-- The finite cup kernels transgress to the negative external cup sum. -/
theorem finiteExternalCupKernelSum_transgression
    {C Y : Scheme.{u}} (p : Y ⟶ C) (ℓ n : ℕ) [Fact ℓ.Prime]
    {T V : C.Etale} (hT : IsTerminal T) (q : V ⟶ T)
    (hq : Sieve.generate (Presieve.singleton q) ∈ C.smallEtaleTopology T)
    {I : Type u} (S : Finset I)
    (x : I → finiteLevelCohomology Y ℓ n 1) (y : I → finiteLevelCohomology C ℓ n 1)
    (d : finiteLevelCohomology C ℓ n 1 →
      (kernel (abelianCechUnitAugmentation C.smallEtaleTopology hT q) ⟶
        (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)))
    (hd : ∀ z : finiteLevelCohomology C ℓ n 1,
      (abelianCechAugmentationSequence_shortExact C.smallEtaleTopology hT q hq).extClass.comp
        (Ext.mk₀ (d z)) (add_zero 1) = z) :
    let BC := etaleBaseChange p
    let hTB := hT.isTerminalObj BC T
    let qB := BC.map q
    (abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hTB qB
      (etaleBaseChange_singleton_covering p q hq)).extClass.comp
      (∑ j ∈ S, finiteCechKernelCupClass Y ℓ n hTB qB
        (finiteCechKernelPullback p ℓ n hT q hq (d (y j))) (x j))
      (show 1 + 1 = 2 from rfl) =
      -(∑ j ∈ S, finiteLevelCup Y ℓ n 1 1 2 rfl (x j)
        (finiteLevelCohomologyPullback ℓ p n 1 (y j))) := by
  intro BC hTB qB
  let δ (j : I) : finiteLevelCohomology C ℓ n 1 :=
    (abelianCechAugmentationSequence_shortExact C.smallEtaleTopology hT q hq).extClass.comp
      (Ext.mk₀ (d (y j))) (add_zero 1)
  have htrans := finiteCechKernelCupSum_transgression p ℓ n hT q hq S (fun j => d (y j)) x
  have hswap := cup_sum_swap_of_pointwise_eq S x δ y
    (finiteLevelCohomologyPullback ℓ p n 1)
    (fun a b => finiteLevelCup Y ℓ n 1 1 2 rfl a b)
    (fun j => hd (y j)) (finiteLevelCup_anticomm_one Y ℓ n)
  exact htrans.trans hswap

/-- The difference of two transgressions descends if their edge restrictions agree. -/
private theorem finiteTensor_residual_descent
    {C Y : Scheme.{u}} (p : Y ⟶ C) [Flat p] [QuasiCompact p] [GeometricallyConnected p]
    (ℓ n : ℕ) [Fact ℓ.Prime]
    {T V : C.Etale} (hT : IsTerminal T) (q : V ⟶ T)
    (hq : Sieve.generate (Presieve.singleton q) ∈ C.smallEtaleTopology T) :
    let BC := etaleBaseChange p
    let hTB := hT.isTerminalObj BC T
    let qB := BC.map q
    let hqB := etaleBaseChange_singleton_covering p q hq
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hTB qB
    let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hTB qB hqB
    let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)
    let tr := hA.extClass.precomp F (show 1 + 1 = 2 from rfl)
    ∀ (a b : Ext.{u} A.X₁ F 1),
      (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).comp a (zero_add 1) =
        (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).comp b (zero_add 1) →
      ∃ β : finiteLevelCohomology C ℓ n 2,
        tr a - tr b = finiteLevelCohomologyPullback ℓ p n 2 β := by
  intro BC hTB qB hqB A hA F tr a b hedge
  obtain ⟨w, -, hres⟩ := abelianCechKernelClass_exists_residual Y hTB qB hqB F a b hedge
  obtain ⟨v, -, hdescent⟩ := abelianCechConstantTwoStepClass_exists_descent p hT q hq
    (ellPowerCoefficients ℓ n) w
  let β : finiteLevelCohomology C ℓ n 2 :=
    ((abelianCechAugmentationSequence_shortExact C.smallEtaleTopology hT q hq).extClass.comp
      (abelianCechFirstRelationSequence_shortExact C.smallEtaleTopology hT q).extClass rfl).comp
        (Ext.mk₀ v) (add_zero 2)
  exact ⟨β, hres.trans hdescent⟩

/-- Equal edge restrictions identify the transgressed classes when both vanish on a section. -/
theorem finiteTensor_eq_of_first_relation
    {C Y : Scheme.{u}} (p : Y ⟶ C) [Flat p] [QuasiCompact p] [GeometricallyConnected p]
    (σ : C ⟶ Y) (hσ : σ ≫ p = 𝟙 C) (ℓ n : ℕ) [Fact ℓ.Prime]
    {T V : C.Etale} (hT : IsTerminal T) (q : V ⟶ T)
    (hq : Sieve.generate (Presieve.singleton q) ∈ C.smallEtaleTopology T) :
    let BC := etaleBaseChange p
    let hTB := hT.isTerminalObj BC T
    let qB := BC.map q
    let hqB := etaleBaseChange_singleton_covering p q hq
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hTB qB
    let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hTB qB hqB
    let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)
    let tr := hA.extClass.precomp F (show 1 + 1 = 2 from rfl)
    let edge := (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).precomp F
      (zero_add 1)
    ∀ (a b : Ext.{u} A.X₁ F 1) (α γ : finiteLevelCohomology Y ℓ n 2) (r : ℤ_[ℓ]),
      tr a = -α → tr b = -γ →
      edge (r.appr (n + 1) • a) = edge b →
      finiteLevelCohomologyPullback ℓ σ n 2 α = 0 →
      finiteLevelCohomologyPullback ℓ σ n 2 γ = 0 →
      r • α = γ := by
  intro BC hTB qB hqB A hA F tr edge a b α γ r ha hb hedge hα hγ
  let ar := r.appr (n + 1) • a
  have hscaled : tr ar = -(r • α) :=
    (map_nsmul tr (r.appr (n + 1)) a).trans
      ((congrArg (fun x : finiteLevelCohomology Y ℓ n 2 => r.appr (n + 1) • x) ha).trans
        ((finiteLevelCohomology_smul_eq_appr Y ℓ n 2 r (-α)).symm.trans (smul_neg r α)))
  obtain ⟨β, hresidual⟩ := finiteTensor_residual_descent p ℓ n hT q hq ar b hedge
  have hsection := finiteLevelPullback_section_apply σ p hσ ℓ n 2 β
  exact eq_of_signed_residual_pullback
    (finiteLevelCohomologyPullback ℓ σ n 2) (finiteLevelCohomologyPullback ℓ p n 2)
    r α γ (tr ar) (tr b) β hsection hα hγ hscaled hb hresidual

end AlgebraicCurve.CurveModel
