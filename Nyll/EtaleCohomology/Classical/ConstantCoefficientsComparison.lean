/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Frobenius.Cohomology
public import Nyll.EtaleCohomology.Sites.ConstantCoefficientComparison
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Constant module coefficients and constant abelian coefficients

Forgetting the coefficient action commutes with constant sheaves. The actual
inverse-image coefficient comparison respects the canonical constant-sheaf
comparisons. Consequently the native coefficient-linear pullback agrees,
under this comparison, with actual constant abelian pullback in every degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The underlying abelian sheaf of the constant module sheaf is the constant
abelian sheaf of the underlying coefficient group. -/
def etaleConstantModuleForgetIso :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙
        Classical.forgetCoefficients.{u + 1, u, u, u} ≅
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
        constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} := by
  let : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  exact constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- Forgetting the original constant module coefficients preserves
their literal sheafification generators on every étale object. -/
theorem etaleConstantModuleForgetIso_toSheafify (M : ModuleCat.{u} R) (V : X.Etale) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op V)) ≫
      ((etaleConstantModuleForgetIso X R).hom.app M).hom.app (op V) =
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M))).app (op V) := by
  let : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  exact Sites.constantCommuteCompose_toSheafify X.smallEtaleTopology
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) M V

/-- The native constant-module comparison carries the forgotten
constant-sheaf unit to the abelian constant-sheaf unit. -/
theorem etaleConstantModuleForgetIso_unit {T : X.Etale} (hT : IsTerminal T)
    (M : ModuleCat.{u} R) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app M) ≫
      ((etaleConstantModuleForgetIso X R).hom.app M).hom.app (op T) =
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) := by
  let : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  exact Sites.constantCommuteCompose_unit X.smallEtaleTopology
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) hT M

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual inverse-image coefficient comparison respects both canonical
constant-sheaf comparisons. -/
theorem etalePullbackForgetCoefficientsIso_constant (M : ModuleCat.{u} R) :
    (etalePullbackForgetCoefficientsIso f R).inv.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
      Classical.forgetCoefficients.{u + 1, u, u, u}.map
        ((etalePullbackConstantIso f R).hom.app M) ≫
      (etaleConstantModuleForgetIso X R).hom.app M =
    (etaleAbelianPullback f).map ((etaleConstantModuleForgetIso Y R).hom.app M) ≫
      (etaleAbelianPullbackConstantIso f).hom.app
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) := by
  let V := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let UX := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let UY := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := Y.smallEtaleTopology) (R := R)
  let KMX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let KMY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let KAX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (V.obj M)
  let KAY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (V.obj M)
  let δX : UX.obj KMX ≅ KAX := (etaleConstantModuleForgetIso X R).app M
  let δY : UY.obj KMY ≅ KAY := (etaleConstantModuleForgetIso Y R).app M
  let am := etalePullbackPushforwardAdjunction f R
  let aa := etaleAbelianPullbackPushforwardAdjunction f
  let εm : (etalePullback f R).obj KMY ⟶ KMX :=
    (etalePullbackConstantIso f R).hom.app M
  let εa : (etaleAbelianPullback f).obj KAY ⟶ KAX :=
    (etaleAbelianPullbackConstantIso f).hom.app (V.obj M)
  let vm : KMY ⟶ (etalePushforward f R).obj KMX := am.homEquiv KMY KMX εm
  let va : KAY ⟶ (etaleAbelianPushforward f).obj KAX := aa.homEquiv KAY KAX εa
  let φ : UY.obj KMY ⟶ (etaleAbelianPushforward f).obj KAX :=
    UY.map vm ≫ (etaleAbelianPushforward f).map δX.hom
  let T : Y.Etale := ⊤_ Y.Etale
  let hT : IsTerminal T := terminalIsTerminal
  let FT : X.Etale := (etaleBaseChange f).obj T
  let hFT : IsTerminal FT := hT.isTerminalObj (etaleBaseChange f) T
  let ηm : M ⟶ KMY.obj.obj (op T) :=
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app M
  let ηmf : M ⟶ KMX.obj.obj (op FT) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hFT).unit.app M
  let ηa : V.obj M ⟶ KAY.obj.obj (op T) :=
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app (V.obj M)
  let ηaf : V.obj M ⟶ KAX.obj.obj (op FT) :=
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hFT).unit.app (V.obj M)
  let dT : V.obj (KMY.obj.obj (op T)) ≅ KAY.obj.obj (op T) :=
    ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)).mapIso δY
  let dFT : V.obj (KMX.obj.obj (op FT)) ≅ KAX.obj.obj (op FT) :=
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op FT)).mapIso δX
  let vmT : KMY.obj.obj (op T) ⟶ KMX.obj.obj (op FT) := vm.hom.app (op T)
  let vaT : KAY.obj.obj (op T) ⟶ KAX.obj.obj (op FT) := va.hom.app (op T)
  have hdT : V.map ηm ≫ dT.hom = ηa := etaleConstantModuleForgetIso_unit Y R hT M
  have hdFT : V.map ηmf ≫ dFT.hom = ηaf :=
    etaleConstantModuleForgetIso_unit X R hFT M
  have hdTi : ηa ≫ dT.inv = V.map ηm := by
    rw [← hdT, Category.assoc, dT.hom_inv_id, Category.comp_id]
  have hm : ηm ≫ vmT = ηmf := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} R) hT).comp am)
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hFT) M
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit] at h
    exact h
  have ha : ηa ≫ vaT = ηaf := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT).comp aa)
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hFT) (V.obj M)
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit] at h
    exact h
  have hφi : δY.inv ≫ φ = va := by
    apply ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv
      (V.obj M) ((etaleAbelianPushforward f).obj KAX)).injective
    change ηa ≫ (dT.inv ≫ (V.map vmT ≫ dFT.hom)) = ηa ≫ vaT
    calc
      _ = (ηa ≫ dT.inv) ≫ V.map vmT ≫ dFT.hom := by
        rw [Category.assoc]
      _ = V.map ηm ≫ V.map vmT ≫ dFT.hom := by rw [hdTi]
      _ = V.map (ηm ≫ vmT) ≫ dFT.hom := by
        rw [Functor.map_comp, Category.assoc]
      _ = V.map ηmf ≫ dFT.hom := by rw [hm]
      _ = ηaf := hdFT
      _ = ηa ≫ vaT := ha.symm
  have hφ : φ = δY.hom ≫ va := by
    rw [← hφi, ← Category.assoc, δY.hom_inv_id, Category.id_comp]
  let ηmp : KMY ⟶ (etalePushforward f R).obj ((etalePullback f R).obj KMY) :=
    am.unit.app KMY
  let ηap : UY.obj KMY ⟶ (etaleAbelianPushforward f).obj
      ((etaleAbelianPullback f).obj (UY.obj KMY)) := aa.unit.app (UY.obj KMY)
  let νmp : UY.obj KMY ⟶ (etaleAbelianPushforward f).obj
      (UX.obj ((etalePullback f R).obj KMY)) := UY.map ηmp
  let e : UX.obj ((etalePullback f R).obj KMY) ≅
      (etaleAbelianPullback f).obj (UY.obj KMY) :=
    (etalePullbackForgetCoefficientsIso f R).app KMY
  have hu : νmp ≫ (etaleAbelianPushforward f).map e.hom = ηap :=
    etalePullbackForgetCoefficientsIso_unit f R KMY
  have hui : ηap ≫ (etaleAbelianPushforward f).map e.inv = νmp := by
    rw [← hu, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hl : aa.homEquiv (UY.obj KMY) KAX (e.inv ≫ UX.map εm ≫ δX.hom) = φ := by
    change ηap ≫ (etaleAbelianPushforward f).map (e.inv ≫ UX.map εm ≫ δX.hom) = φ
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hui, ← Category.assoc]
    rfl
  have hr : aa.homEquiv (UY.obj KMY) KAX
      ((etaleAbelianPullback f).map δY.hom ≫ εa) = δY.hom ≫ va := by
    rw [Adjunction.homEquiv_naturality_left]
  apply (aa.homEquiv (UY.obj KMY) KAX).injective
  exact hl.trans (hφ.trans hr.symm)

/-- Forgetting constant module coefficients identifies the native additive
cohomology group with cohomology of the constant underlying abelian group. -/
def etaleConstantCohomologyForgetEquiv (M : ModuleCat.{u} R) (n : ℕ) :
    etaleCohomology X R ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) n ≃+
      Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) n :=
  ((Sheaf.functorH X.smallEtaleTopology n).mapIso
    ((etaleConstantModuleForgetIso X R).app M)).addCommGroupIsoToAddEquiv

/-- The original coefficient-linear pullback agrees with actual constant
abelian pullback under the native constant-coefficient comparison. -/
theorem etaleConstantCohomologyPullbackMap_forget (M : ModuleCat.{u} R) (n : ℕ)
    (x : etaleCohomology Y R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M) n) :
    etaleConstantCohomologyForgetEquiv R (X := X) M n
        (etaleConstantCohomologyPullbackMap f R M n x) =
      Sheaf.H.map ((etaleAbelianPullbackConstantIso f).hom.app
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) n
        (etaleAbelianCohomologyPullbackMap f
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
            ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) n
          (etaleConstantCohomologyForgetEquiv R (X := Y) M n x)) := by
  let UX := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let UY := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := Y.smallEtaleTopology) (R := R)
  let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let δX := (etaleConstantModuleForgetIso X R).app M
  let δY := (etaleConstantModuleForgetIso Y R).app M
  let e := (etalePullbackForgetCoefficientsIso f R).app F
  let εm := (etalePullbackConstantIso f R).hom.app M
  let εa := (etaleAbelianPullbackConstantIso f).hom.app
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)
  change Sheaf.H.{u} (UY.obj F) n at x
  change Sheaf.H.map δX.hom n
      (Sheaf.H.map (UX.map εm) n
        (Sheaf.H.map e.inv n (etaleAbelianCohomologyPullbackMap f (UY.obj F) n x))) =
    Sheaf.H.map εa n
      (etaleAbelianCohomologyPullbackMap f _ n (Sheaf.H.map δY.hom n x))
  rw [etaleAbelianCohomologyPullbackMap_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun ψ => Sheaf.H.map ψ n
    (etaleAbelianCohomologyPullbackMap f (UY.obj F) n x))
      (etalePullbackForgetCoefficientsIso_constant R f M)

end EtaleCohomology
