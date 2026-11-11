/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.AbelJacobiFiniteH1
public import Nyll.JacobianVarieties.Kummer.CohomologyAbelianPullbackCharacters
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateComparison
public import Nyll.ProCGroups.Abelian.RootsOfUnityCharacterCriterion
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianPrimeToTateComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.LangFirstQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiniteQuotientRealization
public import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
public import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Topology.Constructions
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# The actual Abel--Jacobi Tate isomorphism

Finite H¹ pullback detects the actual abelianized fundamental-group map.
Composing with multiplication-cover monodromy gives the actual full Tate
module. The formula on the abelianization quotient records the inducing map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open scoped IsMulCommutative

namespace JacobianVarieties.Kummer

/-- Actual Abel--Jacobi induces the full Tate isomorphism on the
topological abelianization, with its original quotient map. -/
theorem exists_abelJacobi_fullTate_equiv
    {K F₀ : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
 :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M₀.C),
      ∃ e : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) ≃ₜ*
          Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
        ∀ γ : Aut (FiniteEtale.fiber ξ),
          e (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ) =
            G.fundamentalGroupEquivFullTateAt hc (ξ ≫ aj.1)
              (FiniteEtale.fundamentalGroupHom aj.1 ξ γ) := by
  intro G hc Ω hΩ hsep ξ
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  let eT := G.fundamentalGroupEquivFullTateAt hc (ξ ≫ aj.1)
  have : IsMulCommutative (Aut (FiniteEtale.fiber (ξ ≫ aj.1))) :=
    ⟨⟨fun a b => eT.injective
      ((eT.map_mul a b).trans ((mul_comm (eT a) (eT b)).trans
        (eT.map_mul b a).symm))⟩⟩
  let f := ProCGroups.Abelian.TopologicalAbelianization.lift
    (FiniteEtale.fundamentalGroupHom aj.1 ξ)
  have hf (n : ℕ+) :
      let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
      let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
      Function.Bijective (f.compLeft (rootsOfUnity (n : ℕ) K)) := by
    intro htop hdiscrete
    have hn : IsUnit ((n : ℕ) : K) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr n.ne_zero)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    exact (bijective_constantH1Pullback_iff_abelianCharacterPullback aj.1 A ξ).mp
      (abelJacobi_finiteH1Pullback_bijective M₀ ε D hD aj hclass n hn)
  have : TotallyDisconnectedSpace
      (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator (Aut (FiniteEtale.fiber ξ)))
      (Subgroup.isClosed_closedCommutator _)
  let e := ProCGroups.Duality.equivOfBijectiveRootsOfUnityPullback K f hf
  refine ⟨e.trans eT, ?_⟩
  intro γ
  change eT (f (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ)) = _
  rw [ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk]

/-- Actual Abel--Jacobi identifies the maximal pro-Sigma quotient of the
geometric abelianization with the original Jacobian's restricted Tate module.
The map is the original Abel--Jacobi map followed by multiplication monodromy. -/
theorem exists_abelJacobi_sigmaTate_equiv
    {K F₀ : Type u} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (sigma : Set ℕ)
    (hI : ∀ n : ProCGroups.sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K)) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M₀.C),
      ∃ e :
          (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) ⧸
            ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup sigma)
              (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)))) ≃ₜ*
          Multiplicative (ProCGroups.RestrictedTateModule (G.AlgPoints hc K)
            (ProCGroups.sigmaTorsionIndices sigma)),
        ∀ γ : Aut (FiniteEtale.fiber ξ),
          e (QuotientGroup.mk'
              (ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup sigma)
                (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))))
              (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ)) =
            RelativeGroupLaw.UnitMultiplication.fundamentalGroupSigmaEquivTateAt
              G hc sigma hI (ξ ≫ aj.val)
                (QuotientGroup.mk'
                  (ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup sigma)
                    (Aut (FiniteEtale.fiber (ξ ≫ aj.val))))
                  (FiniteEtale.fundamentalGroupHom aj.val ξ γ)) := by
  intro G hc Ω hΩ hsep ξ
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  have : IsMulCommutative (Aut (FiniteEtale.fiber (ξ ≫ aj.val))) :=
    ⟨⟨G.fundamentalGroup_mul_comm_at (ξ ≫ aj.val)⟩⟩
  let f := ProCGroups.Abelian.TopologicalAbelianization.lift
    (FiniteEtale.fundamentalGroupHom aj.val ξ)
  have hf (n : ProCGroups.sigmaTorsionIndices sigma) :
      let _ : TopologicalSpace (rootsOfUnity (n.val : ℕ) K) := ⊥
      let _ : DiscreteTopology (rootsOfUnity (n.val : ℕ) K) := ⟨rfl⟩
      Function.Bijective (f.compLeft (rootsOfUnity (n.val : ℕ) K)) := by
    intro htop hdiscrete
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n.val : ℕ) K))
    exact (bijective_constantH1Pullback_iff_abelianCharacterPullback aj.val A ξ).mp
      (abelJacobi_finiteH1Pullback_bijective M₀ ε D hD aj hclass n.val (hI n))
  have : TotallyDisconnectedSpace
      (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator (Aut (FiniteEtale.fiber ξ)))
      (Subgroup.isClosed_closedCommutator _)
  let e := ProCGroups.Duality.residualEquivOfBijectiveSigmaRootsOfUnityPullback
    K sigma hI f hf
  let eT := RelativeGroupLaw.UnitMultiplication.fundamentalGroupSigmaEquivTateAt
    G hc sigma hI (ξ ≫ aj.val)
  refine ⟨e.trans eT, ?_⟩
  intro γ
  change eT (e (QuotientGroup.mk' _
    (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ))) = _
  rw [ProCGroups.Duality.residualEquivOfBijectiveSigmaRootsOfUnityPullback_apply_mk,
    ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk]

/-- Every original finite abelian pro-Sigma quotient of the curve's geometric
fundamental group is represented by a pointed Galois cover of its Jacobian.
Its original pointed deck quotient, precomposed with the actual Abel--Jacobi
map, equals the prescribed quotient, including its labels in the finite group. -/
theorem exists_abelJacobi_sigma_pointedGaloisCover
    {K F₀ : Type u} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (sigma : Set ℕ)
    (hI : ∀ n : ProCGroups.sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M₀.C)
    (Q : Type u) [CommGroup Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (hQ : ProCGroups.FiniteGroupClass.sigmaGroup sigma Q)
    (φ : π₁ᵉᵗ(ξ) →ₜ* Q) (hφ : Function.Surjective φ) :
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    ∃ (V : FiniteEtale D.P) (hV : CategoryTheory.PreGaloisCategory.IsGalois V)
      (v : (FiniteEtale.fiber (ξ ≫ aj.val)).obj V) (e : (Aut V)ᵐᵒᵖ ≃* Q),
      let _ : CategoryTheory.PreGaloisCategory.IsGalois V := hV
      e.toMonoidHom.comp
        ((EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          (ξ ≫ aj.val) V hV v).comp (FiniteEtale.fundamentalGroupHom aj.val ξ).toMonoidHom) =
        φ.toMonoidHom := by
  intro connected
  have : Finite Q := (ProCGroups.FiniteGroupClass.sigmaGroup sigma).finite hQ
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  obtain ⟨E, hE⟩ := exists_abelJacobi_sigmaTate_equiv M₀ ε D hD aj hclass sigma hI Ω ξ
  let ET := RelativeGroupLaw.UnitMultiplication.fundamentalGroupSigmaEquivTateAt
    G hc sigma hI (ξ ≫ aj.val)
  let Qup := ULift.{u + 1} Q
  let eQ : Qup ≃* Q := MulEquiv.ulift
  let up : Q →ₜ* Qup :=
    { toMonoidHom := eQ.symm.toMonoidHom
      continuous_toFun := continuous_uliftUp }
  let down : Qup →ₜ* Q :=
    { toMonoidHom := eQ.toMonoidHom
      continuous_toFun := continuous_uliftDown }
  have hQup : ProCGroups.FiniteGroupClass.sigmaGroup sigma Qup := by
    refine ⟨inferInstance, ?_⟩
    simpa only [Qup, Nat.card_ulift] using hQ.2
  have hQbasis : ProCGroups.ProC.HasOpenNormalBasisInClass
      (ProCGroups.FiniteGroupClass.sigmaGroup sigma) Qup :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma) hQup
  let φab := ProCGroups.Abelian.TopologicalAbelianization.lift (up.comp φ)
  let φSigmaUp := ProCGroups.ProC.lift_proCResidualCoreQuotient
    (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary φab hQbasis
  let φSigma := down.comp φSigmaUp
  let qJ : π₁ᵉᵗ(ξ ≫ aj.val) →ₜ*
      π₁ᵉᵗ(ξ ≫ aj.val) ⧸ ProCGroups.ProC.proCResidualCore
        (ProCGroups.FiniteGroupClass.sigmaGroup sigma) π₁ᵉᵗ(ξ ≫ aj.val) :=
    { toMonoidHom := QuotientGroup.mk' _
      continuous_toFun := QuotientGroup.continuous_mk }
  let ψ := φSigma.comp ((ContinuousMonoidHom.toContinuousMonoidHom E.symm).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom ET).comp qJ))
  have hψ : ψ.comp (FiniteEtale.fundamentalGroupHom aj.val ξ) = φ := by
    apply ContinuousMonoidHom.ext
    intro γ
    change (φSigmaUp (E.symm (ET (qJ (FiniteEtale.fundamentalGroupHom aj.val ξ γ))))).down =
      φ γ
    have hcompare := (congrArg E.symm (hE γ)).symm.trans (E.symm_apply_apply _)
    exact (congrArg (fun z => (φSigmaUp z).down) hcompare).trans
      (congrArg ULift.down
        ((ProCGroups.ProC.lift_proCResidualCoreQuotient_mk
          (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary
          φab hQbasis (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ)).trans
            (ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk (up.comp φ) γ)))
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨γ, rfl⟩ := hφ z
    exact ⟨FiniteEtale.fundamentalGroupHom aj.val ξ γ, DFunLike.congr_fun hψ γ⟩
  obtain ⟨V, hV, v, e, he⟩ := FiniteEtale.exists_galoisCover_quotient_mulEquiv
    (ξ ≫ aj.val) Q ψ hψsurj
  refine ⟨V, hV, v, e, ?_⟩
  intro coverGalois
  apply MonoidHom.ext
  intro γ
  exact (DFunLike.congr_fun he (FiniteEtale.fundamentalGroupHom aj.val ξ γ)).trans
    (DFunLike.congr_fun hψ γ)

/-- Every actual finite abelian Sigma Galois cover of the curve is the
pullback of an actual Jacobian cover. The recovered isomorphism retains the
chosen point, and the cover degree is unchanged at every geometric point
of the Jacobian, including its origin. -/
theorem exists_abelJacobi_sigma_pullbackCover
    {K F₀ : Type u} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (sigma : Set ℕ)
    (hI : ∀ n : ProCGroups.sigmaTorsionIndices sigma, IsUnit ((n.val : ℕ) : K))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M₀.C)
    (W : FiniteEtale M₀.C) (hW : CategoryTheory.PreGaloisCategory.IsGalois W)
    (w : (FiniteEtale.fiber ξ).obj W)
    (hcomm : IsMulCommutative (Aut W))
    (hSigma : ProCGroups.FiniteGroupClass.sigmaGroup sigma (Aut W)ᵐᵒᵖ) :
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    ∃ (V : FiniteEtale D.P) (_ : CategoryTheory.PreGaloisCategory.IsGalois V)
      (v : (FiniteEtale.fiber (ξ ≫ aj.val)).obj V)
      (j : W ≅ (FiniteEtale.pullback aj.val).obj V),
      FiniteEtale.pointedPullbackFiberEquiv aj.val ξ (ξ ≫ aj.val) rfl V
          ((FiniteEtale.fiber ξ).map j.hom w) = v ∧
      ∀ (Ω' : Type u) [Field Ω'] [IsSepClosed Ω'] (y : Spec (.of Ω') ⟶ D.P),
        Nat.card ((FiniteEtale.fiber y).obj V) = Nat.card ((FiniteEtale.fiber ξ).obj W) := by
  intro connected
  classical
  let : CategoryTheory.PreGaloisCategory.IsGalois W := hW
  let : IsMulCommutative (Aut W) := hcomm
  let : CommGroup (Aut W)ᵐᵒᵖ := inferInstance
  let : TopologicalSpace (Aut W)ᵐᵒᵖ := ⊥
  let : DiscreteTopology (Aut W)ᵐᵒᵖ := ⟨rfl⟩
  let φ := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientHom ξ W hW w
  have hφ : Function.Surjective φ :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective ξ W hW w
  obtain ⟨V, hV, v, e, he⟩ := exists_abelJacobi_sigma_pointedGaloisCover
    M₀ ε D hD aj hclass sigma hI Ω ξ (Aut W)ᵐᵒᵖ hSigma φ hφ
  obtain ⟨j, hj⟩ := FiniteEtale.exists_pointedPullbackCoverIso_of_quotientLabels
    aj.val ξ W hW w V hV v e he
  refine ⟨V, hV, v, j, hj, ?_⟩
  let eW := (FintypeCat.equivEquivIso.symm ((FiniteEtale.fiber ξ).mapIso j)).trans
    (FiniteEtale.pointedPullbackFiberEquiv aj.val ξ (ξ ≫ aj.val) rfl V)
  have hcard : Nat.card ((FiniteEtale.fiber (ξ ≫ aj.val)).obj V) =
      Nat.card ((FiniteEtale.fiber ξ).obj W) := (Nat.card_congr eW).symm
  intro Ω' hΩ' hsep' y
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso y (ξ ≫ aj.val))
  exact (Nat.card_congr (FintypeCat.equivEquivIso.symm (t.app V))).trans hcard

end JacobianVarieties.Kummer
