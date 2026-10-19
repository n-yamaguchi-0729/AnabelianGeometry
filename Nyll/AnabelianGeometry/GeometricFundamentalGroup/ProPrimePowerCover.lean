/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.PrimeExponentCharacters
import Nyll.ProCGroups.ProC.MaximalQuotients.SubgroupComparison
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualUniversalProperty
import Nyll.ProCGroups.FiniteGroups.PGroupFormation
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalFundamentalGroup
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.AnabelianGeometry.WeightFiltration.CharacterAnnihilatorTransport
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The power-image cover of an abelian maximal pro-prime quotient

Finite prime-order characters make the power image open. Restricting the
maximal quotient to its inverse image and using the surjective power map
then bounds the cover's prime-order character count by the original count.
The open normal subgroup is realized as an actual finite étale cover.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open ProCGroups ProCGroups.ProC
open scoped IsMulCommutative

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

private theorem exists_openNormal_character_card_le_of_abelian_maximalProP
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (p : ℕ) [Fact p.Prime]
    [TopologicalSpace (rootsOfUnity p K)] [DiscreteTopology (rootsOfUnity p K)]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Finite (G →ₜ* rootsOfUnity p K)]
    (hn : 1 < Nat.card (G →ₜ* rootsOfUnity p K))
    (hcomm : IsMulCommutative (G ⧸ proCResidualCore (FiniteGroupClass.pGroup p) G)) :
    ∃ H : OpenNormalSubgroup G, 1 < H.toSubgroup.index ∧
      Nat.card (H →ₜ* rootsOfUnity p K) ≤ Nat.card (G →ₜ* rootsOfUnity p K) := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let R := proCResidualCore (FiniteGroupClass.pGroup p) G
  have hR : IsClosed (R : Set G) := proCResidualCore_isClosed _ _
  have : IsClosed (R : Set G) := hR
  let A := G ⧸ R
  have : IsMulCommutative A := hcomm
  have : TotallyDisconnectedSpace A :=
    totallyDisconnectedSpace_quotient_closedNormal R hR
  let q : G →ₜ* A := ContinuousMonoidHom.quotientMk R
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective R
  have hmax : IsMaximalProCQuotient (FiniteGroupClass.pGroup p) q.toMonoidHom :=
    isMaximalProCQuotient_residualCore (FiniteGroupClass.pGroup_formation p)
      (FiniteGroupClass.pGroup_hereditary p)
  let liftC : rootsOfUnity p K →ₜ* ULift.{u} (rootsOfUnity p K) :=
    ⟨{ toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl },
      continuous_uliftUp⟩
  let lowerC : ULift.{u} (rootsOfUnity p K) →ₜ* rootsOfUnity p K :=
    ⟨(MulEquiv.ulift).toMonoidHom, continuous_uliftDown⟩
  have hC : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)
      (ULift.{u} (rootsOfUnity p K)) :=
    HasOpenNormalBasisInClass.of_finite_discrete
      (FiniteGroupClass.pGroup_formation p).quotientClosed
      ⟨inferInstance, IsPGroup.of_card (n := 1) (by
        rw [pow_one]
        exact (Nat.card_congr (MulEquiv.ulift.toEquiv)).trans
          (HasEnoughRootsOfUnity.natCard_rootsOfUnity K p))⟩
  have hpowC (c : rootsOfUnity p K) : c ^ p = 1 := by
    exact (congrArg (fun n : ℕ => c ^ n)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity K p).symm).trans pow_card_eq_one'
  let power : A →ₜ* A := ⟨powMonoidHom p, continuous_id.pow p⟩
  let U : Subgroup A := power.toMonoidHom.range
  have hUclosed : IsClosed (U : Set A) := ContinuousMonoidHom.isClosed_range power
  have : IsClosed (U : Set A) := hUclosed
  have : CompactSpace U := hUclosed.isClosedEmbedding_subtypeVal.compactSpace
  have : TotallyDisconnectedSpace (A ⧸ U) :=
    totallyDisconnectedSpace_quotient_closedNormal U hUclosed
  have hpowQ (z : A ⧸ U) : z ^ p = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective U z
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := U) (a ^ p)).mpr ⟨a, rfl⟩
  let c : rootsOfUnity p K ≃* Multiplicative (ZMod p) :=
    mulEquivOfCyclicCardEq (by
      rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity K p]
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  have hsep (a : A) (ha : a ∉ U) :
      ∃ χ : A →ₜ* rootsOfUnity p K, χ a ≠ 1 := by
    have hqa : QuotientGroup.mk' U a ≠ 1 :=
      fun h => ha ((QuotientGroup.eq_one_iff (N := U) a).mp h)
    obtain ⟨χ, hχ⟩ := ProCGroups.Abelian.exists_prime_character_profinite hpowQ hqa
    let c' : Multiplicative (ZMod p) →ₜ* rootsOfUnity p K :=
      ⟨c.symm.toMonoidHom, continuous_of_discreteTopology⟩
    refine ⟨c'.comp (χ.comp (ContinuousMonoidHom.quotientMk U)), ?_⟩
    intro h
    apply hχ
    apply c.symm.injective
    exact h.trans c.symm.map_one.symm
  have : Finite (A →ₜ* rootsOfUnity p K) := Finite.of_injective
    (fun χ : A →ₜ* rootsOfUnity p K => χ.comp q) (by
      intro χ ψ h
      apply ContinuousMonoidHom.ext
      intro a
      obtain ⟨g, rfl⟩ := hq a
      exact DFunLike.congr_fun h g)
  have hUchars : (U : Set A) =
      ⋂ χ : A →ₜ* rootsOfUnity p K, (χ.toMonoidHom.ker : Set A) := by
    ext a
    rw [Set.mem_iInter]
    constructor
    · rintro ⟨b, rfl⟩ χ
      change χ (b ^ p) = 1
      rw [map_pow]
      exact hpowC (χ b)
    · intro h
      by_contra ha
      obtain ⟨χ, hχ⟩ := hsep a ha
      exact hχ (h χ)
  have hUopen : IsOpen (U : Set A) := by
    rw [hUchars]
    exact isOpen_iInter_of_finite fun χ =>
      (isOpen_discrete ({1} : Set (rootsOfUnity p K))).preimage χ.continuous
  let H : OpenNormalSubgroup G :=
    { toSubgroup := U.comap q.toMonoidHom
      isOpen' := hUopen.preimage q.continuous }
  have hHne : H.toSubgroup ≠ ⊤ := by
    intro hH
    have : Nontrivial (G →ₜ* rootsOfUnity p K) := Finite.one_lt_card_iff_nontrivial.mp hn
    obtain ⟨χ, hχ⟩ := exists_ne (1 : G →ₜ* rootsOfUnity p K)
    let χbar := lowerC.comp
      (lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary p) (liftC.comp χ) hC)
    apply hχ
    apply ContinuousMonoidHom.ext
    intro g
    have hgH : g ∈ H.toSubgroup := by
      rw [hH]
      exact Subgroup.mem_top g
    have hg : q g ∈ U := hgH
    obtain ⟨a, ha⟩ := hg
    calc
      χ g = χbar (q g) :=
        (congrArg lowerC (lift_proCResidualCoreQuotient_mk
          (FiniteGroupClass.pGroup_hereditary p) (liftC.comp χ) hC g)).symm
      _ = χbar (a ^ p) := congrArg χbar ha.symm
      _ = 1 := (χbar.map_pow a p).trans (hpowC (χbar a))
  let qU := ContinuousMonoidHom.restrictPreimage q U
  have hmaxU := hmax.restrictPreimage (FiniteGroupClass.pGroup_fullFormation p) q U
  have hlift (χ : H →ₜ* rootsOfUnity p K) :
      ∃ ψ : U →ₜ* rootsOfUnity p K, ∀ h : H, ψ (qU h) = χ h := by
    obtain ⟨ψ, hψ, _⟩ := hmaxU.existsUnique_lift hC
      (liftC.comp χ).toMonoidHom (liftC.comp χ).continuous
    exact ⟨lowerC.comp ⟨ψ, hψ.1⟩,
      fun h => congrArg lowerC (DFunLike.congr_fun hψ.2 h)⟩
  let lift (χ : H →ₜ* rootsOfUnity p K) : U →ₜ* rootsOfUnity p K :=
    (hlift χ).choose
  have hlift_apply (χ : H →ₜ* rootsOfUnity p K) (h : H) : lift χ (qU h) = χ h :=
    (hlift χ).choose_spec h
  let f : (H →ₜ* rootsOfUnity p K) → (G →ₜ* rootsOfUnity p K) :=
    fun χ => ((lift χ).comp power.rangeRestrict).comp q
  have hf : Function.Injective f := by
    intro χ ψ h
    apply ContinuousMonoidHom.ext
    intro z
    obtain ⟨a, ha⟩ := (qU z).property
    obtain ⟨g, hg⟩ := hq a
    have hh := DFunLike.congr_fun h g
    change lift χ (power.rangeRestrict (q g)) = lift ψ (power.rangeRestrict (q g)) at hh
    have hpow : power.rangeRestrict (q g) = qU z := by
      apply Subtype.ext
      exact (congrArg power hg).trans ha
    rw [hpow, hlift_apply, hlift_apply] at hh
    exact hh
  have : Finite (G ⧸ H.toSubgroup) := openNormalSubgroup_finiteQuotient H
  exact ⟨H, Subgroup.one_lt_index_of_ne_top hHne, Nat.card_le_card_of_injective f hf⟩

/-- If the maximal pro-p fundamental group were abelian, a nontrivial
actual Galois cover would have no more μp-valued H¹ classes than the base.
The cover and its subgroup comparison are constructed, not assumed. -/
theorem exists_galoisCover_finiteH1_card_le_of_abelian_maximalProP
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme} [ConnectedSpace X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (p : ℕ) [Fact p.Prime]
    (hn : 1 < Nat.card (Sheaf.H.{0}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity p K)))) 1))
    (hcomm : IsMulCommutative
      (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi))) :
    ∃ (W : FiniteEtale X) (_ : IsGalois W)
      (xiW : Spec (.of Ω) ⟶ W.left), xiW ≫ W.hom = xi ∧
      1 < Nat.card ((fiber xi).obj W) ∧
      Nat.card (Sheaf.H.{0}
        ((constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (Additive (rootsOfUnity p K)))) 1) ≤
        Nat.card (Sheaf.H.{0}
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
            (AddCommGrpCat.of (Additive (rootsOfUnity p K)))) 1) := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let C := AddCommGrpCat.of (Additive (rootsOfUnity p K))
  let : TopologicalSpace (rootsOfUnity p K) := ⊥
  have : DiscreteTopology (rootsOfUnity p K) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative C) := ⊥
  have : DiscreteTopology (Multiplicative C) := ⟨rfl⟩
  let eX := finiteH1CharacterEquiv C xi
  have hcardX : Nat.card (Sheaf.H.{0}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1) =
      Nat.card (π₁ᵉᵗ(xi) →ₜ* rootsOfUnity p K) := Nat.card_congr eX.toEquiv
  have : Finite (π₁ᵉᵗ(xi) →ₜ* rootsOfUnity p K) :=
    Nat.finite_of_card_ne_zero (by
      rw [← hcardX]
      exact ne_of_gt (lt_trans Nat.zero_lt_one hn))
  obtain ⟨H, hH, hchars⟩ :=
    exists_openNormal_character_card_le_of_abelian_maximalProP K p (G := π₁ᵉᵗ(xi))
      (by rwa [← hcardX]) hcomm
  obtain ⟨W, hW, xiW, hxiW, eW, hdegree, _⟩ :=
    exists_galoisCover_lift_fundamentalGroup_equiv_openNormal_compatible xi H
  have : IsGalois W := hW
  have : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let eHW := (finiteH1CharacterEquiv C xiW).trans
    (WeightFiltration.characterPullback eW.symm)
  refine ⟨W, hW, xiW, hxiW, by rwa [hdegree], ?_⟩
  calc
    Nat.card (Sheaf.H.{0}
        ((constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1) =
        Nat.card (H →ₜ* rootsOfUnity p K) := Nat.card_congr eHW.toEquiv
    _ ≤ Nat.card (π₁ᵉᵗ(xi) →ₜ* rootsOfUnity p K) := hchars
    _ = _ := hcardX.symm

end AnabelianGeometry.GeometricFundamentalGroup
