/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.SurjectiveBaseChangeDescent

/-!
# The original deck group after connected surjective base change

If a Galois cover stays connected after surjective base change, the actual
pullback map on automorphisms is bijective and the new cover is Galois.
This preserves abelianity without replacing the cover by a Galois closure.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- Connected surjective base change preserves a Galois cover and its
original deck group through the actual pullback map. -/
theorem isGalois_pullback_and_bijective_mapAut_of_isConnected
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    (j : T ⟶ S) [Surjective j] (Y : FiniteEtale S) [IsGalois Y]
    [IsConnected ((FiniteEtale.pullback j).obj Y)] :
    IsGalois ((FiniteEtale.pullback j).obj Y) ∧
      Function.Bijective ((FiniteEtale.pullback j).mapAut Y) := by
  let F := FiniteEtale.pullback j
  let P := F.obj Y
  have hfaithful : F.Faithful := FiniteEtale.pullback_faithful_of_isDominant j
  have hinjective : Function.Injective (F.mapAut Y) := by
    intro σ τ h
    apply Aut.ext
    apply Iso.ext
    apply F.map_injective
    exact congrArg (fun a : Aut (F.obj Y) => a.asIso.hom) h
  let t : T := Classical.choice (inferInstance : Nonempty T)
  let Ω := AlgebraicClosure (T.residueField t)
  let ξ : Spec (.of Ω) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
      T.fromSpecResidueField t
  have hdegree : Nat.card (Aut Y) = P.hom.finrank (ξ (IsLocalRing.closedPoint Ω)) := by
    have hY := (FiniteEtale.isGalois_iff_card_aut_eq_finrank (ξ ≫ j) Y).mp
      (inferInstance : IsGalois Y)
    have hrank := Scheme.Hom.finrank_of_isPullback
      (Limits.pullback.fst Y.hom j) (Limits.pullback.snd Y.hom j)
        Y.hom j (IsPullback.of_hasPullback Y.hom j) (ξ (IsLocalRing.closedPoint Ω))
    exact hY.trans hrank.symm
  have hlower : Nat.card (Aut Y) ≤ Nat.card (Aut P) :=
    Nat.card_le_card_of_injective (F.mapAut Y) hinjective
  have hupper : Nat.card (Aut P) ≤ Nat.card (Aut Y) := by
    have h := card_aut_le_card_fiber_of_connected (FiniteEtale.fiber ξ) P
    rw [FiniteEtale.natCard_fiber_eq_finrank ξ P, ← hdegree] at h
    exact h
  have hcard : Nat.card (Aut Y) = Nat.card (Aut P) := Nat.le_antisymm hlower hupper
  have hP : IsGalois P :=
    (FiniteEtale.isGalois_iff_card_aut_eq_finrank ξ P).mpr (hcard.symm.trans hdegree)
  exact ⟨hP, (Nat.bijective_iff_injective_and_card (F.mapAut Y)).mpr
    ⟨hinjective, hcard⟩⟩

/-- The same actual pullback preserves an abelian deck group when the
cover remains connected. -/
theorem isMulCommutative_aut_pullback_of_isConnected
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    (j : T ⟶ S) [Surjective j] (Y : FiniteEtale S) [IsGalois Y]
    [IsMulCommutative (Aut Y)] [IsConnected ((FiniteEtale.pullback j).obj Y)] :
    IsMulCommutative (Aut ((FiniteEtale.pullback j).obj Y)) := by
  let f := (FiniteEtale.pullback j).mapAut Y
  have hsurj : Function.Surjective f :=
    (isGalois_pullback_and_bijective_mapAut_of_isConnected j Y).2.2
  exact .of_comm fun σ τ => by
    obtain ⟨a, rfl⟩ := hsurj σ
    obtain ⟨b, rfl⟩ := hsurj τ
    rw [← f.map_mul, ← f.map_mul, mul_comm' a b]

end EtaleFundamentalGroups
