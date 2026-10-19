/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter

/-! # Torsor structures on the actual transported cover fiber -/

noncomputable section
namespace EtaleFundamentalGroups.Cohomology

/-- Pull coefficient translations back onto the actual transported fiber.
The original monodromy action on that fiber is not replaced. -/
@[instance_reducible]
def transportedFiberTorsor
    {A P Q : Type*} [Group A] [Torsor A P] (e : Q ≃ P) : Torsor A Q := by
  let : SMul A Q := ⟨fun a q => e.symm (a • e q)⟩
  let : SDiv A Q := ⟨fun q r => e q /ₛ e r⟩
  let : Nonempty Q := Nonempty.map e.symm inferInstance
  exact e.injective.torsor e (fun a q => e.apply_symm_apply _) (fun _ _ => rfl)

/-- Commutation is proved from the actual action comparison, rather than
postulated as an additional property of the transported fiber. -/
theorem transportedFiberSMulCommClass
    {A P Q G H : Type*} [CommGroup A] [Torsor A P]
    [Group G] [Group H] [MulAction G P] [SMulCommClass G A P] [MulAction H Q]
    (α : G ≃* H) (e : Q ≃ P)
    (he : ∀ (h : H) (q : Q), e (h • q) = α.symm h • e q) :
    letI := transportedFiberTorsor e
    SMulCommClass H A Q := by
  let := transportedFiberTorsor e
  refine ⟨fun h a q => e.injective ?_⟩
  change e (h • e.symm (a • e q)) = e (e.symm (a • e (h • q)))
  rw [he, e.apply_symm_apply, e.apply_symm_apply, he]
  exact smul_comm (α.symm h) a (e q)

/-- Displacement of the constructed torsor equals the source displacement
precomposed by the inverse group isomorphism. -/
theorem transportedFiber_torsorCharacter
    {A P Q G H : Type*} [CommGroup A] [TopologicalSpace A] [Torsor A P]
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [MulAction G P] [SMulCommClass G A P] [MulAction H Q]
    [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
    [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul H Q]
    (α : G ≃ₜ* H) (e : Q ≃ P)
    (he : ∀ (h : H) (q : Q), e (h • q) = α.symm h • e q) (q : Q) :
    letI := transportedFiberTorsor e
    letI := transportedFiberSMulCommClass α.toMulEquiv e he
    torsorCharacter (G := H) q =
      (torsorCharacter (G := G) (e q)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom α.symm) := by
  let := transportedFiberTorsor e
  let := transportedFiberSMulCommClass α.toMulEquiv e he
  apply ContinuousMonoidHom.ext
  intro h
  change (e (h • q) /ₛ e q : A) = (α.symm h • e q) /ₛ e q
  rw [he]

/-- The same compatibility holds on the actual topological abelianizations. -/
theorem transportedFiber_torsorAbelianCharacter
    {A P Q G H : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    [Torsor A P] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MulAction G P] [SMulCommClass G A P] [MulAction H Q]
    [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
    [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul H Q]
    (α : G ≃ₜ* H) (e : Q ≃ P)
    (he : ∀ (h : H) (q : Q), e (h • q) = α.symm h • e q) (q : Q) :
    letI := transportedFiberTorsor e
    letI := transportedFiberSMulCommClass α.toMulEquiv e he
    torsorAbelianCharacter (G := H) q =
      (torsorAbelianCharacter (G := G) (e q)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom
          (ProCGroups.Abelian.TopologicalAbelianization.congr α.symm)) := by
  let := transportedFiberTorsor e
  let := transportedFiberSMulCommClass α.toMulEquiv e he
  apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
  intro h
  change (e (h • q) /ₛ e q : A) = (α.symm h • e q) /ₛ e q
  rw [he]

end EtaleFundamentalGroups.Cohomology
