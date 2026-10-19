/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransportFiber
import Nyll.EtaleFundamentalGroups.Cohomology.TransportedFiberTorsor
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCommonUnit
import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryCommonUnit

/-!
# Common boundary powers of the actual transported cover torsor

The fiber equivalence is constructed from coverTransportActionIso. Coefficient
translations are pulled back to that very fiber, leaving its monodromy action
unchanged. Diagonal boundary relations then force a common unit on its actual
torsor character. No global character equality, matching model torsor, or
common exponent is assumed.

The range correspondence and diagonal relations are geometric input slots:
they are provided by cusp recognition and the actual boundary-inertia theorems.
This is an intermediate transport theorem, not the final configuration theorem.
-/

noncomputable section
open CategoryTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open ProCGroups.Abelian
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

universe u₁ v₁ u₂ v₂ w
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [GaloisCategory C] [GaloisCategory D]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (G : D ⥤ FintypeCat.{w}) [FiberFunctor G]

/-- The genuine transported torsor satisfies one common finite unit-power
formula at every matched boundary coordinate. The exponent is derived. -/
theorem coverTransport_torsor_boundary_power
    (α : Aut F ≃ₜ* Aut G) (X : C)
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (n : InvertibleExponent K)
    [TopologicalSpace (rootsOfUnity n.val K)] [T1Space (rootsOfUnity n.val K)]
    [Torsor (rootsOfUnity n.val K) (F.obj X)]
    [SMulCommClass (Aut F) (rootsOfUnity n.val K) (F.obj X)]
    {ι : Type*} [Fintype ι]
    (b : ι → (primeToRootsSystem K K).inverseLimit →*
      TopologicalAbelianization (Aut G))
    (c : ι → (primeToRootsSystem K K).inverseLimit →*
      TopologicalAbelianization (Aut F))
    (hb : ∀ i, Function.Injective (b i))
    (hc : ∀ i, Function.Injective (c i))
    (hrange : ∀ i, (b i).range.map
      (TopologicalAbelianization.congr α.symm).toMulEquiv.toMonoidHom = (c i).range)
    (hconstant : ∀ t, (∏ i, b i t) = 1)
    (hrelations : ∀ t : ι → (primeToRootsSystem K K).inverseLimit,
      (∏ i, c i (t i)) = 1 → ∀ i j, t i = t j)
    (i₀ : ι) :
    let e := coverTransportFiberEquiv F G α X
    let he := coverTransportFiberEquiv_smul F G α X
    letI := transportedFiberTorsor e
    letI := transportedFiberSMulCommClass α.toMulEquiv e he
    ∃ u : (ZMod n.val)ˣ,
      ∀ (q : G.obj ((coverTransportOfAutEquiv F G α).functor.obj X)) (i : ι)
        (t : (primeToRootsSystem K K).inverseLimit),
        torsorAbelianCharacter (G := Aut G) q (b i t) =
          torsorAbelianCharacter (G := Aut F) (e q) (c i t) ^ (u : ZMod n.val).val := by
  let e := coverTransportFiberEquiv F G α X
  let he := coverTransportFiberEquiv_smul F G α X
  let := transportedFiberTorsor e
  let := transportedFiberSMulCommClass α.toMulEquiv e he
  obtain ⟨u, hu⟩ :=
    AnabelianGeometry.CuspidalInertia.exists_common_unit_on_boundary_characters
      K K b c hb hc (TopologicalAbelianization.congr α.symm).toMulEquiv
      hrange hconstant hrelations i₀ n
  refine ⟨u, ?_⟩
  intro q i t
  rw [transportedFiber_torsorAbelianCharacter α e he q]
  exact hu i (torsorAbelianCharacter (G := Aut F) (e q)).toMonoidHom t

end CategoryTheory.PreGaloisCategory
