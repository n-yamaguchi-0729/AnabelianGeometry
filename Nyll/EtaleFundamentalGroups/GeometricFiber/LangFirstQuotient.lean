/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Geometry.OriginalFiniteFieldLang
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FirstQuotientFunctoriality
public import Nyll.AbelianVarieties.Geometry.AbelianSchemeGeometricallyIntegral
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperGroupScheme
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# Original Lang covers factor through the first arithmetic quotient

The geometric fundamental group of a proper smooth connected group scheme
is commutative in every characteristic. The actual arithmetic-kernel
comparison transfers this fact to the original arithmetic fundamental
group. Functoriality then kills the geometric closed commutator for every
original finite étale cover pulled back from that group scheme.

The original Lang cover is an instance of this general fact. Its action at
an arbitrary geometric point, including a geometric generic point, factors
through the first arithmetic quotient. Neither a rational base point nor
connectedness of the Lang pullback is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale NeronModelInfra
open GoodReductionJacobian ProCGroups.Abelian

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

section ProperGroup

variable {K : Type u} [Field K] [IsSepClosed K]
  {B : Scheme.{u}} {g : B ⟶ Spec (.of K)}
  [IsProper g] [Smooth g] [GeometricallyConnected g]
  (H : RelativeGroupLaw K g)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ B)

include H in
/-- Commutativity of the actual geometric fundamental group holds at every
geometric point, by the existing unit-point theorem and fiber comparison. -/
theorem fundamentalGroup_mul_comm_at (x y : π₁ᵉᵗ(xi)) : x * y = y * x := by
  have : ConnectedSpace B := GeometricallyConnected.connectedSpace g g.isOpenMap
  let e : Spec (.of K) ⟶ B := (H.one (𝟙 _)).val
  let t : fiber xi ≅ fiber e := Classical.choice (nonempty_fiber_iso xi e)
  let E := fundamentalGroupIsoOfFiberIso xi e t
  apply E.injective
  rw [map_mul, map_mul]
  exact H.fundamentalGroup_mul_comm (E x) (E y)

end ProperGroup

section ArithmeticKernel

variable (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
  {A : Scheme.{u}} {f : A ⟶ Spec (.of k)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (G : RelativeGroupLaw k f)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

include G

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k κ))

/-- The original arithmetic kernel of a proper smooth connected group
scheme is abelian; no comparison of its monodromy action is assumed. -/
theorem arithmeticKernel_mul_comm
    (eta : Spec (.of Ω) ⟶ pullback b f)
    (x y : (arithmeticFundamentalGroupHom k κ f
      (eta ≫ pullback.snd b f)).toMonoidHom.ker) : x * y = y * x := by
  have : IsSepClosed κ := IsSepClosure.sep_closed k
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated f
  have : ConnectedSpace (pullback b f : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst b f)
  have : ConnectedSpace (pullback f b : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f b)
  let s : pullback b f ≅ pullback f b := pullbackSymmetry b f
  let T : FiniteEtale (pullback f b) ≌ FiniteEtale (pullback b f) :=
    MorphismProperty.Over.pullbackIso
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ s.symm
  have : (FiniteEtale.pullback s.hom).IsEquivalence := T.isEquivalence_functor
  let q := fundamentalGroupHom s.hom eta
  have hq : Function.Injective q :=
    (fundamentalGroupHom_bijective_of_pullback_isEquivalence s.hom eta).1
  let E := geometricFundamentalGroupKernelEquiv k κ A f eta
  apply E.symm.injective
  rw [map_mul, map_mul]
  apply hq
  rw [map_mul, map_mul]
  exact fundamentalGroup_mul_comm_at (G.baseChange b) (eta ≫ s.hom) _ _

/-- The entire geometric closed commutator vanishes in the original
arithmetic kernel of the target group scheme. -/
theorem arithmeticKernel_closedCommutator_eq_bot
    (eta : Spec (.of Ω) ⟶ pullback b f) :
    Subgroup.closedCommutator
      (arithmeticFundamentalGroupHom k κ f (eta ≫ pullback.snd b f)).toMonoidHom.ker = ⊥ := by
  let D := (arithmeticFundamentalGroupHom k κ f
    (eta ≫ pullback.snd b f)).toMonoidHom.ker
  let : CommGroup D :=
    { (inferInstance : Group D) with mul_comm := arithmeticKernel_mul_comm k κ G eta }
  exact TopologicalAbelianization.closedCommutator_eq_bot_of_commGroup_t1 D

/-- An original morphism to the group scheme has equal full target
monodromy on elements equal in the source's first arithmetic quotient. -/
theorem fundamentalGroupHom_eq_of_firstMk_eq
    {C : Scheme.{u}} (a : C ⟶ A) (xi : Spec (.of Ω) ⟶ C)
    (eta : Spec (.of Ω) ⟶ pullback b f)
    (heta : eta ≫ pullback.snd b f = xi ≫ a)
    (x y : π₁ᵉᵗ(xi))
    (hxy : arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ (a ≫ f) xi).toMonoidHom.ker x =
      arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ (a ≫ f) xi).toMonoidHom.ker y) :
    fundamentalGroupHom a xi x = fundamentalGroupHom a xi y := by
  have hcomm : Subgroup.closedCommutator
      (arithmeticFundamentalGroupHom k κ f (xi ≫ a)).toMonoidHom.ker = ⊥ := by
    have h := arithmeticKernel_closedCommutator_eq_bot k κ G eta
    rw [heta] at h
    exact h
  have hbot : arithmeticFirstKernel
      (arithmeticFundamentalGroupHom k κ f (xi ≫ a)).toMonoidHom.ker = ⊥ := by
    rw [arithmeticFirstKernel, hcomm, Subgroup.map_bot]
  have hmem := QuotientGroup.eq_iff_div_mem.mp
    (arithmeticFirstMk_eq_of_source_eq k κ a f xi x y hxy)
  rw [hbot] at hmem
  exact div_eq_one.mp (Subgroup.mem_bot.mp hmem)

/-- Every original finite étale cover pulled back from the group scheme
has the same native action on equal first-quotient representatives. -/
theorem pullback_smul_eq_of_firstMk_eq
    {C : Scheme.{u}} (a : C ⟶ A) (xi : Spec (.of Ω) ⟶ C)
    (eta : Spec (.of Ω) ⟶ pullback b f)
    (heta : eta ≫ pullback.snd b f = xi ≫ a)
    (x y : π₁ᵉᵗ(xi))
    (hxy : arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ (a ≫ f) xi).toMonoidHom.ker x =
      arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ (a ≫ f) xi).toMonoidHom.ker y)
    (W : FiniteEtale A) (z : (fiber xi).obj ((FiniteEtale.pullback a).obj W)) :
    x • z = y • z := by
  let t := pullbackFiberIso a xi
  have hmap := fundamentalGroupHom_eq_of_firstMk_eq k κ G a xi eta heta x y hxy
  apply (ConcreteCategory.bijective_of_isIso (t.hom.app W)).injective
  exact (pullbackFiberIso_hom_fundamentalGroupHom_apply a xi x W z).trans
    ((congrArg (fun u : π₁ᵉᵗ(xi ≫ a) => u.asIso.hom.app W (t.hom.app W z)) hmap).trans
      (pullbackFiberIso_hom_fundamentalGroupHom_apply a xi y W z).symm)

end ArithmeticKernel

section OriginalLang

variable (k : Type u) [Field k] [Fintype k]
  (A : Scheme.{u}) [A.Over (Spec (.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (.of k))) (hc : G.IsCommutative)
  (hA : AbelianSchemePropertyBundle k (A ↘ Spec (.of k)))

/-- The actual Lang map over the original field as a finite étale object. -/
def originalLangCover : FiniteEtale A :=
  @FiniteEtale.mk A A (originalFiniteFieldLangMap k A G hc).val (by
    have h := originalFiniteFieldLangMap_finite_etale k A G hc (AlgebraicClosure k) hA
    exact { toIsFinite := h.1, toEtale := h.2 })

variable (κ Ω : Type u) [Field κ] [Algebra k κ] [IsSepClosure k κ]
  [Field Ω] [IsSepClosed Ω] [Algebra k Ω] [Algebra κ Ω] [IsScalarTower k κ Ω]
  {C : Scheme.{u}} (c : C ⟶ Spec (.of k)) (a : SchemeHomOver c (A ↘ Spec (CommRingCat.of k)))
  (xi : SchemeHomOver (Spec.algebraMap k Ω) c)

/-- The full native action on the original Lang pullback factors through
the original first arithmetic quotient, also at geometric generic points. -/
theorem originalLangPullback_smul_eq_of_firstMk_eq
    (x y : π₁ᵉᵗ(xi.val))
    (hxy : arithmeticFirstMk (arithmeticFundamentalGroupHom k κ c xi.val).toMonoidHom.ker x =
      arithmeticFirstMk (arithmeticFundamentalGroupHom k κ c xi.val).toMonoidHom.ker y)
    (z : (fiber xi.val).obj
      ((FiniteEtale.pullback a.val).obj (originalLangCover k A G hc hA))) : x • z = y • z := by
  have : IsProper (A ↘ Spec (CommRingCat.of k)) := hA.proper
  have : Smooth (A ↘ Spec (CommRingCat.of k)) := hA.smooth
  have : GeometricallyIntegral (A ↘ Spec (CommRingCat.of k)) := hA.geometricallyIntegral
  have : GeometricallyConnected (A ↘ Spec (CommRingCat.of k)) :=
    GeometricallyIrreducible.geometricallyConnected (A ↘ Spec (CommRingCat.of k))
  let b := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  have hbase : (xi.val ≫ a.val) ≫ (A ↘ Spec (CommRingCat.of k)) = Spec.algebraMap k Ω :=
    (Category.assoc _ _ _).trans ((congrArg (xi.val ≫ ·) a.property).trans xi.property)
  let eta : Spec (.of Ω) ⟶ pullback b (A ↘ Spec (CommRingCat.of k)) := pullback.lift
    (Spec.algebraMap κ Ω) (xi.val ≫ a.val)
      ((fieldGeometricPoint_comp k κ Ω).trans hbase.symm)
  have hxy' : arithmeticFirstMk
      (arithmeticFundamentalGroupHom k κ (a.val ≫ (A ↘ Spec (CommRingCat.of k)))
        xi.val).toMonoidHom.ker x =
      arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ (a.val ≫ (A ↘ Spec (CommRingCat.of k)))
          xi.val).toMonoidHom.ker y := by
    have ha : a.val ≫ (A ↘ Spec (CommRingCat.of k)) = c := a.property
    exact Eq.mpr (congrArg
      (fun d : C ⟶ Spec (CommRingCat.of k) =>
        arithmeticFirstMk (arithmeticFundamentalGroupHom k κ d xi.val).toMonoidHom.ker x =
          arithmeticFirstMk (arithmeticFundamentalGroupHom k κ d xi.val).toMonoidHom.ker y)
      ha) hxy
  exact pullback_smul_eq_of_firstMk_eq k κ G a.val xi.val eta
    (pullback.lift_snd _ _ _) x y hxy' (originalLangCover k A G hc hA) z

end OriginalLang

end GoodReductionJacobian.RelativeGroupLaw
