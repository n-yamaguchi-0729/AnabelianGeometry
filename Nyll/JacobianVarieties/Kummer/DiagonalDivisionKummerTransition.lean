/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullbackCocycle
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Projective.InvertibleTensorPow
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleCycleTensor
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitSections
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.ProperKummerH1
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionTransition
public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Native Kummer classes of the actual division transition families

On a proper integral test product, the original Kummer inclusion uniquely
lifts each actual torsion transition bundle to H¹(μn). The tensor-product
comparison on triples becomes an additive identity in this original H¹.
At prime-power exponents the same class is expressed in the original
finite cyclic coefficients through the existing coherent-root comparison.

For the actual division overlap, properness and integrality of each
component product are supplied below. No connectedness of the division
cover is imposed. The result is cohomology on each actual component
product; it is not yet a Čech transgression or a decomposition of H².
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of K)} {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  {T : Scheme.{u}} {t : T ⟶ Spec (.of K)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)

section IntegralProduct

variable {W : Scheme.{u}} {w : W ⟶ Spec (.of K)}
  [IsIntegral (pullback c w)]

local notation "s" => h.divisionStructure a n
local notation "Y" => pullback c w
local notation "d" => pullback.snd c w ≫ w

omit [IsAlgClosed K] in
/-- The specified pulled-back division root gives the actual
native H¹ lift of the original classified family through multiplication
by n. Both classes use the same whole test product. -/
theorem divisionRootPullbackH1_nsmul (x : SchemeHomOver w s) :
    n • invertibleModuleMultiplicativeGroupH1
        ((h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c x)) =
      invertibleModuleMultiplicativeGroupH1
        (((h.poincare.pullbackAlong a).isInvertible.pullback
          (h.divisionProductProjection a n)).pullback (baseChangeSnd c x)) := by
  let j := baseChangeSnd c x
  let hL := (h.divisionRootFamily a n).isInvertible.pullback j
  let hM := ((h.poincare.pullbackAlong a).isInvertible.pullback
    (h.divisionProductProjection a n)).pullback j
  obtain ⟨e⟩ := h.divisionRootFamily_tensorPowIso a n
  have hclass := invertibleModuleMultiplicativeGroupH1_iso hM (hL.tensorPow n)
    ((Scheme.Modules.pullback j).mapIso e ≪≫
      Scheme.Modules.pullbackTensorPowIso j (h.divisionRootFamily a n).L n)
  rw [invertibleModuleMultiplicativeGroupH1_tensorPow] at hclass
  exact hclass.symm

omit [IsAlgClosed K] in
/-- The original fixed generic-unit representatives retain the actual
root comparison: the second root differs from the transition tensored
with the first root by the image of one actual global rational unit. -/
theorem divisionTransitionGenericUnitH0_rootComparison
    (x y : SchemeHomOver w s) :
    ∃ u : Additive (Y).functionFieldˣ,
      let m : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
        Sheaf.H.map.{u} (etaleGenericUnitShortComplex Y).g 0
          ((genericPointUnitsH0Equiv Y).symm u)
      invertibleModuleGenericUnitH0
          ((h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c y)) =
        m + (invertibleModuleGenericUnitH0
              (h.divisionTransitionFamily a n x y).isInvertible +
            invertibleModuleGenericUnitH0
              ((h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c x))) := by
  let hT := (h.divisionTransitionFamily a n x y).isInvertible
  let hX := (h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c x)
  let hY := (h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c y)
  obtain ⟨e⟩ := h.divisionTransitionFamily_tensor_rootIso a n x y
  obtain ⟨u, hu⟩ := invertibleModuleGenericUnitH0_iso (hT.tensor hX) hY e
  obtain ⟨v, hv⟩ := invertibleModuleGenericUnitH0_tensor hT hX
  refine ⟨u + v, ?_⟩
  intro m
  let correction : Additive (Y).functionFieldˣ →+
      Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
    (Sheaf.H.map.{u} (etaleGenericUnitShortComplex Y).g 0).comp
      (genericPointUnitsH0Equiv Y).symm.toAddMonoidHom
  let mu : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 := correction u
  let mv : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 := correction v
  let z := invertibleModuleGenericUnitH0 hT + invertibleModuleGenericUnitH0 hX
  have hu' : invertibleModuleGenericUnitH0 hY =
      mu + invertibleModuleGenericUnitH0 (hT.tensor hX) := hu
  have hv' : invertibleModuleGenericUnitH0 (hT.tensor hX) = mv + z := hv
  have hm : m = mu + mv := correction.map_add u v
  exact hu'.trans
    ((congrArg (fun t : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 => mu + t) hv').trans
      ((add_assoc mu mv z).symm.trans
        (congrArg (fun t : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 => t + z) hm.symm)))

omit [IsAlgClosed K] in
/-- The actual transition class is exactly the difference of the two
actual pulled-back root classes. The rational correction in the fixed
generic-unit representatives is killed by the original boundary. -/
theorem divisionTransitionH1_eq_rootDifference (x y : SchemeHomOver w s) :
    invertibleModuleMultiplicativeGroupH1
        (h.divisionTransitionFamily a n x y).isInvertible =
      invertibleModuleMultiplicativeGroupH1
          ((h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c y)) -
        invertibleModuleMultiplicativeGroupH1
          ((h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c x)) := by
  let hT := (h.divisionTransitionFamily a n x y).isInvertible
  let hX := (h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c x)
  let hY := (h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd c y)
  obtain ⟨e⟩ := h.divisionTransitionFamily_tensor_rootIso a n x y
  have hclass := invertibleModuleMultiplicativeGroupH1_iso (hT.tensor hX) hY e
  exact (eq_sub_iff_add_eq).2
    ((invertibleModuleMultiplicativeGroupH1_tensor hT hX).symm.trans hclass)

omit [IsAlgClosed K] in
/-- The original H¹(Gm) class of the actual transition bundle is
killed by the original exponent, using its actual tensor-power root. -/
theorem divisionTransitionH1_nsmul_eq_zero (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    n • invertibleModuleMultiplicativeGroupH1
      (h.divisionTransitionFamily a n x y).isInvertible = 0 := by
  obtain ⟨e⟩ := h.divisionTransitionFamily_tensorPowIso_unit a n x y hxy
  have hclass := invertibleModuleMultiplicativeGroupH1_iso
    ((h.divisionTransitionFamily a n x y).isInvertible.tensorPow n)
    (Scheme.Modules.isInvertible_unit Y) e
  rw [invertibleModuleMultiplicativeGroupH1_tensorPow,
    invertibleModuleMultiplicativeGroupH1_unit] at hclass
  exact hclass

omit [IsAlgClosed K] in
/-- The original transition bundle, as an element of the original
power kernel in H¹(Gm). -/
def divisionTransitionPowerKernel (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) n).ker :=
  ⟨invertibleModuleMultiplicativeGroupH1
      (h.divisionTransitionFamily a n x y).isInvertible,
    h.divisionTransitionH1_nsmul_eq_zero a n x y hxy⟩

omit [IsAlgClosed K] in
/-- The original tensor cocycle is an additive cocycle in the
original H¹(Gm) power kernel. -/
theorem divisionTransitionPowerKernel_cocycle
    (x y z : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y)
    (hyz : postComp (h.divisionBaseMap a n) y =
      postComp (h.divisionBaseMap a n) z) :
    h.divisionTransitionPowerKernel a n y z hyz +
        h.divisionTransitionPowerKernel a n x y hxy =
      h.divisionTransitionPowerKernel a n x z (hxy.trans hyz) := by
  apply Subtype.ext
  change invertibleModuleMultiplicativeGroupH1
      (h.divisionTransitionFamily a n y z).isInvertible +
    invertibleModuleMultiplicativeGroupH1
      (h.divisionTransitionFamily a n x y).isInvertible =
    invertibleModuleMultiplicativeGroupH1
      (h.divisionTransitionFamily a n x z).isInvertible
  obtain ⟨e⟩ := h.divisionTransitionFamily_tensorIso a n x y z
  exact (invertibleModuleMultiplicativeGroupH1_tensor
    (h.divisionTransitionFamily a n y z).isInvertible
    (h.divisionTransitionFamily a n x y).isInvertible).symm.trans
      (invertibleModuleMultiplicativeGroupH1_iso
        ((h.divisionTransitionFamily a n y z).isInvertible.tensor
          (h.divisionTransitionFamily a n x y).isInvertible)
        (h.divisionTransitionFamily a n x z).isInvertible e)

variable [IsProper c] [IsProper w]

/-- The unique class in original H¹(μn) whose original Kummer image
is the actual transition bundle. Properness supplies uniqueness. -/
def divisionTransitionKummerClass (hn : 0 < n) (hnK : IsUnit (n : K))
    (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) 1 :=
  (properIntegralKummerH1EquivPowerKernel d hn hnK).symm
    (h.divisionTransitionPowerKernel a n x y hxy)

/-- The comparison uses the original coefficient inclusion, not
a newly defined map from cohomology to bundles. -/
theorem divisionTransitionKummerClass_inclusion (hn : 0 < n) (hnK : IsUnit (n : K))
    (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    etaleRootsOfUnityH1ToMultiplicativeGroup Y n
        (h.divisionTransitionKummerClass a n hn hnK x y hxy) =
      invertibleModuleMultiplicativeGroupH1
        (h.divisionTransitionFamily a n x y).isInvertible :=
  congrArg Subtype.val
    ((properIntegralKummerH1EquivPowerKernel d hn hnK).apply_symm_apply
      (h.divisionTransitionPowerKernel a n x y hxy))

/-- The original native Kummer classes satisfy the cocycle identity
by the actual whole-product tensor comparison. -/
theorem divisionTransitionKummerClass_cocycle (hn : 0 < n) (hnK : IsUnit (n : K))
    (x y z : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y)
    (hyz : postComp (h.divisionBaseMap a n) y =
      postComp (h.divisionBaseMap a n) z) :
    h.divisionTransitionKummerClass a n hn hnK y z hyz +
        h.divisionTransitionKummerClass a n hn hnK x y hxy =
      h.divisionTransitionKummerClass a n hn hnK x z (hxy.trans hyz) := by
  change (properIntegralKummerH1EquivPowerKernel d hn hnK).symm _ +
    (properIntegralKummerH1EquivPowerKernel d hn hnK).symm _ =
      (properIntegralKummerH1EquivPowerKernel d hn hnK).symm _
  rw [← map_add, h.divisionTransitionPowerKernel_cocycle a n x y z hxy hyz]

end IntegralProduct

section FiniteCoefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (r : ℕ)
  {W : Scheme.{u}} {w : W ⟶ Spec (.of K)}
  [IsIntegral (pullback c w)] [IsProper c] [IsProper w]

local notation "N" => ℓ ^ (r + 1)
local notation "s" => h.divisionStructure a N
local notation "Y" => pullback c w
local notation "d" => pullback.snd c w ≫ w

/-- The same original Kummer transition in the existing finite
cyclic coefficient group and its original coherent-root comparison. -/
def divisionTransitionFiniteClass (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a N) x =
      postComp (h.divisionBaseMap a N) y) : finiteLevelCohomology Y ℓ r 1 :=
  (finiteLevelKummerCohomologyEquiv d ℓ hℓ r 1).symm
    (h.divisionTransitionKummerClass a N
      (pow_pos (Nat.Prime.pos (Fact.out : ℓ.Prime)) (r + 1))
      (by simpa only [Nat.cast_pow] using IsUnit.pow (r + 1) hℓ) x y hxy)

/-- Original coefficient comparison and original Kummer inclusion
recover the actual original transition bundle class. -/
theorem divisionTransitionFiniteClass_inclusion (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a N) x =
      postComp (h.divisionBaseMap a N) y) :
    etaleRootsOfUnityH1ToMultiplicativeGroup Y N
        (finiteLevelKummerCohomologyEquiv d ℓ hℓ r 1
          (h.divisionTransitionFiniteClass a ℓ hℓ r x y hxy)) =
      invertibleModuleMultiplicativeGroupH1
        (h.divisionTransitionFamily a N x y).isInvertible := by
  rw [divisionTransitionFiniteClass, AddEquiv.apply_symm_apply]
  exact h.divisionTransitionKummerClass_inclusion a N
    (pow_pos (Nat.Prime.pos (Fact.out : ℓ.Prime)) (r + 1))
    (by simpa only [Nat.cast_pow] using IsUnit.pow (r + 1) hℓ) x y hxy

/-- Through the original finite coefficient comparison and Kummer
inclusion, the transition is precisely the difference of the two
specified division-root classes, before any transgression is formed. -/
theorem divisionTransitionFiniteClass_eq_rootDifference
    (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a N) x =
      postComp (h.divisionBaseMap a N) y) :
    etaleRootsOfUnityH1ToMultiplicativeGroup Y N
        (finiteLevelKummerCohomologyEquiv d ℓ hℓ r 1
          (h.divisionTransitionFiniteClass a ℓ hℓ r x y hxy)) =
      invertibleModuleMultiplicativeGroupH1
          ((h.divisionRootFamily a N).isInvertible.pullback (baseChangeSnd c y)) -
        invertibleModuleMultiplicativeGroupH1
          ((h.divisionRootFamily a N).isInvertible.pullback (baseChangeSnd c x)) :=
  (h.divisionTransitionFiniteClass_inclusion a ℓ hℓ r x y hxy).trans
    (h.divisionTransitionH1_eq_rootDifference a N x y)

/-- The original finite transition classes satisfy the additive
cocycle identity in the original finite cohomology group. -/
theorem divisionTransitionFiniteClass_cocycle (x y z : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a N) x =
      postComp (h.divisionBaseMap a N) y)
    (hyz : postComp (h.divisionBaseMap a N) y =
      postComp (h.divisionBaseMap a N) z) :
    h.divisionTransitionFiniteClass a ℓ hℓ r y z hyz +
        h.divisionTransitionFiniteClass a ℓ hℓ r x y hxy =
      h.divisionTransitionFiniteClass a ℓ hℓ r x z (hxy.trans hyz) := by
  unfold divisionTransitionFiniteClass
  rw [← map_add, h.divisionTransitionKummerClass_cocycle a N
    (pow_pos (Nat.Prime.pos (Fact.out : ℓ.Prime)) (r + 1))
    (by simpa only [Nat.cast_pow] using IsUnit.pow (r + 1) hℓ) x y z hxy hyz]

end FiniteCoefficients

section ActualOverlapComponents

variable [IsIntegral C] [IsProper c] [Smooth c]
  [IsProper t] [Smooth D.toBase] [IsProper D.toBase]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (r : ℕ)

local notation "N" => ℓ ^ (r + 1)
local notation "O" => h.divisionOverlap a N
local notation "o" => h.divisionOverlapStructure a N

include hℓ

omit [IsAlgClosed K] [IsIntegral C] [IsProper c] [Smooth c] [Fact ℓ.Prime] in
private theorem divisionOverlap_isProper : IsProper o := by
  have : IsFinite (h.divisionProjection a N) := h.divisionProjection_finite a N
    (by simpa only [Nat.cast_pow] using hℓ.pow (r + 1))
  change IsProper
    (pullback.fst (h.divisionProjection a N) (h.divisionProjection a N) ≫
      (h.divisionProjection a N ≫ t))
  infer_instance

omit [IsProper c] [Fact ℓ.Prime] in
/-- The actual component product of the division overlap supplies
its own properness and integrality, before any native Kummer comparison. -/
theorem divisionOverlapComponentProduct_geometry (Z : irreducibleComponents O) :
    IsIntegral (pullback c ((O).reducedIrreducibleComponentι Z.1 Z.2 ≫ o)) ∧
      IsProper ((O).reducedIrreducibleComponentι Z.1 Z.2 ≫ o) := by
  have : IsProper o := h.divisionOverlap_isProper a ℓ hℓ r
  have hi : IsProper ((O).reducedIrreducibleComponentι Z.1 Z.2 ≫ o) :=
    reducedIrreducibleComponent_isProper o Z
  exact ⟨isIntegral_pullback_of_smooth_of_isAlgClosed c
    ((O).reducedIrreducibleComponentι Z.1 Z.2 ≫ o), hi⟩

/-- The actual two overlap projections, restricted to an actual
component, give an original finite Kummer transition class on its
whole product with the curve. All comparison hypotheses are supplied
by the original proper schemes and the actual finite division cover. -/
def divisionOverlapComponentFiniteClass (Z : irreducibleComponents O) :
    finiteLevelCohomology
      (pullback c ((O).reducedIrreducibleComponentι Z.1 Z.2 ≫ o)) ℓ r 1 := by
  let i := (O).reducedIrreducibleComponentι Z.1 Z.2
  let w := i ≫ o
  let v : SchemeHomOver w o := ⟨i, rfl⟩
  let x := postComp (h.divisionOverlapFirst a N) v
  let y := postComp (h.divisionOverlapSecond a N) v
  have hgeom := h.divisionOverlapComponentProduct_geometry a ℓ hℓ r Z
  have : IsIntegral (pullback c w) := hgeom.1
  have : IsProper w := hgeom.2
  have hxy : postComp (h.divisionBaseMap a N) x =
      postComp (h.divisionBaseMap a N) y := by
    apply Subtype.ext
    change (i ≫ (h.divisionOverlapFirst a N).1) ≫ (h.divisionProjection a N) =
      (i ≫ (h.divisionOverlapSecond a N).1) ≫ (h.divisionProjection a N)
    rw [Category.assoc, Category.assoc]
    exact congrArg (i ≫ ·)
      (congrArg Subtype.val (h.divisionOverlap_projection_eq a N))
  exact h.divisionTransitionFiniteClass a ℓ hℓ r x y hxy

/-- On the actual component product, the original finite coefficient
comparison and the original Kummer inclusion recover the transition
bundle of the two original overlap projections. -/
theorem divisionOverlapComponentFiniteClass_inclusion (Z : irreducibleComponents O) :
    let w := (O).reducedIrreducibleComponentι Z.1 Z.2 ≫ o
    let _ : IsIntegral (pullback c w) :=
      (h.divisionOverlapComponentProduct_geometry a ℓ hℓ r Z).1
    let v : SchemeHomOver w o := ⟨(O).reducedIrreducibleComponentι Z.1 Z.2, rfl⟩
    etaleRootsOfUnityH1ToMultiplicativeGroup (pullback c w) N
        (finiteLevelKummerCohomologyEquiv (pullback.snd c w ≫ w) ℓ hℓ r 1
          (h.divisionOverlapComponentFiniteClass a ℓ hℓ r Z)) =
      invertibleModuleMultiplicativeGroupH1
        (h.divisionTransitionFamily a N
          (postComp (h.divisionOverlapFirst a N) v)
          (postComp (h.divisionOverlapSecond a N) v)).isInvertible := by
  intro w hY v
  have : IsProper w := (h.divisionOverlapComponentProduct_geometry a ℓ hℓ r Z).2
  unfold divisionOverlapComponentFiniteClass
  exact h.divisionTransitionFiniteClass_inclusion a ℓ hℓ r _ _ _

end ActualOverlapComponents

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
