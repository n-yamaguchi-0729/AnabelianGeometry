/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CartierGeneratorOrder
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitPrincipalDivisor
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorCoefficientLocality
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Finsupp.Ext

/-!
# The actual Cartier section has the original multiplicity divisor

An original quotient section can be compared with a rational representative
on a neighborhood of each closed point. The actual global divisor
isomorphism and residue-fiber naturality preserve that local equality.
The proved principal-divisor formula then computes its coefficient. For
an actual Cartier equation this is the original stalk-ideal multiplicity,
including all nonreduced multiplicities.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- Local equality in the original quotient implies equality of the
original divisor coordinate at a point of that residue fiber. -/
theorem genericUnitDivisorH0Equiv_eq_of_section_eq
    (a b : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0)
    (w : Place K F) (V : M.C.Etale)
    (y : closedPointResidueFiber M.C (M.placeEquiv.symm w) V) :
    let Q := etaleGenericUnitQuotient M.C
    let hT : IsTerminal (Scheme.Etale.mk (𝟙 M.C)) := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) M.C
    Q.obj.map (hT.from V).op (Sheaf.H.equiv₀.{u} Q hT a) =
      Q.obj.map (hT.from V).op (Sheaf.H.equiv₀.{u} Q hT b) →
        M.genericUnitDivisorH0Equiv a w = M.genericUnitDivisorH0Equiv b w := by
  intro Q hT h
  let D := closedPointDivisorSheaf M.C
  let E := smoothCurveClosedPointDivisorGenericUnitIso M.toBase
  let T : M.C.Etale := Scheme.Etale.mk (𝟙 M.C)
  let m := hT.from V
  let sa := Sheaf.H.equiv₀.{u} Q hT a
  let sb := Sheaf.H.equiv₀.{u} Q hT b
  change M.divisorSheafH0Equiv (Sheaf.H.map E.inv 0 a) w =
    M.divisorSheafH0Equiv (Sheaf.H.map E.inv 0 b) w
  have ha₀ := Sheaf.H.equiv₀_naturality.{u}
    (J := M.C.smallEtaleTopology) (F := Q) (G := D) hT E.inv a
  have hb₀ := Sheaf.H.equiv₀_naturality.{u}
    (J := M.C.smallEtaleTopology) (F := Q) (G := D) hT E.inv b
  have ha := ConcreteCategory.congr_hom (E.inv.hom.naturality m.op) sa
  have hb := ConcreteCategory.congr_hom (E.inv.hom.naturality m.op) sb
  change E.inv.hom.app (op V) (Q.obj.map m.op sa) =
    D.obj.map m.op (E.inv.hom.app (op T) sa) at ha
  change E.inv.hom.app (op V) (Q.obj.map m.op sb) =
    D.obj.map m.op (E.inv.hom.app (op T) sb) at hb
  have hab := congrArg (fun t : Q.obj.obj (op V) => E.inv.hom.app (op V) t) h
  have hrestricted := ha.symm.trans (hab.trans hb)
  have hlocal := closedPointDivisorGlobalCoefficient_eq_of_restriction_eq
    M.C (M.placeEquiv.symm w) V y
    (E.inv.hom.app (op T) sa) (E.inv.hom.app (op T) sb) hrestricted
  have hca := congrArg (closedPointDivisorGlobalCoefficient M.C (M.placeEquiv.symm w)) ha₀
  have hcb := congrArg (closedPointDivisorGlobalCoefficient M.C (M.placeEquiv.symm w)) hb₀
  have hnative := hca.symm.trans (hlocal.trans hcb)
  exact (M.divisorSheafH0Equiv_apply (Sheaf.H.map E.inv 0 a) w).trans
    (hnative.trans (M.divisorSheafH0Equiv_apply (Sheaf.H.map E.inv 0 b) w).symm)

/-- An actual local equation in the original quotient has its original
place order as coefficient under the actual global divisor isomorphism. -/
theorem genericUnitDivisorH0Equiv_of_local_equation
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0)
    (w : Place K F) (U : M.C.Opens) [Nonempty U]
    (hx : (M.placeEquiv.symm w).1 ∈ U)
    (f : Γ(M.C, U)) (hf : f ≠ 0) :
    let Q := etaleGenericUnitQuotient M.C
    let hT : IsTerminal (Scheme.Etale.mk (𝟙 M.C)) := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) M.C
    Q.obj.map (hT.from ((zariskiToEtale M.C).obj U)).op
        (Sheaf.H.equiv₀.{u} Q hT a) = openSectionGenericUnitQuotient M.C U f hf →
      M.genericUnitDivisorH0Equiv a w =
        w.ord (M.ffEquiv.symm (M.C.germToFunctionField U f)) := by
  intro Q hT hs
  let G := (etaleAbelianPushforward (M.C.fromSpecStalk (genericPoint M.C))).obj
    (etaleMultiplicativeGroupSheaf (Spec (.of M.C.functionField)))
  let V := (zariskiToEtale M.C).obj U
  let T : M.C.Etale := Scheme.Etale.mk (𝟙 M.C)
  let m := hT.from V
  let π : G ⟶ Q := (etaleGenericUnitShortComplex M.C).g
  let r := Additive.ofMul (openSectionRationalUnit M.C U f hf)
  let b : Sheaf.H.{u} G 0 := (genericPointUnitsH0Equiv M.C).symm r
  have hb : genericPointUnitsH0Equiv M.C b = r :=
    (genericPointUnitsH0Equiv M.C).apply_symm_apply r
  have hπ : Q.obj.map m.op
      (Sheaf.H.equiv₀.{u} Q hT (Sheaf.H.map π 0 b)) =
        openSectionGenericUnitQuotient M.C U f hf := by
    have hnat := Sheaf.H.equiv₀_naturality.{u}
      (J := M.C.smallEtaleTopology) (F := G) (G := Q) hT π b
    have hmap := congrArg (fun t : Q.obj.obj (op T) => Q.obj.map m.op t) hnat
    have hn := ConcreteCategory.congr_hom (π.hom.naturality m.op)
      (Sheaf.H.equiv₀.{u} G hT b)
    change π.hom.app (op V)
        (G.obj.map m.op (Sheaf.H.equiv₀.{u} G hT b)) =
      Q.obj.map m.op (π.hom.app (op T) (Sheaf.H.equiv₀.{u} G hT b)) at hn
    have hsection := (genericPointUnitsH0Equiv_section M.C b V).trans
      (congrArg (rationalUnitDirectImageSection
        (M.C.fromSpecStalk (genericPoint M.C)) V) hb)
    have hquotient := congrArg (fun t : G.obj.obj (op V) => π.hom.app (op V) t) hsection
    have hlocal : π.hom.app (op V)
        (rationalUnitDirectImageSection (M.C.fromSpecStalk (genericPoint M.C)) V r) =
        openSectionGenericUnitQuotient M.C U f hf := by rfl
    exact hmap.symm.trans (hn.symm.trans (hquotient.trans hlocal))
  have hcoord : M.genericUnitDivisorH0Equiv a w =
      M.genericUnitsDivisorH0Map b w :=
    M.genericUnitDivisorH0Equiv_eq_of_section_eq a (Sheaf.H.map π 0 b) w V
      ⟨⟨(M.placeEquiv.symm w).1, hx⟩, rfl⟩ (hs.trans hπ.symm)
  rw [hcoord, M.genericUnitsDivisorH0Map_apply]
  change w.ord (M.ffEquiv.symm ((genericPointUnitsH0Equiv M.C b).toMul :
    M.C.functionField)) = _
  rw [hb]
  rfl

/-- The actual native quotient class of an invertible ideal has its
actual stalk-ideal multiplicity at every original place. -/
theorem genericUnitDivisorH0Equiv_cartier_apply
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) (w : Place K F) :
    M.genericUnitDivisorH0Equiv
        (effectiveCartierGenericUnitH0 ⟨I, hI.isEffectiveCartier⟩) w =
      M.cartierMultiplicity I hI (M.placeEquiv.symm w) := by
  let x := M.placeEquiv.symm w
  obtain ⟨U, hx, f, hf, hIf⟩ := hI.isEffectiveCartier x.1
  have : Nonempty U.1 := ⟨⟨x.1, hx⟩⟩
  have hf0 : f ≠ 0 := by
    intro hz
    apply (zero_ne_one : (0 : Γ(M.C, U.1)) ≠ 1)
    exact hf.left (by simp only [hz, zero_mul])
  have hc := M.genericUnitDivisorH0Equiv_of_local_equation
    (effectiveCartierGenericUnitH0 ⟨I, hI.isEffectiveCartier⟩) w U.1 hx f hf0
    (effectiveCartierGenericUnitH0_section ⟨I, hI.isEffectiveCartier⟩ U f hf0 hIf)
  have ho := M.ord_affineGenerator I hI U.1 U.2 f hIf x hx
  have hxw : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
  rw [hxw] at ho
  exact hc.trans ho

/-- The original Cartier multiplicity modulus is exactly the divisor of
the actual native quotient section, with every original coefficient. -/
theorem genericUnitDivisorH0Equiv_cartier
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    M.genericUnitDivisorH0Equiv
        (effectiveCartierGenericUnitH0 ⟨I, hI.isEffectiveCartier⟩) =
      (M.cartierModulus I hI).toDivisor := by
  ext w
  exact M.genericUnitDivisorH0Equiv_cartier_apply I hI w

end AlgebraicCurve.CurveModel
