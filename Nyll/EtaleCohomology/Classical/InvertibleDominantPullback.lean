/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalFrames
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalPullbackFrames
public import Nyll.EtaleCohomology.Classical.CartierCycleModuleIsomorphism
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitSections
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.RationalUnitSquarePullback
public import Nyll.EtaleCohomology.Classical.UnitQuotientFunctoriality
public import Nyll.EtaleCohomology.Classical.UnitQuotientPullbackSections
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Native invertible-module classes under dominant pullback

The canonical map of the original function fields supplies an actual
commuting generic-point square. Its original unit-quotient map takes each
frame to its pulled rational value. Actual pulled frames differ from those
values by one global rational unit, killed by the original boundary. Thus
the same native H¹(Gm) class commutes with arbitrary dominant pullback.

The frame comparison argument is generalized from
`InvertibleFiniteEtalePullback`; that finite-cover theorem uses this result.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open Scheme.Modules EtaleFundamentalGroups

namespace EtaleCohomology

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) (hf : DenseRange f)

/-- The original generic-unit H⁰ map induced by the actual function-field
square of a dominant morphism. No cartesian-square hypothesis is needed. -/
def dominantGenericUnitH0Pullback :
    Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
  etaleUnitQuotientCohomologySquareMap (X.fromSpecStalk (genericPoint X)) f
    (Y.fromSpecStalk (genericPoint Y))
    (Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)))
    (Spec_functionFieldMap_fromSpecStalk f hf) 0

/-- The original generic-unit boundary is natural for the canonical
function-field square of an arbitrary dominant morphism. -/
theorem dominantGenericUnitH0Pullback_boundary
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    etaleMultiplicativeGroupCohomologyPullback f 1
        (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl a) =
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact Y) 0 1 rfl
        (dominantGenericUnitH0Pullback f hf a) := by
  have : Mono (etaleMultiplicativeGroupToPushforward
      (X.fromSpecStalk (genericPoint X))) := etaleMultiplicativeGroupToGenericPoint_mono X
  have : Mono (etaleMultiplicativeGroupToPushforward
      (Y.fromSpecStalk (genericPoint Y))) := etaleMultiplicativeGroupToGenericPoint_mono Y
  exact etaleUnitBoundary_zero_pullback_square (X.fromSpecStalk (genericPoint X)) f
    (Y.fromSpecStalk (genericPoint Y))
    (Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)))
    (Spec_functionFieldMap_fromSpecStalk f hf) a

private theorem dominantGenericUnitH0Pullback_frameSection
    {L : X.Modules} (hL : IsInvertible L)
    (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (hs : IsFrameOn s U) :
    let hY := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    (etaleGenericUnitQuotient Y).obj.map
        (hY.from ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))).op
          (Sheaf.H.equiv₀ (etaleGenericUnitQuotient Y) hY
            (dominantGenericUnitH0Pullback f hf (invertibleModuleGenericUnitH0 hL))) =
      genericPointRationalUnitQuotientSection Y ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))
        (Additive.ofMul (Units.map (f.functionFieldMap hf).toMonoidHom
          (hL.frameRationalUnit U s hs))) := by
  intro hY
  let V := (zariskiToEtale X).obj U
  let W := (zariskiToEtale Y).obj (f ⁻¹ᵁ U)
  let l : W.left ⟶ V.left := f.resLE U (f ⁻¹ᵁ U) le_rfl
  have hl : l ≫ V.hom = W.hom ≫ f := f.resLE_comp_ι le_rfl
  let i := X.fromSpecStalk (genericPoint X)
  let j := Y.fromSpecStalk (genericPoint Y)
  let φ := f.functionFieldMap hf
  let h := Spec_functionFieldMap_fromSpecStalk f hf
  let a := Additive.ofMul (hL.frameRationalUnit U s hs)
  have hsection := etaleUnitQuotientCohomologySquareMap_zero_local_lift
    i f j (Spec.map (CommRingCat.ofHom φ)) h (A := V) (B := W) l hl
    (invertibleModuleGenericUnitH0 hL) (rationalUnitDirectImageSection i V a)
    (invertibleModuleGenericUnitH0_section hL U s hs).symm
  have hr := rationalUnitDirectImageSection_square f i j φ h (V := V) (W := W) l hl a
  exact hsection.trans (congrArg ((etaleGenericUnitShortComplex Y).g.hom.app (op W)) hr)

/-- The native quotient representatives for an actual pulled-back
invertible module differ by the image of one actual global rational unit. -/
theorem invertibleModuleGenericUnitH0_dominantPullback
    {L : X.Modules} (hL : IsInvertible L) :
    ∃ a : Additive Y.functionFieldˣ,
      invertibleModuleGenericUnitH0 (hL.pullback f) =
        Sheaf.H.map
          (show (etaleGenericUnitShortComplex Y).X₂ ⟶ etaleGenericUnitQuotient Y from
            (etaleGenericUnitShortComplex Y).g) 0
          ((genericPointUnitsH0Equiv Y).symm a) +
            dominantGenericUnitH0Pullback f hf (invertibleModuleGenericUnitH0 hL) := by
  obtain ⟨a, ha⟩ := hL.exists_unit_pullbackFrameRationalUnit_eq_mul f hf
  refine ⟨Additive.ofMul a, ?_⟩
  apply etaleAbelianH0_ext_zariski Y (etaleGenericUnitQuotient Y)
  intro y
  obtain ⟨U, s, hyU, hs⟩ := hL.exists_frameSection (f y)
  have : Nonempty U := ⟨⟨f y, hyU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨y, hyU⟩⟩
  refine ⟨f ⁻¹ᵁ U, hyU, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y
  let ev : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 →+
      (etaleGenericUnitQuotient Y).obj.obj (op ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))) :=
    ((etaleGenericUnitQuotient Y).obj.map
      (hT.from ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))).op).hom.comp
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient Y) hT).toAddMonoidHom
  let m : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
    Sheaf.H.map (etaleGenericUnitShortComplex Y).g 0
      ((genericPointUnitsH0Equiv Y).symm (Additive.ofMul a))
  let v : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
    dominantGenericUnitH0Pullback f hf (invertibleModuleGenericUnitH0 hL)
  change ev (invertibleModuleGenericUnitH0 (hL.pullback f)) = ev (m + v)
  have hsec : ev (invertibleModuleGenericUnitH0 (hL.pullback f)) =
      invertibleFrameGenericUnitQuotient (hL.pullback f) (f ⁻¹ᵁ U)
        (pullbackLocalSection f s) (hs.pullbackLocalSection f) :=
    invertibleModuleGenericUnitH0_section (hL.pullback f) (f ⁻¹ᵁ U)
      (pullbackLocalSection f s) (hs.pullbackLocalSection f)
  have himage : ev m = genericPointRationalUnitQuotientSection Y
      ((zariskiToEtale Y).obj (f ⁻¹ᵁ U)) (Additive.ofMul a) :=
    genericPointUnitQuotientH0_section Y (Additive.ofMul a)
      ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))
  have hsource : ev v = genericPointRationalUnitQuotientSection Y
      ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))
        (Additive.ofMul (Units.map (f.functionFieldMap hf).toMonoidHom
          (hL.frameRationalUnit U s hs))) :=
    dominantGenericUnitH0Pullback_frameSection f hf hL U s hs
  let q := genericPointRationalUnitQuotientHom Y ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))
  have hq : invertibleFrameGenericUnitQuotient (hL.pullback f) (f ⁻¹ᵁ U)
        (pullbackLocalSection f s) (hs.pullbackLocalSection f) =
      q (Additive.ofMul a) + q (Additive.ofMul
        (Units.map (f.functionFieldMap hf).toMonoidHom (hL.frameRationalUnit U s hs))) :=
    (congrArg (fun z : Y.functionFieldˣ => q (Additive.ofMul z)) (ha U s hs)).trans
      (q.map_add _ _)
  exact hsec.trans
    (hq.trans
      ((congrArg₂
        (fun z w : (etaleGenericUnitQuotient Y).obj.obj
          (op ((zariskiToEtale Y).obj (f ⁻¹ᵁ U))) => z + w)
        himage.symm hsource.symm).trans (ev.map_add m v).symm))

include hf in
/-- The original native H¹(Gm) class of an actual invertible module
commutes with every dominant morphism of integral schemes. -/
theorem invertibleModuleMultiplicativeGroupH1_dominantPullback
    {L : X.Modules} (hL : IsInvertible L) :
    etaleMultiplicativeGroupCohomologyPullback f 1
        (invertibleModuleMultiplicativeGroupH1 hL) =
      invertibleModuleMultiplicativeGroupH1 (hL.pullback f) := by
  obtain ⟨a, ha⟩ := invertibleModuleGenericUnitH0_dominantPullback f hf hL
  let δX : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
  let δY : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact Y) 0 1 rfl
  let P := etaleMultiplicativeGroupCohomologyPullback f 1
  let m : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
    Sheaf.H.map (etaleGenericUnitShortComplex Y).g 0 ((genericPointUnitsH0Equiv Y).symm a)
  let v : Sheaf.H.{u} (etaleGenericUnitQuotient Y) 0 :=
    dominantGenericUnitH0Pullback f hf (invertibleModuleGenericUnitH0 hL)
  have hz : δY m = 0 := genericPointUnitH0_boundary_zero a
  have hb : P (δX (invertibleModuleGenericUnitH0 hL)) = δY v :=
    dominantGenericUnitH0Pullback_boundary f hf (invertibleModuleGenericUnitH0 hL)
  have he : δY (invertibleModuleGenericUnitH0 (hL.pullback f)) =
      P (δX (invertibleModuleGenericUnitH0 hL)) :=
    (congrArg δY ha).trans
      ((δY.map_add m v).trans
        ((congrArg
          (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 => z + δY v) hz).trans
            ((zero_add (δY v)).trans hb.symm)))
  change P (-δX (invertibleModuleGenericUnitH0 hL)) =
    -δY (invertibleModuleGenericUnitH0 (hL.pullback f))
  exact (P.map_neg _).trans
    (congrArg (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 => -z) he.symm)

end EtaleCohomology
