/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CurveFiniteEtaleModel
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitAutomorphism
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitPrincipalDivisor
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GaloisCechCochains
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteDeckSections
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteProjectionSections
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward

/-!
# An actual divisor vertex on the original Galois cover

An arithmetic divisor on the function field of the original cover
defines a section of its original generic-unit quotient, hence an actual
map from the original free vertex sheaf. Its deck differences are computed
using the actual native quotient pullback. The valuations of a specified
field cochain then prove the original edge equation on the entire free
edge sheaf, retaining both that cochain and that divisor.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups EtaleCohomology

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  (M : CurveModel K F) [IsNormalIntegral M.C]
  (Y : FiniteEtale M.C) [IsGalois Y]

local notation "I" => finiteEtaleInclusion M.C
local notation "J" => M.C.smallEtaleTopology
local notation "Q" => etaleGenericUnitQuotient M.C
local notation "G" => CategoryTheory.ShortComplex.X₂ (etaleGenericUnitShortComplex M.C)
local notation "P" => presheafToSheaf J AddCommGrpCat
local notation "A" => sheafificationAdjunction J AddCommGrpCat

/-- The specified original arithmetic divisor, as a vertex map on
the actual same finite Galois cover. -/
def galoisGenericUnitDivisorVertex :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    Divisor K Y.left.functionField → ((freeAbelianSheafYoneda J).obj ((I).obj Y) ⟶ Q) := by
  intro hY algKY D
  exact (freeAbelianSheafYonedaHomEquiv J ((I).obj Y) Q).symm
    ((finiteEtaleGenericUnitQuotientSectionsEquiv Y).symm
      ((M.finiteEtaleModel Y).genericUnitDivisorH0Equiv.symm D))

/-- The vertex retains exactly its specified divisor under the
original section and native H⁰ identifications. -/
theorem galoisGenericUnitDivisorVertex_section :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    ∀ D : Divisor K Y.left.functionField,
      freeAbelianSheafYonedaHomEquiv J ((I).obj Y) Q (M.galoisGenericUnitDivisorVertex Y D) =
        (finiteEtaleGenericUnitQuotientSectionsEquiv Y).symm
          ((M.finiteEtaleModel Y).genericUnitDivisorH0Equiv.symm D) := by
  intro hY algKY D
  exact (freeAbelianSheafYonedaHomEquiv J ((I).obj Y) Q).apply_symm_apply _

/-- Actual valuations of the original field cochain prove its
quotient is the difference of the specified original divisor vertex.
Only the pointwise arithmetic divisor equation is used: the equality
on the original free edge sheaf is the conclusion. -/
theorem galoisGenericUnitDivisorVertex_boundary
    {T : M.C.Etale} (hT : IsTerminal T) (f : (I).obj Y ⟶ T) [HasPullback f f] :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    ∀ (D : Divisor K Y.left.functionField) (a : Aut Y → Additive Y.left.functionFieldˣ)
      (τ : Aut Y → Y.left.functionField ≃ₐ[K] Y.left.functionField),
      (∀ (σ : Aut Y) (z : Y.left.functionField),
        σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange z = τ σ z) →
      (∀ (σ : Aut Y) (w : Place K Y.left.functionField),
        w.ord ((a σ).toMul : Y.left.functionField) =
          (SemilinearAut.ofAlgAut (τ σ) • D - D) w) →
      (P).map (freeCechEdgeBoundaryNat (yoneda.map f)) ≫
          M.galoisGenericUnitDivisorVertex Y D =
        galoisCechEdgeCochain M.C G Y f
            (fun σ => (finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ)) ≫
          (etaleGenericUnitShortComplex M.C).g := by
  intro hY algKY D a τ hτ ha
  let N := M.finiteEtaleModel Y
  let E := finiteEtaleGenericUnitQuotientSectionsEquiv Y
  let s := E.symm (N.genericUnitDivisorH0Equiv.symm D)
  apply abelianCechEdgeHom_ext_galois M.C Q Y hT f
  intro σ
  rw [abelianCechVertexBoundary_galois_coordinate,
    galoisGenericUnitDivisorVertex_section]
  have hnat := (sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv_naturality_right
    (galoisCechEdgeCochain M.C G Y f
      (fun σ => (finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ)))
    (etaleGenericUnitShortComplex M.C).g
  have happ := congrArg
    (fun η : (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ (Q).obj =>
      η.app (op ((I).obj Y)) (FreeAbelianGroup.of (galoisCechEdge M.C Y hT f σ))) hnat
  refine Eq.trans ?_ happ.symm
  change (Q).obj.map ((I).map σ.asIso.hom).op s - s =
    (etaleGenericUnitShortComplex M.C).g.hom.app (op ((I).obj Y))
      ((((A).homEquiv _ G
        (galoisCechEdgeCochain M.C G Y f
          (fun σ => (finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ)))).app (op ((I).obj Y)))
        (FreeAbelianGroup.of (galoisCechEdge M.C Y hT f σ)))
  have hedge := galoisCechEdgeCochain_edge_coordinate M.C G Y hT f
    (fun σ => (finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ)) σ
  have hproject := congrArg
    ((etaleGenericUnitShortComplex M.C).g.hom.app (op ((I).obj Y))) hedge
  refine Eq.trans ?_ hproject.symm
  apply E.injective
  let e : N.C ≅ N.C := (FiniteEtale.forget M.C ⋙ Over.forget M.C).mapIso σ.asIso
  have hOpenDeck : IsOpenImmersion σ.asIso.hom.left :=
    inferInstanceAs (IsOpenImmersion e.hom)
  have hs := E.apply_symm_apply (N.genericUnitDivisorH0Equiv.symm D)
  have hdeck := finiteEtaleGenericUnitQuotientSectionsEquiv_deck Y σ s
  have hleft := (E.map_sub ((Q).obj.map ((I).map σ.asIso.hom).op s) s).trans
    (congrArg₂ (fun x y => x - y)
      (hdeck.trans (congrArg
        (etaleGenericUnitQuotientCohomologyPullback σ.asIso.hom.left 0) hs)) hs)
  have hp := finiteEtaleGenericUnitQuotientSectionsEquiv_projection Y
    ((finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ))
  have hright := hp.trans (congrArg
    (fun z : Additive Y.left.functionFieldˣ =>
      Sheaf.H.map (etaleGenericUnitShortComplex Y.left).g 0
        ((genericPointUnitsH0Equiv Y.left).symm z))
    ((finiteEtaleGenericUnitSectionsEquiv Y).apply_symm_apply (a σ)))
  refine hleft.trans (Eq.trans ?_ hright.symm)
  apply N.genericUnitDivisorH0Equiv.injective
  have he : ∀ z : Y.left.functionField,
      e.hom.functionFieldMap e.hom.surjective.denseRange (N.ffEquiv z) =
        N.ffEquiv (τ σ z) := hτ σ
  have hD := N.genericUnitDivisorH0Equiv.apply_symm_apply D
  have hauto := N.genericUnitDivisorH0Equiv_automorphism e (τ σ) he
    (N.genericUnitDivisorH0Equiv.symm D)
  have hdivleft := (N.genericUnitDivisorH0Equiv.map_sub
    (etaleGenericUnitQuotientCohomologyPullback e.hom 0
      (N.genericUnitDivisorH0Equiv.symm D)) (N.genericUnitDivisorH0Equiv.symm D)).trans
    (congrArg₂ (fun x y => x - y)
      (hauto.trans (congrArg (fun d => SemilinearAut.ofAlgAut (τ σ) • d) hD)) hD)
  refine hdivleft.trans ?_
  apply Finsupp.ext
  intro w
  change (SemilinearAut.ofAlgAut (τ σ) • D - D) w =
    N.genericUnitsDivisorH0Map ((genericPointUnitsH0Equiv Y.left).symm (a σ)) w
  have hw := N.genericUnitsDivisorH0Map_apply
    ((genericPointUnitsH0Equiv Y.left).symm (a σ)) w
  change N.genericUnitsDivisorH0Map ((genericPointUnitsH0Equiv Y.left).symm (a σ)) w =
    w.ord (((genericPointUnitsH0Equiv Y.left)
      ((genericPointUnitsH0Equiv Y.left).symm (a σ))).toMul : Y.left.functionField) at hw
  have hunit := congrArg
    (fun z : Additive Y.left.functionFieldˣ => w.ord (z.toMul : Y.left.functionField))
    ((genericPointUnitsH0Equiv Y.left).apply_symm_apply (a σ))
  exact (ha σ w).symm.trans (hw.trans hunit).symm

end AlgebraicCurve.CurveModel
