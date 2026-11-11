/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianPullbackConstants
public import Nyll.EtaleCohomology.Classical.ConstantEtaleSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoRestriction
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.ConstantRepresentable
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSectionMaps
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.JacobsonSpace

/-!
# Residue-field coefficients under divisor chart transport

The canonical restriction comparison for constant abelian sheaves preserves
their original sections. Applying this on each residue-field point shows that
the existing coefficient equivalence is unchanged by an étale change of base
field. The native cartesian comparison then preserves the integer coefficient
of each closed-point divisor summand under a chart isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- The actual restriction comparison for a constant abelian sheaf sends the
original constant section to the same section. -/
theorem etaleRestrictionConstantAbelianIso_hom_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (A : AddCommGrpCat.{u}) (V : X.Etale) :
    let k := (Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f)
      AddCommGrpCat.{u} terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
      (etaleRestriction f AddCommGrpCat.{u})
      (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u})).app A
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app
        (op ((etalePostcompose f).obj V)) ≫ k.hom.hom.app (op V) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op V) := by
  intro k
  let L := etalePostcompose f
  let R := etaleBaseChange f
  let a := etalePostcomposeBaseChangeAdjunction f
  let W := L.obj V
  let α := a.unit.app V
  let ε := a.counit.app W
  let CY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let CX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let ηY := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)
  let ηX := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)
  have h := constantSheafCompLeftAdjointIso_hom_section f
    (etaleRestriction f AddCommGrpCat.{u})
    (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}) A W
  change ηY.app (op W) ≫
      (((etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}).unit.app
        CY).hom.app (op W) ≫ k.hom.hom.app (op (R.obj W))) =
    ηX.app (op (R.obj W)) at h
  rw [etaleRestrictionUnit_app] at h
  let c : CY.obj.obj (op (L.obj (R.obj W))) ⟶ CX.obj.obj (op (R.obj W)) :=
    k.hom.hom.app (op (R.obj W))
  let d : CY.obj.obj (op W) ⟶ CX.obj.obj (op V) := k.hom.hom.app (op V)
  let t : A ⟶ CY.obj.obj (op W) := ηY.app (op W)
  let s₀ : A ⟶ CX.obj.obj (op V) := ηX.app (op V)
  let s₁ : A ⟶ CX.obj.obj (op (R.obj W)) := ηX.app (op (R.obj W))
  change t ≫ CY.obj.map ε.op ≫ c = s₁ at h
  have hn : CY.obj.map (L.map α).op ≫ k.hom.hom.app (op V) =
      k.hom.hom.app (op (R.obj W)) ≫ CX.obj.map α.op :=
    k.hom.hom.naturality α.op
  have hm : CY.obj.map ε.op ≫ CY.obj.map (L.map α).op = 𝟙 _ := by
    rw [← CY.obj.map_comp, ← op_comp]
    exact (congrArg (fun m => CY.obj.map m.op)
      (a.left_triangle_components V)).trans (CY.obj.map_id _)
  change CY.obj.map (L.map α).op ≫ d = c ≫ CX.obj.map α.op at hn
  have hd : (CY.obj.map ε.op ≫ c) ≫ CX.obj.map α.op = d := by
    rw [Category.assoc, ← hn, ← Category.assoc, hm, Category.id_comp]
  have hη : s₁ ≫ CX.obj.map α.op = s₀ := by
    have hnatural := ηX.naturality α.op
    change (𝟙 A) ≫ s₀ = s₁ ≫ CX.obj.map α.op at hnatural
    exact hnatural.symm.trans (Category.id_comp s₀)
  change t ≫ d = s₀
  calc
    _ = t ≫ ((CY.obj.map ε.op ≫ c) ≫ CX.obj.map α.op) :=
      congrArg (fun m => t ≫ m) hd.symm
    _ = (t ≫ (CY.obj.map ε.op ≫ c)) ≫ CX.obj.map α.op :=
      (Category.assoc _ _ _).symm
    _ = s₁ ≫ CX.obj.map α.op :=
      congrArg (fun m => m ≫ CX.obj.map α.op) h
    _ = s₀ := hη

/-- The original pointwise coefficients of a constant abelian sheaf are
preserved by the canonical restriction comparison between base fields. -/
theorem fieldEtaleConstantAbelianSectionsAddEquiv_restriction
    {K L : Type u} [Field K] [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) [Etale f]
    (A : AddCommGrpCat.{u}) (V : (Spec (CommRingCat.of L)).Etale) :
    let k := (Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f)
      AddCommGrpCat.{u} terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange f)
        (⊤_ (Spec (CommRingCat.of K)).Etale))
      (etaleRestriction f AddCommGrpCat.{u})
      (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u})).app A
    ∀ (s : ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology
      AddCommGrpCat.{u}).obj A).obj.obj (op ((etalePostcompose f).obj V))) (x : V.left),
      fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec L V A
        (k.hom.hom.app (op V) s) x =
      fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K
        ((etalePostcompose f).obj V) A s x := by
  intro k s x
  let ρ := V.left.fromSpecResidueField x
  let q := ρ ≫ V.hom
  have hq : Etale q := fieldEtaleResiduePoint_etale L V x
  let P := (etalePostcompose q).obj (etaleBaseObject (Spec (V.left.residueField x)))
  let r : P ⟶ V := MorphismProperty.Over.homMk (A := P) (B := V) ρ (by
    change ρ ≫ V.hom = (𝟙 _) ≫ q
    exact (Category.id_comp q).symm)
  let P' := (etalePostcompose f).obj P
  have : Subsingleton P'.left :=
    inferInstanceAs (Subsingleton (Spec (V.left.residueField x)))
  let r' := (etalePostcompose f).map r
  let ξ : P.left := IsLocalRing.closedPoint (V.left.residueField x)
  let CK := (constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology
    AddCommGrpCat.{u}).obj A
  let CL := (constantSheaf (Spec (CommRingCat.of L)).smallEtaleTopology
    AddCommGrpCat.{u}).obj A
  let ηK := toSheafify (Spec (CommRingCat.of K)).smallEtaleTopology
    ((Functor.const (Spec (CommRingCat.of K)).Etaleᵒᵖ).obj A)
  let ηL := toSheafify (Spec (CommRingCat.of L)).smallEtaleTopology
    ((Functor.const (Spec (CommRingCat.of L)).Etaleᵒᵖ).obj A)
  let t := CK.obj.map r'.op s
  let E := fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec K P' A
  let b := E t ξ
  have ht : t = ηK.app (op P') b := by
    apply E.injective
    have hb : E t = fun _ => b := by
      funext z
      exact congrArg (E t) (Subsingleton.elim z ξ)
    exact hb.trans
      (fieldEtaleConstantAbelianSectionsAddEquiv_apply_toSheafify K P' A b).symm
  have hn : CL.obj.map r.op (k.hom.hom.app (op V) s) =
      k.hom.hom.app (op P) t :=
    (ConcreteCategory.congr_hom (k.hom.hom.naturality r.op) s).symm
  have hk : k.hom.hom.app (op P) t = ηL.app (op P) b := by
    rw [ht]
    exact ConcreteCategory.congr_hom
      (etaleRestrictionConstantAbelianIso_hom_section f A P) b
  have hL := fieldEtaleConstantAbelianSectionsAddEquiv_morphism_naturality
    L P V r A (k.hom.hom.app (op V) s) ξ
  have hK := fieldEtaleConstantAbelianSectionsAddEquiv_morphism_naturality
    K P' ((etalePostcompose f).obj V) r' A s ξ
  have hx : r.left ξ = x := Scheme.fromSpecResidueField_apply x ξ
  have hx' : r'.left ξ = x := hx
  rw [hx] at hL
  rw [hx'] at hK
  calc
    _ = fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec L P A
        (CL.obj.map r.op (k.hom.hom.app (op V) s)) ξ := hL.symm
    _ = fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec L P A
        (ηL.app (op P) b) ξ :=
      congrArg (fun t =>
        fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec L P A t ξ)
        (hn.trans hk)
    _ = b := congrFun
      (fieldEtaleConstantAbelianSectionsAddEquiv_apply_toSheafify L P A b) ξ
    _ = _ := hK

/-- Chart transport of the actual residue-field summand preserves the
integer attached to each original point of the residue fiber. -/
theorem closedPointDivisorSummandIsoRestrictionIso_coefficient
    {U X : Scheme.{u}} (e : U ≅ X) (y : closedPoints U) (V : U.Etale) :
    let x : closedPoints X := (e.hom.homeomorph.sets
      e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y
    ∀ (s : (closedPointDivisorSummand X x).obj.obj
      (op ((etalePostcompose e.hom).obj V)))
      (z : closedPointResidueFiber U y V),
      closedPointDivisorSummandSectionsAddEquiv U y V
        ((closedPointDivisorSummandIsoRestrictionIso e y).hom.hom.app (op V) s) z =
      closedPointDivisorSummandSectionsAddEquiv X x
        ((etalePostcompose e.hom).obj V) s
        ⟨z.1, by
          change e.hom (V.hom z.1) = e.hom y.1
          exact congrArg e.hom z.2⟩ := by
  intro x s z
  let iU := closedPointResidueFieldMap U y
  let iX := closedPointResidueFieldMap X x
  let g : Spec (U.residueField y.1) ⟶ Spec (X.residueField x.1) :=
    Spec.map (e.hom.residueFieldMap y.1)
  have : IsIso (e.hom.residueFieldMap y.1) := inferInstance
  have : IsIso g := inferInstanceAs (IsIso (Spec.map (e.hom.residueFieldMap y.1)))
  have hg : Etale g := inferInstance
  have H : IsPullback iU g e.hom iX := by
    apply IsPullback.of_vert_isIso
    exact ⟨(e.hom.SpecMap_residueFieldMap_fromSpecResidueField y.1).symm⟩
  let C := (constantSheaf (Spec (X.residueField x.1)).smallEtaleTopology
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let k := (Sites.constantSheafCompLeftAdjointIso (etaleBaseChange g)
    AddCommGrpCat.{u} terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (etaleBaseChange g)
      (⊤_ (Spec (X.residueField x.1)).Etale))
    (etaleRestriction g AddCommGrpCat.{u})
    (etaleRestrictionPushforwardAdjunction g AddCommGrpCat.{u})).app
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let W := (etaleBaseChange iU).obj V
  let T := (etaleBaseChange iX).obj ((etalePostcompose e.hom).obj V)
  let m : (etalePostcompose g).obj W ⟶ T :=
    (@etaleRestrictionBaseChangeSiteIsoOfIsPullback
      X (Spec (X.residueField x.1)) U e.hom (inferInstance : Etale e.hom) iX
      (Spec (U.residueField y.1)) iU g hg H).hom.app V
  let pU := closedPointResidueFiberPointEquiv U y V
  let pX := closedPointResidueFiberPointEquiv X x ((etalePostcompose e.hom).obj V)
  let zX : closedPointResidueFiber X x ((etalePostcompose e.hom).obj V) :=
    ⟨z.1, by
      change e.hom (V.hom z.1) = e.hom y.1
      exact congrArg e.hom z.2⟩
  have hmap : (closedPointDivisorSummandIsoRestrictionIso e y).hom.hom.app
      (op V) s = k.hom.hom.app (op W) (C.obj.map m.op s) := by
    rfl
  have hproj : m.left ≫ pullback.fst ((etalePostcompose e.hom).obj V).hom iX =
      pullback.fst V.hom iU :=
    ((IsPullback.of_hasPullback V.hom iU).paste_vert H).isoPullback_hom_fst
  have hcoord : m.left (pU.symm z) = pX.symm zX := by
    apply pX.injective
    rw [pX.apply_symm_apply]
    apply Subtype.ext
    change pullback.fst ((etalePostcompose e.hom).obj V).hom iX
      (m.left (pU.symm z)) = z.1
    exact (congrArg (fun a : W.left ⟶ V.left => a (pU.symm z)) hproj).trans
      (congrArg Subtype.val (pU.apply_symm_apply z))
  change fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
      (U.residueField y.1) W (AddCommGrpCat.of (ULift.{u} ℤ))
        ((closedPointDivisorSummandIsoRestrictionIso e y).hom.hom.app (op V) s)
        (pU.symm z) =
    fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
      (X.residueField x.1) T (AddCommGrpCat.of (ULift.{u} ℤ)) s (pX.symm zX)
  calc
    _ = fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
        (U.residueField y.1) W (AddCommGrpCat.of (ULift.{u} ℤ))
          (k.hom.hom.app (op W) (C.obj.map m.op s)) (pU.symm z) :=
      congrArg (fun t => fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
        (U.residueField y.1) W (AddCommGrpCat.of (ULift.{u} ℤ)) t (pU.symm z)) hmap
    _ = fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
        (X.residueField x.1) ((etalePostcompose g).obj W)
          (AddCommGrpCat.of (ULift.{u} ℤ)) (C.obj.map m.op s) (pU.symm z) :=
      @fieldEtaleConstantAbelianSectionsAddEquiv_restriction
        (X.residueField x.1) (U.residueField y.1) inferInstance inferInstance g hg
        (AddCommGrpCat.of (ULift.{u} ℤ)) W (C.obj.map m.op s) (pU.symm z)
    _ = fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
        (X.residueField x.1) T (AddCommGrpCat.of (ULift.{u} ℤ))
          s (m.left (pU.symm z)) :=
      fieldEtaleConstantAbelianSectionsAddEquiv_morphism_naturality
        (X.residueField x.1) ((etalePostcompose g).obj W) T m
          (AddCommGrpCat.of (ULift.{u} ℤ)) s (pU.symm z)
    _ = _ := congrArg
      (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
        (X.residueField x.1) T (AddCommGrpCat.of (ULift.{u} ℤ)) s) hcoord

end EtaleCohomology
