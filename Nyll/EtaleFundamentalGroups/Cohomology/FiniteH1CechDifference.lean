/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.Monodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromyDisplacement
public import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
public import Nyll.EtaleFundamentalGroups.Cohomology.RepresentedMonodromy
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Category.FinTopCat

/-!
# Original extension differences on a connected finite overlap

Two maps from an actual connected finite overlap into a cover determine two
restrictions of the same extension lift. Their difference is the original
monodromy character evaluated on an element carrying the first geometric
point to the second. The equality is proved for the original sheaf maps:
transitivity on the overlap and faithful monodromy descend the torsor
displacement calculation from one geometric point.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleCohomology Opposite
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {E Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ Q) (hip : i ≫ p = 0) (hs : (ShortComplex.mk i p hip).ShortExact)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- A genuine overlap displacement gives equality of the original lift
maps with translation by the original extension character. -/
theorem extensionFiber_map_eq_translation_of_fiber
    {V W : FiniteEtale X} [IsConnected W]
    (f : (finiteEtaleSheaf X).obj V ⟶ extensionFiber (ShortComplex.mk i p hip) t)
    (m₀ m₁ : W ⟶ V) (w : (FiniteEtale.fiber ξ).obj W)
    (g : Aut (FiniteEtale.fiber ξ))
    (hg : (FiniteEtale.fiber ξ).map m₁ w =
      g • (FiniteEtale.fiber ξ).map m₀ w) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (finiteEtaleSheaf X).map m₁ ≫ f =
      (finiteEtaleSheaf X).map m₀ ≫ f ≫
        constantFiberTranslation A i p hip t
          (extensionMonodromyCharacter A i p hip hs t ξ g).toAdd := by
  intro coefficientTopology
  let H := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).functor
  let N := (finiteLocallyConstantSetMonodromy ξ).functor
  let F := functorToContAction (FiniteEtale.fiber ξ)
  let L : EtaleFiniteLocallyConstantSetSheaf X :=
    ⟨extensionFiber (ShortComplex.mk i p hip) t,
      extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p hip) t hs
        (constantAbelian_isFiniteLocallyConstant X A)⟩
  let mf : H.obj V ⟶ L := ObjectProperty.homMk f
  let a := (extensionMonodromyCharacter A i p hip hs t ξ g).toAdd
  let tr : L ⟶ L := ObjectProperty.homMk (constantFiberTranslation A i p hip t a)
  let eV := representedMonodromyIso ξ V
  let eW := representedMonodromyIso ξ W
  let left : F.obj W ⟶ N.obj L := eW.inv ≫ N.map (H.map m₁ ≫ mf)
  let right : F.obj W ⟶ N.obj L := eW.inv ≫ N.map (H.map m₀ ≫ mf ≫ tr)
  have hl : left = F.map m₁ ≫ eV.inv ≫ N.map mf := by
    dsimp only [left]
    rw [N.map_comp, ← Category.assoc, ← representedMonodromyIso_inv_naturality]
    exact Category.assoc _ _ _
  have hr : right = F.map m₀ ≫ eV.inv ≫ N.map mf ≫ N.map tr := by
    dsimp only [right]
    rw [N.map_comp, N.map_comp, ← Category.assoc,
      ← representedMonodromyIso_inv_naturality]
    simp only [Category.assoc]
    rfl
  have hw : left.hom.hom w = right.hom.hom w := by
    rw [hl, hr]
    change (N.map mf).hom.hom (eV.inv.hom.hom
        ((FiniteEtale.fiber ξ).map m₁ w)) =
      (N.map tr).hom.hom ((N.map mf).hom.hom
        (eV.inv.hom.hom ((FiniteEtale.fiber ξ).map m₀ w)))
    rw [hg]
    let v₀ : (F.obj V).obj.V := (FiniteEtale.fiber ξ).map m₀ w
    have he : eV.inv.hom.hom (ConcreteCategory.hom (((F.obj V).obj.ρ g).asHom) v₀) =
        ConcreteCategory.hom (((N.obj (H.obj V)).obj.ρ g).asHom) (eV.inv.hom.hom v₀) :=
      ConcreteCategory.congr_hom (eV.inv.hom.comm g) v₀
    have hm : (N.map mf).hom.hom
        (ConcreteCategory.hom (((N.obj (H.obj V)).obj.ρ g).asHom) (eV.inv.hom.hom v₀)) =
        ConcreteCategory.hom (((N.obj L).obj.ρ g).asHom) ((N.map mf).hom.hom (eV.inv.hom.hom v₀)) :=
      ConcreteCategory.congr_hom ((N.map mf).hom.comm g) (eV.inv.hom.hom v₀)
    change (N.map mf).hom.hom
        (eV.inv.hom.hom (ConcreteCategory.hom (((F.obj V).obj.ρ g).asHom) v₀)) =
      (N.map tr).hom.hom ((N.map mf).hom.hom (eV.inv.hom.hom v₀))
    let T := extensionMonodromyTorsor A i p hip hs t ξ
    exact (congrArg ((N.map mf).hom.hom) he).trans
      (hm.trans ((extensionMonodromyCharacter_smul A i p hip hs t ξ g _).symm.trans
        (translation_on_monodromy A i p hip hs t ξ a _).symm))
  have hlr : left = right := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro v
    obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq (Aut (FiniteEtale.fiber ξ)) w v
    exact (ConcreteCategory.congr_hom (left.hom.comm γ) w).trans
      ((congrArg (fun q => γ • q) hw).trans
        (ConcreteCategory.congr_hom (right.hom.comm γ) w).symm)
  have hn : N.map (H.map m₁ ≫ mf) = N.map (H.map m₀ ≫ mf ≫ tr) :=
    (cancel_epi eW.inv).mp hlr
  exact congrArg (fun k : H.obj W ⟶ L => k.hom) (N.map_injective hn)

/-- The actual coefficient section between the original two lifts is the
constant section of the original H¹ character, with second-minus-first sign. -/
theorem extensionFiberSectionDifference_eq_h1Character
    {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
    (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hip : i ≫ p = 0) (hs : (ShortComplex.mk i p hip).ShortExact)
    {V W : FiniteEtale X} [IsConnected W]
    (f : (finiteEtaleSheaf X).obj V ⟶
      extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X))
    (m₀ m₁ : W ⟶ V) (w : (FiniteEtale.fiber ξ).obj W)
    (g : Aut (FiniteEtale.fiber ξ))
    (hg : (FiniteEtale.fiber ξ).map m₁ w =
      g • (FiniteEtale.fiber ξ).map m₀ w) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    extensionFiberSectionDifference (ShortComplex.mk i p hip) (integerUnitSection X) hs
        (op ((finiteEtaleToEtale X).obj W))
        (f.hom.app _ ((finiteEtaleToEtale X).map m₀))
        (f.hom.app _ ((finiteEtaleToEtale X).map m₁)) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app _
        (h1Character A ξ hs.extClass g).toAdd := by
  intro coefficientTopology
  rw [h1Character_extClass]
  apply extensionFiberSectionDifference_unique
  apply eq_sub_iff_add_eq.mpr
  have hm := extensionFiber_map_eq_translation_of_fiber A i p hip hs
    (integerUnitSection X) ξ f m₀ m₁ w g hg
  have hv := congrArg
    (fun k : (finiteEtaleSheaf X).obj W ⟶
      extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X) =>
      (k.hom.app (op ((finiteEtaleToEtale X).obj W)) (𝟙 _)).val) hm
  have hv' := hv.symm
  change i.hom.app (op ((finiteEtaleToEtale X).obj W))
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app _
        (extensionMonodromyCharacter A i p hip hs (integerUnitSection X) ξ g).toAdd) +
      (show E.obj.obj (op ((finiteEtaleToEtale X).obj W)) from
        (f.hom.app _ (𝟙 _ ≫ (finiteEtaleToEtale X).map m₀)).val) =
    (show E.obj.obj (op ((finiteEtaleToEtale X).obj W)) from
      (f.hom.app _ (𝟙 _ ≫ (finiteEtaleToEtale X).map m₁)).val) at hv'
  simpa only [Category.id_comp] using hv'

end EtaleFundamentalGroups.Cohomology
