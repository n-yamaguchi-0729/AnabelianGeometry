/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianExtensionCocycle
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCechLift
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Original Cech edge values are actual extension-fiber differences

The actual free-abelian lift evaluates on every generator to restriction
of the original local section. The actual module cocycle therefore has
the same second-minus-first coefficient section as the original fiber
translation. This statement holds on every original étale overlap,
without connectedness or a constant-scalar choice on that overlap.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} (R : Type u) [CommRing R]

variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
  {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)).obj F ⟶ E)
  (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))) (hip : i ≫ p = 0)
  {V : X.Etale}
  (s : (extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)).obj.obj (op V))

local notation "b" => extensionFiberCechLift R i p hip s

/-- The original free-abelian lift evaluates on each actual Yoneda
generator to restriction of the same original local section. -/
theorem extensionFiberCechLift_generator {W : X.Etale} (m : W ⟶ V) :
    (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
      (yoneda.obj V ⋙ AddCommGrpCat.free) E b).app (op W))
        (FreeAbelianGroup.of m) = E.obj.map m.op s.val := by
  let β := (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
    (yoneda.obj V ⋙ AddCommGrpCat.free) E b
  have hs : β.app (op V) (FreeAbelianGroup.of (𝟙 V)) = s.val :=
    (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V E).apply_symm_apply s.val
  have h := ConcreteCategory.congr_hom (β.naturality m.op)
    (FreeAbelianGroup.of (𝟙 V))
  change β.app (op W) (FreeAbelianGroup.of (m ≫ 𝟙 V)) =
    E.obj.map m.op (β.app (op V) (FreeAbelianGroup.of (𝟙 V))) at h
  simpa only [Category.comp_id, hs] using h

variable (hE : (ShortComplex.mk i p hip).ShortExact)
  {T : X.Etale} (hT : IsTerminal T) (f : V ⟶ T)

local notation "hb" => extensionFiberCechLift_projection R i p hip s hT f
local notation "z" => abelianExtensionModuleCechCocycle X R hT f i p hip hE b hb

/-- The actual module edge value has the original second-minus-first
image under the original coefficient inclusion. -/
theorem extensionFiberCechCocycle_inclusion (W : X.Etale)
    (a : (cechEdgeFunctor (yoneda.map f)).obj (op W)) :
    i.hom.app (op W)
        ((freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F z).app (op W) a) =
      E.obj.map a.second.op s.val - E.obj.map a.first.op s.val := by
  let A := cechEdgeFunctor (yoneda.map f)
  let adj := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}
  have h := congrArg (fun k : (freeAbelianSheafFunctor X).obj A ⟶ E =>
      ((adj.homEquiv (A ⋙ AddCommGrpCat.free) E k).app (op W)) (FreeAbelianGroup.of a))
    (abelianExtensionModuleCechCocycle_difference X R hT f i p hip hE b hb)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left] at h
  change i.hom.app (op W)
      (((adj.homEquiv (A ⋙ AddCommGrpCat.free)
        ((Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R)).obj F)
        (freeModuleSheafUnderlyingHomEquiv X R A F z)).app (op W))
          (FreeAbelianGroup.of a)) =
    (((adj.homEquiv (yoneda.obj V ⋙ AddCommGrpCat.free) E b).app (op W)))
      (freeCechEdgeBoundary ((yoneda.map f).app (op W)) (FreeAbelianGroup.of a)) at h
  have hgen := freeModuleSheafUnderlyingHomEquiv_generator X R A F z (op W) a
  change (((adj.homEquiv (A ⋙ AddCommGrpCat.free)
      ((Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R)).obj F)
      (freeModuleSheafUnderlyingHomEquiv X R A F z)).app (op W))
        (FreeAbelianGroup.of a)) =
    (freeModuleSheafHomEquiv X R A F z).app (op W) a at hgen
  let β := adj.homEquiv (yoneda.obj V ⋙ AddCommGrpCat.free) E b
  have hboundary :
      freeCechEdgeBoundary ((yoneda.map f).app (op W)) (FreeAbelianGroup.of a) =
        FreeAbelianGroup.of a.second - FreeAbelianGroup.of a.first :=
    FreeAbelianGroup.lift_apply_of
      (fun q : CechEdge ((yoneda.map f).app (op W)) =>
        FreeAbelianGroup.of q.second - FreeAbelianGroup.of q.first) a
  have hsecond : β.app (op W) (FreeAbelianGroup.of a.second) =
      E.obj.map a.second.op s.val :=
    extensionFiberCechLift_generator R i p hip s a.second
  have hfirst : β.app (op W) (FreeAbelianGroup.of a.first) =
      E.obj.map a.first.op s.val :=
    extensionFiberCechLift_generator R i p hip s a.first
  have hright : β.app (op W)
      (freeCechEdgeBoundary ((yoneda.map f).app (op W)) (FreeAbelianGroup.of a)) =
      E.obj.map a.second.op s.val - E.obj.map a.first.op s.val :=
    (congrArg (fun x : FreeAbelianGroup (W ⟶ V) => β.app (op W) x) hboundary).trans
      ((map_sub (β.app (op W)).hom
        (FreeAbelianGroup.of a.second) (FreeAbelianGroup.of a.first)).trans
          (congrArg₂ (fun x y : E.obj.obj (op W) => x - y) hsecond hfirst))
  exact (congrArg (fun x : F.obj.obj (op W) => i.hom.app (op W) x) hgen).symm.trans
    (h.trans hright)

/-- The original module cocycle evaluates to the actual coefficient
section given by the original extension-fiber translation. -/
theorem extensionFiberCechCocycle_firstDifference (W : X.Etale)
    (a : (cechEdgeFunctor (yoneda.map f)).obj (op W)) :
    (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F z).app (op W) a =
      extensionFiberSectionDifference (ShortComplex.mk i p hip) (integerUnitSection X)
        hE (op W)
        ((extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)).obj.map a.first.op s)
        ((extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)).obj.map
          a.second.op s) := by
  symm
  apply extensionFiberSectionDifference_unique (ShortComplex.mk i p hip)
    (integerUnitSection X) hE (op W)
    ((extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)).obj.map a.first.op s)
    ((extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)).obj.map a.second.op s)
  exact extensionFiberCechCocycle_inclusion R i p hip s hE hT f W a

end EtaleFundamentalGroups.Cohomology
