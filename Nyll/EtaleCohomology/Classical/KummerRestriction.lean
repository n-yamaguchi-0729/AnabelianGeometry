/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionNaturality
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectNaturality
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.SheafH0TerminalTransport
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original Kummer coefficients on an étale object

The original inverse-image map of Kummer kernels gives a map from
the actually restricted roots sheaf to the native roots sheaf on
the source. Its square with the original inclusions in Gm commutes.
Consequently localization of an objectwise Kummer class retains its
original coefficient image in native Gm cohomology.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] (n : ℕ)

/-- The original Kummer pullback, transported through the original
inverse-image/restriction comparison on the actual étale morphism. -/
def etaleRootsOfUnityRestriction :
    (etaleRestriction f AddCommGrpCat.{u}).obj (etaleRootsOfUnitySheaf X n) ⟶
      etaleRootsOfUnitySheaf U n :=
  (etaleAbelianPullbackRestrictionIso f).inv.app (etaleRootsOfUnitySheaf X n) ≫
    etaleRootsOfUnityPullback f n

/-- The restricted Kummer class retains the original kernel
inclusion and the unchanged native unit-sheaf identification. -/
theorem etaleRootsOfUnityRestriction_ι :
    etaleRootsOfUnityRestriction f n ≫ kernel.ι (etaleMultiplicativeGroupPower U n) =
      (etaleRestriction f AddCommGrpCat.{u}).map
          (kernel.ι (etaleMultiplicativeGroupPower X n)) ≫
        (etaleRestrictionMultiplicativeGroupIso f).hom := by
  let I := etaleAbelianPullbackRestrictionIso f
  let i := kernel.ι (etaleMultiplicativeGroupPower X n)
  change (I.inv.app _ ≫ etaleRootsOfUnityPullback f n) ≫
    kernel.ι (etaleMultiplicativeGroupPower U n) = _
  rw [Category.assoc, etaleRootsOfUnityPullback_ι, ← Category.assoc,
    ← I.inv.naturality i, Category.assoc,
    ← etaleMultiplicativeGroupPullback_restriction]
  rw [← Category.assoc (I.inv.app _) (I.hom.app _),
    I.inv_hom_id_app, Category.id_comp]

/-- The original native Kummer pullback is restriction followed by
the original identification of the restricted Kummer kernel. -/
theorem etaleRootsOfUnityCohomologyPullback_restriction
    (i : ℕ) (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) i) :
    etaleRootsOfUnityCohomologyPullback f n i a =
      Sheaf.H.map (etaleRootsOfUnityRestriction f n) i
        (etaleAbelianRestrictionCohomologyPullback f
          (etaleRootsOfUnitySheaf X n) i a) := by
  let I := etaleAbelianPullbackRestrictionIso f
  change Sheaf.H.map (etaleRootsOfUnityPullback f n) i
      (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf X n) i a) =
    Sheaf.H.map (I.inv.app _ ≫ etaleRootsOfUnityPullback f n) i
      (Sheaf.H.map (I.hom.app _) i
        (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf X n) i a))
  rw [← Sheaf.H.map_comp_apply, ← Category.assoc, I.hom_inv_id_app, Category.id_comp]

/-- Exact étale restriction preserves the original Kummer kernel, and its
canonical comparison is the existing Kummer restriction map. -/
instance etaleRootsOfUnityRestriction_isIso :
    IsIso (etaleRootsOfUnityRestriction f n) := by
  let R := etaleRestriction f AddCommGrpCat.{u}
  let e := etaleRestrictionMultiplicativeGroupIso f
  have hpower : R.map (etaleMultiplicativeGroupPower X n) ≫ e.hom =
      e.hom ≫ etaleMultiplicativeGroupPower U n := by
    have hid : R.map (𝟙 (etaleMultiplicativeGroupSheaf X)) =
        𝟙 (R.obj (etaleMultiplicativeGroupSheaf X)) := R.map_id _
    simp only [etaleMultiplicativeGroupPower, Functor.map_nsmul]
    rw [hid]
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]
  let eK : R.obj (etaleRootsOfUnitySheaf X n) ≅ etaleRootsOfUnitySheaf U n :=
    PreservesKernel.iso R (etaleMultiplicativeGroupPower X n) ≪≫
      kernel.mapIso (R.map (etaleMultiplicativeGroupPower X n))
        (etaleMultiplicativeGroupPower U n) e e hpower
  have hι : eK.hom ≫ kernel.ι (etaleMultiplicativeGroupPower U n) =
      R.map (kernel.ι (etaleMultiplicativeGroupPower X n)) ≫ e.hom := by
    change ((PreservesKernel.iso R (etaleMultiplicativeGroupPower X n)).hom ≫
      (kernel.mapIso (R.map (etaleMultiplicativeGroupPower X n))
        (etaleMultiplicativeGroupPower U n) e e hpower).hom) ≫ _ = _
    rw [Category.assoc, kernel.mapIso_hom, kernel.map, kernel.lift_ι,
      ← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]
  have he : etaleRootsOfUnityRestriction f n = eK.hom :=
    (cancel_mono (kernel.ι (etaleMultiplicativeGroupPower U n))).mp
      ((etaleRootsOfUnityRestriction_ι f n).trans hι.symm)
  rw [he]
  exact inferInstance

/-- Sections of the original Kummer sheaf on an étale object are native
degree-zero Kummer classes on that object's own scheme. -/
def etaleRootsOfUnitySectionsEquiv :
    (etaleRootsOfUnitySheaf X n).obj.obj (op (Scheme.Etale.mk f)) ≃+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf U n) 0 := by
  let W := (zariskiToEtale U).obj ⊤
  let hW : IsTerminal W :=
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) U).ofIso
        (zariskiToEtaleTopIso U).symm
  let c := (etaleRestrictionTopObjectSectionIso f (etaleRootsOfUnitySheaf X n)).symm ≪≫
    ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      (asIso (etaleRootsOfUnityRestriction f n))).app (op W)
  exact c.addCommGroupIsoToAddEquiv.trans
    (Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf U n) hW).symm

/-- The native class retains the actual restriction component at the
terminal top-open object. -/
theorem etaleRootsOfUnitySectionsEquiv_apply
    (s : (etaleRootsOfUnitySheaf X n).obj.obj (op (Scheme.Etale.mk f))) :
    let W := (zariskiToEtale U).obj ⊤
    let hW : IsTerminal W :=
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) U).ofIso
          (zariskiToEtaleTopIso U).symm
    Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf U n) hW
        (etaleRootsOfUnitySectionsEquiv f n s) =
      (etaleRootsOfUnityRestriction f n).hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso f (etaleRootsOfUnitySheaf X n)).inv s) := by
  intro W hW
  exact (Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf U n) hW).apply_symm_apply _

/-- The same original section comparison evaluated at the identity object
of the source scheme's small étale site. -/
def etaleRootsOfUnityIdentitySectionsEquiv :
    (etaleRootsOfUnitySheaf X n).obj.obj (op (Scheme.Etale.mk f)) ≃+
      (etaleRootsOfUnitySheaf U n).obj.obj (op (Scheme.Etale.mk (𝟙 U))) :=
  (etaleRootsOfUnitySectionsEquiv f n).trans
    (Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf U n)
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) U))

/-- Passing to identity-object sections uses the original presheaf map
from the top-open object, with no independent choice of roots. -/
theorem etaleRootsOfUnityIdentitySectionsEquiv_apply
    (s : (etaleRootsOfUnitySheaf X n).obj.obj (op (Scheme.Etale.mk f))) :
    etaleRootsOfUnityIdentitySectionsEquiv f n s =
      (etaleRootsOfUnitySheaf U n).obj.map (zariskiToEtaleTopIso U).inv.op
        ((etaleRootsOfUnityRestriction f n).hom.app
          (op ((zariskiToEtale U).obj ⊤))
          ((etaleRestrictionTopObjectSectionIso f (etaleRootsOfUnitySheaf X n)).inv s)) := by
  let hU := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) U
  let hW := hU.ofIso (zariskiToEtaleTopIso U).symm
  change Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf U n) hU
    (etaleRootsOfUnitySectionsEquiv f n s) = _
  rw [← sheafH0_restriction (etaleRootsOfUnitySheaf U n) hU hW
    (zariskiToEtaleTopIso U).inv, etaleRootsOfUnitySectionsEquiv_apply]

/-- The original restriction-composition isomorphism preserves the
original Kummer kernels, through their unchanged inclusions in Gm. -/
theorem etaleRestrictionObjectIso_rootsOfUnity
    {V W : X.Etale} (g : W ⟶ V) :
    (etaleRestriction g.left AddCommGrpCat.{u}).map
        (etaleRootsOfUnityRestriction V.hom n) ≫
      etaleRootsOfUnityRestriction g.left n =
    (etaleRestrictionObjectIso g).hom.app (etaleRootsOfUnitySheaf X n) ≫
      etaleRootsOfUnityRestriction W.hom n := by
  have hV : etaleRootsOfUnityRestriction V.hom n ≫
      kernel.ι (etaleMultiplicativeGroupPower V.left n) =
        (etaleRestriction V.hom AddCommGrpCat.{u}).map
          (kernel.ι (etaleMultiplicativeGroupPower X n)) ≫
            (etaleRestrictionMultiplicativeGroupIso V.hom).hom :=
    etaleRootsOfUnityRestriction_ι V.hom n
  have hW : etaleRootsOfUnityRestriction W.hom n ≫
      kernel.ι (etaleMultiplicativeGroupPower W.left n) =
        (etaleRestriction W.hom AddCommGrpCat.{u}).map
          (kernel.ι (etaleMultiplicativeGroupPower X n)) ≫
            (etaleRestrictionMultiplicativeGroupIso W.hom).hom :=
    etaleRootsOfUnityRestriction_ι W.hom n
  apply (cancel_mono (kernel.ι (etaleMultiplicativeGroupPower W.left n))).mp
  rw [Category.assoc, etaleRootsOfUnityRestriction_ι g.left n,
    ← Category.assoc, ← Functor.map_comp, hV, Functor.map_comp, Category.assoc,
    etaleRestrictionObjectIso_multiplicativeGroup, Category.assoc, hW]
  have hnat :
      (etaleRestriction g.left AddCommGrpCat.{u}).map
          ((etaleRestriction V.hom AddCommGrpCat.{u}).map
            (kernel.ι (etaleMultiplicativeGroupPower X n))) ≫
        (etaleRestrictionObjectIso g).hom.app (etaleMultiplicativeGroupSheaf X) =
      (etaleRestrictionObjectIso g).hom.app (etaleRootsOfUnitySheaf X n) ≫
        (etaleRestriction W.hom AddCommGrpCat.{u}).map
          (kernel.ι (etaleMultiplicativeGroupPower X n)) :=
    (etaleRestrictionObjectIso g).hom.naturality
      (kernel.ι (etaleMultiplicativeGroupPower X n))
  simpa only [Category.assoc] using
    congrArg (fun q => q ≫ (etaleRestrictionMultiplicativeGroupIso W.hom).hom) hnat

variable (V : X.Etale)

/-- Objectwise Kummer cohomology mapped to the native Kummer
cohomology of the same étale scheme, using the original localization
equivalence and original Kummer pullback. -/
def etaleRootsOfUnityCohomologyPresheafRestriction (i : ℕ) :
    Sheaf.H'.{u} (etaleRootsOfUnitySheaf X n) i V →+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf V.left n) i :=
  (Sheaf.H.map (etaleRootsOfUnityRestriction V.hom n) i).comp
    (etaleCohomologyPresheafRestrictionEquiv V (etaleRootsOfUnitySheaf X n) i).toAddMonoidHom

/-- The original coefficient inclusion commutes with passing from
objectwise Kummer cohomology to the native cohomology of that object. -/
theorem etaleRootsOfUnityCohomologyPresheafRestriction_inclusion
    (i : ℕ) (a : Sheaf.H'.{u} (etaleRootsOfUnitySheaf X n) i V) :
    Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower V.left n)) i
        (etaleRootsOfUnityCohomologyPresheafRestriction n V i a) =
      Sheaf.H.map (etaleRestrictionMultiplicativeGroupIso V.hom).hom i
        (etaleCohomologyPresheafRestrictionEquiv V (etaleMultiplicativeGroupSheaf X) i
          (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology i).map
            (kernel.ι (etaleMultiplicativeGroupPower X n))).app (op V) a)) := by
  change Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower V.left n)) i
    (Sheaf.H.map (etaleRootsOfUnityRestriction V.hom n) i
      (etaleCohomologyPresheafRestrictionEquiv V (etaleRootsOfUnitySheaf X n) i a)) = _
  have hV : etaleRootsOfUnityRestriction V.hom n ≫
      kernel.ι (etaleMultiplicativeGroupPower V.left n) =
        (etaleRestriction V.hom AddCommGrpCat.{u}).map
          (kernel.ι (etaleMultiplicativeGroupPower X n)) ≫
            (etaleRestrictionMultiplicativeGroupIso V.hom).hom :=
    etaleRootsOfUnityRestriction_ι V.hom n
  rw [← Sheaf.H.map_comp_apply, hV,
    Sheaf.H.map_comp_apply, etaleCohomologyPresheafRestrictionEquiv_naturality]

variable {V} in
/-- Restriction along an actual morphism of étale objects becomes
the original native Kummer pullback in every cohomological degree. -/
theorem etaleRootsOfUnityCohomologyPresheafRestriction_object_restriction
    {W : X.Etale} (g : W ⟶ V) (i : ℕ)
    (a : Sheaf.H'.{u} (etaleRootsOfUnitySheaf X n) i V) :
    etaleRootsOfUnityCohomologyPresheafRestriction n W i
        (((etaleRootsOfUnitySheaf X n).cohomologyPresheaf i).map g.op a) =
      etaleRootsOfUnityCohomologyPullback g.left n i
        (etaleRootsOfUnityCohomologyPresheafRestriction n V i a) := by
  change Sheaf.H.map (etaleRootsOfUnityRestriction W.hom n) i
      (etaleCohomologyPresheafRestrictionEquiv W (etaleRootsOfUnitySheaf X n) i
        (((etaleRootsOfUnitySheaf X n).cohomologyPresheaf i).map g.op a)) =
    etaleRootsOfUnityCohomologyPullback g.left n i
      (Sheaf.H.map (etaleRootsOfUnityRestriction V.hom n) i
        (etaleCohomologyPresheafRestrictionEquiv V (etaleRootsOfUnitySheaf X n) i a))
  rw [etaleCohomologyPresheafRestrictionEquiv_object_restriction,
    ← Sheaf.H.map_comp_apply, etaleRootsOfUnityCohomologyPullback_restriction,
    etaleAbelianRestrictionCohomologyPullback_naturality,
    ← Sheaf.H.map_comp_apply, etaleRestrictionObjectIso_rootsOfUnity]
  all_goals rfl

end EtaleCohomology
