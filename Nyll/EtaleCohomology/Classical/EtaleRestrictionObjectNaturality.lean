/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectLocalization
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectSections
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectCohomology
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectUnits

/-!
# Object naturality of the original localized cohomology

The restriction of the original cohomology presheaf along a morphism
of étale objects is the original cohomological pullback on their
underlying schemes. The coefficient comparison is the actual
composition isomorphism of restrictions.

The proof identifies the source morphisms on degree-zero sections
and then applies the original exact-functor map on Ext in every
degree. Thus the comparison retains the original restriction maps,
including restrictions of classes which do not come from the base.
-/
