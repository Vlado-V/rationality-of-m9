module

public import M9StacksIntegration.CurveSchemeTangent
public import M9StacksIntegration.Private.CofiberedThin
public import StacksFrontier.Deformation.Examples.Geometric.SchemesHull
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.EquivalenceCriterion

/-!
# Actual genus-nine scheme deformations are prorepresentable

The zero infinitesimal automorphisms are derived from the actual negative
tangent line, not assumed. Original 0ET5 then constructs prorepresentability
and a hull for the literal native flat-deformation functor. Thinness of all
Artin fibres proves the actual equivalence with its isomorphism classes.
No formal-deformation identification or versal-ring dimension is an input.
-/

attribute [local instance 10000] SheafOfModules.hasDerivedCategory
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples
open M9Native.InvertibleExtCancellation

universe u

namespace M9Native.CurveSchemeProrepresentability

/-- Field specialization of the original native classical-base condition.
The short proof is the pinned `ProperFlatVersalPowerSeries.isClassical_self`,
source SHA 9cbd4573292938ee22dcdc133ba2b8060be9451d063b6c10d5bc9ed18f2ff0d5, retained here without
importing the unrelated proper-flat-space moduli construction. -/
theorem classical_baseField (k : Type u) [Field k] : IsClassical k k :=
  ⟨⟨inferInstance, inferInstance, by
      simpa only [IsLocalRing.maximalIdeal_eq_bot] using IsAdicComplete.bot k⟩,
    ⟨(AlgEquiv.ofBijective (Algebra.ofId k (IsLocalRing.ResidueField k))
      ⟨(algebraMap k _).injective, IsLocalRing.residue_surjective⟩).symm⟩⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]
  (hg : genus f = 9)

include hg

/-- Actual original derivations vanish because the actual tangent H⁰ does. -/
theorem derivations_eq_zero
    (D : schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X) f) : D = 0 := by
  let := modulesLinearOverField k f
  let := CurveTangentLineGeometry.differentials_isInvertible f
  letI : Subsingleton (cohomologyOverField k f
      (M9StacksIntegration.InvertibleHomCancellation.dual (Scheme.Hom.relativeDifferentials f)) 0) := by
    change Subsingleton (cohomologyOverField k f (CurveTangentLineGeometry.tangentLine f) 0)
    exact SmoothCurveTangentCohomology.tangent_h0_subsingleton f hg
  have hHom : Subsingleton (Scheme.Hom.relativeDifferentials f ⟶ structureSheafModules X) :=
    (M9StacksIntegration.InvertibleHomCancellation.homDualLinearEquivCohomologyZero
      f (Scheme.Hom.relativeDifferentials f)).injective.subsingleton
  letI : Subsingleton (Scheme.Hom.relativeDifferentials (Over.mk f).hom ⟶
      structureSheafModules (Over.mk f).left) := hHom
  let e := infinitesimalAutomorphismGroupTrivialDeformationChain (Λ := k) (Over.mk f)
  let : Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X) f) :=
    e.2.2.symm.injective.subsingleton
  exact Subsingleton.elim _ _

/-- Original infinitesimal automorphisms vanish at the actual trivial deformation. -/
theorem infinitesimalAutomorphisms_eq_bot :
    infinitesimalAutomorphisms
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k)
        (Over.mk f)).predeformation.cofibered
      dualNumbersInclusion.{u,u,u}
      (residueMorphism.{u,u,u} (artinianDualNumbers.{u,u,u} k k))
      isCanonicalDualNumberPair_dualNumbersInclusion.{u,u,u}
      (dualNumbersTrivialDeformationHom (Over.mk f))
      (dualNumbersTrivialDeformationHom_isHomLift (Over.mk f)) = ⊥ :=
  infinitesimalAutomorphisms_schemeDeformation_eq_bot (Λ := k) (Over.mk f)
    (derivations_eq_zero f hg)

/-- All actual Artin deformation fibres are thin, derived from the original
Rim-Schlessinger condition and the actual zero infinitesimal automorphisms. -/
theorem fiber_isThin (A : ArtinianLocalAlgCat.{u,u,u} k k) :
    Quiver.IsThin ((schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Fiber A) :=
  isThin_fiber_of_infinitesimalAutomorphisms_eq_bot
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
    dualNumbersInclusion.{u,u,u}
    (residueMorphism.{u,u,u} (artinianDualNumbers.{u,u,u} k k))
    isCanonicalDualNumberPair_dualNumbersInclusion.{u,u,u}
    (dualNumbersTrivialDeformationHom (Over.mk f))
    (dualNumbersTrivialDeformationHom_isHomLift (Over.mk f))
    (infinitesimalAutomorphisms_eq_bot f hg) A

/-- The actual deformation structure functor is faithful. -/
theorem structure_faithful :
    (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Faithful :=
  CofiberedThin.faithful_of_isThin_fibers _
    (schemeDeformation_cofibered (Over.mk f)) (fiber_isThin f hg)

/-- The actual scheme deformation category is equivalent to its actual
functor of fibrewise isomorphism classes, with no supplied equivalence. -/
theorem isomorphismClasses_isEquivalence :
    (toIsomorphismClasses (schemeDeformationBased (Λ := k) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))).toFunctor.IsEquivalence := by
  apply (isEquivalence_toIsomorphismClasses_iff _ _).mpr
  apply (faithful_toIsomorphismClasses_iff _ _).mpr
  intro a b α β hαβ
  exact (structure_faithful f hg).map_injective hαβ

/-- Original 0ET5 prorepresentability of the literal curve deformation functor. -/
theorem isProrepresentable :
    IsProrepresentableULift
      (isomorphismClasses (schemeDeformationBased (Λ := k) (Over.mk f))
        (schemeDeformation_cofibered (Over.mk f))) := by
  letI : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  exact isProrepresentableULift_isomorphismClasses_scheme (classical_baseField k)
    (Over.mk f) (derivations_eq_zero f hg)

omit hg

/-- An actual hull exists; no chosen versal formal object is supplied. -/
theorem existsHull :
    let F := isomorphismClasses (schemeDeformationBased (Λ := k) (Over.mk f))
      (schemeDeformation_cofibered (Over.mk f))
    ∃ ξ : FormalObject (Functor.Elements.π F),
      IsHull (categoryOfElements_projection_isCofibered F) ξ := by
  letI : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  exact exists_hull_isomorphismClasses_scheme (classical_baseField k) (Over.mk f)

end M9Native.CurveSchemeProrepresentability
