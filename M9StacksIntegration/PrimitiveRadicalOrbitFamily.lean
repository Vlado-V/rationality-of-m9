module

public import M9StacksIntegration.PrimitiveRhoFiberNondegenerate
public import M9StacksIntegration.PrimitiveGaussGroupScheme
public import M9StacksIntegration.PrimitiveGrassmannianAction

/-!
# The genuine Gauss-times-rho-family morphism

The source is the actual tensor coordinate ring of the thirteen-parameter
symplectic family and the nondegenerate thirty-two-parameter graph domain.
The map is the actual native Sp6 action on the actual perpendicular graph
family. No dominance, homogeneous-space section, or field quotient is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace M9Native.PrimitiveRadicalOrbitFamily

abbrev base := Spec (.of ℂ)
abbrev gaussRing := PrimitiveGaussCoordinates.sourceRing ℂ
abbrev fiberRing := PrimitiveRhoFiberNondegenerate.nondegenerateRing
abbrev coordinateRing := gaussRing ⊗[ℂ] fiberRing
abbrev source := Spec (.of coordinateRing)

def projection : source ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ coordinateRing))

abbrev sourceOver : Over base := Over.mk projection

def gaussProjection : source ⟶ PrimitiveGaussGroupScheme.source :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : gaussRing →ₐ[ℂ] coordinateRing).toRingHom)

def fiberProjection : source ⟶ PrimitiveRhoFiberNondegenerate.nondegenerateDomain :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : fiberRing →ₐ[ℂ] coordinateRing).toRingHom)

@[reassoc] theorem gaussProjection_over :
    gaussProjection ≫ PrimitiveGaussGroupScheme.sourceProjection = projection := by
  rw [gaussProjection,PrimitiveGaussGroupScheme.sourceProjection,projection,
    ← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1

@[reassoc] theorem fiberProjection_over :
    fiberProjection ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ fiberRing)) = projection := by
  rw [fiberProjection,projection,← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (Algebra.TensorProduct.includeRight : fiberRing →ₐ[ℂ] coordinateRing).comp_algebraMap

def gaussOver : sourceOver ⟶ PrimitiveGaussGroupScheme.sourceOver :=
  Over.homMk gaussProjection gaussProjection_over

/-- The actual thirteen-parameter symplectic transformation on the actual tensor source. -/
def groupParameter : sourceOver ⟶ PrimitiveGrassmannianAction.group :=
  gaussOver ≫ PrimitiveGaussGroupScheme.gaussFamily

/-- The actual nondegenerate rho-plus-graph nine-plane on the same tensor source. -/
def fiberParameter : sourceOver ⟶ PrimitiveGrassmannianAction.overSpace :=
  Over.homMk (fiberProjection ≫ PrimitiveRhoFiberNondegenerate.map) (by
    change (fiberProjection ≫ PrimitiveRhoFiberNondegenerate.map) ≫
      GrassmannianCharts.projection ℂ 9 14 = projection
    rw [Category.assoc,PrimitiveRhoFiberNondegenerate.map_projection,fiberProjection_over])

/-- The actual native orbit-family map, formed by the genuine group-scheme action. -/
def family : sourceOver ⟶ PrimitiveGrassmannianAction.overSpace :=
  lift groupParameter fiberParameter ≫ PrimitiveGrassmannianAction.action

def map : source ⟶ GrassmannianCharts.space ℂ 9 14 := family.left

@[reassoc] theorem map_projection : map ≫ GrassmannianCharts.projection ℂ 9 14 = projection :=
  family.w

/-- The universal quotient class is the genuine inverse-precomposition action
on the original perpendicular-graph quotient class. -/
theorem map_pointClass : PrimitiveGrassmannianAction.pointClass map =
    PrimitiveFamilyFreeAction.transformPoints sourceOver
      (Sp6GroupScheme.pointsMulEquiv base sourceOver groupParameter)
      (PrimitiveGrassmannianAction.pointClass fiberParameter.left) :=
  PrimitiveGrassmannianAction.action_pointClass sourceOver groupParameter fiberParameter

/-- Every test-scheme point uses the same actual symplectic matrix and original quotient class. -/
theorem test_pointClass (T : Over base) (g : T ⟶ PrimitiveGrassmannianAction.group)
    (x : T ⟶ PrimitiveGrassmannianAction.overSpace) :
    PrimitiveGrassmannianAction.pointClass
        ((lift g x ≫ PrimitiveGrassmannianAction.action).left) =
      PrimitiveFamilyFreeAction.transformPoints T
        (Sp6GroupScheme.pointsMulEquiv base T g) (PrimitiveGrassmannianAction.pointClass x.left) :=
  PrimitiveGrassmannianAction.action_pointClass T g x

end M9Native.PrimitiveRadicalOrbitFamily
