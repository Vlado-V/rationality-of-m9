module

public import M9StacksIntegration.LagrangianTranslatedCharts
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth

/-!
# The actual LG inclusion is a genuine regular immersion

The actual translated affine-six charts prove smoothness of the actual
LG scheme. The ambient native Grassmannian is smooth. Stacks 067U
therefore proves regularity of their original closed inclusion. No lci,
normal-bundle, regular-section, or expected-codimension hypothesis is
supplied as data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Regularity concerns the literal zero-scheme inclusion of the actual
rank-three exterior-square section on the native Grassmannian. -/
theorem inclusion_isRegularImmersion :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion (inclusion K) := by
  letI : Smooth (grassmannianProjection K) := by
    change Smooth (AlgebraicGeometry.Grassmannian.schemeOver.over 3 6 (base K)).hom
    infer_instance
  letI : Smooth (inclusion K ≫ grassmannianProjection K) :=
    inferInstanceAs (Smooth (projection K))
  exact Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth
    (inclusion K) (grassmannianProjection K)

end M9Native.LagrangianDegree
