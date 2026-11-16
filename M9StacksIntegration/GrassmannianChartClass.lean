module

public import M9StacksIntegration.ConicFrameMap
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

/-! The native chart's literal quotient class, exposed for polynomial
families without changing the pinned chart definitions. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.GrassmannianChartClass

open AlgebraicGeometry.Grassmannian

variable {T : Scheme.{u}} (r n : ℕ) (ι : Fin (n-r) ↪ Fin n)

def normalized (g : T ⟶ coordinateChartScheme.{u} ι) : NormalizedQuotient T r n ι :=
  (normalizedQuotientCoefficientsEquiv T r n ι).symm
    (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} ι) g)

theorem chart_class (g : T ⟶ coordinateChartScheme.{u} ι) :
    (functorData r n).objEquiv T
      ((schemeRepresentableBy r n).homEquiv (g ≫ chart r n ι)) =
      ⟦normalizedQuotientPresentation T r n ι (normalized r n ι g)⟧ := by
  exact objEquiv_homEquiv_comp_chartMap r n ι g

theorem normalized_map (g : T ⟶ coordinateChartScheme.{u} ι) :
    (normalized r n ι g).val = chartQuotientMap r n ι g := by
  exact Eq.trans (Eq.refl ((normalized r n ι g).val)) (Eq.refl _)

end M9Native.GrassmannianChartClass
