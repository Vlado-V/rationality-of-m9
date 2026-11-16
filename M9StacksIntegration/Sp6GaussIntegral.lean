module

public import M9StacksIntegration.Sp6GaussTranslatedCharts
public import M9StacksIntegration.Sp6GaussChartDomain
public import M9StacksIntegration.Sp6IntegerAlgebraCoherence

/-!
# Integrality of the original symplectic group

The actual eight Gauss opens are integral and share the literal upper(I)
point. They cover every scheme point, so irreducibility and reducedness
glue to the original group. The original affine algebra is a domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace M9Native.Sp6GaussIntegral

open Sp6GaussTranslatedCharts (source group chart admissibleCover)
open LagrangianAdmissibleMinors (Choice)

variable (K : Type u) [Field K]

theorem source_eq_domainSpec : source K =
    Spec (.of (Sp6GaussChartDomain.ChartCoordinateRing K)) := by
  have h := Sp6IntegerAlgebraCoherence.tensorObject_eq K
    Sp6GaussCellCoordinates.CoordinateRing
    (Sp6AffineBaseChange.integerAlgebra K) (Sp6AffineBaseChange.integerAlgebra K)
    (Sp6AffineBaseChange.integerAlgebra Sp6GaussCellCoordinates.CoordinateRing)
    (inferInstance : Algebra Sp6AffineBaseChange.IntegerRing Sp6GaussCellCoordinates.CoordinateRing)
  exact congrArg (fun B : CommRingCat => Spec B) h

instance source_integral : IsIntegral (source K) := by
  rw [source_eq_domainSpec]
  exact Sp6GaussChartDomain.chartBaseChange_integral K

theorem chart_range_irreducible (s : Choice) : IsIrreducible (Set.range (chart K s)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (source K)).image
      (chart K s) (chart K s).continuous.continuousOn

instance group_irreducible : IrreducibleSpace (group K) := by
  obtain ⟨x,hx⟩ := Sp6GaussTranslatedCharts.exists_point_in_all_charts K
  exact irreducibleSpace_of_isOpen_cover (fun s : Choice => Set.range (chart K s))
    (fun s => (chart K s).isOpenEmbedding.isOpen_range)
    (chart_range_irreducible K) (Sp6GaussTranslatedCharts.charts_cover K) x hx

instance group_reduced : IsReduced (group K) := by
  have (s : (admissibleCover K).I₀) : IsReduced ((admissibleCover K).X s) := by
    change IsReduced (source K)
    infer_instance
  exact IsReduced.of_openCover (group K) (admissibleCover K)

/-- Integrality concerns the actual original group, over every field. -/
instance group_integral : IsIntegral (group K) :=
  isIntegral_of_irreducibleSpace_of_isReduced (group K)

instance affineSpec_integral :
    IsIntegral (Spec (.of (Sp6AffineBaseChange.CoordinateRing K))) :=
  IsIntegral.of_isIso (Sp6AffineBaseChange.affineIso K).inv

/-- The original affine tensor coordinate algebra has no zero divisors. -/
instance coordinate_isDomain : IsDomain (Sp6AffineBaseChange.CoordinateRing K) :=
  (affine_isIntegral_iff (.of (Sp6AffineBaseChange.CoordinateRing K))).mp inferInstance

instance group_projection_geometricallyIrreducible [IsSepClosed K] :
    GeometricallyIrreducible (Sp6GroupScheme.obj (Spec (.of K))).hom :=
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K (group K) _

instance group_projection_geometricallyIntegral [IsSepClosed K] [PerfectField K] :
    GeometricallyIntegral (Sp6GroupScheme.obj (Spec (.of K))).hom :=
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

instance affine_projection_geometricallyIrreducible [IsSepClosed K] :
    GeometricallyIrreducible (Sp6AffineBaseChange.projection K) :=
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K
    (Spec (.of (Sp6AffineBaseChange.CoordinateRing K))) _

instance affine_projection_geometricallyIntegral [IsSepClosed K] [PerfectField K] :
    GeometricallyIntegral (Sp6AffineBaseChange.projection K) :=
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- Every actual field extension tensor of the original algebra is a
 domain; no density or reducedness premise is introduced. -/
theorem tensor_isDomain [IsSepClosed K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] :
    IsDomain (Sp6AffineBaseChange.CoordinateRing K ⊗[K] L) := by
  let f := Spec.map (CommRingCat.ofHom
    (algebraMap K (Sp6AffineBaseChange.CoordinateRing K)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  haveI : GeometricallyIntegral f := affine_projection_geometricallyIntegral K
  haveI : IsIntegral (pullback f g) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) g
      (pullback.fst f g) (pullback.snd f g) (.of_hasPullback f g)
  haveI : IsIntegral (Spec (.of (Sp6AffineBaseChange.CoordinateRing K ⊗[K] L))) :=
    IsIntegral.of_isIso (pullbackSpecIso K (Sp6AffineBaseChange.CoordinateRing K) L).hom
  exact (affine_isIntegral_iff
    (.of (Sp6AffineBaseChange.CoordinateRing K ⊗[K] L))).mp inferInstance

end M9Native.Sp6GaussIntegral
