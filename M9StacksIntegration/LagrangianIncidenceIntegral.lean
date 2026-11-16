module

public import M9StacksIntegration.LagrangianIncidenceFibreQuotient
public import M9StacksIntegration.GrassmannianFixedLine
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth
public import M9StacksIntegration.IteratedLineSectionCuts
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Integrality of the original universal LG incidence

Each actual field fibre over LG is the native Grassmannian Gr(8,13):
the actual rank-five quotient kills the actual nonzero Pluecker line.
The comparison uses the original all-test zero ideal, including nilpotents.
Smoothness and the integral LG base then give the integral total incidence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianIncidenceIntegral

open LagrangianLinearSections LagrangianIncidenceFieldFrame
open LagrangianIncidenceFibreQuotient IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K]

/-- The actual incidence fibre and the actual fixed-line Grassmannian
represent the same subfunctor of the native field Grassmannian. -/
def fibreIsoGrassOfFrame (L : Type u) [Field L]
    (x : Spec (.of L) ⟶ LagrangianGrassmannian.space K)
    (e : (Scheme.Modules.pullback x).obj (LagrangianPluckerQuotient.determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules))
    (hv : fieldCoefficients K L x e ≠ 0) :
    fibre K L x ≅ GrassmannianCharts.space L 8 13 := by
  let A : Over (parameter L) := Over.mk (toParameter K L x)
  let B : Over (parameter L) :=
    Over.mk (GrassmannianFixedLine.map L (fieldCoefficients K L x e) hv)
  letI : Mono A.hom := toParameter_mono K L x
  letI : Mono B.hom := GrassmannianFixedLine.map_mono L (fieldCoefficients K L x e) hv
  exact comparisonIso A B (fun T q =>
    (LagrangianIncidenceFibreQuotient.factorsThrough_iff_column_zero K L x q e).trans
      (GrassmannianFixedLine.factorsThrough_iff_column_zero L
        (fieldCoefficients K L x e) hv q).symm)

/-- No field-point frame or fibre identification is a premise: both are
constructed from the actual nonzero Pluecker system. -/
def fibreIsoGrass (L : Type u) [Field L]
    (x : Spec (.of L) ⟶ LagrangianGrassmannian.space K) :
    fibre K L x ≅ GrassmannianCharts.space L 8 13 :=
  fibreIsoGrassOfFrame K L x
    (Classical.choose (exists_frame_coefficients_ne_zero K L x))
    (Classical.choose_spec (exists_frame_coefficients_ne_zero K L x))

theorem fibre_irreducible (L : Type u) [Field L]
    (x : Spec (.of L) ⟶ LagrangianGrassmannian.space K) :
    IrreducibleSpace (pullback (C := Scheme.{u}) (familyToLG K) x) :=
  (fibreIsoGrass K L x).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

instance familyToLG_geometricallyIrreducible : GeometricallyIrreducible (familyToLG K) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ x
  exact fibre_irreducible K L x

instance family_irreducible : IrreducibleSpace (family K) :=
  GeometricallyIrreducible.irreducibleSpace (familyToLG K) (familyToLG K).isOpenMap

/-- The total original incidence is genuinely integral.  Reducedness is
derived from its proved smooth absolute projection. -/
instance family_integral : IsIntegral (family K) := by
  let : AlgebraicGeometry.IsNormal (family K) :=
    isNormal_of_isRegular (family K) (LagrangianLinearSectionGenericSmooth.family_regular K)
  exact isIntegral_of_irreducibleSpace_of_isReduced (family K)

end M9Native.LagrangianIncidenceIntegral

end
