module

public import M9StacksIntegration.LagrangianLinearSectionEquations
public import M9StacksIntegration.LagrangianPluckerTrivialization
public import M9StacksIntegration.LagrangianPluckerGeneration

/-! Genuine determinant-line trivializations of the original incidence family.
Their fourteen actual coefficients are exactly the frozen primitive chart
functions, and consequently generate the unit ideal. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.LagrangianLinearSectionLineCharts
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianPluckerQuotient M9Native.LagrangianPluckerTrivialization
open M9Native.LagrangianAffineDeterminant M9Native.LagrangianLinearSections
open M9Native.LagrangianLinearSectionEquations M9Native.LinearIncidenceTensorCoordinates
open AlgebraicGeometry.Grassmannian
variable (K : Type u) [Field K]

def lineTrivialization {T : Scheme.{u}} [IsAffine T] (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    (Scheme.Modules.pullback f).obj (determinantLine K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules) :=
  M9Native.LagrangianPluckerGeneration.chartLineIso K f ι g hfg

theorem lineTrivialization_sections {T : Scheme.{u}} [IsAffine T] (f : T ⟶ space K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) (j : Fin 14) :
    unitCoordinate T ((lineTrivialization K f ι g hfg).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)))=
        M9Native.LagrangianPlucker.chartCoordinates K f ι g j := by
  exact M9Native.LagrangianPluckerGeneration.chartLineIso_primitive K f ι g hfg j

def ambientLineIso {T : Scheme.{u}} [IsAffine T] (f : T ⟶ ambient K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : ((f ≫ toLG K) ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules) :=
  asIso ((Scheme.Modules.pullbackComp f (toLG K)).hom.app (determinantLine K)) ≪≫
    lineTrivialization K (f ≫ toLG K) ι g hfg

theorem ambientLineIso_coefficients {T : Scheme.{u}} [IsAffine T] (f : T ⟶ ambient K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : ((f ≫ toLG K) ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    lineCoefficients K f (ambientLineIso K f ι g hfg)=
      M9Native.LagrangianPlucker.chartCoordinates K (f ≫ toLG K) ι g := by
  funext j
  exact (congrArg (fun s => unitCoordinate T
    ((lineTrivialization K (f ≫ toLG K) ι g hfg).hom.app ⊤ s))
    (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp f (toLG K)
      (determinantLine K) (primitiveSections K j))).trans
        (lineTrivialization_sections K (f ≫ toLG K) ι g hfg j)

theorem ambientLineIso_span [CharZero K] {T : Scheme.{u}} [IsAffine T] (f : T ⟶ ambient K)
    (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
    (hfg : ((f ≫ toLG K) ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=g ≫ chart 3 6 ι) :
    Ideal.span (Set.range (lineCoefficients K f (ambientLineIso K f ι g hfg)))=⊤ := by
  rw [ambientLineIso_coefficients]
  exact M9Native.LagrangianPlucker.chartCoordinates_span K (f ≫ toLG K) ι g hfg

end M9Native.LagrangianLinearSectionLineCharts
end
