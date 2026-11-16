module

public import M9StacksIntegration.LagrangianKernelFivePullback
public import M9StacksIntegration.LagrangianTranslatedDeterminantSections

/-!
# Literal five-minor coordinates in the genuine translated frame

The actual exterior pullback and quotient-frame maps retain every raw
ordered minor. Thus the original five determinant sections are the
literal five polynomial minors in every actual translated chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.LagrangianTranslatedFiveMinorSections

open AlgebraicGeometry.Grassmannian LagrangianGrassmannian LagrangianMatrixChart
open LagrangianPluckerQuotient LagrangianPluckerEpimorphism LagrangianDeterminantSections
open LagrangianPullback LagrangianKernelFivePullback LagrangianKernelFiveMinorNormalization
open LagrangianTranslatedDeterminantSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable (k : Type u) [Field k]

/-- Genuine target transport retains every actual ordered universal minor. -/
theorem determinantTransportIso_minor {T : Scheme.{u}} (l : T ⟶ space k) {Q : T.Modules}
    (e : (pullbackPresentation l (quotientOnLG k)).target ≅ Q) (c : Fin 3 ↪ Fin 6) :
    (determinantTransportIso k l e).hom.app ⊤
      (pullbackGlobalSections l (determinantLine k)
        (minorSection (space k) (quotientOnLG k).map c)) =
      minorSection T ((pullbackPresentation l (quotientOnLG k)).map ≫ e.hom) c := by
  change (Scheme.Modules.exteriorPowerMap e.hom 3).app ⊤
    ((exteriorPullbackIso l (quotientOnLG k).target 3).hom.app ⊤
      (pullbackGlobalSections l (determinantLine k)
        (minorSection (space k) (quotientOnLG k).map c))) = _
  exact (congrArg ((Scheme.Modules.exteriorPowerMap e.hom 3).app ⊤)
    (LagrangianDeterminantPullback.minorSection_pullback l (quotientOnLG k) c)).trans
      (minorSection_postcomp T (pullbackPresentation l (quotientOnLG k)).map e.hom c)

variable [CharZero k] (g : Matrix.symplecticGroup (Fin 3) k)

/-- The actual original determinant frame sends a minor to its literal polynomial determinant. -/
theorem translatedDeterminantIso_minor (c : Fin 3 ↪ Fin 6) :
    (translatedDeterminantIso k g).hom.app ⊤
      (pullbackGlobalSections (LagrangianTranslatedCharts.translatedBigCell k g) (determinantLine k)
        (minorSection (space k) (quotientOnLG k).map c)) =
      MukaiConormalBigCellSections.scalarEquiv k
        (Matrix.det ((translatedMatrix k g).submatrix id c)) := by
  change (LagrangianAffineDeterminant.affineDeterminantIso _).hom.app ⊤
    ((determinantTransportIso k (LagrangianTranslatedCharts.translatedBigCell k g)
      (translatedQuotientIso k g)).hom.app ⊤
      (pullbackGlobalSections (LagrangianTranslatedCharts.translatedBigCell k g) (determinantLine k)
        (minorSection (space k) (quotientOnLG k).map c))) = _
  rw [determinantTransportIso_minor, LagrangianAffineDeterminant.affineDeterminantIso_coordinate,
    minorSection_freeCoordinates, translatedQuotientIso_matrix]
  exact (RingHom.map_det (MukaiConormalBigCellSections.scalarEquiv k).toRingHom
    ((translatedMatrix k g).submatrix id c)).symm

/-- No coordinate normalization is supplied: these are the actual five original sections. -/
theorem translatedFiveSections_coordinate (a : Fin 5) :
    (translatedDeterminantIso k g).hom.app ⊤
      (pulledFiveSections k (LagrangianTranslatedCharts.translatedBigCell k g) a) =
      MukaiConormalBigCellSections.scalarEquiv k
        (Matrix.det ((translatedMatrix k g).submatrix id (fiveMinor a))) :=
  translatedDeterminantIso_minor k g (fiveMinor a)

end M9Native.LagrangianTranslatedFiveMinorSections
