module

public import M9StacksIntegration.LagrangianSectionGeneration
public import M9StacksIntegration.LagrangianPluckerTrivialization

/-!
# The actual fourteen-section Plucker quotient on native LG

The native affine matrix cover trivializes the genuine universal
determinant line.  In those trivializations its fourteen sections are the
checked primitive chart coordinates, whose ideal is the unit ideal.
Actual epimorphy is then descended along the actual open cover and is
transported to every test-scheme quotient by actual pullback isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianPluckerEpimorphism

open AlgebraicGeometry.Grassmannian
open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPluckerTrivialization LagrangianSectionGeneration LagrangianPullback
open LagrangianDeterminantSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Grassmannian.pullbackPresentation

variable (K : Type u) [Field K]

/-- The actual LG matrix-cover domains are closed subschemes of the
actual affine Grassmannian matrix charts. -/
theorem matrixCover_chart_isAffine (ι : Fin 3 ↪ Fin 6) :
    IsAffine ((LagrangianPlucker.matrixCover K).X ι) := by
  change IsAffine (pullback (inclusion K) (GrassmannianCharts.chartOver K 3 6 ι))
  infer_instance

/-- Pullback and actual determinant trivialization retain the original
finite free section map on every native matrix chart. -/
theorem chart_sectionMap {T : Scheme.{u}} (f : T ⟶ space K) (ι : Fin 3 ↪ Fin 6)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ inclusion K) ≫ pullback.snd _ _ = g ≫ chart 3 6 ι) :
    ((pullbackFreeIso f 14).inv ≫
        (Scheme.Modules.pullback f).map (primitiveDeterminantMap K)) ≫
          (chartDeterminantIso K f ι g hfg).hom =
      sectionMap T (Scheme.Modules.exteriorPower (freeOn T 3) 3)
        (primitiveSection T K (LagrangianPlucker.coefficientMap K f)
          (chartQuotientMap 3 6 ι g)) := by
  let sf := fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j)
  calc
    _ = sectionMap T ((Scheme.Modules.pullback f).obj (determinantLine K)) sf ≫
        (chartDeterminantIso K f ι g hfg).hom :=
      congrArg (fun q => q ≫ (chartDeterminantIso K f ι g hfg).hom)
        (sectionMap_pullback f (determinantLine K) (primitiveSections K))
    _ = sectionMap T (Scheme.Modules.exteriorPower (freeOn T 3) 3)
        (fun j => (chartDeterminantIso K f ι g hfg).hom.app ⊤ (sf j)) :=
      sectionMap_postcomp T sf (chartDeterminantIso K f ι g hfg).hom
    _ = _ := congrArg (sectionMap T (Scheme.Modules.exteriorPower (freeOn T 3) 3))
      (funext fun j => chartDeterminantIso_primitive K f ι g hfg j)

variable [CharZero K]

/-- Every actual affine matrix chart sees an epimorphic fourteen-section
map, because the literal primitive chart coordinates span the unit ideal. -/
theorem matrixCover_pullback_epi (ι : Fin 3 ↪ Fin 6) :
    Epi ((Scheme.Modules.pullback ((LagrangianPlucker.matrixCover K).f ι)).map
      (primitiveDeterminantMap K)) := by
  let T := (LagrangianPlucker.matrixCover K).X ι
  let f := (LagrangianPlucker.matrixCover K).f ι
  let g := LagrangianPlucker.matrixChartIntegral K ι
  have hfg : (f ≫ inclusion K) ≫ pullback.snd _ _ = g ≫ chart 3 6 ι :=
    LagrangianPlucker.matrixChartIntegral_diagram K ι
  let := matrixCover_chart_isAffine K ι
  let s := primitiveSection T K (LagrangianPlucker.coefficientMap K f) (chartQuotientMap 3 6 ι g)
  have hcoord : (fun j => freeDeterminantCoordinates T (s j)) =
      LagrangianPlucker.chartCoordinates K f ι g :=
    funext fun j => primitiveSection_freeCoordinates T K _ _ j
  have hspan : Ideal.span (Set.range (fun j => freeDeterminantCoordinates T (s j))) = ⊤ :=
    (congrArg (fun v => Ideal.span (Set.range v)) hcoord).trans
      (LagrangianPlucker.chartCoordinates_span K f ι g hfg)
  have hep := sectionMap_epi_of_span T s hspan
  have hc : Epi (((pullbackFreeIso f 14).inv ≫
      (Scheme.Modules.pullback f).map (primitiveDeterminantMap K)) ≫
        (chartDeterminantIso K f ι g hfg).hom) :=
    (chart_sectionMap K f ι g hfg).symm ▸ hep
  have hp : Epi ((pullbackFreeIso f 14).inv ≫
      (Scheme.Modules.pullback f).map (primitiveDeterminantMap K)) :=
    (epi_comp_iff_of_isIso _ (chartDeterminantIso K f ι g hfg).hom).mp hc
  exact (epi_comp_iff_of_epi (pullbackFreeIso f 14).inv _).mp hp

/-- The fourteen actual universal primitive sections generate the actual
native LG determinant line. -/
theorem primitiveDeterminantMap_epi : Epi (primitiveDeterminantMap K) := by
  apply epi_of_epi_pullback_cover (primitiveDeterminantMap K)
    (LagrangianPlucker.matrixCover K).f (fun x => (LagrangianPlucker.matrixCover K).exists_eq x)
  intro ι
  change Fin 3 ↪ Fin 6 at ι
  exact matrixCover_pullback_epi K ι

theorem primitiveSections_generatesStalks :
    Stacks.ProjectiveFromSections.GeneratesStalks (primitiveSections K) :=
  generatesStalks_of_sectionMap_epi (space K) (determinantLine K) (primitiveSections K)
    (primitiveDeterminantMap_epi K)

/-- The actual exterior-power comparison and actual quotient isomorphism
give the determinant transport on an arbitrary test scheme. -/
def determinantTransportIso {T : Scheme.{u}} (f : T ⟶ space K) {Q : T.Modules}
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    (Scheme.Modules.pullback f).obj (determinantLine K) ≅ Scheme.Modules.exteriorPower Q 3 :=
  exteriorPullbackIso f (quotientOnLG K).target 3 ≪≫
    (Scheme.Modules.exteriorPowerFunctor T 3).mapIso e

omit [CharZero K] in
theorem determinantTransportIso_primitive {T : Scheme.{u}} (f : T ⟶ space K) {Q : T.Modules}
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) (j : Fin 14) :
    (determinantTransportIso K f e).hom.app ⊤
        (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)) =
      primitiveSection T K (LagrangianPlucker.coefficientMap K f)
        ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom) j := by
  change (Scheme.Modules.exteriorPowerMap e.hom 3).app ⊤
    ((exteriorPullbackIso f (quotientOnLG K).target 3).hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j))) = _
  exact (congrArg ((Scheme.Modules.exteriorPowerMap e.hom 3).app ⊤)
    (LagrangianPrimitiveSectionsPullback.primitiveSections_pullback K f j)).trans
      (primitiveSection_postcomp T K (LagrangianPlucker.coefficientMap K f)
        (pullbackPresentation f (quotientOnLG K)).map e.hom j)

omit [CharZero K] in
theorem transported_sectionMap {T : Scheme.{u}} (f : T ⟶ space K) {Q : T.Modules}
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    ((pullbackFreeIso f 14).inv ≫
        (Scheme.Modules.pullback f).map (primitiveDeterminantMap K)) ≫
          (determinantTransportIso K f e).hom =
      sectionMap T (Scheme.Modules.exteriorPower Q 3)
        (primitiveSection T K (LagrangianPlucker.coefficientMap K f)
          ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom)) := by
  let sf := fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j)
  calc
    _ = sectionMap T ((Scheme.Modules.pullback f).obj (determinantLine K)) sf ≫
        (determinantTransportIso K f e).hom :=
      congrArg (fun q => q ≫ (determinantTransportIso K f e).hom)
        (sectionMap_pullback f (determinantLine K) (primitiveSections K))
    _ = sectionMap T (Scheme.Modules.exteriorPower Q 3)
        (fun j => (determinantTransportIso K f e).hom.app ⊤ (sf j)) :=
      sectionMap_postcomp T sf (determinantTransportIso K f e).hom
    _ = _ := congrArg (sectionMap T (Scheme.Modules.exteriorPower Q 3))
      (funext fun j => determinantTransportIso_primitive K f e j)

/-- The actual fourteen-section quotient is epimorphic on every test
scheme, after every actual commuting quotient-target isomorphism. -/
theorem primitiveSectionMap_epi {T : Scheme.{u}} (f : T ⟶ space K) {Q : T.Modules}
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    Epi (sectionMap T (Scheme.Modules.exteriorPower Q 3)
      (primitiveSection T K (LagrangianPlucker.coefficientMap K f)
        ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom))) := by
  let := primitiveDeterminantMap_epi K
  have h : Epi (((pullbackFreeIso f 14).inv ≫
      (Scheme.Modules.pullback f).map (primitiveDeterminantMap K)) ≫
        (determinantTransportIso K f e).hom) := inferInstance
  exact transported_sectionMap K f e ▸ h

theorem primitiveSection_generatesStalks {T : Scheme.{u}} (f : T ⟶ space K) {Q : T.Modules}
    (e : (pullbackPresentation f (quotientOnLG K)).target ≅ Q) :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (primitiveSection T K (LagrangianPlucker.coefficientMap K f)
        ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom)) :=
  generatesStalks_of_sectionMap_epi T (Scheme.Modules.exteriorPower Q 3) _
    (primitiveSectionMap_epi K f e)

end M9Native.LagrangianPluckerEpimorphism
