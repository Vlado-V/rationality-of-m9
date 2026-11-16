module

public import M9StacksIntegration.FreeTwoProjectiveChartCoordinates
public import M9StacksIntegration.LagrangianSectionGeneration

/-!
# The two actual affine-line charts cover the original free-two projective bundle

The original tautological map is an actual epimorphism.  Its two original
basis sections therefore generate the tautological line at every stalk.
The native split-complement identity identifies their nonvanishing opens
with the two constructed charts, proving coverage of every scheme point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Chow Stacks.RelativeProj

universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
namespace M9Native.FreeTwoProjectiveChartCover

open FreeTwoCoordinates FreeTwoProjectiveCharts FreeTwoProjectiveChartCoordinates
open LagrangianMatrixChart SectionZeroIdealFactorization LagrangianPluckerQuotient

/-- The actual coordinate inclusions commute with canonical free pullback. -/
theorem pullback_inclusion {X P : Scheme.{u}} (p : P ⟶ X) (i : Fin 2) :
    (Scheme.Modules.pullbackUnitIso p).inv ≫
        (Scheme.Modules.pullback p).map (FreeTwoCoordinates.inclusion X i) =
      FreeTwoCoordinates.inclusion P i ≫
        (AlgebraicGeometry.Grassmannian.pullbackFreeIso p 2).inv := by
  let : (SheafOfModules.pushforward p.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).isRightAdjoint
  have h := AlgebraicGeometry.Grassmannian.pullback_map_ιFree_comp_pullbackFreeIso_hom p 2
    (ULift.up.{u} i)
  change (Scheme.Modules.pullback p).map (FreeTwoCoordinates.inclusion X i) ≫
      (AlgebraicGeometry.Grassmannian.pullbackFreeIso p 2).hom =
    (Scheme.Modules.pullbackUnitIso p).hom ≫ FreeTwoCoordinates.inclusion P i at h
  apply (cancel_mono (AlgebraicGeometry.Grassmannian.pullbackFreeIso p 2).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [h,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

variable (X : Scheme.{u})

abbrev nativeBundle : Scheme.{u} := projectiveBundle X (freeOn X 2)
abbrev nativeProjection : nativeBundle X ⟶ X := projectiveBundleToBase X (freeOn X 2)
abbrev nativeLine : (nativeBundle X).Modules := tautologicalDatumTwist (freeOn X 2)

/-- The actual presentation comparison, with the original source scheme retained in its type. -/
def presentationIso : projectiveBundleSpace X ≅ nativeBundle X :=
  bundlePresentationIso (freeOn X 2)

instance nativeLine_invertible : Stacks.Ample.IsInvertibleModule (nativeBundle X) (nativeLine X) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
    (isInvertible_tautologicalDatumTwist (freeOn X 2))

/-- The original two hyperplane sections of the native quotient presentation. -/
def nativeTautCoordinate (i : Fin 2) : Γ(nativeLine X, ⊤) :=
  hyperplaneSection (FreeTwoCoordinates.inclusion X i)

/-- The actual tautological quotient, with its source expressed in the
canonical actual free rank-two frame. -/
def nativeFreeQuotient : freeOn (nativeBundle X) 2 ⟶ nativeLine X :=
  (AlgebraicGeometry.Grassmannian.pullbackFreeIso (nativeProjection X) 2).inv ≫
    tautologicalDatumUniv (freeOn X 2)

instance nativeFreeQuotient_epi : Epi (nativeFreeQuotient X) := by
  dsimp [nativeFreeQuotient]
  infer_instance


/-- The two original section maps are the actual epimorphic quotient. -/
theorem native_sectionMap_eq :
    sectionMap (nativeBundle X) (nativeLine X) (nativeTautCoordinate X) = nativeFreeQuotient X := by
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan
      (R := (nativeBundle X).ringCatSheaf) (ULift.{u} (Fin 2))) _ _ (fun j => ?_)
  rcases j with ⟨j⟩
  change SheafOfModules.ιFree (R := (nativeBundle X).ringCatSheaf) (ULift.up.{u} j) ≫
      sectionMap (nativeBundle X) (nativeLine X) (nativeTautCoordinate X) =
    SheafOfModules.ιFree (R := (nativeBundle X).ringCatSheaf) (ULift.up.{u} j) ≫
      nativeFreeQuotient X
  rw [sectionMap_component]
  change Scheme.Modules.unitHomEquivTop (nativeLine X)
      (hyperplaneSection (FreeTwoCoordinates.inclusion X j)) = _
  rw [unitHomEquivTop_hyperplaneSection]
  dsimp only [hyperplaneSectionHom,nativeFreeQuotient]
  calc
    _ = ((Scheme.Modules.pullbackUnitIso (nativeProjection X)).inv ≫
        (Scheme.Modules.pullback (nativeProjection X)).map (FreeTwoCoordinates.inclusion X j)) ≫
          tautologicalDatumUniv (freeOn X 2) := (Category.assoc _ _ _).symm
    _ = (FreeTwoCoordinates.inclusion (nativeBundle X) j ≫
        (AlgebraicGeometry.Grassmannian.pullbackFreeIso (nativeProjection X) 2).inv) ≫
          tautologicalDatumUniv (freeOn X 2) :=
      congrArg (fun q => q ≫ tautologicalDatumUniv (freeOn X 2))
        (pullback_inclusion (nativeProjection X) j)
    _ = _ := Category.assoc _ _ _

theorem nativeTautCoordinate_generates :
    Stacks.ProjectiveFromSections.GeneratesStalks (nativeTautCoordinate X) := by
  apply LagrangianSectionGeneration.generatesStalks_of_sectionMap_epi
  rw [native_sectionMap_eq]
  infer_instance

/-- The actual native chart image is its actual native split complement. -/
theorem nativeChart_range (i : Fin 2) :
    Set.range (nativeChart X i) =
      (splitQuotientComplement (FreeTwoCoordinates.projection X (other i)) : Set (nativeBundle X)) := by
  rw [show nativeChart X i =
      ((splitting X i).splitQuotientComplementIso (singleBasis X)).inv ≫
        (splitQuotientComplement (FreeTwoCoordinates.projection X (other i))).ι from
    ((splitting X i).splitQuotientComplementIso_inv_ι (singleBasis X)).symm]
  change Set.range (Function.comp
    (splitQuotientComplement (FreeTwoCoordinates.projection X (other i))).ι
    ((splitting X i).splitQuotientComplementIso (singleBasis X)).inv) = _
  rw [Set.range_comp,Set.range_eq_univ.mpr
    ((splitting X i).splitQuotientComplementIso (singleBasis X)).inv.surjective,
    Set.image_univ,Scheme.Opens.range_ι]

/-- Every actual scheme point lies in one of the actual native charts. -/
theorem nativeCharts_cover (x : nativeBundle X) :
    ∃ i : Fin 2, x ∈ Set.range (nativeChart X i) := by
  obtain ⟨i,hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks
    (nativeTautCoordinate X) (nativeTautCoordinate_generates X) x
  change x ∈ Stacks.Ample.nonvanishingLocus (nativeLine X)
    (hyperplaneSection (FreeTwoCoordinates.inclusion X i)) at hi
  rw [nonvanishingLocus_hyperplaneSection
    (FreeTwoCoordinates.projection X (other i)) (FreeTwoCoordinates.inclusion X i)
    (FreeTwoCoordinates.projection X i) (FreeTwoCoordinates.inclusion X (other i))
    (splitting_identity X i) (inclusion_projection_other X i)] at hi
  refine ⟨i,?_⟩
  rw [nativeChart_range]
  exact hi

set_option maxHeartbeats 800000 in
/-- The two actual charts cover the SAME original Chow/incidence projective bundle. -/
theorem charts_cover (x : projectiveBundleSpace X) :
    ∃ i : Fin 2, x ∈ Set.range (chart X i) := by
  obtain ⟨i,z,hz⟩ := nativeCharts_cover X ((presentationIso X).hom x)
  refine ⟨i,z,?_⟩
  change (presentationIso X).inv (nativeChart X i z) = x
  rw [hz]
  exact congrArg (fun f : projectiveBundleSpace X ⟶ projectiveBundleSpace X => f x)
    (presentationIso X).hom_inv_id

/-- A genuine native open cover, with no geometric or reducedness premise on X. -/
def chartCover : (projectiveBundleSpace X).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2) (fun _ => chartSpace X) (chart X)
    (fun x => by
      obtain ⟨i,z,hz⟩ := charts_cover X x
      exact ⟨i,z,hz⟩)

end M9Native.FreeTwoProjectiveChartCover
