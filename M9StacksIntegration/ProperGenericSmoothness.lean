module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# A proper morphism with regular source is generically smooth in characteristic zero

The generic-fibre inclusion is a flat preimmersion, hence identifies its actual
local rings with local rings of the source. Regularity and perfection of the
generic residue field imply smoothness of that entire fibre. Properness then
makes the image of the closed nonsmooth locus a closed subset missing the generic
point, giving a genuine nonempty open of the target over which the original
morphism is smooth.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.ProperGenericSmoothness

variable {X Y : Scheme.{u}} [IsIntegral Y]

/-- The actual generic-point morphism of an integral scheme is flat. -/
theorem flat_fromSpecResidueField_genericPoint :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  have : IsIso (Y.residue (genericPoint Y)) := isIso_residue_genericPoint Y
  have : Flat (Y.fromSpecStalk (genericPoint Y)) := flat_fromSpecStalk Y _
  change Flat (Spec.map (Y.residue (genericPoint Y)) ≫ Y.fromSpecStalk (genericPoint Y))
  infer_instance

/-- Every actual local ring on the generic fibre is the corresponding source local ring. -/
theorem genericFiber_stalkMap_isIso (f : X ⟶ Y) (x : f.fiber (genericPoint Y)) :
    IsIso ((f.fiberι (genericPoint Y)).stalkMap x) := by
  have : Flat (Y.fromSpecResidueField (genericPoint Y)) := flat_fromSpecResidueField_genericPoint
  have : Flat (f.fiberι (genericPoint Y)) := inferInstanceAs (Flat (pullback.fst _ _))
  exact isIso_stalkMap_of_flat_isPreimmersion (f.fiberι (genericPoint Y)) x

/-- Regularity on an actual affine neighbourhood gives regularity of the actual stalk. -/
theorem regularLocal_stalk (hX : IsRegular X) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U,hxU,hU⟩ := hX x
  let := X.presheaf.algebra_section_stalk ⟨x,hxU⟩
  have := U.2.isLocalization_stalk ⟨x,hxU⟩
  have : IsRegularRing Γ(X,U) := hU
  exact IsRegularRing.isRegularLocalRing_of_isLocalization
    (U.2.primeIdealOf ⟨x,hxU⟩).asIdeal (X.presheaf.stalk x)

/-- A regular source has a smooth actual generic fibre when the generic residue field is perfect. -/
theorem smooth_genericFiber (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hX : IsRegular X) [PerfectField (Y.residueField (genericPoint Y))] :
    Smooth (f.fiberToSpecResidueField (genericPoint Y)) := by
  have : LocallyOfFinitePresentation (f.fiberToSpecResidueField (genericPoint Y)) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f (Y.fromSpecResidueField _)))
  rw [← Scheme.Hom.smoothLocus_eq_top_iff,eq_top_iff]
  intro x _
  have : IsRegularLocalRing (X.presheaf.stalk (f.fiberι (genericPoint Y) x)) :=
    regularLocal_stalk hX _
  have : IsIso ((f.fiberι (genericPoint Y)).stalkMap x) := genericFiber_stalkMap_isIso f x
  have hreg : IsRegularLocalRing ((f.fiber (genericPoint Y)).presheaf.stalk x) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((f.fiberι (genericPoint Y)).stalkMap x)).commRingCatIsoToRingEquiv
  let : Algebra (Y.residueField (genericPoint Y)) ((f.fiber (genericPoint Y)).residueField x) :=
    ((Scheme.ΓSpecIso (Y.residueField (genericPoint Y))).inv ≫
      (f.fiberToSpecResidueField (genericPoint Y)).appTop ≫
      (f.fiber (genericPoint Y)).Γevaluation x).hom.toAlgebra
  have hsep : Algebra.IsSeparableExtension (Y.residueField (genericPoint Y))
      ((f.fiber (genericPoint Y)).residueField x) := by
    have : Algebra.FormallySmooth (Y.residueField (genericPoint Y))
        ((f.fiber (genericPoint Y)).residueField x) := Algebra.formallySmooth_of_perfectField _ _
    exact Algebra.FormallySmooth.isSeparableExtension _ _
  have hsm := (smoothAt_iff_isRegularLocalRing_stalk
    (f.fiberToSpecResidueField (genericPoint Y)) x hsep).mpr hreg
  exact Scheme.Hom.mem_smoothLocus.mpr (hsm.formallySmooth_stalkMap _ _)

/-- Every point over the generic point is in the actual smooth locus. -/
theorem generic_preimage_subset_smoothLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hX : IsRegular X) [PerfectField (Y.residueField (genericPoint Y))] :
    f ⁻¹' {genericPoint Y} ⊆ (f.smoothLocus : Set X) := by
  have : Flat (Y.fromSpecResidueField (genericPoint Y)) := flat_fromSpecResidueField_genericPoint
  have : LocallyOfFinitePresentation (f.fiberToSpecResidueField (genericPoint Y)) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f (Y.fromSpecResidueField _)))
  have : Smooth (f.fiberToSpecResidueField (genericPoint Y)) := smooth_genericFiber f hX
  rw [← f.range_fiberι]
  rintro _ ⟨y,rfl⟩
  have hy : y ∈ (f.fiberToSpecResidueField (genericPoint Y)).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have hsq : IsPullback (f.fiberι (genericPoint Y)) (f.fiberToSpecResidueField (genericPoint Y))
      f (Y.fromSpecResidueField (genericPoint Y)) := IsPullback.of_hasPullback _ _
  rw [Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inr inferInstance)] at hy
  exact hy

/-- Properness removes the images of all nonsmooth points at once. -/
theorem exists_nonempty_open_smooth (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (hX : IsRegular X) [PerfectField (Y.residueField (genericPoint Y))] :
    ∃ U : Y.Opens,(U : Set Y).Nonempty ∧ Smooth (f ∣_ U) ∧ IsProper (f ∣_ U) := by
  let U : Y.Opens := ⟨(f '' ((f.smoothLocus : Set X)ᶜ))ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩
  have hη : genericPoint Y ∈ U := by
    rintro ⟨x,hx,hfx⟩
    exact hx (generic_preimage_subset_smoothLocus f hX (by simpa only [Set.mem_preimage,
      Set.mem_singleton_iff] using hfx))
  have hpre : ((f ⁻¹ᵁ U : X.Opens) : Set X) ⊆ (f.smoothLocus : Set X) := by
    intro x hx
    by_contra hxs
    exact hx ⟨x,hxs,rfl⟩
  have hsm : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,← Scheme.Hom.preimage_smoothLocus_eq,eq_top_iff]
    exact fun x _ => hpre x.2
  refine ⟨U,⟨genericPoint Y,hη⟩,?_,inferInstance⟩
  exact MorphismProperty.of_postcomp (@Smooth) (W':=MorphismProperty.monomorphisms Scheme)
    (f ∣_ U) U.ι inferInstance (by rw [morphismRestrict_ι];exact hsm)

/-- Characteristic zero makes the actual generic residue field perfect. -/
theorem exists_nonempty_open_smooth_of_charZero (K : Type u) [Field K] [CharZero K]
    (sY : Y ⟶ Spec (.of K)) (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (hX : IsRegular X) :
    ∃ U : Y.Opens,(U : Set Y).Nonempty ∧ Smooth (f ∣_ U) ∧ IsProper (f ∣_ U) := by
  let : Algebra K (Y.residueField (genericPoint Y)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ sY.appTop ≫ Y.Γevaluation (genericPoint Y)).hom.toAlgebra
  have : CharZero (Y.residueField (genericPoint Y)) :=
    charZero_of_injective_algebraMap (algebraMap K (Y.residueField (genericPoint Y))).injective
  exact exists_nonempty_open_smooth f hX

/-- A proper morphism from an actual smooth scheme to an integral characteristic-zero
base is smooth over a genuine nonempty open of that base. -/
theorem exists_nonempty_open_smooth_of_smooth_over_charZero
    (K : Type u) [Field K] [CharZero K] (sX : X ⟶ Spec (.of K)) [Smooth sX]
    (sY : Y ⟶ Spec (.of K)) (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f] :
    ∃ U : Y.Opens,(U : Set Y).Nonempty ∧ Smooth (f ∣_ U) ∧ IsProper (f ∣_ U) :=
  exists_nonempty_open_smooth_of_charZero K sY f (isRegular_of_smooth_over_field sX)

/-- Dominance and properness ensure that the resulting smooth family still has nonempty fibres. -/
theorem exists_nonempty_open_smooth_surjective (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    [IsProper f] [IsDominant f] (hX : IsRegular X)
    [PerfectField (Y.residueField (genericPoint Y))] :
    ∃ U : Y.Opens,(U : Set Y).Nonempty ∧ Smooth (f ∣_ U) ∧ IsProper (f ∣_ U) ∧
      Surjective (f ∣_ U) := by
  obtain ⟨U,hU,hsm,hproper⟩ := exists_nonempty_open_smooth f hX
  have : Surjective f := inferInstance
  refine ⟨U,hU,hsm,hproper,?_⟩
  dsimp only [morphismRestrict]
  infer_instance

end M9Native.ProperGenericSmoothness

end
