module

public import M9StacksIntegration.MukaiThreeGeneratorRecognition
public import M9StacksIntegration.MukaiRecognitionHomBound

/-!
# Three determinant sections from the original three generators

Dualizing the actual sequence of a three-generator rank-two bundle
produces an epimorphism onto its determinant. Absence of maps from the
original bundle to the structure sheaf makes its three actual generator
sections independent. No complete basis, section count, or degree is
assumed. This extracts the part of native three-generator recognition
that precedes its use of a complete basis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiThreeGeneratorDeterminantSections

section Constants

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- The actual dual sequence constructs an epimorphism onto the genuine
determinant line with three independent original-field sections. -/
theorem exists_independent_generator_sections (F β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (q : netFree X ⟶ F) [Epi q]
    (hdet : topExterior F 2 ≅ β)
    (hvan : ∀ a : F ⟶ structureModule X, a = 0) :
    letI := modulesLinearOverField k f
    ∃ p : netFree X ⟶ β, Epi p ∧
      LinearIndependent k (fun i : ULift.{u} (Fin 3) =>
        (MukaiPencilQuotient.sectionHomLinearEquiv f β).symm
          (SheafOfModules.ιFree i ≫ p)) := by
  classical
  letI := modulesLinearOverField k f
  let O : X.Modules := structureModule X
  let N : X.Modules := netFree X
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (netFree X) 3 := netFree_rank X
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (netFree X) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (netFree X) 3
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
      q inferInstance 3 2 inferInstance inferInstance
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel q) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (kernel q) 1
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} β 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} β :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree β 1
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  let hprod : tensor (kernel q) β ≅ structureModule X :=
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf (kernel q)).symm hdet.symm ≪≫
      Scheme.Modules.exteriorPowerTensorExteriorPowerIso
        (kernel.ι q) q (kernel.condition q) hS 1 1 ≪≫
      freeTopExteriorIso 3 (netFree X) (Iso.refl _)
  let eZ : kernel q ≅ dualSheaf β :=
    tensorInverseNativeIso β (kernel q)
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.property
        β (kernel q) ≪≫ hprod)
  letI := isIso_toDoubleDual_of_isFiniteLocallyFree β
  let eZdual : dualSheaf (kernel q) ≅ β :=
    (MukaiPencilQuotient.dualIso eZ).symm ≪≫ (asIso (toDoubleDual β)).symm
  obtain ⟨wd, hD⟩ := exists_dualSheaf_shortExact
    (kernel.ι q) q (kernel.condition q) hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 inferInstance)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 inferInstance)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 inferInstance)
  let eFree := dualNetFreeIso X
  let i : dualSheaf F ⟶ netFree X := dualMap q ≫ eFree.hom
  let p : netFree X ⟶ β := eFree.inv ≫ dualMap (kernel.ι q) ≫ eZdual.hom
  have w : i ≫ p = 0 := by
    calc
      i ≫ p = (dualMap q ≫ dualMap (kernel.ι q)) ≫ eZdual.hom := by
        simp [i, p, Category.assoc]
      _ = 0 := by rw [wd, zero_comp]
  let T := ShortComplex.mk i p w
  let eT : ShortComplex.mk (dualMap q) (dualMap (kernel.ι q)) wd ≅ T :=
    ShortComplex.isoMk (Iso.refl _) eFree eZdual
      (by simp [T, i]) (by simp [T, p])
  have hT : T.ShortExact := ShortComplex.shortExact_of_iso eT hD
  letI : Mono T.f := hT.mono_f
  letI : Subsingleton (F ⟶ structureModule X) :=
    ⟨fun a b => (hvan a).trans (hvan b).symm⟩
  let eH : (structureModule X ⟶ dualSheaf F) ≃ₗ[k] (F ⟶ structureModule X) :=
    (unitHomLinearEquivCohomologyZero k f (dualSheaf F)).trans
      (MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f F (structureModule X)).symm
  letI : Subsingleton (structureModule X ⟶ dualSheaf F) :=
    ⟨fun a b => eH.injective (Subsingleton.elim _ _)⟩
  let P : (O ⟶ N) →ₗ[k] (O ⟶ β) :=
    { toFun := fun a => a ≫ p
      map_add' := fun a b => by simp only [Preadditive.add_comp]
      map_smul' := fun c a => by simp [Linear.smul_comp] }
  have hP : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro a ha
    change a = 0
    change a ≫ p = 0 at ha
    let t := hT.exact.lift a ha
    have ht : t ≫ i = a := hT.exact.lift_f a ha
    have ht0 : t = 0 := Subsingleton.elim _ _
    exact ht.symm.trans (by rw [ht0, zero_comp])
  let eSec := MukaiPencilQuotient.sectionHomLinearEquiv f β
  refine ⟨p, hT.epi_g, ?_⟩
  exact ((MukaiThreeGeneratorRecognition.freeInclusions_linearIndependent k f).map'
    P (LinearMap.ker_eq_bot.mpr hP)).map'
      eSec.symm.toLinearMap (LinearMap.ker_eq_bot.mpr eSec.symm.injective)

/-- Properness supplies finite-dimensionality; the actual independent
determinant sections then give the lower bound without a basis input. -/
theorem three_le_h0_of_three_generators [IsProper f] (F β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (q : netFree X ⟶ F) [Epi q]
    (hdet : topExterior F 2 ≅ β)
    (hvan : ∀ a : F ⟶ structureModule X, a = 0) :
    3 ≤ Module.finrank k (cohomologyOverField k f β 0) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} β 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f β 1
  obtain ⟨p, hp, hs⟩ := exists_independent_generator_sections k f F β q hdet hvan
  simpa using hs.fintype_card_le_finrank

end Constants

/-- On the actual algebraically closed proper curve the native constants
isomorphism is derived, leaving only the given bundle and actual maps. -/
theorem three_le_h0_of_three_generators_on_curve
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (F β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (q : netFree X ⟶ F) [Epi q]
    (hdet : topExterior F 2 ≅ β)
    (hvan : ∀ a : F ⟶ structureModule X, a = 0) :
    3 ≤ Module.finrank k (cohomologyOverField k f β 0) := by
  letI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  exact three_le_h0_of_three_generators k f F β q hdet hvan

end M9Native.MukaiThreeGeneratorDeterminantSections
