module

public import M9StacksIntegration.DirectC9TwoTerm
public import M9StacksIntegration.DirectC9OriginalPoint
public import M9StacksIntegration.DirectImageTwoTermPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField

/-!
# The actual C9 differential has the original curve's section kernels

A single genuine global rank-ten differential works at every actual
point over the original field. Proper-flat derived base change along
its actual graph identifies its kernel sections with H0 of the actual
degree-eight line on the ORIGINAL curve. No nonexistence premise over
an extension field or unrelated chosen fibre differential is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.CurvePower
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace M9Native.DirectC9FibreKernel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open DirectC9Bundles (E10 F10)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C)

/-- The actual proper-flat family commutes with the actual prescribed-point
base change whose source is the ORIGINAL curve. -/
def pointDerivedBaseChangeIso
    (p : Spec (.of k) ⟶ (power C 9).left) (hp : p ≫ (power C 9).hom = 𝟙 _) :
    (derivedPullback p.toLRSHom.toShHom).obj
      (derivedPushforwardModule (familyProjection C) (degreeEightLine C c₀)) ≅
        derivedPushforwardModule C.hom (DirectC9OriginalPoint.pointLine k C c₀ p hp) := by
  let L : (familySpace C).Modules := degreeEightLine C c₀
  letI hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L := degreeEightLine_isInvertible C c₀
  have hLF := isFinitePresentation_and_isFlatOver_of_isInvertible (familyProjection C) L hL
  exact (baseChangeDerivedPushforward (familyProjection C) p C.hom
    (DirectC9OriginalPoint.pointGraph k C p hp)
    (DirectC9OriginalPoint.pointGraph_isPullback k C p hp)
    (DirectC9FibreGeometry.projection_finitePresentation k C) inferInstance L hLF.1 hLF.2).some

/-- One actual global rank-ten differential has the correct actual section
kernel at every point over the original field. -/
theorem exists_global_originalFieldKernel (hg : genus C.hom = 9) :
    ∃ d : E10 k C c₀ ⟶ F10 k C c₀,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E10 k C c₀) 10 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (F10 k C c₀) 10 ∧
      ∀ (p : Spec (.of k) ⟶ (power C 9).left) (hp : p ≫ (power C 9).hom = 𝟙 _),
        Nonempty (cohomologyOverField k C.hom (DirectC9OriginalPoint.pointLine k C c₀ p hp) 0 ≅
          moduleSpecΓFunctor.obj (kernel ((Scheme.Modules.pullback p).map d))) := by
  obtain ⟨a,d,b,hT⟩ := DirectC9TwoTerm.exists_restrictionTriangle k C c₀ hg
  have hE := DirectC9Bundles.E10_rank k C c₀ hg
  have hF := DirectC9Bundles.F10_rank k C c₀
  refine ⟨d,hE,hF,fun p hp => ?_⟩
  let ebc := pointDerivedBaseChangeIso k C c₀ p hp
  let eK := (DirectImageTwoTermPullback.nonempty_pullback_homologyZeroIsoKernel
    p 10 10 hE hF a d b hT).some
  let H := DerivedCategory.homologyFunctor (Spec (.of k)).Modules 0
  exact ⟨(DerivedFibreOverField.sectionsHomologyDerivedPushforwardIso k C.hom
      (DirectC9OriginalPoint.pointLine k C c₀ p hp) 0).symm ≪≫
    moduleSpecΓFunctor.mapIso ((H.mapIso ebc).symm ≪≫ eK)⟩

end M9Native.DirectC9FibreKernel
