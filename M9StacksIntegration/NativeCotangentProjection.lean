module

public import M9StacksIntegration.StandardSmoothCotangentProjection
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCokernelDerivation

/-!
# The original cotangent chain projection and the original cokernel isomorphism

The homology normalization and the differential normalization use the
same original canonical conormal sequence. Their degree-zero projections
therefore agree by the actual double-complex homology computation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace M9Native.NativeCotangentProjection

section Site

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The original class map followed by original homology coordinates is
exactly the original cokernel projection in differential coordinates. -/
theorem class_comp_homologyIso :
    CochainCokernelProjection.toHomology (naiveCotangentComplex.{u,u,u,u} J A B a)
        (HomologicalComplex.double_d_eq_zero₀
          (canonicalConormalSequence.{u,u,u,u} J A B a).f
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)
          0 ((ComplexShape.up ℤ).next 0) (by decide)) ≫
      (Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso.{u,u,u,u} J A B a).hom =
      cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0) ≫
        (naiveCotangentCokernelIso.{u,u,u,u} J A B a).hom := by
  have h₀ :
      CochainCokernelProjection.toHomology (naiveCotangentComplex.{u,u,u,u} J A B a)
          (HomologicalComplex.double_d_eq_zero₀
          (canonicalConormalSequence.{u,u,u,u} J A B a).f
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)
          0 ((ComplexShape.up ℤ).next 0) (by decide)) ≫
        (naiveCotangentComplexHomologyZeroIsoCokernel.{u,u,u,u} J A B a).hom =
      eqToHom (naiveCotangentComplex_X_zero.{u,u,u,u} J A B a) ≫
        cokernel.π (canonicalConormalSequence.{u,u,u,u} J A B a).f :=
    CochainCokernelProjection.toHomology_doubleIso
      (canonicalConormalSequence.{u,u,u,u} J A B a).f
  have hπ :
      cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0) ≫
        (naiveCotangentCokernelIsoConormal.{u,u,u,u} J A B a).hom =
      eqToHom (naiveCotangentComplex_X_zero.{u,u,u,u} J A B a) ≫
        cokernel.π (canonicalConormalSequence.{u,u,u,u} J A B a).f := by
    simp [naiveCotangentCokernelIsoConormal]
  simp only [Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso,
    naiveCotangentCokernelIso, Iso.trans_hom, ← Category.assoc]
  rw [h₀, hπ]

end Site

namespace Ringed

variable {X S : RingedSpace.{u,u}} (f : X ⟶ S)

/-- The literal final native transport from site differentials to the
original ringed-space differential object. -/
def siteDifferentialsIso :
    AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u,u,u,u}
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) ≅
    AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u,u,u}
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) :=
  eqToIso (AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite_eq_moduleOfDifferentials
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f))

/-- The original projection keeps the original cokernel isomorphism and
the original explicit site-to-ringed differential transport. -/
theorem complexProjection_f_zero :
    (StandardSmoothCotangentProjection.Ringed.complexProjection f).f 0 =
      cokernel.π ((RingedSpace.naiveCotangentComplex f).d (-1) 0) ≫
        (naiveCotangentCokernelIso.{u,u,u,u} (Opens.grothendieckTopology X.carrier)
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)).hom ≫
        (siteDifferentialsIso f).hom ≫
        (HomologicalComplex.singleObjXSelf (V := RingedSpace.siteModules X) (ComplexShape.up ℤ) 0 _).inv := by
  rw [StandardSmoothCotangentProjection.Ringed.complexProjection_f_zero]
  have h := class_comp_homologyIso (Opens.grothendieckTopology X.carrier)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)
  have ht := congrArg (fun t : (RingedSpace.naiveCotangentComplex f).X 0 ⟶
      AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u,u,u,u}
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) =>
      t ≫ (siteDifferentialsIso f).hom ≫
        (HomologicalComplex.singleObjXSelf (V := RingedSpace.siteModules X) (ComplexShape.up ℤ) 0
          (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u,u,u}
            (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f))).inv) h
  simpa only [RingedSpace.naiveCotangentComplexHomologyZeroIso,
    RingedSpace.naiveCotangentComplex, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, siteDifferentialsIso,
    Iso.trans_hom, Category.assoc] using ht

end Ringed

end M9Native.NativeCotangentProjection
