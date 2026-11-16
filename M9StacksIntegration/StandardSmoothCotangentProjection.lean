module

public import M9StacksIntegration.StandardSmoothCotangent
public import M9StacksIntegration.CochainCokernelProjection
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero

/-!
# The actual chain projection realizes smooth cotangent normalization

The projection is built on the original cochain complex and original
homology isomorphism. Its actual derived arrow equals the frozen
standard smooth comparison, by the computed original H0 normalization.
No equality between derived models or canonical maps is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace M9Native.StandardSmoothCotangentProjection

section Single

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The native derived single-sheaf homology comparison is exactly the
original cochain comparison followed by original single homology. -/
theorem singleHomology_factors (M : C) :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).hom =
      ((DerivedCategory.homologyFunctorFactors C 0).app
        ((CochainComplex.singleFunctor C 0).obj M)).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso]

end Single

namespace Ringed

variable {X S : RingedSpace.{u,u}} (f : X ⟶ S)

/-- The original cotangent complex has no differential out of degree zero. -/
theorem outgoing_zero :
    (RingedSpace.naiveCotangentComplex f).d 0 ((ComplexShape.up ℤ).next 0) = 0 := by
  change (HomologicalComplex.double (RingedSpace.naiveCotangentConormalShortComplex f).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d
      0 ((ComplexShape.up ℤ).next 0) = 0
  exact HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)

/-- The original ringed-space chain projection, in the original small-site category. -/
def complexProjection : RingedSpace.naiveCotangentComplex f ⟶
    (CochainComplex.singleFunctor (RingedSpace.siteModules X) 0).obj
      (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)) :=
  CochainCokernelProjection.toSingle (C := RingedSpace.siteModules X)
    (RingedSpace.naiveCotangentComplex f) (outgoing_zero f) _
      (RingedSpace.naiveCotangentComplexHomologyZeroIso f)

/-- Its degree-zero part retains the literal original native homology comparison. -/
theorem complexProjection_f_zero :
    (complexProjection f).f 0 =
      CochainCokernelProjection.toHomology (C := RingedSpace.siteModules X)
        (RingedSpace.naiveCotangentComplex f) (outgoing_zero f) ≫
        (RingedSpace.naiveCotangentComplexHomologyZeroIso f).hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv :=
  CochainCokernelProjection.toSingle_f_zero _ _ _ _

end Ringed

attribute [local instance 100000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original native complex projection to the original sheaf of differentials. -/
def complexProjection : Scheme.naiveCotangentComplex f ⟶
    (CochainComplex.singleFunctor X.Modules 0).obj (Scheme.Hom.relativeDifferentials f) :=
  Ringed.complexProjection f.toLRSHom.toShHom

/-- Its actual original derived H0 is the frozen native normalization. -/
theorem derivedProjection_homology :
    (DerivedCategory.homologyFunctor X.Modules 0).map (DerivedCategory.Q.map (complexProjection f)) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app
        (Scheme.Hom.relativeDifferentials f)).hom =
          (StandardSmoothCotangent.homologyZeroIso f).hom := by
  rw [singleHomology_factors, ← Category.assoc]
  have h := (DerivedCategory.homologyFunctorFactors X.Modules 0).hom.naturality
    (complexProjection f)
  change (DerivedCategory.homologyFunctor X.Modules 0).map
      (DerivedCategory.Q.map (complexProjection f)) ≫
        ((DerivedCategory.homologyFunctorFactors X.Modules 0).app
          ((CochainComplex.singleFunctor X.Modules 0).obj
            (Scheme.Hom.relativeDifferentials f))).hom =
      ((DerivedCategory.homologyFunctorFactors X.Modules 0).app
        (Scheme.naiveCotangentComplex f)).hom ≫
          HomologicalComplex.homologyMap (complexProjection f) 0 at h
  rw [h, Category.assoc]
  have hc := CochainCokernelProjection.homology_toSingle
    (C := RingedSpace.siteModules X.toRingedSpace)
    (RingedSpace.naiveCotangentComplex f.toLRSHom.toShHom)
    (Ringed.outgoing_zero f.toLRSHom.toShHom)
    _ (RingedSpace.naiveCotangentComplexHomologyZeroIso f.toLRSHom.toShHom)
  exact congrArg (fun t => ((DerivedCategory.homologyFunctorFactors X.Modules 0).app
      (Scheme.naiveCotangentComplex f)).hom ≫ t) hc

/-- The actual chain projection is the literal original standard smooth
comparison in the derived category, by genuine H0 faithfulness. -/
theorem derivedProjection_eq [Smooth f] :
    DerivedCategory.Q.map (complexProjection f) =
      (StandardSmoothCotangent.differentialsIso f).hom := by
  let := StandardSmoothCotangent.isLE_zero f
  apply (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    (StandardSmoothCotangent.nativeObject f)
    ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.Hom.relativeDifferentials f))
      0).injective
  apply (cancel_mono
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app
      (Scheme.Hom.relativeDifferentials f)).hom).mp
  exact (derivedProjection_homology f).trans
    (StandardSmoothCotangent.differentialsIso_homology f).symm

end M9Native.StandardSmoothCotangentProjection
