module

public import M9StacksIntegration.Private.DerivedHeartIso
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag

/-!
# The original smooth naive cotangent complex is the original differentials

The native infinitesimal lifting theorem supplies formal smoothness.
Actual stalkwise cotangent vanishing then concentrates the actual naive
cotangent complex in degree zero. The resulting derived isomorphism is
normalized by the original `H⁰(NL) ≅ Ω` comparison, retaining naturality.
-/

attribute [local instance 10000] SheafOfModules.hasDerivedCategory
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.SmoothNaiveCotangent

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

abbrev derivedObject : DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)

def homologyZeroIso :
    (DerivedCategory.homologyFunctor X.Modules 0).obj (derivedObject f) ≅
      Scheme.Hom.relativeDifferentials f :=
  (DerivedCategory.homologyFunctorFactors X.Modules 0).app (Scheme.naiveCotangentComplex f) ≪≫
    Scheme.naiveCotangentComplexHomologyZeroIso f

theorem isGE_zero [Smooth f] : (derivedObject f).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact (Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth f
    (Stacks.Smooth.formallySmoothScheme_of_smooth f) n (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app (Scheme.naiveCotangentComplex f))

theorem isLE_zero [Smooth f] : (derivedObject f).IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact (Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth f
    (Stacks.Smooth.formallySmoothScheme_of_smooth f) n (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app (Scheme.naiveCotangentComplex f))

/-- An actual derived isomorphism between the original complex and original sheaf. -/
def differentialsIso [Smooth f] :
    derivedObject f ≅ (DerivedCategory.singleFunctor X.Modules 0).obj
      (Scheme.Hom.relativeDifferentials f) := by
  let := isGE_zero f
  let := isLE_zero f
  exact DerivedHeartIso.toSingle _ _ (homologyZeroIso f)

/-- Its normalization is the original native degree-zero cotangent comparison. -/
theorem differentialsIso_homology [Smooth f] :
    (DerivedCategory.homologyFunctor X.Modules 0).map (differentialsIso f).hom ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app
        (Scheme.Hom.relativeDifferentials f)).hom = (homologyZeroIso f).hom := by
  let := isGE_zero f
  let := isLE_zero f
  exact DerivedHeartIso.H0_map_toSingle_hom _ _ (homologyZeroIso f)

variable {Z : Scheme.{u}} (g : X ⟶ Z)

/-- The actual map on differentials induced by a derived cotangent arrow, read
through the original native homology comparisons. -/
def differentialMap (a : derivedObject f ⟶ derivedObject g) :
    Scheme.Hom.relativeDifferentials f ⟶ Scheme.Hom.relativeDifferentials g :=
  (homologyZeroIso f).inv ≫
    (DerivedCategory.homologyFunctor X.Modules 0).map a ≫ (homologyZeroIso g).hom

theorem differentialsIso_naturality [Smooth f] [Smooth g]
    (a : derivedObject f ⟶ derivedObject g) :
    a ≫ (differentialsIso g).hom = (differentialsIso f).hom ≫
      (DerivedCategory.singleFunctor X.Modules 0).map (differentialMap f g a) := by
  let := isGE_zero f
  let := isLE_zero f
  let := isGE_zero g
  let := isLE_zero g
  apply DerivedHeartIso.toSingle_naturality
  simp only [differentialMap, Iso.hom_inv_id_assoc]

end M9Native.SmoothNaiveCotangent
