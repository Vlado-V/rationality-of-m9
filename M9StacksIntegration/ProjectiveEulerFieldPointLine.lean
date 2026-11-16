module

public import M9StacksIntegration.ProjectiveEulerFieldPoint
public import M9StacksIntegration.MukaiConormalOriginCoordinates

/-! The chart line coordinate is a genuine isomorphism of the actual
pulled negative-line sections. Any native line trivialization therefore
changes all Euler coefficients by one derived nonzero scalar. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.AlgebraicGeometry.ProjEulerSequence Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open scoped TensorProduct

universe u

namespace M9Native.ProjectiveEulerFieldPointLine

open SpecFieldStalkSections SpecFieldPullbackSections ProjectiveEulerFieldPoint

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ) (K : Type u) [Field K]
variable (p : space K ⟶ ProjectiveEulerFieldPoint.projectiveSpace R n)

abbrev negative : (ProjectiveEulerFieldPoint.projectiveSpace R n).Modules :=
  twistingSheaf (polyGrading R n) (-1)
abbrev pulledNegative := (Scheme.Modules.pullback p).obj (negative R n)
abbrev negativeSections := moduleSpecΓFunctor.obj (pulledNegative R n K p)

local instance imageNegativeModule : Module (imageRing R n K p)
    ((negative R n).presheaf.stalk (image R n K p)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (negative R n) (image R n K p)

local instance imageMiddleModule : Module (imageRing R n K p)
    ((middle R n).presheaf.stalk (image R n K p)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (middle R n) (image R n K p)

local instance imageAlgebra : Algebra (imageRing R n K p) (localRing K) :=
  (p.stalkMap (point K)).hom.toAlgebra

local instance negativeStalkSModule : Module (localRing K)
    ((pulledNegative R n K p).presheaf.stalk (point K)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (pulledNegative R n K p) (point K)

local instance negativeStalkKModule : Module K
    ((pulledNegative R n K p).presheaf.stalk (point K)) :=
  moduleStalk K (pulledNegative R n K p)

local instance negativeStalkTower : IsScalarTower K (localRing K)
    ((pulledNegative R n K p).presheaf.stalk (point K)) :=
  stalkScalarTower K (pulledNegative R n K p)

variable (i : Fin (n+1))
variable (hp : image R n K p ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))

include hp in
/-- Multiplication by Ti in the actual negative-line stalk. -/
def nativeLineCoordinate : (negative R n).presheaf.stalk (image R n K p) ≃ₗ[imageRing R n K p]
    imageRing R n K p := by
  let e := twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i)
    (chartNonzero R n K p i hp)
  refine { __ := e.toAddEquiv, map_smul' := fun b m => ?_ }
  have hm := associatedModuleSheafStalk_smul_eq (polyGrading R n)
    (twistGrading (polyGrading R n) (-1)) (image R n K p) b m
  exact (congrArg e hm.symm).trans (e.map_smul b m)

include hp in
/-- The actual negative-line field coordinate, obtained through genuine
pullback-stalk and Spec-section comparisons. -/
def fieldLineCoordinate : negativeSections R n K p ≃ₗ[K] K := by
  let E := (Stacks.Divisors.pullbackStalkBaseChange p (negative R n) (point K)).trans
    (((nativeLineCoordinate R n K p i hp).baseChange (imageRing R n K p) (localRing K) _ _).trans
      (TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K)))
  exact ((sectionsStalkEquiv K (pulledNegative R n K p)).trans
    (E.restrictScalars K)).trans (scalarLinearEquiv K).symm

theorem fieldLineCoordinate_pulledSection
    (s : Γ(negative R n, ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))) :
    fieldLineCoordinate R n K p i hp
      (pulledSection K p (negative R n)
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s) =
      ProjectiveEulerFieldPoint.evaluation R n K p (nativeLineCoordinate R n K p i hp
        ((negative R n).presheaf.germ
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
          (image R n K p) hp s)) := by
  let C := nativeLineCoordinate R n K p i hp
  let m := (negative R n).presheaf.germ
    (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) (image R n K p) hp s
  change (scalarLinearEquiv K).symm
    ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K))
      (C.baseChange (imageRing R n K p) (localRing K) _ _
        (Stacks.Divisors.pullbackStalkBaseChange p (negative R n) (point K)
          (sectionsStalkEquiv K (pulledNegative R n K p)
            (pulledSection K p (negative R n)
              (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s))))) = _
  refine (congrArg (fun t => (scalarLinearEquiv K).symm
    ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K))
      (C.baseChange (imageRing R n K p) (localRing K) _ _ t)))
        (baseChange_pulledSection K p (negative R n)
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s)).trans ?_
  refine (congrArg (fun t => (scalarLinearEquiv K).symm
    ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K)) t))
      (LinearEquiv.baseChange_tmul (R := imageRing R n K p) (A := localRing K)
        (M := (negative R n).presheaf.stalk (image R n K p))
        (N := imageRing R n K p) (e := C) (1 : localRing K) m)).trans ?_
  refine (congrArg (scalarLinearEquiv K).symm
    (TensorProduct.AlgebraTensorModule.rid_tmul (R := imageRing R n K p)
      (A := localRing K) (M := localRing K) (C m) (1 : localRing K))).trans ?_
  change (scalarLinearEquiv K).symm ((p.stalkMap (point K)).hom (C m) * 1) = _
  rw [mul_one]
  rfl

def component (k : Fin (n+1)) : middle R n ⟶ negative R n :=
  biproduct.π (twistMinusOneFamily R n) k

def componentAt (k : Fin (n+1)) : moduleSpecΓFunctor.obj (pulledMiddle R n K p) →ₗ[K]
    negativeSections R n K p :=
  (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (component R n k))).hom

theorem fieldLineCoordinate_component_pulledSection (k : Fin (n+1))
    (s : Γ(middle R n, ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))) :
    fieldLineCoordinate R n K p i hp
      (componentAt R n K p k (pulledSection K p (middle R n)
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s)) =
      middleCoordinate R n K p i hp k
        (pulledSection K p (middle R n)
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s) := by
  change fieldLineCoordinate R n K p i hp
    ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (component R n k))).hom
      (pulledSection K p (middle R n)
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s)) = _
  rw [pulledSection_naturality,fieldLineCoordinate_pulledSection,middleCoordinate_pulledSection]
  have hg := (TopCat.Presheaf.stalkFunctor_map_germ_apply
    (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (image R n K p) hp
    ((PresheafOfModules.toPresheaf (projRingSheaf (polyGrading R n)).obj).map
      (component R n k).val) s).symm
  exact congrArg (fun z => ProjectiveEulerFieldPoint.evaluation R n K p
    (nativeLineCoordinate R n K p i hp z)) hg

theorem fieldLineCoordinate_euler_basis (j : {j : Fin (n+1) // j ≠ i}) (k : Fin (n+1)) :
    fieldLineCoordinate R n K p i hp
      (componentAt R n K p k (eulerAt R n K p (cotangentBasis R n K p i hp j))) =
      Stacks.LinearAlgebra.kernelGen (ratio R n K p i hp) i j.1 k := by
  rw [cotangentBasis_apply]
  let U := ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)
  let s := (eulerFirst R n).app U (localRatioDifferential R n i j.1)
  have he : eulerAt R n K p (ratioDifferential R n K p i hp j.1) =
      pulledSection K p (middle R n) U hp s :=
    pulledSection_naturality K p (eulerFirst R n) U hp (localRatioDifferential R n i j.1)
  rw [he]
  exact (fieldLineCoordinate_component_pulledSection R n K p i hp k s).trans
    ((congrArg (middleCoordinate R n K p i hp k) he).symm.trans
      (middleCoordinate_euler_ratioDifferential R n K p i hp j.1 k))

/-- The actual unit sheaf's sections have their original Spec coordinate. -/
def unitCoordinates : moduleSpecΓFunctor.obj (SheafOfModules.unit (space K).ringCatSheaf) ≃ₗ[K] K := by
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  refine { __ := e.toAddEquiv, map_smul' := fun a s => ?_ }
  change e ((Scheme.ΓSpecIso (.of K)).inv.hom a * (show Γ(space K, ⊤) from s)) = a * e s
  rw [map_mul]
  have h : e ((Scheme.ΓSpecIso (.of K)).inv.hom a) = a :=
    e.apply_symm_apply a
  rw [h]

/-- A given genuine native line isomorphism supplies a line coordinate,
not an assumed multiplier or a prescribed image. -/
def coordinatesFromIso (e : pulledNegative R n K p ≅ SheafOfModules.unit (space K).ringCatSheaf) :
    negativeSections R n K p ≃ₗ[K] K :=
  (moduleSpecΓFunctor.mapIso e).toLinearEquiv.trans (unitCoordinates K)

/-- One nonzero scalar is constructed from the two actual line
trivializations, and is common to every genuine Euler basis vector/component. -/
theorem exists_uniform_scalar
    (e : pulledNegative R n K p ≅ SheafOfModules.unit (space K).ringCatSheaf) :
    ∃ a : K, a ≠ 0 ∧ ∀ (j : {j : Fin (n+1) // j ≠ i}) (k : Fin (n+1)),
      coordinatesFromIso R n K p e
        (componentAt R n K p k (eulerAt R n K p (cotangentBasis R n K p i hp j))) =
        a * Stacks.LinearAlgebra.kernelGen (ratio R n K p i hp) i j.1 k := by
  obtain ⟨a, ha, h⟩ := MukaiConormalOriginCoordinates.exists_common_scalar K
    (coordinatesFromIso R n K p e) (fieldLineCoordinate R n K p i hp)
  refine ⟨a, ha, fun j k => ?_⟩
  rw [h,fieldLineCoordinate_euler_basis]

end M9Native.ProjectiveEulerFieldPointLine
