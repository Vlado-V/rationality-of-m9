module

public import M9StacksIntegration.SpecFieldPullbackSections
public import M9StacksIntegration.ProjectiveEulerStalkBasis
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackStalkBasis

/-! The actual native projective Euler arrow at a field-valued point.
Its basis vectors are genuine pullbacks of the ratio differentials. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.AlgebraicGeometry.ProjEulerSequence
open scoped TensorProduct

universe u

namespace M9Native.ProjectiveEulerFieldPoint

open SpecFieldStalkSections SpecFieldPullbackSections

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ) (K : Type u) [Field K]

abbrev projectiveSpace : Scheme.{u} := AlgebraicGeometry.Proj (polyGrading R n)
abbrev cotangent : (projectiveSpace R n).Modules := projDifferentials R n
abbrev middle : (projectiveSpace R n).Modules := twistMinusOneSum R n
abbrev eulerFirst : cotangent R n ⟶ middle R n := eulerFirstArrow R n

variable (p : space K ⟶ projectiveSpace R n)

abbrev image : ProjectiveSpectrum.top (polyGrading R n) := p.base (point K)
abbrev imageRing := projStalk R n (image R n K p)
abbrev pulledCotangent := (Scheme.Modules.pullback p).obj (cotangent R n)
abbrev pulledMiddle := (Scheme.Modules.pullback p).obj (middle R n)
abbrev cotangentSections := moduleSpecΓFunctor.obj (pulledCotangent R n K p)

local instance imageCotangentModule : Module (imageRing R n K p)
    (ProjectiveEulerStalkBasis.cotangentStalk R n (image R n K p)) :=
  ProjectiveEulerStalkBasis.cotangentModule R n (image R n K p)

local instance imageMiddleModule : Module (imageRing R n K p)
    (ProjectiveEulerStalkBasis.middleStalk R n (image R n K p)) :=
  ProjectiveEulerStalkBasis.middleModule R n (image R n K p)

local instance imageCotangentPresheafModule : Module (imageRing R n K p)
    ((cotangent R n).presheaf.stalk (image R n K p)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (cotangent R n) (image R n K p)

local instance imageMiddlePresheafModule : Module (imageRing R n K p)
    ((middle R n).presheaf.stalk (image R n K p)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (middle R n) (image R n K p)

local instance imageAlgebra : Algebra (imageRing R n K p) (localRing K) :=
  (p.stalkMap (point K)).hom.toAlgebra

local instance pulledCotangentStalkModule : Module (localRing K)
    ((pulledCotangent R n K p).presheaf.stalk (point K)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (pulledCotangent R n K p) (point K)

local instance pulledMiddleStalkModule : Module (localRing K)
    ((pulledMiddle R n K p).presheaf.stalk (point K)) :=
  Stacks.ModuleStalkSpecialization.stalkModule (pulledMiddle R n K p) (point K)

local instance pulledCotangentStalkKModule : Module K
    ((pulledCotangent R n K p).presheaf.stalk (point K)) :=
  moduleStalk K (pulledCotangent R n K p)

local instance pulledMiddleStalkKModule : Module K
    ((pulledMiddle R n K p).presheaf.stalk (point K)) :=
  moduleStalk K (pulledMiddle R n K p)

local instance pulledCotangentStalkTower : IsScalarTower K (localRing K)
    ((pulledCotangent R n K p).presheaf.stalk (point K)) :=
  stalkScalarTower K (pulledCotangent R n K p)

local instance pulledMiddleStalkTower : IsScalarTower K (localRing K)
    ((pulledMiddle R n K p).presheaf.stalk (point K)) :=
  stalkScalarTower K (pulledMiddle R n K p)

variable (i : Fin (n+1))
variable (hp : image R n K p ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
include hp

def chartNonzero : (MvPolynomial.X i : MvPolynomial (Fin (n+1)) R) ∉
    (image R n K p).asHomogeneousIdeal := hp

/-- The original local ratio differential before pullback. -/
def localRatioDifferential (j : Fin (n+1)) :
    Γ(cotangent R n, ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :=
  (Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d (chartFracSection R n i j)

/-- The genuine field-point pullback of d(Tj/Ti), with the actual adjunction unit. -/
def ratioDifferential (j : Fin (n+1)) : cotangentSections R n K p :=
  pulledSection K p (cotangent R n)
    (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp
    (localRatioDifferential R n i j)

theorem baseChange_ratioDifferential (j : Fin (n+1)) :
    Stacks.Divisors.pullbackStalkBaseChange p (cotangent R n) (point K)
      (sectionsStalkEquiv K (pulledCotangent R n K p)
        (ratioDifferential R n K p i hp j)) =
      (1 : localRing K) ⊗ₜ[imageRing R n K p]
        chartDiffGerm R n (image R n K p) i hp j :=
  baseChange_pulledSection K p (cotangent R n)
    (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp
    (localRatioDifferential R n i j)

/-- Base change of the actual native cotangent basis to the actual field-point stalk. -/
def fieldStalkBasis : Module.Basis {j : Fin (n+1) // j ≠ i} (localRing K)
    ((pulledCotangent R n K p).presheaf.stalk (point K)) :=
  (Algebra.TensorProduct.basis (localRing K)
    (ProjectiveEulerStalkBasis.cotangentBasis R n (image R n K p) i
      (chartNonzero R n K p i hp) hp)).map
        (Stacks.Divisors.pullbackStalkBaseChange p (cotangent R n) (point K)).symm

theorem fieldStalkBasis_apply (j : {j : Fin (n+1) // j ≠ i}) :
    fieldStalkBasis R n K p i hp j =
      (Stacks.Divisors.pullbackStalkBaseChange p (cotangent R n) (point K)).symm
        ((1 : localRing K) ⊗ₜ[imageRing R n K p]
          chartDiffGerm R n (image R n K p) i hp j.1) := by
  change (Stacks.Divisors.pullbackStalkBaseChange p (cotangent R n) (point K)).symm
    (Algebra.TensorProduct.basis (localRing K)
      (ProjectiveEulerStalkBasis.cotangentBasis R n (image R n K p) i
        (chartNonzero R n K p i hp) hp) j) = _
  rw [Algebra.TensorProduct.basis_apply,ProjectiveEulerStalkBasis.cotangentBasis_apply]

/-- Field-linear coordinates on the original actual pullback sections. -/
def cotangentCoordinates : cotangentSections R n K p ≃ₗ[K] ({j : Fin (n+1) // j ≠ i} → K) :=
  (sectionsStalkEquiv K (pulledCotangent R n K p)).trans
    (((fieldStalkBasis R n K p i hp).equivFun.restrictScalars K).trans
      (LinearEquiv.piCongrRight fun _ => (scalarLinearEquiv K).symm))

theorem cotangentCoordinates_ratioDifferential (j : {j : Fin (n+1) // j ≠ i}) :
    cotangentCoordinates R n K p i hp (ratioDifferential R n K p i hp j.1) = Pi.single j 1 := by
  classical
  have hg : sectionsStalkEquiv K (pulledCotangent R n K p)
      (ratioDifferential R n K p i hp j.1) = fieldStalkBasis R n K p i hp j := by
    apply (Stacks.Divisors.pullbackStalkBaseChange p (cotangent R n) (point K)).injective
    rw [baseChange_ratioDifferential,fieldStalkBasis_apply,LinearEquiv.apply_symm_apply]
  change (fun k => (scalarLinearEquiv K).symm
    ((fieldStalkBasis R n K p i hp).equivFun
      (sectionsStalkEquiv K (pulledCotangent R n K p)
        (ratioDifferential R n K p i hp j.1)) k)) = _
  rw [hg]
  funext k
  rw [Module.Basis.equivFun_self]
  have h1 : (scalarLinearEquiv K).symm 1 = 1 := (scalarStalkEquiv K).symm.map_one
  by_cases hk : k = j
  · subst k
    simp [Pi.single_apply,h1]
  · have hjk : j ≠ k := Ne.symm hk
    simp [Pi.single_apply,hk,hjk]

/-- A genuine K-linear basis, rather than a dimension or spanning premise. -/
def cotangentBasis : Module.Basis {j : Fin (n+1) // j ≠ i} K (cotangentSections R n K p) :=
  Module.Basis.ofEquivFun (cotangentCoordinates R n K p i hp)

theorem cotangentBasis_apply (j : {j : Fin (n+1) // j ≠ i}) :
    cotangentBasis R n K p i hp j = ratioDifferential R n K p i hp j.1 := by
  apply (cotangentCoordinates R n K p i hp).injective
  rw [cotangentCoordinates_ratioDifferential]
  have h := congrFun (Module.Basis.coe_ofEquivFun (cotangentCoordinates R n K p i hp)) j
  exact (congrArg (cotangentCoordinates R n K p i hp) h).trans
    ((cotangentCoordinates R n K p i hp).apply_symm_apply _)

/-- Evaluation in the original field, through the actual point's stalk map. -/
def evaluation : imageRing R n K p →+* K :=
  (scalarStalkEquiv K).symm.toRingHom.comp (p.stalkMap (point K)).hom

def ratio (j : Fin (n+1)) : K :=
  evaluation R n K p (coordRatio R n (image R n K p) i (chartNonzero R n K p i hp) j)

theorem ratio_self : ratio R n K p i hp i = 1 := by
  rw [ratio,coordRatio_self,map_one]

/-- The canonical Ti-trivialized coordinate on the actual pulled Euler middle stalk. -/
def middleCoordinateStalk (k : Fin (n+1)) :
    (pulledMiddle R n K p).presheaf.stalk (point K) →ₗ[localRing K] localRing K :=
  ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K)).toLinearMap.comp
    ((ProjectiveEulerStalkBasis.coordinateLinear R n (image R n K p) i
      (chartNonzero R n K p i hp) k).baseChange (localRing K))).comp
        (Stacks.Divisors.pullbackStalkBaseChange p (middle R n) (point K)).toLinearMap

/-- Field-linear coordinates on the actual pullback middle sections. -/
def middleCoordinate (k : Fin (n+1)) :
    moduleSpecΓFunctor.obj (pulledMiddle R n K p) →ₗ[K] K :=
  ((scalarLinearEquiv K).symm.toLinearMap.comp
    ((middleCoordinateStalk R n K p i hp k).restrictScalars K)).comp
      (sectionsStalkEquiv K (pulledMiddle R n K p)).toLinearMap

theorem middleCoordinate_pulledSection (k : Fin (n+1))
    (s : Γ(middle R n, ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))) :
    middleCoordinate R n K p i hp k
      (pulledSection K p (middle R n)
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s) =
      evaluation R n K p
        (ProjectiveEulerStalkBasis.coordinateLinear R n (image R n K p) i
          (chartNonzero R n K p i hp) k
          ((middle R n).presheaf.germ
            (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
            (image R n K p) hp s)) := by
  change (scalarLinearEquiv K).symm
    ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K))
      (((ProjectiveEulerStalkBasis.coordinateLinear R n (image R n K p) i
        (chartNonzero R n K p i hp) k).baseChange (localRing K))
          (Stacks.Divisors.pullbackStalkBaseChange p (middle R n) (point K)
            (sectionsStalkEquiv K (pulledMiddle R n K p)
              (pulledSection K p (middle R n)
                (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s))))) = _
  let C := ProjectiveEulerStalkBasis.coordinateLinear R n (image R n K p) i
    (chartNonzero R n K p i hp) k
  let m := (middle R n).presheaf.germ
    (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) (image R n K p) hp s
  refine (congrArg (fun t => (scalarLinearEquiv K).symm
    ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K))
      (C.baseChange (localRing K) t)))
        (baseChange_pulledSection K p (middle R n)
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp s)).trans ?_
  refine (congrArg (fun t => (scalarLinearEquiv K).symm
    ((TensorProduct.AlgebraTensorModule.rid (imageRing R n K p) (localRing K) (localRing K)) t))
      (LinearMap.baseChange_tmul C (1 : localRing K) m)).trans ?_
  refine (congrArg (scalarLinearEquiv K).symm
    (TensorProduct.AlgebraTensorModule.rid_tmul (R := imageRing R n K p)
      (A := localRing K) (M := localRing K) (C m) (1 : localRing K))).trans ?_
  change (scalarLinearEquiv K).symm ((p.stalkMap (point K)).hom (C m) * 1) = _
  rw [mul_one]
  rfl

def eulerAt : cotangentSections R n K p →ₗ[K]
    moduleSpecΓFunctor.obj (pulledMiddle R n K p) :=
  (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (eulerFirst R n))).hom

/-- The actual pullback Euler arrow sends the actual pulled ratio
differential to e_j−ratio_j e_i, in the canonical chart coordinates. -/
theorem middleCoordinate_euler_ratioDifferential (j k : Fin (n+1)) :
    middleCoordinate R n K p i hp k
      (eulerAt R n K p (ratioDifferential R n K p i hp j)) =
      Stacks.LinearAlgebra.kernelGen (ratio R n K p i hp) i j k := by
  classical
  change middleCoordinate R n K p i hp k
    ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (eulerFirst R n))).hom
      (pulledSection K p (cotangent R n)
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hp
        (localRatioDifferential R n i j))) = _
  rw [pulledSection_naturality,middleCoordinate_pulledSection]
  have hg : (middle R n).presheaf.germ
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
      (image R n K p) hp
      ((eulerFirst R n).app
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
        (localRatioDifferential R n i j)) =
      (SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) (image R n K p)
        (eulerFirstArrow R n)).hom
        (chartDiffGerm R n (image R n K p) i hp j) := by
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
      (image R n K p) hp
      ((PresheafOfModules.toPresheaf (projRingSheaf (polyGrading R n)).obj).map
        (eulerFirst R n).val) (localRatioDifferential R n i j)).symm
  rw [hg]
  change evaluation R n K p
    (eulerStalkCoord R n (image R n K p) i (chartNonzero R n K p i hp) k
      ((SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) (image R n K p)
        (eulerFirstArrow R n)).hom
        (chartDiffGerm R n (image R n K p) i hp j))) = _
  rw [eulerStalkCoord_stalkMap_eulerFirstArrow]
  simp only [Stacks.LinearAlgebra.kernelGen_apply,ratio,map_sub,map_mul,apply_ite,map_one,map_zero]
  split_ifs <;> rfl

theorem middleCoordinate_euler_basis (j : {j : Fin (n+1) // j ≠ i}) (k : Fin (n+1)) :
    middleCoordinate R n K p i hp k
      (eulerAt R n K p (cotangentBasis R n K p i hp j)) =
      Stacks.LinearAlgebra.kernelGen (ratio R n K p i hp) i j.1 k := by
  rw [cotangentBasis_apply]
  exact middleCoordinate_euler_ratioDifferential R n K p i hp j.1 k

end M9Native.ProjectiveEulerFieldPoint
