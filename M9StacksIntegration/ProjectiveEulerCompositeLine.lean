module

public import M9StacksIntegration.ProjectiveEulerFieldPointLine
public import M9StacksIntegration.NativePullbackTensorLine

/-! Genuine source coordinates for the determinant-twisted Euler map
pulled through a composite. Both the original tensor input and the
original perfect line pairing are retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace M9Native.ProjectiveEulerCompositeLine

open SpecFieldStalkSections ProjectiveEulerFieldPoint ProjectiveEulerFieldPointLine
open MukaiBundleDeterminant (tensor)
open NativeTensorLineTrivialization (tensorRight)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (K : Type u) [Field K]
variable {X : Scheme.{u}} (f : X ⟶ projectiveSpace R n) (p : space K ⟶ X)
variable (L : X.Modules)
variable (τ : (Scheme.Modules.pullback p).obj L ≅ SheafOfModules.unit (space K).ringCatSheaf)

/-- Pullback of the original tensor, actual positive-line cancellation,
and the genuine pullback-composition isomorphism, in that order. -/
def coordinateIso (M : (projectiveSpace R n).Modules) :
    (Scheme.Modules.pullback p).obj (tensor ((Scheme.Modules.pullback f).obj M) L) ≅
      (Scheme.Modules.pullback (p ≫ f)).obj M :=
  NativePullbackTensorLine.sourceIso p ((Scheme.Modules.pullback f).obj M) L τ ≪≫
    (Scheme.Modules.pullbackComp p f).app M

theorem coordinateIso_naturality {M N : (projectiveSpace R n).Modules} (a : M ⟶ N) :
    (Scheme.Modules.pullback p).map
        ((tensorRight L).map ((Scheme.Modules.pullback f).map a)) ≫
        (coordinateIso R n K f p L τ N).hom =
      (coordinateIso R n K f p L τ M).hom ≫
        (Scheme.Modules.pullback (p ≫ f)).map a := by
  have h := (Scheme.Modules.pullbackComp p f).hom.naturality a
  simp only [coordinateIso,Iso.trans_hom,← Category.assoc]
  rw [NativePullbackTensorLine.sourceIso_naturality,Category.assoc]
  exact congrArg (fun b =>
    (NativePullbackTensorLine.sourceIso p ((Scheme.Modules.pullback f).obj M) L τ).hom ≫ b) h

theorem coordinateIso_inv_naturality {M N : (projectiveSpace R n).Modules} (a : M ⟶ N) :
    (coordinateIso R n K f p L τ M).inv ≫
        (Scheme.Modules.pullback p).map
          ((tensorRight L).map ((Scheme.Modules.pullback f).map a)) =
      (Scheme.Modules.pullback (p ≫ f)).map a ≫
        (coordinateIso R n K f p L τ N).inv := by
  apply (cancel_mono (coordinateIso R n K f p L τ N).hom).mp
  rw [Category.assoc,coordinateIso_naturality]
  simp only [Iso.inv_hom_id_assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]

def sourceCoordinates (M : (projectiveSpace R n).Modules) :
    moduleSpecΓFunctor.obj
        ((Scheme.Modules.pullback p).obj (tensor ((Scheme.Modules.pullback f).obj M) L)) ≃ₗ[K]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (p ≫ f)).obj M) :=
  (moduleSpecΓFunctor.mapIso (coordinateIso R n K f p L τ M)).toLinearEquiv

theorem sourceCoordinates_untwist (M : (projectiveSpace R n).Modules)
    (x : moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback p).obj (tensor ((Scheme.Modules.pullback f).obj M) L))) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp p f).app M).inv).hom
        (sourceCoordinates R n K f p L τ M x) =
      (moduleSpecΓFunctor.map
        (NativePullbackTensorLine.sourceIso p ((Scheme.Modules.pullback f).obj M) L τ).hom).hom x := by
  have h : (coordinateIso R n K f p L τ M).hom ≫
      ((Scheme.Modules.pullbackComp p f).app M).inv =
      (NativePullbackTensorLine.sourceIso p ((Scheme.Modules.pullback f).obj M) L τ).hom := by
    simp only [coordinateIso,Iso.trans_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hΓ := congrArg (fun t => (moduleSpecΓFunctor.map t).hom x) h
  simp only [CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply] at hΓ
  exact hΓ

/-- Vanishing of the original tensor differential implies vanishing on
the very same cotangent input read by the actual composite coordinate iso. -/
theorem map_zero_of_tensor_map_zero
    (M : (projectiveSpace R n).Modules) {B : X.Modules}
    (D : (Scheme.Modules.pullback f).obj M ⟶ B)
    (x : moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback p).obj (tensor ((Scheme.Modules.pullback f).obj M) L)))
    (hx : (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map ((tensorRight L).map D))).hom x = 0) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map D)).hom
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp p f).app M).inv).hom
        (sourceCoordinates R n K f p L τ M x)) = 0 := by
  rw [sourceCoordinates_untwist]
  exact NativePullbackTensorLine.map_zero_of_tensor_map_zero K p D L τ x hx

variable (e : tensor ((Scheme.Modules.pullback f).obj (negative R n)) L ≅
  SheafOfModules.unit X.ringCatSheaf)

/-- This uses the original global pairing, pulled to the actual point;
the negative-line trivialization is derived from it and the positive frame. -/
def negativeTrivialization : pulledNegative R n K (p ≫ f) ≅
    SheafOfModules.unit (space K).ringCatSheaf :=
  (coordinateIso R n K f p L τ (negative R n)).symm ≪≫
    (Scheme.Modules.pullback p).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso p

abbrev source := (Scheme.Modules.pullback p).obj
  (tensor ((Scheme.Modules.pullback f).obj (cotangent R n)) L)

def pairedEulerComponent (k : Fin (n+1)) : source R n K f p L ⟶
    SheafOfModules.unit (space K).ringCatSheaf :=
  (Scheme.Modules.pullback p).map
    ((tensorRight L).map ((Scheme.Modules.pullback f).map
      (eulerFirst R n ≫ component R n k)) ≫ e.hom) ≫
    (Scheme.Modules.pullbackUnitIso p).hom

theorem pairedEulerComponent_comparison (k : Fin (n+1)) :
    (coordinateIso R n K f p L τ (cotangent R n)).inv ≫
        pairedEulerComponent R n K f p L e k =
      (Scheme.Modules.pullback (p ≫ f)).map (eulerFirst R n ≫ component R n k) ≫
        (negativeTrivialization R n K f p L τ e).hom := by
  have h := coordinateIso_inv_naturality R n K f p L τ
    (eulerFirst R n ≫ component R n k)
  change (coordinateIso R n K f p L τ (cotangent R n)).inv ≫
      ((Scheme.Modules.pullback p).map
        ((tensorRight L).map ((Scheme.Modules.pullback f).map
          (eulerFirst R n ≫ component R n k)) ≫ e.hom) ≫
        (Scheme.Modules.pullbackUnitIso p).hom) = _
  rw [CategoryTheory.Functor.map_comp]
  simpa only [negativeTrivialization,Iso.trans_hom,Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom,Category.assoc] using
    congrArg (fun t => t ≫ (Scheme.Modules.pullback p).map e.hom ≫
      (Scheme.Modules.pullbackUnitIso p).hom) h

def coefficient (k : Fin (n+1)) : moduleSpecΓFunctor.obj (source R n K f p L) →ₗ[K] K :=
  (unitCoordinates K).toLinearMap.comp
    (moduleSpecΓFunctor.map (pairedEulerComponent R n K f p L e k)).hom

variable (i : Fin (n+1))
variable (hp : image R n K (p ≫ f) ∈
  ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))

def basis : Module.Basis {j : Fin (n+1) // j ≠ i} K
    (moduleSpecΓFunctor.obj (source R n K f p L)) :=
  (cotangentBasis R n K (p ≫ f) i hp).map
    (sourceCoordinates R n K f p L τ (cotangent R n)).symm

theorem basis_apply (j : {j : Fin (n+1) // j ≠ i}) :
    basis R n K f p L τ i hp j =
      (moduleSpecΓFunctor.map (coordinateIso R n K f p L τ (cotangent R n)).inv).hom
        (ratioDifferential R n K (p ≫ f) i hp j.1) := by
  change (sourceCoordinates R n K f p L τ (cotangent R n)).symm
    (cotangentBasis R n K (p ≫ f) i hp j) = _
  rw [cotangentBasis_apply]
  rfl

theorem coefficient_comparison (z : cotangentSections R n K (p ≫ f)) (k : Fin (n+1)) :
    coefficient R n K f p L e k
        ((sourceCoordinates R n K f p L τ (cotangent R n)).symm z) =
      coordinatesFromIso R n K (p ≫ f) (negativeTrivialization R n K f p L τ e)
        (componentAt R n K (p ≫ f) k (eulerAt R n K (p ≫ f) z)) := by
  have hΓ := congrArg (fun t : pulledCotangent R n K (p ≫ f) ⟶
      SheafOfModules.unit (space K).ringCatSheaf => (moduleSpecΓFunctor.map t).hom z)
    (pairedEulerComponent_comparison R n K f p L τ e k)
  change unitCoordinates K
      ((moduleSpecΓFunctor.map (pairedEulerComponent R n K f p L e k)).hom
        ((moduleSpecΓFunctor.map (coordinateIso R n K f p L τ (cotangent R n)).inv).hom z)) =
    unitCoordinates K
      ((moduleSpecΓFunctor.map (negativeTrivialization R n K f p L τ e).hom).hom
        ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback (p ≫ f)).map (component R n k))).hom
          ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback (p ≫ f)).map (eulerFirst R n))).hom z)))
  simp only [CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply] at hΓ
  exact congrArg (unitCoordinates K) hΓ

/-- All coefficients of the ORIGINAL paired determinant-twisted Euler
map use a single nonzero scalar, derived from actual line isomorphisms. -/
theorem exists_uniform_scalar :
    ∃ a : K, a ≠ 0 ∧ ∀ (j : {j : Fin (n+1) // j ≠ i}) (k : Fin (n+1)),
      coefficient R n K f p L e k (basis R n K f p L τ i hp j) =
        a * Stacks.LinearAlgebra.kernelGen (ratio R n K (p ≫ f) i hp) i j.1 k := by
  obtain ⟨a,ha,h⟩ := ProjectiveEulerFieldPointLine.exists_uniform_scalar
    R n K (p ≫ f) i hp (negativeTrivialization R n K f p L τ e)
  refine ⟨a,ha,fun j k => ?_⟩
  change coefficient R n K f p L e k
    ((sourceCoordinates R n K f p L τ (cotangent R n)).symm
      (cotangentBasis R n K (p ≫ f) i hp j)) = _
  rw [coefficient_comparison]
  exact h j k

end M9Native.ProjectiveEulerCompositeLine
