module

public import M9StacksIntegration.MukaiBundle
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Actual finite free-object changes of basis

A scalar matrix acts on the actual coproduct of copies of an object in a
linear category. This construction preserves matrix products and identities,
so an actual change of basis gives an actual isomorphism of free objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace M9Native.FiniteCopowerBasisChange

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] (O : C)
  {I J K : Type z} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [HasCoproduct (fun _ : I => O)] [HasCoproduct (fun _ : J => O)]
  [HasCoproduct (fun _ : K => O)]

/-- The genuine map of finite coproducts with the specified scalar matrix. -/
def matrixMap (a : Matrix J I k) : (∐ fun _ : I => O) ⟶ (∐ fun _ : J => O) :=
  Sigma.desc (fun i => ∑ j, a j i • Sigma.ι (fun _ : J => O) j)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
@[reassoc (attr := simp)] theorem generator_matrixMap (a : Matrix J I k) (i : I) :
    Sigma.ι (fun _ : I => O) i ≫ matrixMap O a =
      ∑ j, a j i • Sigma.ι (fun _ : J => O) j := by
  simp [matrixMap]

theorem matrixMap_one : matrixMap O (1 : Matrix I I k) = 𝟙 (∐ fun _ : I => O) := by
  apply Sigma.hom_ext
  intro i
  simp [matrixMap, Matrix.one_apply]

omit [Fintype I] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem matrixMap_comp (a : Matrix J I k) (b : Matrix K J k) :
    matrixMap O a ≫ matrixMap O b = matrixMap O (b*a) := by
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc, generator_matrixMap, Preadditive.sum_comp,
    Linear.smul_comp, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_comm]

/-- An actual coefficient change of basis induces an actual free-object iso. -/
def linearEquivIso (e : (I → k) ≃ₗ[k] (J → k)) :
    (∐ fun _ : I => O) ≅ (∐ fun _ : J => O) where
  hom := matrixMap O (LinearMap.toMatrix' e.toLinearMap)
  inv := matrixMap O (LinearMap.toMatrix' e.symm.toLinearMap)
  hom_inv_id := by
    rw [matrixMap_comp, ← LinearMap.toMatrix'_comp]
    simp only [LinearEquiv.symm_comp, LinearMap.toMatrix'_id, matrixMap_one]
  inv_hom_id := by
    rw [matrixMap_comp, ← LinearMap.toMatrix'_comp]
    simp only [LinearEquiv.comp_symm, LinearMap.toMatrix'_id, matrixMap_one]

theorem linearEquivIso_generator (e : (I → k) ≃ₗ[k] (J → k)) (i : I) :
    Sigma.ι (fun _ : I => O) i ≫ (linearEquivIso O e).hom =
      ∑ j, e (Pi.single i 1) j • Sigma.ι (fun _ : J => O) j := by
  simp only [linearEquivIso, generator_matrixMap, LinearMap.toMatrix'_apply,
    LinearEquiv.coe_coe]

end M9Native.FiniteCopowerBasisChange

namespace M9Native.FiniteCopowerBasisChange

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) {I J : Type u}
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The original canonical generator, typed in the native scheme category. -/
abbrev freeModule (X : Scheme.{u}) (I : Type u) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) I

abbrev freeGenerator (i : I) : MukaiBundle.structureModule X ⟶
    freeModule X I := SheafOfModules.ιFree i

/-- An actual base-field change of basis gives an actual free-sheaf iso. -/
def sheafFreeIso (e : (I → k) ≃ₗ[k] (J → k)) :
    freeModule X I ≅ freeModule X J := by
  letI := modulesLinearOverField k f
  exact linearEquivIso (MukaiBundle.structureModule X) e

/-- Its effect on the actual native free generators is the original
coefficient matrix, with the original base-field scalar action. -/
theorem sheafFreeIso_generator (e : (I → k) ≃ₗ[k] (J → k)) (i : I) :
    letI := modulesLinearOverField k f
    freeGenerator (X := X) i ≫ (sheafFreeIso f e).hom =
      ∑ j, e (Pi.single i 1) j • freeGenerator (X := X) j := by
  let := modulesLinearOverField k f
  exact linearEquivIso_generator (MukaiBundle.structureModule X) e i

end M9Native.FiniteCopowerBasisChange
