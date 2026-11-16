module

public import M9.FiniteNoNameField
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coordinates on semilinear Hom spaces

The action on a Hom space is conjugation by the given semilinear actions.
The action on its dual is the actual contragredient action, including the
coefficient automorphism.  Fixed bases of the source and target give fixed
matrix-coordinate functions, with no assumed descent of the function field.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.SemilinearHomCoordinates

open Module

section Actions

variable (G L E F : Type*) [Group G] [Field L] [MulSemiringAction G L]
  [AddCommGroup E] [Module L E] [DistribMulAction G E] [SMulDistribClass G L E]
  [AddCommGroup F] [Module L F] [DistribMulAction G F] [SMulDistribClass G L F]

/-- The actual action on linear maps between two semilinear spaces. -/
def homOperator (g : G) (f : E →ₗ[L] F) : E →ₗ[L] F where
  toFun x := g • f (g⁻¹ • x)
  map_add' x y := by simp only [smul_add, map_add]
  map_smul' a x := by
    simp only [smul_distrib_smul, map_smul, smul_inv_smul, RingHom.id_apply]

@[instance_reducible] def homAction : DistribMulAction G (E →ₗ[L] F) where
  smul := homOperator G L E F
  one_smul f := by
    apply LinearMap.ext
    intro x
    change (1 : G) • f ((1 : G)⁻¹ • x) = f x
    simp
  mul_smul g h f := by
    apply LinearMap.ext
    intro x
    change (g * h) • f ((g * h)⁻¹ • x) = g • (h • f (h⁻¹ • (g⁻¹ • x)))
    simp only [mul_inv_rev, mul_smul]
  smul_zero g := by
    apply LinearMap.ext
    intro x
    change g • (0 : E →ₗ[L] F) (g⁻¹ • x) = 0
    exact smul_zero g
  smul_add g f h := by
    apply LinearMap.ext
    intro x
    change g • (f (g⁻¹ • x) + h (g⁻¹ • x)) = _
    exact smul_add g _ _

theorem homAction_apply (g : G) (f : E →ₗ[L] F) (x : E) :
    letI := homAction G L E F
    (g • f) x = g • f (g⁻¹ • x) := rfl

theorem homSemilinear :
    letI := homAction G L E F
    SMulDistribClass G L (E →ₗ[L] F) := by
  let := homAction G L E F
  refine ⟨fun g a f => ?_⟩
  ext x
  change g • (a • f (g⁻¹ • x)) = (g • a) • (g • f (g⁻¹ • x))
  exact smul_distrib_smul g a (f (g⁻¹ • x))

end Actions

section Dual

variable (G L V : Type*) [Group G] [Field L] [MulSemiringAction G L]
  [AddCommGroup V] [Module L V] [DistribMulAction G V] [SMulDistribClass G L V]

local instance fieldSemilinear : SMulDistribClass G L L := ⟨fun g a b => smul_mul' g a b⟩

/-- The semilinear contragredient action on actual linear functionals. -/
@[instance_reducible] def dualAction : DistribMulAction G (Dual L V) :=
  homAction G L V L

theorem dualAction_apply (g : G) (l : Dual L V) (v : V) :
    letI := dualAction G L V
    (g • l) v = g • l (g⁻¹ • v) := rfl

theorem dualSemilinear :
    letI := dualAction G L V
    SMulDistribClass G L (Dual L V) := homSemilinear G L V L

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dual of a fixed basis is fixed under the actual contragredient action. -/
theorem dualBasis_fixed (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (g : G) (i : ι) :
    letI := dualAction G L V
    g • b.dualBasis i = b.dualBasis i := by
  let := dualAction G L V
  apply LinearMap.ext
  intro v
  change g • b.dualBasis i (g⁻¹ • v) = b.dualBasis i v
  rw [Basis.dualBasis_apply, Basis.dualBasis_apply]
  have h := FiniteGaloisDescent.basisCoordinates_smul G L V b hb g⁻¹ v i
  change b.repr (g⁻¹ • v) i = g⁻¹ • b.repr v i at h
  rw [h, smul_inv_smul]

end Dual

section Matrices

variable (G L E F : Type*) [Group G] [Field L] [MulSemiringAction G L]
  [AddCommGroup E] [Module L E] [DistribMulAction G E] [SMulDistribClass G L E]
  [AddCommGroup F] [Module L F] [DistribMulAction G F] [SMulDistribClass G L F]
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

local instance : DistribMulAction G (E →ₗ[L] F) := homAction G L E F
local instance : SMulDistribClass G L (E →ₗ[L] F) := homSemilinear G L E F

def homMatrixBasis (bE : Basis I L E) (bF : Basis J L F) :
    Basis (J × I) L (E →ₗ[L] F) :=
  (Matrix.stdBasis L J I).map (LinearMap.toMatrix bE bF).symm

omit [DecidableEq J] in
/-- Matrix coefficients change only through the field automorphism in fixed bases. -/
theorem toMatrix_smul (bE : Basis I L E) (bF : Basis J L F)
    (hE : ∀ (g : G) (i : I), g • bE i = bE i)
    (hF : ∀ (g : G) (j : J), g • bF j = bF j)
    (g : G) (f : E →ₗ[L] F) (i : J) (j : I) :
    LinearMap.toMatrix bE bF (g • f) i j =
      g • LinearMap.toMatrix bE bF f i j := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  change bF.repr (g • f (g⁻¹ • bE j)) i = g • bF.repr (f (bE j)) i
  rw [hE]
  exact FiniteGaloisDescent.basisCoordinates_smul G L F bF hF g (f (bE j)) i

theorem homMatrixBasis_fixed (bE : Basis I L E) (bF : Basis J L F)
    (hE : ∀ (g : G) (i : I), g • bE i = bE i)
    (hF : ∀ (g : G) (j : J), g • bF j = bF j)
    (g : G) (ij : J × I) :
    g • homMatrixBasis L E F bE bF ij = homMatrixBasis L E F bE bF ij := by
  classical
  apply (LinearMap.toMatrix bE bF).injective
  funext i j
  rw [toMatrix_smul G L E F bE bF hE hF]
  by_cases hi : i = ij.1 <;> by_cases hj : j = ij.2 <;>
    simp [homMatrixBasis, Matrix.stdBasis, hi, hj]

def coordinateBasis (bE : Basis I L E) (bF : Basis J L F) :
    Basis (J × I) L (Dual L (E →ₗ[L] F)) := (homMatrixBasis L E F bE bF).dualBasis

theorem coordinateBasis_apply (bE : Basis I L E) (bF : Basis J L F)
    (ij : J × I) (f : E →ₗ[L] F) :
    coordinateBasis L E F bE bF ij f = LinearMap.toMatrix bE bF f ij.1 ij.2 := by
  simp [coordinateBasis, homMatrixBasis, Matrix.stdBasis]

/-- These are genuine fixed matrix-coordinate functionals on the raw Hom space. -/
theorem coordinateBasis_fixed (bE : Basis I L E) (bF : Basis J L F)
    (hE : ∀ (g : G) (i : I), g • bE i = bE i)
    (hF : ∀ (g : G) (j : J), g • bF j = bF j)
    (g : G) (ij : J × I) :
    letI := dualAction G L (E →ₗ[L] F)
    g • coordinateBasis L E F bE bF ij = coordinateBasis L E F bE bF ij :=
  dualBasis_fixed G L (E →ₗ[L] F) _ (homMatrixBasis_fixed G L E F bE bF hE hF) g ij

end Matrices

section FieldExt

variable {L V A : Type*} [Field L] [AddCommGroup V] [Module L V] [Field A]

/-- Ring homomorphisms out of the actual rational coordinate field are
determined by coefficients and degree-one coordinate functions. -/
theorem coordinateFieldHom_ext
    (f h : FiniteNoNameField.CoordinateField L V →+* A)
    (hL : ∀ a : L, f (algebraMap L _ a) = h (algebraMap L _ a))
    (hV : ∀ v : V,
      f (algebraMap (SymmetricAlgebra L V) _ (SymmetricAlgebra.ι L V v)) =
        h (algebraMap (SymmetricAlgebra L V) _ (SymmetricAlgebra.ι L V v))) : f = h := by
  apply IsFractionRing.ringHom_ext (A := SymmetricAlgebra L V)
  intro p
  induction p using SymmetricAlgebra.induction with
  | algebraMap a => exact hL a
  | ι v => exact hV v
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

end FieldExt

end M9.SemilinearHomCoordinates
