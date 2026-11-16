module

public import M9.FiniteNoNameField
public import M9.WreathFrameComparison
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-! Genuine scalar extension of the frame coordinate representation. The
semilinear action is constructed on the tensor product, and the coordinate
basis is the actual base change of the dual matrix-entry basis. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.ScalarExtendedRepresentation

open Module
open scoped TensorProduct BigOperators

section General

variable (K F G V : Type*) [Field K] [Field F] [Algebra K F] [Group G]
  [MulSemiringAction G F] [SMulCommClass G K F]
  [AddCommGroup V] [Module K V]

def ScalarExtension := F ⊗[K] V

instance scalarExtensionAddCommGroup : AddCommGroup (ScalarExtension K F V) := by
  unfold ScalarExtension
  infer_instance

instance scalarExtensionModule : Module F (ScalarExtension K F V) := by
  unfold ScalarExtension
  infer_instance

instance scalarExtensionBaseModule : Module K (ScalarExtension K F V) := by
  unfold ScalarExtension
  infer_instance

instance scalarExtensionFinite [Module.Finite K V] : Module.Finite F (ScalarExtension K F V) := by
  unfold ScalarExtension
  infer_instance

/-- The named carrier is linearly the genuine tensor product. -/
def underlyingTensorEquiv : ScalarExtension K F V ≃ₗ[F] F ⊗[K] V :=
  LinearEquiv.refl F _

def tmul (a : F) (v : V) : ScalarExtension K F V := a ⊗ₜ[K] v

@[simp] theorem underlyingTensorEquiv_tmul (a : F) (v : V) :
    underlyingTensorEquiv K F V (tmul K F V a v)=a ⊗ₜ[K] v := rfl

/-- The tensor action uses the actual field automorphism on the first factor
and the given genuine representation on the second factor. -/
def tensorOperator (ρ : G →* (V ≃ₗ[K] V)) (g : G) :
    ScalarExtension K F V →ₗ[K] ScalarExtension K F V :=
  TensorProduct.map (MulSemiringAction.toAlgAut G K F g).toLinearMap (ρ g).toLinearMap

@[simp] theorem tensorOperator_tmul (ρ : G →* (V ≃ₗ[K] V)) (g : G) (a : F) (v : V) :
    tensorOperator K F G V ρ g (a ⊗ₜ[K] v)=(g • a) ⊗ₜ[K] (ρ g v) := rfl

theorem tensorOperator_one (ρ : G →* (V ≃ₗ[K] V)) :
    tensorOperator K F G V ρ 1=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change F ⊗[K] V at x
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp
  | add x y hx hy => simp [hx,hy]

theorem tensorOperator_mul (ρ : G →* (V ≃ₗ[K] V)) (g h : G) :
    tensorOperator K F G V ρ (g*h)=
      (tensorOperator K F G V ρ g).comp (tensorOperator K F G V ρ h) := by
  apply LinearMap.ext
  intro x
  change F ⊗[K] V at x
  change tensorOperator K F G V ρ (g*h) x=
    tensorOperator K F G V ρ g (tensorOperator K F G V ρ h x)
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [mul_smul]
  | add x y hx hy => simp [hx,hy]

/-- The actual additive group action on scalar-extended vectors. -/
@[instance_reducible] def tensorAction (ρ : G →* (V ≃ₗ[K] V)) :
    DistribMulAction G (ScalarExtension K F V) where
  smul g x := tensorOperator K F G V ρ g x
  one_smul x := by
    change tensorOperator K F G V ρ 1 x=x
    rw [tensorOperator_one]
    rfl
  mul_smul g h x := by
    change tensorOperator K F G V ρ (g*h) x=
      tensorOperator K F G V ρ g (tensorOperator K F G V ρ h x)
    rw [tensorOperator_mul]
    rfl
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

theorem tensorOperator_smul (ρ : G →* (V ≃ₗ[K] V)) (g : G) (a : F)
    (x : ScalarExtension K F V) :
    tensorOperator K F G V ρ g (a • x)=(g • a) • tensorOperator K F G V ρ g x := by
  change F ⊗[K] V at x
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    change tensorOperator K F G V ρ g ((a*c) ⊗ₜ[K] v)=
      ((g • a) • tensorOperator K F G V ρ g (c ⊗ₜ[K] v) : F ⊗[K] V)
    rw [tensorOperator_tmul,tensorOperator_tmul,smul_mul']
    rfl
  | add x y hx hy =>
    simp only [smul_add,map_add,hx,hy]

/-- Compatibility with the coefficient action is proved semilinearity. -/
theorem tensorSemilinear (ρ : G →* (V ≃ₗ[K] V)) :
    letI := tensorAction K F G V ρ
    SMulDistribClass G F (ScalarExtension K F V) := by
  let := tensorAction K F G V ρ
  exact ⟨tensorOperator_smul K F G V ρ⟩

theorem action_tmul (ρ : G →* (V ≃ₗ[K] V)) (g : G) (a : F) (v : V) :
    letI := tensorAction K F G V ρ
    g • tmul K F V a v=tmul K F V (g • a) (ρ g v) :=
  tensorOperator_tmul K F G V ρ g a v

variable {ι : Type*} [Fintype ι]

/-- The coordinate basis is a genuine scalar-extended basis. -/
def scalarBasis (b : Basis ι K V) : Basis ι F (ScalarExtension K F V) := b.baseChange F

omit [Fintype ι] in
@[simp] theorem scalarBasis_apply (b : Basis ι K V) (i : ι) :
    scalarBasis K F V b i=(1 : F) ⊗ₜ[K] b i := Basis.baseChange_apply _ _ _

/-- The standard coordinate realization is proved from the tensor basis. -/
def scalarExtensionEquiv (b : Basis ι K V) : ScalarExtension K F V ≃ₗ[F] (ι → F) :=
  (scalarBasis K F V b).equivFun

@[simp] theorem scalarExtensionEquiv_tmul (b : Basis ι K V) (a : F) (v : V) (i : ι) :
    scalarExtensionEquiv K F V b (a ⊗ₜ[K] v) i=algebraMap K F (b.repr v i)*a := by
  change (b.baseChange F).repr (a ⊗ₜ[K] v) i=_
  rw [Basis.baseChange_repr_tmul]
  exact Algebra.smul_def _ _

theorem finrank_scalarExtension (b : Basis ι K V) :
    finrank F (ScalarExtension K F V)=Fintype.card ι :=
  finrank_eq_card_basis (scalarBasis K F V b)

omit [Fintype ι] in
theorem scalarBasis_action_coordinates (ρ : G →* (V ≃ₗ[K] V)) (b : Basis ι K V)
    (g : G) (i j : ι) :
    letI := tensorAction K F G V ρ
    (scalarBasis K F V b).repr (g • scalarBasis K F V b i) j=
      algebraMap K F (b.repr (ρ g (b i)) j) := by
  rw [scalarBasis_apply]
  change (scalarBasis K F V b).repr
    (tensorOperator K F G V ρ g ((1 : F) ⊗ₜ[K] b i)) j=_
  rw [tensorOperator_tmul,smul_one]
  change (b.baseChange F).repr ((1 : F) ⊗ₜ[K] (ρ g (b i))) j=_
  rw [Basis.baseChange_repr_tmul,Algebra.smul_def,mul_one]

theorem scalarBasis_action (ρ : G →* (V ≃ₗ[K] V)) (b : Basis ι K V) (g : G) (i : ι) :
    letI := tensorAction K F G V ρ
    g • scalarBasis K F V b i=
      ∑ j, algebraMap K F (b.repr (ρ g (b i)) j) • scalarBasis K F V b j := by
  let := tensorAction K F G V ρ
  simpa only [scalarBasis_action_coordinates K F G V ρ b g i] using
    ((scalarBasis K F V b).sum_repr (g • scalarBasis K F V b i)).symm

end General

section Dual

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The genuine coordinate representation is contragredient: precomposition
with the inverse native point operator. -/
def dualRepresentation (ρ : G →* (V ≃ₗ[K] V)) :
    G →* (Dual K V ≃ₗ[K] Dual K V) where
  toFun g := (ρ g⁻¹).dualMap
  map_one' := by
    ext α v
    simp
  map_mul' g h := by
    ext α v
    simp [mul_inv_rev]

@[simp] theorem dualRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (g : G)
    (α : Dual K V) (v : V) : dualRepresentation ρ g α v=α (ρ g⁻¹ v) := rfl

end Dual

section Frame

abbrev FrameGroup := FrameAction.TetrahedralFrameGroup
abbrev FrameField := WreathFrameComparison.FramePermutationField ℂ
abbrev FramePoint := FrameAction.Mat3 ℂ
abbrev FrameDual := Dual ℂ FramePoint
abbrev FrameIndex := Fin 3 × Fin 3
abbrev FrameModule := ScalarExtension ℂ FrameField FrameDual

def frameDualRepresentation : FrameGroup →* (FrameDual ≃ₗ[ℂ] FrameDual) :=
  dualRepresentation FrameAction.tetrahedralRepresentation

instance frameModuleAction : DistribMulAction FrameGroup FrameModule :=
  tensorAction ℂ FrameField FrameGroup FrameDual frameDualRepresentation

instance frameModuleSemilinear : SMulDistribClass FrameGroup FrameField FrameModule :=
  tensorSemilinear ℂ FrameField FrameGroup FrameDual frameDualRepresentation

def frameDualBasis : Basis FrameIndex ℂ FrameDual := (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).dualBasis

def frameBasis : Basis FrameIndex FrameField FrameModule :=
  scalarBasis ℂ FrameField FrameDual frameDualBasis

def frameCoordinates : FrameModule ≃ₗ[FrameField] (FrameIndex → FrameField) := frameBasis.equivFun

@[simp] theorem frameBasis_apply (i : FrameIndex) : frameBasis i=(1 : FrameField) ⊗ₜ[ℂ] frameDualBasis i :=
  scalarBasis_apply ℂ FrameField FrameDual frameDualBasis i

theorem finrank_frameModule : finrank FrameField FrameModule=9 := by
  rw [finrank_eq_card_basis frameBasis]
  norm_num [FrameIndex]

theorem frame_action_tmul (g : FrameGroup) (a : FrameField) (α : FrameDual) :
    g • tmul ℂ FrameField FrameDual a α=
      tmul ℂ FrameField FrameDual (g • a) (frameDualRepresentation g α) :=
  tensorOperator_tmul ℂ FrameField FrameGroup FrameDual frameDualRepresentation g a α

theorem frameBasis_action (g : FrameGroup) (i : FrameIndex) :
    g • frameBasis i=∑ j, algebraMap ℂ FrameField
      (frameDualBasis.repr (frameDualRepresentation g (frameDualBasis i)) j) • frameBasis j :=
  scalarBasis_action ℂ FrameField FrameGroup FrameDual frameDualRepresentation frameDualBasis g i

/-- Actual inverse point-matrix coefficients for the coordinate representation. -/
def frameCoefficient (g : FrameGroup) (i j : FrameIndex) : ℂ :=
  frameDualBasis i (FrameAction.tetrahedralRepresentation g⁻¹
    (Matrix.stdBasis ℂ (Fin 3) (Fin 3) j))

theorem frameCoefficient_eq_repr (g : FrameGroup) (i j : FrameIndex) :
    frameCoefficient g i j=frameDualBasis.repr (frameDualRepresentation g (frameDualBasis i)) j := by
  simp only [frameDualBasis,Basis.dualBasis_repr,frameCoefficient,frameDualRepresentation,
    dualRepresentation_apply]

theorem frameBasis_action_native (g : FrameGroup) (i : FrameIndex) :
    g • frameBasis i=∑ j, algebraMap ℂ FrameField (frameCoefficient g i j) • frameBasis j := by
  simpa only [frameCoefficient_eq_repr] using frameBasis_action g i

abbrev FrameCoordinateRing := FiniteNoNameField.CoordinateRing FrameField FrameModule
abbrev FrameCoordinateField := FiniteNoNameField.CoordinateField FrameField FrameModule

def frameInvariantBasis := FiniteGaloisDescent.invariantBasis FrameGroup FrameField FrameModule

/-- The ring action is genuine finite semilinear descent, with compatibility
on every originally given degree-one vector proved below. -/
@[instance_reducible] def framePolynomialAction : MulSemiringAction FrameGroup FrameCoordinateRing :=
  FiniteNoNameField.symmetricPolynomialAction FrameGroup FrameField FrameModule frameInvariantBasis

@[instance_reducible] def frameRationalAction : MulSemiringAction FrameGroup FrameCoordinateField :=
  FiniteNoNameField.symmetricRationalAction FrameGroup FrameField FrameModule frameInvariantBasis

theorem frame_polynomial_constant (g : FrameGroup) (a : FrameField) :
    letI := framePolynomialAction
    g • algebraMap FrameField FrameCoordinateRing a=algebraMap FrameField FrameCoordinateRing (g • a) :=
  FiniteNoNameField.symmetricPolynomialAction_constant FrameGroup FrameField FrameModule _ g a

theorem frame_polynomial_generator (g : FrameGroup) (x : FrameModule) :
    letI := framePolynomialAction
    g • SymmetricAlgebra.ι FrameField FrameModule x=
      SymmetricAlgebra.ι FrameField FrameModule (g • x) :=
  FiniteNoNameField.symmetricPolynomialAction_iota FrameGroup FrameField FrameModule _
    (FiniteGaloisDescent.invariantBasis_fixed FrameGroup FrameField FrameModule) g x

theorem frame_rational_constant (g : FrameGroup) (a : FrameField) :
    letI := frameRationalAction
    g • algebraMap FrameField FrameCoordinateField a=algebraMap FrameField FrameCoordinateField (g • a) :=
  FiniteNoNameField.symmetricRationalAction_constant FrameGroup FrameField FrameModule _ g a

theorem frame_rational_generator (g : FrameGroup) (x : FrameModule) :
    letI := frameRationalAction
    g • algebraMap FrameCoordinateRing FrameCoordinateField (SymmetricAlgebra.ι FrameField FrameModule x)=
      algebraMap FrameCoordinateRing FrameCoordinateField (SymmetricAlgebra.ι FrameField FrameModule (g • x)) :=
  FiniteNoNameField.symmetricRationalAction_iota FrameGroup FrameField FrameModule _
    (FiniteGaloisDescent.invariantBasis_fixed FrameGroup FrameField FrameModule) g x

end Frame

section PermutationRepresentation

variable {K G ι : Type*} [Field K] [Group G]

def permutationRepresentation (π : G →* Equiv.Perm ι) :
    G →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun g := LinearEquiv.funCongrLeft K K (π g).symm
  map_one' := by
    ext v i
    change v ((π 1).symm i)=v i
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v i
    change v ((π (g*h)).symm i)=v ((π h).symm ((π g).symm i))
    rw [map_mul]
    rfl

@[simp] theorem permutationRepresentation_apply (π : G →* Equiv.Perm ι) (g : G) (v : ι → K) (i : ι) :
    permutationRepresentation (K := K) π g v i=v ((π g).symm i) := rfl

theorem permutationRepresentation_basis [Fintype ι] (π : G →* Equiv.Perm ι) (g : G) (i : ι) :
    permutationRepresentation (K := K) π g (Pi.basisFun K ι i)=Pi.basisFun K ι (π g i) := by
  classical
  funext j
  change (Pi.single i (1 : K) : ι → K) ((π g).symm j)=(Pi.single (π g i) 1 : ι → K) j
  simp [Pi.single_apply,Equiv.symm_apply_eq]

end PermutationRepresentation

section PermutationModule

variable (F : Type*) [Field F] [Algebra ℂ F]
  [MulSemiringAction FrameGroup F] [SMulCommClass FrameGroup ℂ F]

abbrev PermutationIndex := SymmetricBlockInvariants.BlockIndex
abbrev PermutationPoint := PermutationIndex → ℂ
abbrev PermutationModule := ScalarExtension ℂ F PermutationPoint

def framePermutationRepresentation : FrameGroup →* (PermutationPoint ≃ₗ[ℂ] PermutationPoint) :=
  permutationRepresentation WreathFrameComparison.frameIndexRepresentation

instance permutationModuleAction : DistribMulAction FrameGroup (PermutationModule F) :=
  tensorAction ℂ F FrameGroup PermutationPoint framePermutationRepresentation

instance permutationModuleSemilinear : SMulDistribClass FrameGroup F (PermutationModule F) :=
  tensorSemilinear ℂ F FrameGroup PermutationPoint framePermutationRepresentation

def permutationBasis : Basis PermutationIndex F (PermutationModule F) :=
  scalarBasis ℂ F PermutationPoint (Pi.basisFun ℂ PermutationIndex)

def permutationCoordinates : PermutationModule F ≃ₗ[F] (PermutationIndex → F) :=
  (permutationBasis F).equivFun

omit [MulSemiringAction FrameGroup F] [SMulCommClass FrameGroup ℂ F] in
@[simp] theorem permutationBasis_apply (i : PermutationIndex) :
    permutationBasis F i=tmul ℂ F PermutationPoint 1 (Pi.basisFun ℂ PermutationIndex i) :=
  scalarBasis_apply ℂ F PermutationPoint (Pi.basisFun ℂ PermutationIndex) i

omit [MulSemiringAction FrameGroup F] [SMulCommClass FrameGroup ℂ F] in
theorem finrank_permutationModule : finrank F (PermutationModule F)=8 := by
  rw [finrank_eq_card_basis (permutationBasis F)]
  norm_num [PermutationIndex,SymmetricBlockInvariants.BlockIndex]

theorem permutationBasis_action (g : FrameGroup) (i : PermutationIndex) :
    g • permutationBasis F i=
      permutationBasis F (WreathFrameComparison.frameIndexRepresentation g i) := by
  rw [permutationBasis_apply,permutationBasis_apply]
  change tensorOperator ℂ F FrameGroup PermutationPoint framePermutationRepresentation g
    ((1 : F) ⊗ₜ[ℂ] (Pi.basisFun ℂ PermutationIndex i))=
      (1 : F) ⊗ₜ[ℂ] (Pi.basisFun ℂ PermutationIndex
        (WreathFrameComparison.frameIndexRepresentation g i))
  rw [tensorOperator_tmul,smul_one]
  congr 1
  exact permutationRepresentation_basis WreathFrameComparison.frameIndexRepresentation g i

abbrev PermutationCoordinateRing := FiniteNoNameField.CoordinateRing F (PermutationModule F)
abbrev PermutationCoordinateField := FiniteNoNameField.CoordinateField F (PermutationModule F)

variable [FaithfulSMul FrameGroup F]

def permutationInvariantBasis := FiniteGaloisDescent.invariantBasis FrameGroup F (PermutationModule F)

@[instance_reducible] def permutationPolynomialAction :
    MulSemiringAction FrameGroup (PermutationCoordinateRing F) :=
  FiniteNoNameField.symmetricPolynomialAction FrameGroup F (PermutationModule F) (permutationInvariantBasis F)

@[instance_reducible] def permutationRationalAction :
    MulSemiringAction FrameGroup (PermutationCoordinateField F) :=
  FiniteNoNameField.symmetricRationalAction FrameGroup F (PermutationModule F) (permutationInvariantBasis F)

theorem permutation_polynomial_constant (g : FrameGroup) (a : F) :
    letI := permutationPolynomialAction F
    g • algebraMap F (PermutationCoordinateRing F) a=algebraMap F (PermutationCoordinateRing F) (g • a) :=
  FiniteNoNameField.symmetricPolynomialAction_constant FrameGroup F (PermutationModule F) _ g a

theorem permutation_polynomial_generator (g : FrameGroup) (x : PermutationModule F) :
    letI := permutationPolynomialAction F
    g • SymmetricAlgebra.ι F (PermutationModule F) x=SymmetricAlgebra.ι F (PermutationModule F) (g • x) :=
  FiniteNoNameField.symmetricPolynomialAction_iota FrameGroup F (PermutationModule F) _
    (FiniteGaloisDescent.invariantBasis_fixed FrameGroup F (PermutationModule F)) g x

theorem permutation_rational_constant (g : FrameGroup) (a : F) :
    letI := permutationRationalAction F
    g • algebraMap F (PermutationCoordinateField F) a=algebraMap F (PermutationCoordinateField F) (g • a) :=
  FiniteNoNameField.symmetricRationalAction_constant FrameGroup F (PermutationModule F) _ g a

theorem permutation_rational_generator (g : FrameGroup) (x : PermutationModule F) :
    letI := permutationRationalAction F
    g • algebraMap (PermutationCoordinateRing F) (PermutationCoordinateField F)
      (SymmetricAlgebra.ι F (PermutationModule F) x)=
        algebraMap (PermutationCoordinateRing F) (PermutationCoordinateField F)
          (SymmetricAlgebra.ι F (PermutationModule F) (g • x)) :=
  FiniteNoNameField.symmetricRationalAction_iota FrameGroup F (PermutationModule F) _
    (FiniteGaloisDescent.invariantBasis_fixed FrameGroup F (PermutationModule F)) g x

theorem permutation_rational_standard_generator (g : FrameGroup) (i : PermutationIndex) :
    letI := permutationRationalAction F
    g • algebraMap (PermutationCoordinateRing F) (PermutationCoordinateField F)
      (SymmetricAlgebra.ι F (PermutationModule F) (permutationBasis F i))=
        algebraMap (PermutationCoordinateRing F) (PermutationCoordinateField F)
          (SymmetricAlgebra.ι F (PermutationModule F)
            (permutationBasis F (WreathFrameComparison.frameIndexRepresentation g i))) := by
  let := permutationRationalAction F
  rw [permutation_rational_generator,permutationBasis_action]

end PermutationModule

end M9.ScalarExtendedRepresentation
