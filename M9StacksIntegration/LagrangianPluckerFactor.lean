module

public import M9StacksIntegration.LagrangianPluckerLinear

/-! The exact coordinate evaluation identities used to compare the actual
primitive projective morphism with the native full Plucker morphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Module
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianPluckerFactor
open M9Native.LagrangianPluckerLinear
variable (K : Type u) [Field K]

theorem primitiveLinearMap_basis (c : MinorIndex) :
    primitiveLinearMap K (Pi.basisFun K MinorIndex c)=
      (M9Native.LagrangianField.coordinate3 K c).comp (M9Native.LagrangianField.Primitive K).subtype := by
  rw [primitiveLinearMap,LinearMap.comp_apply,coordinateLinearMap,Basis.constr_basis]
  rfl

variable [CharZero K]

theorem primitiveBasis14_val (j : Fin 14) :
    (primitiveBasis14 K j).val=M9Native.LagrangianField.coordinateEmbedding K
      (M9Native.LagrangianField.coordinateBasis14 K j) := by
  rw [primitiveBasis14,Basis.map_apply,M9Native.LagrangianField.primitiveEquiv_val]

theorem primitiveLinearMap_basis_coordinate (c : MinorIndex) (j : Fin 14) :
    primitiveLinearMap K (Pi.basisFun K MinorIndex c) (primitiveBasis14 K j)=
      M9Native.LagrangianField.primitiveMinor14 K c (Pi.single j 1) := by
  rw [primitiveLinearMap_basis,LinearMap.comp_apply]
  change M9Native.LagrangianField.coordinate3 K c ((primitiveBasis14 K j).val)=_
  rw [primitiveBasis14_val]
  change _=M9Native.LagrangianField.coordinate3 K c
    (M9Native.LagrangianField.coordinateEmbedding K
      ((M9Native.LagrangianField.coordinateBasis14 K).equivFun.symm (Pi.single j 1)))
  rw [Basis.equivFun_symm_single]

section RingEvaluation
variable {R : Type u} [CommRing R]

def primitiveEvaluation (κ : K →+* R) (s : Fin 14 → R) :
    SymmetricAlgebra K (Module.Dual K (Primitive K)) →+* R :=
  (MvPolynomial.eval₂Hom κ s).comp
    (SymPow.gradedMvPolynomialHom (primitiveBasis14 K).dualBasis).toRingHom

theorem primitiveEvaluation_ι (κ : K →+* R) (s : Fin 14 → R)
    (ell : Module.Dual K (Primitive K)) :
    primitiveEvaluation K κ s (SymmetricAlgebra.ι K _ ell)=
      ∑ j : Fin 14,κ (ell (primitiveBasis14 K j))*s j := by
  have h := congrArg (fun v => SymmetricAlgebra.equivMvPolynomial (primitiveBasis14 K).dualBasis
    (SymmetricAlgebra.ι K _ v)) ((primitiveBasis14 K).dualBasis.sum_repr ell)
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply,Basis.dualBasis_repr] at h
  have hh := congrArg (MvPolynomial.eval₂Hom κ s) h.symm
  simpa only [primitiveEvaluation,RingHom.comp_apply,GradedRingHom.coe_toRingHom,
    SymPow.gradedMvPolynomialHom_apply,map_sum,MvPolynomial.smul_eq_C_mul,map_mul,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X'] using hh

omit [CharZero K] in
theorem coordinate3_basis_map (κ : K →+* R) (c : MinorIndex) (j : Fin 20) :
    κ (M9Native.LagrangianField.coordinate3 K c (M9Native.LagrangianField.thirdBasis20 K j))=
      M9Native.LagrangianRing.coordinate3 R c (M9Native.LagrangianRing.thirdBasis20 R j) := by
  change κ (M9Native.LagrangianRing.coordinate3 K c (M9Native.LagrangianRing.thirdBasis20 K j))=_
  rw [M9Native.LagrangianRing.thirdBasis20_apply,M9Native.LagrangianRing.thirdBasis20_apply]
  simp only [M9Native.LagrangianRing.coordinate3,exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [RingHom.map_det]
  congr 1
  ext i k
  have hf (p : Prop) [Decidable p] (a b : K) : κ (if p then a else b)=(if p then κ a else κ b) := by
    split_ifs <;> rfl
  simp [M9Native.LagrangianRing.basisVector,Pi.single_apply,hf]

omit [CharZero K] in
theorem primitiveMinor14_basis_sum (c : MinorIndex) (j : Fin 14) :
    M9Native.LagrangianField.primitiveMinor14 K c (Pi.single j 1)=
      ∑ i : Fin 20,M9Native.LagrangianField.embeddingMatrix K i j*
        M9Native.LagrangianField.coordinate3 K c (M9Native.LagrangianField.thirdBasis20 K i) := by
  have hb := Basis.equivFun_symm_single (M9Native.LagrangianField.coordinateBasis14 K) j
  have hc : M9Native.LagrangianRing.coordinate3 K c=M9Native.LagrangianField.coordinate3 K c := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change M9Native.LagrangianRing.coordinate3 K c (exteriorPower.ιMulti K 3 v)=
      M9Native.LagrangianField.coordinate3 K c (exteriorPower.ιMulti K 3 v)
    simp only [M9Native.LagrangianRing.coordinate3,M9Native.LagrangianField.coordinate3,
      exteriorPower.pairingDual_ιMulti_ιMulti]
  have hs : M9Native.LagrangianField.coordinate3 K c
      (M9Native.LagrangianField.coordinateEmbedding K (M9Native.LagrangianField.coordinateBasis14 K j))=
      ∑ i : Fin 20,M9Native.LagrangianField.embeddingMatrix K i j*
        M9Native.LagrangianField.coordinate3 K c (M9Native.LagrangianField.thirdBasis20 K i) := by
    simpa only [M9Native.LagrangianField.embeddingMatrix,LinearMap.toMatrix_apply,
      Basis.equivFun_apply,M9Native.LagrangianRing.thirdBasis20_eq_field,hc] using
      M9Native.LagrangianRing.coordinate3_eq_sum K
        (M9Native.LagrangianField.coordinateEmbedding K (M9Native.LagrangianField.coordinateBasis14 K j)) c
  exact (congrArg (fun v => M9Native.LagrangianField.coordinate3 K c
    (M9Native.LagrangianField.coordinateEmbedding K v)) hb).trans hs

omit [CharZero K] in
/-- Base change of the exact primitive minor functional, including on
coordinate rings with nilpotents. -/
theorem minorFourteen_eq_sum (κ : K →+* R) (c : MinorIndex) (s : Fin 14 → R) :
    M9Native.LagrangianRing.minorFourteen R κ c s=
      ∑ j : Fin 14,κ (M9Native.LagrangianField.primitiveMinor14 K c (Pi.single j 1))*s j := by
  simp only [M9Native.LagrangianRing.minorFourteen,Matrix.mulVec_apply_eq_sum,
    Matrix.map_apply,primitiveMinor14_basis_sum,map_sum,map_mul,coordinate3_basis_map,Finset.sum_mul]
  calc
    _ = ∑ j : Fin 14,∑ i : Fin 20,κ (M9Native.LagrangianField.embeddingMatrix K i j)*s j*
        M9Native.LagrangianRing.coordinate3 R c (M9Native.LagrangianRing.thirdBasis20 R i) :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
      ring

/-- Evaluating the actual restricted coordinate form gives precisely the
actual scalar-extended primitive minor. -/
theorem primitiveEvaluation_coordinate (κ : K →+* R) (s : Fin 14 → R) (c : MinorIndex) :
    primitiveEvaluation K κ s (SymmetricAlgebra.ι K _
      (primitiveLinearMap K (Pi.basisFun K MinorIndex c)))=
        M9Native.LagrangianRing.minorFourteen R κ c s := by
  rw [primitiveEvaluation_ι,minorFourteen_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [primitiveLinearMap_basis_coordinate]

end RingEvaluation
end M9Native.LagrangianPluckerFactor
