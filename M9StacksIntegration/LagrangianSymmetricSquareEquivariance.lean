module

public import M9StacksIntegration.LagrangianSymmetricSquare
public import StacksFrontier.LinearAlgebra.SymmetricPower.TensorSquareCauchy

/-! Actual normalized symmetric-square naturality under every coefficient matrix. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators TensorProduct

universe u

namespace M9Native.LagrangianSymmetricSquare

open LagrangianInfinitesimal LagrangianSymmetricCongruence

variable (R : Type u) [CommRing R] [Invertible (2 : R)]

/-- The literal normalized symmetrized outer product. -/
def outer (v w : Fin 3 → R) : symmetricMatrices R :=
  ⟨fun i j => ⅟(2:R)*(v i*w j+w i*v j),by
    change (fun i j => ⅟(2:R)*(v j*w i+w j*v i))= _
    funext i j
    ring⟩

def outerBilinear : (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] symmetricMatrices R where
  toFun v :=
    { toFun := outer R v
      map_add' w z := by ext i j; simp [outer]; ring
      map_smul' r w := by ext i j; simp [outer]; ring }
  map_add' v w := by ext z i j; simp [outer]; ring
  map_smul' r v := by ext z i j; simp [outer]; ring

theorem outer_swap (v w : Fin 3 → R) : outerBilinear R v w=outerBilinear R w v := by
  ext i j
  simp [outerBilinear,outer,add_comm]

/-- The genuine universal-property map from the native symmetric square. -/
def toMatrices : Square R →ₗ[R] symmetricMatrices R :=
  SymPow.sqLift (outerBilinear R) (outer_swap R)

omit [Invertible (2 : R)] in
theorem monomialBasis_eq_product (i : Fin 6) :
    monomialBasis R i=SymPow.sqMul (LinearMap.id : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
      (Pi.single (upperPair i).1 1 ⊗ₜ[R] Pi.single (upperPair i).2 1) := by
  apply Subtype.ext
  rw [monomialBasis_coe,SymPow.sqMul_tmul]
  rfl

/-- The explicit half-coordinate normalization is exactly the actual
symmetric bilinear universal-property map. -/
theorem toMatrices_eq_squareEquiv : toMatrices R=(squareEquivMatrices R).toLinearMap := by
  have hcoordinates (B : symmetricMatrices R) (k : Fin 6) :
      coordinates R B k=B.val (upperPair k).1 (upperPair k).2 := by
    fin_cases k <;> rfl
  have hhalf (v : Fin 6 → R) (k : Fin 6) :
      halfCoordinates R v k=
        (if (upperPair k).1=(upperPair k).2 then 1 else ⅟(2:R))*v k := by
    fin_cases k <;> simp [halfCoordinates,upperPair]
  have hdelta (a b c d : Fin 3) :
      (Pi.single a (1:R) : Fin 3 → R) c*(Pi.single b (1:R) : Fin 3 → R) d=
        if a=c ∧ b=d then 1 else 0 := by
    by_cases ha : a=c <;> by_cases hb : b=d <;>
      simp [ha,hb,eq_comm]
  apply (monomialBasis R).ext
  intro i
  have ht : toMatrices R (monomialBasis R i)=
      outer R (Pi.single (upperPair i).1 1) (Pi.single (upperPair i).2 1) := by
    rw [monomialBasis_eq_product]
    exact SymPow.sqLift_sqMul_tmul (outerBilinear R) (outer_swap R) _ _
  rw [ht]
  apply (coordinates R).injective
  change coordinates R (outer R _ _)=
    halfCoordinates R ((monomialBasis R).equivFun (monomialBasis R i))
  funext j
  rw [hcoordinates,hhalf,Module.Basis.equivFun_self]
  change ⅟(2:R)*
      ((Pi.single (upperPair i).1 (1:R) : Fin 3 → R) (upperPair j).1*
          (Pi.single (upperPair i).2 (1:R) : Fin 3 → R) (upperPair j).2+
        (Pi.single (upperPair i).2 (1:R) : Fin 3 → R) (upperPair j).1*
          (Pi.single (upperPair i).1 (1:R) : Fin 3 → R) (upperPair j).2)=
    (if (upperPair j).1=(upperPair j).2 then 1 else ⅟(2:R))*
      (if i=j then 1 else 0)
  rw [hdelta,hdelta]
  by_cases hij : i=j
  · subst j
    by_cases hd : (upperPair i).1=(upperPair i).2
    · simp [hd,one_add_one_eq_two]
    · simp [hd,Ne.symm hd]
  · have hforward : ¬ ((upperPair i).1=(upperPair j).1 ∧
        (upperPair i).2=(upperPair j).2) := by
      rintro ⟨ha,hb⟩
      apply hij
      apply quadraticIndex_injective
      apply Subtype.ext
      change Finsupp.single (upperPair i).1 1+Finsupp.single (upperPair i).2 1=
        Finsupp.single (upperPair j).1 1+Finsupp.single (upperPair j).2 1
      rw [ha,hb]
    have hreverse : ¬ ((upperPair i).2=(upperPair j).1 ∧
        (upperPair i).1=(upperPair j).2) := by
      rintro ⟨ha,hb⟩
      apply hij
      apply quadraticIndex_injective
      apply Subtype.ext
      change Finsupp.single (upperPair i).1 1+Finsupp.single (upperPair i).2 1=
        Finsupp.single (upperPair j).1 1+Finsupp.single (upperPair j).2 1
      rw [ha,hb,add_comm]
    simp [hij,hforward,hreverse]

theorem squareEquiv_product (v w : Fin 3 → R) :
    squareEquivMatrices R (SymPow.sqMul (LinearMap.id : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
      (v ⊗ₜ[R] w))=outer R v w := by
  change (squareEquivMatrices R).toLinearMap _= _
  rw [← toMatrices_eq_squareEquiv]
  exact SymPow.sqLift_sqMul_tmul (outerBilinear R) (outer_swap R) v w

omit [Invertible (2 : R)] in
theorem symMap_product (P : Matrix (Fin 3) (Fin 3) R) (v w : Fin 3 → R) :
    SymPow.symMap 2 P.mulVecLin
      (SymPow.sqMul (LinearMap.id : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (v ⊗ₜ[R] w))=
      SymPow.sqMul LinearMap.id ((P*ᵥv) ⊗ₜ[R] (P*ᵥw)) := by
  apply Subtype.ext
  simp only [SymPow.symMap_coe,SymPow.sqMul_tmul,map_mul,SymPow.symAlgMap_ι,
    LinearMap.id_apply,Matrix.mulVecLin_apply]

theorem outer_congruence (P : Matrix (Fin 3) (Fin 3) R) (v w : Fin 3 → R) :
    outer R (P*ᵥv) (P*ᵥw)=congruence R P (outer R v w) := by
  apply Subtype.ext
  funext i j
  simp [outer,congruence,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

/-- The exact naturality needed to glue native symmetric-square
determinants. It applies to every actual coefficient matrix. -/
theorem squareEquivMatrices_symMap (P : Matrix (Fin 3) (Fin 3) R) (x : Square R) :
    squareEquivMatrices R (SymPow.symMap 2 P.mulVecLin x)=
      congruence R P (squareEquivMatrices R x) := by
  have h : (squareEquivMatrices R).toLinearMap.comp (SymPow.symMap 2 P.mulVecLin)=
      (congruence R P).comp (squareEquivMatrices R).toLinearMap := by
    apply SymPow.sqMul_ext
    intro v w
    exact (congrArg (squareEquivMatrices R) (symMap_product R P v w)).trans
      ((squareEquiv_product R (P*ᵥv) (P*ᵥw)).trans
        ((outer_congruence R P v w).trans
          (congrArg (congruence R P) (squareEquiv_product R v w).symm)))
  exact LinearMap.congr_fun h x

end M9Native.LagrangianSymmetricSquare
