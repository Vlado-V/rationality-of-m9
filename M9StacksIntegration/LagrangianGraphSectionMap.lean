module

public import M9StacksIntegration.LagrangianFreeDualSections
public import M9StacksIntegration.LagrangianCotangentSections
public import M9StacksIntegration.LagrangianGraphCotangent
public import M9StacksIntegration.SymmetricSquareFreeFrames

/-! Exact original sheaf section formulas for an actual graph quotient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators TensorProduct

universe u

namespace M9Native.LagrangianGraphSectionMap

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianLocalPairing LagrangianCotangentFormula
open LagrangianFreeDualSections LagrangianInfinitesimal LagrangianGraphDifferentials
open LagrangianGraphCotangent LagrangianSymmetricSquare LagrangianSymmetricCongruence
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X S : Scheme.{u}} (p : X ⟶ S) (q : freeOn X 6 ⟶ freeOn X 3)
  (A : symmetricMatrices Γ(X,⊤))
  (hfirst : ∀ i j : Fin 3,Stacks.FreeSheafMatrix.toMatrix q i (j.castAdd 3)=
    if i=j then 1 else 0)
  (hlast : ∀ i j : Fin 3,Stacks.FreeSheafMatrix.toMatrix q i (Fin.natAdd 3 j)=A.val i j)

include hfirst hlast

/-- The original quotient's actual dual coefficients equal the literal
graph coefficients, through the proved actual dual-section coordinates. -/
theorem coefficientMap_graph (α : Γ(dualSheaf (freeOn X 3),⊤)) :
    coefficientMap q ⊤ α=graphCoefficients Γ(X,⊤) A.val (freeDualCoordinates X 3 α) := by
  funext j
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  · rw [graphCoefficients_left,coefficientMap_free]
    simp [hfirst]
  · rw [graphCoefficients_right,coefficientMap_free]
    simp only [hlast]

/-- Equality of the actual sheaf's section map and the actual graph
calculus map, with the original quotient map retained. -/
theorem localSquareMap_graph (hq : AnnihilatesSigma X q) :
    localSquareMap p q hq ⊤=
      (graphSquareMap Γ(X,⊤) (localDerivation p ⊤) A).comp
        (SymPow.symMap 2 (freeDualCoordinates X 3).toLinearMap) := by
  apply SymPow.ext_of_prod_ι
  intro s
  have hp : (⟨∏ i : Fin 2,SymmetricAlgebra.ι Γ(X,⊤) Γ(dualSheaf (freeOn X 3),⊤) (s i),
      SymmetricAlgebra.prod_ι_mem _ s⟩ :
        SymPow.symmetricPower 2 Γ(X,⊤) Γ(dualSheaf (freeOn X 3),⊤))=
      SymPow.sqMul LinearMap.id (s 0 ⊗ₜ[Γ(X,⊤)] s 1) := by
    apply Subtype.ext
    simp [Fin.prod_univ_succ,SymPow.sqMul_tmul]
  rw [hp,localSquareMap_product,LinearMap.comp_apply]
  have hm : SymPow.symMap 2 (freeDualCoordinates X 3).toLinearMap
      (SymPow.sqMul LinearMap.id (s 0 ⊗ₜ[Γ(X,⊤)] s 1))=
      SymPow.sqMul LinearMap.id
        (freeDualCoordinates X 3 (s 0) ⊗ₜ[Γ(X,⊤)] freeDualCoordinates X 3 (s 1)) := by
    apply Subtype.ext
    simp only [SymPow.symMap_coe,SymPow.sqMul_tmul,map_mul,SymPow.symAlgMap_ι,
      LinearMap.id_apply,LinearEquiv.coe_coe]
  rw [hm]
  change differentialPair (localDerivation p ⊤) (coefficientMap q ⊤) (s 0) (s 1)=
    SymPow.sqLift _ _ _
  rw [SymPow.sqLift_sqMul_tmul]
  change differentialPair (localDerivation p ⊤) (coefficientMap q ⊤) (s 0) (s 1)=
    differentialPair (localDerivation p ⊤) (graphCoefficients Γ(X,⊤) A.val)
      (freeDualCoordinates X 3 (s 0)) (freeDualCoordinates X 3 (s 1))
  simp only [differentialPair,coefficientMap_graph q A hfirst hlast]

/-- Actual coordinate differentials forming a basis give bijectivity of
the original section map; every other comparison is already proved. -/
theorem localSquareMap_graph_bijective (hq : AnnihilatesSigma X q)
    (b : Module.Basis (Fin 6) Γ(X,⊤) Γ(Scheme.Hom.relativeDifferentials p,⊤))
    (hb : ∀ i,localDerivation p ⊤ (A.val (upperPair i).2 (upperPair i).1)=b i) :
    Function.Bijective (localSquareMap p q hq ⊤) := by
  rw [localSquareMap_graph p q A hfirst hlast hq]
  exact (graphSquareMap_bijective _ _ b hb).comp
    (SymPow.symmetricPowerCongr 2 (freeDualCoordinates X 3)).bijective

end M9Native.LagrangianGraphSectionMap
