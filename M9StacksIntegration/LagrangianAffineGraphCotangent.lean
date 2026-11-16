module

public import M9StacksIntegration.LagrangianNativeGraphCotangent
public import M9StacksIntegration.LagrangianPolynomialDifferentials
public import M9StacksIntegration.LagrangianGraphSectionMap

/-! Genuine native affine section differentials for the original graph coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianAffineGraphCotangent

open LagrangianGraphDifferentials LagrangianGraphCotangent LagrangianGraphSectionMap
open LagrangianInfinitesimal LagrangianSymmetricCongruence LagrangianNativeGraphCotangent
open LagrangianPolynomialDifferentials LagrangianChartCotangent LagrangianDualCoefficients
open LagrangianGrassmannian LagrangianCotangentMap

variable (K : Type u) [Field K]

/-- The original polynomial graph matrix, as genuine structure sheaf
sections through the native affine structure-ring isomorphism. -/
def sectionMatrix : symmetricMatrices Γ(chart K,⊤) :=
  ⟨fun i j => scalarEquiv K ((nativeMatrix K).val i j),by
    funext i j
    exact congrArg (scalarEquiv K)
      (congrFun (congrFun (nativeMatrix K).property i) j)⟩

theorem sectionMatrix_upper (i : Fin 6) :
    (sectionMatrix K).val (upperPair i).2 (upperPair i).1=
      scalarEquiv K (MvPolynomial.X (nativeVariableEquiv.{u} i)) :=
  congrArg (scalarEquiv K) (nativeMatrix_upper K i)

/-- The native universal relative differential of the six actual
coordinate functions forms a basis, giving bijectivity of the actual
graph formula on actual scheme sections. -/
theorem nativeSectionGraphSquareMap_bijective :
    Function.Bijective (graphSquareMap Γ(chart K,⊤)
      (localDerivation (chartProjection K) ⊤) (sectionMatrix K)) := by
  apply graphSquareMap_bijective _ _
    ((sectionsBasis K).reindex nativeVariableEquiv.{u}.symm)
  intro i
  rw [sectionMatrix_upper]
  change (Scheme.Hom.universalRelativeDerivation (chartProjection K)).d
    (scalarEquiv K (MvPolynomial.X (nativeVariableEquiv.{u} i)))=_
  simp only [Module.Basis.reindex_apply,Equiv.symm_symm,sectionsBasis_apply]

end M9Native.LagrangianAffineGraphCotangent
