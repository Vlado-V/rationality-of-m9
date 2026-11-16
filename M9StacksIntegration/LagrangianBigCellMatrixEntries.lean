module

public import M9StacksIntegration.LagrangianBigCellQuotient

/-! The literal last three columns of the original native LG quotient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace M9Native.LagrangianBigCellQuotient
open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPluckerTrivialization AlgebraicGeometry.Grassmannian

/-- The actual normalized chart quotient matrix commutes with every
scheme pullback. This retains its literal original coordinate functions. -/
theorem chartQuotient_comp_matrix {T S : Scheme.{u}} {k n : ℕ}
    (ι : Fin (n-k) ↪ Fin n) (f : T ⟶ S)
    (g : S ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    Stacks.FreeSheafMatrix.toMatrix (X := T) (a := n) (b := n-k)
      (chartQuotientMap k n ι (f ≫ g))=
    (Stacks.FreeSheafMatrix.toMatrix (X := S) (a := n) (b := n-k)
      (chartQuotientMap k n ι g)).map f.appTop.hom := by
  have hc : AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} ι) (f ≫ g)=
      fun a => f.appTop (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} ι) g a) :=
    funext (fun a => AffineSpace.toSpecMvPolyIntEquiv_comp (ChartIndex.{u} ι) f g a)
  exact (toMatrix_chartQuotientMap ι (f ≫ g)).trans
    ((congrArg (chartMatrix ι) hc).trans
      ((chartMatrix_map ι f.appTop.hom
          (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} ι) g)).trans
        (congrArg (fun M : Matrix (Fin (n-k)) (Fin n) Γ(S,⊤) => M.map f.appTop.hom)
          (toMatrix_chartQuotientMap ι g).symm)))

variable (K : Type u) [Field K]

/-- The actual original big-cell quotient matrix is the actual original
matrix-chart quotient matrix with its coefficients pulled back. -/
theorem bigCellQuotient_matrix :
    Stacks.FreeSheafMatrix.toMatrix
      (X := Spec (.of (MvPolynomial (Fin 6) K))) (a := 6) (b := 3)
      ((pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫
        (bigCellQuotientIso K).hom)=
    (Stacks.FreeSheafMatrix.toMatrix (matrixQuotientMap K)).map
      (bigCellMatrixMap K).appTop.hom :=
  (congrArg (Stacks.FreeSheafMatrix.toMatrix
    (X := Spec (.of (MvPolynomial (Fin 6) K))) (a := 6) (b := 3))
      (bigCellQuotientIso_triangle K)).trans
    (chartQuotient_comp_matrix firstPivot (bigCellMatrixMap K) (integralChartPoint K))

/-- Its last three columns are the literal six independent symmetric
polynomial coordinates in the original native numbering. -/
theorem bigCellQuotient_last (i j : Fin 3) :
    Stacks.FreeSheafMatrix.toMatrix
      (X := Spec (.of (MvPolynomial (Fin 6) K))) (a := 6) (b := 3)
      ((pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫
        (bigCellQuotientIso K).hom) i (Fin.natAdd 3 j)=
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 6) K))).inv
        (MvPolynomial.X (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))) :=
  (congrArg (fun M : Matrix (Fin 3) (Fin 6) Γ(Spec (.of (MvPolynomial (Fin 6) K)),⊤) =>
    M i (Fin.natAdd 3 j)) (bigCellQuotient_matrix K)).trans
      ((congrArg (fun x : Γ(Spec (.of (MatrixRing K)),⊤) => (bigCellMatrixMap K).appTop x)
        (matrixQuotient_last K i j)).trans (bigCellMatrixMap_matrixEntry K i j))

end M9Native.LagrangianBigCellQuotient
