module

public import M9StacksIntegration.LagrangianQuotientPrecomposition
public import M9StacksIntegration.LagrangianSymplecticDifferentials
public import M9StacksIntegration.LagrangianSymplecticAction

/-! Actual ambient constant symplectic covariance of the intrinsic LG cotangent map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianCotangentSymplectic

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianCotangentSections LagrangianLocalPairing LagrangianCotangentFormula
open LagrangianCotangentQuotientFrame LagrangianQuotientPrecomposition
open LagrangianSymplecticDifferentials LagrangianSymplecticAction LagrangianTransitivity
open LagrangianSymmetricPullbackProduct
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}} (K : Type u) [Field K] (p : X ⟶ Spec (.of K))

/-- The literal constant-field map on each actual open. -/
def scalarOnOpen (U : X.Opens) : K →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op).hom.comp (scalarMap K p)

/-- The actual universal relative derivation kills these actual
constant coefficient functions on every open. -/
theorem scalarOnOpen_d_zero (U : X.Opens) (c : K) :
    localDerivation p U (scalarOnOpen K p U c)=0 := by
  have h₀ : localDerivation p ⊤ (scalarMap K p c)=0 :=
    Scheme.Hom.universalRelativeDerivation_d_app_eq_zero p ⊤
      ((Scheme.ΓSpecIso (.of K)).inv c)
  exact (localDerivation_map p (show U≤⊤ from le_top) (scalarMap K p c)).trans
    ((congrArg (fun z => (Scheme.Hom.relativeDifferentials p).presheaf.map
      (homOfLE (show U≤⊤ from le_top)).op z) h₀).trans (map_zero _))

/-- The actual restricted free-bundle matrix is the actual native
symplectic matrix over the original ring of local functions. -/
theorem matrixOnOpen_constant (g : Matrix.symplecticGroup (Fin 3) K) (U : X.Opens) :
    matrixOnOpen (constantFreeIso K p g).hom U=
      matrixSix Γ(X,U) (mapSymplectic K (scalarOnOpen K p U) g) := by
  rw [matrixOnOpen,constantFreeIso_matrix,matrixSix_map]
  rfl

/-- The actual transpose coefficient action is symplectic. -/
theorem matrixOnOpen_transpose_symplectic (g : Matrix.symplecticGroup (Fin 3) K)
    (U : X.Opens) :
    (matrixOnOpen (constantFreeIso K p g).hom U).transpose.transpose *
      standardForm Γ(X,U) * (matrixOnOpen (constantFreeIso K p g).hom U).transpose=
        standardForm Γ(X,U) := by
  rw [matrixOnOpen_constant]
  let gU := mapSymplectic K (scalarOnOpen K p U) g
  let t : Matrix.symplecticGroup (Fin 3) Γ(X,U) :=
    ⟨(gU : Matrix SplitIndex SplitIndex Γ(X,U)).transpose,SymplecticGroup.transpose_mem gU.property⟩
  have ht : matrixSix Γ(X,U) t=(matrixSix Γ(X,U) gU).transpose := rfl
  simpa only [ht] using matrixSix_preserves_standardForm Γ(X,U) t

/-- All entries of the actual restricted constant matrix have zero
actual relative derivative. -/
theorem matrixOnOpen_d_zero (g : Matrix.symplecticGroup (Fin 3) K)
    (U : X.Opens) (i j : Fin 6) :
    localDerivation p U (matrixOnOpen (constantFreeIso K p g).hom U i j)=0 := by
  rw [matrixOnOpen_constant,matrixSix_map]
  exact scalarOnOpen_d_zero K p U (matrixSix K g i j)

variable {Q : X.Modules}

/-- The actual local intrinsic form is unchanged by the actual
constant symplectic free-coordinate change. -/
theorem localPairing_constant_symplectic (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (g : Matrix.symplecticGroup (Fin 3) K)
    (hqa : AnnihilatesSigma X ((constantFreeIso K p g).hom ≫ q))
    (U : X.Opens) (α β : Γ(dualSheaf Q,U)) :
    localPairing p ((constantFreeIso K p g).hom ≫ q) hqa U α β=
      localPairing p q hq U α β := by
  change differentialPair (localDerivation p U)
    (coefficientMap ((constantFreeIso K p g).hom ≫ q) U) α β=
      differentialPair (localDerivation p U) (coefficientMap q U) α β
  rw [coefficientMap_precomp]
  exact differentialPair_constant_symplectic (localDerivation p U)
    (matrixOnOpen (constantFreeIso K p g).hom U).transpose
      (matrixOnOpen_transpose_symplectic K p g U)
        (fun i j => matrixOnOpen_d_zero K p g U j i) _ α β

/-- The actual global sheaf map is invariant under actual constant
symplectic ambient coordinates, with every local coefficient identity
and universal-derivation property proved. -/
theorem cotangentMap_constant_symplectic (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (g : Matrix.symplecticGroup (Fin 3) K)
    (hqa : AnnihilatesSigma X ((constantFreeIso K p g).hom ≫ q)) :
    cotangentMap p ((constantFreeIso K p g).hom ≫ q) hqa=cotangentMap p q hq := by
  apply symmetricHom_ext_products (dualSheaf Q)
  intro U α β
  exact (cotangentMap_squareUnit_product p _ hqa U α β).trans
    ((localPairing_constant_symplectic K p q hq g hqa U α β).trans
      (cotangentMap_squareUnit_product p q hq U α β).symm)

end M9Native.LagrangianCotangentSymplectic
