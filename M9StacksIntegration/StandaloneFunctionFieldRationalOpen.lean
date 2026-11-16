module

public import M9StacksIntegration.AffineSpaceVariety
public import M9StacksIntegration.StandaloneBirationalRationalOpen
public import M9StacksIntegration.StandaloneRationalOpenComposition
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.BirationalVariety

/-! From the actual structural function field of a variety to the literal
common dense open in the original full scheme site. The native 0BXP theorem
constructs genuine isomorphic open subschemes; no function-field condition
is substituted for the standalone common-open conclusion. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace M9Native.StandaloneFunctionFieldRationalOpen

variable (K : Type u) [Field K]

/-- This is the actual underlying original scheme over its retained base. -/
def originalVariety (X : Variety K) : M9StandaloneDraft.Schemes K :=
  Over.mk X.structureMap

/-- The native stalk scalar map equals the original structure-map germ. -/
theorem nativeScalarMap_eq (X : Variety K) :
    functionFieldAlgebraMap X =
      GrassmannianCharts.structureScalarMap K X.structureMap := by
  rw [functionFieldAlgebraMap_eq_germToFunctionField]
  rfl

/-- Actual function-field rationality supplies an actual common dense open,
with nonempty source and both maps over the original coefficient field. -/
theorem rationalOpen_of_functionFieldEquiv (n : ℕ) (X : Variety K)
    (h : letI := varietyFunctionFieldAlgebra X
      Nonempty (X.toScheme.functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K))) :
    M9StandaloneDraft.RationalOpen K n (yoneda.obj (originalVariety K X)) := by
  letI := varietyFunctionFieldAlgebra X
  let A := AffineSpaceVariety.variety K n
  letI := varietyFunctionFieldAlgebra A
  obtain ⟨e⟩ := h
  let eA := AffineSpaceVariety.rationalFunctionFieldEquiv K n
  have hB : Scheme.BirationalOver X.structureMap A.structureMap :=
    (Variety.nonempty_algEquiv_functionField_iff_birationalOver X A).mp
      ⟨e.trans eA.symm⟩
  exact StandaloneBirationalRationalOpen.rationalOpen_of_birationalOver K n
    (originalVariety K X) hB

/-- The structural scalar presentation gives the same actual conclusion;
the native and original generic-stalk carriers are unchanged. -/
theorem rationalOpen_of_structuralFunctionFieldEquiv (n : ℕ) (X : Variety K)
    (h : letI := (GrassmannianCharts.structureScalarMap K X.structureMap).toAlgebra
      Nonempty (X.toScheme.functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K))) :
    M9StandaloneDraft.RationalOpen K n (yoneda.obj (originalVariety K X)) := by
  letI := (GrassmannianCharts.structureScalarMap K X.structureMap).toAlgebra
  obtain ⟨e⟩ := h
  let er : X.toScheme.functionField ≃+* FractionRing (MvPolynomial (Fin n) K) := e.toRingEquiv
  have hcomm (c : K) : er (GrassmannianCharts.structureScalarMap K X.structureMap c) =
      algebraMap K (FractionRing (MvPolynomial (Fin n) K)) c := e.commutes c
  letI := varietyFunctionFieldAlgebra X
  let e' : X.toScheme.functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K) :=
    { __ := er
      commutes' := fun c => by
        change er (functionFieldAlgebraMap X c) = _
        rw [nativeScalarMap_eq]
        exact hcomm c }
  exact rationalOpen_of_functionFieldEquiv K n X ⟨e'⟩

/-- An actual represented dense open of a possibly nonschematic target
transfers the same genuine common-open rationality to that target. -/
theorem rationalOpen_of_dense_variety (n : ℕ) (X : Variety K)
    {M : M9StandaloneDraft.Presheaves K}
    (j : yoneda.obj (originalVariety K X) ⟶ M)
    (hj : M9StandaloneDraft.DenseOpen K j)
    (h : letI := varietyFunctionFieldAlgebra X
      Nonempty (X.toScheme.functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K))) :
    M9StandaloneDraft.RationalOpen K n M :=
  StandaloneRationalOpenComposition.rationalOpen_comp K n j hj
    (rationalOpen_of_functionFieldEquiv K n X h)

end M9Native.StandaloneFunctionFieldRationalOpen
