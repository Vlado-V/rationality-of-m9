module

public import M9StacksIntegration.LagrangianInfinitesimal
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.SpecComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale

/-!
# The actual native relative cotangent sheaf on the LG big cell

The canonical differential map of the actual open immersion identifies
the pullback of native relative differentials with those of affine
six-space. Its free frame is the actual polynomial Kähler basis `dX`.
This is a comparison of actual sheaves, not a tangent dimension count.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianChartCotangent

open LagrangianMatrixChart LagrangianGrassmannian

variable (K : Type u) [Field K]

def kaehlerAlgebraIso {A B : Type u} [CommRing A] [CommRing B]
    (i₁ i₂ : Algebra A B) (h : i₁=i₂) :
    (letI := i₁; ModuleCat.of B Ω[B⁄A]) ≅ (letI := i₂; ModuleCat.of B Ω[B⁄A]) := by
  cases h
  exact Iso.refl _

abbrev Ring := MvPolynomial (Fin 6) K
abbrev chart : Scheme.{u} := Spec (.of (Ring K))
abbrev coefficient : CommRingCat.of K ⟶ CommRingCat.of (Ring K) :=
  CommRingCat.ofHom MvPolynomial.C
abbrev chartProjection : chart K ⟶ Spec (.of K) := Spec.map (coefficient K)

/-- The literal polynomial differential basis in the native universe. -/
def polynomialBasis : Module.Basis (ULift.{u} (Fin 6)) (Ring K) Ω[Ring K⁄K] :=
  (KaehlerDifferential.mvPolynomialBasis K (Fin 6)).reindex Equiv.ulift.symm

/-- The only scalar transport here is the equality of the coefficient
map algebra structure and the actual polynomial algebra structure. -/
def polynomialDifferentialsIso :
    CommRingCat.KaehlerDifferential (coefficient K) ≅
      ModuleCat.of (Ring K) (ULift.{u} (Fin 6) →₀ Ring K) :=
  kaehlerAlgebraIso ((coefficient K).hom.toAlgebra)
      (inferInstance : Algebra K (Ring K)) (Algebra.algebra_ext _ _ (fun _ => rfl)) ≪≫
    (polynomialBasis K).repr.toModuleIso

/-- The actual sheaf of relative differentials on affine six-space,
trivialized by the six literal coordinate differentials. -/
def affineCotangentIso : Scheme.Hom.relativeDifferentials (chartProjection K) ≅
    freeOn (chart K) 6 :=
  (Stacks.AlgebraicGeometry.AffineDifferentialsIso.tildeKaehlerIso (coefficient K)).symm ≪≫
    (tilde.functor (.of (Ring K))).mapIso (polynomialDifferentialsIso K) ≪≫
    tildeFinsupp (R := CommRingCat.of (Ring K)) (ULift.{u} (Fin 6))

theorem chart_square : bigCell K ≫ projection K=chartProjection K ≫ 𝟙 (base K) := by
  simpa only [Category.comp_id] using bigCell_projection K

/-- This is the canonical differential map of the actual native big
cell, not an independently chosen comparison map. -/
def nativeDifferentialMap :
    (Scheme.Modules.pullback (bigCell K)).obj (Scheme.Hom.relativeDifferentials (projection K)) ⟶
      Scheme.Hom.relativeDifferentials (chartProjection K) :=
  Scheme.Hom.relativeDifferentialsMap (bigCell K) (projection K) (chartProjection K)
    (𝟙 (base K)) (chart_square K)

instance nativeDifferentialMap_isIso : IsIso (nativeDifferentialMap K) :=
  Scheme.Hom.isIso_relativeDifferentialsMap_of_etale (bigCell K) (projection K)
    (chartProjection K) (𝟙 (base K)) (chart_square K)

/-- The actual native cotangent sheaf of LG restricts to its genuine
six-coordinate differential frame. -/
def nativeCotangentChartIso :
    (Scheme.Modules.pullback (bigCell K)).obj (Scheme.Hom.relativeDifferentials (projection K)) ≅
      freeOn (chart K) 6 :=
  asIso (nativeDifferentialMap K) ≪≫ affineCotangentIso K

end M9Native.LagrangianChartCotangent
