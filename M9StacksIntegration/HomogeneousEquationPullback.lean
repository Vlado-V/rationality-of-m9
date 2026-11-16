module

public import M9StacksIntegration.HomogeneousEquationIdeal
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-! The literal homogeneous equation ideal commutes with an actual
surjective graded projective map, in every degree and over every ring. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.HomogeneousEquationPullback

private theorem pullbackGlobal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) : pullbackGlobalSections f M s =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s) = _
  exact Functor.map_id_apply _ _ _

variable (K : Type u) [CommRing K] (n m d : ℕ)
    (ψ : polyGrading K n →+*ᵍ polyGrading K m) (hψ : Function.Surjective ψ)
    {ι : Type v} [Finite ι] (F : ι → polyGrading K n d)

def imageForm (i : ι) : polyGrading K m d := ⟨ψ (F i), ψ.map_mem (F i).property⟩

/-- Equality of the full pulled equation ideals, without reduction or
a presumed projective-map triangle. -/
theorem equationIdeal_comap (i : ι) :
    (HomogeneousEquationIdeal.equationIdeal K n d F i).comap
        (Proj.map ψ (Proj.irrelevant_le_map_of_surjective ψ hψ)) =
      HomogeneousEquationIdeal.equationIdeal K m d (imageForm K n m d ψ F) i := by
  rw [HomogeneousEquationIdeal.equationIdeal, ← Stacks.Divisors.zeroScheme_pullback]
  dsimp only [HomogeneousEquationIdeal.equationIdeal]
  apply zeroScheme_eq_of_iso
    (pullbackTwistIso ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) d)
  rw [pullbackGlobal_eq]
  exact pullbackTwistIso_degreeSection ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) d (F i)

end M9Native.HomogeneousEquationPullback
