module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-! The literal ratio differentials form a basis of the actual native
projective cotangent stalk on each standard chart. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ProjTrivialization

universe u

namespace M9Native.ProjectiveEulerStalkBasis

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)
variable (x : ProjectiveSpectrum.top (polyGrading R n)) (i : Fin (n+1))
variable (hx : (MvPolynomial.X i : MvPolynomial (Fin (n+1)) R) ∉ x.asHomogeneousIdeal)
variable (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))

abbrev cotangentStalk :=
  ↥(SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x (projDifferentials R n))
abbrev middleStalk :=
  ↥(SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x (twistMinusOneSum R n))

local instance cotangentModule : Module (projStalk R n x) (cotangentStalk R n x) :=
  Stacks.RelativeDifferentialStalk.moduleStalkRelativeDifferentials (projToSpecCoeff R n) x

local instance middleModule : Module (projStalk R n x) (middleStalk R n x) :=
  Stacks.ModuleStalkSpecialization.stalkModule
    (X := Proj (polyGrading R n)) (twistMinusOneSum R n) x

include hx hxb in
/-- A basis whose vectors are the original native germs of d(Tj/Ti). -/
def cotangentBasis : Module.Basis {j : Fin (n+1) // j ≠ i}
    (projStalk R n x) (cotangentStalk R n x) := by
  classical
  let v : {j : Fin (n+1) // j ≠ i} → cotangentStalk R n x :=
    fun j => chartDiffGerm R n x i hxb j.1
  have hv (j : {j : Fin (n+1) // j ≠ i}) :
      eulerStalkMap R n x i hx (v j) =
        Stacks.LinearAlgebra.kernelGen (coordRatio R n x i hx) i j.1 :=
    funext fun k => eulerStalkCoord_stalkMap_eulerFirstArrow R n x i hx hxb j.1 k
  have hgen := (Stacks.LinearAlgebra.kernelBasis (B := projStalk R n x)
    (coordRatio_self R n x i hx)).linearIndependent.map'
    (LinearMap.ker (Stacks.LinearAlgebra.unitalRow (B := projStalk R n x)
      (coordRatio R n x i hx))).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hi : LinearIndependent (projStalk R n x) v := by
    apply LinearIndependent.of_comp (eulerStalkMap R n x i hx)
    have hh : (eulerStalkMap R n x i hx) ∘ v =
        (LinearMap.ker (Stacks.LinearAlgebra.unitalRow (B := projStalk R n x)
          (coordRatio R n x i hx))).subtype ∘
          (Stacks.LinearAlgebra.kernelBasis (B := projStalk R n x)
            (coordRatio_self R n x i hx)) := by
      funext j
      exact (hv j).trans (Stacks.LinearAlgebra.kernelBasis_apply_coe
        (B := projStalk R n x) (coordRatio_self R n x i hx) j).symm
    rw [hh]
    exact hgen
  exact Module.Basis.mk hi
    (by rw [show Submodule.span (projStalk R n x) (Set.range v) = ⊤ from
      span_range_chartDiffGerm_eq_top R n x i hx hxb])

@[simp] theorem cotangentBasis_apply (j : {j : Fin (n+1) // j ≠ i}) :
    cotangentBasis R n x i hx hxb j = chartDiffGerm R n x i hxb j.1 := by
  classical
  simp only [cotangentBasis,Module.Basis.mk_apply]

include hx in
/-- Each actual middle-stalk coordinate is linear over the actual local ring. -/
def coordinateLinear (k : Fin (n+1)) :
    middleStalk R n x →ₗ[projStalk R n x] projStalk R n x where
  toFun := eulerStalkCoord R n x i hx k
  map_add' := eulerStalkCoord_add R n x i hx k
  map_smul' b m := by
    have hb : b • m = (stalkRingEquiv R n x).symm b • m :=
      (congrArg (fun c : projStalk R n x => c • m)
        ((stalkRingEquiv R n x).apply_symm_apply b).symm).trans
        (AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq'
          (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x
          (twistMinusOneSum R n).val ((stalkRingEquiv R n x).symm b) m)
    exact (congrArg (eulerStalkCoord R n x i hx k) hb).trans
      (eulerStalkCoord_smul R n x i hx k b m)

theorem coordinateLinear_euler_basis (j : {j : Fin (n+1) // j ≠ i}) (k : Fin (n+1)) :
    coordinateLinear R n x i hx k
      ((SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (eulerFirstArrow R n)).hom (cotangentBasis R n x i hx hxb j)) =
      Stacks.LinearAlgebra.kernelGen (coordRatio R n x i hx) i j.1 k := by
  rw [cotangentBasis_apply]
  exact eulerStalkCoord_stalkMap_eulerFirstArrow R n x i hx hxb j.1 k

end M9Native.ProjectiveEulerStalkBasis
