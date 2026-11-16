module

public import M9StacksIntegration.MukaiTensorPullbackNaturality
public import M9StacksIntegration.MukaiConormalFieldCoordinates
public import M9StacksIntegration.TensorFreeCoordinates

/-! A morphism out of the actual tensor cube of a rank-one bundle over
Spec K is determined by its values on genuine diagonal sections. This
uses a basis of the actual section module and native affine tensor
comparisons; no symmetry of the cubic is asserted or required. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiFieldLineCubic

open MukaiBundleDeterminant MukaiTensorPullbackNaturality LinearIncidenceTensorCoordinates

variable (K : Type u) [Field K]

abbrev Sections (A : (Spec (.of K)).Modules) := moduleSpecΓFunctor.obj A

def tensorSection (A B : (Spec (.of K)).Modules) (s : Sections K A) (t : Sections K B) :
    Sections K (tensor A B) := tensorTop (Spec (.of K)) A B s t

theorem tensorSection_smul_left (A B : (Spec (.of K)).Modules) (a : K)
    (s : Sections K A) (t : Sections K B) :
    tensorSection K A B (a • s) t = a • tensorSection K A B s t := by
  change tensorTop (Spec (.of K)) A B ((Scheme.ΓSpecIso (.of K)).inv.hom a • (show Γ(A, ⊤) from s)) t =
    (Scheme.ΓSpecIso (.of K)).inv.hom a • tensorTop (Spec (.of K)) A B s t
  exact tensorTop_smul_left _ A B _ s t

theorem tensorSection_smul_right (A B : (Spec (.of K)).Modules) (a : K)
    (s : Sections K A) (t : Sections K B) :
    tensorSection K A B s (a • t) = a • tensorSection K A B s t := by
  change tensorTop (Spec (.of K)) A B s ((Scheme.ΓSpecIso (.of K)).inv.hom a • (show Γ(B, ⊤) from t)) =
    (Scheme.ΓSpecIso (.of K)).inv.hom a • tensorTop (Spec (.of K)) A B s t
  exact TensorFreeCoordinates.tensorTop_smul_right (X := Spec (.of K)) (A := A) B _ s t

def tripleSection (A : (Spec (.of K)).Modules) (s t u : Sections K A) : Sections K (cubeObj A) :=
  tensorSection K (tensor A A) A (tensorSection K A A s t) u

theorem tripleSection_smul (A : (Spec (.of K)).Modules) (a b c : K)
    (s t u : Sections K A) :
    tripleSection K A (a • s) (b • t) (c • u) =
      (a*b*c) • tripleSection K A s t u := by
  simp only [tripleSection, tensorSection_smul_left, tensorSection_smul_right, smul_smul,
    mul_comm, mul_left_comm]

/-- Actual diagonal values determine an actual sheaf morphism on a
field-point line, even for a trilinear construction without symmetry. -/
theorem hom_eq_zero_of_diagonal {A B : (Spec (.of K)).Modules}
    (hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 1)
    (a : cubeObj A ⟶ B)
    (h : ∀ s : Sections K A,
      (moduleSpecΓFunctor.map a).hom (tripleSection K A s s s) = 0) : a = 0 := by
  let := hA
  let hAA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor A A) (1*1) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (Spec (.of K)) A A 1 1
  let hAAA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cubeObj A) ((1*1)*1) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (Spec (.of K)) (tensor A A) A (1*1) 1
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} A := hA.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (tensor A A) := hAA.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cubeObj A) := hAAA.isFiniteLocallyFree
  let : A.IsQuasicoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree A
  let : (tensor A A).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree (tensor A A)
  let : (cubeObj A).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree (cubeObj A)
  have hdim := MukaiConormalFieldCoordinates.finite_and_finrank_sections K A 1
  let : Module.Finite K (Sections K A) := hdim.1
  let b : Basis (Fin 1) K (Sections K A) := Module.finBasisOfFinrankEq K (Sections K A) hdim.2
  have hs (s : Sections K A) : s = (b.equivFun s 0) • b 0 := by
    simpa only [Fin.sum_univ_one, Basis.equivFun_apply] using (b.sum_repr s).symm
  apply affine_cube_hom_ext a 0
  intro s t u
  change (moduleSpecΓFunctor.map a).hom (tripleSection K A s t u) = 0
  rw [hs s, hs t, hs u, tripleSection_smul, map_smul, h, smul_zero]

end M9Native.MukaiFieldLineCubic
