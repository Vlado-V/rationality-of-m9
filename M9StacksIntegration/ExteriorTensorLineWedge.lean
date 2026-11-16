module

public import M9StacksIntegration.ExteriorTensorLineAlgebra
public import M9StacksIntegration.MukaiCupAlternating
public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafStalkMaps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact

/-!
# The actual exterior-square quotient and its stalk formula

The quotient is constructed from the native exterior presentation in degree
two, with the actual generator of the constructed exterior algebra. The
stalk and elementary stalk-functor proofs below adapt only the corresponding
small helpers of `SymmetricSquareTensorSequence` and
`SymmetricSquareFiltration` at Stacks commit
`c496df0d9beea9deaeabcea8492605f9a0a2313b`; their unrelated symmetric-square
and projective Euler-sequence dependency closure is not imported.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open M9Native.MukaiCupAlternating M9Native.MukaiBundleDeterminant
open _root_.SheafOfModules _root_.SheafOfModules.TensorStalkMaps

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.ExteriorTensorLine

section Algebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The actual degree-one generator, with its exterior-power membership. -/
def degreeOneGenerator : V →ₗ[R] ⋀[R]^1 V :=
  (ExteriorAlgebra.ι R).codRestrict _ fun v =>
    (pow_one (LinearMap.range (ExteriorAlgebra.ι R : V →ₗ[R] ExteriorAlgebra R V))).ge
      (LinearMap.mem_range_self _ v)

theorem beta_degreeOneGenerator (z : V ⊗[R] V) :
    ExtPow.beta 1 (LinearMap.id (R := R) (M := V))
        (LinearMap.lTensor V degreeOneGenerator z) = wedgeQuotient z := by
  have h : ExtPow.beta 1 (LinearMap.id (R := R) (M := V)) ∘ₗ
      LinearMap.lTensor V degreeOneGenerator = wedgeQuotient := by
    apply TensorProduct.ext'
    intro v w
    apply Subtype.ext
    simp [wedge, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      degreeOneGenerator, ExtPow.beta, ExtPow.betaBil]
  exact DFunLike.congr_fun h z

end Algebra

variable {X : Scheme.{u}}

abbrev stalkRing (X : Scheme.{u}) (x : X) : Type u :=
  ↑(TopCat.Presheaf.stalk X.sheaf.obj x)

abbrev moduleStalk (F : X.Modules) (x : X) : Type u :=
  ↑(TopCat.Presheaf.stalk F.val.presheaf x)

/-- The actual exterior-square quotient of sheaves. -/
def wedgeSheaf (F : X.Modules) : tensor F F ⟶ exteriorSquare F :=
  let A := exteriorAlgebras F
  tensorHom (𝟙 F) A.exteriorGenerator ≫
    (ExtPresentation.extComplex A.exteriorGenerator A.exteriorGenerator
      A.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra
      (0 : F ⟶ F) (𝟙 F) (by simp) 1).f

/-- Stalk maps preserve identities, at the commutative stalk-ring spelling. -/
theorem stalk_id (F : X.Modules) (x : X) (z : moduleStalk F x) :
    PresheafOfModules.stalkMapL x (𝟙 F : F ⟶ F).val z = z := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf z
  exact PresheafOfModules.stalkMapL_germ x _ U hU s

theorem stalk_comp {F G H : X.Modules} (a : F ⟶ G) (b : G ⟶ H)
    (x : X) (z : moduleStalk F x) :
    PresheafOfModules.stalkMapL x (a ≫ b).val z =
      PresheafOfModules.stalkMapL x b.val (PresheafOfModules.stalkMapL x a.val z) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf z
  refine (PresheafOfModules.stalkMapL_germ x _ U hU s).trans ?_
  refine Eq.trans ?_ (congrArg (PresheafOfModules.stalkMapL x b.val)
    (PresheafOfModules.stalkMapL_germ x a.val U hU s)).symm
  exact (PresheafOfModules.stalkMapL_germ x b.val U hU _).symm

theorem stalk_zero {F G : X.Modules} (x : X) (z : moduleStalk F x) :
    PresheafOfModules.stalkMapL x (0 : F ⟶ G).val z = 0 := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf z
  refine (PresheafOfModules.stalkMapL_germ x _ U hU s).trans ?_
  exact (congrArg (TopCat.Presheaf.germ G.val.presheaf U x hU)
    (_root_.SheafOfModules.zero_val_app_apply (op U) s)).trans (map_zero _)

theorem sheaf_eq_of_stalk {F G : X.Modules} (a b : F ⟶ G)
    (h : ∀ (x : X) (z : moduleStalk F x),
      PresheafOfModules.stalkMapL x a.val z = PresheafOfModules.stalkMapL x b.val z) : a = b := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  exact TopCat.Presheaf.section_ext
    ((AlgebraicGeometry.SheafOfModules.toTopSheaf X.ringCatSheaf).obj G) U.unop _ _ fun x hx =>
    (PresheafOfModules.stalkMapL_germ x a.val U.unop hx s).symm.trans
      ((h x _).trans (PresheafOfModules.stalkMapL_germ x b.val U.unop hx s))

/-- The canonical comparison of the exterior-power stalk with the exterior
power of the actual module stalk. -/
def exteriorStalk (F : X.Modules) (n : ℕ) (x : X) :
    moduleStalk ((exteriorAlgebras F).exteriorPower n) x ≃ₗ[stalkRing X x]
      ⋀[stalkRing X x]^n (moduleStalk F x) :=
  exteriorPowerStalkEquiv (exteriorAlgebras F).exterior
    (exteriorAlgebras F).exteriorGenerator (exteriorAlgebras F).exterior_isExteriorAlgebra n x

theorem exteriorStalk_generator (F : X.Modules) (x : X) (z : moduleStalk F x) :
    exteriorStalk F 1 x
        (PresheafOfModules.stalkMapL x (exteriorAlgebras F).exteriorGenerator.val z) =
      degreeOneGenerator z := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf z
  let A := exteriorAlgebras F
  have hg := exteriorPowerStalkEquiv_germ_homogeneousProd A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra 1 x U hU (fun _ => s)
  have h1 : A.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) 1
      (fun _ => A.exteriorGenerator.val.app (op U) s) = A.exteriorGenerator.val.app (op U) s :=
    eq_of_heq (A.exterior.toPresheafGradedAlgebra.one_mul 1 (op U) _)
  refine (congrArg (exteriorStalk F 1 x)
    (PresheafOfModules.stalkMapL_germ x A.exteriorGenerator.val U hU s)).trans ?_
  refine Eq.trans ?_ (hg.trans ?_)
  · exact congrArg (fun t => exteriorStalk F 1 x
      (TopCat.Presheaf.germ (A.exteriorPower 1).val.presheaf U x hU t)) h1.symm
  · apply Subtype.ext
    simp [degreeOneGenerator, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]

/-- The stalk formula pins the quotient to the actual universal wedge. -/
theorem exteriorStalk_wedgeSheaf (F : X.Modules) (x : X)
    (z : moduleStalk (tensor F F) x) :
    exteriorStalk F 2 x (PresheafOfModules.stalkMapL x (wedgeSheaf F).val z) =
      wedgeQuotient (PresheafOfModules.tensorSheafStalkEquiv X.sheaf F F x z) := by
  let A := exteriorAlgebras F
  refine (congrArg (exteriorStalk F 2 x) (stalk_comp _ _ x z)).trans ?_
  refine (ExtPresentation.exteriorPowerStalkEquiv_extComplex_f
    A.exteriorGenerator A.exteriorGenerator A.exterior_isExteriorAlgebra
    A.exterior_isExteriorAlgebra (0 : F ⟶ F) (𝟙 F) (by simp) 1 x _).trans ?_
  have ht := tensorSheafStalkEquiv_stalkMapL_tensorHom (𝟙 F) A.exteriorGenerator x z
  have he : (TensorProduct.congr (LinearEquiv.refl (stalkRing X x) (moduleStalk F x))
      (exteriorStalk F 1 x)).toLinearMap ∘ₗ
      TensorProduct.map (PresheafOfModules.stalkMapL x (𝟙 F : F ⟶ F).val)
        (PresheafOfModules.stalkMapL x A.exteriorGenerator.val) =
      LinearMap.lTensor (moduleStalk F x) degreeOneGenerator := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul]
    exact congrArg₂ (fun p q => p ⊗ₜ[stalkRing X x] q)
      (stalk_id F x a) (exteriorStalk_generator F x b)
  have hβ := congrArg (ExtPow.beta 1
    (PresheafOfModules.stalkMapL x (𝟙 F : F ⟶ F).val))
      ((congrArg (TensorProduct.congr (LinearEquiv.refl _ _) (exteriorStalk F 1 x)) ht).trans
        (DFunLike.congr_fun he _))
  refine hβ.trans ?_
  have hi : PresheafOfModules.stalkMapL x (𝟙 F : F ⟶ F).val = LinearMap.id :=
    LinearMap.ext (stalk_id F x)
  exact (congrArg (fun φ => ExtPow.beta 1 φ
    (LinearMap.lTensor (moduleStalk F x) degreeOneGenerator
      (PresheafOfModules.tensorSheafStalkEquiv X.sheaf F F x z))) hi).trans
    (beta_degreeOneGenerator _)

theorem wedgeSheaf_epi (F : X.Modules) : Epi (wedgeSheaf F) := by
  refine (SymPresentation.epi_iff_surjective_stalkMapL _).2 fun x z => ?_
  obtain ⟨w, hw⟩ := wedgeQuotient_surjective (exteriorStalk F 2 x z)
  refine ⟨(PresheafOfModules.tensorSheafStalkEquiv X.sheaf F F x).symm w,
    (exteriorStalk F 2 x).injective ?_⟩
  exact (exteriorStalk_wedgeSheaf F x _).trans
    ((congrArg wedgeQuotient
      ((PresheafOfModules.tensorSheafStalkEquiv X.sheaf F F x).apply_symm_apply w)).trans hw)

end M9Native.ExteriorTensorLine
