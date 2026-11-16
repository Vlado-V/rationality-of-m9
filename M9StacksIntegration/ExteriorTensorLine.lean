module

public import M9StacksIntegration.ExteriorTensorLineWedge
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# The canonical exterior square of a sheaf tensored with an invertible line

The map is the descent of the actual middle-four interchange followed by
the actual exterior quotient. A genuine stalk trivialization of the line
proves that this canonical map is an isomorphism. Its defining square is
the precise wedge formula needed for the determinant-induced Serre pairing.
Neither a determinant relation nor a rank-one isomorphism of exterior
powers is assumed. The construction works for every module sheaf E.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open M9Native.MukaiCupAlternating M9Native.MukaiBundleDeterminant
open _root_.SheafOfModules _root_.SheafOfModules.TensorStalkMaps

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.ExteriorTensorLine

variable {X : Scheme.{u}}

/-- The quotient is literally multiplication of the actual exterior
generators, so it agrees with `MukaiCupAlternating.wedgeBySection`. -/
theorem wedgeSheaf_unit (F : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (v w : F.val.obj U) :
    (wedgeSheaf F).val.app U
        ((PresheafOfModules.tensorSheafUnit F F).app U (v ⊗ₜ w)) =
      ((exteriorAlgebras F).exterior.mul 1 1).app U
        ((exteriorAlgebras F).exteriorGenerator.val.app U v)
        ((exteriorAlgebras F).exteriorGenerator.val.app U w) := by
  let A := exteriorAlgebras F
  let c := ExtPresentation.extComplex A.exteriorGenerator A.exteriorGenerator
    A.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra
    (0 : F ⟶ F) (𝟙 F) (by simp) 1
  refine (congrArg (c.f.val.app U)
    (tensorHom_unit (𝟙 F) A.exteriorGenerator U v w)).trans ?_
  have h := GradedAlgebra.presentationShortComplex_f_unit
    A.exterior_isExteriorAlgebra.isUniversal (𝟙 F) (0 : F ⟶ F)
    (GradedAlgebra.squareZero_comp (0 : F ⟶ F) A.exterior_isExteriorAlgebra.1)
    (by simp) 1 2 rfl U v (A.exteriorGenerator.val.app U w)
  exact h.trans (by rfl)

/-- This is an actual trivialization of the line stalk, obtained from
finite local freeness of rank one. It is used only to verify the map. -/
def lineStalkTrivialization (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (x : X) :
    moduleStalk M x ≃ₗ[stalkRing X x] stalkRing X x :=
  (Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp M 1 x).some ≪≫ₗ
    Finsupp.uniqueLinearEquiv (stalkRing X x) (stalkRing X x) (0 : Fin 1)

/-- The actual source stalk, as an exterior square of actual tensor stalks. -/
def sourceStalk (E M : X.Modules) (x : X) :
    moduleStalk (exteriorSquare (tensor E M)) x ≃ₗ[stalkRing X x]
      ⋀[stalkRing X x]^2 (moduleStalk E x ⊗[stalkRing X x] moduleStalk M x) :=
  exteriorStalk (tensor E M) 2 x ≪≫ₗ
    exteriorPowerCongr 2 (PresheafOfModules.tensorSheafStalkEquiv X.sheaf E M x)

/-- The actual target stalk, retaining the order of both line factors. -/
def targetStalk (E M : X.Modules) (x : X) :
    moduleStalk (tensor (exteriorSquare E) (tensor M M)) x ≃ₗ[stalkRing X x]
      (⋀[stalkRing X x]^2 (moduleStalk E x)) ⊗[stalkRing X x]
        (moduleStalk M x ⊗[stalkRing X x] moduleStalk M x) :=
  PresheafOfModules.tensorSheafStalkEquiv X.sheaf (exteriorSquare E) (tensor M M) x ≪≫ₗ
    TensorProduct.congr (exteriorStalk E 2 x)
      (PresheafOfModules.tensorSheafStalkEquiv X.sheaf M M x)

/-- The canonical quadratic morphism, before exterior descent. -/
def quadraticSheafMap (E M : X.Modules) :
    tensor (tensor E M) (tensor E M) ⟶ tensor (exteriorSquare E) (tensor M M) :=
  middleFour E M E M ≫ tensorHom (wedgeSheaf E) (𝟙 (tensor M M))

theorem sourceStalk_wedgeSheaf (E M : X.Modules) (x : X)
    (z : moduleStalk (tensor (tensor E M) (tensor E M)) x) :
    sourceStalk E M x (PresheafOfModules.stalkMapL x (wedgeSheaf (tensor E M)).val z) =
      wedgeQuotient (tensorTensorStalkEquiv E M E M x z) := by
  refine (congrArg
    (exteriorPowerCongr 2 (PresheafOfModules.tensorSheafStalkEquiv X.sheaf E M x))
      (exteriorStalk_wedgeSheaf (tensor E M) x z)).trans ?_
  exact DFunLike.congr_fun
    (exterior_map_comp_wedgeQuotient
      (PresheafOfModules.tensorSheafStalkEquiv X.sheaf E M x).toLinearMap) _

theorem targetStalk_quadraticSheafMap (E M : X.Modules) (x : X)
    (z : moduleStalk (tensor (tensor E M) (tensor E M)) x) :
    targetStalk E M x (PresheafOfModules.stalkMapL x (quadraticSheafMap E M).val z) =
      quadraticMap (tensorTensorStalkEquiv E M E M x z) := by
  refine (congrArg (targetStalk E M x) (stalk_comp _ _ x z)).trans ?_
  have ht := tensorSheafStalkEquiv_stalkMapL_tensorHom (wedgeSheaf E)
    (𝟙 (tensor M M)) x (PresheafOfModules.stalkMapL x (middleFour E M E M).val z)
  refine (congrArg (TensorProduct.congr (exteriorStalk E 2 x)
    (PresheafOfModules.tensorSheafStalkEquiv X.sheaf M M x)) ht).trans ?_
  have hc := congr_map_apply
    (PresheafOfModules.tensorSheafStalkEquiv X.sheaf E E x)
    (PresheafOfModules.tensorSheafStalkEquiv X.sheaf M M x)
    (exteriorStalk E 2 x)
    (PresheafOfModules.tensorSheafStalkEquiv X.sheaf M M x)
    (PresheafOfModules.stalkMapL x (wedgeSheaf E).val)
    (PresheafOfModules.stalkMapL x (𝟙 (tensor M M) : tensor M M ⟶ tensor M M).val)
    wedgeQuotient LinearMap.id
    (exteriorStalk_wedgeSheaf E x)
    (fun t => congrArg (PresheafOfModules.tensorSheafStalkEquiv X.sheaf M M x)
      (stalk_id (tensor M M) x t))
    (PresheafOfModules.tensorSheafStalkEquiv X.sheaf (tensor E E) (tensor M M) x
      (PresheafOfModules.stalkMapL x (middleFour E M E M).val z))
  refine hc.trans ?_
  exact congrArg (TensorProduct.map wedgeQuotient LinearMap.id)
    (tensorTensorStalkEquiv_stalkMapL_middleFour E M E M x z)

theorem stalk_kernel_ι {F G : X.Modules} (p : F ⟶ G) (x : X)
    (z : moduleStalk (kernel p) x) :
    PresheafOfModules.stalkMapL x p.val
      (PresheafOfModules.stalkMapL x (kernel.ι p).val z) = 0 :=
  (stalk_comp (kernel.ι p) p x z).symm.trans
    ((congrArg (fun a : kernel p ⟶ G => PresheafOfModules.stalkMapL x a.val z)
      (kernel.condition p)).trans (stalk_zero x z))

/-- The canonical quadratic map annihilates the exterior quotient's kernel.
This is checked on actual stalks using the proved module isomorphism. -/
theorem kernel_wedgeSheaf_comp_quadraticSheafMap (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    kernel.ι (wedgeSheaf (tensor E M)) ≫ quadraticSheafMap E M = 0 := by
  apply sheaf_eq_of_stalk
  intro x z
  apply (targetStalk E M x).injective
  refine (congrArg (targetStalk E M x) (stalk_comp _ _ x z)).trans ?_
  refine (targetStalk_quadraticSheafMap E M x _).trans ?_
  let b := lineStalkTrivialization M x
  refine (DFunLike.congr_fun (moduleIso_comp_wedgeQuotient
    (V := moduleStalk E x) b) _).symm.trans ?_
  refine (congrArg (moduleIso (V := moduleStalk E x) b)
    (sourceStalk_wedgeSheaf E M x _).symm).trans ?_
  refine Eq.trans ?_ (congrArg (targetStalk E M x) (stalk_zero x z)).symm
  refine Eq.trans ?_ (map_zero (targetStalk E M x)).symm
  exact (congrArg (fun t => moduleIso (V := moduleStalk E x) b (sourceStalk E M x t))
    (stalk_kernel_ι (wedgeSheaf (tensor E M)) x z)).trans
      ((congrArg (moduleIso (V := moduleStalk E x) b) (map_zero _)).trans (map_zero _))

/-- The canonical morphism, descended from the actual universal exterior
quotient. Its definition contains no chosen trivialization. -/
def sheafMap (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    exteriorSquare (tensor E M) ⟶ tensor (exteriorSquare E) (tensor M M) :=
  have : Epi (C := X.Modules) (wedgeSheaf (tensor E M)) := wedgeSheaf_epi _
  Abelian.epiDesc (C := X.Modules) (wedgeSheaf (tensor E M)) (quadraticSheafMap E M)
    (kernel_wedgeSheaf_comp_quadraticSheafMap E M)

theorem wedgeSheaf_comp_sheafMap (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    wedgeSheaf (tensor E M) ≫ sheafMap E M = quadraticSheafMap E M := by
  have : Epi (C := X.Modules) (wedgeSheaf (tensor E M)) := wedgeSheaf_epi _
  exact Abelian.comp_epiDesc (C := X.Modules) _ _ _

attribute [irreducible] sheafMap

/-- The actual exterior quotient is surjective at each stalk. -/
theorem wedgeSheaf_stalk_surjective (F : X.Modules) (x : X) :
    Function.Surjective (PresheafOfModules.stalkMapL x (wedgeSheaf F).val) :=
  (SymPresentation.epi_iff_surjective_stalkMapL (wedgeSheaf F)).1 (wedgeSheaf_epi F) x

theorem stalk_wedgeSheaf_comp_sheafMap (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (x : X)
    (t : moduleStalk (tensor (tensor E M) (tensor E M)) x) :
    PresheafOfModules.stalkMapL x (sheafMap E M).val
        (PresheafOfModules.stalkMapL x (wedgeSheaf (tensor E M)).val t) =
      PresheafOfModules.stalkMapL x (quadraticSheafMap E M).val t :=
  (stalk_comp (wedgeSheaf (tensor E M)) (sheafMap E M) x t).symm.trans
    (congrArg
      (fun a : tensor (tensor E M) (tensor E M) ⟶ tensor (exteriorSquare E) (tensor M M) =>
        PresheafOfModules.stalkMapL x a.val t)
      (wedgeSheaf_comp_sheafMap E M))

theorem targetStalk_sheafMap_on_wedge (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (x : X)
    (t : moduleStalk (tensor (tensor E M) (tensor E M)) x) :
    targetStalk E M x (PresheafOfModules.stalkMapL x (sheafMap E M).val
        (PresheafOfModules.stalkMapL x (wedgeSheaf (tensor E M)).val t)) =
      moduleIso (V := moduleStalk E x) (lineStalkTrivialization M x)
        (sourceStalk E M x
          (PresheafOfModules.stalkMapL x (wedgeSheaf (tensor E M)).val t)) := by
  refine (congrArg (targetStalk E M x) (stalk_wedgeSheaf_comp_sheafMap E M x t)).trans ?_
  refine (targetStalk_quadraticSheafMap E M x t).trans ?_
  refine (DFunLike.congr_fun (moduleIso_comp_wedgeQuotient
    (V := moduleStalk E x) (lineStalkTrivialization M x)) _).symm.trans ?_
  exact congrArg (moduleIso (V := moduleStalk E x) (lineStalkTrivialization M x))
    (sourceStalk_wedgeSheaf E M x t).symm

/-- The stalk of the descended map is the proved canonical module map. -/
theorem targetStalk_sheafMap (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (x : X)
    (z : moduleStalk (exteriorSquare (tensor E M)) x) :
    targetStalk E M x (PresheafOfModules.stalkMapL x (sheafMap E M).val z) =
      moduleIso (V := moduleStalk E x) (lineStalkTrivialization M x)
        (sourceStalk E M x z) := by
  refine (wedgeSheaf_stalk_surjective (tensor E M) x z).elim fun t ht => ?_
  refine (congrArg (fun a => targetStalk E M x
    (PresheafOfModules.stalkMapL x (sheafMap E M).val a)) ht).symm.trans ?_
  refine (targetStalk_sheafMap_on_wedge E M x t).trans ?_
  exact congrArg (fun a => moduleIso (V := moduleStalk E x) (lineStalkTrivialization M x)
    (sourceStalk E M x a)) ht

instance sheafMap_isIso (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] : IsIso (sheafMap E M) := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (O := X.ringCatSheaf) (sheafMap E M)).2 fun x => ?_
  change Function.Bijective (PresheafOfModules.stalkMapL x (sheafMap E M).val)
  constructor
  · intro a b hab
    apply (sourceStalk E M x).injective
    apply (moduleIso (V := moduleStalk E x) (lineStalkTrivialization M x)).injective
    exact (targetStalk_sheafMap E M x a).symm.trans
      ((congrArg (targetStalk E M x) hab).trans (targetStalk_sheafMap E M x b))
  · intro y
    refine ⟨(sourceStalk E M x).symm
      ((moduleIso (V := moduleStalk E x) (lineStalkTrivialization M x)).symm
        (targetStalk E M x y)), (targetStalk E M x).injective ?_⟩
    exact (targetStalk_sheafMap E M x _).trans (by simp)

/-- The actual canonical tensor-line exterior-square isomorphism. -/
def exteriorTensorLineIso (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    exteriorSquare (tensor E M) ≅ tensor (exteriorSquare E) (tensor M M) :=
  asIso (sheafMap E M)

/-- The precise canonical wedge square; this is stronger than an arbitrary
isomorphism between the two invertible sheaves. -/
theorem exteriorTensorLineIso_wedge (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    wedgeSheaf (tensor E M) ≫ (exteriorTensorLineIso E M).hom =
      middleFour E M E M ≫ tensorHom (wedgeSheaf E) (𝟙 (tensor M M)) :=
  wedgeSheaf_comp_sheafMap E M

/-- The native sheafification image of a pure tensor of local sections. -/
abbrev sectionTensor (E M : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (v : E.val.obj U) (l : M.val.obj U) : (tensor E M).val.obj U :=
  (PresheafOfModules.tensorSheafUnit E M).app U (v ⊗ₜ l)

/-- The product of the actual exterior generators, in their original order. -/
abbrev sectionWedge (F : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (v w : F.val.obj U) : (exteriorSquare F).val.obj U :=
  ((exteriorAlgebras F).exterior.mul 1 1).app U
    ((exteriorAlgebras F).exteriorGenerator.val.app U v)
    ((exteriorAlgebras F).exteriorGenerator.val.app U w)

/-- Exact compatibility with the wedge morphism used in the native
cup-boundary calculation. -/
theorem sectionWedge_eq_wedgeBySection (F : X.Modules) (σ : F.sections)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (v : F.val.obj U) :
    sectionWedge F U (σ.val U) v = (wedgeBySection F σ).val.app U v := rfl

theorem quadraticSheafMap_unit (E M : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (v w : E.val.obj U) (l m : M.val.obj U) :
    (quadraticSheafMap E M).val.app U
        (sectionTensor (tensor E M) (tensor E M) U
          (sectionTensor E M U v l) (sectionTensor E M U w m)) =
      sectionTensor (exteriorSquare E) (tensor M M) U
        (sectionWedge E U v w) (sectionTensor M M U l m) := by
  refine (congrArg
    ((tensorHom (wedgeSheaf E) (𝟙 (tensor M M))).val.app U)
    (middleFour_unit E M E M U v l w m)).trans ?_
  refine (tensorHom_unit (wedgeSheaf E) (𝟙 (tensor M M)) U _ _).trans ?_
  exact congrArg₂ (sectionTensor (exteriorSquare E) (tensor M M) U)
    (wedgeSheaf_unit E U v w) rfl

/-- The actual decomposable wedge formula on every open set, expressed
using the same multiplication as `MukaiCupAlternating.wedgeBySection`. -/
theorem exteriorTensorLineIso_decomposable (E M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (v w : E.val.obj U) (l m : M.val.obj U) :
    (exteriorTensorLineIso E M).hom.val.app U
        (sectionWedge (tensor E M) U (sectionTensor E M U v l) (sectionTensor E M U w m)) =
      sectionTensor (exteriorSquare E) (tensor M M) U
        (sectionWedge E U v w) (sectionTensor M M U l m) := by
  refine (congrArg ((exteriorTensorLineIso E M).hom.val.app U)
    (wedgeSheaf_unit (tensor E M) U _ _)).symm.trans ?_
  refine (congrArg (fun a : tensor (tensor E M) (tensor E M) ⟶
      tensor (exteriorSquare E) (tensor M M) => a.val.app U
    (sectionTensor (tensor E M) (tensor E M) U
      (sectionTensor E M U v l) (sectionTensor E M U w m)))
    (exteriorTensorLineIso_wedge E M)).trans ?_
  exact quadraticSheafMap_unit E M U v w l m

end M9Native.ExteriorTensorLine
