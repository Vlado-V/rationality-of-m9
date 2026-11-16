module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank

/-!
# The exterior diagonal in Mukai's cup-boundary argument

The actual exterior algebra supplies the wedge map; no alternating pairing
is postulated. Naturality of native Ext under exact tensor functors then
annihilates the diagonal of the tensor-extension pairing. The canonical
H¹/connecting comparison and the identification with the determinant-induced
Serre pairing are recorded as separate geometric interfaces.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiCupAlternating

section ExtNaturality

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Naturality of actual Ext sends a vanishing composite of component maps
to a zero Yoneda product. This is used with the canonical exterior wedge. -/
theorem ext_diagonal_zero_of_naturality
    {F G : C ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F ⟶ G) {A B D : C} {n : ℕ} (ξ : Abelian.Ext A B n)
    (b : G.obj B ⟶ D) (hz : τ.app B ≫ b = 0) :
    ((Abelian.Ext.mk₀ (τ.app A)).comp (ξ.mapExactFunctor G) (zero_add n)).comp
      (Abelian.Ext.mk₀ b) (add_zero n) = 0 := by
  rw [← Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp ξ τ,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hz,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

end ExtNaturality

section NativeExterior

variable {X : Scheme.{u}} (F : X.Modules)

/-- The native, constructed exterior algebra of the actual sheaf F. -/
def exteriorAlgebras : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X) F :=
  _root_.SheafOfModules.algebras (Osharp := X.sheaf) (Opens.grothendieckTopology X) F

/-- The actual second exterior power of F. -/
abbrev exteriorSquare : X.Modules := (exteriorAlgebras F).exteriorPower 2

/-- Wedge with an actual compatible global section, for the native
exterior algebra universal property. It is specialized below to the
library's constructed canonical algebra. -/
def wedgeBySectionIn
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X) F) (σ : F.sections) : F ⟶ A.exteriorPower 2 where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := fun y => (A.exterior.mul 1 1).app U
            (A.exteriorGenerator.val.app U (σ.val U))
            (A.exteriorGenerator.val.app U y)
          map_add' := fun y z => by simp only [map_add]
          map_smul' := fun r y => by
            rw [map_smul]
            exact (A.exterior.mul 1 1).map_smul_right U r _ _ }
      naturality {U V} j := by
        apply ModuleCat.hom_ext
        ext y
        change (A.exterior.mul 1 1).app V
            (A.exteriorGenerator.val.app V (σ.val V))
            (A.exteriorGenerator.val.app V (F.val.map j y)) =
          (A.exteriorPower 2).val.map j
            ((A.exterior.mul 1 1).app U (A.exteriorGenerator.val.app U (σ.val U))
              (A.exteriorGenerator.val.app U y))
        symm
        refine ((A.exterior.mul 1 1).naturality j _ _).trans ?_
        congr 1
        · exact congrArg ((A.exterior.mul 1 1).app V)
            ((PresheafOfModules.naturality_apply A.exteriorGenerator.val j (σ.val U)).symm.trans
              (congrArg (A.exteriorGenerator.val.app V) (σ.property j)))
        · exact (PresheafOfModules.naturality_apply A.exteriorGenerator.val j y).symm }

/-- The composite with wedge by the same section vanishes by the exterior
algebra's proved square-zero law. -/
theorem section_comp_wedgeBySectionIn_eq_zero
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X) F)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    s ≫ wedgeBySectionIn F A (F.unitHomEquiv s) = 0 := by
  apply (A.exteriorPower 2).unitHomEquiv.injective
  ext U
  change (A.exterior.mul 1 1).app U
      (A.exteriorGenerator.val.app U ((F.unitHomEquiv s).val U))
      (A.exteriorGenerator.val.app U ((F.unitHomEquiv s).val U)) = 0
  exact A.squareZero_exteriorGenerator U _

/-- The actual wedge morphism, using the constructed exterior algebra. -/
def wedgeBySection (σ : F.sections) : F ⟶ exteriorSquare F :=
  wedgeBySectionIn F (exteriorAlgebras F) σ

/-- The formula for the actual wedge morphism on local sections. -/
theorem wedgeBySection_app (σ : F.sections) (U : X.Opensᵒᵖ) (y : F.val.obj U) :
    (wedgeBySection F σ).val.app U y =
      ((exteriorAlgebras F).exterior.mul 1 1).app U
        ((exteriorAlgebras F).exteriorGenerator.val.app U (σ.val U))
        ((exteriorAlgebras F).exteriorGenerator.val.app U y) := rfl

/-- The composite of an actual global section with wedge by itself is
zero, with no supplied alternation hypothesis. -/
theorem section_comp_wedgeBySection_eq_zero
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    s ≫ wedgeBySection F (F.unitHomEquiv s) = 0 :=
  section_comp_wedgeBySectionIn_eq_zero F (exteriorAlgebras F) s

end NativeExterior

section NativeTensorExt

variable {X : Scheme.{u}} [HasExt.{w} X.Modules]

/-- Tensor on the right with an actual module sheaf. -/
abbrev tensorRight (F : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).flip.obj F

theorem tensorRight_additive (F : X.Modules) : (tensorRight F).Additive where
  map_add := NatTrans.congr_app
    (Functor.map_add (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf)) F

/-- Finite local freeness makes the original tensor functor exact. -/
theorem tensorRight_exact (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F) :
    exactFunctor X.Modules X.Modules (tensorRight F) :=
  SheafOfModules.isFlat_of_isFiniteLocallyFree F hF

/-- Tensoring the original section in the second factor, with its ambient
category explicitly fixed to the native scheme modules. -/
def tensorBySection (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    tensorRight (_root_.SheafOfModules.unit X.ringCatSheaf) ⟶ tensorRight F :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).flip.map s

/-- The actual wedge map tensored with the coefficient sheaf. -/
def tensorWedgeMap (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) (B : X.Modules) :
    (tensorRight F).obj B ⟶ (tensorRight (exteriorSquare F)).obj B :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).obj B).map
    (wedgeBySection F (F.unitHomEquiv s))

/-- The actual tensor-extension Yoneda diagonal vanishes. The only
geometric premise is finite local freeness of F, used to tensor Ext
exactly. The zero composite comes from the constructed exterior algebra.
The Ext universe is arbitrary, including the native locally small one. -/
theorem tensorExt_wedge_diagonal_eq_zero
    (F : X.Modules) (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F)
    {A B : X.Modules} {n : ℕ} (ξ : Abelian.Ext A B n)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    let := tensorRight_additive F
    let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
    let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
    ((Abelian.Ext.mk₀ (C := X.Modules) ((tensorBySection F s).app A)).comp
      (ξ.mapExactFunctor (tensorRight F)) (zero_add n)).comp
      (Abelian.Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s B)) (add_zero n) = 0 := by
  let U : X.Modules := _root_.SheafOfModules.unit X.ringCatSheaf
  let := tensorRight_additive F
  let := tensorRight_additive U
  have hflatF := tensorRight_exact F hF
  have hflatU := tensorRight_exact U
    (SheafOfModules.isFiniteLocallyFreeOfRank_unit X).isFiniteLocallyFree
  let : PreservesFiniteLimits (tensorRight F) := hflatF.1
  let : PreservesFiniteColimits (tensorRight F) := hflatF.2
  let : PreservesFiniteLimits (tensorRight U) := hflatU.1
  let : PreservesFiniteColimits (tensorRight U) := hflatU.2
  refine ext_diagonal_zero_of_naturality (tensorBySection F s) ξ (tensorWedgeMap F s B) ?_
  change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).obj B).map s ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).obj B).map
      (wedgeBySection F (F.unitHomEquiv s)) = 0
  rw [← Functor.map_comp, section_comp_wedgeBySection_eq_zero, Functor.map_zero]

/-- The diagonal identity for the actual class of a tensorized short
exact sequence. This uses native functoriality of extClass, so its
connecting class is identified, rather than assumed to be cup product. -/
theorem tensorShortExact_wedge_diagonal_eq_zero
    (F : X.Modules) (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    let := tensorRight_additive F
    let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
    let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
    ((Abelian.Ext.mk₀ (C := X.Modules) ((tensorBySection F s).app S.X₃)).comp
      (hS.map_of_exact (tensorRight F)).extClass (zero_add 1)).comp
      (Abelian.Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s S.X₁)) (add_zero 1) = 0 := by
  let := tensorRight_additive F
  let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
  let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
  let p (e : Abelian.Ext ((tensorRight F).obj S.X₃) ((tensorRight F).obj S.X₁) 1) :=
    ((Abelian.Ext.mk₀ (C := X.Modules) ((tensorBySection F s).app S.X₃)).comp e (zero_add 1)).comp
      (Abelian.Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s S.X₁)) (add_zero 1)
  exact (congrArg p (Abelian.Ext.mapExactFunctor_extClass (tensorRight F) hS).symm).trans
    (tensorExt_wedge_diagonal_eq_zero F hF hS.extClass s)

end NativeTensorExt

end M9Native.MukaiCupAlternating
