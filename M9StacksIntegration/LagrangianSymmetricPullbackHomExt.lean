module

public import M9StacksIntegration.LagrangianSymmetricPullbackProduct

/-! Actual morphisms from a pulled-back symmetric square are detected on its local unit products. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.LagrangianSymmetricPullbackHomExt

open LagrangianSymmetricPullbackProduct

variable {X Y : Scheme.{u}}

/-- The actual pullback adjunction and native symmetric sheafification
universal property reduce equality to literal local generator products. -/
theorem hom_ext_products (g : X ⟶ Y) (F : Y.Modules) {N : X.Modules}
    {a b : (Scheme.Modules.pullback g).obj
      ((Scheme.Modules.symmetricAlgebra Y F).piece 2) ⟶ N}
    (h : ∀ (U : Y.Opens) (α β : Γ(F,U)),
      a.val.app (op (g ⁻¹ᵁ U))
        (pullbackUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β))=
      b.val.app (op (g ⁻¹ᵁ U))
        (pullbackUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β))) :
    a=b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply SymPow.sqMul_ext
  intro α β
  exact h U.unop α β

end M9Native.LagrangianSymmetricPullbackHomExt
