module

public import M9StacksIntegration.MukaiHomExact
public import M9StacksIntegration.InvertibleHomCancellation

/-!
# Actual tensor-Hom adjunction on Ext for the Mukai pairing

Both exactness and linearity of the right adjoint are derived from the
actual tensor-dual natural isomorphism. The scalar action is precisely
`modulesLinearOverField`, used by the original extension construction.
The final categorical identity transports an actual adjunction mate on
Yoneda Ext; it does not assume an alternating form or a parity result.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v w

namespace M9Native.MukaiExtAdjunction

open M9Native.MukaiCupAlternating M9Native.MukaiHomExact

variable {X : Scheme.{u}}

/-- Additivity of native sheaf-Hom comes from its actual tensor-dual
natural isomorphism. -/
theorem homFunctor_additive (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) :
    (homFunctor F).Additive := by
  let := tensorRight_additive
    (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F)
  exact Functor.additive_of_iso (tensorDualHomNatIso F r hF)

/-- The same actual comparison preserves the exact original scalar
action on scheme-module morphisms. -/
theorem homFunctor_linear (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) :
    letI := modulesLinearOverField k f
    Functor.Linear k (homFunctor F) := by
  let := modulesLinearOverField k f
  let := M9StacksIntegration.InvertibleHomCancellation.tensorRight_linear f
    (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F)
  exact Functor.linear_of_iso k (tensorDualHomNatIso F r hF)

section NativeExt

variable [HasExt.{w} X.Modules]

/-- The actual native tensor-Hom adjunction induces an additive
bijection of the actual Yoneda Ext groups in every degree. -/
def tensorHomExtAddEquiv (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r)
    (A W : X.Modules) (n : ℕ) :
    Ext ((tensorRight F).obj A) W n ≃+ Ext A ((homFunctor F).obj W) n := by
  letI := tensorRight_additive F
  letI := homFunctor_additive F r hF
  letI := hF
  let hfree := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  letI : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hfree).1
  letI : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hfree).2
  letI : PreservesFiniteLimits (homFunctor F) := (homFunctor_exact F r hF).1
  letI : PreservesFiniteColimits (homFunctor F) := (homFunctor_exact F r hF).2
  let adj : tensorRight F ⊣ homFunctor F :=
    Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F
  exact adj.extEquiv.{w,w}

/-- The bijection is linear for the original extension scalar action. -/
def tensorHomExtLinearEquiv (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r)
    (A W : X.Modules) (n : ℕ) :
    letI := modulesLinearOverField k f
    Ext ((tensorRight F).obj A) W n ≃ₗ[k] Ext A ((homFunctor F).obj W) n := by
  letI := modulesLinearOverField k f
  letI := tensorRight_additive F
  letI := homFunctor_additive F r hF
  letI := homFunctor_linear k f F r hF
  letI := hF
  let hfree := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  letI : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hfree).1
  letI : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hfree).2
  letI : PreservesFiniteLimits (homFunctor F) := (homFunctor_exact F r hF).1
  letI : PreservesFiniteColimits (homFunctor F) := (homFunctor_exact F r hF).2
  let adj : tensorRight F ⊣ homFunctor F :=
    Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F
  exact adj.extLinearEquiv.{w,w} k

/-- The linear equivalence retains exactly the additive adjunction map. -/
theorem tensorHomExtLinearEquiv_toAddEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r)
    (A W : X.Modules) (n : ℕ) :
    letI := modulesLinearOverField k f
    (tensorHomExtLinearEquiv k f F r hF A W n).toAddEquiv =
      tensorHomExtAddEquiv F r hF A W n := by
  let := modulesLinearOverField k f
  rfl

end NativeExt

section Mate

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {F G F' G' : C ⥤ C}
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- Actual adjunction mates retain their naturality on Yoneda Ext.
The displayed mate identity is a degree-zero structural identity of the
two adjunctions, not a hypothesis on an Ext class or a bilinear form. -/
theorem extAdjunction_mate (adj : F ⊣ G) (adj' : F' ⊣ G')
    (τ : F ⟶ F') (σ : G' ⟶ G)
    (hMate : ∀ Y, F.map (σ.app Y) ≫ adj.counit.app Y =
      τ.app (G'.obj Y) ≫ adj'.counit.app Y)
    {A W : C} {n : ℕ} (e : Ext A (G'.obj W) n) :
    adj.extEquiv.symm (e.comp (Ext.mk₀ (σ.app W)) (add_zero n)) =
      (Ext.mk₀ (τ.app A)).comp (adj'.extEquiv.symm e) (zero_add n) := by
  rw [Adjunction.extEquiv_symm_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (add_zero n), Ext.mk₀_comp_mk₀,
    hMate W, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (add_zero n),
    Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (zero_add n),
    Adjunction.extEquiv_symm_apply]

end Mate

end M9Native.MukaiExtAdjunction
