module

public import M9StacksIntegration.MukaiExtAdjunction

/-!
# Section evaluation under the actual Ext adjunction

A natural section `θ : Id ⟶ F` gives an actual evaluation map
`G W ⟶ W` by the adjunction counit. The proved Yoneda identity says
pulling back the transposed Ext class by that section is precisely
postcomposing the original class by this evaluation map. No comparison
of independently chosen cohomology boundaries enters this statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w

namespace M9Native.MukaiExtEvaluation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {F G : C ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The evaluation is an actual composite of the given natural section
with the genuine adjunction counit. -/
def adjunctionEvaluation (adj : F ⊣ G) (θ : 𝟭 C ⟶ F) (W : C) : G.obj W ⟶ W :=
  θ.app (G.obj W) ≫ adj.counit.app W

/-- Pulling back the transposed actual Yoneda class is its actual
postcomposition by section evaluation. -/
theorem extAdjunction_evaluation (adj : F ⊣ G) (θ : 𝟭 C ⟶ F)
    {A W : C} {n : ℕ} (e : Ext A (G.obj W) n) :
    (Ext.mk₀ (θ.app A)).comp (adj.extEquiv.symm e) (zero_add n) =
      e.comp (Ext.mk₀ (adjunctionEvaluation adj θ W)) (add_zero n) := by
  rw [Adjunction.extEquiv_symm_apply,
    ← Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (zero_add n),
    ← Ext.mapExactFunctor_comp_mk₀_natTransApp e θ,
    Ext.id_mapExactFunctor,
    Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (add_zero n),
    Ext.mk₀_comp_mk₀]
  rfl

/-- Therefore an actual zero evaluation gives an actual zero pullback
under the transposed Ext class. -/
theorem extAdjunction_pullback_eq_zero_of_evaluation (adj : F ⊣ G)
    (θ : 𝟭 C ⟶ F) {A W : C} {n : ℕ} (e : Ext A (G.obj W) n)
    (h : e.comp (Ext.mk₀ (adjunctionEvaluation adj θ W)) (add_zero n) = 0) :
    (Ext.mk₀ (θ.app A)).comp (adj.extEquiv.symm e) (zero_add n) = 0 :=
  (extAdjunction_evaluation adj θ e).trans h

end M9Native.MukaiExtEvaluation
