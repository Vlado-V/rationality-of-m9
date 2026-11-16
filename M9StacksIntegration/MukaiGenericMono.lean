module

public import M9StacksIntegration.MukaiSaturationRank

/-!
# Generic injectivity of an actual torsion-free-source sheaf morphism

On an integral scheme, sections of a torsion-free quasi-coherent
module are determined by their actual generic germs. Consequently an
original sheaf morphism from such a module is monic when its original
generic stalk map is injective. This supplies the genuine first
alternative in Mukai's semi-irreducibility definition; a desired rank
or monomorphism is not inserted as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.MukaiGenericMono

open MukaiSaturationRank

variable {X : Scheme.{u}}

/-- The actual map of local-ring stalks sends the original zero sheaf
morphism to zero on every genuine stalk element. -/
theorem stalkMap_zero {F G : X.Modules} (x : X) (m : Stalk F x) :
    stalkMap (0 : F ⟶ G) x m = 0 := by
  obtain ⟨U,hx,t,rfl⟩ := F.presheaf.exists_germ_eq m
  rw [stalkMap_germ]
  change TopCat.Presheaf.germ G.presheaf U x hx 0 = 0
  exact map_zero _

/-- Equality of original generic stalk maps determines an original
morphism into a torsion-free quasi-coherent sheaf. -/
theorem hom_ext_of_generic_stalkMap_eq [IsIntegral X]
    {G F : X.Modules} [F.IsQuasicoherent]
    (hF : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree F)
    (a b : G ⟶ F)
    (h : ∀ m : Stalk G (genericPoint X),
      stalkMap a (genericPoint X) m = stalkMap b (genericPoint X) m) : a = b := by
  apply Scheme.Modules.hom_ext_iff.mpr
  intro U
  by_cases hη : genericPoint X ∈ U
  · ext m
    apply injective_generic_germ_of_isTorsionFree F hF hη
    exact (stalkMap_germ a (genericPoint X) U hη m).symm.trans
      ((h _).trans (stalkMap_germ b (genericPoint X) U hη m))
  · have : Subsingleton Γ(F,U) := subsingleton_sections_of_notMem_genericPoint F U hη
    ext m
    exact Subsingleton.elim _ _

/-- Injectivity of the genuine generic stalk map implies that the
original sheaf morphism itself is monic. -/
theorem mono_of_generic_stalkMap_injective [IsIntegral X]
    {F E : X.Modules} [F.IsQuasicoherent]
    (hF : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree F)
    (φ : F ⟶ E) (hφ : Function.Injective (stalkMap φ (genericPoint X))) : Mono φ := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro G a ha
  apply hom_ext_of_generic_stalkMap_eq hF a 0
  intro m
  rw [stalkMap_zero]
  apply hφ
  rw [map_zero]
  exact (stalkMap_comp a φ (genericPoint X) m).symm.trans (by rw [ha,stalkMap_zero])

end M9Native.MukaiGenericMono
