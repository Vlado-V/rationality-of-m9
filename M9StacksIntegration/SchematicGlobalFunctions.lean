module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions

/-!
# Global functions of the original represented schemes

The native global-functions pullback is defined through its actual atlas
comparison. Its compatibility with scheme pullback is therefore proved
using the native chart naturality theorem, rather than treated as a
definitional equality. Bijectivity then transfers through the actual
identity-chart ring equivalences.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.SchematicGlobalFunctions
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity-chart comparisons intertwine the actual native
global-functions map and the original scheme's actual pullback. -/
theorem yoneda_naturality {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (s : globalFunctions' B S hS (yoneda.obj V)) :
    globalFunctionsYonedaRingEquiv B S hS U
        (globalFunctionsMap B S hS (schemeSpaceMap g) s) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        (globalFunctionsYonedaRingEquiv B S hS V s) := by
  have ht : yoneda.map g ≫ (idEtaleChart B S hS V).obj.hom =
      (idEtaleChart B S hS U).obj.hom ≫ (schemeSpaceMap g).hom := by
    change yoneda.map g ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map g
    rw [Category.comp_id, Category.id_comp]
  exact globalFunctionsMap_val_chart B S hS (schemeSpaceMap g)
    (idEtaleChart B S hS V) (idEtaleChart B S hS U) g ht s

/-- Actual bijectivity of scheme pullback gives actual bijectivity of
the native represented-space pullback, through the proved comparisons. -/
theorem bijective_of_bijective_appTop {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop.hom) :
    Function.Bijective (globalFunctionsMap B S hS (schemeSpaceMap g)) := by
  let eU := globalFunctionsYonedaRingEquiv B S hS U
  let eV := globalFunctionsYonedaRingEquiv B S hS V
  constructor
  · intro a b hab
    apply eV.injective
    apply hg.1
    exact (yoneda_naturality B S hS g a).symm.trans
      ((congrArg eU hab).trans (yoneda_naturality B S hS g b))
  · intro a
    obtain ⟨b, hb⟩ := hg.2 (eU a)
    refine ⟨eV.symm b, ?_⟩
    apply eU.injective
    rw [yoneda_naturality, eV.apply_symm_apply, hb]

end M9Native.SchematicGlobalFunctions
