module

public import M9StacksIntegration.StandaloneModuliDraft
public import M9StacksIntegration.EtaleDensePullback

/-! Genuine dense open immersions of schemes define the all-test dense opens
in the standalone moduli statement. Density is tested only along etale charts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9Native.StandaloneDenseOpen

variable (K : Type u) [Field K]

local instance openPropertyStable :
    (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
      (Over.forget (M9StandaloneDraft.Base K))).IsStableUnderBaseChange where
  of_isPullback h hg :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion.{u}) (h.map (Over.forget (M9StandaloneDraft.Base K))) hg

/-- Actual open immersions satisfy the representable all-test property. -/
theorem openImmersion_yoneda {U X : M9StandaloneDraft.Schemes K} (j : U ⟶ X)
    [IsOpenImmersion j.left] : M9StandaloneDraft.OpenImmersion K (yoneda.map j) := by
  apply MorphismProperty.relative_map
  change IsOpenImmersion j.left
  infer_instance

/-- Ordinary scheme density implies literal etale-chart-tested density in
all original test schemes, retaining every represented pullback square. -/
theorem denseOpen_yoneda {U X : M9StandaloneDraft.Schemes K} (j : U ⟶ X)
    [IsOpenImmersion j.left] (hj : DenseRange j.left) :
    M9StandaloneDraft.DenseOpen K (yoneda.map j) := by
  refine ⟨openImmersion_yoneda K j, ?_⟩
  intro V v hv P a b hp
  let v' : V ⟶ X := yoneda.preimage v
  let b' : P ⟶ U := yoneda.preimage b
  have hv' : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf (yoneda.map v') := by
    simpa only [v',yoneda.map_preimage] using hv
  have hvEtale : Etale v'.left :=
    MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))) (F := yoneda) hv'
  letI := hvEtale
  have hp' : IsPullback (yoneda.map b') (yoneda.map a) (yoneda.map j) (yoneda.map v') := by
    simpa only [b',v',yoneda.map_preimage] using hp
  have hOver : IsPullback b' a j v' := hp'.of_map_of_faithful yoneda
  have hScheme := hOver.map (Over.forget (M9StandaloneDraft.Base K))
  exact EtaleDensePullback.denseRange_of_isPullback j.left v'.left b'.left a.left hScheme hj

end M9Native.StandaloneDenseOpen
