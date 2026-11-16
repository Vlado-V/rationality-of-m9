module

public import M9StacksIntegration.SectionZeroEvaluation
public import M9StacksIntegration.SectionZeroIdealFactorization

/-!
# Pulling back the literal native vector-section zero ideal

The native zero ideal agrees with its proved dual-evaluation ideal.
Thus the genuine all-test-scheme pullback theorem applies to the literal
native zero scheme, in arbitrary finite locally free rank and without
replacing its scheme structure by its support.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.NativeVectorSectionZeroPullback

/-- The two definitions have exactly the same native affine ideals. -/
theorem zeroSchemeOfSection_eq_evaluationIdeal {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E, ⊤)) :
    Stacks.Chow.zeroSchemeOfSection X E s =
      SectionZeroIdealFactorization.sectionZeroIdeal X E s := by
  ext U
  rw [Stacks.Chow.SectionZeroScheme.zeroSchemeOfSection_ideal,
    SectionZeroIdealFactorization.sectionZeroIdeal_ideal]

/-- The literal full native zero ideal commutes with every native
scheme pullback. No flatness, reducedness, or regularity is assumed. -/
theorem zeroSchemeOfSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (s : Γ(E, ⊤)) :
    Stacks.Chow.zeroSchemeOfSection Y ((Scheme.Modules.pullback f).obj E)
        (pullbackGlobalSections f E s) =
      (Stacks.Chow.zeroSchemeOfSection X E s).comap f := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback f).obj E) r :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      f.base f.toRingCatSheafHom E r inferInstance
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      ((Scheme.Modules.pullback f).obj E) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Scheme.Modules.pullback f).obj E) r
  rw [zeroSchemeOfSection_eq_evaluationIdeal,
    zeroSchemeOfSection_eq_evaluationIdeal]
  exact SectionZeroIdealFactorization.sectionZeroIdeal_pullback f E r s

end M9Native.NativeVectorSectionZeroPullback
