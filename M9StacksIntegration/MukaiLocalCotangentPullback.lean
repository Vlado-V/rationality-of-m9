module

public import M9StacksIntegration.LagrangianFieldJetCoefficients
public import M9StacksIntegration.SpecFieldPullbackSections
public import M9StacksIntegration.LineFramePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization

/-!
# Actual local cotangent pullback at a field point

The map is the literal native comparison for iterated pullback, followed
by pullback of the canonical relative-differentials map. Its action on
the differential of an actual local function follows from the native
universal derivation and actual pullback-section composition. There is
no supplied chain-rule compatibility or point-over-base identity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.MukaiLocalCotangentPullback

variable (K : Type u) [Field K] {A Y : Scheme.{u}}
  (b : Y ⟶ Spec (.of K)) (h : A ⟶ Y) (q : A ⟶ Spec (.of K))
  (hh : h ≫ b = q) (z : Spec (.of K) ⟶ A)

/-- The actual canonical differential map of the original commuting base square. -/
def differentialsMap : (Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials b) ⟶
    Scheme.Hom.relativeDifferentials q :=
  Scheme.Hom.relativeDifferentialsMap h b q (𝟙 _) (by simpa using hh)

/-- The literal sheaf map from the composite point pullback to the source cotangent fibre. -/
def cotangentSheafMap :
    (Scheme.Modules.pullback (z ≫ h)).obj (Scheme.Hom.relativeDifferentials b) ⟶
      (Scheme.Modules.pullback z).obj (Scheme.Hom.relativeDifferentials q) :=
  (Scheme.Modules.pullbackComp z h).inv.app (Scheme.Hom.relativeDifferentials b) ≫
    (Scheme.Modules.pullback z).map (differentialsMap K b h q hh)

/-- The original point-cotangent map, with the actual Spec(K) scalar structure. -/
def pointCotangentMap : LagrangianFieldJetCoefficients.Cotangent K b (z ≫ h) →ₗ[K]
    LagrangianFieldJetCoefficients.Cotangent K q z :=
  (moduleSpecΓFunctor.map (cotangentSheafMap K b h q hh z)).hom

theorem pointCotangentMap_apply
    (v : LagrangianFieldJetCoefficients.Cotangent K b (z ≫ h)) :
    pointCotangentMap K b h q hh z v =
      ((Scheme.Modules.pullback z).map (differentialsMap K b h q hh)).app ⊤
        (((Scheme.Modules.pullbackComp z h).inv.app
          (Scheme.Hom.relativeDifferentials b)).app ⊤ v) := rfl

/-- The actual field point lies in U because the whole source maps to U. -/
def point_mem (U : Y.Opens) (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U) :
    (z ≫ h).base (SpecFieldStalkSections.point K) ∈ U :=
  hU trivial

/-- Native pullback composition, solved for its actual inverse comparison
and applied to the original local section. -/
theorem pullbackComp_inv_pulledSection (M : Y.Modules) (U : Y.Opens)
    (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U) (t : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp z h).inv.app M).app ⊤
        (SpecFieldPullbackSections.pulledSection K (z ≫ h) M U
          (point_mem K h z U hU) t) =
      pullbackGlobalSections z ((Scheme.Modules.pullback h).obj M)
        (Scheme.Modules.pullbackSection h M U ⊤ hU t) := by
  let hz : (⊤ : (Spec (.of K)).Opens) ≤ z ⁻¹ᵁ (⊤ : A.Opens) := by simp
  have hc := Scheme.Modules.pullbackSection_comp z h M U ⊤ ⊤ hU hz
    (SpecFieldPullbackSections.preimageTop K (z ≫ h) U (point_mem K h z U hU)) t
  have hi := congrArg (((Scheme.Modules.pullbackComp z h).inv.app M).app ⊤) hc
  have he := congrArg (fun f => f.app ⊤
    (Scheme.Modules.pullbackSection z ((Scheme.Modules.pullback h).obj M) ⊤ ⊤ hz
      (Scheme.Modules.pullbackSection h M U ⊤ hU t)))
    ((Scheme.Modules.pullbackComp z h).app M).hom_inv_id
  exact (hi.symm.trans he).trans
    (pullbackGlobalSections_eq_pullbackSection z ((Scheme.Modules.pullback h).obj M) hz _).symm

/-- The actual untransposed chain rule for the original local function. -/
theorem differentialsMap_pulled_d (U : Y.Opens)
    (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U) (t : Γ(Y, U)) :
    (differentialsMap K b h q hh).app ⊤
        (Scheme.Modules.pullbackSection h (Scheme.Hom.relativeDifferentials b) U ⊤ hU
          ((Scheme.Hom.universalRelativeDerivation b).d t)) =
      (Scheme.Hom.universalRelativeDerivation q).d (h.appLE U ⊤ hU t) :=
  Scheme.Hom.relativeDifferentialsMap_pullbackSection h b q (𝟙 _)
    (by simpa using hh) U ⊤ hU t

/-- Actual cotangent pullback carries the pulled local universal differential
to the literal point derivative of the original pulled function. -/
theorem pointCotangentMap_pulled_d (U : Y.Opens)
    (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U) (t : Γ(Y, U)) :
    pointCotangentMap K b h q hh z
        (SpecFieldPullbackSections.pulledSection K (z ≫ h)
          (Scheme.Hom.relativeDifferentials b) U (point_mem K h z U hU)
          ((Scheme.Hom.universalRelativeDerivation b).d t)) =
      LagrangianFieldJetCoefficients.pointDerivative K q z (h.appLE U ⊤ hU t) := by
  rw [pointCotangentMap_apply, pullbackComp_inv_pulledSection K h z
    (Scheme.Hom.relativeDifferentials b) U hU ((Scheme.Hom.universalRelativeDerivation b).d t)]
  exact (SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections z
    (differentialsMap K b h q hh) _).trans
    (congrArg (fun v => pullbackGlobalSections z (Scheme.Hom.relativeDifferentials q) v)
      (differentialsMap_pulled_d K b h q hh U hU t))

include hh in
/-- Vanishing of the actual ambient local differential implies vanishing
of the actual source point derivative. -/
theorem pointDerivative_eq_zero_of_pulled_d_eq_zero (U : Y.Opens)
    (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U) (t : Γ(Y, U))
    (ht : SpecFieldPullbackSections.pulledSection K (z ≫ h)
      (Scheme.Hom.relativeDifferentials b) U (point_mem K h z U hU)
      ((Scheme.Hom.universalRelativeDerivation b).d t) = 0) :
    LagrangianFieldJetCoefficients.pointDerivative K q z (h.appLE U ⊤ hU t) = 0 := by
  have hc := pointCotangentMap_pulled_d K b h q hh z U hU t
  rw [ht, map_zero] at hc
  exact hc.symm

end M9Native.MukaiLocalCotangentPullback
