module

public import M9StacksIntegration.GenusNineCoarseOverField

/-!
# The actual smooth curve stack has finite diagonal

This uses the original separatedness and quasi-DM conclusions of the checked
native constructor. Finiteness is proved for every actual algebraic space
representing a base change of the diagonal, by properness and local
quasi-finiteness. It is stronger than finiteness of the inertia projection.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace M9Native.StackFiniteDiagonal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A separated quasi-DM algebraic stack has a finite absolute diagonal.
The quantified representatives are the actual native base changes. -/
theorem relativeProperty_of_separated_quasiDM
    (X : Stack.AlgebraicStacks.{u, w} B S hS)
    (hsep : Stack.IsSeparatedOver B S hS X)
    (hqdm : Stack.IsQuasiDMOver B S hS X) :
    Stack.RelativeProperty B S hS (Space.finiteMorphismProperty B S hS)
      (Stack.diagonal.{u, u, u + 1} B S hS X.val) := by
  have hproper : Stack.RelativeProperty B S hS (Space.properProperty B S hS)
      (Stack.diagonal.{u, u, u + 1} B S hS X.val) :=
    (Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism B S hS X
      (Space.properProperty B S hS)).2 hsep
  have hquasi : Stack.RelativeProperty B S hS (Space.locallyQuasiFiniteProperty B S hS)
      (Stack.diagonal.{u, u, u + 1} B S hS X.val) :=
    (Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism B S hS X
      (Space.locallyQuasiFiniteProperty B S hS)).2 hqdm
  intro U z hz F hF he
  exact Space.isFinite_of_isProper_of_isLocallyQuasiFinite B S hS
    (ObjectProperty.FullSubcategory.property _)
    (ObjectProperty.FullSubcategory.property _) _
    (hproper U z hz F hF he) (hquasi U z hz F hF he)

end M9Native.StackFiniteDiagonal

namespace M9Native.GenusNineFiniteDiagonal

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The finite diagonal of the actual native field-base smooth genus-nine
stack; no algebraicity, diagonal, or coarse-space premise is supplied. -/
theorem actual :
    Stack.RelativeProperty B (Spec (.of K)) hK
      (Space.finiteMorphismProperty B (Spec (.of K)) hK)
      (Stack.diagonal.{u, u, u + 1} B (Spec (.of K)) hK
        (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9
          (by decide)).val) :=
  M9Native.StackFiniteDiagonal.relativeProperty_of_separated_quasiDM B _ hK _
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack_separated B hZ K hK 9
      (by decide))
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack_quasiDM B hZ K hK 9
      (by decide))

end M9Native.GenusNineFiniteDiagonal
