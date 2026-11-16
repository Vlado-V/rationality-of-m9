module

public import M9StacksIntegration.NativeRelativeAffineModels

/-!
# The SAME relative affine models over another actual base

Changing only the ambient base retains the original finite-type K-models
and the actual limiting cone of their underlying schemes. This lets the
relative K-models feed the native absolute curve stack without claiming
that any model is of finite type over the integers.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.NativeRelativeAffineRebase
universe u

/-- View the SAME native affine schemes over another actual base. -/
def rebase (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS') :
    BigAffineFppf B S hS ⥤ BigAffineFppf B S' hS' :=
  ObjectProperty.lift (IsAffineOver B S' hS')
    (BigAffineFppf.inclusion B S hS ⋙ Over.map k) (fun U => U.property)

/-- Forgetting the ambient base retains the literal original schemes/maps. -/
theorem rebase_toScheme (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS') :
    rebase B S S' hS hS' k ⋙ BigAffineFppf.toScheme B S' hS' =
      BigAffineFppf.toScheme B S hS := rfl

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  (S : Scheme.{u}) (hS : B.Contains S) (k : B.obj hK ⟶ B.obj hS)

/-- The ACTUAL K-finite-type diagram, read over the supplied actual base. -/
def diagramOver : (Finset A)ᵒᵖ ⥤ BigAffineFppf B S hS :=
  NativeRelativeAffineModels.diagram K A B hK ⋙ rebase B (Spec (.of K)) S hK hS k

/-- The ACTUAL cone, with all original maps retained. -/
def coneOver (hA : B.Contains (Spec (.of A))) :
    Cone (diagramOver K A B hK S hS k) :=
  (rebase B (Spec (.of K)) S hK hS k).mapCone
    (NativeRelativeAffineModels.cone K A B hK hA)

/-- The cone underlying the actual rebased native diagram is genuinely
limiting among ALL original schemes. -/
def isLimit_toScheme_coneOver (hA : B.Contains (Spec (.of A))) :
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone
      (coneOver K A B hK S hS k hA)) :=
  NativeRelativeAffineModels.isLimit_toScheme_cone K A B hK hA

end M9StacksIntegration.NativeRelativeAffineRebase
