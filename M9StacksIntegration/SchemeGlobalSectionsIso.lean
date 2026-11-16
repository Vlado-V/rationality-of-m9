module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Global functions on an actual scheme isomorphism retain the original
field scalars when its actual structural triangle commutes. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.SchemeGlobalSectionsIso

variable (K : Type u) [Field K] {X Y : Scheme.{u}}

/-- The actual global-function isomorphism for the original field actions. -/
def globalSectionsAlgEquiv (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
    (e : X ≅ Y) (he : e.hom ≫ fY = fX) :
    letI : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop).hom.toAlgebra
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fY.appTop).hom.toAlgebra
    Γ(Y, ⊤) ≃ₐ[K] Γ(X, ⊤) := by
  letI : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop).hom.toAlgebra
  letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fY.appTop).hom.toAlgebra
  have hc : ((Scheme.ΓSpecIso (.of K)).inv ≫ fY.appTop) ≫ e.hom.appTop =
      (Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, he]
  exact { (asIso e.hom.appTop).commRingCatIsoToRingEquiv with
    commutes' := fun r => congrArg (fun a : CommRingCat.of K ⟶ CommRingCat.of Γ(X, ⊤) => a r) hc }

theorem finrank_globalSections_eq (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
    (e : X ≅ Y) (he : e.hom ≫ fY = fX) :
    letI : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop).hom.toAlgebra
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fY.appTop).hom.toAlgebra
    finrank K Γ(X, ⊤) = finrank K Γ(Y, ⊤) := by
  let : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop).hom.toAlgebra
  let : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ fY.appTop).hom.toAlgebra
  exact (globalSectionsAlgEquiv K fX fY e he).toLinearEquiv.finrank_eq.symm

end M9Native.SchemeGlobalSectionsIso

end
