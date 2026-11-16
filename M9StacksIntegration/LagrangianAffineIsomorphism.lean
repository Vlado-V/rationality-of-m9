module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! Actual quasicoherent morphisms on an affine scheme are detected on global sections. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianAffineIsomorphism

/-- This criterion uses the original tilde/global-sections counit and
its actual naturality. No local isomorphism premise is supplied. -/
theorem isIso_of_globalSections_bijective {R : CommRingCat.{u}}
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (hφ : Function.Bijective (φ.app ⊤)) : IsIso φ := by
  let ψ := (moduleSpecΓFunctor (R := R)).map φ
  letI : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).mpr hφ
  let eF := asIso (Scheme.Modules.fromTildeΓ F)
  let eG := asIso (Scheme.Modules.fromTildeΓ G)
  have hnat : (tilde.functor R).map ψ ≫ eG.hom=eF.hom ≫ φ :=
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have hcomp : IsIso ((tilde.functor R).map ψ ≫ eG.hom) := by infer_instance
  letI : IsIso (eF.hom ≫ φ) := hnat ▸ hcomp
  exact (isIso_comp_left_iff eF.hom φ).mp inferInstance

end M9Native.LagrangianAffineIsomorphism
