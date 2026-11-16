module

public import M9StacksIntegration.ExteriorEvaluation
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackMonoDualMap
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ExteriorPowerMono

/-!
# Exterior powers of an actual subbundle are universally monomorphic

A short exact sequence with finite locally free quotient splits at every
actual local-ring stalk. Exterior functoriality carries those actual
retractions to retractions of every exterior-power stalk map. The native
pullback-stalk theorem then proves that the actual exterior map remains
monic after EVERY scheme pullback, including nonreduced test schemes.
No universal injectivity or local splitting is supplied as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SheafOfModules.SheafHomStalk
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf

namespace M9Native.ExteriorSubbundleUniversalMono
universe u
variable {X : Scheme.{u}}

/-- Two native stalk-map spellings give the SAME actual local-ring map. -/
theorem stalkMapL_eq_stalkHom {E F : X.Modules} (j : E ⟶ F) (x : X)
    (z : E.presheaf.stalk x) :
    PresheafOfModules.stalkMapL x j.val z = stalkHom j x z := by
  obtain ⟨U, hx, t, rfl⟩ := E.presheaf.exists_germ_eq z
  exact (PresheafOfModules.stalkMapL_germ x j.val U hx t).trans
    (stalkHom_germAt j x U hx t).symm

/-- The actual exterior-stalk comparison is natural for the actual map. -/
theorem stalkComparison_map {E F : X.Modules} (j : E ⟶ F) (n : ℕ) (x : X)
    (z : (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf.stalk x) :
    ExteriorEvaluation.stalkComparison F n x
        (stalkHom (Scheme.Modules.exteriorPowerMap j (n : ℤ)) x z) =
      exteriorPower.map n (stalkHom j x) (ExteriorEvaluation.stalkComparison E n x z) := by
  have h := _root_.SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap
    (Scheme.Modules.exteriorGenerator E) (Scheme.Modules.exteriorGenerator F)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F) j n x z
  change ExteriorEvaluation.stalkComparison F n x
      (PresheafOfModules.stalkMapL x (Scheme.Modules.exteriorPowerMap j (n : ℤ)).val z) =
    exteriorPower.map n (PresheafOfModules.stalkMapL x j.val)
      (ExteriorEvaluation.stalkComparison E n x z) at h
  have he : PresheafOfModules.stalkMapL x j.val = stalkHom j x :=
    LinearMap.ext (stalkMapL_eq_stalkHom j x)
  have hext := stalkMapL_eq_stalkHom (Scheme.Modules.exteriorPowerMap j (n : ℤ)) x z
  rw [he] at h
  rw [hext] at h
  exact h

/-- Actual short exactness and a locally free quotient, rather than an
assumed exterior injection, prove universal monicity of the exterior map. -/
theorem mono_pullback_exteriorPowerMap (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} S.X₃) (n : ℕ)
    {T : Scheme.{u}} (f : T ⟶ X) :
    Mono ((Scheme.Modules.pullback f).map (Scheme.Modules.exteriorPowerMap S.f (n : ℤ))) := by
  apply mono_pullback_map_of_forall_stalk_splitInjective
  intro x
  obtain ⟨r, hr⟩ := exists_stalkHom_retraction S.f S.g S.zero hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hQ) x
  let re : (Scheme.Modules.exteriorPower S.X₂ (n : ℤ)).presheaf.stalk x
      →ₗ[X.presheaf.stalk x] (Scheme.Modules.exteriorPower S.X₁ (n : ℤ)).presheaf.stalk x :=
    (ExteriorEvaluation.stalkComparison S.X₁ n x).symm.toLinearMap.comp
      ((exteriorPower.map n r).comp (ExteriorEvaluation.stalkComparison S.X₂ n x).toLinearMap)
  refine ⟨re, fun z => ?_⟩
  apply (ExteriorEvaluation.stalkComparison S.X₁ n x).injective
  change (ExteriorEvaluation.stalkComparison S.X₁ n x)
      ((ExteriorEvaluation.stalkComparison S.X₁ n x).symm
        (exteriorPower.map n r
          (ExteriorEvaluation.stalkComparison S.X₂ n x
            (stalkHom (Scheme.Modules.exteriorPowerMap S.f (n : ℤ)) x z)))) = _
  rw [LinearEquiv.apply_symm_apply, stalkComparison_map]
  let sf : S.X₁.presheaf.stalk x →ₗ[X.presheaf.stalk x] S.X₂.presheaf.stalk x := stalkHom S.f x
  have hret : r.comp sf = LinearMap.id := LinearMap.ext hr
  change exteriorPower.map n r (exteriorPower.map n sf
    (ExteriorEvaluation.stalkComparison S.X₁ n x z)) = _
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hret, exteriorPower.map_id,
    LinearMap.id_apply]

end M9Native.ExteriorSubbundleUniversalMono
