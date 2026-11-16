module

public import M9StacksIntegration.LagrangianKernelLinearEmbedding
public import M9StacksIntegration.LagrangianKernelFiveSections

/-!
# Actual projective comparison for the original five-space

The native map of sections is compared with the native map of functions
using an actual line frame. The coordinate-form ring map is then checked
on the original basis. The resulting projective triangle is a theorem
about actual scheme morphisms, without a supplied equality of maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianKernelProjectiveComparison

open LagrangianPluckerQuotient LagrangianSectionGeneration
open LagrangianProjectiveSections LagrangianKernelLinearEmbedding LagrangianCommonKernelSpan
open Stacks.ProjectiveSpaceChartRatio

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

section Framing

variable {X : Scheme.{u}} {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
  {n : ℕ} (s : Fin (n+1) → Γ(M, ⊤))
  (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
  (e : M ≅ ProjectiveSectionFunctions.UnitLine X)

include hs in
theorem framed_generatesStalks :
    Stacks.ProjectiveFromSections.GeneratesStalks (fun i => e.hom.app ⊤ (s i)) := by
  letI := LagrangianPluckerGeneration.sectionMap_epi_of_generatesStalks s hs
  have hep : Epi (sectionMap X M s ≫ e.hom) := inferInstance
  have hmap := MukaiPrimitiveCanonicalEvaluation.sectionMap_postcomp (X := X) s e.hom
  exact generatesStalks_of_sectionMap_epi X _ _ (hmap ▸ hep)

theorem toProjectiveSpaceOver_framed {S : Scheme.{u}} (f : X ⟶ S)
    (hspan : Ideal.span (Set.range (fun i => (show Γ(X, ⊤) from e.hom.app ⊤ (s i)))) = ⊤) :
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (show Γ(X, ⊤) from e.hom.app ⊤ (s i))) hspan f := by
  calc
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (fun i => e.hom.app ⊤ (s i)) (framed_generatesStalks s hs e) f :=
      ProjectiveSectionIso.toProjectiveSpaceOver_iso s _ hs
        (framed_generatesStalks s hs e) e (fun _ => rfl) f
    _ = _ := ProjectiveSectionFunctions.toProjectiveSpaceOver_unit _
      (framed_generatesStalks s hs e) hspan f

end Framing

section RingEvaluation

variable {k V R : Type u} [CommRing k] [AddCommGroup V] [Module k V] [CommRing R]
  {n : ℕ} (b : Basis (Fin (n+1)) k V) (κ : k →+* R) (s : Fin (n+1) → R)

/-- Evaluation on every actual symmetric-algebra generator, with its structural coefficients. -/
theorem moduleEvaluation_generator (v : V) :
    moduleEvaluation b κ s (SymmetricAlgebra.ι k V v) =
      ∑ i : Fin (n+1), κ (b.repr v i) * s i := by
  have hi := congrArg (SymmetricAlgebra.ι k V) (b.sum_repr v)
  simp only [map_sum, map_smul] at hi
  have h := congrArg (moduleEvaluation b κ s) hi
  simpa only [map_sum, Algebra.smul_def, map_mul,
    LagrangianPluckerClosed.moduleEvaluation_algebraMap,
    LagrangianPluckerClosed.moduleEvaluation_basis] using h.symm

end RingEvaluation

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (sU : Fin 14 → Γ(X, ⊤))
  (hU : Ideal.span (Set.range sU) = ⊤) (sV : Fin 5 → Γ(X, ⊤))
  (hV : Ideal.span (Set.range sV) = ⊤)

/-- The actual symmetric-algebra evaluation triangle is derived from literal original coefficients. -/
theorem evaluation_triangle
    (hrel : ∀ j : Fin 14, sU j = ∑ a : Fin 5,
      baseRingHom f (embeddingFourteen k (Pi.single a 1) j) * sV a) :
    (moduleEvaluation (Pi.basisFun k (Fin 5)) (baseRingHom f) sV).comp
      (gradedHom k).toRingHom =
      moduleEvaluation (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis (baseRingHom f) sU := by
  apply LagrangianPluckerClosed.symmetricRingHom_ext (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis
  · intro c
    change moduleEvaluation (Pi.basisFun k (Fin 5)) (baseRingHom f) sV
      (SymPow.symAlgMap (restrictionToFive k)
        (algebraMap k (SymmetricAlgebra k (Module.Dual k (LagrangianField.Primitive k))) c)) = _
    rw [AlgHom.commutes, LagrangianPluckerClosed.moduleEvaluation_algebraMap,
      LagrangianPluckerClosed.moduleEvaluation_algebraMap]
  · intro j
    rw [LagrangianPluckerClosed.moduleEvaluation_basis]
    simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom, gradedHom,
      SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι]
    rw [moduleEvaluation_generator]
    simp only [Pi.basisFun_repr]
    calc
      _ = ∑ a : Fin 5, baseRingHom f (embeddingFourteen k (Pi.single a 1) j) * sV a := by
        apply Finset.sum_congr rfl
        intro a _
        exact congrArg (fun c => baseRingHom f c * sV a) (restrictionToFive_basis k j a)
      _ = _ := (hrel j).symm

/-- The native P4/P13 triangle on actual global functions, for every test scheme. -/
theorem functions_triangle
    (hrel : ∀ j : Fin 14, sU j = ∑ a : Fin 5,
      baseRingHom f (embeddingFourteen k (Pi.single a 1) j) * sV a) :
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver sV hV f ≫ fixedLinearEmbedding k =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver sU hU f := by
  have h := fromSections_comp_linearMap
    (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis (Pi.basisFun k (Fin 5))
    (restrictionToFive k) (restrictionToFive_surjective k) f sU hU sV hV
    (evaluation_triangle k f sU sV hrel)
  apply (cancel_mono (LagrangianPluckerLinear.primitiveProjectiveIso k).hom).1
  simpa only [fixedLinearEmbedding, linearEmbedding, gradedHom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, LagrangianPluckerLinear.primitiveProjectiveIso] using h

section FramedTriangle

variable {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
  (s : Fin 14 → Γ(M, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
  (t : Fin 5 → Γ(M, ⊤)) (ht : Stacks.ProjectiveFromSections.GeneratesStalks t)
  (e : M ≅ ProjectiveSectionFunctions.UnitLine X)
  (hspanS : Ideal.span (Set.range (fun j => (show Γ(X, ⊤) from e.hom.app ⊤ (s j)))) = ⊤)
  (hspanT : Ideal.span (Set.range (fun a => (show Γ(X, ⊤) from e.hom.app ⊤ (t a)))) = ⊤)

include e hspanS hspanT in
/-- An actual line frame and actual section linear combinations give the
native projective triangle; no equality of projective maps is a premise. -/
theorem framed_triangle
    (hrel : ∀ j : Fin 14, s j = ∑ a : Fin 5,
      baseRingHom f (embeddingFourteen k (Pi.single a 1) j) • t a) :
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht f ≫ fixedLinearEmbedding k =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f := by
  rw [toProjectiveSpaceOver_framed t ht e f hspanT,
    toProjectiveSpaceOver_framed s hs e f hspanS]
  apply functions_triangle k f _ hspanS _ hspanT
  intro j
  have h := congrArg (fun v => e.hom.app ⊤ v) (hrel j)
  simpa only [map_sum, Scheme.Modules.Hom.app_smul, smul_eq_mul] using h

end FramedTriangle

end M9Native.LagrangianKernelProjectiveComparison
