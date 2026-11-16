module

public import M9StacksIntegration.ParameterClosedResidueField

/-!
# The structural residue point as the genuine scalar isomorphism

At a closed point of a finite-type chart over an algebraically closed field,
the actual residue spectrum is isomorphic to the original base spectrum.
Thus deformation theory may retain coefficients in the actual residue field
while using this genuine affine-open Artin base in the original chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.ParameterStructuralResidue

/-- The canonical field-spectrum point is precisely the spectrum of the
inverse of its original structural residue-field isomorphism. -/
theorem fieldPoint_eq_specMap {K : Type u} [Field K] (z : Spec (.of K)) :
    (Spec (.of K)).fromSpecResidueField z =
      Spec.map (Scheme.Spec.residueFieldIsoOfField z).inv := by
  have := z.isPrime
  rw [Scheme.Spec.residueFieldIsoOfField_eq]
  change _ = Spec.map
    ((Ideal.algEquivResidueFieldOfField z.asIdeal).toRingEquiv.toCommRingCatIso.hom ≫
      (Scheme.Spec.residueFieldIso (.of K) z).inv)
  have h : (Ideal.algEquivResidueFieldOfField z.asIdeal).toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap K z.asIdeal.ResidueField) := by
    ext a
    simp [Ideal.algEquivResidueFieldOfField_apply]
  rw [h, Spec.map_comp]
  exact (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of K) z).symm

variable (K : Type u) [Field K] [IsAlgClosed K] {T : Scheme.{u}}
  (s : T ⟶ Spec (.of K)) [LocallyOfFiniteType s]
  (x : T) (hx : IsClosed ({x} : Set T))

/-- The original structural point is the spectrum of the actual structural
residue isomorphism; no field identification is selected independently. -/
theorem structuralPoint_eq_specMap :
    T.fromSpecResidueField x ≫ s =
      Spec.map (ParameterClosedResidueField.residueIso K s x hx).hom := by
  rw [← s.SpecMap_residueFieldMap_fromSpecResidueField x, fieldPoint_eq_specMap,
    ← Spec.map_comp]
  rfl

include hx in
/-- The original structural map of residue spectra is an actual isomorphism. -/
theorem structuralPoint_isIso : IsIso (T.fromSpecResidueField x ≫ s) := by
  rw [structuralPoint_eq_specMap K s x hx]
  infer_instance

include hx in
/-- It is therefore a genuine open Artin base for native atlas lifting. -/
theorem structuralPoint_isOpenImmersion :
    IsOpenImmersion (T.fromSpecResidueField x ≫ s) := by
  have := structuralPoint_isIso K s x hx
  infer_instance

include hx in
/-- The exact field-valued point hypotheses of native atlas deformation
theory follow for this actual residue point. -/
theorem structuralPoint_finite :
    LocallyOfFiniteType (T.fromSpecResidueField x ≫ s) ∧
      QuasiCompact (T.fromSpecResidueField x ≫ s) := by
  have := structuralPoint_isIso K s x hx
  exact ⟨inferInstance, inferInstance⟩

end M9Native.ParameterStructuralResidue
