module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian

/-! Finite parameter bases from the actual universal-equation strata.
An immersed Noetherian stratum of a finite-type coefficient ring is
of finite presentation over the coefficient base. Its field base changes
are Noetherian, so every open restriction remains quasi-compact. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.EquationParameterGeometry
variable (A R : Type u) [CommRing A] [IsNoetherianRing A] [CommRing R]
variable [Algebra A R] [Algebra.FiniteType A R]
variable {T : Scheme.{u}} (j : T ⟶ Spec (.of R)) [IsImmersion j] [IsNoetherian T]

abbrev projection : T ⟶ Spec (.of A) := j ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))

theorem projection_geometry :
    LocallyOfFiniteType (projection A R j) ∧ QuasiCompact (projection A R j) ∧
      LocallyOfFinitePresentation (projection A R j) ∧ IsSeparated (projection A R j) := by
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType (projection A R j) := inferInstance
  refine ⟨inferInstance, inferInstance, ?_, inferInstance⟩
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

variable (K : Type u) [Field K] [Algebra A K]

abbrev fieldParameter :=
  pullback (projection A R j) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

abbrev fieldProjection : fieldParameter A R j K ⟶ Spec (.of K) :=
  pullback.snd (projection A R j) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

theorem fieldParameter_isNoetherian : IsNoetherian (fieldParameter A R j K) := by
  obtain ⟨hft, hqc, hfp, hsep⟩ := projection_geometry A R j
  let := hft
  let := hqc
  let : IsLocallyNoetherian (fieldParameter A R j K) :=
    LocallyOfFiniteType.isLocallyNoetherian (fieldProjection A R j K)
  let : CompactSpace (fieldParameter A R j K) :=
    QuasiCompact.compactSpace_of_compactSpace (fieldProjection A R j K)
  exact ⟨⟩

theorem open_fieldParameter_geometry (U : (fieldParameter A R j K).Opens) :
    LocallyOfFinitePresentation (U.ι ≫ fieldProjection A R j K) ∧
      QuasiCompact (U.ι ≫ fieldProjection A R j K) ∧
        IsSeparated (U.ι ≫ fieldProjection A R j K) := by
  obtain ⟨hft, hqc, hfp, hsep⟩ := projection_geometry A R j
  let := hfp
  let := hsep
  let := fieldParameter_isNoetherian A R j K
  refine ⟨inferInstance, ?_, inferInstance⟩
  infer_instance

end M9Native.EquationParameterGeometry
end
