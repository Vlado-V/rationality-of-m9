module

public import M9StacksIntegration.NativeProjectiveVector
public import M9StacksIntegration.PrimitiveGaussGroupScheme
public import M9StacksIntegration.PrimitiveGaussOrbitVector

/-! The genuine fixed-rho orbit morphism from the native symplectic group scheme.
Its values on every test scheme are the actual ring-valued exterior representation. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveRhoOrbit

open PrimitiveGaussOrbitVector

abbrev base : Scheme := Spec (.of ℂ)
abbrev groupObject : Over base := Sp6GroupScheme.obj base
abbrev groupSpace : Scheme := groupObject.left

def coefficient (T : Over base) : ℂ →+* Γ(T.left, ⊤) :=
  T.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom

def vector (T : Over base) (g : T ⟶ groupObject) : Fin 14 → Γ(T.left, ⊤) :=
  PrimitiveRingCoordinates.primitiveMatrix Γ(T.left, ⊤) (coefficient T)
    (Sp6GroupScheme.pointsMulEquiv base T g) *ᵥ (coefficient T ∘ rhoCoordinates)

theorem rhoCoordinates_ne_zero : rhoCoordinates ≠ 0 := by
  intro h
  apply M9.PrimitiveStabilizer.rho_ne_zero ℂ
  have hz : M9.PrimitiveRadicalScheme.primitiveCoordinates
      (0 : M9.ExteriorPrimitive.Primitive ℂ) = (0 : Fin 14 → ℂ) :=
    M9.PrimitiveRadicalScheme.primitiveCoordinates.map_zero
  exact M9.PrimitiveRadicalScheme.primitiveCoordinates.injective (h.trans hz.symm)

theorem constant_span (R : Type) [CommRing R] (f : ℂ →+* R) :
    Ideal.span (Set.range (f ∘ rhoCoordinates)) = ⊤ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp rhoCoordinates_ne_zero
  have hm : f (rhoCoordinates i) ∈ Ideal.span (Set.range (f ∘ rhoCoordinates)) :=
    Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.eq_top_of_isUnit_mem _ hm ((isUnit_iff_ne_zero.mpr hi).map f)

theorem vector_span (T : Over base) (g : T ⟶ groupObject) :
    Ideal.span (Set.range (vector T g)) = ⊤ := by
  rw [vector, NativeProjectiveVector.span_mulVec_eq _
    (PrimitiveRingCoordinates.primitiveMatrix Γ(T.left, ⊤) (coefficient T)
      (Sp6GroupScheme.pointsMulEquiv base T g)⁻¹)
    (by rw [← PrimitiveRingCoordinates.primitiveMatrix_mul, inv_mul_cancel,
      PrimitiveRingCoordinates.primitiveMatrix_one])]
  exact constant_span _ _

/-- The universal fixed-rho orbit morphism to the literal native polynomial Proj. -/
def orbitMorphism : groupSpace ⟶ M9.ProjectiveGeometry.ProjectiveSpace.projectiveSpace 13 :=
  NativeProjectiveVector.onScheme groupSpace (coefficient groupObject)
    (vector groupObject (𝟙 groupObject)) (vector_span _ _)

theorem coefficient_natural (T : Over base) (g : T ⟶ groupObject) :
    g.left.appTop.hom.comp (coefficient groupObject) = coefficient T := by
  have h := congrArg (fun f : T.left ⟶ base =>
    f.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom) g.w
  simpa only [coefficient, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_assoc] using h

theorem vector_natural (T : Over base) (g : T ⟶ groupObject) :
    g.left.appTop.hom ∘ vector groupObject (𝟙 groupObject) = vector T g := by
  have hc := coefficient_natural T g
  have hg : Sp6GroupScheme.pointsMulEquiv base T g =
      LagrangianTransitivity.mapSymplectic Γ(groupSpace, ⊤) g.left.appTop.hom
        (Sp6GroupScheme.pointsMulEquiv base groupObject (𝟙 groupObject)) := by
    calc
      _ = Sp6GroupScheme.mapMatrix g.left.appTop.hom
          (Sp6GroupScheme.pointsMulEquiv base groupObject (𝟙 groupObject)) := by
        simpa only [Category.comp_id] using
          (Sp6GroupScheme.pointsMulEquiv_natural g (𝟙 groupObject))
      _ = _ := by
        apply Subtype.ext
        rfl
  have hM := PrimitiveRingCoordinates.primitiveMatrix_map Γ(groupSpace, ⊤)
    (coefficient groupObject) g.left.appTop.hom
    (Sp6GroupScheme.pointsMulEquiv base groupObject (𝟙 groupObject))
  rw [hc, ← hg] at hM
  have hr : g.left.appTop.hom ∘ (coefficient groupObject ∘ rhoCoordinates) =
      coefficient T ∘ rhoCoordinates := by
    funext i
    exact RingHom.congr_fun hc (rhoCoordinates i)
  funext i
  change g.left.appTop.hom ((PrimitiveRingCoordinates.primitiveMatrix Γ(groupSpace, ⊤)
    (coefficient groupObject) _ *ᵥ (coefficient groupObject ∘ rhoCoordinates)) i) = _
  rw [RingHom.map_mulVec, ← hM, hr]
  rfl

/-- Every test-scheme pullback is the actual primitive action on rho. -/
theorem orbitMorphism_pullback (T : Over base) (g : T ⟶ groupObject) :
    g.left ≫ orbitMorphism = NativeProjectiveVector.onScheme T.left (coefficient T)
      (vector T g) (vector_span T g) := by
  change g.left ≫ NativeProjectiveVector.onScheme groupSpace (coefficient groupObject)
    (vector groupObject (𝟙 groupObject)) (vector_span _ _) = _
  have h := NativeProjectiveVector.onScheme_map g.left (coefficient groupObject)
    (vector groupObject (𝟙 groupObject)) (vector_span _ _)
  simpa only [coefficient_natural T g, vector_natural T g] using h

open PrimitiveGaussCoordinates PrimitiveGaussGroupScheme

theorem gauss_coefficient : coefficient sourceOver =
    (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom.comp (algebraMap ℂ (sourceRing ℂ)) := by
  ext c
  exact NativeProjectiveVector.spec_appTop (algebraMap ℂ (sourceRing ℂ)) c

theorem gauss_vector : vector sourceOver gaussFamily =
    (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom ∘ orbitVector := by
  rw [vector, pointsMulEquiv_gaussFamily, gauss_coefficient]
  have hM := PrimitiveRingCoordinates.primitiveMatrix_map (sourceRing ℂ)
    (algebraMap ℂ (sourceRing ℂ)) (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom
    (PrimitiveGaussFamily.family ℂ)
  have hg : globalFamily = LagrangianTransitivity.mapSymplectic (sourceRing ℂ)
      (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom (PrimitiveGaussFamily.family ℂ) := by
    apply Subtype.ext
    rfl
  rw [hg]
  change PrimitiveRingCoordinates.primitiveMatrix Γ(Spec (.of (sourceRing ℂ)), ⊤)
    ((Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom.comp (algebraMap ℂ (sourceRing ℂ)))
    (LagrangianTransitivity.mapSymplectic (sourceRing ℂ)
      (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom (PrimitiveGaussFamily.family ℂ)) *ᵥ
    (((Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom.comp
      (algebraMap ℂ (sourceRing ℂ))) ∘ rhoCoordinates) = _
  rw [hM]
  funext i
  exact (RingHom.map_mulVec (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom
    (PrimitiveRingCoordinates.primitiveMatrix (sourceRing ℂ) (algebraMap ℂ (sourceRing ℂ))
      (PrimitiveGaussFamily.family ℂ))
    (algebraMap ℂ (sourceRing ℂ) ∘ rhoCoordinates) i).symm

theorem orbitVector_span : Ideal.span (Set.range orbitVector) = ⊤ := by
  rw [orbitVector, NativeProjectiveVector.span_mulVec_eq _
    (PrimitiveRingCoordinates.primitiveMatrix (sourceRing ℂ) (algebraMap ℂ (sourceRing ℂ))
      (PrimitiveGaussFamily.family ℂ)⁻¹)
    (by rw [← PrimitiveRingCoordinates.primitiveMatrix_mul, inv_mul_cancel,
      PrimitiveRingCoordinates.primitiveMatrix_one])]
  exact constant_span _ _

/-- Pulling back the actual group-scheme orbit gives the native morphism of the literal
Gauss orbit vector over its source ring. -/
theorem gauss_pullback : gaussFamily.left ≫ orbitMorphism =
    NativeProjectiveVector.point (algebraMap ℂ (sourceRing ℂ)) orbitVector orbitVector_span := by
  rw [orbitMorphism_pullback, NativeProjectiveVector.point_eq_onScheme]
  simp only [gauss_coefficient, gauss_vector]
  rfl

end M9Native.PrimitiveRhoOrbit
