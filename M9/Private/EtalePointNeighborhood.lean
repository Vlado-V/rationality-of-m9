module

public import M9.AffinePointLifting
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Actual field-valued points in a principal open image of an étale map

The scheme open-mapping theorem and weak Nullstellensatz are combined without
assuming any comparison between scheme points and rational points.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.EtalePointNeighborhood

open AlgebraicGeometry CategoryTheory

universe u

variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

/-- The actual maximal-prime spectrum point defined by an actual field-valued point. -/
def pointPrime (p : R →ₐ[K] K) : PrimeSpectrum R :=
  ⟨RingHom.ker p.toRingHom,(AffinePointLifting.point_kernel_isMaximal p).isPrime⟩

@[simp] theorem comap_pointPrime (φ : R →ₐ[K] S) (ψ : S →ₐ[K] K) :
    PrimeSpectrum.comap φ.toRingHom (pointPrime ψ) = pointPrime (ψ.comp φ) := by
  ext r
  rfl

/-- The native scheme theorem gives the literal open map on prime spectra. -/
theorem isOpenMap_comap_of_etale (φ : R →ₐ[K] S) (hφ : RingHom.Etale φ.toRingHom) :
    IsOpenMap (PrimeSpectrum.comap φ.toRingHom) := by
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hφ
  exact f.isOpenMap

/-- A genuine principal open around any actual image point consists of actual lifted points. -/
theorem exists_principal_open_point_lifts [IsAlgClosed K] [Algebra.FiniteType K S]
    (φ : R →ₐ[K] S) (hφ : RingHom.Etale φ.toRingHom) (ψ₀ : S →ₐ[K] K) :
    ∃ f : R, ψ₀ (φ f) ≠ 0 ∧ ∀ p : R →ₐ[K] K, p f ≠ 0 →
      ∃ ψ : S →ₐ[K] K, ψ.comp φ = p := by
  let U : Set (PrimeSpectrum R) := Set.range (PrimeSpectrum.comap φ.toRingHom)
  have hU : IsOpen U := by
    simpa only [Set.image_univ] using (isOpenMap_comap_of_etale φ hφ) Set.univ isOpen_univ
  have hpoint : pointPrime (ψ₀.comp φ) ∈ U := by
    exact ⟨pointPrime ψ₀,comap_pointPrime φ ψ₀⟩
  obtain ⟨_,⟨f,rfl⟩,hpf,hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU _ hpoint
  refine ⟨f,?_,?_⟩
  · exact (PrimeSpectrum.mem_basicOpen f (pointPrime (ψ₀.comp φ))).mp hpf
  · intro p hp
    have hp' : pointPrime p ∈ PrimeSpectrum.basicOpen f := hp
    obtain ⟨q,hq⟩ := hfU hp'
    let : q.asIdeal.IsPrime := q.isPrime
    apply AffinePointLifting.exists_point_lift φ p q.asIdeal
    exact congrArg PrimeSpectrum.asIdeal hq

end M9.EtalePointNeighborhood
