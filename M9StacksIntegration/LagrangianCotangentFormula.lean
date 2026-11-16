module

public import M9StacksIntegration.LagrangianPluckerFirstJet
public import Mathlib.RingTheory.Derivation.Basic

/-!
# The intrinsic cotangent bilinear form of an isotropic quotient

For the dual of the actual quotient, the six coefficient functions give
an isotropic linear map `c`. The formula
`Σ (cα)_e d(cβ)_f - (cα)_f d(cβ)_e`
is linear in both arguments: the apparent Leibniz error is exactly the
actual symplectic pairing, which is zero. Its symmetry follows by
differentiating that same zero pairing. This constructs the cotangent
map intrinsically and avoids assuming overlap compatibility.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

universe u v w

namespace M9Native.LagrangianCotangentFormula

variable {k : Type u} {R : Type v} [CommRing k] [CommRing R] [Algebra k R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module k M]
variable {Q : Type*} [AddCommGroup Q] [Module R Q]

/-- The literal standard symplectic pairing in the native six-coordinate order. -/
def symplecticPair (x y : Fin 6 → R) : R :=
  ∑ i : Fin 3, (x (i.castAdd 3) * y (Fin.natAdd 3 i) -
    x (Fin.natAdd 3 i) * y (i.castAdd 3))

/-- The intrinsic differential formula, before using isotropy. -/
def differentialPair (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R)) (α β : Q) : M :=
  ∑ i : Fin 3,
    (c α (i.castAdd 3) • d (c β (Fin.natAdd 3 i)) -
      c α (Fin.natAdd 3 i) • d (c β (i.castAdd 3)))

theorem differentialPair_add_left (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (α α' β : Q) : differentialPair d c (α+α') β=differentialPair d c α β+differentialPair d c α' β := by
  simp only [differentialPair,map_add,Pi.add_apply,add_smul]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  abel

theorem differentialPair_smul_left (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (r : R) (α β : Q) : differentialPair d c (r • α) β=r • differentialPair d c α β := by
  simp [differentialPair,smul_sub,Finset.smul_sum,smul_smul]

theorem differentialPair_add_right (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (α β β' : Q) : differentialPair d c α (β+β')=differentialPair d c α β+differentialPair d c α β' := by
  simp only [differentialPair,map_add,Pi.add_apply,smul_add]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  abel

/-- The entire Leibniz error is the original symplectic pairing. -/
theorem differentialPair_smul_right (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (r : R) (α β : Q) :
    differentialPair d c α (r • β)=r • differentialPair d c α β+
      symplecticPair (c α) (c β) • d r := by
  simp only [differentialPair,symplecticPair,map_smul,Pi.smul_apply,smul_eq_mul,
    Derivation.leibniz,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  module

/-- The antisymmetric part is the differential of the actual
symplectic pairing. -/
theorem differential_symplecticPair (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (α β : Q) :
    d (symplecticPair (c α) (c β))=differentialPair d c α β-differentialPair d c β α := by
  simp only [symplecticPair,differentialPair,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    map_add,map_sub,Derivation.leibniz]
  module

/-- The actual intrinsic symmetric bilinear map attached to the
isotropic coefficient map. Its linearity is proved from the Leibniz rule. -/
def intrinsicBilinear (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (hiso : ∀ α β,symplecticPair (c α) (c β)=0) : Q →ₗ[R] Q →ₗ[R] M where
  toFun α :=
    { toFun := differentialPair d c α
      map_add' β β' := differentialPair_add_right d c α β β'
      map_smul' r β := by
        simpa only [hiso,zero_smul,add_zero,RingHom.id_apply] using
          differentialPair_smul_right d c r α β }
  map_add' α α' := LinearMap.ext (fun β => differentialPair_add_left d c α α' β)
  map_smul' r α := LinearMap.ext (fun β => differentialPair_smul_left d c r α β)

theorem intrinsicBilinear_symmetric (d : Derivation k R M) (c : Q →ₗ[R] (Fin 6 → R))
    (hiso : ∀ α β,symplecticPair (c α) (c β)=0) (α β : Q) :
    intrinsicBilinear d c hiso α β=intrinsicBilinear d c hiso β α := by
  apply sub_eq_zero.mp
  change differentialPair d c α β-differentialPair d c β α=0
  rw [← differential_symplecticPair,hiso,map_zero]

end M9Native.LagrangianCotangentFormula
