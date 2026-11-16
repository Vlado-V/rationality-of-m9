module

public import M9StacksIntegration.SymplecticUnitWitness
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! An arbitrary original independent pair admits a true symplectic
partner of the first vector orthogonal to the second. In particular the
pair itself need not be a symplectic plane. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Module

universe u

namespace M9Native.SymplecticPlanePartner

open LagrangianRing
variable (K : Type u) [Field K]

/-- Independence supplies the two prescribed actual pairing values;
no partner or nonzero pairing is assumed. -/
theorem exists_common_partner (w : Fin 2 → V K) (hw : LinearIndependent K w) :
    ∃ c : V K, omega K (w 0) c = 1 ∧ omega K (w 1) c = 0 := by
  let U : Submodule K (V K) := Submodule.span K (Set.range w)
  let b : Basis (Fin 2) K U := Basis.span hw
  obtain ⟨φ,hφ⟩ := LinearMap.exists_extend (b.coord 0)
  have hbi (i : Fin 2) : ((b i : U) : V K) = w i := Basis.coe_span_apply hw i
  have hvalues (i : Fin 2) : φ (w i) = if i = 0 then 1 else 0 := by
    rw [← hbi]
    have h := LinearMap.congr_fun hφ (b i)
    simpa [Basis.coord_apply,Finsupp.single_apply,eq_comm] using h
  let c : V K := ((omega K).toDual (Sp6VectorTransitivity.omega_nondegenerate K)).symm (-φ)
  have hc (v : V K) : omega K c v = -φ v :=
    LinearMap.BilinForm.apply_toDual_symm_apply (-φ) v
  refine ⟨c,?_,?_⟩
  · rw [omega_swap K (w 0) c,hc,neg_neg]
    simpa using hvalues 0
  · rw [omega_swap K (w 1) c,hc,neg_neg]
    simpa using hvalues 1

/-- The chosen vector is from the proved actual existence theorem. -/
def commonPartner (w : Fin 2 → V K) (hw : LinearIndependent K w) : V K :=
  Classical.choose (exists_common_partner K w hw)

theorem omega_first_commonPartner (w : Fin 2 → V K) (hw : LinearIndependent K w) :
    omega K (w 0) (commonPartner K w hw) = 1 :=
  (Classical.choose_spec (exists_common_partner K w hw)).1

theorem omega_second_commonPartner (w : Fin 2 → V K) (hw : LinearIndependent K w) :
    omega K (w 1) (commonPartner K w hw) = 0 :=
  (Classical.choose_spec (exists_common_partner K w hw)).2

end M9Native.SymplecticPlanePartner
