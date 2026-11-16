module

public import M9StacksIntegration.LagrangianPluckerClosed

/-! Actual determinant-line sections of quotient presentations, with their
literal native minor coordinates. These are used to construct the universal
primitive Plucker line quotient rather than assuming a tautological one. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
universe u
namespace M9Native.LagrangianDeterminantSections
open M9Native.LagrangianMatrixChart
open M9Native.LagrangianGrassmannian

section Ring
variable (R : Type u) [CommRing R]

abbrev Three := Fin 3 → R
abbrev Top := ⋀[R]^3 (Three R)

def volume : Top R := exteriorPower.ιMulti R 3 (Pi.basisFun R (Fin 3))

def topCoordinate : Top R →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (Pi.basisFun R (Fin 3)).det

@[simp] theorem topCoordinate_ιMulti (v : Fin 3 → Three R) :
    topCoordinate R (exteriorPower.ιMulti R 3 v)=(Pi.basisFun R (Fin 3)).det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

@[simp] theorem topCoordinate_volume : topCoordinate R (volume R)=1 := by
  rw [volume,topCoordinate_ιMulti,Module.Basis.det_self]

/-- The determinant formula holds in the actual top exterior power over
an arbitrary commutative ring. -/
theorem ιMulti_eq_det_smul (v : Fin 3 → Three R) :
    exteriorPower.ιMulti R 3 v=(Pi.basisFun R (Fin 3)).det v • volume R := by
  have h : exteriorPower.ιMulti R 3 (M:=Three R)=
      ((Pi.basisFun R (Fin 3)).det).smulRight (volume R) := by
    apply (Pi.basisFun R (Fin 3)).ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change exteriorPower.ιMulti R 3 ((Pi.basisFun R (Fin 3)) ∘ σ)=
      ((Pi.basisFun R (Fin 3)).det).smulRight (volume R) ((Pi.basisFun R (Fin 3)) ∘ σ)
    have hdet : Matrix.detRowAlternating (Pi.basisFun R (Fin 3))=1 := by
      change Matrix.det (fun a b : Fin 3 => (Pi.basisFun R (Fin 3)) a b)=(1:R)
      have hm : (fun a b : Fin 3 => (Pi.basisFun R (Fin 3)) a b)=(1 : Matrix (Fin 3) (Fin 3) R) := by
        ext a b
        simp [Pi.basisFun_apply,Matrix.one_apply,Pi.single_apply,eq_comm]
      rw [hm,Matrix.det_one]
    simp [AlternatingMap.map_perm,volume,hdet]
  exact DFunLike.congr_fun h v

/-- The literal determinant-coordinate equivalence for a free rank-three module. -/
def topEquiv : Top R ≃ₗ[R] R := by
  refine LinearEquiv.ofLinearMap (topCoordinate R) ((LinearMap.id : R →ₗ[R] R).smulRight (volume R)) ?_ ?_
  · ext
    simp [topCoordinate_volume]
  · apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change topCoordinate R (exteriorPower.ιMulti R 3 v) • volume R=exteriorPower.ιMulti R 3 v
    rw [topCoordinate_ιMulti]
    exact (ιMulti_eq_det_smul R v).symm

@[simp] theorem topEquiv_apply (w : Top R) : topEquiv R w=topCoordinate R w := rfl

end Ring

section Sheaves
variable (X : Scheme.{u})

/-- The actual determinant coordinates on the actual exterior sheaf of free rank three. -/
def freeDeterminantCoordinates :
    Γ(Scheme.Modules.exteriorPower (freeOn X 3) 3,⊤) ≃ₗ[Γ(X,⊤)] Γ(X,⊤) :=
  (freeExteriorSectionsEquiv X 3 3).symm.trans (topEquiv Γ(X,⊤))

/-- The actual ordered standard third wedge of the six free sheaf sections. -/
def standardWedge (c : Fin 3 ↪ Fin 6) :
    Γ(Scheme.Modules.exteriorPower (freeOn X 6) 3,⊤) :=
  M9Native.ExteriorEvaluation.sectionComparison (freeOn X 6) 3 ⊤
    (exteriorPower.ιMulti Γ(X,⊤) 3 (fun i => freeBasisSection X 6 (c i)))

/-- The actual determinant section associated with a native quotient minor. -/
def minorSection {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (c : Fin 3 ↪ Fin 6) :
    Γ(Scheme.Modules.exteriorPower Q 3,⊤) :=
  (exteriorPowerMap X q 3).app ⊤ (standardWedge X c)

/-- This determinant section is literally the wedge of the quotient's basis images. -/
theorem minorSection_eq_wedge {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (c : Fin 3 ↪ Fin 6) :
    minorSection X q c=M9Native.ExteriorEvaluation.sectionComparison Q 3 ⊤
      (exteriorPower.ιMulti Γ(X,⊤) 3 (fun i => q.app ⊤ (freeBasisSection X 6 (c i)))) := by
  rw [minorSection,standardWedge,exteriorPowerMap_eq_native]
  exact M9Native.ExteriorEvaluation.sectionComparison_map_ιMulti q 3 ⊤
    (fun i => freeBasisSection X 6 (c i))

/-- Actual changes of quotient target transport all determinant sections. -/
theorem minorSection_postcomp {Q Q' : X.Modules} (q : freeOn X 6 ⟶ Q) (e : Q ⟶ Q')
    (c : Fin 3 ↪ Fin 6) :
    (exteriorPowerMap X e 3).app ⊤ (minorSection X q c)=minorSection X (q ≫ e) c := by
  rw [minorSection_eq_wedge,minorSection_eq_wedge,exteriorPowerMap_eq_native]
  exact M9Native.ExteriorEvaluation.sectionComparison_map_ιMulti e 3 ⊤
    (fun i => q.app ⊤ (freeBasisSection X 6 (c i)))

theorem freeExteriorSectionsEquiv_symm_comparison (n r : ℕ)
    (v : Fin n → Γ(freeOn X r,⊤)) :
    (freeExteriorSectionsEquiv X n r).symm
        (M9Native.ExteriorEvaluation.sectionComparison (freeOn X r) n ⊤
          (exteriorPower.ιMulti Γ(X,⊤) n v))=
      exteriorPower.ιMulti Γ(X,⊤) n (fun i => freeSectionCoordinates X r (v i)) := by
  apply (freeExteriorSectionsEquiv X n r).injective
  rw [LinearEquiv.apply_symm_apply,freeExteriorSectionsEquiv_ιMulti]
  simp only [LinearEquiv.symm_apply_apply]

/-- The actual determinant section has the literal native maximal-minor value. -/
theorem minorSection_freeCoordinates (q : freeOn X 6 ⟶ freeOn X 3) (c : Fin 3 ↪ Fin 6) :
    freeDeterminantCoordinates X (minorSection X q c)=
      Matrix.det ((Stacks.FreeSheafMatrix.toMatrix q).submatrix id c) := by
  rw [minorSection_eq_wedge]
  change topEquiv Γ(X,⊤) ((freeExteriorSectionsEquiv X 3 3).symm _)=_
  rw [freeExteriorSectionsEquiv_symm_comparison,topEquiv_apply,topCoordinate_ιMulti,Module.Basis.det_apply]
  congr 1
  ext i j
  change freeSectionCoordinates X 3 (q.app ⊤ (freeBasisSection X 6 (c j))) i=_
  exact freeCoordinates_map_basis q i (c j)

end Sheaves
end M9Native.LagrangianDeterminantSections
