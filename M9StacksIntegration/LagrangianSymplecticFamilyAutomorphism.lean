module

public import M9StacksIntegration.LagrangianVariableSymplecticAction

/-! Actual variable symplectic automorphisms of the original LG after
arbitrary base change. The coefficient matrix is pulled from the genuine
base scheme, so its coefficients are unchanged by the constructed map.
The inverse follows from the native quotient classifier's proved action
law, without a supplied scheme-action or quotient-covariance premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
universe u

namespace M9Native.LagrangianSymplecticFamilyAutomorphism

open LagrangianGrassmannian LagrangianTransitivity
open LagrangianVariableSymplecticAction

/-- Actual coefficient change, bundled as a group homomorphism. -/
def coefficientGroupHom {R A : Type u} [CommRing R] [CommRing A] (ρ : R →+* A) :
    Matrix.symplecticGroup (Fin 3) R →* Matrix.symplecticGroup (Fin 3) A where
  toFun := mapSymplectic R ρ
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one ρ (map_zero _) (map_one _)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.map_mul

variable (K : Type u) [Field K] {S : Scheme.{u}} (s : S ⟶ Spec (.of K))

abbrev family : Scheme.{u} := pullback (projection K) s
abbrev toLG : family K s ⟶ space K := pullback.fst (projection K) s
abbrev toBase : family K s ⟶ S := pullback.snd (projection K) s

/-- Pull the original variable matrix from the actual base scheme. -/
def baseMatrix (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    Matrix.symplecticGroup (Fin 3) Γ(family K s, ⊤) :=
  coefficientGroupHom (toBase K s).appTop.hom g

/-- The actual base-preserving native family morphism. -/
def familyMap (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    family K s ⟶ family K s :=
  pullback.lift (actPoint K (toLG K s) (baseMatrix K s g)) (toBase K s)
    (by rw [actPoint_projection]; exact pullback.condition)

@[reassoc] theorem familyMap_toLG (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    familyMap K s g ≫ toLG K s = actPoint K (toLG K s) (baseMatrix K s g) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem familyMap_toBase
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    familyMap K s g ≫ toBase K s = toBase K s :=
  pullback.lift_snd _ _ _

/-- Every original coefficient pulled from the base is unchanged by
this actual family map, including on nonreduced test schemes. -/
theorem familyMap_pulledBaseMatrix
    (g h : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    mapSymplectic Γ(family K s, ⊤) (familyMap K s g).appTop.hom (baseMatrix K s h) =
      baseMatrix K s h := by
  apply Subtype.ext
  ext i j
  change (familyMap K s g).appTop ((toBase K s).appTop ((h : Matrix _ _ Γ(S, ⊤)) i j)) =
    (toBase K s).appTop ((h : Matrix _ _ Γ(S, ⊤)) i j)
  change ((familyMap K s g) ≫ toBase K s).appTop ((h : Matrix _ _ Γ(S, ⊤)) i j) = _
  rw [familyMap_toBase]

theorem familyMap_one : familyMap K s 1 = 𝟙 (family K s) := by
  apply pullback.hom_ext
  · rw [familyMap_toLG,Category.id_comp]
    change actPoint K (toLG K s) ((coefficientGroupHom (toBase K s).appTop.hom) 1) = _
    rw [map_one,actPoint_one]
  · rw [familyMap_toBase,Category.id_comp]

/-- Multiplication of the original coefficient matrices is the actual
right action on the base-changed native LG scheme. -/
theorem familyMap_mul (g h : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    familyMap K s g ≫ familyMap K s h = familyMap K s (g*h) := by
  apply pullback.hom_ext
  · rw [Category.assoc,familyMap_toLG,actPoint_natural,familyMap_toLG,
      familyMap_pulledBaseMatrix,actPoint_mul,familyMap_toLG]
    congr 1
    exact ((coefficientGroupHom (toBase K s).appTop.hom).map_mul g h).symm
  · rw [Category.assoc,familyMap_toBase,familyMap_toBase,familyMap_toBase]

/-- The genuine family automorphism with its actual inverse. -/
def automorphism (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) : family K s ≅ family K s where
  hom := familyMap K s g
  inv := familyMap K s g⁻¹
  hom_inv_id := by rw [familyMap_mul,mul_inv_cancel,familyMap_one]
  inv_hom_id := by rw [familyMap_mul,inv_mul_cancel,familyMap_one]

@[reassoc] theorem automorphism_hom_toLG (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    (automorphism K s g).hom ≫ toLG K s = actPoint K (toLG K s) (baseMatrix K s g) :=
  familyMap_toLG K s g

@[reassoc (attr := simp)] theorem automorphism_hom_toBase
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    (automorphism K s g).hom ≫ toBase K s = toBase K s :=
  familyMap_toBase K s g

@[reassoc] theorem automorphism_inv_toLG (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    (automorphism K s g).inv ≫ toLG K s = actPoint K (toLG K s) (baseMatrix K s g⁻¹) :=
  familyMap_toLG K s g⁻¹

@[reassoc (attr := simp)] theorem automorphism_inv_toBase
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    (automorphism K s g).inv ≫ toBase K s = toBase K s :=
  familyMap_toBase K s g⁻¹

/-- The same constructed isomorphism in the actual category over its
original base, retaining the base projection. -/
def automorphismOver (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    Over.mk (toBase K s) ≅ Over.mk (toBase K s) :=
  Over.isoMk (automorphism K s g) (automorphism_hom_toBase K s g)

end M9Native.LagrangianSymplecticFamilyAutomorphism
