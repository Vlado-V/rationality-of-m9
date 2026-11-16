module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! Actual extension of a derivation to a fraction field, using the
universal property of localization in the square-zero extension. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.FractionDerivation

variable {K R L : Type*} [CommRing K] [CommRing R] [IsDomain R] [Field L]
  [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L] [IsFractionRing R L]

/-- The dual-number lift is the original ring map together with the actual derivative. -/
def dualMap (D : Derivation K R R) : R →+* TrivSqZeroExt L L where
  toFun r := ⟨algebraMap R L r,algebraMap R L (D r)⟩
  map_one' := by ext <;> simp [Derivation.map_one_eq_zero]
  map_zero' := by ext <;> simp
  map_add' r s := by ext <;> simp
  map_mul' r s := by
    ext
    · simp
    · simp [TrivSqZeroExt.snd_mul,Derivation.leibniz,mul_comm]

theorem dualMap_units (D : Derivation K R R) (r : nonZeroDivisors R) :
    IsUnit (dualMap (L := L) D r) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  simpa [dualMap] using
    (IsFractionRing.injective R L).ne (nonZeroDivisors.ne_zero r.property)

def dualLift (D : Derivation K R R) : L →+* TrivSqZeroExt L L :=
  IsLocalization.lift (M := nonZeroDivisors R) (dualMap_units D)

@[simp] theorem dualLift_algebraMap (D : Derivation K R R) (r : R) :
    dualLift D (algebraMap R L r) = dualMap D r :=
  IsLocalization.lift_eq (dualMap_units D) r

theorem dualLift_fst (D : Derivation K R R) (z : L) : (dualLift D z).fst = z := by
  have heq : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (dualLift D) = RingHom.id L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    simp [dualMap]
  exact DFunLike.congr_fun heq z

theorem dualLift_constant (D : Derivation K R R) (c : K) :
    dualLift D (algebraMap K L c) = algebraMap K (TrivSqZeroExt L L) c := by
  rw [IsScalarTower.algebraMap_apply K R L,dualLift_algebraMap]
  ext
  · change algebraMap R L (algebraMap K R c) = algebraMap K L c
    exact (IsScalarTower.algebraMap_apply K R L c).symm
  · simp [dualMap,TrivSqZeroExt.algebraMap_eq_inl']

/-- The derivative on the actual fraction field, with no arbitrary extension data. -/
def extend (D : Derivation K R R) : Derivation K L L where
  toFun z := (dualLift D z).snd
  map_add' z w := by simp
  map_smul' c z := by
    rw [Algebra.smul_def,map_mul,dualLift_constant]
    simp [TrivSqZeroExt.algebraMap_eq_inl',Algebra.smul_def]
  map_one_eq_zero' := by simp
  leibniz' z w := by
    change (dualLift D (z * w)).snd = z * (dualLift D w).snd + w * (dualLift D z).snd
    simp [TrivSqZeroExt.snd_mul,dualLift_fst,mul_comm,add_comm]

@[simp] theorem extend_algebraMap (D : Derivation K R R) (r : R) :
    extend D (algebraMap R L r) = algebraMap R L (D r) := by
  change (dualLift D (algebraMap R L r)).snd = _
  rw [dualLift_algebraMap]
  rfl

end M9Native.FractionDerivation
