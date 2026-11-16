module

public import M9StacksIntegration.CurvePowerTopPower

/-!
# From actual diagonal intersection identities to the reduced pair algebra

These are integral identities in an arbitrary commutative ring. They
separate the genuine geometric inputs—point square, point-diagonal
incidence, diagonal square, and the modified small diagonal—from the
formal reduced-pair identities used in the root calculation.
-/

@[expose] public section

namespace M9Native.CurvePowerDiagonalAlgebra

variable {R : Type*} [CommRing R]

def reducedDiagonal (p q d : R) : R := d - p - q

def modifiedTriple (p q r d e f : R) : R :=
  e * f - e * q - f * p - d * r + p * q + p * r + q * r

theorem point_mul_reducedDiagonal_left (p q d : R)
    (hp : p ^ 2 = 0) (hpd : p * d = p * q) :
    p * reducedDiagonal p q d = 0 := by
  unfold reducedDiagonal
  linear_combination hpd - hp

theorem point_mul_reducedDiagonal_right (p q d : R)
    (hq : q ^ 2 = 0) (hqd : q * d = p * q) :
    q * reducedDiagonal p q d = 0 := by
  unfold reducedDiagonal
  linear_combination hqd - hq

theorem reducedDiagonal_sq (t p q d : R) (hp : p ^ 2 = 0) (hq : q ^ 2 = 0)
    (hpd : p * d = p * q) (hqd : q * d = p * q) (hd : d ^ 2 = t * p * q) :
    reducedDiagonal p q d ^ 2 = (t - 2) * p * q := by
  unfold reducedDiagonal
  linear_combination hd - 2 * hpd - 2 * hqd + hp + hq

theorem reducedDiagonal_sq_genus_nine (p q d : R)
    (hp : p ^ 2 = 0) (hq : q ^ 2 = 0) (hpd : p * d = p * q)
    (hqd : q * d = p * q) (hd : d ^ 2 = -16 * p * q) :
    reducedDiagonal p q d ^ 2 = -18 * p * q := by
  have h := reducedDiagonal_sq (-16) p q d hp hq hpd hqd hd
  norm_num at h
  linear_combination h

theorem reducedDiagonal_cross (p q r d e f : R) (hr : r ^ 2 = 0)
    (hre : r * e = p * r) (hrf : r * f = q * r)
    (htriple : modifiedTriple p q r d e f = 0) :
    reducedDiagonal p r e * reducedDiagonal q r f = r * reducedDiagonal p q d := by
  unfold reducedDiagonal modifiedTriple at *
  linear_combination htriple - hre - hrf + hr

end M9Native.CurvePowerDiagonalAlgebra
