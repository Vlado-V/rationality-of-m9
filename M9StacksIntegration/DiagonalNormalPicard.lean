module

public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor

/-!
# The actual diagonal divisor and the cotangent line

The categorical conormal of a closed immersion is compared to the ideal
of its actual scheme-theoretic image, using its proved image isomorphism.
Applied to the diagonal, this identifies the actual relative differentials
with the restriction of the diagonal's negative twist.  For a separated
smooth relative curve, Cartier invertibility is derived from the original
diagonal divisor; no normal-line or Picard equality is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace M9Native.DiagonalNormalPicard

/-- The actual image isomorphism compares the two genuine ideal-sheaf
models, before pulling them back along the original closed immersion. -/
theorem nonempty_conormal_iso_pullback_kerIdeal
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Nonempty (Stacks.Conormal.conormalSheaf i ≅
      (Scheme.Modules.pullback i).obj (Stacks.Divisors.negativeTwist' i.ker)) := by
  let : IsIso i.toImage := IsClosedImmersion.isIso_of_ker_eq i i.imageι i.toImage
    i.toImage_imageι (Scheme.IdealSheafData.ker_subschemeι i.ker).symm
  let e : Z ≅ i.ker.subscheme := asIso i.toImage
  let er := (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mapIso e
  have he : i.toLRSHom.toShHom = er.hom ≫ i.ker.subschemeι.toLRSHom.toShHom := by
    change i.toLRSHom.toShHom = (i.toImage ≫ i.ker.subschemeι).toLRSHom.toShHom
    rw [i.toImage_imageι]
  obtain ⟨φ, _⟩ := Stacks.ClosedImmersion.exists_idealSheafIso_hom_comp_ι er
    i.ker.subschemeι.toLRSHom.toShHom i.toLRSHom.toShHom he
  exact ⟨(Stacks.Immersion.conormalSheafSelfIso i).symm ≪≫
    (modulePullback i.toLRSHom.toShHom).mapIso φ.symm⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

omit [IsSeparated f] in
/-- The literal point-graph ideal is the kernel of the original diagonal. -/
theorem diagonalIdeal_eq_ker :
    Stacks.Hilbert.diagonalIdeal f = (pullback.diagonal f).ker := by
  have h : Stacks.Hilbert.pointGraph (Over.mk f) (Over.mk f) (𝟙 _) =
      pullback.diagonal f := rfl
  exact congrArg Scheme.Hom.ker h

/-- The genuine cotangent sheaf equals the negative diagonal line
restricted along the original diagonal morphism. -/
theorem nonempty_differentials_iso_pullback_diagonalNegativeTwist :
    Nonempty (Scheme.Hom.relativeDifferentials f ≅
      (Scheme.Modules.pullback (pullback.diagonal f)).obj
        (Stacks.Divisors.negativeTwist' (Stacks.Hilbert.diagonalIdeal f))) := by
  rw [diagonalIdeal_eq_ker f]
  obtain ⟨e⟩ := nonempty_conormal_iso_pullback_kerIdeal (pullback.diagonal f)
  exact ⟨Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f ≪≫ e⟩

variable [SmoothOfRelativeDimension 1 f]

/-- Actual relative smoothness makes the original diagonal an effective
Cartier divisor, so its restriction makes the actual cotangent invertible. -/
theorem differentials_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Scheme.Hom.relativeDifferentials f) := by
  let := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
  have hN := Stacks.Divisors.isInvertible_negativeTwist_picard
    (Stacks.Hilbert.diagonalIdeal f)
  have hP := Stacks.RingedSpace.modulePullback_isInvertible_of
    (pullback.diagonal f).toLRSHom.toShHom
    (Stacks.Divisors.negativeTwist' (Stacks.Hilbert.diagonalIdeal f)) hN
  obtain ⟨e⟩ := nonempty_differentials_iso_pullback_diagonalNegativeTwist f
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ e.symm

/-- The Picard-class form of the actual cotangent/diagonal comparison. -/
theorem differentials_picardClass :
    letI := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
    Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
      (Scheme.Hom.relativeDifferentials f) (differentials_isInvertible f) =
      Stacks.Picard.schemePullbackClass (pullback.diagonal f)
        (Stacks.Divisors.negativeTwistPicardClass (Stacks.Hilbert.diagonalIdeal f)) := by
  let := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
  have hN := Stacks.Divisors.isInvertible_negativeTwist_picard
    (Stacks.Hilbert.diagonalIdeal f)
  have hP := Stacks.RingedSpace.modulePullback_isInvertible_of
    (pullback.diagonal f).toLRSHom.toShHom
    (Stacks.Divisors.negativeTwist' (Stacks.Hilbert.diagonalIdeal f)) hN
  refine Eq.trans ?_ (Stacks.Picard.pullbackClass_classOf
    (pullback.diagonal f).toLRSHom.toShHom _ hN).symm
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
    (nonempty_differentials_iso_pullback_diagonalNegativeTwist f)

/-- The positive diagonal line restricts to the negative cotangent class. -/
theorem diagonal_picardClass_pullback :
    letI := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
    Stacks.Picard.schemePullbackClass (pullback.diagonal f)
        (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f)) =
      -Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
        (Scheme.Hom.relativeDifferentials f) (differentials_isInvertible f) := by
  let := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
  have h := differentials_picardClass f
  rw [Stacks.Divisors.negativeTwistPicardClass_eq_neg] at h
  have hn : Stacks.Picard.schemePullbackClass (pullback.diagonal f)
      (-Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f)) =
      -Stacks.Picard.schemePullbackClass (pullback.diagonal f)
        (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f)) :=
    map_neg (Stacks.Picard.schemePullbackClassHom (pullback.diagonal f)) _
  rw [hn] at h
  exact neg_eq_iff_eq_neg.mp h.symm

end M9Native.DiagonalNormalPicard
