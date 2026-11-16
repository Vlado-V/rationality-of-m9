module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClassPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible

/-!
# Lifting genuine Picard equalities to actual tensor-line isomorphisms

This is the native meaning of equality of Picard classes: an actual
isomorphism of actual invertible module sheaves.  The pullback functors
in the conclusions are the scheme-module pullbacks used by ordinary
cohomology and base change.  No Chern identity is a hypothesis or a
conclusion here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.PoincareChern

/-- The native Picard class at the actual scheme-module spelling. -/
abbrev lineClass {Y : Scheme.{u}} (L : Y.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    Stacks.Picard.ofScheme Y :=
  Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatSheaf.2 L hL

/-- The actual representative chosen by the native Picard group. -/
abbrev lineRepresentative (Y : Scheme.{u}) (x : Stacks.Picard.ofScheme Y) : Y.Modules :=
  (Stacks.Picard.picardRepresentative Y.toRingedSpace x).obj

instance lineRepresentative_isInvertible (Y : Scheme.{u}) (x : Stacks.Picard.ofScheme Y) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (lineRepresentative Y x) :=
  (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property

theorem lineClass_representative (Y : Scheme.{u}) (x : Stacks.Picard.ofScheme Y) :
    lineClass (lineRepresentative Y x) = x :=
  Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace x

theorem lineClass_congr {Y : Scheme.{u}} {L M : Y.Modules}
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (e : L ≅ M) : lineClass L = lineClass M :=
  (Stacks.SheafOfModules.picardClass_eq_iff Y.presheaf Y.ringCatSheaf.2 L M hL hM).2 ⟨e⟩

instance lineTensor_isInvertible {Y : Scheme.{u}} (L M : Y.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Scheme.Modules.tensorObj L M) :=
  @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ Y.presheaf Y.ringCatSheaf.2
    _ _ _ _ hL hM

/-- The native class pullback is the class of the actual scheme-module
pullback; the comparison between the two native pullback spellings is
an actual natural isomorphism. -/
theorem lineClass_pullback {Y S : Scheme.{u}} (g : Y ⟶ S) (L : S.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L] :
    lineClass ((Scheme.Modules.pullback g).obj L) =
      Stacks.Picard.schemePullbackClass g (lineClass L) := by
  have hp := Stacks.RingedSpace.modulePullback_isInvertible_of g.toLRSHom.toShHom L hL
  have hc := Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom L hL
  exact (lineClass_congr ((Stacks.ProjectiveBundleQuotients.pullbackIso g).app L)).trans
    hc.symm

/-- Tensor product adds the actual Picard classes. -/
theorem lineClass_tensor {Y : Scheme.{u}} (L M : Y.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] :
    lineClass (Scheme.Modules.tensorObj L M) = lineClass L + lineClass M :=
  (Stacks.SheafOfModules.picardClass_tensorSheaf Y.presheaf Y.ringCatSheaf.2
    L M hL hM (lineTensor_isInvertible L M)).symm

/-- An equality already proved in the genuine Picard group gives an
actual tensor-line isomorphism. -/
theorem nonempty_tensorIso_of_lineClass_eq {Y : Scheme.{u}} (N G L : Y.Modules)
    [hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
    [hG : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 G]
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (h : lineClass L = lineClass N + lineClass G) :
    Nonempty (Scheme.Modules.tensorObj N G ≅ L) := by
  apply (Stacks.SheafOfModules.picardClass_eq_iff Y.presheaf Y.ringCatSheaf.2
    (Scheme.Modules.tensorObj N G) L inferInstance hL).1
  exact (lineClass_tensor N G).trans h.symm

/-- The actual divisor line is the representative of its genuine
native divisor class, at the scheme-module spelling. -/
theorem lineClass_divisor {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.divisorSheaf D) :=
      Stacks.Divisors.isInvertible_invertibleSheaf_picard D
    lineClass (Stacks.Divisors.divisorSheaf D) = Stacks.Divisors.picardClass D :=
  rfl

/-- A genuine normalized-family Picard equality lifts to a genuine
isomorphism of the pulled-back family line with the divisor line
twisted by the specified actual base line. -/
theorem nonempty_divisorTensorIso_of_pullbackClass_eq
    {Y S T : Scheme.{u}} (g : Y ⟶ S) (π : Y ⟶ T)
    (x : Stacks.Picard.ofScheme S) (n : Stacks.Picard.ofScheme T)
    (D : Y.IdealSheafData) [hD : Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h : Stacks.Picard.schemePullbackClass g x =
      Stacks.Picard.schemePullbackClass π n + Stacks.Divisors.picardClass D) :
    Nonempty (Scheme.Modules.tensorObj
      ((Scheme.Modules.pullback π).obj (lineRepresentative T n))
      (Stacks.Divisors.divisorSheaf D) ≅
      (Scheme.Modules.pullback g).obj (lineRepresentative S x)) := by
  letI : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.divisorSheaf D) :=
    Stacks.Divisors.isInvertible_invertibleSheaf_picard D
  apply nonempty_tensorIso_of_lineClass_eq
    ((Scheme.Modules.pullback π).obj (lineRepresentative T n))
    (Stacks.Divisors.divisorSheaf D)
    ((Scheme.Modules.pullback g).obj (lineRepresentative S x))
  rw [lineClass_pullback, lineClass_representative, lineClass_pullback,
    lineClass_representative, lineClass_divisor]
  exact h

end M9Native.PoincareChern
