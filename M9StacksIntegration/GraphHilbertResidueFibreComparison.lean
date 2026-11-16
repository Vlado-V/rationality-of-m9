module

public import M9StacksIntegration.GraphHilbertEulerComparison

/-! The residue-field fibres of an actual represented closed support,
with their original scheme projections and restricted native line. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace M9Native.GraphHilbertResidueFibreComparison
open AlgebraicGeometry.Space M9Native.GraphHilbertEulerComparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} (A : CoherentObject D)
  (Z : ClosedSubspaces B S hS (D.space A.T).1)
  (U : BigFppfOver B S hS) (f : U ⟶ A.T.left)
  (E : schemeSpace U ≅ closedSubspaceToSpace B S hS (D.space A.T) Z)
  (hE : E.hom ≫ A.closedSubspaceProjection Z = schemeSpaceMap f)
  (t : A.testScheme)

/-- The actual original scheme fibre over `Spec κ(t)`. -/
abbrev originalFibre : BigFppfOver B S hS := pullback (A.pointSchemeHom t) f

/-- Its actual projection to the residue field. -/
abbrev originalFibreProjection : originalFibre A U f t ⟶ A.pointScheme t :=
  pullback.fst (A.pointSchemeHom t) f

theorem originalFibre_isPullback :
    IsPullback (schemeSpaceMap (pullback.snd (A.pointSchemeHom t) f))
      (schemeSpaceMap (originalFibreProjection A U f t)) (schemeSpaceMap f)
      ((schemeSpaceFunctor B S hS).map (A.pointSchemeHom t)) := by
  apply IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
  exact ((IsPullback.of_hasPullback (A.pointSchemeHom t) f).flip.map yoneda)

include hE in
theorem originalFibre_isPullback_support :
    IsPullback (schemeSpaceMap (pullback.snd (A.pointSchemeHom t) f) ≫ E.hom)
      (schemeSpaceMap (originalFibreProjection A U f t)) (A.closedSubspaceProjection Z)
      ((schemeSpaceFunctor B S hS).map (A.pointSchemeHom t)) := by
  have sqE : IsPullback E.hom (schemeSpaceMap f) (A.closedSubspaceProjection Z) (𝟙 _) :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _)
      ⟨hE.trans (Category.comp_id _).symm⟩
  simpa only [Category.comp_id] using
    (originalFibre_isPullback A U f t).paste_horiz sqE

/-- The actual support fibre is represented by the actual original
scheme fibre. This uses the original scheme pullback and both genuine
cartesian squares; no fibre isomorphism is an input. -/
def originalFibreIso :
    schemeSpace (originalFibre A U f t) ≅
      closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t) :=
  (originalFibre_isPullback_support A Z U f E hE t).isoIsPullback _ _
    (A.isPullback_closedFibre_pointScheme Z t)

theorem originalFibreIso_projection :
    (originalFibreIso A Z U f E hE t).hom ≫
      closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t) ≫
        D.projection (A.pointTest t) = schemeSpaceMap (originalFibreProjection A U f t) :=
  (originalFibre_isPullback_support A Z U f E hE t).isoIsPullback_hom_snd _ _
    (A.isPullback_closedFibre_pointScheme Z t)

theorem originalFibreIso_toSupport :
    (originalFibreIso A Z U f E hE t).hom ≫ A.closedFibreToSubspace Z t =
      schemeSpaceMap (pullback.snd (A.pointSchemeHom t) f) ≫ E.hom :=
  (originalFibre_isPullback_support A Z U f E hE t).isoIsPullback_hom_fst _ _
    (A.isPullback_closedFibre_pointScheme Z t)

theorem closedFibreToSubspace_comp_ambient :
    A.closedFibreToSubspace Z t ≫
        (closedSubspaceInclusion B S hS (D.space A.T) Z ≫ baseChangeProjection D.f A.T) =
      closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t) ≫
        baseChangeProjection D.f (A.pointTest t) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ baseChangeProjection D.f A.T) (A.isPullback_closedFibre Z t).w).trans
      ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (baseChangeMap_comp_projection D.f (A.pointTestHom t)))))

/-- The projection produced by the native scalar comparison is exactly
the actual original scheme fibre projection. -/
theorem projectionOfIso_originalFibreIso :
    projectionOfIso (originalFibreIso A Z U f E hE t)
      ((closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t)).hom ≫
        A.fibreProjection t) = originalFibreProjection A U f t := by
  apply yoneda.map_injective
  rw [projectionOfIso, yoneda.map_preimage]
  exact congrArg (fun q => q.hom) (originalFibreIso_projection A Z U f E hE t)

/-- The map from the represented original fibre to the original native
ambient space. -/
def originalFibreAmbientMap : schemeSpace (originalFibre A U f t) ⟶ D.X :=
  (originalFibreIso A Z U f E hE t).hom ≫
    closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t) ≫
      baseChangeProjection D.f (A.pointTest t)

theorem originalFibreAmbientMap_eq :
    originalFibreAmbientMap A Z U f E hE t =
      schemeSpaceMap (pullback.snd (A.pointSchemeHom t) f) ≫ E.hom ≫
        closedSubspaceInclusion B S hS (D.space A.T) Z ≫ baseChangeProjection D.f A.T := by
  unfold originalFibreAmbientMap
  rw [← closedFibreToSubspace_comp_ambient A Z t]
  rw [← Category.assoc, originalFibreIso_toSupport]
  simp only [Category.assoc]

variable (L : AlgebraicGeometry.Space.Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O).property L]

/-- The actual native line restricted to the represented original fibre. -/
abbrev nativeFibreLine : AlgebraicGeometry.Space.Modules.{u, u} B S hS
    (schemeSpace (originalFibre A U f t)).1 (schemeSpace (originalFibre A U f t)).2 :=
  (modulePullback B S hS (originalFibreAmbientMap A Z U f E hE t)).obj L

instance nativeFibreLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (schemeSpace (originalFibre A U f t)).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (schemeSpace (originalFibre A U f t)).1 (schemeSpace (originalFibre A U f t)).2).O).property
      (nativeFibreLine A Z U f E hE t L) :=
  stacksIsInvertible_modulePullback_obj B S hS (originalFibreAmbientMap A Z U f E hE t) L

/-- The actual original scheme restriction of the ambient line. -/
abbrev originalFibreLine : ((BigFppfOver.toScheme B S hS).obj (originalFibre A U f t)).Modules :=
  baseChangeModule B S hS L (originalFibre A U f t)
    (originalFibreAmbientMap A Z U f E hE t).hom

theorem originalFibreLine_eq_reading :
    originalFibreLine A Z U f E hE t L =
      schemeReading B S hS (originalFibre A U f t) (nativeFibreLine A Z U f E hE t L) := rfl

/-- The actual fibre restriction is the genuine original pullback of
the total restricted line. Its compatibility is derived from the two
cartesian squares and the native quasi-coherent base-change theorem. -/
def originalFibreLinePullbackIso :
    originalFibreLine A Z U f E hE t L ≅
      Stacks.AmpleLocallyClosed.pullbackModule
        ((BigFppfOver.toScheme B S hS).map (pullback.snd (A.pointSchemeHom t) f))
        (baseChangeModule B S hS L U
          (E.hom ≫ closedSubspaceInclusion B S hS (D.space A.T) Z ≫
            baseChangeProjection D.f A.T).hom) :=
  eqToIso (congrArg (baseChangeModule B S hS L (originalFibre A U f t))
    (congrArg (fun q => q.hom) (originalFibreAmbientMap_eq A Z U f E hE t))) ≪≫
  (nonempty_baseChangeModule_baseChange_of_isInvertible L hL U (originalFibre A U f t)
    (E.hom ≫ closedSubspaceInclusion B S hS (D.space A.T) Z ≫
      baseChangeProjection D.f A.T).hom (pullback.snd (A.pointSchemeHom t) f)).some

/-- Every integer tensor power of that actual original line. -/
abbrev originalFibreLinePower (n : ℤ) :
    ((BigFppfOver.toScheme B S hS).obj (originalFibre A U f t)).Modules :=
  schemeReadingTensorPower B S hS (originalFibre A U f t)
    (nativeFibreLine A Z U f E hE t L) n

/-- The native twisted Euler characteristic of the actual closed
support is the original scheme Euler characteristic of every integer
power of the actual restricted line. -/
theorem twistedEuler_eq_originalFibreLinePower
    (eZ : A.F ≅ pushforwardStructureSheaf B S hS (D.space A.T) Z) (n : ℤ) :
    CoherentObject.twistedEuler L A t n =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank (A.testScheme.residueField t)
          (cohomologyOverField (A.testScheme.residueField t)
            ((BigFppfOver.toScheme B S hS).map (originalFibreProjection A U f t))
            (originalFibreLinePower A Z U f E hE t L n) i) : ℤ) := by
  let W := closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t)
  haveI : (smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS W.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  haveI : HasWeakSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u})
  let it := closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t)
  let pt := it ≫ baseChangeProjection D.f (A.pointTest t)
  let Et := originalFibreIso A Z U f E hE t
  let q := it.hom ≫ A.fibreProjection t
  let Lpow := invertibleTensorPower B S hS D.X.1 D.X.2 L n
  haveI hPow := stacksIsInvertible_invertibleTensorPower B S hS D.X L n
  let M := (modulePullback B S hS pt).obj Lpow
  haveI hM := stacksIsInvertible_modulePullback_obj B S hS pt Lpow
  let Mraw := ((Stacks.SheafOfModules.Tensor.sheafTensor
    (smallEtaleRingedSite B S hS W.1 W.2).O).obj (SheafOfModules.unit _)).obj
      ((modulePullback B S hS it).obj (CoherentObject.fibreTwist L A t n))
  let eM : Mraw ≅ M :=
    Stacks.SheafOfModules.tensorSheafLeftUnitor (structurePresheaf B S hS W.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS W.1 W.2).O).property _ ≪≫
      (modulePullbackCompIso B S hS it (baseChangeProjection D.f (A.pointTest t))).app Lpow
  have hPM := isQuasicoherentOnSite_modulePullback_of_isInvertible Et.hom M hM
  have hWU := (eulerCharacteristicAlong_iso_eq_schemeReading
    (k := A.testScheme.residueField t)
    (hk := B.residueField_spec_contains A.T.left.left.property t)
    (g := A.pointSchemeHom' t) Et q M hM).trans
      (eulerCharacteristicAlong_eq_schemeReading B S hS (originalFibre A U f t)
        (A.testScheme.residueField t)
        (B.residueField_spec_contains A.T.left.left.property t)
        (A.pointSchemeHom' t) (projectionOfIso Et q) _ hPM).symm
  dsimp only [Et, q, it] at hWU
  rw [projectionOfIso_originalFibreIso] at hWU
  let ePow : (modulePullback B S hS Et.hom).obj M ≅
      invertibleTensorPower B S hS (schemeSpace (originalFibre A U f t)).1
        (schemeSpace (originalFibre A U f t)).2
        (nativeFibreLine A Z U f E hE t L) n :=
    (modulePullbackCompIso B S hS Et.hom pt).app Lpow ≪≫
      modulePullbackInvertibleTensorPowerIso B S hS (Et.hom ≫ pt) L n
  exact (A.twistedEuler_eq_of_closedSubspace Z t L eZ n).trans
    ((eulerCharacteristicAlong_congr B S hS W.1 W.2
      (A.testScheme.residueField t) _ eM).trans
        (hWU.trans ((eulerCharacteristicAlong_congr B S hS _ _
          (A.testScheme.residueField t) _ ePow).trans
            (eulerCharacteristicAlong_tensorPower_eq_schemeReading B S hS
              (originalFibre A U f t) (A.testScheme.residueField t)
              (B.residueField_spec_contains A.T.left.left.property t)
              (A.pointSchemeHom' t) (originalFibreProjection A U f t)
              (nativeFibreLine A Z U f E hE t L) n))))

/-- The native Hilbert condition is precisely the original scheme
Euler condition at every original residue point and every integer.
No Hilbert membership, degree, or line compatibility is a premise. -/
theorem hasHilbertPolynomial_iff_originalFibreEuler
    (eZ : A.F ≅ pushforwardStructureSheaf B S hS (D.space A.T) Z) (P : ℤ → ℤ) :
    CoherentObject.HasHilbertPolynomial L P A ↔
      ∀ (t : A.testScheme) (n : ℤ), P n =
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
          (Module.finrank (A.testScheme.residueField t)
            (cohomologyOverField (A.testScheme.residueField t)
              ((BigFppfOver.toScheme B S hS).map (originalFibreProjection A U f t))
              (originalFibreLinePower A Z U f E hE t L n) i) : ℤ) := by
  rw [CoherentObject.hasHilbertPolynomial_iff]
  constructor
  · intro h t n
    exact (h t n).trans (twistedEuler_eq_originalFibreLinePower A Z U f E hE t L eZ n)
  · intro h t n
    exact (h t n).trans (twistedEuler_eq_originalFibreLinePower A Z U f E hE t L eZ n).symm

end M9Native.GraphHilbertResidueFibreComparison
