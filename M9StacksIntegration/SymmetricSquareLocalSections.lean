module

public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyUnitIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme

/-!
# Actual symmetric and exterior sections on finite-free opens

The native sectionwise comparisons become linear equivalences on a
trivializing open. Bijectivity is derived from the actual finite free
model and the genuine sheafification universal property. No comparison
or compatibility with gluing is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open scoped TensorProduct

universe u

namespace M9Native.SymmetricSquareBundleDeterminant

section PresheafPowers

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O : Sheaf J CommRingCat.{u}}

/-- The actual sectionwise symmetric powers carry an actual sheaf
isomorphism to a presheaf isomorphism, by functoriality. -/
def symPowPresheafIso (n : ℕ)
    {F G : SheafOfModules.{u} (toRingCat J O)} (e : F ≅ G) :
    PresheafOfModules.symPow n F.val ≅ PresheafOfModules.symPow n G.val where
  hom := PresheafOfModules.symPowMap n e.hom.val
  inv := PresheafOfModules.symPowMap n e.inv.val
  hom_inv_id := by
    rw [← PresheafOfModules.symPowMap_comp, ← SheafOfModules.comp_val, e.hom_inv_id,
      SheafOfModules.id_val, PresheafOfModules.symPowMap_id]
  inv_hom_id := by
    rw [← PresheafOfModules.symPowMap_comp, ← SheafOfModules.comp_val, e.inv_hom_id,
      SheafOfModules.id_val, PresheafOfModules.symPowMap_id]

/-- The analogous actual presheaf isomorphism for exterior powers. -/
def extPowPresheafIso (n : ℕ)
    {F G : SheafOfModules.{u} (toRingCat J O)} (e : F ≅ G) :
    PresheafOfModules.extPow n F.val ≅ PresheafOfModules.extPow n G.val where
  hom := PresheafOfModules.extPowMap n e.hom.val
  inv := PresheafOfModules.extPowMap n e.inv.val
  hom_inv_id := by
    rw [← PresheafOfModules.extPowMap_comp, ← SheafOfModules.comp_val, e.hom_inv_id,
      SheafOfModules.id_val, PresheafOfModules.extPowMap_id]
  inv_hom_id := by
    rw [← PresheafOfModules.extPowMap_comp, ← SheafOfModules.comp_val, e.inv_hom_id,
      SheafOfModules.id_val, PresheafOfModules.extPowMap_id]

/-- On an actual finite free sheaf the presheaf of sectionwise
symmetric powers already satisfies descent. -/
theorem isSheaf_symPow_of_iso_free (n : ℕ) (F : SheafOfModules.{u} (toRingCat J O))
    (I : Type u) [Finite I]
    (e : F ≅ SheafOfModules.free (R := toRingCat J O) I) :
    Presheaf.IsSheaf J (PresheafOfModules.symPow n F.val).presheaf := by
  classical
  let t := symPowPresheafIso n e ≪≫
    Stacks.SheafOfModules.symPowFreeIso (toRingCat J O).property n
  exact (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf (toRingCat J O).obj).mapIso t)).2
      (SheafOfModules.free (R := toRingCat J O) {d : I →₀ ℕ | d.degree = n}).isSheaf

/-- Exterior powers of an actual finite free sheaf have the same
sectionwise descent property. -/
theorem isSheaf_extPow_of_iso_free (n : ℕ) (F : SheafOfModules.{u} (toRingCat J O))
    (I : Type u) [Finite I]
    (e : F ≅ SheafOfModules.free (R := toRingCat J O) I) :
    Presheaf.IsSheaf J (PresheafOfModules.extPow n F.val).presheaf := by
  classical
  letI : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  let t := extPowPresheafIso n e ≪≫
    Stacks.SheafOfModules.extPowFreeIso (toRingCat J O).property n
  exact (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf (toRingCat J O).obj).mapIso t)).2
      (SheafOfModules.free (R := toRingCat J O) (Set.powersetCard I n)).isSheaf

end PresheafPowers

section LocalSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (W : C)
  (P : PresheafOfModules.{u} R.obj)

/-- The actual global sheafification unit is already bijective on a
slice where its source satisfies the sheaf condition. This uses the
native restricted unit and its proved local bijectivity. -/
theorem bijective_unit_app_of_isSheaf_over
    (hP : Presheaf.IsSheaf (J.over W)
      ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor R W).obj P).presheaf)
    (V : (Over W)ᵒᵖ) :
    Function.Bijective
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P).app
        ((Over.forget W).op.obj V)).hom) := by
  let F : Sheaf (J.over W) AddCommGrpCat.{u} := ⟨_, hP⟩
  let G := (SheafOfModules.toSheaf (R.over W)).obj
    (((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over W)
  let a : F ⟶ G := ⟨Stacks.SheafOfModules.SliceSheafification.overToSheafify R W P⟩
  letI : Sheaf.IsLocallyInjective a :=
    Stacks.SheafOfModules.SliceSheafification.isLocallyInjective_overToSheafify R W P
  letI : Sheaf.IsLocallySurjective a :=
    Stacks.SheafOfModules.SliceSheafification.isLocallySurjective_overToSheafify R W P
  letI : IsIso a := (Sheaf.isLocallyBijective_iff_isIso a).1 ⟨inferInstance, inferInstance⟩
  letI : IsIso a.hom := (sheafToPresheaf (J.over W) AddCommGrpCat.{u}).map_isIso a
  exact ConcreteCategory.bijective_of_isIso (a.hom.app V)

end LocalSheafification

section LocalPowerComparisons

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (F : SheafOfModules.{u} (toRingCat J O)) (W : C)
  [(J.over W).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify (J.over W) AddCommGrpCat.{u}]
  [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [(J.over W).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The sectionwise symmetric-power presheaf is a sheaf on every
actual finite-free trivializing slice. -/
theorem isSheaf_symPow_over_of_iso_free (n : ℕ) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := (toRingCat J O).over W) I) :
    Presheaf.IsSheaf (J.over W)
      ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor (toRingCat J O) W).obj
        (PresheafOfModules.symPow n F.val)).presheaf := by
  let t :
      ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor (toRingCat J O) W).obj
        (PresheafOfModules.symPow n F.val)).presheaf ≅
      (PresheafOfModules.symPow (O := (Over.forget W).op ⋙ O.obj) n (F.over W).val).presheaf :=
    { hom := PresheafOfModules.symPowOverAb W n F.val
      inv := PresheafOfModules.symPowOverAbInv W n F.val
      hom_inv_id := by rfl
      inv_hom_id := by rfl }
  exact (Presheaf.isSheaf_of_iso_iff t).2
      (isSheaf_symPow_of_iso_free (O := O.over W) n (F.over W) I e)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [(J.over W).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The analogous sectionwise exterior-power sheaf condition on the
same actual finite-free trivializing slice. -/
theorem isSheaf_extPow_over_of_iso_free (n : ℕ) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := (toRingCat J O).over W) I) :
    Presheaf.IsSheaf (J.over W)
      ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor (toRingCat J O) W).obj
        (PresheafOfModules.extPow n F.val)).presheaf := by
  let t :
      ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor (toRingCat J O) W).obj
        (PresheafOfModules.extPow n F.val)).presheaf ≅
      (PresheafOfModules.extPow (O := (Over.forget W).op ⋙ O.obj) n (F.over W).val).presheaf :=
    { hom := PresheafOfModules.extPowOverAb W n F.val
      inv := PresheafOfModules.extPowOverAbInv W n F.val
      hom_inv_id := by rfl
      inv_hom_id := by rfl }
  exact (Presheaf.isSheaf_of_iso_iff t).2
      (isSheaf_extPow_of_iso_free (O := O.over W) n (F.over W) I e)

/-- The canonical comparison to an actual symmetric algebra is
bijective on sections inside an actual finite-free trivialization. -/
theorem symPowCmp_bijective_of_iso_free_over
    (A : SheafOfModules.GradedAlgebra.{u,u} (toRingCat J O))
    (gen : F ⟶ A.piece 1) (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)
    (n : ℕ) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := (toRingCat J O).over W) I)
    (V : (Over W)ᵒᵖ) :
    Function.Bijective
      (((A.symPowCmp gen hA.1 n).app ((Over.forget W).op.obj V)).hom) := by
  rw [SheafOfModules.symPowCmp_eq_sheafifyUnit_comp F A gen hA.1 hA n]
  exact (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (toRingCat J O) ((Over.forget W).op.obj V)).map
      (SheafOfModules.symmetricPieceIso F A gen hA (n : ℤ)).hom)).comp
    (bijective_unit_app_of_isSheaf_over (toRingCat J O) W
      (PresheafOfModules.symPow n F.val)
      (isSheaf_symPow_over_of_iso_free F W n I e) V)

/-- The canonical exterior comparison is bijective on sections inside
an actual finite-free trivialization, with no comparison premise. -/
theorem extPowCmp_bijective_of_iso_free_over
    (A : SheafOfModules.GradedAlgebra.{u,u} (toRingCat J O))
    (gen : F ⟶ A.piece 1) (hA : SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)
    (n : ℕ) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := (toRingCat J O).over W) I)
    (V : (Over W)ᵒᵖ) :
    Function.Bijective
      (((A.extPowCmp gen hA.1 n).app ((Over.forget W).op.obj V)).hom) := by
  rw [SheafOfModules.extPowCmp_eq_sheafifyUnit_comp F A gen hA.1 hA n]
  exact (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (toRingCat J O) ((Over.forget W).op.obj V)).map
      (SheafOfModules.exteriorPieceIso F A gen hA (n : ℤ)).hom)).comp
    (bijective_unit_app_of_isSheaf_over (toRingCat J O) W
      (PresheafOfModules.extPow n F.val)
      (isSheaf_extPow_over_of_iso_free F W n I e) V)

end LocalPowerComparisons

section Schemes

variable {X : Scheme.{u}}

/-- The literal degree-two piece of the native symmetric algebra. -/
abbrev symmetricSquare (F : X.Modules) : X.Modules :=
  (Scheme.Modules.symmetricAlgebra X F).piece 2

/-- The actual symmetric section comparison, linear over the original
ring of functions on the given open. -/
def symmetricSectionComparison (F : X.Modules) (n : ℕ) (U : X.Opens) :
    SymPow.symmetricPower n Γ(X, U) Γ(F, U) →ₗ[Γ(X, U)]
      Γ((Scheme.Modules.symmetricAlgebra X F).piece (n : ℤ), U) :=
  (((Scheme.Modules.symmetricAlgebra X F).symPowCmp
    (Scheme.Modules.symmetricAlgebraGen X F)
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).1 n).app (op U)).hom.comp
      (PresheafOfModules.symPowSections n F.val (op U)).symm.toLinearMap

/-- The analogous actual sectionwise exterior comparison. -/
def exteriorSectionComparison (F : X.Modules) (n : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^n Γ(F, U)) →ₗ[Γ(X, U)]
      Γ(Scheme.Modules.exteriorPower F (n : ℤ), U) :=
  (((Scheme.Modules.exteriorAlgebra F).extPowCmp
    (Scheme.Modules.exteriorGenerator F)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F).1 n).app (op U)).hom.comp
      (PresheafOfModules.extPowSections n F.val (op U)).symm.toLinearMap

/-- On every open inside an actual finite-free trivialization, the
canonical native symmetric comparison is an actual linear equivalence. -/
def symmetricSectionsEquivOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) (n : ℕ) :
    SymPow.symmetricPower n Γ(X, U) Γ(F, U) ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.symmetricAlgebra X F).piece (n : ℤ), U) :=
  LinearEquiv.ofBijective (symmetricSectionComparison F n U)
    ((symPowCmp_bijective_of_iso_free_over F W
      (Scheme.Modules.symmetricAlgebra X F) (Scheme.Modules.symmetricAlgebraGen X F)
      (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F) n I e
      (op (Over.mk (homOfLE h)))).comp
        (PresheafOfModules.symPowSections n F.val (op U)).symm.bijective)

/-- The actual exterior comparison on the same finite-free open is an
actual linear equivalence. -/
def exteriorSectionsEquivOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) (n : ℕ) :
    (⋀[Γ(X, U)]^n Γ(F, U)) ≃ₗ[Γ(X, U)]
      Γ(Scheme.Modules.exteriorPower F (n : ℤ), U) :=
  LinearEquiv.ofBijective (exteriorSectionComparison F n U)
    ((extPowCmp_bijective_of_iso_free_over F W
      (Scheme.Modules.exteriorAlgebra F) (Scheme.Modules.exteriorGenerator F)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F) n I e
      (op (Over.mk (homOfLE h)))).comp
        (PresheafOfModules.extPowSections n F.val (op U)).symm.bijective)

@[simp] theorem symmetricSectionsEquivOn_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) (n : ℕ)
    (x : SymPow.symmetricPower n Γ(X, U) Γ(F, U)) :
    symmetricSectionsEquivOn F W U h I e n x = symmetricSectionComparison F n U x := rfl

@[simp] theorem exteriorSectionsEquivOn_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) (n : ℕ)
    (x : ⋀[Γ(X, U)]^n Γ(F, U)) :
    exteriorSectionsEquivOn F W U h I e n x = exteriorSectionComparison F n U x := rfl

end Schemes

end M9Native.SymmetricSquareBundleDeterminant
