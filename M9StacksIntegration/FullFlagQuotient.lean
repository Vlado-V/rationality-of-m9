module

public import M9StacksIntegration.FlagTowerLines
public import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian

/-!
# The last actual quotient of a full native flag is the original bundle

For a rank-r bundle a full flag has last quotient of rank r. The native
short-exact rank argument forces the original last subobject to vanish.
The resulting isomorphism is normalized by the original quotient map.
The tower specialization therefore attaches the flag's top bundle to
the genuine pullback of the original bundle, with no isomorphism premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.FlagTower

universe u

namespace M9Native.FullFlagQuotient

section Flags

variable {T : Scheme.{u}} {M : T.Modules} (r : ℕ)
  [hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M (r+1)]
  (F : Flag M (r+1))

/-- The actual final subobject of a full native flag is zero. -/
theorem lastSub_eq_bot : F.sub (Fin.last r) = ⊥ :=
  eq_bot_of_rank (r+1) hM (by simpa using F.rank (Fin.last r))

/-- The true universal-property comparison, retaining its quotient-map law. -/
theorem exists_quotientIso :
    ∃ e : FlagTowerLines.quotient F (Fin.last r) ≅ M,
      cokernel.π (F.sub (Fin.last r)).arrow ≫ e.hom = 𝟙 M := by
  apply FlagQuotientLines.exists_iso_of_kernel_eq _ (𝟙 M)
  calc
    kernelSubobject (cokernel.π (F.sub (Fin.last r)).arrow) = F.sub (Fin.last r) :=
      FlagQuotientLines.kernel_cokernel_subobject _
    _ = ⊥ := lastSub_eq_bot r F
    _ = kernelSubobject (𝟙 M) := by
      symm
      change Subobject.mk (kernel.ι (𝟙 M)) = ⊥
      rw [Subobject.mk_eq_bot_iff_zero]
      simpa using kernel.condition (𝟙 M)

/-- The normalized last-quotient isomorphism of the actual full flag. -/
def quotientIso : FlagTowerLines.quotient F (Fin.last r) ≅ M :=
  Classical.choose (exists_quotientIso r F)

@[reassoc]
theorem quotientIso_π :
    cokernel.π (F.sub (Fin.last r)).arrow ≫ (quotientIso r F).hom = 𝟙 M :=
  Classical.choose_spec (exists_quotientIso r F)

/-- No arbitrary automorphism of the original bundle remains. -/
theorem quotientIso_unique (e : FlagTowerLines.quotient F (Fin.last r) ≅ M)
    (he : cokernel.π (F.sub (Fin.last r)).arrow ≫ e.hom = 𝟙 M) :
    e = quotientIso r F := by
  apply Iso.ext
  exact (cancel_epi (cokernel.π (F.sub (Fin.last r)).arrow)).mp
    (he.trans (quotientIso_π r F).symm)

end Flags

section Towers

variable {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (r+1)]

/-- The last original universal quotient on the full native tower is
its actual pullback of the original bundle. -/
def towerQuotientIso :
    letI := hE.isFiniteLocallyFree
    FlagTowerLines.universalQuotient E (r+1) (Fin.last r) ≅
      (Scheme.Modules.pullback (tower (r+1) E).2).obj E := by
  letI := hE.isFiniteLocallyFree
  letI := @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _
    (tower (r+1) E).2 E (r+1) hE
  exact quotientIso r (FlagTowerLines.universalFlag E (r+1))

@[reassoc]
theorem towerQuotientIso_π :
    letI := hE.isFiniteLocallyFree
    cokernel.π ((FlagTowerLines.universalFlag E (r+1)).sub (Fin.last r)).arrow ≫
        (towerQuotientIso E r).hom =
      𝟙 ((Scheme.Modules.pullback (tower (r+1) E).2).obj E) := by
  letI := hE.isFiniteLocallyFree
  letI := @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _
    (tower (r+1) E).2 E (r+1) hE
  exact quotientIso_π r (FlagTowerLines.universalFlag E (r+1))

end Towers

end M9Native.FullFlagQuotient
