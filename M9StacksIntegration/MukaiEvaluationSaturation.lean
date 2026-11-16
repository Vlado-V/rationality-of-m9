module

public import M9StacksIntegration.MukaiSemiIrreducible
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Quotient
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.TorsionFreeDimensionOne

/-!
# Saturating a prescribed native evaluation image

For an actual sheaf morphism `φ : F → E`, this file constructs

`ker(E → coker φ → (coker φ)/(coker φ)_tors)`.

The quotient is torsion free and the original map factors through the
kernel. Thus the original sections are retained. This is different from
constructing some unspecified line subbundle. Finite local freeness and
the rank of this prescribed kernel on a smooth curve are separate results;
they are not premises hidden in its definition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.MukaiEvaluationSaturation

open Stacks.AlgebraicGeometry.TorsionQuasicoherent

variable {X : Scheme.{u}} [IsIntegral X]
variable {F E : X.Modules} (φ : F ⟶ E)
variable [(cokernel φ).IsQuasicoherent]

/-- The actual quotient of the original cokernel by its torsion subsheaf. -/
abbrev torsionFreeQuotient : X.Modules := torsionQuotient (cokernel φ)

/-- The actual quotient morphism whose kernel saturates the prescribed
image. Both factors are categorical cokernel projections. -/
def projection : E ⟶ torsionFreeQuotient φ :=
  cokernel.π φ ≫ cokernel.π (torsionIncl (cokernel φ))

instance projection_epi : Epi (projection φ) := by
  dsimp [projection]
  infer_instance

/-- The saturated image is a constructed categorical kernel. -/
def saturation : X.Modules := kernel (projection φ)

/-- Inclusion of the constructed saturated image in the original sheaf. -/
def inclusion : saturation φ ⟶ E := kernel.ι (projection φ)

instance inclusion_mono : Mono (inclusion φ) := by
  dsimp [inclusion]
  infer_instance

/-- The original map is killed by the quotient projection, before any
rank or local-freeness statement is made. -/
theorem comp_projection_zero : φ ≫ projection φ = 0 := by
  simp only [projection, ← Category.assoc, cokernel.condition, zero_comp]

/-- The original evaluation map factors through its constructed
saturation, by the universal property of the actual kernel. -/
def factor : F ⟶ saturation φ :=
  kernel.lift (projection φ) φ (comp_projection_zero φ)

@[reassoc (attr := simp)] theorem factor_inclusion : factor φ ≫ inclusion φ = φ :=
  kernel.lift_ι _ _ _

/-- The original sectionwise image is retained by the actual factor map. -/
theorem sectionsMap_factor_inclusion (s : F.sections) :
    _root_.SheafOfModules.sectionsMap (inclusion φ)
      (_root_.SheafOfModules.sectionsMap (factor φ) s) =
        _root_.SheafOfModules.sectionsMap φ s := by
  have h := congrArg (fun q => _root_.SheafOfModules.sectionsMap q s) (factor_inclusion φ)
  exact h

/-- The constructed quotient is genuinely torsion free, by native
Stacks Tag 0AXT, rather than by a saturation label. -/
theorem torsionFreeQuotient_isTorsionFree :
    Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree (torsionFreeQuotient φ) :=
  isTorsionFree_torsionQuotient (cokernel φ)

/-- The actual kernel and torsion-free quotient form a short exact
sequence, so this construction retains its sheaf-theoretic maps. -/
theorem sequence_shortExact :
    (ShortComplex.mk (inclusion φ) (projection φ) (kernel.condition (projection φ))).ShortExact :=
  { exact := ShortComplex.exact_kernel (projection φ) }

/-- The torsion-free quotient is quasi-coherent, using the original
quasi-coherent torsion subsheaf and the genuine cokernel. -/
instance torsionFreeQuotient_isQuasicoherent : (torsionFreeQuotient φ).IsQuasicoherent := by
  let : (torsionModule (cokernel φ)).IsQuasicoherent :=
    torsionSubsheaf_isQuasicoherent (cokernel φ)
  exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _

/-- The quotient of a coherent original sheaf is coherent on a locally
Noetherian scheme. Coherence of the saturation is not an input. -/
theorem torsionFreeQuotient_isCoherent [IsLocallyNoetherian X] [E.IsCoherent] :
    (torsionFreeQuotient φ).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_epi_of_isQuasicoherent (projection φ)

/-- The prescribed saturation is coherent, as the actual kernel of a
morphism between the original coherent sheaf and its coherent quotient. -/
theorem saturation_isCoherent [IsLocallyNoetherian X] [E.IsCoherent] :
    (saturation φ).IsCoherent := by
  let := torsionFreeQuotient_isCoherent φ
  exact _root_.SheafOfModules.kernel_isCoherent (projection φ)

/-- On an integral regular curve the constructed torsion-free quotient
is finite locally free. Its coherence is derived from the original E. -/
theorem torsionFreeQuotient_isFiniteLocallyFree
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E) :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (torsionFreeQuotient φ) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let := hE
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let := torsionFreeQuotient_isCoherent φ
  exact (isTorsionFree_iff_isFiniteLocallyFree hreg hdim (torsionFreeQuotient φ)).mp
    (torsionFreeQuotient_isTorsionFree φ)

/-- The actual saturation of a prescribed image in a vector bundle on
an integral regular curve is finite locally free. Torsion freeness is
pulled back along the original injective kernel stalk map; no subbundle
or local-freeness witness is supplied for the saturation. -/
theorem saturation_isFiniteLocallyFree
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E) :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (saturation φ) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let := hE
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let := saturation_isCoherent φ
  let : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  let : (saturation φ).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (saturation φ)
  have hET : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr hE
  have hST : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree (saturation φ) := by
    refine (isTorsionFree_iff_forall_stalk (saturation φ)).mpr fun x => ?_
    let := Stacks.SheafOfModules.FlatShortExact.stalkModule
      (X := X.toRingedSpace) (saturation φ) x
    let := Stacks.SheafOfModules.FlatShortExact.stalkModule
      (X := X.toRingedSpace) E x
    let : Module.IsTorsionFree (X.presheaf.stalk x)
        (Stacks.SheafOfModules.FlatShortExact.abStalk (X := X.toRingedSpace) E x) :=
      (isTorsionFree_iff_forall_stalk E).mp hET x
    obtain ⟨j,_,hj,_,_⟩ := Stacks.SheafOfModules.FlatShortExact.stalkShortExact
      (X := X.toRingedSpace)
      (ShortComplex.mk (inclusion φ) (projection φ) (kernel.condition (projection φ)))
      (sequence_shortExact φ) x
    exact hj.moduleIsTorsionFree j (fun r m => j.map_smul r m)
  exact (isTorsionFree_iff_isFiniteLocallyFree hreg hdim (saturation φ)).mp hST

end M9Native.MukaiEvaluationSaturation
