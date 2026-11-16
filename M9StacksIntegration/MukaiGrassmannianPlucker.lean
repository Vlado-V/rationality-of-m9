module

public import M9StacksIntegration.GrassmannianCharts
public import M9StacksIntegration.MukaiOrderedMinors
public import M9StacksIntegration.MukaiGrassmannianDimension
public import M9StacksIntegration.MukaiGrassmannianPoints
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Projective
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The actual five-dimensional Grassmannian in ordered Plücker coordinates

The native Grassmannian convention `G(3,5)` parametrizes rank-two
quotients of a rank-five free module. Its twenty ordered maximal minors
give the original closed immersion into projective 19-space. The ambient
projective space is identified with `P((K^20)*)`, using the dual coordinate
basis reindexed by the native `pluckerIndexEquiv`. No compressed Plücker
model or independently chosen projective variety is substituted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.MukaiGrassmannianPlucker

variable (K : Type u) [Field K]

abbrev OrderedCoordinates := MukaiOrderedMinors.OrderedPair → K
abbrev AmbientForms := Module.Dual K (OrderedCoordinates K)
abbrev ambient : Scheme.{u} := projectiveSpaceOfModule K (AmbientForms K)
abbrev grass : Scheme.{u} := GrassmannianCharts.space K 3 5

/-- The precise dual-coordinate basis, with the native ordering of all
twenty embeddings. -/
def ambientBasis : Module.Basis (Fin (Grassmannian.pluckerDim 3 5 + 1)) K (AmbientForms K) :=
  (Pi.basisFun K MukaiOrderedMinors.OrderedPair).dualBasis.reindex
    (Grassmannian.pluckerIndexEquiv 3 5)

theorem pluckerDim_eq_nineteen : Grassmannian.pluckerDim 3 5 = 19 := by
  norm_num [Grassmannian.pluckerDim,Fintype.card_embedding_eq]

/-- The actual base change of the native integral Plücker morphism. -/
def pluckerOver : grass K ⟶ projectiveSpaceOverRing (Grassmannian.pluckerDim 3 5) (.of K) :=
  pullback.map (terminal.from (Spec (.of K)))
    (terminal.from (Grassmannian.scheme.{u} 3 5))
    (terminal.from (Spec (.of K)))
    (terminal.from (projectiveSpaceAtUniverse.{u} (Grassmannian.pluckerDim 3 5)))
    (𝟙 _) (Grassmannian.pluckerMap 3 5) (𝟙 _) (by simp) (by simp)

instance pluckerOver_isClosedImmersion : IsClosedImmersion (pluckerOver K) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance
    (Grassmannian.isClosedImmersion_pluckerMap 3 5) (Category.id_comp _).symm (by simp)

/-- The same literal Plücker morphism in the projective-space-of-module
coordinates used by the native linear-subspace dimension theorem. -/
def plucker : grass K ⟶ ambient K :=
  pluckerOver K ≫ (basisProjectiveSpaceIso (ambientBasis K)).hom

instance plucker_isClosedImmersion : IsClosedImmersion (plucker K) := by
  dsimp [plucker]
  infer_instance

def image : Set (ambient K) := Set.range (plucker K)

theorem image_isClosed : IsClosed (image K) :=
  (plucker K).isClosedEmbedding.isClosed_range

theorem image_nonempty : (image K).Nonempty :=
  ⟨plucker K (Classical.arbitrary (grass K)),Set.mem_range_self _⟩

/-- The actual native six-dimensional open chart gives the lower
dimension bound on the original closed Plücker image. -/
theorem image_dimension_lower : (6 : WithBot ℕ∞) ≤ topologicalKrullDim (image K) := by
  have he := (plucker K).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _
  exact (MukaiGrassmannianDimension.grass_dimension_lower K).trans_eq he

/-- The genuine K-valued Grassmannian chart point of a two-row matrix.
When the pivot submatrix is identity, the normalized native chart matrix
is literally M, by `GrassmannianCharts.matrixPoint_chartMatrix`. -/
def matrixPoint (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K) :
    Spec (.of K) ⟶ grass K :=
  MukaiGrassmannianPoints.matrixPoint K ι M

@[reassoc (attr := simp)] theorem matrixPoint_projection
    (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K) :
    matrixPoint K ι M ≫ GrassmannianCharts.projection K 3 5 = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem matrixPoint_toIntegral
    (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K) :
    matrixPoint K ι M ≫ GrassmannianCharts.toIntegral K 3 5 =
      GrassmannianCharts.matrixPoint K 3 5 ι M ≫ Grassmannian.chart 3 5 ι :=
  pullback.lift_snd _ _ _

end M9Native.MukaiGrassmannianPlucker
