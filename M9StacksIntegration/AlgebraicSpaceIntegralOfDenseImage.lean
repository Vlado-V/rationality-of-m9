module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace

/-! Actual native integrality from a genuine dense irreducible image.
Continuity is derived for the actual native morphism. Reducedness and
decency remain the genuine target properties supplied by their separate
producers; no target integrality or irreducibility is assumed. -/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
attribute [local instance] Space.pointTopology

namespace M9Native.AlgebraicSpaceIntegralOfDenseImage

universe u
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The actual image of an irreducible native source makes the actual
target irreducible when that image is dense. -/
theorem irreducible_of_dense_image (f : X ⟶ Y)
    (hX : IrreducibleSpace (Space.points B S hS X.obj))
    (hd : DenseRange (Space.pointsMap B S hS X.obj f.hom)) :
    IrreducibleSpace (Space.points B S hS Y.obj) := by
  letI := hX
  have hi := (IrreducibleSpace.isIrreducible_univ (Space.points B S hS X.obj)).image
    (Space.pointsMap B S hS X.obj f.hom)
    (Space.continuous_pointsMap B S hS f.hom).continuousOn
  have hc := hi.closure
  rw [Set.image_univ, hd.closure_range] at hc
  exact (irreducibleSpace_def _).2 hc

/-- The three defining native properties of integrality are proved from
the genuine dense image and actual reduced/decent target. -/
theorem integral_of_dense_irreducible_image (f : X ⟶ Y)
    (hX : IrreducibleSpace (Space.points B S hS X.obj))
    (hd : DenseRange (Space.pointsMap B S hS X.obj f.hom))
    (hr : Space.HasEtaleLocalProperty B S hS Y.obj (fun Z : Scheme.{u} => IsReduced Z))
    (hdec : Space.IsDecentSpace B S hS Y.obj) :
    Space.IsIntegralSpace B S hS Y.obj :=
  ⟨hr, hdec, irreducible_of_dense_image B S hS f hX hd⟩

/-- An actual integral parameter space gives the same actual integral
target after proving density and the target's reducedness and decency. -/
theorem integral_of_dense_integral_image (f : X ⟶ Y)
    (hX : Space.IsIntegralSpace B S hS X.obj)
    (hd : DenseRange (Space.pointsMap B S hS X.obj f.hom))
    (hr : Space.HasEtaleLocalProperty B S hS Y.obj (fun Z : Scheme.{u} => IsReduced Z))
    (hdec : Space.IsDecentSpace B S hS Y.obj) :
    Space.IsIntegralSpace B S hS Y.obj :=
  integral_of_dense_irreducible_image B S hS f hX.2.2 hd hr hdec

end M9Native.AlgebraicSpaceIntegralOfDenseImage
