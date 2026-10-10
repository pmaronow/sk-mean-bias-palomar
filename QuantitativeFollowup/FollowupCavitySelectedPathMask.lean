module
public import QuantitativeFollowup.FollowupCavityPathVarianceCoordinates
public import FourPapersCommon.GaussianSelectedCoordinateScale

@[expose] public section

/-! The selected Brownian coordinate at every independent tree edge,
with coupling disorder excluded from the mask. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

@[reducible] def cavitySelectedEdgeMask (i : Fin n) :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→GaussianCoordinateIndex (Fin n) T→Bool
  | _,.leaf => Empty.elim
  | _,.advance T => Sum.elim (fun l=>decide (l=i)) (cavitySelectedEdgeMask i T)
  | _,.fork T U => Sum.elim (cavitySelectedEdgeMask i T) (cavitySelectedEdgeMask i U)

def cavitySelectedRootPathMask (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T→Bool :=
  Sum.elim (fun _=>false) (cavitySelectedEdgeMask i T)

theorem cavitySelectedEdgeMask_multiplier (i : Fin n) (b : ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (e : GaussianCoordinateIndex (Fin n) T) :
    finiteCascadeEdgeMultiplier (cavityPathVarianceMultiplier i b) T e =
      if cavitySelectedEdgeMask i T e then Real.sqrt b else 1 := by
  induction T with
  | leaf => exact Empty.elim e
  | advance T ih =>
      cases e with
      | inl l => simp [finiteCascadeEdgeMultiplier,cavitySelectedEdgeMask,cavityPathVarianceMultiplier]
      | inr e => exact ih e
  | fork T U ihT ihU =>
      cases e with
      | inl e => exact ihT e
      | inr e => exact ihU e

theorem gaussianSelectedScale_eq_cavityPathDiagonal (i : Fin n) (b : ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)] :
    gaussianSelectedScale (cavitySelectedRootPathMask i T) b =
      finiteGaussianDiagonal (Sum.elim (fun _ : AnisotropicCouplingIndex n=>1)
        (finiteCascadeEdgeMultiplier (cavityPathVarianceMultiplier i b) T)) := by
  apply finiteStateCLM_eq_of_single
  intro e
  have he : EuclideanSpace.single e (1:ℝ)=EuclideanSpace.basisFun _ ℝ e := by
    ext d
    simp [EuclideanSpace.basisFun_apply,PiLp.single_apply]
  rw [finiteGaussianDiagonal_single,he,gaussianSelectedScale_basis]
  congr 1
  cases e with
  | inl l => rfl
  | inr e => exact (cavitySelectedEdgeMask_multiplier i b T e).symm

end QuantitativeFollowup
