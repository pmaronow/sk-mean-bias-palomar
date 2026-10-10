module
public import QuantitativeFollowup.FollowupCavityScalarCovarianceReduction
public import QuantitativeFollowup.ScalarResponseRegrouping

@[expose] public section

/-! The genuine scalar factor in the last response kernel is exactly the
projected covariance printed in the cavity decomposition. This keeps every
strict-future boundary and requires no response identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem scalarFutureCenteredPairing_eq_projectedCovariance (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r l : Paper.Overlap) (hrl : r≤l) :
    scalarFutureCenteredPairing β μ p r l=cavityScalarProjectedCovariance β μ p r l :=by
  have hrl' : (r:ℝ)≤l := hrl
  have he : scalarFutureSquareProcess β μ r l hrl=cavityScalarFutureSquare β μ r l :=by
    funext ω
    change scalarFutureSquare β μ r l hrl (parisiPhysicalSplitState β 0 μ r ω)=
      scalarFutureSquareExtended β μ r l (parisiPhysicalSplitState β 0 μ r ω)
    rw [scalarFutureSquareExtended_eq β μ r l hrl]
  rw [scalarFutureCenteredPairing,dif_pos hrl',he,cavityScalarProjectedCovariance,
    covariance_eq_sub (cavityScalarSquare_memLp_two β μ p) (cavityScalarFutureSquare_memLp_two β μ r l)]
  simp only [scalarCenteredSquare,sub_mul,Pi.mul_apply]
  have hsub := integral_sub ((cavityScalarSquare_memLp_two β μ p).integrable_mul
    (cavityScalarFutureSquare_memLp_two β μ r l))
    (((cavityScalarFutureSquare_memLp_two β μ r l).integrable (by norm_num)).const_mul
      (Gamma β μ p))
  simp only [Pi.mul_apply] at hsub
  rw [hsub,integral_const_mul]
  rfl

theorem scalarResponseKernel7_eq_projectedCovariance (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r l : Paper.Overlap) (hrl : r≤l) :
    scalarResponseKernel7 β μ p r l=cavityScalarProjectedCovariance β μ p r l :=by
  rw [←scalarFutureCenteredPairing_eq_kernel β μ p r l hrl]
  exact scalarFutureCenteredPairing_eq_projectedCovariance β μ p r l hrl

theorem scalarFutureCenteredPairing_strict_future_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) :
    (fun l : Paper.Overlap=>if r<l then scalarFutureCenteredPairing β μ p r l else 0)=
      fun l=>if r<l then cavityScalarProjectedCovariance β μ p r l else 0 :=by
  funext l
  split_ifs with hl
  · exact scalarFutureCenteredPairing_eq_projectedCovariance β μ p r l hl.le
  · rfl

end QuantitativeFollowup
