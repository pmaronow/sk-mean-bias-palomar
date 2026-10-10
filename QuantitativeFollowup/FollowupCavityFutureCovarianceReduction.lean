module
public import QuantitativeFollowup.FollowupCavityResidualPenaltyPrinted
public import QuantitativeFollowup.FollowupCavityRestCovariance
public import FourPapersCommon.ConditionalCovarianceResidual

@[expose] public section

/-! Genuine full-past conditional projections identify the printed Theta
bracket. No covariance sign or response identity is supplied as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem cavityRestSelfOverlap_memLp_two (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    MemLp (cavityRestSelfOverlap D μ p) 2 (anisotropicMeasureSampleLaw D μ a):=
  MemLp.of_bound (measurable_cavityRestSelfOverlap D μ p).aestronglyMeasurable 1
    (.of_forall (cavityRestSelfOverlap_norm_le D μ p))

 theorem cavityRestFutureSquare_memLp_two (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap) :
    MemLp (cavityRestFutureSquare D μ r p) 2 (anisotropicMeasureSampleLaw D μ a) := by
  have hm : Measurable (cavityRestFutureSquare D μ r p):=by
    have hmap : Measurable (fun ω : AnisotropicDisorderBrownianSample n=>(r,(p,ω))):=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    have hh:=(measurable_cavityRestFutureSquare D μ).comp
      hmap
    exact hh
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  exact .of_forall fun ω=>by
    rw [Real.norm_of_nonneg (cavityRestFutureSquare_mem_unit D μ r p ω).1]
    exact (cavityRestFutureSquare_mem_unit D μ r p ω).2

 def cavityRestProjectedCovariance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l p : Paper.Overlap) : ℝ:=
  covariance (cavityRestFutureSquare D μ r l) (cavityRestSelfOverlap D μ p)
    (anisotropicMeasureSampleLaw D μ a)

 theorem cavityRestProjectedCovariance_sub_eq_residual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap)
    (hrp : r≤p) (hrl : r≤l) :
    cavityRestProjectedCovariance D μ a r l p-
      covariance (cavityRestSelfOverlap D μ l) (cavityRestSelfOverlap D μ p)
        (anisotropicMeasureSampleLaw D μ a)=
      -cavityRestConditionalCovariance D μ a r p l := by
  have he:=covariance_conditional_residual (anisotropicMeasureSampleLaw D μ a)
    (anisotropicBrownianFiltration n (r:ℝ).toNNReal) ((anisotropicBrownianFiltration n).le _)
    (cavityRestSelfOverlap_memLp_two D μ a p) (cavityRestSelfOverlap_memLp_two D μ a l)
    (cavityRestFutureSquare_memLp_two D μ a r p) (cavityRestFutureSquare_memLp_two D μ a r l)
    (cavityRestFutureSquare_condExp D μ a r p hrp) (cavityRestFutureSquare_condExp D μ a r l hrl)
  change covariance (cavityRestFutureSquare D μ r l) (cavityRestSelfOverlap D μ p) _-
    covariance (cavityRestSelfOverlap D μ l) (cavityRestSelfOverlap D μ p) _=_
  rw [covariance_comm (cavityRestFutureSquare D μ r l),
    covariance_comm (cavityRestSelfOverlap D μ l)]
  exact he

 theorem cavityRestProjectedCovariance_past (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap)
    (hpr : p≤r) (hrl : r≤l) :
    cavityRestProjectedCovariance D μ a r l p=
      covariance (cavityRestSelfOverlap D μ l) (cavityRestSelfOverlap D μ p)
        (anisotropicMeasureSampleLaw D μ a) := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n):=inferInstance
  let m:=anisotropicBrownianFiltration n (r:ℝ).toNNReal
  have hm : m ≤ ambient :=
    (anisotropicBrownianFiltration n).le _
  have hx : Measurable[m] (cavityRestSelfOverlap D μ p):=
    (continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp
      ((adapted_anisotropicProcessMagnetization D μ p).mono
        ((anisotropicBrownianFiltration n).mono (Real.toNNReal_mono hpr)) le_rfl)
  have hc:=cavityRestFutureSquare_condExp D μ a r l hrl
  have hp:=integral_conditional_projection_mul
    (m₀:=ambient) P m hm
    (cavityRestSelfOverlap_memLp_two D μ a l) (cavityRestSelfOverlap_memLp_two D μ a p)
    (cavityRestFutureSquare_memLp_two D μ a r l) hx.aestronglyMeasurable hc
  have hmean : (∫ω,cavityRestFutureSquare D μ r l ω ∂P)=
      ∫ω,cavityRestSelfOverlap D μ l ω ∂P:=
    (integral_congr_ae hc.symm).trans (integral_condExp hm)
  unfold cavityRestProjectedCovariance
  rw [covariance_eq_sub (cavityRestFutureSquare_memLp_two D μ a r l)
    (cavityRestSelfOverlap_memLp_two D μ a p),
    covariance_eq_sub (cavityRestSelfOverlap_memLp_two D μ a l)
      (cavityRestSelfOverlap_memLp_two D μ a p),hmean]
  exact congrArg (fun x : ℝ=>x-(∫ω,cavityRestSelfOverlap D μ l ω ∂P)*
    (∫ω,cavityRestSelfOverlap D μ p ω ∂P)) hp.symm

end QuantitativeFollowup
