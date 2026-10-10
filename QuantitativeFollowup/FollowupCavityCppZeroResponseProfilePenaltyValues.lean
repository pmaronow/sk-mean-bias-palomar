module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileFutureValues
public import QuantitativeFollowup.FollowupCavityRestResidualCovariance
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals
public import QuantitativeFollowup.ScalarProcessContinuity

@[expose] public section

/-! The actual scalar/rest conditional residual covariance survives the
prescribed-atom quantizer. Equal-time mask values are retained exactly;
the strict-order relation is eventually unchanged on the fixed base law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper FRSB
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem continuous_cavityScalarFutureSquare_profile (β : ℝ) (ω : Paper.BrownianSample) :
    Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>
      cavityScalarFutureSquare β z.1 z.2.1 z.2.2 ω) := by
  have hm : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  have hx := (continuous_scalarPhysicalSplitState_parameter β 0 ω).comp hm
  have hi : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>
      (z.1,(z.2.1,(z.2.2,parisiPhysicalSplitState β 0 z.1 z.2.1 ω)))) :=
    continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_snd.snd.prodMk hx))
  have hh := (continuous_scalarFutureSquareExtended β).comp hi
  exact hh.congr (fun z=>rfl)

theorem continuous_cavityScalarFutureMean_profile (β : ℝ) :
    Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>
      cavityScalarFutureMean β z.1 z.2.1 z.2.2) := by
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure) (bound:=fun _=>(1:ℝ))
  · intro z
    have hm : Measurable (fun ω : Paper.BrownianSample=>(z.2,ω)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_cavityScalarFutureSquare β z.1).comp hm).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>by
      rw [Real.norm_of_nonneg (cavityScalarFutureSquare_mem_unit β z.1 z.2.1 z.2.2 ω).1]
      exact (cavityScalarFutureSquare_mem_unit β z.1 z.2.1 z.2.2 ω).2
  · exact integrable_const _
  · exact .of_forall (continuous_cavityScalarFutureSquare_profile β)

theorem tendsto_cavityScalarFutureCenteredTail_preserving (β : ℝ)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (r p : Paper.Overlap)
    (ω : Paper.BrownianSample) :
    Tendsto (fun N=>cavityScalarFutureCenteredTail β (FRSB.preservingMeasure μ S N)
      (FRSB.preservingRound S N r) (ω,FRSB.preservingRound S N p)) atTop
      (𝓝 (cavityScalarFutureCenteredTail β μ r (ω,p))) := by
  have hz := (FRSB.tendsto_preservingMeasure μ S).prodMk_nhds
    ((FRSB.tendsto_preservingRound S r).prodMk_nhds (FRSB.tendsto_preservingRound S p))
  have ht := ((continuous_cavityScalarFutureSquare_profile β ω).tendsto _ |>.comp hz).sub
    ((continuous_cavityScalarFutureMean_profile β).tendsto _ |>.comp hz)
  dsimp only [Function.comp_def] at ht
  by_cases hrp : r<p
  · simp only [cavityScalarFutureCenteredTail,if_pos hrp]
    apply Tendsto.congr' _ ht
    exact (nativeStreaming_round_lt_eventually S r p).mono fun N hN=>by
      simp only [cavityScalarFutureCenteredTail,if_pos (hN.mpr hrp)]
  · simp only [cavityScalarFutureCenteredTail,if_neg hrp]
    apply Tendsto.congr' _ tendsto_const_nhds
    exact (nativeStreaming_round_lt_eventually S r p).mono fun N hN=>by
      simp only [cavityScalarFutureCenteredTail,if_neg (not_congr hN |>.mpr hrp)]

theorem tendsto_cavityRestFutureResidualTail_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (r p : Paper.Overlap)
    (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun N=>cavityRestFutureResidualTail D (FRSB.preservingMeasure μ S N)
      (FRSB.preservingRound S N r) (ω,FRSB.preservingRound S N p)) atTop
      (𝓝 (cavityRestFutureResidualTail D μ r (ω,p))) := by
  have hμ := FRSB.tendsto_preservingMeasure μ S
  have hr := FRSB.tendsto_preservingRound S r
  have hp := FRSB.tendsto_preservingRound S p
  have hs : Tendsto (fun N=>cavityRestSelfOverlap D (FRSB.preservingMeasure μ S N)
      (FRSB.preservingRound S N p) ω) atTop (𝓝 (cavityRestSelfOverlap D μ p ω)) :=
    continuous_eval.tendsto _ |>.comp
      ((tendsto_cavityRestOverlapPath_profile D hμ ω).prodMk_nhds hp)
  have hf := tendsto_cavityRestFutureSquare_profile_level D hμ (hr.min hp) hp
    (fun _=>min_le_right _ _) (min_le_right r p) ω
  by_cases hrp : r<p
  · have ht := hs.sub hf
    simp only [min_eq_left hrp.le] at ht
    simp only [cavityRestFutureResidualTail,if_pos hrp]
    apply Tendsto.congr' _ ht
    exact (nativeStreaming_round_lt_eventually S r p).mono fun N hN=>by
      simp only [cavityRestFutureResidualTail,if_pos (hN.mpr hrp),min_eq_left (hN.mpr hrp).le]
  · simp only [cavityRestFutureResidualTail,if_neg hrp]
    apply Tendsto.congr' _ tendsto_const_nhds
    exact (nativeStreaming_round_lt_eventually S r p).mono fun N hN=>by
      simp only [cavityRestFutureResidualTail,if_neg (not_congr hN |>.mpr hrp)]

theorem tendsto_cavityScalarFutureCovariance_preserving (β : ℝ)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (r p l : Paper.Overlap) :
    Tendsto (fun N=>cavityScalarFutureCovariance β (FRSB.preservingMeasure μ S N)
      (FRSB.preservingRound S N r) (FRSB.preservingRound S N p) (FRSB.preservingRound S N l))
      atTop (𝓝 (cavityScalarFutureCovariance β μ r p l)) := by
  apply tendsto_integral_of_dominated_convergence (fun _=>(1:ℝ))
  · intro N
    have hm (s : Paper.Overlap) := (measurable_cavityScalarFutureCenteredTail β
      (FRSB.preservingMeasure μ S N)).comp
      ((measurable_const (a:=FRSB.preservingRound S N r)).prodMk
        (measurable_id.prodMk (measurable_const (a:=FRSB.preservingRound S N s))))
    exact ((hm p).mul (hm l)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact .of_forall fun ω=>by
      rw [norm_mul]
      exact (mul_le_mul (cavityScalarFutureCenteredTail_norm_le β _ _ _)
        (cavityScalarFutureCenteredTail_norm_le β _ _ _) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · exact .of_forall fun ω=>
      (tendsto_cavityScalarFutureCenteredTail_preserving β μ S r p ω).mul
        (tendsto_cavityScalarFutureCenteredTail_preserving β μ S r l ω)

theorem tendsto_cavityRestResidualCovariance_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (a : ℝ) (r p l : Paper.Overlap) :
    Tendsto (fun N=>cavityRestResidualCovariance D (FRSB.preservingMeasure μ S N) a
      (FRSB.preservingRound S N r) (FRSB.preservingRound S N p) (FRSB.preservingRound S N l))
      atTop (𝓝 (cavityRestResidualCovariance D μ a r p l)) := by
  refine tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D
    (FRSB.tendsto_preservingMeasure μ S) a _ _ ?_ 1 (by norm_num) ?_ ?_
  · intro N
    have hm (s : Paper.Overlap) := (measurable_cavityRestFutureResidualTail D
      (FRSB.preservingMeasure μ S N)).comp
      ((measurable_const (a:=FRSB.preservingRound S N r)).prodMk
        (measurable_id.prodMk (measurable_const (a:=FRSB.preservingRound S N s))))
    exact ((hm p).mul (hm l)).aestronglyMeasurable
  · intro N ω
    rw [norm_mul]
    exact (mul_le_mul (cavityRestFutureResidualTail_norm_le D _ _ _)
      (cavityRestFutureResidualTail_norm_le D _ _ _) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · exact .of_forall fun ω=>
      (tendsto_cavityRestFutureResidualTail_preserving D μ S r p ω).mul
        (tendsto_cavityRestFutureResidualTail_preserving D μ S r l ω)

end QuantitativeFollowup
