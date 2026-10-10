module
public import QuantitativeFollowup.AnisotropicVarianceRestartMoments
public import QuantitativeFollowup.AnisotropicVarianceFutureMeasurable
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! The actual finite variance derivatives converge to the Stieltjes
response of the restarted arbitrary-profile diffusion. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def anisotropicRestartVarianceResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : Fin n) : ℝ :=
  (1/2 : ℝ)*(1-(q:ℝ)-∫r,max 0 ((r:ℝ)-(q:ℝ))*
    anisotropicRestartSpinSquare D μ g q x i r∂(μ:Measure Paper.Overlap))

private theorem overlap_positive_part_le_one (q r : Paper.Overlap) :
    max 0 ((r:ℝ)-(q:ℝ))≤1 := max_le (by norm_num) (by linarith [r.property.2,q.property.1])

theorem anisotropicFiniteTailVarianceResponse_clamp_integral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicFiniteTailVarianceResponse D s q P i=
      (1/2 : ℝ)*(1-(q:ℝ)-∫r,max 0 ((r:ℝ)-(q:ℝ))*
        cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme s q q.property) (k+2) P i
          (anisotropicClampOverlap q r)∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap)) := by
  rw [anisotropicFiniteTailVarianceResponse_stieltjes,integral_anisotropicClampedSchemeMeasure]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hqr : q≤r
  · simp only [anisotropicClampOverlap_coe,max_eq_right (show (q:ℝ)≤(r:ℝ) from hqr)]
  · have hrq : (r:ℝ)≤(q:ℝ):=le_of_not_ge hqr
    simp only [anisotropicClampOverlap_coe,max_eq_left hrq,sub_self,max_self,zero_mul,
      max_eq_left (sub_nonpos.mpr hrq)]

theorem tendsto_anisotropicVarianceFiniteTailResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) :
    Tendsto (fun j=>anisotropicFiniteTailVarianceResponse (anisotropicReplaceVariance D i (bj j))
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i) atTop
      (𝓝 (anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i b) μ g q x i)) := by
  let Dj:=fun j=>anisotropicReplaceVariance D i (bj j)
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let P:=anisotropicDisorderInjection n g+anisotropicFieldInjection n x
  let Qj:=fun j r=>cavityFiniteConditionalCoordinateSquare (Dj j)
    (vectorClampedScheme (sj j) q q.property) (vectorDyadicIndex j+3) P i
    (anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r))
  let fj:=fun j (r : Paper.Overlap)=>max 0 ((Paper.parisiGridRound (vectorDyadicIndex j) r:ℝ)-(q:ℝ))*Qj j r
  let f:=fun r : Paper.Overlap=>max 0 ((r:ℝ)-(q:ℝ))*anisotropicRestartSpinSquare (anisotropicReplaceVariance D i b) μ g q x i r
  have hQm j : Measurable (Qj j):=
    (measurable_cavityFiniteConditionalCoordinateSquare _ _ _ _ _).comp
      ((continuous_anisotropicClampOverlap q).measurable.comp (Paper.measurable_parisiGridRound _))
  have hfm j : Measurable (fj j):=
    (measurable_const.max ((measurable_subtype_coe.comp (Paper.measurable_parisiGridRound _)).sub_const _)).mul (hQm j)
  have hQb j r : Qj j r∈Icc (0:ℝ) 1:=cavityFiniteConditionalCoordinateSquare_mem_Icc _ _ _ _ _ _
  have hfb j r : ‖fj j r‖≤(1:ℝ) := by
    have hc:=overlap_positive_part_le_one q (Paper.parisiGridRound (vectorDyadicIndex j) r)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (le_max_left _ _) (hQb j r).1)]
    exact (mul_le_of_le_one_right (le_max_left _ _) (hQb j r).2).trans hc
  have hlim r : Tendsto (fun j=>fj j r) atTop (𝓝 (f r)) := by
    have hr : Tendsto (fun j=>(Paper.parisiGridRound (vectorDyadicIndex j) r:ℝ)) atTop (𝓝 (r:ℝ)):=
      (continuous_subtype_val.tendsto r).comp ((Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex)
    have hc := (tendsto_const_nhds (x:=(0:ℝ))).max (hr.sub_const (q:ℝ))
    by_cases hqr : q<r
    · have hcl j : anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r)=
          Paper.parisiGridRound (vectorDyadicIndex j) r := by
        apply Subtype.ext
        exact max_eq_right (hqr.le.trans (Paper.le_parisiGridRound _ r))
      have hsq:=tendsto_anisotropicVarianceRestart_node_square D μ i hb ht g q r hqr x
      simpa only [fj,Qj,f,hcl] using hc.mul hsq
    · have hrq : (r:ℝ)≤(q:ℝ):=le_of_not_gt hqr
      have hc0 : Tendsto (fun j=>max 0 ((Paper.parisiGridRound (vectorDyadicIndex j) r:ℝ)-(q:ℝ))) atTop (𝓝 0) := by
        simpa only [max_eq_left (sub_nonpos.mpr hrq)] using hc
      have hs:=squeeze_zero (fun j=>mul_nonneg (le_max_left _ _) (hQb j r).1)
        (fun j=>mul_le_of_le_one_right (le_max_left _ _) (hQb j r).2) hc0
      simpa only [fj,f,max_eq_left (sub_nonpos.mpr hrq),zero_mul] using hs
  have hInt:=tendsto_integral_filter_of_dominated_convergence (μ:=(μ:Measure Paper.Overlap))
    (fun _=>(1:ℝ)) (.of_forall fun j=>(hfm j).aestronglyMeasurable)
    (.of_forall fun j=>.of_forall fun r=>hfb j r) (integrable_const _) (.of_forall hlim)
  have he j : anisotropicFiniteTailVarianceResponse (Dj j) (sj j) q P i=
      (1/2 : ℝ)*(1-(q:ℝ)-∫r,fj j r∂(μ:Measure Paper.Overlap)) := by
    rw [anisotropicFiniteTailVarianceResponse_clamp_integral,FRSB.parisiSchemeMeasure_grid_eq]
    rw [Paper.parisiGridMeasure,ProbabilityMeasure.toMeasure_map]
    rw [integral_map_of_stronglyMeasurable (Paper.measurable_parisiGridRound _) ]
    exact ((measurable_const.max (measurable_subtype_coe.sub_const _)).mul
        ((measurable_cavityFiniteConditionalCoordinateSquare _ _ _ _ _).comp
          (continuous_anisotropicClampOverlap q).measurable)).stronglyMeasurable
  change Tendsto (fun j=>anisotropicFiniteTailVarianceResponse (Dj j) (sj j) q P i) atTop _
  simp_rw [he]
  simpa only [anisotropicRestartVarianceResponse,f] using
    ((tendsto_const_nhds (x:=1-(q:ℝ))).sub hInt).const_mul (1/2 : ℝ)

end QuantitativeFollowup
