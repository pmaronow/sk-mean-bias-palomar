module
public import QuantitativeFollowup.AnisotropicVarianceRestartMoments

@[expose] public section

/-! The native restarted-square limit at and beyond the starting level.
The equality case retains an atom exactly at the vertex and uses the actual
zero-elapsed-time diffusion, rather than a strict-future approximation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem tendsto_anisotropicVarianceRestart_node_square_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) (g : AnisotropicDisorder n)
    (q r : Paper.Overlap) (hqr : q≤r) (x : Field n) :
    Tendsto (fun j=>cavityFiniteConditionalCoordinateSquare
      (anisotropicReplaceVariance D i (bj j))
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
      (vectorDyadicIndex j+3) (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)
      i (Paper.parisiGridRound (vectorDyadicIndex j) r)) atTop
      (𝓝 (anisotropicRestartSpinSquare (anisotropicReplaceVariance D i b) μ g q x i r)) := by
  let Dj:=fun j=>anisotropicReplaceVariance D i (bj j)
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let v:=fun j=>vectorDyadicTimeIndex r j
  let R:=fun j=>anisotropicRestartElapsed (sj j) q (v j)
  let yj:=fun j=>anisotropicInverseNoiseMap (Dj j) x
  let Pj:=fun j sample=>anisotropicFiniteRestartPhysicalParameter (Dj j) (sj j) g q (yj j) (R j) sample
  let rj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) r
  let Mj:=fun j sample=>anisotropicFiniteTailMagnetization (Dj j) (sj j) (rj j) (Pj j sample) i
  have hv j : v j≤vectorDyadicIndex j+3:=(vectorDyadicTimeIndex_le r j).trans (by omega)
  have hqv j : (q:ℝ)≤(sj j).q (v j) := by
    rw [vectorDyadicTimeIndex_node]
    exact hqr.trans (Paper.le_parisiGridRound _ r)
  have hn j : anisotropicSchemeNode (sj j) (v j) (hv j)=rj j :=
    Subtype.ext (vectorDyadicTimeIndex_node μ r j)
  have hR j : R j≤vectorRestartHorizon q := by
    unfold R anisotropicRestartElapsed vectorRestartHorizon
    apply Real.toNNReal_le_toNNReal
    exact sub_le_sub_right (max_le q.property.2 ((sj j).q_le_one (hv j))) _
  have hrj : Tendsto rj atTop (𝓝 r):=(Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex
  have hRt : Tendsto R atTop (𝓝 ((r:ℝ)-(q:ℝ)).toNNReal) := by
    have hh:=(continuous_subtype_val.tendsto r).comp hrj
    have hmax:=((tendsto_const_nhds (x:=(q:ℝ))).max hh).sub_const (q:ℝ)
    have htime:=continuous_real_toNNReal.tendsto _ |>.comp hmax
    have hnode j : (sj j).q (v j)=(rj j:ℝ) := vectorDyadicTimeIndex_node μ r j
    simpa only [R,anisotropicRestartElapsed,hnode,
      max_eq_right (show (q:ℝ)≤(r:ℝ) from hqr),Function.comp_def] using htime
  have hPi sample : Tendsto (fun j=>Pj j sample) atTop
      (𝓝 (anisotropicRestartPhysicalParameter (anisotropicReplaceVariance D i b) μ g q x
        ((r:ℝ)-(q:ℝ)).toNNReal sample)) := by
    exact tendsto_anisotropicVarianceFiniteRestartPhysicalParameter_moving D μ i hb ht g q x sample hR hRt
  have hM sample : Tendsto (fun j=>Mj j sample) atTop
      (𝓝 (anisotropicRestartSpinResponse (anisotropicReplaceVariance D i b) μ g q x i r sample)) := by
    have hh:=tendsto_anisotropicVarianceDyadicTailMagnetization_moving D μ i hb ht (hrj.prodMk_nhds (hPi sample))
    exact (EuclideanSpace.proj i).continuous.tendsto _ |>.comp hh
  have hm j : Measurable (Mj j):= by
    have hm0 := (EuclideanSpace.proj i).measurable.comp
      ((measurable_anisotropicFiniteTailMagnetization (Dj j) (sj j)).comp
        ((measurable_const (a:=rj j)).prodMk
          (measurable_anisotropicFiniteRestartPhysicalParameter (Dj j) (sj j) g q (yj j) (R j))))
    simpa only [Mj,Pj,Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply] using hm0
  have hbd j sample : |Mj j sample|≤1:=anisotropicFiniteTailMagnetization_component_bound _ _ _ _ _
  have hh:=tendsto_integral_filter_of_dominated_convergence (μ:=vectorDisorderBrownianMeasure n)
    (fun _=>(1:ℝ)) (.of_forall fun j=>(hm j).pow_const 2 |>.aestronglyMeasurable)
    (.of_forall fun j=>.of_forall fun sample=>by
      rw [Real.norm_eq_abs,abs_pow]
      simpa using pow_le_pow_left₀ (abs_nonneg _) (hbd j sample) 2)
    (integrable_const _) (.of_forall fun sample=>(hM sample).pow 2)
  have he j : cavityFiniteConditionalCoordinateSquare (Dj j) (vectorClampedScheme (sj j) q q.property)
      (vectorDyadicIndex j+3) (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i (rj j)=
      ∫sample,(Mj j sample)^2∂vectorDisorderBrownianMeasure n := by
    have hP : anisotropicDisorderInjection n g+anisotropicUnitInput (Dj j) (yj j)=
        anisotropicDisorderInjection n g+anisotropicFieldInjection n x := by
      simp only [yj,anisotropicUnitInput,ContinuousLinearMap.comp_apply,anisotropicNoiseMap_inverseNoise]
    have hx:=cavityFiniteRestartCoordinateSquare_node (Dj j) (sj j) g q (yj j) (v j) (hv j) (hqv j) i
    rw [hn j,hP] at hx
    exact hx
  change Tendsto (fun j=>cavityFiniteConditionalCoordinateSquare (Dj j)
    (vectorClampedScheme (sj j) q q.property) (vectorDyadicIndex j+3)
    (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i (rj j)) atTop _
  simp_rw [he]
  exact hh


end HexagonPaper
