module
public import QuantitativeFollowup.AnisotropicSpinPathConditionals

@[expose] public section

/-! The actual full-vector anisotropic magnetization is the conditional
terminal spin and is a martingale, with its genuine zero initial value. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem adapted_anisotropicProcessMagnetization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (anisotropicProcessMagnetization D μ q) := by
  have h := (continuous_anisotropicMeasureTailMagnetization_joint D μ).measurable.comp
    ((measurable_const (a:=q)).prodMk (adapted_anisotropicProcessParameter D μ q))
  change Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
    (fun sample=>anisotropicMeasureTailMagnetization D μ q (anisotropicProcessParameter D μ q sample))
  simpa only [Function.comp_def] using h

theorem anisotropicMeasureTailMagnetization_zero_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) :
    anisotropicMeasureTailMagnetization D μ 0 (anisotropicDisorderInjection n g)=0 := by
  have h := (tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ).tendsto_at
    (0,anisotropicDisorderInjection n g)
  simp_rw [anisotropicFiniteTailMagnetization_clamped,anisotropicMagnetization_zero_field] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem anisotropicProcessMagnetization_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessMagnetization D μ 0 sample=0 := by
  unfold anisotropicProcessMagnetization anisotropicProcessParameter
  simp only [Set.Icc.coe_zero,anisotropicMeasureState_zero,map_zero,add_zero]
  exact anisotropicMeasureTailMagnetization_zero_field D μ sample.1

def anisotropicSpinFiltration (n : ℕ) :
    Filtration Paper.Overlap (inferInstance :
      MeasurableSpace (AnisotropicDisorderBrownianSample n × Configuration n)) where
  seq q := anisotropicSpinPast n (q:ℝ).toNNReal
  mono' _ _ h := MeasurableSpace.comap_mono
    ((anisotropicBrownianFiltration n).mono (Real.toNNReal_mono h))
  le' q := anisotropicSpinPast_le n (q:ℝ).toNNReal

theorem anisotropic_terminal_spin_condExp (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n × Configuration n => spinVector p.2) |
      anisotropicSpinFiltration n q] =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p => anisotropicProcessMagnetization D μ q p.1 := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  letI := anisotropicMeasureSpinPathLaw_probability D μ a
  have hm : Measurable (fun p : AnisotropicDisorderBrownianSample n × Configuration n =>
      spinVector p.2) := (measurable_of_finite spinVector).comp measurable_snd
  have hi : Integrable (fun p : AnisotropicDisorderBrownianSample n × Configuration n =>
      spinVector p.2) P := (integrable_const (Real.sqrt (n:ℝ))).mono'
    hm.aestronglyMeasurable (.of_forall fun p => (norm_spinVector p.2).le)
  have hc (l : Fin n) :
      (fun p => (P[(fun p : AnisotropicDisorderBrownianSample n × Configuration n =>
        spinVector p.2) | anisotropicSpinFiltration n q]) p l) =ᵐ[P]
      fun p => anisotropicProcessMagnetization D μ q p.1 l := by
    have hproj := (EuclideanSpace.proj l).comp_condExp_comm
      (m:=anisotropicSpinFiltration n q) hi
    have hspin := anisotropicMeasureSpinPathLaw_spin_condExp D μ a q l
    exact hproj.trans hspin
  filter_upwards [ae_all_iff.mpr hc] with p hp
  ext l
  exact hp l

theorem anisotropic_joint_spin_mean_martingale (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) :
    Martingale (fun q : Paper.Overlap => fun p :
        AnisotropicDisorderBrownianSample n × Configuration n =>
      anisotropicProcessMagnetization D μ q p.1)
      (anisotropicSpinFiltration n) (anisotropicMeasureSpinPathLaw D μ a) := by
  letI := anisotropicMeasureSpinPathLaw_probability D μ a
  apply (martingale_condExp (fun p : AnisotropicDisorderBrownianSample n × Configuration n =>
    spinVector p.2) (anisotropicSpinFiltration n)
    (anisotropicMeasureSpinPathLaw D μ a)).congr
  · intro q
    exact ((adapted_anisotropicProcessMagnetization D μ q).comp
      (comap_measurable Prod.fst)).stronglyMeasurable
  · intro q
    exact anisotropic_terminal_spin_condExp D μ a q

end QuantitativeFollowup
