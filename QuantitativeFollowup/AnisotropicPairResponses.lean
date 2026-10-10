module
public import QuantitativeFollowup.AnisotropicCouplingCoordinates

@[expose] public section

/-! Every actual finite posterior pair-spin moment has a genuine moving-time
arbitrary-profile limit, obtained from unit-coupling derivatives. Original
coupling scales may vanish and no moment convergence is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def anisotropicTailPairResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) : ℝ :=
  fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
    (anisotropicCouplingRescaling D P) (anisotropicCouplingDirection e)

def anisotropicFiniteTailPairResponse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) : ℝ :=
  fderiv ℝ (anisotropicFiniteTailPotential (anisotropicUnitCouplings D) s q)
    (anisotropicCouplingRescaling D P) (anisotropicCouplingDirection e)

def anisotropicFiniteTailSpinKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) : Kernel (AnisotropicParameter n) (Configuration n) :=
  anisotropicFiniteSpinKernel D (vectorClampedScheme s q q.property) (k+2)

instance anisotropicFiniteTailSpinKernel_markov (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) : IsMarkovKernel (anisotropicFiniteTailSpinKernel D s q) :=by
  unfold anisotropicFiniteTailSpinKernel
  infer_instance

theorem anisotropicFiniteTailPairResponse_eq_spinMoment (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    anisotropicFiniteTailPairResponse D s q P e=
      ∫σ,Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2) ∂anisotropicFiniteTailSpinKernel D s q P := by
  unfold anisotropicFiniteTailPairResponse anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped _ s q q.property le_rfl]
  exact anisotropicFinitePairMean_unitCoupling D (vectorClampedScheme s q q.property) (k+2) P e

theorem anisotropicFiniteTailPairResponse_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    anisotropicFiniteTailPairResponse D s (anisotropicSchemeNode s i hi) P e=
      ∫σ,Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2) ∂anisotropicFiniteSpinKernel D s (k+2-i) P := by
  unfold anisotropicFiniteTailPairResponse
  rw [anisotropicFiniteTailPotential_node]
  exact anisotropicFinitePairMean_unitCoupling D s (k+2-i) P e

theorem anisotropicFiniteTailPairResponse_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    ‖anisotropicFiniteTailPairResponse D s q P e‖≤1 := by
  rw [anisotropicFiniteTailPairResponse_eq_spinMoment]
  have hb (σ : Configuration n) :
      ‖Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)‖ ≤ (1:ℝ) := by
    simp only [norm_mul,Real.norm_eq_abs,Paper.abs_spinSign,mul_one,le_refl]
  have h := norm_integral_le_of_norm_le_const
    (μ:=anisotropicFiniteTailSpinKernel D s q P) (C:=1) (.of_forall hb)
  simpa only [probReal_univ,mul_one] using h

theorem continuous_anisotropicTailPairResponse_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : AnisotropicCouplingIndex n) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n=>anisotropicTailPairResponse D μ z.1 z.2 e) := by
  have hD := (continuous_anisotropicMeasureTailDifferential_joint (anisotropicUnitCouplings D) μ).comp
    (continuous_fst.prodMk ((anisotropicCouplingRescaling D).continuous.comp continuous_snd))
  have h := hD.clm_apply (continuous_const (y:=anisotropicCouplingDirection e))
  simpa only [Function.comp_def,anisotropicTailPairResponse] using h

theorem tendsto_anisotropicFiniteTailPairResponse_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : AnisotropicCouplingIndex n)
    {qj : ℕ→Paper.Overlap} {q : Paper.Overlap} {Pj : ℕ→AnisotropicParameter n} {P : AnisotropicParameter n}
    (hq : Tendsto qj atTop (𝓝 q)) (hP : Tendsto Pj atTop (𝓝 P)) :
    Tendsto (fun j=>anisotropicFiniteTailPairResponse D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j) (Pj j) e) atTop
      (𝓝 (anisotropicTailPairResponse D μ q P e)) := by
  have hPs := (anisotropicCouplingRescaling D).continuous.continuousAt.tendsto.comp hP
  have hD := (tendstoUniformly_anisotropicDyadicTailDifferential (anisotropicUnitCouplings D) μ).tendsto_comp
    (continuous_anisotropicMeasureTailDifferential_joint (anisotropicUnitCouplings D) μ).continuousAt
    (hq.prodMk_nhds hPs)
  have hev : Continuous (fun T : AnisotropicParameter n→L[ℝ]ℝ=>T (anisotropicCouplingDirection e)) :=
    continuous_id.clm_apply continuous_const
  have h := hev.continuousAt.tendsto.comp hD
  simpa only [Function.comp_def,anisotropicFiniteTailPairResponse,anisotropicTailPairResponse,
    anisotropicDyadicTailPotential,anisotropicFiniteTailPotential] using h

theorem anisotropicTailPairResponse_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    ‖anisotropicTailPairResponse D μ q P e‖≤1 := by
  apply le_of_tendsto ((tendsto_anisotropicFiniteTailPairResponse_moving D μ e
    (tendsto_const_nhds (x:=q)) (tendsto_const_nhds (x:=P))).norm)
  exact .of_forall fun j=>anisotropicFiniteTailPairResponse_bound D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q P e

theorem tendsto_anisotropicProcessPairResponse_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n) (e : AnisotropicCouplingIndex n)
    {qj : ℕ→Paper.Overlap} {q : Paper.Overlap} (hq : Tendsto qj atTop (𝓝 q)) :
    Tendsto (fun j=>anisotropicFiniteTailPairResponse D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (qj j) (anisotropicFiniteProcessParameter D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j) sample) e)
      atTop (𝓝 (anisotropicTailPairResponse D μ q (anisotropicProcessParameter D μ q sample) e)) :=
  tendsto_anisotropicFiniteTailPairResponse_moving D μ e hq
    (tendsto_anisotropicFiniteProcessParameter_moving_time D μ sample hq)

end QuantitativeFollowup
