module
public import QuantitativeFollowup.AnisotropicVariancePotentialContinuity
public import QuantitativeFollowup.AnisotropicTailHessian

@[expose] public section

/-! Actual C² spatial jets under simultaneous diagonal-variance and dyadic
profile approximation. The covariance perturbation preserves the terminal
energy map, so all derivative regularity constants are uniform in it. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendstoUniformly_anisotropicVarianceDyadicTailDifferential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) :
    TendstoUniformly (fun j=>fun z : Paper.Overlap×AnisotropicParameter n=>
      fderiv ℝ (anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ z.1 j) z.2)
      (fun z=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ z.1) z.2)
        atTop := by
  let F:=fun j q=>anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ q j
  let G:=fun q=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
  have hu : TendstoUniformly (fun j (z : Paper.Overlap×AnisotropicParameter n)=>F j z.1 z.2)
      (fun z=>G z.1 z.2) atTop := tendstoUniformly_anisotropicVarianceDyadicTailPotential D μ i hb ht
  have hf j q : ContDiff ℝ 2 (F j q):=
    (contDiff_anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ q j).of_le (by simp)
  have hL j q : LipschitzWith (‖anisotropicEnergyMap D‖₊^2) (fderiv ℝ (F j q)) := by
    simpa only [F,anisotropicReplaceVariance_energyMap] using
      anisotropicDyadicTailPotential_fderiv_lipschitz (anisotropicReplaceVariance D i (bj j)) μ q j
  apply tendstoUniformly_fderiv_family F _ (fun j q=>(hf j q).differentiable (by norm_num))
    (‖anisotropicEnergyMap D‖₊^2) hL
    ((tendstoUniformlyOn_univ.mpr hu).uniformCauchySeqOn)
  intro z
  obtain ⟨g',hg,hd,_⟩:=exists_uniform_derivative_limit (fun j=>F j z.1) (G z.1)
    (fun j=>hf j z.1) (‖anisotropicEnergyMap D‖₊^2) (fun j=>hL j z.1)
    (hu.comp (fun P=>(z.1,P)))
  have he : g'=fderiv ℝ (G z.1):=funext fun P=>(hd P).fderiv.symm
  rw [he] at hg
  exact hg.tendsto_at z.2

theorem tendstoUniformly_anisotropicVarianceDyadicTailSecondDifferential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b)) :
    TendstoUniformly (fun j=>fun z : Paper.Overlap×AnisotropicParameter n=>
      fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential
        (anisotropicReplaceVariance D i (bj j)) μ z.1 j)) z.2)
      (fun z=>fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential
        (anisotropicReplaceVariance D i b) μ z.1)) z.2) atTop := by
  let F:=fun j q=>fderiv ℝ (anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ q j)
  let G:=fun q=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q)
  have hu : TendstoUniformly (fun j (z : Paper.Overlap×AnisotropicParameter n)=>F j z.1 z.2)
      (fun z=>G z.1 z.2) atTop := tendstoUniformly_anisotropicVarianceDyadicTailDifferential D μ i hb ht
  have hf j q : ContDiff ℝ 2 (F j q):=
    (contDiff_anisotropicDyadicTailPotential (anisotropicReplaceVariance D i (bj j)) μ q j).fderiv_right (by simp)
  have hL j q : LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3) (fderiv ℝ (F j q)) := by
    dsimp only [F,anisotropicDyadicTailPotential]
    rw [anisotropicTailRecursion_eq_clamped _ _ q q.property le_rfl]
    simpa only [anisotropicReplaceVariance_energyMap] using
      anisotropicFinitePotential_secondDifferential_lipschitz (anisotropicReplaceVariance D i (bj j))
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property) _
  apply tendstoUniformly_fderiv_family F _ (fun j q=>(hf j q).differentiable (by norm_num))
    (8*‖anisotropicEnergyMap D‖₊^3) hL
    ((tendstoUniformlyOn_univ.mpr hu).uniformCauchySeqOn)
  intro z
  obtain ⟨g',hg,hd,_⟩:=exists_uniform_derivative_limit (fun j=>F j z.1) (G z.1)
    (fun j=>hf j z.1) (8*‖anisotropicEnergyMap D‖₊^3) (fun j=>hL j z.1)
    (hu.comp (fun P=>(z.1,P)))
  have he : g'=fderiv ℝ (G z.1):=funext fun P=>(hd P).fderiv.symm
  rw [he] at hg
  exact hg.tendsto_at z.2

theorem tendsto_anisotropicVarianceDyadicTailDifferential_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b))
    {zj : ℕ→Paper.Overlap×AnisotropicParameter n} {z : Paper.Overlap×AnisotropicParameter n}
    (hz : Tendsto zj atTop (𝓝 z)) :
    Tendsto (fun j=>fderiv ℝ (anisotropicDyadicTailPotential
      (anisotropicReplaceVariance D i (bj j)) μ (zj j).1 j) (zj j).2) atTop
      (𝓝 (fderiv ℝ (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ z.1) z.2)) :=
  (tendstoUniformly_anisotropicVarianceDyadicTailDifferential D μ i hb ht).tendsto_comp
    (continuous_anisotropicMeasureTailDifferential_joint (anisotropicReplaceVariance D i b) μ).continuousAt hz

theorem tendsto_anisotropicVarianceDyadicTailSecondDifferential_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) {bj : ℕ→ℝ} {b : ℝ}
    (hb : 0<b) (ht : Tendsto bj atTop (𝓝 b))
    {zj : ℕ→Paper.Overlap×AnisotropicParameter n} {z : Paper.Overlap×AnisotropicParameter n}
    (hz : Tendsto zj atTop (𝓝 z)) :
    Tendsto (fun j=>fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential
      (anisotropicReplaceVariance D i (bj j)) μ (zj j).1 j)) (zj j).2) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential
        (anisotropicReplaceVariance D i b) μ z.1)) z.2)) :=
  (tendstoUniformly_anisotropicVarianceDyadicTailSecondDifferential D μ i hb ht).tendsto_comp
    (continuous_anisotropicMeasureTailSecondDifferential_joint (anisotropicReplaceVariance D i b) μ).continuousAt hz

end QuantitativeFollowup
