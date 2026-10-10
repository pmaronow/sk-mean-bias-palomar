module
public import QuantitativeFollowup.FollowupCavityRestProcess
public import QuantitativeFollowup.AnisotropicVarianceRestartConditional
public import QuantitativeFollowup.AnisotropicRestartLevelContinuity

@[expose] public section

/-! Genuine rest-system future self-overlap means. Joint measurability in
both levels is derived from the actual measurable Picard construction;
the conditional expectation is the constructed full-past continuation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

private def cavityRestFutureDrift (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (z : Paper.Overlap×AnisotropicRestartNoiseData n) (s : ℝ) (y : Field n) : Field n :=
  anisotropicRestartNoiseDrift D μ z.1 z.2 s y

private theorem measurable_cavityRestFutureDrift (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : (ℝ×Field n)×(Paper.Overlap×AnisotropicRestartNoiseData n)=>
      cavityRestFutureDrift D μ z.2 z.1.1 z.1.2) := by
  let t : (ℝ×Field n)×(Paper.Overlap×AnisotropicRestartNoiseData n)→ℝ≥0 :=
    fun z=>(z.2.1:ℝ).toNNReal+z.1.1.toNNReal
  have ht : Measurable t := by unfold t;fun_prop
  have hw : Measurable (fun z : (ℝ×Field n)×(Paper.Overlap×AnisotropicRestartNoiseData n)=>
      vectorContinuousNoise z.2.2.2 z.1.1) :=
    continuous_vectorContinuousNoise.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd.snd.snd)
  have hy := (measurable_snd.snd.fst.snd.add measurable_fst.snd).add hw
  have hP := ((anisotropicDisorderInjection n).measurable.comp
      measurable_snd.snd.fst.fst).add
    ((anisotropicFieldInjection n).measurable.comp ((anisotropicNoiseMap D).measurable.comp hy))
  have hq : Measurable (fun z : (ℝ×Field n)×(Paper.Overlap×AnisotropicRestartNoiseData n)=>
      projIcc (0:ℝ) 1 zero_le_one (t z)) := by fun_prop
  have hM := (measurable_anisotropicMeasureTailMagnetization D μ).comp (hq.prodMk hP)
  have hC := (Paper.parisiCDF_monotone μ).measurable.comp
    (NNReal.continuous_coe.measurable.comp ht)
  have hh := hC.smul ((anisotropicNoiseMap D).measurable.comp hM)
  convert hh using 1
  funext z
  simp only [cavityRestFutureDrift,anisotropicRestartNoiseDrift,vectorContinuousNoiseDrift,
    vectorTimeShiftDriftData,anisotropicWhitenedDriftData,anisotropicWhitenedDrift,
    t,Function.comp_def,one_smul,Pi.smul_def']
  rfl

theorem measurable_cavityRestExtendedFutureState (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : ℝ×(Paper.Overlap×AnisotropicRestartNoiseData n)=>
      anisotropicExtendedRestartNoiseStatePath D μ z.2.2.1.1 z.2.1 z.2.2.1.2 z.2.2.2 z.1) := by
  have hc := VectorIntegralPicard.measurable_uncurry_solution_compProj
    (T:=1) zero_le_one (0:Field n) (cavityRestFutureDrift D μ)
    (fun z=>bounded_anisotropicRestartNoiseDrift D μ z.1 z.2)
    (measurable_cavityRestFutureDrift D μ)
  have hn : Measurable (fun z : ℝ×(Paper.Overlap×AnisotropicRestartNoiseData n)=>
      vectorContinuousNoise z.2.2.2 z.1) := continuous_vectorContinuousNoise.measurable.comp
    (measurable_fst.prodMk measurable_snd.snd.snd)
  have hh := (measurable_snd.snd.fst.snd.add hc).add hn
  convert hh using 1
  funext z
  simp only [anisotropicExtendedRestartNoiseStatePath,vectorNoiseStatePath,
    one_smul,Pi.add_apply]
  rfl

def cavityRestFutureNoiseSpin (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (i : Fin n) (ω : AnisotropicDisorderBrownianSample n)
    (W : VectorWienerPath n) : ℝ :=
  anisotropicMeasureTailMagnetization D μ p
    (anisotropicDisorderInjection n ω.1+anisotropicUnitInput D
      (anisotropicExtendedRestartNoiseStatePath D μ ω.1 r
        (anisotropicInverseNoiseMap D (anisotropicMeasureState D μ r ω)) W
        ((p:ℝ)-(r:ℝ)))) i

theorem measurable_cavityRestFutureNoiseSpin (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap×AnisotropicDisorderBrownianSample n)×VectorWienerPath n=>
      cavityRestFutureNoiseSpin D μ z.1.1 z.1.2.1 i z.1.2.2 z.2) := by
  have harg : Measurable (fun z : (Paper.Overlap×Paper.Overlap×AnisotropicDisorderBrownianSample n)×VectorWienerPath n=>
      ((z.1.1:ℝ),z.1.2.2)) := by fun_prop
  have hs := (measurable_uncurry_anisotropicMeasureState D μ).comp harg
  have hx := (anisotropicInverseNoiseMap D).measurable.comp hs
  have he : Measurable (fun z : (Paper.Overlap×Paper.Overlap×AnisotropicDisorderBrownianSample n)×VectorWienerPath n=>
      (z.1.2.1:ℝ)-(z.1.1:ℝ)) := by fun_prop
  have hz := (measurable_cavityRestExtendedFutureState D μ).comp
    (he.prodMk (measurable_fst.fst.prodMk
      ((measurable_fst.snd.snd.fst.prodMk hx).prodMk measurable_snd)))
  have hP := ((anisotropicDisorderInjection n).measurable.comp
      measurable_fst.snd.snd.fst).add ((anisotropicUnitInput D).measurable.comp hz)
  exact (EuclideanSpace.proj i).measurable.comp
    ((measurable_anisotropicMeasureTailMagnetization D μ).comp
      (measurable_fst.snd.fst.prodMk hP))

def cavityRestFutureSquare (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (ω : AnisotropicDisorderBrownianSample n) : ℝ :=
  (∑i : Fin n,∫W,(cavityRestFutureNoiseSpin D μ r p i ω W)^2 ∂vectorWienerMeasure n)/(n:ℝ)

theorem measurable_cavityRestFutureSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      cavityRestFutureSquare D μ z.1 z.2.1 z.2.2) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_cavityRestFutureNoiseSpin D μ i).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem cavityRestFutureSquare_mem_unit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) (ω : AnisotropicDisorderBrownianSample n) :
    cavityRestFutureSquare D μ r p ω∈Icc (0:ℝ) 1 := by
  have hi (i : Fin n) : (∫W,(cavityRestFutureNoiseSpin D μ r p i ω W)^2 ∂vectorWienerMeasure n)∈Icc (0:ℝ) 1 := by
    refine ⟨integral_nonneg fun _=>sq_nonneg _,?_⟩
    have hb (W : VectorWienerPath n) : ‖(cavityRestFutureNoiseSpin D μ r p i ω W)^2‖≤(1:ℝ) := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (anisotropicMeasureTailMagnetization_component_bound D μ p _ i)
    have hh := norm_integral_le_of_norm_le_const (μ:=vectorWienerMeasure n) (.of_forall hb)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh)
  constructor
  · unfold cavityRestFutureSquare;positivity
  · by_cases hn : n=0
    · simp [cavityRestFutureSquare,hn]
    · unfold cavityRestFutureSquare
      apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hi i).2)

theorem cavityRestFutureSquare_eq_conditional_square (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) (hrp : r≤p)
    (ω : AnisotropicDisorderBrownianSample n) :
    cavityRestFutureSquare D μ r p ω=
      (∑i : Fin n,anisotropicRestartConditionalSpinSquare D μ r p i ω)/(n:ℝ) := by
  unfold cavityRestFutureSquare
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact .of_forall fun W=>by
    dsimp only
    unfold cavityRestFutureNoiseSpin anisotropicRestartNoiseSpinResponse
    rw [anisotropicRestartNoiseStatePath_eq_extended D μ ω.1 r
      (anisotropicInverseNoiseMap D (anisotropicMeasureState D μ r ω)) W
      ((p:ℝ)-(r:ℝ)) ⟨sub_nonneg.mpr hrp,sub_le_sub_right p.property.2 _⟩]

theorem cavityRestFutureSquare_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap) (hrp : r≤p) :
    (anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ p|
      anisotropicBrownianFiltration n (r:ℝ).toNNReal]
      =ᵐ[anisotropicMeasureSampleLaw D μ a] cavityRestFutureSquare D μ r p := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let m:=anisotropicBrownianFiltration n (r:ℝ).toNNReal
  let X:=fun i : Fin n=>fun ω : AnisotropicDisorderBrownianSample n=>
    (anisotropicProcessSpinResponse D μ p i ω)^2
  have hi (i : Fin n) : Integrable (X i) P :=
    (integrable_const 1).mono' ((measurable_anisotropicProcessSpinResponse D μ p i).pow_const 2).aestronglyMeasurable
      (.of_forall fun ω=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr
          (anisotropicMeasureTailMagnetization_component_bound D μ p _ i))
  have hs:=condExp_finsetSum (μ:=P) (s:=Finset.univ) (fun i _=>hi i) m
  have hc:=condExp_smul (μ:=P) ((n:ℝ)⁻¹) (∑i : Fin n,X i) m
  have hall:=ae_all_iff.2 fun i : Fin n=>
    anisotropicRestartConditionalSpinSquare_condExp D μ a r p hrp i
  have he : cavityRestSelfOverlap D μ p=(n:ℝ)⁻¹ •(∑i : Fin n,X i) := by
    funext ω
    simp only [cavityRestSelfOverlap,anisotropicSelectedMeanSquare,Finset.card_univ,
      Fintype.card_fin,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,X,div_eq_mul_inv,mul_comm]
    rfl
  rw [he]
  filter_upwards [hc,hs,hall] with ω hc hs hall
  rw [hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hs,cavityRestFutureSquare_eq_conditional_square D μ r p hrp ω]
  simp only [Finset.sum_apply,div_eq_mul_inv,mul_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _=>hall i)

end QuantitativeFollowup
