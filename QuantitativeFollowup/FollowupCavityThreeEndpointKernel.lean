module
public import QuantitativeFollowup.FollowupCavityThreeEndpointRestart
public import QuantitativePaper.VectorConditionalObservableDensity
public import QuantitativePaper.VectorConditionalReplicaMoments
public import QuantitativePaper.VectorNoiseStateDriftCongruence
public import FourPapersCommon.BoundedAffineConditionalVariance

@[expose] public section

/-! The completed SK continuation retains a fresh entire Wiener path.
Its probability law is derived from the actual restarted Picard state and
terminal Gibbs kernel, including singular or unused initial disorder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cavityVectorEndpointAdvance (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (z : VectorState n×VectorWienerPath n) : VectorState n :=
  (z.1.1,vectorNoiseRestartStatePath (vectorMeasureDriftData μ β t ht)
    (Real.sqrt ((1-t)*β^2)) q z (1-(q:ℝ)))

theorem measurable_cavityVectorEndpointAdvance (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Measurable (cavityVectorEndpointAdvance (n:=n) μ β t ht q) :=
  measurable_fst.fst.prodMk
    ((measurable_uncurry_vectorNoiseRestartStatePath _ _ q).comp
      (measurable_const.prodMk measurable_id))

def cavityVectorEndpointSpinKernel (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : Kernel (VectorState n) (Configuration n) :=
  (terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
    (measurable_vectorTerminalExponent_state n β t)) ∘ₖ
      independentNoiseKernel (vectorWienerMeasure n) (cavityVectorEndpointAdvance μ β t ht q)

instance cavityVectorEndpointSpinKernel_markov (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    IsMarkovKernel (cavityVectorEndpointSpinKernel (n:=n) μ β t ht q) := by
  unfold cavityVectorEndpointSpinKernel
  haveI:=isMarkovKernel_independentNoiseKernel (vectorWienerMeasure n)
    (cavityVectorEndpointAdvance μ β t ht q)
    (measurable_cavityVectorEndpointAdvance μ β t ht q)
  infer_instance

theorem standardSKOffDiagonalEndpointSpinKernel (μ : Paper.ParisiMeasure)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (z : AnisotropicObservationState n) :
    anisotropicObservationTerminalSpinKernel (standardSKOffDiagonalModel n β t hβ ht) μ q z=
      cavityVectorEndpointSpinKernel μ β t ht.le q
        (standardSKOffDiagonalCompression z.1,Real.sqrt ((1-t)*β^2) • z.2) := by
  ext A hA
  rw [anisotropicObservationTerminalSpinKernel,cavityVectorEndpointSpinKernel,
    Kernel.comp_apply' _ _ _ hA,Kernel.comp_apply' _ _ _ hA,
    anisotropicObservationTransition_apply,
    independentNoiseKernel_apply _ _ (measurable_cavityVectorEndpointAdvance μ β t ht.le q)]
  have hma : Measurable (fun W:VectorWienerPath n=>
      (z.1,anisotropicRestartNoiseStatePath (standardSKOffDiagonalModel n β t hβ ht) μ q
        (z,W) ((1:Paper.Overlap)-(q:ℝ)))) := by
    simpa only [Function.comp_def,anisotropicObservationNoiseAdvance,id_eq] using
      (measurable_anisotropicObservationNoiseAdvance (standardSKOffDiagonalModel n β t hβ ht) μ q 1).comp
        ((measurable_const (a:=z)).prodMk measurable_id)
  have hmv : Measurable (fun W:VectorWienerPath n=>cavityVectorEndpointAdvance μ β t ht.le q
      ((standardSKOffDiagonalCompression z.1,Real.sqrt ((1-t)*β^2) • z.2),W)) := by
    exact (measurable_cavityVectorEndpointAdvance μ β t ht.le q).comp
      (measurable_const.prodMk measurable_id)
  rw [lintegral_map ((Kernel.comap _ _ _).measurable_coe hA)
      hma,lintegral_map ((terminalSpinKernel _ _).measurable_coe hA) hmv]
  apply lintegral_congr
  intro W
  simp only [Kernel.comap_apply,anisotropicObservationParameter,
    anisotropicUnitInput,ContinuousLinearMap.comp_apply]
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKOffDiagonalNoiseMap,standardSKOffDiagonalTerminalLaw]
  change (terminalLaw (vectorTerminalExponent n β t (standardSKOffDiagonalCompression z.1)
    (Real.sqrt ((1-t)*β^2) • anisotropicRestartNoiseStatePath
      (standardSKOffDiagonalModel n β t hβ ht) μ q ((z.1,z.2),W) (1-(q:ℝ))))) A=_
  have hH : 1-(q:ℝ)∈Icc (0:ℝ) (vectorRestartHorizon q) := by
    rw [vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
    exact ⟨sub_nonneg.mpr q.property.2,le_rfl⟩
  rw [standardSKOffDiagonalRestartNoiseState μ β t hβ ht q z.1 z.2 W _ hH]
  rfl

theorem cavityVectorEndpointSpinKernel_mean (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (d : Configuration n→ℝ)
    (z : VectorState n) :
    (∫σ,d σ∂cavityVectorEndpointSpinKernel μ β t ht q z)=
      ∫W,terminalMean (vectorTerminalExponent n β t z.1
        (vectorNoiseRestartStatePath (vectorMeasureDriftData μ β t ht)
          (Real.sqrt ((1-t)*β^2)) q (z,W) (1-(q:ℝ)))) d∂vectorWienerMeasure n := by
  have hi : Integrable d (cavityVectorEndpointSpinKernel μ β t ht q z) :=
    bounded_real_integrable _ (measurable_of_finite d) (∑σ:Configuration n,‖d σ‖)
      (fun σ=>Finset.single_le_sum (fun τ _=>norm_nonneg (d τ)) (Finset.mem_univ σ))
  rw [cavityVectorEndpointSpinKernel,Kernel.integral_comp hi,
    independentNoiseKernel_apply _ _ (measurable_cavityVectorEndpointAdvance μ β t ht q)]
  change (∫x,∫σ,d σ∂terminalLaw (vectorTerminalExponent n β t x.1 x.2)
    ∂(vectorWienerMeasure n).map (fun W=>cavityVectorEndpointAdvance μ β t ht q (z,W)))=_
  simp only [integral_terminalLaw]
  have hm : Measurable (fun W:VectorWienerPath n=>cavityVectorEndpointAdvance μ β t ht q (z,W)) :=
    (measurable_cavityVectorEndpointAdvance μ β t ht q).comp
      (measurable_const.prodMk measurable_id)
  rw [integral_map hm.aemeasurable
    ((continuous_vectorTerminalMean_joint β t d).measurable.aestronglyMeasurable)]
  rfl

theorem cavityVectorEndpointSpinKernel_conditional_mean (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (d : Configuration n→ℝ) :
    (vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalObservable μ β t ht d|
      vectorBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[vectorMeasureDisorderTilt μ β t a]
      fun sample=>∫σ,d σ∂cavityVectorEndpointSpinKernel μ β t ht q
        (sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample) := by
  let f : VectorState n→ℝ:=fun z=>terminalMean (vectorTerminalExponent n β t z.1 z.2) d
  let C:ℝ:=∑σ:Configuration n,|d σ|
  have hf : Measurable f:=(continuous_vectorTerminalMean_joint β t d).measurable
  have hC (z : VectorState n) : ‖f z‖≤C := by
    rw [Real.norm_eq_abs]
    exact terminalMean_bound _ d C
      (fun σ=>Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ))
  have hb:=condExp_vectorAdditiveState_future (vectorMeasureDriftData μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 q (vectorRestartHorizon q) le_rfl f hf C hC
  have hsum : (q:ℝ).toNNReal+vectorRestartHorizon q=1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ q.property.1,
      vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
    simp
  rw [hsum] at hb
  change (vectorDisorderBrownianMeasure n)[vectorMeasureTerminalObservable μ β t ht d|
    vectorBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[vectorDisorderBrownianMeasure n] _ at hb
  have htbase := (withDensity_absolutelyContinuous
    (μ:=vectorDisorderBrownianMeasure n)
    (f:=fun sample=>ENNReal.ofReal (vectorMeasureOuterWeight μ β t a sample.1))).ae_eq hb
  refine (vectorMeasureTerminalObservable_condExp_eq_base μ β t a ht q d).trans ?_
  filter_upwards [htbase] with sample hs
  rw [hs,cavityVectorEndpointSpinKernel_mean]
  rw [vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
  rfl

theorem vectorConditionalTerminalSpinKernel_eq_endpoint (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    vectorConditionalTerminalSpinKernel (n:=n) μ β t a ht q=ᵐ[vectorMeasureSpinPathLaw μ β t a ht]
      fun p : VectorMarkedSample n=>cavityVectorEndpointSpinKernel μ β t ht q
        (p.1.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal p.1) := by
  have hmeans (d : Configuration n→ℝ) :
      (fun p=>∫σ,d σ∂vectorConditionalTerminalSpinKernel μ β t a ht q p)=ᵐ[
        vectorMeasureSpinPathLaw μ β t a ht]
        fun p=>∫σ,d σ∂cavityVectorEndpointSpinKernel μ β t ht q
          (p.1.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal p.1) :=
    (vectorConditionalTerminalSpinKernel_condExp μ β t a ht q d).symm.trans
      ((vectorMeasureSpinPathLaw_terminal_observable_condExp μ β t a ht q d).trans
        ((measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht).quasiMeasurePreserving.ae
          (cavityVectorEndpointSpinKernel_conditional_mean μ β t a ht q d)))
  have hsingle : ∀ᵐp∂vectorMeasureSpinPathLaw μ β t a ht,∀σ:Configuration n,
      (vectorConditionalTerminalSpinKernel μ β t a ht q p).real {σ}=
        (cavityVectorEndpointSpinKernel μ β t ht q
          (p.1.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal p.1)).real {σ} := by
    apply ae_all_iff.mpr
    intro σ
    have hh:=hmeans (({σ}:Set (Configuration n)).indicator (fun _=>1))
    filter_upwards [hh] with p hp
    simpa only [integral_indicator_const _ (measurableSet_singleton σ),
      smul_eq_mul,mul_one] using hp
  filter_upwards [hsingle] with p hp
  apply Measure.ext_of_singleton
  intro σ
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (hp σ)

theorem cavityVectorEndpointSpinKernel_removeDiagonal (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    cavityVectorEndpointSpinKernel μ β t ht q (p,x)=
      cavityVectorEndpointSpinKernel μ β t ht q ((p.1,0),x) := by
  have hpath (W : VectorWienerPath n) :
      vectorNoiseRestartStatePath (vectorMeasureDriftData μ β t ht)
        (Real.sqrt ((1-t)*β^2)) q ((p,x),W) (1-(q:ℝ))=
      vectorNoiseRestartStatePath (vectorMeasureDriftData μ β t ht)
        (Real.sqrt ((1-t)*β^2)) q (((p.1,0),x),W) (1-(q:ℝ)) := by
    apply vectorNoiseStatePath_drift_congr
    · intro u hu y
      change _ • vectorMeasureGradient μ β t _ p y=_ • vectorMeasureGradient μ β t _ (p.1,0) y
      rw [vectorMeasureGradient_diagonal_shift μ β t ht]
    · rw [vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
      exact ⟨sub_nonneg.mpr q.property.2,le_rfl⟩
  ext A hA
  rw [cavityVectorEndpointSpinKernel,Kernel.comp_apply' _ _ _ hA,
    Kernel.comp_apply' _ _ _ hA,
    independentNoiseKernel_apply _ _ (measurable_cavityVectorEndpointAdvance μ β t ht q),
    independentNoiseKernel_apply _ _ (measurable_cavityVectorEndpointAdvance μ β t ht q)]
  have hm (z:VectorState n) : Measurable (fun W:VectorWienerPath n=>
      cavityVectorEndpointAdvance μ β t ht q (z,W)) :=
    (measurable_cavityVectorEndpointAdvance μ β t ht q).comp
      (measurable_const.prodMk measurable_id)
  rw [lintegral_map ((terminalSpinKernel _ _).measurable_coe hA)
      (hm (p,x)),
    lintegral_map ((terminalSpinKernel _ _).measurable_coe hA)
      (hm ((p.1,0),x))]
  apply lintegral_congr
  intro W
  change terminalLaw (vectorTerminalExponent n β t p _ ) A=
    terminalLaw (vectorTerminalExponent n β t (p.1,0) _) A
  dsimp only [cavityVectorEndpointAdvance]
  rw [hpath,vectorTerminalLaw_diagonal_shift β t p]

end QuantitativeFollowup
