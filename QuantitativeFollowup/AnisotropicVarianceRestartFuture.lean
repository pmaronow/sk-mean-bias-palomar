module
public import QuantitativeFollowup.AnisotropicVarianceRestartHistory
public import QuantitativeFollowup.AnisotropicFiniteFeatureKernels
public import FourPapersCommon.HistoryKernelExpectation
public import FourPapersCommon.FiniteStateCascadeExpectationTransport
public import QuantitativeFollowup.FollowupCavityNodeBStieltjes

@[expose] public section

/-! Actual bounded future observables and conditional binary squares of a
restarted anisotropic diffusion, including every repeated profile node. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper OverlapPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integral_anisotropicFiniteRestart_state_eq_depth_expectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (v : ℕ) (hv : v≤k+2) (F : AnisotropicParameter n→ℝ) (hF : Measurable F)
    (B : ℝ) (hB : 0≤B) (hb : ∀P,|F P|≤B) :
    (∫sample,F (anisotropicFiniteRestartPhysicalParameter D s g q x
      (anisotropicRestartElapsed s q v) sample) ∂vectorDisorderBrownianMeasure n)=
      sourceKernelExpectation (fun d=>anisotropicDepthKernel D (vectorClampedScheme s q q.property)
        (k+2-v+d)) v F (anisotropicDisorderInjection n g+anisotropicUnitInput D x) := by
  have he:=integral_history_eq_reverse_kernel_expectation
    (Measure.dirac (anisotropicDisorderInjection n g+anisotropicUnitInput D x))
    (anisotropicFiniteRestartPhysicalKernel D s q) (fun _=>inferInstance) v F hF B hB hb
  rw [←anisotropicFiniteRestartPhysical_history_law D s g q x v hv,
    integral_map (f:=fun h : FiniteHistory (AnisotropicParameter n) v=>F (h (Fin.last v)))
      (measurable_anisotropicFiniteRestartPhysicalHistory D s g q x v).aemeasurable
      ((hF.comp (measurable_pi_apply (Fin.last v))).aestronglyMeasurable),integral_dirac] at he
  have hκ : ∀d<v,anisotropicFiniteRestartPhysicalKernel D s q (v-1-d)=
      anisotropicDepthKernel D (vectorClampedScheme s q q.property) (k+2-v+d) := by
    intro d hd
    unfold anisotropicFiniteRestartPhysicalKernel anisotropicFiniteTransition anisotropicDepthKernel
    rw [show k+1+1-(v-1-d+1)=k+2-v+d by omega]
  rw [sourceKernelExpectation_congr_kernels _ _ v hκ] at he
  exact he

theorem cavityFiniteConditionalCoordinateSquare_eq_parameter_expectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (P : AnisotropicParameter n) (i : Fin n) (r : Paper.Overlap) :
    cavityFiniteConditionalCoordinateSquare D s J P i r=
      let d:=cavityFiniteFutureDepth s J r
      sourceKernelExpectation (fun l=>anisotropicDepthKernel D s (d+l)) (J-d)
        (fun Q=>(anisotropicFiniteFeatureMean D s d (fun σ=>Paper.spinSign (σ i)) Q)^2) P := by
  let d:=cavityFiniteFutureDepth s J r
  let G : FiniteStateField (QuantitativePaper.Configuration n)→ℝ := fun y=>
    (∫σ,Paper.spinSign (σ i)∂finiteStateCascadeGibbsKernel
      (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y)^2
  have hG : Measurable G :=
    ((measurable_of_finite (fun σ : QuantitativePaper.Configuration n=>Paper.spinSign (σ i))).stronglyMeasurable.integral_kernel.measurable).pow_const 2
  have he:=sourceKernelExpectation_finiteStateCascade_comp_linear (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (gtStateLogPartition (fun _ : QuantitativePaper.Configuration n=>0))
    (finiteStateGaussianTerminal_lipschitz (fun _ : QuantitativePaper.Configuration n=>0)) d (J-d) G hG P
  rw [←anisotropicDepthKernel_eq_parameterCascadeKernel D s] at he
  have hA : (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))=
      cavityFiniteEnergyInput D s := rfl
  rw [hA] at he
  change sourceKernelExpectation _ _ _ _=_ at he
  change (∫y,G y∂sourceKernelLaw _ (J-d) (anisotropicEnergyMap D P))=_
  have hGb : ∀y,|G y|≤1 := by
    intro y
    letI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : QuantitativePaper.Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) d
    have hb : ∀σ : QuantitativePaper.Configuration n,‖Paper.spinSign (σ i)‖≤(1:ℝ) := by
      intro σ
      cases hs : σ i <;> simp [Paper.spinSign,hs]
    have hm:=norm_integral_le_of_norm_le_const
      (μ:=finiteStateCascadeGibbsKernel (fun _ : QuantitativePaper.Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y) (.of_forall hb)
    simp only [probReal_univ,mul_one,Real.norm_eq_abs] at hm
    simpa [G,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  rw [←sourceKernelExpectation_eq_integral _ (fun l=>
      isMarkovKernel_finiteStateGaussianTerminalCascadeKernel (fun _ : QuantitativePaper.Configuration n=>0)
        (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) (d+l))
      G hG 1 hGb]
  have hmean : (fun y=>G ((anisotropicEnergyMap D) y))=
      fun y=>(anisotropicFiniteFeatureMean D s d (fun σ=>Paper.spinSign (σ i)) y)^2 := by
    funext y
    rfl
  rw [hmean] at he
  exact he

theorem cavityFiniteRestartCoordinateSquare_eq_state_mean_square (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (i : Fin n) (r : Paper.Overlap) :
    cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme s q q.property) (k+2)
      (anisotropicDisorderInjection n g+anisotropicUnitInput D x) i r=
      let d:=cavityFiniteFutureDepth (vectorClampedScheme s q q.property) (k+2) r
      ∫sample,(anisotropicFiniteFeatureMean D (vectorClampedScheme s q q.property) d
        (fun σ=>Paper.spinSign (σ i))
        (anisotropicFiniteRestartPhysicalParameter D s g q x
          (anisotropicRestartElapsed s q (k+2-d)) sample))^2 ∂vectorDisorderBrownianMeasure n := by
  let d:=cavityFiniteFutureDepth (vectorClampedScheme s q q.property) (k+2) r
  have hd : d≤k+2:=cavityFiniteFutureDepth_le _ _ _
  rw [cavityFiniteConditionalCoordinateSquare_eq_parameter_expectation]
  have hF : Measurable (fun P=>(anisotropicFiniteFeatureMean D (vectorClampedScheme s q q.property) d
      (fun σ=>Paper.spinSign (σ i)) P)^2) :=
    (measurable_anisotropicFiniteFeatureMean D _ d _).pow_const 2
  have hb : ∀P,|(anisotropicFiniteFeatureMean D (vectorClampedScheme s q q.property) d
      (fun σ=>Paper.spinSign (σ i)) P)^2|≤1 := by
    intro P
    have hm:=anisotropicFiniteFeatureMean_bound D (vectorClampedScheme s q q.property) d
      (fun σ=>Paper.spinSign (σ i)) 1 (fun σ=>by cases hs : σ i <;> simp [Paper.spinSign,hs]) P
    rw [Real.norm_eq_abs] at hm
    simpa [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  have he:=integral_anisotropicFiniteRestart_state_eq_depth_expectation D s g q x (k+2-d)
    (by omega) _ hF 1 zero_le_one hb
  rw [show k+2-(k+2-d)=d by omega] at he
  exact he.symm

end QuantitativeFollowup
