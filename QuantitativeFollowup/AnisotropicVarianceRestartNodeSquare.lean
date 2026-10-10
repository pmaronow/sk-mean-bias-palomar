module
public import QuantitativeFollowup.AnisotropicVarianceRestartFuture
public import QuantitativeFollowup.AnisotropicFiniteNodeResponse

@[expose] public section

/-! Exact node observations in the genuine restarted continuation law.
Repeated nodes are handled by the true zero-variance cascade identities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem cavityFiniteCoordinatePairMoment_eq_parameter_expectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (p j : ℕ) (P : AnisotropicParameter n) (i : Fin n) :
    finiteStateCascadePairMoment (fun _ : QuantitativePaper.Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p j (anisotropicEnergyMap D P)
      (cavityCoordinateFeature i) (cavityCoordinateFeature i)=
      sourceKernelExpectation (fun l=>anisotropicDepthKernel D s (p+l)) j
        (fun Q=>(anisotropicFiniteFeatureMean D s p (fun σ=>Paper.spinSign (σ i)) Q)^2) P := by
  let G : FiniteStateField (QuantitativePaper.Configuration n)→ℝ := fun y=>
    (∫σ,Paper.spinSign (σ i)∂finiteStateCascadeGibbsKernel
      (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p y)^2
  have hG : Measurable G :=
    ((measurable_of_finite (fun σ : QuantitativePaper.Configuration n=>Paper.spinSign (σ i))).stronglyMeasurable.integral_kernel.measurable).pow_const 2
  have he:=sourceKernelExpectation_finiteStateCascade_comp_linear (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (gtStateLogPartition (fun _ : QuantitativePaper.Configuration n=>0))
    (finiteStateGaussianTerminal_lipschitz (fun _ : QuantitativePaper.Configuration n=>0)) p j G hG P
  rw [←anisotropicDepthKernel_eq_parameterCascadeKernel D s] at he
  have hA : (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))=
      cavityFiniteEnergyInput D s := rfl
  rw [hA] at he
  have hmean : (fun y=>G ((anisotropicEnergyMap D) y))=
      fun y=>(anisotropicFiniteFeatureMean D s p (fun σ=>Paper.spinSign (σ i)) y)^2 := by
    funext y;rfl
  rw [hmean] at he
  unfold finiteStateCascadePairMoment
  simp_rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg s)]
  simpa only [cavityCoordinateFeature,G,pow_two] using he

theorem anisotropicFiniteFeatureMean_clamped_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (v : ℕ) (hv : v≤k+2) (hqv : (q:ℝ)≤ s.q v)
    (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicFiniteFeatureMean D (vectorClampedScheme s q q.property) (k+2-v)
      (fun σ=>Paper.spinSign (σ i)) P=
      anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s v hv) P i := by
  have hF : anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-v)=
      anisotropicFinitePotential D s (k+2-v) := by
    rw [←anisotropicTailRecursion_eq_clamped D s q q.property (by omega),
      anisotropicTailRecursion_prefix_of_le D s q (by omega)
        (by rw [show k+2-(k+2-v)=v by omega];exact hqv)]
  rw [anisotropicFiniteTailMagnetization_node]
  unfold anisotropicFiniteFeatureMean
  rw [←anisotropicMagnetization_eq_spin_mean]
  change anisotropicMagnetization D (vectorClampedScheme s q q.property) (k+2-v) P i=_
  simp only [anisotropicMagnetization_apply,hF]

theorem cavityFiniteRestartCoordinateSquare_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (v : ℕ) (hv : v≤k+2) (hqv : (q:ℝ)≤ s.q v) (i : Fin n) :
    cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme s q q.property) (k+2)
      (anisotropicDisorderInjection n g+anisotropicUnitInput D x) i (anisotropicSchemeNode s v hv)=
      ∫sample,(anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s v hv)
        (anisotropicFiniteRestartPhysicalParameter D s g q x (anisotropicRestartElapsed s q v) sample) i)^2
          ∂vectorDisorderBrownianMeasure n := by
  let c:=vectorClampedScheme s q q.property
  have hnode : scalarSchemeTransportNode c (v+1)=anisotropicSchemeNode s v hv := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe c (v+1) (by omega),vectorClampedScheme_overlap_succ,
      max_eq_right hqv]
    rfl
  rw [cavityFiniteConditionalCoordinateSquare_eq_futureSquare]
  conv_lhs => rw [←hnode,show v+1=k+1+2-(k+2-v) by omega,
    cavityFiniteFutureSquare_node D c (k+2) (k+2-v) (by omega) (by omega)]
  rw [show k+2-(k+2-v)=v by omega,cavityFiniteCoordinatePairMoment_eq_parameter_expectation]
  have hmean : (fun P=>(anisotropicFiniteFeatureMean D c (k+2-v) (fun σ=>Paper.spinSign (σ i)) P)^2)=
      fun P=>(anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s v hv) P i)^2 := by
    funext P
    rw [anisotropicFiniteFeatureMean_clamped_node D s q v hv hqv P i]
  rw [hmean]
  have hF : Measurable (fun P=>(anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s v hv) P i)^2) := by
    rw [show anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s v hv)=
      anisotropicMagnetization D s (k+2-v) from funext (anisotropicFiniteTailMagnetization_node D s v hv)]
    exact ((boundedJets_anisotropicMagnetization_component D s (k+2-v) i).1.continuous.measurable).pow_const 2
  have hb : ∀P,|(anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s v hv) P i)^2|≤1 := by
    intro P
    simpa [abs_pow] using pow_le_pow_left₀ (abs_nonneg _)
      (anisotropicFiniteTailMagnetization_component_bound D s _ P i) 2
  exact (integral_anisotropicFiniteRestart_state_eq_depth_expectation D s g q x v hv _ hF 1 zero_le_one hb).symm

end QuantitativeFollowup
