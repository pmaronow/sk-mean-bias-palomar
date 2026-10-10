module
public import QuantitativePaper.VectorExponentialTimeLocalization
public import QuantitativePaper.VectorRestartExponentialIto

@[expose] public section

/-! Literal exponential-growth Dynkin formula on a strict finite cell.
All localization hypotheses are discharged by a genuine smooth cutoff;
only the original cell smoothness and actual growth envelopes remain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_restart_cell_exponential_dynkin
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (f : VectorCompactTestParameter n→ℝ) (l u : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' Ioo l u))
    (B K : ℝ) (hB : 0≤B)
    (hjets : ∀q∈Ioo l u,∀p : Couplings n×ℝ,∀x : Field n,∀r : ℕ,r≤2→
      ‖iteratedFDeriv ℝ r (fun y=>f (q,(p,y))) x‖≤B*Real.exp (K*(‖p‖+‖x‖)))
    (htime : ∀q∈Ioo l u,∀p : Couplings n×ℝ,∀x : Field n,
      ‖vectorCompactSmoothTimeField f (q,(p,x))‖≤B*Real.exp (K*(‖p‖+‖x‖)))
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤1) (hla : l<(a:ℝ)) (hbu : (b:ℝ)<u) :
    let X:=vectorRestartState μ β t ht q p x
    let d:=vectorAdditiveDrift (vectorRestartDriftData μ β t ht q p)
      (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
    let σ:=Real.sqrt ((1-t)*β^2)
    Integrable (Function.uncurry (vectorExponentialGenerator f X d σ))
      ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod (vectorDisorderBrownianMeasure n)) ∧
    (∫sample,f (b,(sample.1,X b sample))-f (a,(sample.1,X a sample))
      ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,vectorExponentialGenerator f X d σ r sample
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let X:=vectorRestartState (n:=n) μ β t ht q p x
  let d:=vectorAdditiveDrift (vectorRestartDriftData (n:=n) μ β t ht q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
  let σ:=Real.sqrt ((1-t)*β^2)
  let P:=vectorDisorderBrownianMeasure n
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  obtain ⟨ρ,hρ,hsρ,hsU,hρv,hρeq⟩:=exists_cellTimeCutoff l a b u hla hab hbu
  have hρb (q : ℝ) : ‖ρ q‖≤1:=abs_le.mpr ⟨by linarith [hρv q |>.1],hρv q |>.2⟩
  let F:=timeLocalizedFunction ρ f
  have hFc : ContDiff ℝ ∞ F:=contDiff_timeLocalizedFunction ρ f (Ioo l u) isOpen_Ioo hρ hsU hf
  obtain ⟨B',hB',hFj,hFt⟩:=timeLocalized_vectorCell_exponential_bounds
    ρ hρ hsρ hρb (Ioo l u) isOpen_Ioo hsU f hf B K hB hjets htime
  obtain ⟨hInt,hIdentity⟩:=vector_restart_exponential_dynkin μ β t ht q p x F hFc B' K hB'
    (fun q _ p x r hr=>hFj q p x r hr) (fun q _ p x=>hFt q p x) a b hab hb
  have hlocal (r : ℝ≥0) (hr : r∈Icc a b) (sample : VectorDisorderBrownianSample n) :
      F=ᶠ[𝓝 ((r:ℝ),(sample.1,X r sample))]f:=
    timeLocalizedFunction_eventually_eq ρ f r (sample.1,X r sample) (hρeq r hr)
  have hGen (r : ℝ≥0) (hr : r∈Icc a b) (sample : VectorDisorderBrownianSample n) :
      vectorExponentialGenerator F X d σ r sample=vectorExponentialGenerator f X d σ r sample:=
    vectorExponentialGenerator_congr_of_eventuallyEq F f X d σ r sample (hlocal r hr sample)
  have hMem : ∀ᵐz ∂ν.prod P,z.1∈Ioc a b:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  have hIntRaw : Integrable (Function.uncurry (vectorExponentialGenerator f X d σ)) (ν.prod P):=by
    apply hInt.congr
    filter_upwards [hMem] with z hz
    exact hGen z.1 ⟨hz.1.le,hz.2⟩ z.2
  have hLeft : (∫sample,F (b,(sample.1,X b sample))-F (a,(sample.1,X a sample)) ∂P)=
      ∫sample,f (b,(sample.1,X b sample))-f (a,(sample.1,X a sample)) ∂P:=by
    apply integral_congr_ae
    exact .of_forall fun sample=>by
      dsimp only
      rw [(hlocal b ⟨hab,le_rfl⟩ sample).eq_of_nhds,(hlocal a ⟨le_rfl,hab⟩ sample).eq_of_nhds]
  have hRight : (∫sample,(∫r in Ioc a b,vectorExponentialGenerator F X d σ r sample
      ∂nonnegativeLebesgueMeasure) ∂P)=
      ∫sample,(∫r in Ioc a b,vectorExponentialGenerator f X d σ r sample
        ∂nonnegativeLebesgueMeasure) ∂P:=by
    apply integral_congr_ae
    exact .of_forall fun sample=>setIntegral_congr_fun measurableSet_Ioc
      (fun r hr=>hGen r ⟨hr.1.le,hr.2⟩ sample)
  rw [hLeft,hRight] at hIdentity
  exact ⟨hIntRaw,hIdentity⟩

end QuantitativePaper
