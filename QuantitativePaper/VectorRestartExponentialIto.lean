module
public import QuantitativePaper.VectorExponentialItoGenerator
public import QuantitativePaper.VectorRestartExponentialItoLimit

@[expose] public section

/-! Genuine exponential-growth Dynkin formula for the constructed fixed-parameter
restarted Parisi diffusion under its genuine Wiener reference law. Only field jets
through order two and the actual time derivative need exponential bounds. -/
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

theorem vector_restart_exponential_dynkin
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (f : VectorCompactTestParameter n→ℝ) (hf : ContDiff ℝ ∞ f)
    (B K : ℝ) (hB : 0≤B)
    (hjets : ∀q : ℝ,q∈Icc (0:ℝ) 1→∀p : Couplings n×ℝ,∀x : Field n,
      ∀r : ℕ,r≤2→‖iteratedFDeriv ℝ r (fun y=>f (q,(p,y))) x‖≤
        B*Real.exp (K*(‖p‖+‖x‖)))
    (htime : ∀q : ℝ,q∈Icc (0:ℝ) 1→∀p : Couplings n×ℝ,∀x : Field n,
      ‖vectorCompactSmoothTimeField f (q,(p,x))‖≤B*Real.exp (K*(‖p‖+‖x‖)))
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤1) :
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
  have hc:=vectorItoCharacteristics_vectorRestartState (n:=n) μ β t ht q p x
  let F : ℕ→VectorCompactTestParameter n→ℝ:=fun j=>vectorExponentialLocalized j f
  have hFc (j : ℕ) : ContDiff ℝ ∞ (F j):=contDiff_vectorExponentialLocalized j f hf
  have hFs (j : ℕ) : HasCompactSupport (F j):=hasCompactSupport_vectorExponentialLocalized j f
  let tests : ℕ→TimeFTCData (VectorDisorderBrownianSample n) (Field n) 1:=fun j=>
    vectorCompactSmoothSampleTimeData (F j) (hFc j) (hFs j) 1
  have hsp (j : ℕ) : VectorSpatialItoTest (fun q=>(tests j).f q) X:=
    vectorCompactSmoothSampleSpatialTest (F j) (hFc j) (hFs j) X hc.continuous_state hc.adapted_state
  obtain ⟨D,hD⟩:=hc.bounded_drift
  let c : ℕ→ℝ:=fun r=>localizedJetCoefficient (E:=(Couplings n×ℝ)×Field n) r
  have hc0 (r : ℕ) : 0≤c r:=localizedJetCoefficient_nonneg r
  have hcz := hc0 0
  have hco := hc0 1
  have hct := hc0 2
  let C:=(c 0+c 1*D+σ^2/2*((n:ℝ)*c 2)+1)*B
  have hC : 0≤C:=by dsimp [C];positivity
  have hsl (j r : ℕ) (hr : r≤2) (q : ℝ≥0) (hq : q≤1)
      (sample : VectorDisorderBrownianSample n) :
      ‖iteratedFDeriv ℝ r (fun y=>F j (q,(sample.1,y))) (X q sample)‖≤
        c r*(B*Real.exp (K*(‖sample.1‖+‖X q sample‖))) := by
    exact norm_iteratedFDeriv_vectorExponentialLocalized_slice_le j r f hf q sample.1
      (X q sample) _ (fun i hi=>hjets q ⟨q.coe_nonneg,hq⟩ sample.1 _ i (hi.trans hr))
  have hval (j : ℕ) (q : ℝ≥0) (hq : q≤1) (sample : VectorDisorderBrownianSample n) :
      ‖(tests j).f q sample (X q sample)‖≤C*Real.exp (K*(‖sample.1‖+‖X q sample‖)) := by
    have hh:=hsl j 0 (by omega) q hq sample
    simp only [norm_iteratedFDeriv_zero] at hh
    apply hh.trans
    have he : 0≤Real.exp (K*(‖sample.1‖+‖X q sample‖)):=(Real.exp_pos _).le
    have hrest : 0≤c 1*D+σ^2/2*((n:ℝ)*c 2)+1:=by positivity
    dsimp [C]
    nlinarith [mul_nonneg hrest (mul_nonneg hB he)]
  have hgen (j : ℕ) (q : ℝ≥0) (hq : q≤1) (sample : VectorDisorderBrownianSample n) :
      ‖vectorItoGenerator (tests j) X d σ q sample‖≤
        C*Real.exp (K*(‖sample.1‖+‖X q sample‖)) := by
    rw [vectorItoGenerator_compactSmooth_eq]
    have hfirst : ‖fderiv ℝ (fun y=>F j (q,(sample.1,y))) (X q sample)‖≤
        c 1*(B*Real.exp (K*(‖sample.1‖+‖X q sample‖))):=by
      rw [←norm_iteratedFDeriv_one]
      exact hsl j 1 (by omega) q hq sample
    have htimej : ‖vectorCompactSmoothTimeField (F j) (q,(sample.1,X q sample))‖≤
        B*Real.exp (K*(‖sample.1‖+‖X q sample‖)) :=
      (norm_vectorCompactSmoothTimeField_vectorExponentialLocalized_le j f hf q
        ⟨q.coe_nonneg,hq⟩ sample.1 (X q sample)).trans
          (htime q ⟨q.coe_nonneg,hq⟩ sample.1 (X q sample))
    apply (vectorExponentialGenerator_bound (F j) X d σ q sample D _ _ _
      (hD q sample) hfirst (hsl j 2 le_rfl q hq sample) htimej).trans
    have he : 0≤Real.exp (K*(‖sample.1‖+‖X q sample‖)):=(Real.exp_pos _).le
    dsimp [C]
    nlinarith [mul_nonneg (hc0 0) (mul_nonneg hB he)]
  apply vector_restart_dynkin_of_exponential_localizations μ β t ht q p x tests hsp
    (fun q sample=>f (q,(sample.1,X q sample))) (vectorExponentialGenerator f X d σ)
    (measurable_vectorExponentialGenerator f hf hc) a b hab hb C K hC
  · exact hval
  · intro q hq sample
    apply tendsto_const_nhds.congr'
    filter_upwards [vectorExponentialLocalized_eventually_eq f q ⟨q.coe_nonneg,hq⟩ sample.1
      (X q sample)] with j hj
    exact hj.eq_of_nhds.symm
  · intro j q hq sample
    exact hgen j q (hq.2.trans hb) sample
  · intro q hq sample
    have hh:=vectorExponentialLocalizedGenerator_eventually_eq f X d σ q (hq.2.trans hb) sample
    apply tendsto_const_nhds.congr'
    filter_upwards [hh] with j hj
    rw [vectorItoGenerator_compactSmooth_eq]
    exact hj.symm

end QuantitativePaper
