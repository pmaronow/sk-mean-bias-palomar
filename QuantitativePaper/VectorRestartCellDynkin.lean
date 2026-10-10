module
public import QuantitativePaper.VectorRestartExponentialCellIto

@[expose] public section

/-! Fixed-parameter cell Dynkin formula for the actual restarted Parisi
state. The observable depends only on elapsed time and the field. The
Gaussian initial-disorder coordinate is integrated out by an explicit lift,
and the generator uses the literal covariance `(1-t)*beta^2`. -/
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

def vectorRestartCellTestLift (f : ℝ×Field n→ℝ)
    (z : VectorCompactTestParameter n) : ℝ:=f (z.1,z.2.2)

def vectorRestartCellTimeField (f : ℝ×Field n→ℝ) (z : ℝ×Field n) : ℝ:=
  fderiv ℝ f z (1,0)

theorem hasDerivAt_vectorRestartCell_time {f : ℝ×Field n→ℝ}
    {r : ℝ} {x : Field n} (hf : ContDiffAt ℝ ∞ f (r,x)) :
    HasDerivAt (fun s=>f (s,x)) (vectorRestartCellTimeField f (r,x)) r :=
  hf.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))

theorem vectorRestartCellTestLift_contDiffOn (f : ℝ×Field n→ℝ) (l u : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' Ioo l u)) :
    ContDiffOn ℝ ∞ (vectorRestartCellTestLift f) (Prod.fst ⁻¹' Ioo l u) := by
  have hp : ContDiff ℝ ∞ (fun z : VectorCompactTestParameter n=>(z.1,z.2.2)):=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  exact hf.comp hp.contDiffOn (fun z hz=>hz)

theorem vectorRestartCellTestLift_timeField (f : ℝ×Field n→ℝ)
    (r : ℝ) (p : Couplings n×ℝ) (x : Field n)
    (hf : ContDiffAt ℝ ∞ f (r,x)) :
    vectorCompactSmoothTimeField (vectorRestartCellTestLift f) (r,(p,x))=
      vectorRestartCellTimeField f (r,x) := by
  have hp : ContDiff ℝ ∞ (fun z : VectorCompactTestParameter n=>(z.1,z.2.2)):=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hLift : ContDiffAt ℝ ∞ (vectorRestartCellTestLift f) (r,(p,x)):=
    hf.comp (r,(p,x)) hp.contDiffAt
  exact (hasDerivAt_vectorCell_time hLift).unique (hasDerivAt_vectorRestartCell_time hf)

def vectorRestartCellGenerator (f : ℝ×Field n→ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (c : ℝ)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ℝ:=
  fderiv ℝ (fun y=>f (r,y)) (X r sample) (d r sample)+
    c/2*vectorBilinearTrace (vectorHessian (fun y=>f (r,y)) (X r sample))+
    vectorRestartCellTimeField f (r,X r sample)

theorem vector_restart_fixed_parameter_cell_dynkin
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (f : ℝ×Field n→ℝ) (l u : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' Ioo l u))
    (B K : ℝ) (hB : 0≤B)
    (hjets : ∀r∈Ioo l u,∀y : Field n,∀j : ℕ,j≤2→
      ‖iteratedFDeriv ℝ j (fun z=>f (r,z)) y‖≤B*Real.exp (K*‖y‖))
    (htime : ∀r∈Ioo l u,∀y : Field n,
      ‖vectorRestartCellTimeField f (r,y)‖≤B*Real.exp (K*‖y‖))
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤1) (hla : l<(a:ℝ)) (hbu : (b:ℝ)<u) :
    let X:=vectorRestartState μ β t ht q p x
    let d:=vectorAdditiveDrift (vectorRestartDriftData μ β t ht q p)
      (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
    let c:=(1-t)*β^2
    Integrable (Function.uncurry (vectorRestartCellGenerator f X d c))
      ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod (vectorDisorderBrownianMeasure n)) ∧
    (∫sample,f (b,X b sample)-f (a,X a sample) ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,vectorRestartCellGenerator f X d c r sample
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let X:=vectorRestartState (n:=n) μ β t ht q p x
  let d:=vectorAdditiveDrift (vectorRestartDriftData (n:=n) μ β t ht q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
  let c:=(1-t)*β^2
  let P:=vectorDisorderBrownianMeasure n
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  have he (g : Couplings n×ℝ) (y : Field n) :
      B*Real.exp (K*‖y‖)≤B*Real.exp (|K| *(‖g‖+‖y‖)) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hB
    calc
      K*‖y‖≤|K| *‖y‖:=mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
      _≤|K| *(‖g‖+‖y‖):=by nlinarith [mul_nonneg (abs_nonneg K) (norm_nonneg g)]
  have hLift:=vectorRestartCellTestLift_contDiffOn f l u hf
  have hAt (r : ℝ) (hr : r∈Ioo l u) (y : Field n) :
      ContDiffAt ℝ ∞ f (r,y):=
    hf.contDiffAt ((isOpen_Ioo.preimage continuous_fst).mem_nhds hr)
  have hJ (r : ℝ) (hr : r∈Ioo l u) (g : Couplings n×ℝ) (y : Field n)
      (j : ℕ) (hj : j≤2) :
      ‖iteratedFDeriv ℝ j (fun z=>vectorRestartCellTestLift f (r,(g,z))) y‖≤
        B*Real.exp (|K| *(‖g‖+‖y‖)):=
    (hjets r hr y j hj).trans (he g y)
  have hT (r : ℝ) (hr : r∈Ioo l u) (g : Couplings n×ℝ) (y : Field n) :
      ‖vectorCompactSmoothTimeField (vectorRestartCellTestLift f) (r,(g,y))‖≤
        B*Real.exp (|K| *(‖g‖+‖y‖)) := by
    rw [vectorRestartCellTestLift_timeField f r g y (hAt r hr y)]
    exact (htime r hr y).trans (he g y)
  obtain ⟨hI,hD⟩:=vector_restart_cell_exponential_dynkin μ β t ht q p x
    (vectorRestartCellTestLift f) l u hLift B |K| hB hJ hT a b hab hb hla hbu
  have hc : 0≤c:=mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)
  have hEq (r : ℝ≥0) (hr : r∈Ioc a b) (sample : VectorDisorderBrownianSample n) :
      vectorExponentialGenerator (vectorRestartCellTestLift f) X d (Real.sqrt c) r sample=
        vectorRestartCellGenerator f X d c r sample := by
    have hrU : (r:ℝ)∈Ioo l u:=⟨lt_trans hla (by exact_mod_cast hr.1),
      lt_of_le_of_lt (by exact_mod_cast hr.2) hbu⟩
    simp only [vectorExponentialGenerator,vectorRestartCellTestLift,vectorRestartCellGenerator,
      Real.sq_sqrt hc,vectorRestartCellTestLift_timeField f r sample.1 (X r sample) (hAt r hrU _)]
  have hMem : ∀ᵐz ∂ν.prod P,z.1∈Ioc a b := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  have hI' : Integrable (Function.uncurry (vectorRestartCellGenerator f X d c)) (ν.prod P) := by
    apply hI.congr
    filter_upwards [hMem] with z hz
    exact hEq z.1 hz z.2
  have hD' : (∫sample,(∫r in Ioc a b,
      vectorExponentialGenerator (vectorRestartCellTestLift f) X d (Real.sqrt c) r sample
        ∂nonnegativeLebesgueMeasure) ∂P)=
      ∫sample,(∫r in Ioc a b,vectorRestartCellGenerator f X d c r sample
        ∂nonnegativeLebesgueMeasure) ∂P := by
    apply integral_congr_ae
    exact .of_forall fun sample=>setIntegral_congr_fun measurableSet_Ioc
      (fun r hr=>hEq r hr sample)
  rw [hD'] at hD
  exact ⟨hI',hD⟩

end QuantitativePaper
