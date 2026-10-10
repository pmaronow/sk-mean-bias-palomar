module
public import QuantitativePaper.VectorProfileRetainedExpectedContinuity
public import QuantitativePaper.VectorProfileCellExpectationIntegrable

@[expose] public section

/-! Every closed retained exponential-value observable has a genuine
integrable section under the actual fractional finite diffusion law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem integrable_vectorProfile_retained_observable
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hθAB : θ∈Ioo A B)
    (F : ℝ→VectorProfileParameter n×Field n→ℝ)
    (hF : RetainedExponentialContinuousOn F (Icc (s₀.q i) (s₀.q (i+1)))
      (vectorProfileRetainedDomain n A B))
    (q : ℝ≥0) (hq : (q:ℝ)∈Icc (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      F q ((θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ hθ) β t ht q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ hθ) β t outer) := by
  let s:=vectorProfileScheme s₀ s₁ θ hθ
  obtain ⟨C,R,hC,hR,hbound⟩:=hF.bound
  have hSection : Continuous (fun z : (Couplings n×ℝ)×Field n=>F q ((θ,z.1),z.2)):=by
    rw [←continuousOn_univ]
    apply hF.continuous.comp
      (f:=fun z : (Couplings n×ℝ)×Field n=>((q:ℝ),((θ,z.1),z.2)))
      (g:=fun w : ℝ×(VectorProfileParameter n×Field n)=>F w.1 w.2)
      (show Continuous (fun z : (Couplings n×ℝ)×Field n=>
        ((q:ℝ),((θ,z.1),z.2))) by fun_prop).continuousOn
    exact fun z hz=>⟨hq,hθAB⟩
  have hmeas : Measurable (fun sample : VectorDisorderBrownianSample n=>
      F q ((θ,sample.1),vectorFiniteState s β t ht q sample)):=
    hSection.measurable.comp (measurable_fst.prodMk
      (measurable_uncurry_vectorFiniteState s β t ht).of_uncurry_left)
  have hq1 : q≤1:=by exact_mod_cast hq.2.trans (s₀.q_le_one (by omega))
  apply ((integrable_exp_vectorFiniteState_and_disorder s β t outer R ht q hq1).const_mul (C*Real.exp R)).mono' hmeas.aestronglyMeasurable
  exact .of_forall fun sample=>by
    let x:=vectorFiniteState s β t ht q sample
    have hn : ‖(((θ,sample.1),x) : VectorProfileParameter n×Field n)‖≤1+‖sample.1‖+‖x‖:=by
      change max (max |θ| ‖sample.1‖) ‖x‖≤1+‖sample.1‖+‖x‖
      have hθ1 : |θ|≤1:=abs_le.mpr ⟨by linarith [hθ.1],hθ.2⟩
      apply max_le
      · apply max_le
        · linarith [norm_nonneg sample.1,norm_nonneg x]
        · linarith [norm_nonneg x]
      · linarith [norm_nonneg sample.1]
    apply (hbound q hq ((θ,sample.1),x) hθAB).trans
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hn hR)) hC).trans_eq
    rw [show R*(1+‖sample.1‖+‖x‖)=R+R*(‖sample.1‖+‖x‖) by ring,Real.exp_add]
    ring

end QuantitativePaper
