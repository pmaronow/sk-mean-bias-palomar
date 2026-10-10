module
public import QuantitativePaper.VectorFiniteStatePathEnvelope

@[expose] public section

/-! Actual expected exponential-growth tests are continuous on closed time
cells. The integrable dominating function is constructed from genuine
Brownian path moments and the literal finite-profile disorder tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem continuousOn_vectorFinite_expected_exp_test
    (s : SpinGlass.Targets.RSBScheme k) (β t outer : ℝ) (ht : t≤1)
    (a b : ℝ) (ha : 0≤a) (hb : b≤1)
    (F : ℝ×((Couplings n×ℝ)×Field n)→ℝ)
    (hF : ContinuousOn F (Icc a b×ˢuniv)) (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hbound : ∀q∈Icc a b,∀p x,|F (q,p,x)|≤C*Real.exp (R*(‖p‖+‖x‖))) :
    ContinuousOn (fun q=>∫sample : VectorDisorderBrownianSample n,
      F (q,sample.1,vectorFiniteState s β t ht q.toNNReal sample)
      ∂vectorFiniteDisorderTilt s β t outer) (Icc a b) := by
  let M : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    C*Real.exp (R*(‖sample.1‖+vectorFiniteStatePathEnvelope β t sample))
  have hi : Integrable M (vectorFiniteDisorderTilt s β t outer):=
    (integrable_exp_vectorFiniteStatePathEnvelope s β t outer R).const_mul C
  have hs (q : ℝ) (hq : q∈Icc a b) :
      Continuous (fun z : (Couplings n×ℝ)×Field n=>F (q,z)):=by
    rw [←continuousOn_univ]
    exact hF.comp (f:=fun z : (Couplings n×ℝ)×Field n=>(q,z))
      (g:=F) (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _=>⟨hq,mem_univ _⟩)
  apply continuousOn_of_dominated (bound:=M)
  · intro q hq
    have hX : Measurable (vectorFiniteState (n:=n) s β t ht q.toNNReal):=
      (measurable_uncurry_vectorFiniteState s β t ht).of_uncurry_left
    exact ((hs q hq).measurable.comp (measurable_fst.prodMk hX)).aestronglyMeasurable
  · intro q hq
    exact .of_forall fun sample=>by
      have hq1 : q.toNNReal≤(1 : ℝ≥0):=by
        simpa only [Real.toNNReal_one] using Real.toNNReal_le_toNNReal (hq.2.trans hb)
      have hx:=norm_vectorFiniteState_le_pathEnvelope s β t ht q.toNNReal hq1 sample
      rw [Real.norm_eq_abs]
      exact (hbound q hq sample.1 _).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add le_rfl hx) hR)) hC)
  · exact hi
  · exact .of_forall fun sample=>by
      have hp : Continuous (fun q : ℝ=>(q,sample.1,vectorFiniteState s β t ht q.toNNReal sample)):=
        continuous_id.prodMk (continuous_const.prodMk
          ((continuous_vectorFiniteState s β t ht sample).comp continuous_real_toNNReal))
      exact hF.comp
        (f:=fun q : ℝ=>(q,sample.1,vectorFiniteState s β t ht q.toNNReal sample))
        (g:=F) hp.continuousOn (fun q hq=>⟨hq,mem_univ _⟩)

end QuantitativePaper
