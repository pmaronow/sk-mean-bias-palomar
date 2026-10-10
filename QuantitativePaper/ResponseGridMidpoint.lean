module
public import QuantitativePaper.VectorProfileFunctionalRegularity
public import QuantitativePaper.ResponseMidpointLimit
public import QuantitativePaper.ResponseCurvatureSequence

@[expose] public section

/-! Actual common-grid curvature densities control midpoint gaps in the
weak measure limit. The limit is used through its proved continuity. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def responseGridMixFunctional (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam θ : ℝ):ℝ:=
  responseEnergyFunctional n (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
    (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) θ) β t lam

theorem responseGridMix_weighted_curvature_bound (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam) :
    IntervalIntegrable (fun θ=>min θ (1-θ)*iteratedDeriv 2
      (responseGridMixFunctional (n:=n) μ ν j β t lam) θ) volume 0 1 ∧
    (∫θ in (0:ℝ)..1,min θ (1-θ)*iteratedDeriv 2
      (responseGridMixFunctional (n:=n) μ ν j β t lam) θ)≤
      responseGridMixFunctional (n:=n) μ ν j β t lam 0+
        responseGridMixFunctional (n:=n) μ ν j β t lam 1-
          2*responseGridMixFunctional (n:=n) μ ν j β t lam (1/2):=by
  let f:=responseGridMixFunctional (n:=n) μ ν j β t lam
  have hs (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1):ContDiffAt ℝ ∞ f θ:=
    contDiffAt_vectorGridResponseFunctional_mix μ ν j β t lam θ ht.le hθ
  apply response_nonnegative_curvature_midpoint_bound f (deriv f) (iteratedDeriv 2 f)
    (continuousOn_vectorGridResponseFunctional_mix hn μ ν j β t lam ht.le)
    (convexOn_vectorGridResponseFunctional_mix μ ν j β t lam hβ ht.le hlam)
  · intro θ hθ
    exact ((hs θ hθ).differentiableAt (by norm_num)).hasDerivAt
  · intro θ hθ
    have hd:=((hs θ hθ).derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hd.hasDerivAt
  · intro θ hθ
    exact iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg hn μ ν j β t lam θ hβ ht hlam hθ
  · intro a ha b hb hab
    have hc : ContinuousOn (iteratedDeriv 2 f) (uIcc a b):=by
      rw [uIcc_of_le hab]
      intro θ hθ
      have hθ01 : θ∈Ioo (0:ℝ) 1:=⟨ha.1.trans_le hθ.1,hθ.2.trans_lt hb.2⟩
      have hd:=((hs θ hθ01).derivWithin (m:=1) (by norm_num)).derivWithin (m:=0) (by norm_num)
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hd.continuousAt.continuousWithinAt
    exact hc.intervalIntegrable

theorem tendsto_responseGridMixFunctional (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1) :
    Tendsto (fun j=>responseGridMixFunctional (n:=n) μ ν j β t lam θ) atTop
      (nhds (responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam)):=by
  have hh:=((continuous_vectorMeasureFunctional n hn β t (lam/β) ht).div_const β).tendsto
    (Paper.parisiMix μ ν θ) |>.comp
      ((FRSB.tendsto_parisiGridMeasure (Paper.parisiMix μ ν θ)).comp tendsto_vectorDyadicIndex)
  convert hh using 1
  · funext j
    unfold responseGridMixFunctional responseEnergyFunctional
    dsimp only [Function.comp_def]
    rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ hθ]
  · rfl

theorem response_midpoint_lower_of_grid_response (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β t lam : ℝ) (hβ : 0<β) (ht : t<1) (hlam : 0≤lam)
    (Sj Dj : ℕ→ℝ→ℝ) (S D Y : ℝ→ℝ) (C a : ℝ)
    (hC : 0≤C) (ha : 0≤a) (ham : a≤1/2)
    (hS : ∀θ∈Ioo (0:ℝ) 1,Tendsto (fun j=>Sj j θ) atTop (nhds (S θ)))
    (hD : ∀θ∈Ioo (0:ℝ) 1,Tendsto (fun j=>Dj j θ) atTop (nhds (D θ)))
    (hgrid : ∀j,∀θ∈Ioo (0:ℝ) 1,(1-t)^3*(Sj j θ)^2≤
      iteratedDeriv 2 (responseGridMixFunctional (n:=n) μ ν j β t lam) θ*Dj j θ)
    (hY : ∀θ∈Ioo a (1-a),0<Y θ)
    (hDY : ∀θ∈Ioo a (1-a),D θ≤Y θ)
    (hSig : ∀θ∈Ioo a (1-a),C*Y θ≤(1-t)^3*(S θ)^2) :
    C*(1/4-a^2)≤responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-
        2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam:=by
  let F₂:=fun j=>iteratedDeriv 2 (responseGridMixFunctional (n:=n) μ ν j β t lam)
  let Gapj:=fun j=>responseGridMixFunctional (n:=n) μ ν j β t lam 0+
    responseGridMixFunctional (n:=n) μ ν j β t lam 1-2*responseGridMixFunctional (n:=n) μ ν j β t lam (1/2)
  have hg:=((tendsto_responseGridMixFunctional hn μ ν β t lam 0 ht.le (by norm_num)).add
    (tendsto_responseGridMixFunctional hn μ ν β t lam 1 ht.le (by norm_num))).sub
      ((tendsto_const_nhds (x:=2)).mul
        (tendsto_responseGridMixFunctional hn μ ν β t lam (1/2) ht.le (by norm_num)))
  have hg' : Tendsto Gapj atTop (nhds (responseEnergyFunctional n μ β t lam+
      responseEnergyFunctional n ν β t lam-2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam)):=by
    simpa only [Gapj,Paper.parisiMix_zero,Paper.parisiMix_one] using hg
  refine response_midpoint_of_curvature_limit_lower F₂ Gapj _ C a hC ha ham
    (fun j=>(responseGridMix_weighted_curvature_bound hn μ ν j β t lam hβ ht hlam).1)
    (fun j θ hθ=>iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg hn μ ν j β t lam θ hβ ht hlam hθ)
    (fun j=>(responseGridMix_weighted_curvature_bound hn μ ν j β t lam hβ ht hlam).2) hg' ?_
  intro θ hθ
  have hθ01 : θ∈Ioo (0:ℝ) 1:=⟨ha.trans_lt hθ.1,by linarith [hθ.2]⟩
  exact response_curvature_lower_sequence (fun j=>Sj j θ) (fun j=>Dj j θ) (fun j=>F₂ j θ)
    (S θ) (D θ) (Y θ) ((1-t)^3) C (hS θ hθ01) (hD θ hθ01)
    (hY θ hθ) (hDY θ hθ) (hSig θ hθ)
    (fun j=>iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg hn μ ν j β t lam θ hβ ht hlam hθ01)
    (fun j=>hgrid j θ hθ01)

end QuantitativePaper
