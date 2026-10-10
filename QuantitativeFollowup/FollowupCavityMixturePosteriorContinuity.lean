module
public import QuantitativeFollowup.FollowupCavityMixtureDensityContinuity
public import QuantitativeFollowup.FollowupCavityMixtureInputContinuity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseCovarianceDifferentiation

@[expose] public section

/-! Genuine joint continuity of normalized retained posterior expectations
for a continuous family of Gaussian input maps, including singular maps. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology ContDiff BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S P : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [TopologicalSpace P] [FirstCountableTopology P] {n : ℕ}

private theorem continuous_cavityHistory_input_family
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (N m : ℕ) (z : Fin m→Field n) :
    Continuous (fun w : P×FiniteStateField S=>
      independentHistory (cascadePosteriorUpdate (L w.1) N) m (w.2,z)) :=by
  induction m with
  | zero => exact continuous_pi (fun _=>continuous_snd)
  | succ m ih =>
    have hh:=ih (fun i=>z i.castSucc)
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · convert ((continuous_apply (Fin.last m)).comp hh).add
        (((hL (N-1-m)).comp continuous_fst).clm_apply (continuous_const (y:=z (Fin.last m)))) using 1
      funext w
      simp only [independentHistory,Fin.snoc_last,cascadePosteriorUpdate,Function.comp_def,Pi.add_apply]
    · convert (continuous_apply j).comp hh using 1
      funext w
      simp only [independentHistory,Fin.snoc_castSucc,Function.comp_def]

theorem continuous_cavityPosteriorHistory_input_family
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (N : ℕ) (z : Fin N→Field n) :
    Continuous (fun w : P×FiniteStateField S=>cascadePosteriorHistory (L w.1) N w.2 z) :=
  continuous_cavityHistory_input_family L hL N N z

theorem continuous_cavityPosteriorLogDensity_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (N : ℕ) (z : (Fin N→Field n)×S) :
    Continuous (fun w : P×FiniteStateField S=>cascadePosteriorLogDensity V a (L w.1) N w.2 z) :=by
  have hh:=continuous_cavityPosteriorHistory_input_family L hL N z.1
  have hU(i):Continuous (fun w : P×FiniteStateField S=>
      cascadePosteriorHistoryPotential V a (L w.1) N i w.2 z.1):=by
    exact (continuous_cavityCascade_input_family V a ha L hL (N-i)).comp
      (continuous_fst.prodMk ((continuous_apply (Fin.ofNat (N+1) i)).comp hh))
  unfold cascadePosteriorLogDensity
  exact ((continuous_const.add
    ((EuclideanSpace.proj z.2).continuous.comp ((continuous_apply (Fin.last N)).comp hh))).sub
      (hU N)).add (continuous_finset_sum _ fun i _=>
        continuous_const.mul ((hU (i+1)).sub (hU i)))

theorem continuous_cavityPosteriorTranslatedMean_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (N : ℕ)
    (f : P×FiniteStateField S→ℝ) (hf : Continuous f)
    (W : P→(Fin N→Field n)→L[ℝ]FiniteStateField S) (hW : Continuous W)
    (B : ℝ) (hB : 0≤B) (hb : ∀p H,‖f (p,H)‖≤B) :
    Continuous (fun w : P×FiniteStateField S=>cavityPosteriorTranslatedMean V a (L w.1) N
      (fun H=>f (w.1,H)) (fun z=>W w.1 z.1) w.2) :=by
  let μ:=cascadePosteriorGaussianBase S (Fin n) N
  let ρ:=fun w : P×FiniteStateField S=>fun z : (Fin N→Field n)×S=>
    Real.exp (cascadePosteriorLogDensity V a (L w.1) N w.2 z)
  let F:=fun w : P×FiniteStateField S=>fun z : (Fin N→Field n)×S=>
    f (w.1,w.2+W w.1 z.1)
  have hF(w):AEStronglyMeasurable (F w) μ:=by
    have hfp : Continuous (fun H : FiniteStateField S=>f (w.1,H)):=
      hf.comp (continuous_const.prodMk continuous_id)
    exact (hfp.measurable.comp (measurable_const.add
      ((W w.1).measurable.comp measurable_fst))).aestronglyMeasurable
  have he(w):cavityPosteriorTranslatedMean V a (L w.1) N
      (fun H=>f (w.1,H)) (fun z=>W w.1 z.1) w.2=∫z,ρ w z*F w z∂μ :=by
    exact integral_cascadePosteriorGaussianLaw_exp V a ha (L w.1) N w.2 _
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro w0
  exact continuousAt_cavityDensity_bounded_moving_integral ρ F w0
    (fun w=>integrable_cascadePosterior_exp V a ha (L w.1) N w.2)
    (fun w z=>(Real.exp_pos _).le)
    (fun w=>integral_cascadePosterior_exp V a ha (L w.1) N w.2)
    (fun z=>(Real.continuous_exp.comp (continuous_cavityPosteriorLogDensity_input_family V a ha L hL N z)).continuousAt)
    hF (fun z=>(hf.comp (continuous_fst.prodMk
      (continuous_snd.add (hW.comp continuous_fst |>.clm_apply continuous_const)))).continuousAt)
    B hB (fun w z=>hb w.1 _)

end QuantitativeFollowup
