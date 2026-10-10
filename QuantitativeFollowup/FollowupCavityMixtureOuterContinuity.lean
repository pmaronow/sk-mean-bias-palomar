module
public import QuantitativeFollowup.FollowupCavityMixturePosteriorContinuity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLogJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterMean
public import QuantitativeFollowup.GaussianShiftFiniteMesh

@[expose] public section

/-! Actual outer posterior value continuity for a varying input family.
The root Gaussian tilt remains part of the normalized law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S P J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [TopologicalSpace P] [FirstCountableTopology P] {n : ℕ}

theorem continuous_cavityOuterPosteriorLogNormalizer_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    Continuous (fun w : P×FiniteStateField S=>
      Real.log (cavityOuterPosteriorNormalizer V a (L w.1) s N R w.2)) :=by
  have hc : Continuous (fun w : P×FiniteStateField S=>finiteStateGaussianStep s
      (R.comp (cavityOuterGaussianCoordinates J))
      (finiteStateGaussianTerminalCascade V a (L w.1) N) w.2):=
    continuous_finiteStateGaussianStep_family s
      (fun w : P×FiniteStateField S=>finiteStateGaussianTerminalCascade V a (L w.1) N)
      ((continuous_cavityCascade_input_family V a ha L hL N).comp
        ((continuous_fst.fst).prodMk continuous_snd)) 1
      (fun w=>finiteStateGaussianTerminalCascade_lipschitz V a ha (L w.1) N)
      (fun _=>R.comp (cavityOuterGaussianCoordinates J)) continuous_const
      (fun w=>w.2) continuous_snd
  have he(w : P×FiniteStateField S):Real.log (cavityOuterPosteriorNormalizer V a (L w.1) s N R w.2)=
      s*finiteStateGaussianStep s (R.comp (cavityOuterGaussianCoordinates J))
        (finiteStateGaussianTerminalCascade V a (L w.1) N) w.2 :=by
    have hh:=congrFun (cavityOuterPosteriorLogNormalizer_eq_mass_step V a ha (L w.1) s N R) w.2
    rw [gaussianShiftColeHopf_eq_finiteStateGaussianStep] at hh
    exact hh
  simp_rw [he]
  exact continuous_const.mul hc

theorem continuous_cavityOuterPosteriorNormalizer_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    Continuous (fun w : P×FiniteStateField S=>cavityOuterPosteriorNormalizer V a (L w.1) s N R w.2) :=by
  have hc:=Real.continuous_exp.comp (continuous_cavityOuterPosteriorLogNormalizer_input_family V a ha L hL s N R)
  apply hc.congr
  intro w
  exact Real.exp_log (finiteCascadeTreeGaussianNormalizer_pos V a ha (L w.1) s N R w.2)

theorem continuous_cavityOuterPosteriorMean_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : P×FiniteStateField S→ℝ) (hf : Continuous f)
    (W : P→(Fin N→Field n)→L[ℝ]FiniteStateField S) (hW : Continuous W)
    (B : ℝ) (hB : 0≤B) (hb : ∀p H,‖f (p,H)‖≤B) :
    Continuous (fun w : P×FiniteStateField S=>cavityOuterPosteriorMean V a (L w.1) s N R
      (fun H=>f (w.1,H)) (W w.1) w.2) :=by
  let μ:=(stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N)
  let ρ:=fun w : P×FiniteStateField S=>fun z : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
    Real.exp (cavityOuterPosteriorLogDensity V a (L w.1) s N R w.2 z)
  let F:=fun w : P×FiniteStateField S=>fun z : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
    f (w.1,w.2+R z.1+W w.1 z.2.1)
  have hρ(z):Continuous (fun w : P×FiniteStateField S=>ρ w z):=by
    have hQ : Continuous (fun w : P×FiniteStateField S=>(w.1,w.2+R z.1)):=
      continuous_fst.prodMk (continuous_snd.add continuous_const)
    have hd : Continuous (fun w : P×FiniteStateField S=>
        cavityOuterPosteriorLogDensity V a (L w.1) s N R w.2 z) :=
      ((((continuous_cavityCascade_input_family V a ha L hL N).comp hQ).const_mul s).add
        ((continuous_cavityPosteriorLogDensity_input_family V a ha L hL N z.2).comp hQ)).sub
          (continuous_cavityOuterPosteriorLogNormalizer_input_family V a ha L hL s N R)
    exact Real.continuous_exp.comp hd
  have hF(w):AEStronglyMeasurable (F w) μ:=by
    have hfp:Continuous (fun H : FiniteStateField S=>f (w.1,H)):=
      hf.comp (continuous_const.prodMk continuous_id)
    exact (hfp.measurable.comp (show Measurable
      (fun z : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>w.2+R z.1+W w.1 z.2.1) from by fun_prop)).aestronglyMeasurable
  have he(w):cavityOuterPosteriorMean V a (L w.1) s N R (fun H=>f (w.1,H)) (W w.1) w.2=
      ∫z,ρ w z*F w z∂μ :=by
    exact integral_cavityOuterPosteriorLaw_exp V a ha (L w.1) s N R w.2 _
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro w0
  exact continuousAt_cavityDensity_bounded_moving_integral ρ F w0
    (fun w=>integrable_cavityOuterPosterior_exp V a ha (L w.1) s N R w.2)
    (fun w z=>(Real.exp_pos _).le)
    (fun w=>integral_cavityOuterPosterior_exp V a ha (L w.1) s N R w.2)
    (fun z=>(hρ z).continuousAt) hF
    (fun z=>(hf.comp (continuous_fst.prodMk ((continuous_snd.add continuous_const).add
      (hW.comp continuous_fst |>.clm_apply continuous_const)))).continuousAt)
    B hB (fun w z=>hb w.1 _)

end QuantitativeFollowup
