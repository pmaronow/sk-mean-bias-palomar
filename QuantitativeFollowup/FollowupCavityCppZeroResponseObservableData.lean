module
public import FourPapersCommon.FiniteStateCascadeSmoothJets
public import FourPapersCommon.FiniteStateCascadeHessianTelescoping
public import QuantitativePaper.BoundedJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSecondMean

@[expose] public section

/-! Honest bounded-C2 data for the actual finite posterior observables.
The scalar spin mean, each rest spin mean, and their square products are
constructed from the genuine finite potential. No response identity or
observable regularity conclusion is supplied as an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal BigOperators ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityFiniteEnergyFeatureMean (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (b : FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H b

theorem boundedJets_cavityFiniteEnergyFeatureMean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (j : ℕ) (b : FiniteStateField S) : BoundedJets (cavityFiniteEnergyFeatureMean V a L j b) :=by
  have hU : BoundedPositiveJets (finiteStateGaussianTerminalCascade V a L j) :=by
    refine ⟨contDiff_finiteStateGaussianTerminalCascade V a ha L j,?_⟩
    intro r hr
    obtain ⟨_,C,hC,hBounds⟩:=finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r j
    exact ⟨C^r,pow_nonneg (by linarith) _,fun H=>hBounds r hr le_rfl H⟩
  exact hU.boundedJets_fderiv_apply b

theorem cavityFiniteEnergyFeatureMean_eq_gibbsMean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (j : ℕ) (b H : FiniteStateField S) :
    cavityFiniteEnergyFeatureMean V a L j b H=
      ∫σ,b σ ∂finiteStateCascadeGibbsKernel V a L j H :=by
  exact fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j H b

def cavityFiniteEnergyRestOverlap {ι : Type} [Fintype ι] (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (b : ι→FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹*∑i,(cavityFiniteEnergyFeatureMean V a L j (b i) H)^2

theorem boundedJets_cavityFiniteEnergyRestOverlap {ι : Type} [Fintype ι]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (b : ι→FiniteStateField S) :
    BoundedJets (cavityFiniteEnergyRestOverlap V a L j b) :=by
  have hm (i : ι):=boundedJets_cavityFiniteEnergyFeatureMean V a ha L j (b i)
  have hh:=boundedJets_finite_sum Finset.univ
    (fun i H=>cavityFiniteEnergyFeatureMean V a L j (b i) H*cavityFiniteEnergyFeatureMean V a L j (b i) H)
    (fun i _=>(hm i).mul (hm i))
  change BoundedJets (fun H=>(Fintype.card ι : ℝ)⁻¹*∑i,(cavityFiniteEnergyFeatureMean V a L j (b i) H)^2)
  simpa only [pow_two] using hh.const_mul (Fintype.card ι : ℝ)⁻¹

structure CavityPosteriorC2Data {Z : Type} [MeasurableSpace Z]
    (F : FiniteStateField S→Z→ℝ) where
  measurable_value : ∀H,Measurable (F H)
  measurable_first : ∀H,Measurable (fun z=>fderiv ℝ (fun Q=>F Q z) H)
  measurable_second : ∀H,Measurable (fun z=>fderiv ℝ (fderiv ℝ (fun Q=>F Q z)) H)
  smooth : ∀z,ContDiff ℝ 2 (fun Q=>F Q z)
  bound : ℝ
  firstBound : ℝ
  secondBound : ℝ
  bound_nonneg : 0 ≤ bound
  firstBound_nonneg : 0 ≤ firstBound
  secondBound_nonneg : 0 ≤ secondBound
  value_bound : ∀H z,|F H z| ≤ bound
  first_bound : ∀H z,‖fderiv ℝ (fun Q=>F Q z) H‖ ≤ firstBound
  second_bound : ∀H z,‖fderiv ℝ (fderiv ℝ (fun Q=>F Q z)) H‖ ≤ secondBound

noncomputable def cavityPosteriorTranslatedC2Data {Z : Type} [MeasurableSpace Z]
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : Z→FiniteStateField S) (hW : Measurable W) :
    CavityPosteriorC2Data (fun H z=>f (H+W z)) :=by
  classical
  let B:=Classical.choose (hf.2 0)
  let D:=Classical.choose (hf.2 1)
  let E:=Classical.choose (hf.2 2)
  have hB:= (Classical.choose_spec (hf.2 0)).1
  have hD:= (Classical.choose_spec (hf.2 1)).1
  have hE:= (Classical.choose_spec (hf.2 2)).1
  have hBb:= (Classical.choose_spec (hf.2 0)).2
  have hDb:= (Classical.choose_spec (hf.2 1)).2
  have hEb:= (Classical.choose_spec (hf.2 2)).2
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f):=hf.1.fderiv_right (by simp)
  have hddf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)):=hdf.fderiv_right (by simp)
  have hfirst (H z) : fderiv ℝ (fun Q=>f (Q+W z)) H=fderiv ℝ f (H+W z) :=
    fderiv_comp_add_right (W z)
  have hsecond (H z) : fderiv ℝ (fderiv ℝ (fun Q=>f (Q+W z))) H=
      fderiv ℝ (fderiv ℝ f) (H+W z) :=by
    have he : fderiv ℝ (fun Q=>f (Q+W z))=fun Q=>fderiv ℝ f (Q+W z) :=
      funext fun Q=>hfirst Q z
    rw [he,fderiv_comp_add_right]
  refine ⟨?_,?_,?_,?_,B,D,E,hB,hD,hE,?_,?_,?_⟩
  · intro H
    exact hf.1.continuous.measurable.comp (measurable_const.add hW)
  · intro H
    simp_rw [hfirst]
    exact hdf.continuous.measurable.comp (measurable_const.add hW)
  · intro H
    simp_rw [hsecond]
    exact hddf.continuous.measurable.comp (measurable_const.add hW)
  · intro z
    exact (hf.1.comp (contDiff_id.add contDiff_const)).of_le (by simp)
  · intro H z
    dsimp only [B]
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hBb (H+W z)
  · intro H z
    rw [hfirst,←norm_iteratedFDeriv_one]
    exact hDb (H+W z)
  · intro H z
    rw [hsecond,←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact hEb (H+W z)

noncomputable def cavityPosteriorFeatureSquareData (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N j i : ℕ)
    (b : FiniteStateField S) :
    CavityPosteriorC2Data (fun H (z : (Fin N→Field n)×S)=>
      (cavityFiniteEnergyFeatureMean V a L j b
        (H+cascadePosteriorHistory L N 0 z.1 (Fin.ofNat (N+1) i)))^2) :=by
  let f:=cavityFiniteEnergyFeatureMean V a L j b
  have hf:=boundedJets_cavityFiniteEnergyFeatureMean V a ha L j b
  let W:=fun z : (Fin N→Field n)×S=>cascadePosteriorHistory L N 0 z.1 (Fin.ofNat (N+1) i)
  have hW : Measurable W:=by
    exact (measurable_pi_apply _).comp ((measurable_cascadePosteriorHistory L N 0).comp measurable_fst)
  simpa only [pow_two] using cavityPosteriorTranslatedC2Data (fun H=>f H*f H) (hf.mul hf) W hW

noncomputable def cavityPosteriorRestOverlapData {ι : Type} [Fintype ι]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N j i : ℕ) (b : ι→FiniteStateField S) :
    CavityPosteriorC2Data (fun H (z : (Fin N→Field n)×S)=>
      cavityFiniteEnergyRestOverlap V a L j b
        (H+cascadePosteriorHistory L N 0 z.1 (Fin.ofNat (N+1) i))) :=by
  apply cavityPosteriorTranslatedC2Data _ (boundedJets_cavityFiniteEnergyRestOverlap V a ha L j b)
  exact (measurable_pi_apply _).comp ((measurable_cascadePosteriorHistory L N 0).comp measurable_fst)

end QuantitativeFollowup
