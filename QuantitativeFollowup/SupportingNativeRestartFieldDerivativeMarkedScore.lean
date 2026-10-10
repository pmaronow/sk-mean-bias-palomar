module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalBounds
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeRecordedScore

@[expose] public section

/-! Exact directional differentiation of the actual finite restarted
coordinate square, retaining its genuine terminal Gibbs mark. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

def cascadePosteriorRecordedSquareResponse (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N i : ℕ) (K W : FiniteStateField S)
    (z : FiniteHistory (FiniteStateField S) (N+1)×S) : ℝ :=
  2*cascadePosteriorRecordedMean V a L (N+1) i K z.1*
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N+1-i)))
      (historyExtended z.1 i) W K+
    (cascadePosteriorRecordedMean V a L (N+1) i K z.1)^2*
      cascadePosteriorRecordedScore V a L N W z

theorem measurable_cascadePosteriorRecordedSquareResponse (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (N i : ℕ) (K W : FiniteStateField S) :
    Measurable (cascadePosteriorRecordedSquareResponse V a L N i K W) := by
  have hs:=contDiff_finiteStateGaussianTerminalCascade V a ha L (N+1-i)
  have hm : Measurable (fun z : FiniteHistory (FiniteStateField S) (N+1)×S=>
      cascadePosteriorRecordedMean V a L (N+1) i K z.1) := by
    change Measurable ((fun h : FiniteHistory (FiniteStateField S) (N+1)=>
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N+1-i)) (h (Fin.ofNat (N+2) i)) K) ∘ Prod.fst)
    exact (((hs.fderiv_right (m:=∞) (by simp)).continuous.comp
      (continuous_apply (Fin.ofNat (N+2) i))).clm_apply continuous_const).measurable.comp measurable_fst
  have hH : Measurable (fun z : FiniteHistory (FiniteStateField S) (N+1)×S=>
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N+1-i)))
        (historyExtended z.1 i) W K) := by
    change Measurable ((fun h : FiniteHistory (FiniteStateField S) (N+1)=>
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N+1-i)))
        (h (Fin.ofNat (N+2) i)) W K) ∘ Prod.fst)
    exact (((((hs.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).continuous.comp
      (continuous_apply (Fin.ofNat (N+2) i))).clm_apply
        continuous_const).clm_apply continuous_const).measurable.comp measurable_fst
  exact ((measurable_const.mul hm).mul hH).add
    (hm.pow_const 2 |>.mul (measurable_cascadePosteriorRecordedScore V a ha L N W))

theorem fderiv_cascadePosterior_retained_square_recorded (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N i : ℕ) (K H W : FiniteStateField S) :
    fderiv ℝ (fun Q=>∫z,cascadePosteriorRetainedSquare V a L (N+1) i K Q z
      ∂cascadePosteriorGaussianLaw V a L (N+1) Q) H W=
      ∫z,cascadePosteriorRecordedSquareResponse V a L N i K W
        (cascadePosteriorHistory L (N+1) H z.1,z.2)
        ∂cascadePosteriorGaussianLaw V a L (N+1) H := by
  rw [fderiv_cascadePosterior_retained_square_stieltjes V a ha ha1 hdec]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    let f:=fun Q=>cascadePosteriorRetainedMean V a L (N+1) i K Q z
    have hd : DifferentiableAt ℝ f H :=
      ((contDiff_cascadePosteriorRetainedMean V a ha L (N+1) i K).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp) H
    change fderiv ℝ (f^2) H W+_=_
    rw [fderiv_pow 2 hd,ContinuousLinearMap.smul_apply]
    simp only [Nat.reduceSub,Nat.cast_ofNat,pow_one,smul_eq_mul,nsmul_eq_mul,f]
    rw [fderiv_cascadePosteriorRetainedMean_apply V a ha,
      cavityFinitePosteriorScore_eq_recorded V a ha]
    rfl

theorem fderiv_anisotropicFiniteRestartPosteriorSquare_marked (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (v : ℕ) (i : Fin n) (x w : Field n) :
    fderiv ℝ (anisotropicFiniteRestartPosteriorSquare D s g q v i) x w=
      ∫z,cascadePosteriorRecordedSquareResponse (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp
          (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+1) v (cavityCoordinateFeature i)
        (anisotropicEnergyMap D (anisotropicFieldInjection n w))
        (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) z.1,z.2)
        ∂anisotropicFiniteRestartMarkedLaw D s g q (anisotropicInverseNoiseMap D x) := by
  let cs:=vectorClampedScheme s q q.property
  let a:=anisotropicSchemeMass cs
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let K:=cavityCoordinateFeature i
  let G:=fun H=>∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
    a L (k+2) v K H z ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0) a L (k+2) H
  let A:=anisotropicRestartFieldEnergyMap D
  let c:=anisotropicEnergyMap D (anisotropicDisorderInjection n g)
  have hG : Differentiable ℝ G := fun H=>(hasFDerivAt_cascadePosterior_retained_square
    (fun _ : Configuration n=>0) a (anisotropicSchemeMass_nonneg cs)
    (anisotropicSchemeMass_le_one cs 0) (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs))
    L (k+2) v K H).differentiableAt
  have he : anisotropicFiniteRestartPosteriorSquare D s g q v i=fun x=>G (c+A x) := by
    funext x
    simp only [anisotropicFiniteRestartPosteriorSquare,G,c,A,anisotropicRestartFieldEnergyMap,
      ContinuousLinearMap.comp_apply,map_add,a,L,K,cs]
  rw [he]
  have hd:=fderiv_comp x (hG (c+A x)) (A.hasFDerivAt.const_add c).differentiableAt
  dsimp only [Function.comp_def] at hd
  rw [hd]
  have hA : fderiv ℝ (fun x=>c+A x) x=A := (A.hasFDerivAt.const_add c).fderiv
  rw [hA,ContinuousLinearMap.comp_apply]
  change fderiv ℝ G (c+A x) (A w)=_
  rw [fderiv_cascadePosterior_retained_square_recorded _ a
    (anisotropicSchemeMass_nonneg cs) (anisotropicSchemeMass_le_one cs 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs))]
  have hp : c+A x=anisotropicEnergyMap D
      (anisotropicDisorderInjection n g+anisotropicUnitInput D (anisotropicInverseNoiseMap D x)) := by
    simp only [c,A,anisotropicRestartFieldEnergyMap,ContinuousLinearMap.comp_apply,
      anisotropicUnitInput,anisotropicNoiseMap_inverseNoise,map_add]
  rw [hp]
  exact integral_anisotropicFiniteRestart_marked_record D s g q (anisotropicInverseNoiseMap D x)
    (cascadePosteriorRecordedSquareResponse (fun _ : Configuration n=>0) a L (k+1) v K (A w))
    (measurable_cascadePosteriorRecordedSquareResponse _ a (anisotropicSchemeMass_nonneg cs) L _ _ _ _)

end QuantitativeFollowup
