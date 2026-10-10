module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseCovarianceDifferentiation
public import FourPapersCommon.FiniteStateCascadeAllJets
public import QuantitativePaper.NormalizedExponentialObservableJets
public import QuantitativePaper.VectorTailTranslation

@[expose] public section

/-! All jets of a genuine bounded smooth retained-field observable under the
actual normalized finite posterior. The observable and density both move
with the initial field; normalization provides the integrable jet bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem aestronglyMeasurable_cavityPosteriorTranslated_exponentialJet
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j r : ℕ)
    (f : FiniteStateField S→ℝ) (hf : ContDiff ℝ ∞ f)
    (W : (Fin j→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    AEStronglyMeasurable (fun z : (Fin j→Field n)×S=>iteratedFDeriv ℝ r
      (fun Q=>Real.exp (cascadePosteriorLogDensity V a L j Q z) • f (Q+W z.1)) H)
      (cascadePosteriorGaussianBase S (Fin n) j) :=by
  letI : MeasurableSpace (FiniteStateField S [×r]→L[ℝ]ℝ):=borel _
  haveI : BorelSpace (FiniteStateField S [×r]→L[ℝ]ℝ):=⟨rfl⟩
  let J:=fun z : (Fin j→Field n)×S=>iteratedFDeriv ℝ r
    (fun Q=>Real.exp (cascadePosteriorLogDensity V a L j Q z) • f (Q+W z.1)) H
  have hc(σ:S):Continuous (fun z : Fin j→Field n=>J (z,σ)):=by
    let F:=fun z : (Fin j→Field n)×FiniteStateField S=>
      Real.exp (cascadePosteriorLogDensity V a L j z.2 (z.1,σ)) • f (z.2+W z.1)
    have hF:ContDiff ℝ ∞ F:=
      ((contDiff_cascadePosteriorLogDensity V a ha L j σ).comp
        (contDiff_snd.prodMk contDiff_fst)).exp.smul
          (hf.comp (contDiff_snd.add (W.contDiff.comp contDiff_fst)))
    exact (continuous_fieldSlice_iteratedFDeriv F hF r).comp
      (continuous_id.prodMk (continuous_const (y:=H)))
  have hm:Measurable J:=measurable_from_prod_countable_left fun σ=>(hc σ).measurable
  have hs:TopologicalSpace.IsSeparable (⋃σ:S,range (fun z : Fin j→Field n=>J (z,σ))):=
    .iUnion fun σ=>TopologicalSpace.isSeparable_range (hc σ)
  apply StronglyMeasurable.aestronglyMeasurable
  apply stronglyMeasurable_iff_measurable_separable.mpr
  refine ⟨hm,hs.mono ?_⟩
  rintro _ ⟨⟨z,σ⟩,rfl⟩
  exact mem_iUnion.mpr ⟨σ,mem_range.mpr ⟨z,rfl⟩⟩

theorem cavityPosteriorTranslatedMean_smooth_bounded_jets
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j r : ℕ)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin j→Field n)→L[ℝ]FiniteStateField S) :
    ContDiff ℝ r (cavityPosteriorTranslatedMean V a L j f (fun z=>W z.1)) ∧
      ∃B:ℝ,0≤B ∧ ∀i,i≤r → ∀H,
        ‖iteratedFDeriv ℝ i (cavityPosteriorTranslatedMean V a L j f (fun z=>W z.1)) H‖≤B :=by
  choose C hC hb using hf.2
  let A:ℝ:=1+∑i∈Finset.range (r+1),C i
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => hC i))
  have hCA(i)(hi:i≤r):C i≤A:=by
    have hh:=Finset.single_le_sum (fun l _=>hC l) (Finset.mem_range.mpr (by omega : i<r+1))
    dsimp only [A];linarith
  let K:=finiteJetPowerBound (fun i=>1+finiteStateSpatialJetBound S n i) r
  have hK:1≤K:=finiteJetPowerBound_ge_one _ _
  have hLBound (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) (H : FiniteStateField S)
      (z : (Fin j → Field n) × S) :
      ‖iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤K^i:=by
    apply (norm_cascadePosteriorLogDensity_jet_le V a ha ha1 hdec L i 1
      (finiteStateSpatialJetBound S n i) (finiteStateSpatialJetBound_nonneg S n i)
      (fun l Q=>norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec L l i hi Q)
      (fun w Q σ=>by
        by_cases hi1:i=1
        · rw [hi1];exact norm_cascadeTerminal_affine_firstJet_le_one V w Q σ
        · rw [cascadeTerminal_affine_higherJet_zero V w Q σ i (by omega),norm_zero];norm_num)
      j H z).trans
    exact finite_jet_bound_le_power (fun l=>1+finiteStateSpatialJetBound S n l) r i hi hir
  have hVBound (i : ℕ) (hir : i ≤ r) (H : FiniteStateField S)
      (z : (Fin j → Field n) × S) :
      ‖iteratedFDeriv ℝ i (fun Q=>f (Q+W z.1)) H‖≤A*K^i:=by
    rw [iteratedFDeriv_comp_add_right]
    exact (hb i _).trans ((hCA i hir).trans (le_mul_of_one_le_right hA (one_le_pow₀ hK)))
  have hh:=exponentialParameterizedExpectation_jets r (cascadePosteriorGaussianBase S (Fin n) j)
    (cascadePosteriorLogDensity V a L j) (fun H z=>f (H+W z.1)) K A (fun _=>A)
    (zero_le_one.trans hK) (fun _=>hA)
    (fun z=>((contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp
      (contDiff_id.prodMk contDiff_const)).of_le (by simp))
    (fun z=>(hf.1.comp (contDiff_id.add contDiff_const)).of_le (by simp))
    ⟨2,fun z=>cascadePosteriorLogDensity_lipschitz V a ha ha1 hdec L j z⟩
    hLBound hVBound
    (fun i _ H=>aestronglyMeasurable_cavityPosteriorTranslated_exponentialJet V a ha L j i f hf.1 W H)
    (fun H=>(integrable_cascadePosterior_exp V a ha L j H).mul_const A)
    (fun H=>by rw [integral_mul_const,integral_cascadePosterior_exp V a ha L j H,one_mul])
  have he:(fun H=>∫z,Real.exp (cascadePosteriorLogDensity V a L j H z) • f (H+W z.1)
      ∂cascadePosteriorGaussianBase S (Fin n) j)=
      cavityPosteriorTranslatedMean V a L j f (fun z=>W z.1):=by
    funext H
    exact (integral_cascadePosteriorGaussianLaw_exp V a ha L j H (fun z=>f (H+W z.1))).symm
  rw [he] at hh
  let B:=∑i∈Finset.range (r+1),exponentialObservableJetCoefficient i K*A
  have hB0(i):0≤exponentialObservableJetCoefficient i K*A:=
    mul_nonneg (exponentialObservableJetCoefficient_nonneg i K (zero_le_one.trans hK)) hA
  refine ⟨hh.1,B,Finset.sum_nonneg (fun i _=>hB0 i),?_⟩
  intro i hi H
  exact (hh.2 i hi H).trans (Finset.single_le_sum (fun l _=>hB0 l)
    (Finset.mem_range.mpr (by omega : i<r+1)))

theorem boundedJets_cavityPosteriorTranslatedMean
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin j→Field n)→L[ℝ]FiniteStateField S) :
    BoundedJets (cavityPosteriorTranslatedMean V a L j f (fun z=>W z.1)) :=by
  refine ⟨contDiff_infty.mpr (fun r=>(cavityPosteriorTranslatedMean_smooth_bounded_jets
    V a ha ha1 hdec L j r f hf W).1),?_⟩
  intro r
  obtain ⟨B,hB,hb⟩:=(cavityPosteriorTranslatedMean_smooth_bounded_jets V a ha ha1 hdec L j r f hf W).2
  exact ⟨B,hB,hb r le_rfl⟩

end QuantitativeFollowup
