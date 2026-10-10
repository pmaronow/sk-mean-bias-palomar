module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLogJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterMean
public import FourPapersCommon.ExponentialObservableIntegralJets

@[expose] public section

/-! Actual outer posterior differentiation, retaining the root Gaussian
and every auxiliary coordinate. No derivative of a normalized expectation
is supplied as an assumption. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem continuous_outer_fixed_slice_jet {A E F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : A×E→F) (hU : ContDiff ℝ ∞ U) (r : ℕ) (x : E) :
    Continuous (fun z : A=>iteratedFDeriv ℝ r (fun y=>U (z,y)) x) :=by
  have hc:=continuous_fieldSlice_iteratedFDeriv U hU r
  exact hc.comp (continuous_id.prodMk (continuous_const (y:=x)))

theorem aestronglyMeasurable_cavityOuterPosterior_exponentialJet
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : ContDiff ℝ ∞ f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    AEStronglyMeasurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r (fun Q=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q p) •
        f (Q+R p.1+W p.2.1)) H)
      ((stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N)) :=by
  letI : MeasurableSpace (FiniteStateField S [×r]→L[ℝ]ℝ):=borel _
  haveI : BorelSpace (FiniteStateField S [×r]→L[ℝ]ℝ):=⟨rfl⟩
  let A:=FiniteStateGaussianInput J×(Fin N→Field n)
  let G:=fun p : A×S=>iteratedFDeriv ℝ r
    (fun Q=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q (p.1.1,(p.1.2,p.2))) •
      f (Q+R p.1.1+W p.1.2)) H
  have hc(σ:S):Continuous (fun z:A=>G (z,σ)):=by
    let F:=fun z:A×FiniteStateField S=>
      Real.exp (cavityOuterPosteriorLogDensity V a L s N R z.2 (z.1.1,(z.1.2,σ))) •
        f (z.2+R z.1.1+W z.1.2)
    have hF:ContDiff ℝ ∞ F:=
      ((contDiff_cavityOuterPosteriorLogDensity_joint V a ha L s N R σ).comp
        (contDiff_snd.prodMk contDiff_fst)).exp.smul
      (hf.comp ((contDiff_snd.add (R.contDiff.comp (contDiff_fst.comp contDiff_fst))).add
        (W.contDiff.comp (contDiff_snd.comp contDiff_fst))))
    change Continuous (fun z : A=>iteratedFDeriv ℝ r (fun Q=>F (z,Q)) H)
    exact continuous_outer_fixed_slice_jet F hF r H
  have hm:Measurable G:=measurable_from_prod_countable_left fun σ=>(hc σ).measurable
  have hs:TopologicalSpace.IsSeparable (⋃σ:S,range (fun z:A=>G (z,σ))):=
    .iUnion fun σ=>TopologicalSpace.isSeparable_range (hc σ)
  have hgs:StronglyMeasurable G:=stronglyMeasurable_iff_measurable_separable.mpr
    ⟨hm,hs.mono (by rintro _ ⟨⟨z,σ⟩,rfl⟩;exact mem_iUnion.mpr ⟨σ,mem_range.mpr ⟨z,rfl⟩⟩)⟩
  exact (hgs.comp_measurable (show Measurable
    (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>((p.1,p.2.1),p.2.2)) from by fun_prop)).aestronglyMeasurable

theorem cavityOuterPosteriorMean_iteratedFDeriv_integral
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    Integrable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r (fun Q=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q p) •
        f (Q+R p.1+W p.2.1)) H)
      ((stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N)) ∧
    iteratedFDeriv ℝ r (cavityOuterPosteriorMean V a L s N R f W) H=
      ∫p,iteratedFDeriv ℝ r (fun Q=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q p) •
        f (Q+R p.1+W p.2.1)) H
        ∂(stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N) :=by
  choose C hC hb using hf.2
  let A:ℝ:=1+∑i∈Finset.range (r+1),C i
  have hA:0≤A:=add_nonneg zero_le_one (Finset.sum_nonneg (fun i _=>hC i))
  have hCA(i)(hi:i≤r):C i≤A:=by
    have hh:=Finset.single_le_sum (fun l _=>hC l) (Finset.mem_range.mpr (by omega : i<r+1))
    dsimp only [A];linarith
  obtain ⟨K,hK,hLB⟩:=cavityOuterPosteriorLogDensity_bounded_positive_jets V a ha ha1 hdec L s N r R
  have hLc(p):ContDiff ℝ ∞ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p):=
    (contDiff_cavityOuterPosteriorLogDensity_joint V a ha L s N R p.2.2).comp
      (contDiff_id.prodMk (contDiff_const (c:=(p.1,p.2.1))))
  have hLip:∃M:ℝ≥0,∀p,LipschitzWith M (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p):=by
    obtain ⟨D,hD,hDB⟩:=cavityOuterPosteriorLogDensity_bounded_positive_jets V a ha ha1 hdec L s N 1 R
    refine ⟨D.toNNReal,fun p=>?_⟩
    apply lipschitzWith_of_nnnorm_fderiv_le ((hLc p).differentiable (by simp))
    intro Q
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ (zero_le_one.trans hD),←norm_iteratedFDeriv_one]
    simpa only [pow_one] using hDB 1 le_rfl le_rfl Q p
  have hVBound (i : ℕ) (hir : i≤r) (Q : FiniteStateField S)
      (p : FiniteStateGaussianInput J×((Fin N→Field n)×S)) :
      ‖iteratedFDeriv ℝ i (fun B=>f (B+R p.1+W p.2.1)) Q‖≤A*K^i:=by
    have he:(fun B=>f (B+R p.1+W p.2.1))=fun B=>f (B+(R p.1+W p.2.1)):=by funext B;rw [add_assoc]
    rw [he,iteratedFDeriv_comp_add_right]
    exact (hb i _).trans ((hCA i hir).trans (le_mul_of_one_le_right hA (one_le_pow₀ hK)))
  have hj:=exponentialObservable_integral_iteratedFDeriv r
    ((stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N))
    (cavityOuterPosteriorLogDensity V a L s N R) (fun Q p=>f (Q+R p.1+W p.2.1)) K (fun _=>A)
    (zero_le_one.trans hK) (fun _=>hA) (fun p=>(hLc p).of_le (by simp))
    (fun p=>(hf.1.comp ((contDiff_id.add contDiff_const).add contDiff_const)).of_le (by simp))
    hLip hLB hVBound
    (fun i _ Q=>aestronglyMeasurable_cavityOuterPosterior_exponentialJet V a ha L s N i R f hf.1 W Q)
    (fun Q=>(integrable_cavityOuterPosterior_exp V a ha L s N R Q).mul_const A) r le_rfl H
  have he:(fun Q=>∫p,Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q p) • f (Q+R p.1+W p.2.1)
      ∂(stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N))=
      cavityOuterPosteriorMean V a L s N R f W:=by
    funext Q
    exact (integral_cavityOuterPosteriorLaw_exp V a ha L s N R Q (fun p=>f (Q+R p.1+W p.2.1))).symm
  rw [he] at hj
  exact hj

end QuantitativeFollowup
