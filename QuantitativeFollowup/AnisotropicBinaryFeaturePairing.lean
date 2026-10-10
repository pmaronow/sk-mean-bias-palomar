module
public import QuantitativeFollowup.AnisotropicBinaryFeatureFinite

@[expose] public section

/-! True whole-past tested finite pair-spin Hessian decomposition along
the actual anisotropic diffusion, with every future square transported by
the honest Gaussian conditional transition law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open OverlapPaper (sourceKernelExpectation sourceKernelExpectation_measurable sourceKernelExpectation_abs_le)
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

theorem measurable_anisotropicFinitePairSecond (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (e : AnisotropicCouplingIndex n) : Measurable (fun P=>anisotropicFinitePairSecond D s j P e) := by
  have hd:=(((contDiff_anisotropicFinitePotential (anisotropicUnitCouplings D) s j).fderiv_right
    (m:=∞) (by simp)).fderiv_right (m:=0) (by simp)).continuous
  have h:=((hd.comp (anisotropicCouplingRescaling D).continuous).clm_apply
    (continuous_const (y:=anisotropicCouplingDirection e))).clm_apply
      (continuous_const (y:=anisotropicCouplingDirection e))
  simpa only [Function.comp_def,anisotropicFinitePairSecond] using h.measurable

def anisotropicPairSecondBound (D : AnisotropicSpinModel n) (e : AnisotropicCouplingIndex n) : ℝ :=
  ‖anisotropicEnergyMap (anisotropicUnitCouplings D)‖^2*‖anisotropicCouplingDirection e‖^2

theorem norm_anisotropicFinitePairSecond_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    ‖anisotropicFinitePairSecond D s j P e‖ ≤ anisotropicPairSecondBound D e := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicFinitePotential (anisotropicUnitCouplings D) s j))
    (anisotropicCouplingRescaling D P)
  have hT : ‖T‖ ≤ ‖anisotropicEnergyMap (anisotropicUnitCouplings D)‖^2 := by
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact norm_anisotropicFinitePotential_secondJet_le _ s j _
  have h1:=(T (anisotropicCouplingDirection e)).le_opNorm (anisotropicCouplingDirection e)
  have h2:=mul_le_mul_of_nonneg_right (T.le_opNorm (anisotropicCouplingDirection e))
    (norm_nonneg (anisotropicCouplingDirection e))
  exact (h1.trans h2).trans (by
    simpa only [anisotropicPairSecondBound,pow_two,mul_assoc] using
      mul_le_mul_of_nonneg_right hT (sq_nonneg (‖anisotropicCouplingDirection e‖)))

private theorem integrable_weighted_bounded {A : Type*} [MeasurableSpace A]
    (P : Measure A) (Z F : A→ℝ) (hZ : Integrable Z P) (hF : Measurable F)
    (B : ℝ) (hb : ∀p,‖F p‖ ≤ B) : Integrable (fun p=>Z p*F p) P := by
  exact (hZ.norm.mul_const B).mono' (hZ.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (.of_forall fun p=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))

theorem anisotropicFinite_pair_second_wholePast_pairing (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+2)
    (e : AnisotropicCouplingIndex n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p,Z p*anisotropicFinitePairSecond D s (k+2-i)
      (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal p) e ∂vectorDisorderBrownianMeasure n)+
      anisotropicSchemeMass s (k+2-i)*(∫p,Z p*(anisotropicFiniteFeatureMean D s (k+2-i)
        (anisotropicPairFeature e) (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal p))^2
          ∂vectorDisorderBrownianMeasure n)+
      (∑u∈Finset.range (k+2-i),(anisotropicSchemeMass s u-anisotropicSchemeMass s (u+1))*
        (∫p,Z p*(anisotropicFiniteFeatureMean D s (u+1) (anisotropicPairFeature e)
          (anisotropicFinitePhysicalParameter D s g (s.q (k+1-u)).toNNReal p))^2
            ∂vectorDisorderBrownianMeasure n))=∫p,Z p ∂vectorDisorderBrownianMeasure n := by
  let j:=k+2-i
  let X:=anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal
  let H:=fun p=>anisotropicFinitePairSecond D s j (X p) e
  let M:=fun d y=>(anisotropicFiniteFeatureMean D s d (anisotropicPairFeature e) y)^2
  let Q:=fun u=>sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (u+1+r)) (j-(u+1)) (M (u+1))
  let w:=fun u=>anisotropicSchemeMass s u-anisotropicSchemeMass s (u+1)
  have hXm:=measurable_anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal
  have hZm:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hMb (d : ℕ) (y : AnisotropicParameter n) : ‖M d y‖ ≤ 1 := by
    rw [norm_pow]
    have hb σ : ‖anisotropicPairFeature e σ‖ ≤ 1 := by
      change ‖Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)‖ ≤ 1
      simp only [norm_mul,Real.norm_eq_abs,Paper.abs_spinSign,mul_one,le_refl]
    exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicFiniteFeatureMean_bound D s d _ 1 hb y) 2).trans_eq (by norm_num)
  have hMm (d : ℕ) : Measurable (M d):=(measurable_anisotropicFiniteFeatureMean D s d _).pow_const 2
  have hQm (u : ℕ) : Measurable (Q u):=sourceKernelExpectation_measurable _ _ (hMm _) _
  have hQb (u : ℕ) (y : AnisotropicParameter n) : ‖Q u y‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using sourceKernelExpectation_abs_le _
      (fun r=>anisotropicDepthKernel_markov D s (u+1+r)) _ (hMm _) 1 zero_le_one
      (fun y=>by simpa only [Real.norm_eq_abs] using hMb (u+1) y) (j-(u+1)) y
  have hHi : Integrable (fun p=>Z p*H p) (vectorDisorderBrownianMeasure n):=
    integrable_weighted_bounded _ Z H hZi ((measurable_anisotropicFinitePairSecond D s j e).comp hXm)
      (anisotropicPairSecondBound D e) (fun p=>norm_anisotropicFinitePairSecond_le D s j _ e)
  have hMi : Integrable (fun p=>Z p*M j (X p)) (vectorDisorderBrownianMeasure n):=
    integrable_weighted_bounded _ Z _ hZi ((hMm j).comp hXm) 1 (fun p=>hMb j _)
  have hQi (u : ℕ) : Integrable (fun p=>Z p*(w u*Q u (X p))) (vectorDisorderBrownianMeasure n):=by
    convert (integrable_weighted_bounded _ Z _ hZi ((hQm u).comp hXm) 1
      (fun p=>hQb u _)).const_mul (w u) using 1
    funext p
    simp only [Function.comp_def]
    ring
  have hpoint (p : VectorDisorderBrownianSample n) :
      Z p*H p+anisotropicSchemeMass s j*(Z p*M j (X p))+
        (∑u∈Finset.range j,Z p*(w u*Q u (X p)))=Z p := by
    have he:=congrArg (fun x : ℝ=>Z p*x) (anisotropicFinitePairSecond_future_decomposition D s j (X p) e)
    simp only [mul_add,Finset.mul_sum] at he
    dsimp only [H,M,Q,w] at ⊢
    nlinarith only [he]
  have he := integral_congr_ae (μ:=vectorDisorderBrownianMeasure n) (.of_forall hpoint)
  have headd:=integral_add (hHi.add (hMi.const_mul (anisotropicSchemeMass s j)))
    (integrable_finsetSum (Finset.range j) (fun u _=>hQi u))
  have headd' := integral_add hHi (hMi.const_mul (anisotropicSchemeMass s j))
  simp only [Pi.add_apply] at headd headd'
  rw [headd,headd',integral_const_mul,integral_finsetSum _ (fun u _=>hQi u)] at he
  have hfuture (u : ℕ) (hu : u∈Finset.range j) :
      (∫p,Z p*(w u*Q u (X p)) ∂vectorDisorderBrownianMeasure n)=
        w u*(∫p,Z p*M (u+1) (anisotropicFinitePhysicalParameter D s g (s.q (k+1-u)).toNNReal p)
          ∂vectorDisorderBrownianMeasure n) := by
    have huj:=Finset.mem_range.mp hu
    have hcur : i ≤ k+1-u := by dsimp [j] at huj;omega
    have hku : k+2-(k+1-u)=u+1 := by dsimp [j] at huj;omega
    have hsub : k+1-u-i=j-(u+1) := by dsimp [j] at huj ⊢;omega
    have hp:=anisotropicFinite_future_integrable_weighted_pairing D s g i (k+1-u) hcur
      (by omega) (M (u+1)) (hMm _) 1 (hMb _) Z hZ hZi
    simp only [anisotropicFiniteFutureExpectation,hku,hsub] at hp
    have hscalar : (fun p : VectorDisorderBrownianSample n=>Z p*(w u*Q u (X p)))=
        fun p=>w u*(Z p*Q u (X p)) := by funext p;ring
    rw [hscalar,integral_const_mul]
    exact congrArg (fun x : ℝ=>w u*x) hp.symm
  rw [Finset.sum_congr rfl hfuture] at he
  exact he

end QuantitativeFollowup
