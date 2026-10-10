module
public import QuantitativeFollowup.AnisotropicBinaryFeatureStieltjes
public import QuantitativePaper.VectorFutureMeanSquareLimit

@[expose] public section

/-! Genuine moving-profile limits of the pair-feature Hessian and future
squares on the actual common Wiener space. The strict future preserves the
starting atom through upward grid rounding. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def anisotropicProcessPairSecond (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicTailPairSecond D μ q (anisotropicProcessParameter D μ q sample) e

def anisotropicFinitePairSquareMoment (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) (r : Paper.Overlap) : ℝ :=
  ∫p,Z p*(anisotropicFiniteTailPairResponse D s r
    (anisotropicFiniteProcessParameter D s r (g,p.2)) e)^2 ∂vectorDisorderBrownianMeasure n

def anisotropicPairSquareMoment (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) (r : Paper.Overlap) : ℝ :=
  ∫p,Z p*(anisotropicProcessPairResponse D μ r e (g,p.2))^2 ∂vectorDisorderBrownianMeasure n

theorem continuous_anisotropicFiniteTailPairSecond_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (e : AnisotropicCouplingIndex n) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n=>anisotropicFiniteTailPairSecond D s z.1 z.2 e) := by
  have h:=((continuous_anisotropicFiniteTailSecondDifferential_joint (anisotropicUnitCouplings D) s).comp
    (continuous_fst.prodMk ((anisotropicCouplingRescaling D).continuous.comp continuous_snd))).clm_apply
      (continuous_const (y:=anisotropicCouplingDirection e))
  simpa only [Function.comp_def,anisotropicFiniteTailPairSecond] using
    h.clm_apply (continuous_const (y:=anisotropicCouplingDirection e))

theorem continuous_anisotropicTailPairSecond_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : AnisotropicCouplingIndex n) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n=>anisotropicTailPairSecond D μ z.1 z.2 e) := by
  have h:=((continuous_anisotropicMeasureTailSecondDifferential_joint (anisotropicUnitCouplings D) μ).comp
    (continuous_fst.prodMk ((anisotropicCouplingRescaling D).continuous.comp continuous_snd))).clm_apply
      (continuous_const (y:=anisotropicCouplingDirection e))
  simpa only [Function.comp_def,anisotropicTailPairSecond] using
    h.clm_apply (continuous_const (y:=anisotropicCouplingDirection e))

theorem norm_anisotropicFiniteTailPairSecond_le (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    ‖anisotropicFiniteTailPairSecond D s q P e‖ ≤ anisotropicPairSecondBound D e := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential (anisotropicUnitCouplings D) s q))
    (anisotropicCouplingRescaling D P)
  have hT:=norm_anisotropicFiniteTailSecondDifferential_le (anisotropicUnitCouplings D) s q
    (anisotropicCouplingRescaling D P)
  have h1:=(T (anisotropicCouplingDirection e)).le_opNorm (anisotropicCouplingDirection e)
  have h2:=mul_le_mul_of_nonneg_right (T.le_opNorm (anisotropicCouplingDirection e))
    (norm_nonneg (anisotropicCouplingDirection e))
  exact (h1.trans h2).trans (by
    simpa only [anisotropicPairSecondBound,pow_two,mul_assoc] using
      mul_le_mul_of_nonneg_right hT (sq_nonneg (‖anisotropicCouplingDirection e‖)))

theorem tendsto_anisotropicProcessPairSecond_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n)
    (e : AnisotropicCouplingIndex n) {qj : ℕ→Paper.Overlap} {q : Paper.Overlap}
    (hq : Tendsto qj atTop (𝓝 q)) :
    Tendsto (fun j=>anisotropicFiniteTailPairSecond D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j)
      (anisotropicFiniteProcessParameter D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (qj j) sample) e) atTop (𝓝 (anisotropicProcessPairSecond D μ q e sample)) := by
  have hP:=(anisotropicCouplingRescaling D).continuous.continuousAt.tendsto.comp
    (tendsto_anisotropicFiniteProcessParameter_moving_time D μ sample hq)
  have hT:=(tendstoUniformly_anisotropicDyadicTailSecondDifferential (anisotropicUnitCouplings D) μ).tendsto_comp
    (continuous_anisotropicMeasureTailSecondDifferential_joint (anisotropicUnitCouplings D) μ).continuousAt
    (hq.prodMk_nhds hP)
  have hev : Continuous (fun T : AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ)=>
      T (anisotropicCouplingDirection e) (anisotropicCouplingDirection e)) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  simpa only [Function.comp_def,anisotropicFiniteTailPairSecond,anisotropicProcessPairSecond,
    anisotropicTailPairSecond,anisotropicDyadicTailPotential,anisotropicFiniteTailPotential] using
      hev.continuousAt.tendsto.comp hT

theorem measurable_uncurry_anisotropicFiniteProcessPairResponse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (e : AnisotropicCouplingIndex n) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicFiniteTailPairResponse D s z.1 (anisotropicFiniteProcessParameter D s z.1 z.2) e) := by
  have hD:=(continuous_anisotropicFiniteTailDifferential_joint (anisotropicUnitCouplings D) s).measurable.comp
    (measurable_fst.prodMk ((anisotropicCouplingRescaling D).continuous.measurable.comp
      (measurable_uncurry_anisotropicFiniteProcessParameter D s)))
  have h:=(continuous_id.clm_apply (continuous_const (y:=anisotropicCouplingDirection e))).measurable.comp hD
  simpa only [Function.comp_def,anisotropicFiniteTailPairResponse,id_eq] using h

theorem measurable_anisotropicFinitePairSquareMoment (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z) :
    Measurable (anisotropicFinitePairSquareMoment D s g e Z) := by
  have hmap : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      (z.1,(g,z.2.2))) :=
    measurable_fst.prodMk ((measurable_const (a:=g)).prodMk measurable_snd.snd)
  have hm := (measurable_uncurry_anisotropicFiniteProcessPairResponse D s e).comp hmap
  have hout:=(((hZ.comp measurable_snd).mul (hm.pow_const 2)).stronglyMeasurable.integral_prod_right'
    (ν:=vectorDisorderBrownianMeasure n)).measurable
  unfold anisotropicFinitePairSquareMoment
  simpa only [Function.comp_def,Pi.mul_def] using hout

theorem norm_anisotropicFinitePairSquareMoment_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Integrable Z (vectorDisorderBrownianMeasure n))
    (r : Paper.Overlap) : ‖anisotropicFinitePairSquareMoment D s g e Z r‖ ≤
      ∫p,‖Z p‖ ∂vectorDisorderBrownianMeasure n := by
  unfold anisotropicFinitePairSquareMoment
  apply norm_integral_le_of_norm_le hZ.norm
  exact .of_forall fun p=>by
    rw [norm_mul,norm_pow]
    have hb:=(pow_le_pow_left₀ (norm_nonneg _)
      (anisotropicFiniteTailPairResponse_bound D s r
        (anisotropicFiniteProcessParameter D s r (g,p.2)) e) 2)
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg (Z p))).trans_eq (by simp)

theorem tendsto_anisotropicPairSquareMoment_grid (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) (r : Paper.Overlap) :
    Tendsto (fun j=>anisotropicFinitePairSquareMoment D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g e Z
      (Paper.parisiGridRound (vectorDyadicIndex j) r)) atTop
      (𝓝 (anisotropicPairSquareMoment D μ g e Z r)) := by
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let rj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) r
  have hr:= (Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex
  unfold anisotropicFinitePairSquareMoment anisotropicPairSquareMoment
  apply tendsto_integral_of_dominated_convergence (fun p=>‖Z p‖)
  · intro j
    have hmap : Measurable (fun p : VectorDisorderBrownianSample n=>(rj j,(g,p.2))) :=
      (measurable_const (a:=rj j)).prodMk ((measurable_const (a:=g)).prodMk measurable_snd)
    have hm := (measurable_uncurry_anisotropicFiniteProcessPairResponse D (sj j) e).comp hmap
    simpa only [Function.comp_def,Pi.mul_def,sj,rj] using (hZ.mul (hm.pow_const 2)).aestronglyMeasurable
  · exact hZi.norm
  · intro j
    exact .of_forall fun p=>by
      rw [norm_mul,norm_pow]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (anisotropicFiniteTailPairResponse_bound D (sj j) (rj j) _ e) 2)
          (norm_nonneg (Z p))).trans_eq (by simp)
  · exact .of_forall fun p=>(tendsto_const_nhds (x:=Z p)).mul
      ((tendsto_anisotropicProcessPairResponse_moving D μ (g,p.2) e hr).pow 2)

def anisotropicGridFuturePairSquare (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) (j : ℕ) : ℝ :=
  ∫r : Paper.Overlap,if Paper.parisiGridRound (vectorDyadicIndex j) q <
      Paper.parisiGridRound (vectorDyadicIndex j) r then
    anisotropicFinitePairSquareMoment D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      g e Z (Paper.parisiGridRound (vectorDyadicIndex j) r) else 0 ∂(μ:Measure Paper.Overlap)

def anisotropicFuturePairSquareMoment (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (Z : VectorDisorderBrownianSample n→ℝ) : ℝ :=
  ∫r : Paper.Overlap,if q < r then anisotropicPairSquareMoment D μ g e Z r else 0
    ∂(μ:Measure Paper.Overlap)

theorem tendsto_anisotropicGridFuturePairSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (e : AnisotropicCouplingIndex n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable Z) (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    Tendsto (anisotropicGridFuturePairSquare D μ g q e Z) atTop
      (𝓝 (anisotropicFuturePairSquareMoment D μ g q e Z)) := by
  unfold anisotropicGridFuturePairSquare anisotropicFuturePairSquareMoment
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : Paper.Overlap=>∫p,‖Z p‖ ∂vectorDisorderBrownianMeasure n)
  · exact .of_forall fun j=>(Measurable.ite
      (measurableSet_lt measurable_const (Paper.measurable_parisiGridRound _))
      ((measurable_anisotropicFinitePairSquareMoment D _ g e Z hZ).comp
        (Paper.measurable_parisiGridRound _)) measurable_const).aestronglyMeasurable
  · exact .of_forall fun j=>.of_forall fun r=>by
      split_ifs
      · exact norm_anisotropicFinitePairSquareMoment_le D _ g e Z hZi _
      · simpa only [norm_zero] using integral_nonneg (fun p=>norm_nonneg (Z p))
  · exact integrable_const _
  · exact .of_forall fun r=>by
      by_cases hqr:q < r
      · rw [ite_eq_left hqr]
        have hq:=continuous_subtype_val.tendsto q |>.comp
          ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)
        have hr:=continuous_subtype_val.tendsto r |>.comp
          ((Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex)
        have hg : (0:ℝ) < (r:ℝ)-q := sub_pos.mpr hqr
        have he : ∀ᶠj in atTop,Paper.parisiGridRound (vectorDyadicIndex j) q <
            Paper.parisiGridRound (vectorDyadicIndex j) r :=
          ((hr.sub hq).eventually (eventually_gt_nhds hg)).mono fun j hj=>
            (show (Paper.parisiGridRound (vectorDyadicIndex j) q:ℝ) <
              (Paper.parisiGridRound (vectorDyadicIndex j) r:ℝ) from sub_pos.mp hj)
        apply (tendsto_anisotropicPairSquareMoment_grid D μ g e Z hZ hZi r).congr'
        filter_upwards [he] with j hj
        simp only [ite_eq_left hj]
      · have he (j : ℕ) : ¬Paper.parisiGridRound (vectorDyadicIndex j) q <
            Paper.parisiGridRound (vectorDyadicIndex j) r :=
          not_lt_of_ge (monotone_vectorProfileRound _ (not_lt.mp hqr))
        simp only [ite_eq_right hqr,ite_eq_right (he _)]
        exact tendsto_const_nhds

end QuantitativeFollowup
