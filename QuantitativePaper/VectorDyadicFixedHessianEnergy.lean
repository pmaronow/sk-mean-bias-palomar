module
public import QuantitativePaper.VectorDyadicJetConvergence
public import QuantitativePaper.VectorGradientComponentCalculus
public import QuantitativeFollowup.CanonicalJetBounds

@[expose] public section

/-! The finite dyadic Hessian energy on the fixed actual arbitrary-profile
diffusion converges uniformly in time and sample. The finite Hessian is the
literal spatial derivative, with a dimension-only bound. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem norm_hessianOperator_sub_eq_secondJet (f g : Field n→ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Field n) :
    ‖hessianOperator f x-hessianOperator g x‖=
      ‖iteratedFDeriv ℝ 2 f x-iteratedFDeriv ℝ 2 g x‖ := by
  have hsdf : ContDiff ℝ ∞ (fderiv ℝ f):=hf.fderiv_right (by simp)
  have hsdg : ContDiff ℝ ∞ (fderiv ℝ g):=hg.fderiv_right (by simp)
  have hdf : Differentiable ℝ (fderiv ℝ f):=hsdf.differentiable (by simp)
  have hdg : Differentiable ℝ (fderiv ℝ g):=hsdg.differentiable (by simp)
  have hsub : hessianOperator (fun y=>f y-g y) x=hessianOperator f x-hessianOperator g x := by
    have he : fderiv ℝ (fun y=>f y-g y)=fun y=>fderiv ℝ f y-fderiv ℝ g y:=
      funext fun y=>fderiv_sub (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)
    unfold hessianOperator
    rw [he]
    change _ ∘L fderiv ℝ (fderiv ℝ f-fderiv ℝ g) x=_
    rw [fderiv_sub (hdf x) (hdg x),ContinuousLinearMap.comp_sub]
  rw [←hsub]
  have hn:=norm_iteratedFDeriv_hessianOperator (fun y=>f y-g y)
    ((hf.sub hg).of_le (by simp)) 0 (by omega) x
  rw [norm_iteratedFDeriv_zero] at hn
  rw [hn]
  change ‖iteratedFDeriv ℝ 2 (f-g) x‖=_
  rw [iteratedFDeriv_sub (i:=2) (hf.of_le (by simp)) (hg.of_le (by simp))]
  rfl

def vectorFiniteTailHessian (s : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) : Field n→L[ℝ]Field n :=
  hessianOperator (vectorTailRecursion s β t q p (k+2)) x

theorem contDiff_vectorTailRecursion_field (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) :
    ContDiff ℝ ∞ (vectorTailRecursion s β t q p (k+2)) := by
  rw [vectorTailRecursion_eq_clamped s β t q q.property p le_rfl]
  exact contDiff_vectorRecursion_field _ β t p _

theorem norm_vectorFiniteTailHessian_le (s : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) : ‖vectorFiniteTailHessian s β t q p x‖≤(n : ℝ) := by
  have hd:=hasFDerivAt_gradient_hessianOperator (vectorTailRecursion s β t q p (k+2))
    ((contDiff_vectorTailRecursion_field s β t q p).of_le (by simp)) x
  change HasFDerivAt (vectorFiniteTailGradient s β t q p) (vectorFiniteTailHessian s β t q p x) x at hd
  rw [←hd.fderiv]
  simpa only [NNReal.coe_natCast] using norm_fderiv_le_of_lipschitz ℝ (x₀:=x)
    (vectorFiniteTailGradient_lipschitz s β t q p)

theorem abs_vectorHessianHilbertSquare_sub_le (H K : Field n→L[ℝ]Field n)
    (hH : ‖H‖≤(n : ℝ)) (hK : ‖K‖≤(n : ℝ)) :
    |vectorHessianHilbertSquare H-vectorHessianHilbertSquare K|≤2*(n : ℝ)^2*‖H-K‖ := by
  have hb (A : Field n→L[ℝ]Field n) (hA : ‖A‖≤(n : ℝ)) (j : Fin n) :
      ‖A (EuclideanSpace.single j 1)‖≤(n : ℝ):=by
    simpa only [PiLp.norm_single,norm_one,mul_one] using
      (A.le_opNorm (EuclideanSpace.single j 1)).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg (EuclideanSpace.single j 1)))
  have hd (j : Fin n) : |‖H (EuclideanSpace.single j 1)‖-‖K (EuclideanSpace.single j 1)‖|≤‖H-K‖:=by
    exact (abs_norm_sub_norm_le _ _).trans (by
      simpa only [ContinuousLinearMap.sub_apply,PiLp.norm_single,norm_one,mul_one] using
        (H-K).le_opNorm (EuclideanSpace.single j 1))
  unfold vectorHessianHilbertSquare
  rw [←Finset.sum_sub_distrib]
  calc
    _≤∑j : Fin n,|‖H (EuclideanSpace.single j 1)‖^2-‖K (EuclideanSpace.single j 1)‖^2|:=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑_j : Fin n,2*(n : ℝ)*‖H-K‖:=by
      apply Finset.sum_le_sum
      intro j _
      rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc
        _≤(2*(n : ℝ))*‖H-K‖:=mul_le_mul (by linarith [hb H hH j,hb K hK j]) (hd j)
          (abs_nonneg _) (by positivity)
        _=_:=by ring
    _=_:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

def vectorDyadicFixedHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorHessianHilbertSquare (vectorFiniteTailHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    β t q sample.1 (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))

theorem vectorDyadicFixedHessianEnergy_nonneg_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) :
    0≤vectorDyadicFixedHessianEnergy μ β t ht q j sample ∧
      vectorDyadicFixedHessianEnergy μ β t ht q j sample≤(n : ℝ)^3 :=
  ⟨vectorHessianHilbertSquare_nonneg _,vectorHessianHilbertSquare_le
    (norm_vectorFiniteTailHessian_le _ β t q sample.1 _)⟩

theorem tendstoUniformly_vectorDyadicFixedHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) :
    TendstoUniformly (fun j (z : Paper.Overlap×VectorDisorderBrownianSample n)=>
      vectorDyadicFixedHessianEnergy μ β t ht z.1 j z.2)
      (fun z=>vectorMeasureHessianEnergy μ β t ht z.1 z.2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let δ:ℝ:=ε/(2*(n : ℝ)^2+1)
  have hδ:0<δ:=by dsimp [δ];positivity
  have hu:=(Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_vectorDyadicTailPotential_jets (n:=n) μ β t ht 2)) δ hδ
  filter_upwards [hu] with j hj
  intro z
  let q:=z.1
  let sample:=z.2
  let X:=vectorMeasureState μ β t ht (q : ℝ).toNNReal sample
  have hclose:=hj (q,(sample.1,X))
  rw [dist_eq_norm] at hclose ⊢
  have hnorm : ‖vectorFiniteTailHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q sample.1 X-
      vectorMeasureHessian μ β t q sample.1 X‖<δ:=by
    change ‖hessianOperator (vectorDyadicTailPotential μ β t q j sample.1) X-
      hessianOperator (vectorMeasureTailPotential μ β t q sample.1) X‖<δ
    rw [norm_hessianOperator_sub_eq_secondJet _ _
      (contDiff_vectorDyadicTailPotential μ β t q j sample.1)
      (contDiff_vectorMeasureTailPotential μ β t ht q sample.1) X]
    simpa only [norm_sub_rev] using hclose
  have he:=abs_vectorHessianHilbertSquare_sub_le
    (vectorFiniteTailHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q sample.1 X)
    (vectorMeasureHessian μ β t q sample.1 X)
    (norm_vectorFiniteTailHessian_le _ β t q sample.1 X) (norm_vectorMeasureHessian_le μ β t ht q sample.1 X)
  change ‖vectorMeasureHessianEnergy μ β t ht q sample-vectorDyadicFixedHessianEnergy μ β t ht q j sample‖<ε
  rw [norm_sub_rev]
  change ‖vectorDyadicFixedHessianEnergy μ β t ht q j sample-vectorMeasureHessianEnergy μ β t ht q sample‖<ε
  rw [Real.norm_eq_abs]
  apply he.trans_lt
  have hnn:0≤2*(n : ℝ)^2:=by positivity
  have hδb:2*(n : ℝ)^2*δ<ε:=by
    dsimp [δ]
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0<2*(n : ℝ)^2+1)).mpr
    nlinarith
  calc
    _≤2*(n : ℝ)^2*δ:=mul_le_mul_of_nonneg_left hnorm.le hnn
    _<ε:=hδb

end QuantitativePaper
