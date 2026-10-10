module
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.PiNat

@[expose] public section

/-! The covariance of an actual square-integrable Hilbert-valued random
variable has finite positive trace.  The trace is computed by integrating
Parseval's identity, rather than postulated as an operator hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology BigOperators
namespace FourPapersCommon
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
variable {ι : Type*}

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
theorem countable_orthonormal_index [SeparableSpace H] (v : ι → H)
    (hv : Orthonormal ℝ v) : Countable ι := by
  classical
  have hex (i : ι) : ∃j : ℕ, dist (v i) (denseSeq H j) < (1/2:ℝ) := by
    exact (denseRange_denseSeq H).exists_dist_lt (v i) (by norm_num)
  choose c hc using hex
  apply Function.Injective.countable (f:=c)
  intro i j hij
  by_contra hne
  have hd : dist (v i) (v j) < (1:ℝ) := by
    have ht := dist_triangle (v i) (denseSeq H (c i)) (v j)
    have hj := hc j
    rw [←hij] at hj
    rw [dist_comm (v j)] at hj
    linarith [hc i]
  have hs : dist (v i) (v j)^2=2 := by
    rw [dist_eq_norm,norm_sub_sq_real,hv.norm_eq_one i,hv.norm_eq_one j,
      hv.inner_eq_zero hne]
    norm_num
  have h0 : 0 ≤ dist (v i) (v j):=dist_nonneg
  nlinarith

theorem covarianceOperator_diagonal_nonneg (P : Measure H) (x : H) :
    0 ≤ inner ℝ (covarianceOperator P x) x :=
  (isPositive_covarianceOperator (μ:=P)).2 x

theorem covarianceOperator_hasSum_diagonal [Countable ι] (P : Measure H)
    (hP : MemLp id 2 P) (b : HilbertBasis ι ℝ H) :
    HasSum (fun i=>inner ℝ (covarianceOperator P (b i)) (b i))
      (∫x,‖x‖^2 ∂P) := by
  let F : ι → H → ℝ:=fun i x=>inner ℝ x (b i)*inner ℝ (b i) x
  have hmeas (i : ι) : AEStronglyMeasurable (F i) P := by
    exact hP.aestronglyMeasurable.inner_const.mul
      hP.aestronglyMeasurable.const_inner
  have hn (i : ι) (x : H) : 0 ≤ F i x := by
    dsimp [F]
    rw [real_inner_comm (b i) x]
    exact mul_self_nonneg _
  have hint : Integrable (fun x : H=>‖x‖^2) P:=
    hP.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hsum (x : H) : HasSum (fun i=>F i x) (‖x‖^2) := by
    simpa only [real_inner_self_eq_norm_sq] using b.hasSum_inner_mul_inner x x
  have ht := hasSum_integral_of_dominated_convergence F hmeas
    (fun i=>.of_forall fun x=>by rw [Real.norm_eq_abs,abs_of_nonneg (hn i x)])
    (.of_forall fun x=>(hsum x).summable)
    (hint.congr (.of_forall fun x=>(hsum x).tsum_eq.symm))
    (.of_forall hsum)
  convert ht using 1
  ext i
  rw [covarianceOperator_inner hP]
  apply integral_congr_ae
  exact .of_forall fun x=>by dsimp [F];rw [real_inner_comm x (b i)]

theorem covarianceOperator_trace_eq [Countable ι] (P : Measure H)
    (hP : MemLp id 2 P) (b : HilbertBasis ι ℝ H) :
    (∑'i,inner ℝ (covarianceOperator P (b i)) (b i))=∫x,‖x‖^2 ∂P :=
  (covarianceOperator_hasSum_diagonal P hP b).tsum_eq

/-- Basis-independent finite positive trace, expressed by the actual
diagonal series for every Hilbert basis. -/
def HasFinitePositiveTrace (A : H→L[ℝ]H) (t : ℝ) : Prop:=
  A.toLinearMap.IsPositive ∧
    ∀ (ι : Type*) [Countable ι] (b : HilbertBasis ι ℝ H),
      HasSum (fun i=>inner ℝ (A (b i)) (b i)) t

theorem covarianceOperator_hasFinitePositiveTrace (P : Measure H)
    (hP : MemLp id 2 P) :
    HasFinitePositiveTrace (covarianceOperator P) (∫x,‖x‖^2 ∂P) := by
  refine ⟨isPositive_covarianceOperator,?_⟩
  intro ι hι b
  exact covarianceOperator_hasSum_diagonal P hP b

/-- The standard finite-diagonal criterion for a positive trace-class
operator on a separable real Hilbert space. -/
def IsPositiveTraceClass (A : H→L[ℝ]H) : Prop:=
  A.toLinearMap.IsPositive ∧
    ∃ (w : Set H) (_ : Countable w) (b : HilbertBasis w ℝ H),
      Summable (fun i=>‖inner ℝ (A (b i)) (b i)‖)

theorem covarianceOperator_isPositiveTraceClass [SeparableSpace H]
    (P : Measure H) (hP : MemLp id 2 P) :
    IsPositiveTraceClass (covarianceOperator P) := by
  obtain ⟨w,b,_⟩:=exists_hilbertBasis (𝕜:=ℝ) (E:=H)
  have hw : Countable w:=countable_orthonormal_index b b.orthonormal
  refine ⟨isPositive_covarianceOperator,w,hw,b,?_⟩
  exact (covarianceOperator_hasSum_diagonal P hP b).summable.congr
    (fun i=>by rw [Real.norm_eq_abs,abs_of_nonneg (covarianceOperator_diagonal_nonneg P (b i))])

theorem covarianceOperator_hasSum_pairing [Countable ι] (P : Measure H)
    (hP : MemLp id 2 P) (b : HilbertBasis ι ℝ H) (J : H→L[ℝ]H) :
    HasSum (fun i=>inner ℝ (covarianceOperator P (b i)) (J (b i)))
      (∫x,inner ℝ x (J x) ∂P) := by
  let F : ι→H→ℝ:=fun i x=>inner ℝ x (b i)*inner ℝ x (J (b i))
  let G : ι→H→ℝ:=fun i x=>inner ℝ x (b i)*inner ℝ (b i) (J.adjoint x)
  let B : ι→H→ℝ:=fun i x=>
    ((inner ℝ x (b i)*inner ℝ (b i) x)+
      (inner ℝ (J.adjoint x) (b i)*inner ℝ (b i) (J.adjoint x)))/2
  have hFG (i : ι) (x : H) : F i x=G i x := by
    dsimp [F,G]
    rw [←ContinuousLinearMap.adjoint_inner_left,real_inner_comm (J.adjoint x) (b i)]
  have hmeas (i : ι) : AEStronglyMeasurable (F i) P:=
    hP.aestronglyMeasurable.inner_const.mul hP.aestronglyMeasurable.inner_const
  have hbound (i : ι) (x : H) : ‖F i x‖≤B i x := by
    rw [hFG]
    dsimp [G,B]
    simp only [real_inner_comm x (b i),real_inner_comm (b i) (J.adjoint x)]
    apply abs_le.mpr
    constructor <;> nlinarith
      [sq_nonneg (inner ℝ x (b i)-inner ℝ (b i) (J.adjoint x)),
       sq_nonneg (inner ℝ x (b i)+inner ℝ (b i) (J.adjoint x))]
  have hbs (x : H) : HasSum (fun i=>B i x)
      ((‖x‖^2+‖J.adjoint x‖^2)/2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      ((b.hasSum_inner_mul_inner x x).add
        (b.hasSum_inner_mul_inner (J.adjoint x) (J.adjoint x))).div_const 2
  have hi := (hP.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).add
    ((hP.continuousLinearMap_comp J.adjoint).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
  have hs (x : H) : HasSum (fun i=>F i x) (inner ℝ x (J.adjoint x)) := by
    convert b.hasSum_inner_mul_inner x (J.adjoint x) using 1
    ext i
    exact hFG i x
  have ht := hasSum_integral_of_dominated_convergence B hmeas
    (fun i=>.of_forall (hbound i)) (.of_forall fun x=>(hbs x).summable)
    ((hi.div_const 2).congr (.of_forall fun x=>(hbs x).tsum_eq.symm))
    (.of_forall hs)
  convert ht using 1
  · ext i
    rw [covarianceOperator_inner hP]
    apply integral_congr_ae
    exact .of_forall fun x=>by
      dsimp [F]
      rw [real_inner_comm x (b i),real_inner_comm x (J (b i))]
  · apply integral_congr_ae
    exact .of_forall fun x=>by
      dsimp only
      conv_rhs => rw [real_inner_comm]
      rw [ContinuousLinearMap.adjoint_inner_left]

theorem covarianceOperator_trace_pairing [Countable ι] (P : Measure H)
    (hP : MemLp id 2 P) (b : HilbertBasis ι ℝ H) (J : H→L[ℝ]H) :
    (∑'i,inner ℝ (covarianceOperator P (b i)) (J (b i)))=
      ∫x,inner ℝ x (J x) ∂P :=
  (covarianceOperator_hasSum_pairing P hP b J).tsum_eq

theorem covarianceOperator_hasSum_comp_diagonal [Countable ι] (P : Measure H)
    (hP : MemLp id 2 P) (b : HilbertBasis ι ℝ H) (J : H→L[ℝ]H) :
    HasSum (fun i=>inner ℝ (J (covarianceOperator P (b i))) (b i))
      (∫x,inner ℝ x (J x) ∂P) := by
  have ht := covarianceOperator_hasSum_pairing P hP b J.adjoint
  convert ht using 1
  · ext i
    rw [ContinuousLinearMap.adjoint_inner_right]
  · apply integral_congr_ae
    exact .of_forall fun x=>by
      dsimp only
      rw [ContinuousLinearMap.adjoint_inner_right,real_inner_comm]

end FourPapersCommon
