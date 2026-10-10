module
public import Paper.RSFunctional
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Endpoint-fixed Lipschitz tests are genuinely dense in the closed L2
space of functions vanishing at endpoint atoms. -/
noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology ENNReal NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def overlapEndpointSet : Set Paper.Overlap:={q|(q:ℝ)=0 ∨ (q:ℝ)=1}

theorem measurableSet_overlapEndpointSet : MeasurableSet overlapEndpointSet:=
  (measurable_subtype_coe (measurableSet_singleton 0)).union
    (measurable_subtype_coe (measurableSet_singleton 1))

def overlapEndpointRestriction (ν : Measure Paper.Overlap) :
    Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 (ν.restrict overlapEndpointSet):=
  Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_le_self (μ:=ν) (s:=overlapEndpointSet))

def endpointFixedL2 (ν : Measure Paper.Overlap) : Submodule ℝ (Lp ℝ 2 ν):=
  (overlapEndpointRestriction ν).ker

theorem mem_endpointFixedL2_iff (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) :
    f∈endpointFixedL2 ν ↔ ∀ᵐ q : Paper.Overlap ∂ν,((q:ℝ)=0 ∨ (q:ℝ)=1)→f q=0 := by
  have hc : overlapEndpointRestriction ν f=ᵐ[ν.restrict overlapEndpointSet] f:=
    Lp.coeFn_LpToLpOfMeasureLeSMul (E:=ℝ) (p:=2) (μ:=ν.restrict overlapEndpointSet)
    (ν:=ν) (c:=1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_le_self (μ:=ν) (s:=overlapEndpointSet)) f
  change overlapEndpointRestriction ν f=0 ↔ _
  change _ ↔ ∀ᵐ q : Paper.Overlap ∂ν,q∈overlapEndpointSet→f q=0
  rw [←ae_restrict_iff' measurableSet_overlapEndpointSet]
  constructor
  · intro h
    rw [h] at hc
    exact hc.symm.trans (Lp.coeFn_zero ℝ 2 (ν.restrict overlapEndpointSet))
  · intro h
    apply Lp.ext
    filter_upwards [hc,h,Lp.coeFn_zero ℝ 2 (ν.restrict overlapEndpointSet)] with q hq hf hz
    exact hq.trans (hf.trans hz.symm)

theorem isClosed_endpointFixedL2 (ν : Measure Paper.Overlap) :
    IsClosed (endpointFixedL2 ν : Set (Lp ℝ 2 ν)) :=
  (overlapEndpointRestriction ν).isClosed_ker

instance instIsClosedEndpointFixedL2 (ν : Measure Paper.Overlap) :
    IsClosed (endpointFixedL2 ν : Set (Lp ℝ 2 ν)):=isClosed_endpointFixedL2 ν

def endpointCutoffPolynomial (j : ℕ) : ℝ[X]:=
  1-(1-X*(1-X))^(j+1)

def endpointCutoff (j : ℕ) : C(Paper.Overlap,ℝ):=
  (endpointCutoffPolynomial j).toContinuousMapOn (Icc (0:ℝ) 1)

theorem endpointCutoff_apply (j : ℕ) (q : Paper.Overlap) :
    endpointCutoff j q=1-(1-(q:ℝ)*(1-(q:ℝ)))^(j+1):=by
  simp [endpointCutoff,endpointCutoffPolynomial]

theorem endpointCutoff_bounds (j : ℕ) (q : Paper.Overlap) :
    0≤endpointCutoff j q ∧ endpointCutoff j q≤1 := by
  rw [endpointCutoff_apply]
  have hw : 0≤(q:ℝ)*(1-(q:ℝ)):=mul_nonneg q.property.1 (sub_nonneg.mpr q.property.2)
  have hw1 : (q:ℝ)*(1-(q:ℝ))≤1:=by nlinarith [sq_nonneg ((q:ℝ)-1/2)]
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith))
  · linarith [pow_nonneg (by linarith : 0≤1-(q:ℝ)*(1-(q:ℝ))) (j+1)]

theorem endpointCutoff_endpoints (j : ℕ) :
    endpointCutoff j ⟨0,by constructor <;>norm_num⟩=0 ∧
      endpointCutoff j ⟨1,by constructor <;>norm_num⟩=0 := by
  simp [endpointCutoff_apply]

theorem endpointCutoff_tendsto_interior (q : Paper.Overlap) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    Tendsto (fun j=>endpointCutoff j q) atTop (𝓝 1) := by
  have hw : 0<(q:ℝ)*(1-(q:ℝ)):=mul_pos hq0 (sub_pos.mpr hq1)
  have hw1 : (q:ℝ)*(1-(q:ℝ))≤1:=by nlinarith [sq_nonneg ((q:ℝ)-1/2)]
  have hh:=tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0≤1-(q:ℝ)*(1-(q:ℝ)))
    (by linarith : 1-(q:ℝ)*(1-(q:ℝ))<1)
  simpa only [endpointCutoff_apply,pow_succ,zero_mul,sub_zero] using
    tendsto_const_nhds.sub (hh.mul_const (1-(q:ℝ)*(1-(q:ℝ))))

theorem polynomial_overlap_lipschitz (P : ℝ[X]) :
    ∃K : ℝ≥0,LipschitzWith K (P.toContinuousMapOn (Icc (0:ℝ) 1)) := by
  let K:=‖P.derivative.toContinuousMapOn (Icc (0:ℝ) 1)‖₊
  have hh : LipschitzOnWith K (fun x : ℝ=>P.eval x) (Icc (0:ℝ) 1):=by
    apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _=>P.differentiableAt)
    intro x hx
    rw [P.deriv]
    exact_mod_cast (P.derivative.toContinuousMapOn (Icc (0:ℝ) 1)).norm_coe_le_norm ⟨x,hx⟩
  refine ⟨K,LipschitzWith.of_dist_le_mul fun x y=>?_⟩
  exact hh.dist_le_mul x x.property y y.property

variable (ν : Measure Paper.Overlap)

theorem memLp_endpointCutoff_mul (j : ℕ) (f : Lp ℝ 2 ν) :
    MemLp (fun q=>endpointCutoff j q*f q) 2 ν := by
  apply (Lp.memLp f).of_le_mul (c:=1) ((endpointCutoff j).continuous.measurable.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable f))
  exact .of_forall fun q=>by
    change ‖endpointCutoff j q*f q‖≤1*‖f q‖
    rw [norm_mul,Real.norm_of_nonneg (endpointCutoff_bounds j q).1]
    exact mul_le_mul_of_nonneg_right (endpointCutoff_bounds j q).2 (norm_nonneg _)

def endpointCutoffLp (j : ℕ) (f : Lp ℝ 2 ν) : Lp ℝ 2 ν:=
  (memLp_endpointCutoff_mul ν j f).toLp (fun q=>endpointCutoff j q*f q)

theorem endpointCutoffLp_coeFn (j : ℕ) (f : Lp ℝ 2 ν) :
    endpointCutoffLp ν j f=ᵐ[ν]fun q=>endpointCutoff j q*f q:=
  (memLp_endpointCutoff_mul ν j f).coeFn_toLp

theorem endpointCutoffLp_contraction (j : ℕ) (f g : Lp ℝ 2 ν) :
    ‖endpointCutoffLp ν j f-endpointCutoffLp ν j g‖≤‖f-g‖ := by
  apply (show ‖endpointCutoffLp ν j f-endpointCutoffLp ν j g‖≤1*‖f-g‖ from
    Lp.norm_le_mul_norm_of_ae_le_mul ?_).trans_eq (one_mul _)
  filter_upwards [Lp.coeFn_sub (endpointCutoffLp ν j f) (endpointCutoffLp ν j g),
    endpointCutoffLp_coeFn ν j f,endpointCutoffLp_coeFn ν j g,Lp.coeFn_sub f g] with q hsub hf hg hfg
  simp only [hsub,hf,hg,hfg,Pi.sub_apply]
  rw [←mul_sub,norm_mul,Real.norm_of_nonneg (endpointCutoff_bounds j q).1]
  exact mul_le_mul_of_nonneg_right (endpointCutoff_bounds j q).2 (norm_nonneg _)

private theorem integral_sq_coe_Lp (f : Lp ℝ 2 ν) :
    (∫q,(f q)^2∂ν)=‖f‖^2 := by
  calc
    _=∫q,inner ℝ (f q) (f q)∂ν:=by
      apply integral_congr_ae
      exact .of_forall fun q=>by simp
    _=inner ℝ f f:=rfl
    _=‖f‖^2:=real_inner_self_eq_norm_sq f

theorem endpointCutoffLp_tendsto (f : Lp ℝ 2 ν) (hf : f∈endpointFixedL2 ν) :
    Tendsto (fun j=>endpointCutoffLp ν j f) atTop (𝓝 f) := by
  let F : ℕ→Paper.Overlap→ℝ:=fun j q=>(endpointCutoff j q*f q-f q)^2
  have hpoint : ∀ᵐq∂ν,Tendsto (fun j=>endpointCutoff j q*f q) atTop (𝓝 (f q)) := by
    filter_upwards [(mem_endpointFixedL2_iff ν f).mp hf] with q hq
    by_cases he : (q:ℝ)=0 ∨ (q:ℝ)=1
    · rw [hq he]
      simp only [mul_zero]
      exact tendsto_const_nhds
    · have h0 : 0<(q:ℝ):=lt_of_le_of_ne q.property.1 (fun hh=>he (Or.inl hh.symm))
      have h1 : (q:ℝ)<1:=lt_of_le_of_ne q.property.2 (fun hh=>he (Or.inr hh))
      simpa only [one_mul] using (endpointCutoff_tendsto_interior q h0 h1).mul_const (f q)
  have hlim : ∀ᵐq∂ν,Tendsto (fun j=>F j q) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hpoint] with q hq
    simpa only [F,sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using
      (hq.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ=>f q) atTop (𝓝 (f q)))).pow 2
  have hm (j : ℕ) : AEStronglyMeasurable (F j) ν:=
    (((endpointCutoff j).continuous.measurable.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)).sub (Lp.aestronglyMeasurable f)).pow 2
  have hb (j : ℕ) : ∀ᵐq∂ν,‖F j q‖≤(f q)^2 := .of_forall fun q=>by
    have hτ:=endpointCutoff_bounds j q
    have hh : |endpointCutoff j q-1|≤1:=abs_le.mpr ⟨by linarith,by linarith⟩
    have he : ‖endpointCutoff j q*f q-f q‖≤‖f q‖:=by
      rw [show endpointCutoff j q*f q-f q=(endpointCutoff j q-1)*f q by ring,norm_mul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
    dsimp only [F]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) he 2
  have hi:=tendsto_integral_of_dominated_convergence (fun q=>(f q)^2) hm
    (Lp.memLp f).integrable_sq hb hlim
  have he (j : ℕ) : (∫q,F j q∂ν)=‖endpointCutoffLp ν j f-f‖^2:=by
    rw [←integral_sq_coe_Lp]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (endpointCutoffLp ν j f) f,endpointCutoffLp_coeFn ν j f] with q hq hτ
    simp only [hq,hτ,Pi.sub_apply,F]
  simp_rw [he] at hi
  simp only [integral_zero] at hi
  have hn:=hi.sqrt
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,dist_eq_norm] using hn

theorem polynomial_toLp_denseRange [IsFiniteMeasure ν] :
    DenseRange (fun P : ℝ[X]=>ContinuousMap.toLp 2 ν ℝ (P.toContinuousMapOn (Icc (0:ℝ) 1))) := by
  have hp : DenseRange (fun P : ℝ[X]=>P.toContinuousMapOn (Icc (0:ℝ) 1)):=by
    have he : closure (polynomialFunctions (Icc (0:ℝ) 1) : Set C(Paper.Overlap,ℝ))=univ := by
      exact congrArg (fun A : Subalgebra ℝ C(Paper.Overlap,ℝ)=>(A : Set C(Paper.Overlap,ℝ)))
        (polynomialFunctions.topologicalClosure (Icc (0:ℝ) 1))
    intro φ
    rw [show Set.range (fun P : ℝ[X]=>P.toContinuousMapOn (Icc (0:ℝ) 1))=
        (polynomialFunctions (Icc (0:ℝ) 1) : Set C(Paper.Overlap,ℝ)) from (polynomialFunctions_coe _).symm,
      he]
    exact mem_univ φ
  exact (ContinuousMap.toLp_denseRange (p:=2) (μ:=ν) ℝ ℝ (by norm_num)).comp hp
    (ContinuousMap.toLp 2 ν ℝ).continuous

def IsEndpointFixedLipschitz (φ : C(Paper.Overlap,ℝ)) : Prop:=
  φ ⟨0,by constructor <;>norm_num⟩=0 ∧ φ ⟨1,by constructor <;>norm_num⟩=0 ∧
    ∃K : ℝ≥0,LipschitzWith K φ

theorem endpointFixedLipschitz_toLp_mem [IsFiniteMeasure ν]
    (φ : C(Paper.Overlap,ℝ)) (hφ : IsEndpointFixedLipschitz φ) :
    ContinuousMap.toLp 2 ν ℝ φ∈endpointFixedL2 ν := by
  rw [mem_endpointFixedL2_iff]
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ) ν φ] with q hq
  intro he
  rw [hq]
  rcases he with h0|h1
  · have heq : q=(⟨0,by constructor <;>norm_num⟩:Paper.Overlap):=Subtype.ext h0
    rw [heq]
    exact hφ.1
  · have heq : q=(⟨1,by constructor <;>norm_num⟩:Paper.Overlap):=Subtype.ext h1
    rw [heq]
    exact hφ.2.1

theorem endpointCutoff_polynomial_toLp [IsFiniteMeasure ν] (j : ℕ) (P : ℝ[X]) :
    endpointCutoffLp ν j (ContinuousMap.toLp 2 ν ℝ (P.toContinuousMapOn (Icc (0:ℝ) 1)))=
      ContinuousMap.toLp 2 ν ℝ ((endpointCutoffPolynomial j*P).toContinuousMapOn (Icc (0:ℝ) 1)) := by
  apply Lp.ext
  filter_upwards [endpointCutoffLp_coeFn ν j (ContinuousMap.toLp 2 ν ℝ (P.toContinuousMapOn (Icc (0:ℝ) 1))),
    ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ) ν (P.toContinuousMapOn (Icc (0:ℝ) 1)),
    ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ) ν ((endpointCutoffPolynomial j*P).toContinuousMapOn (Icc (0:ℝ) 1))]
      with q hτ hp hprod
  simp only [hτ,hp,hprod,endpointCutoff,Polynomial.toContinuousMapOn_apply]
  change (endpointCutoffPolynomial j).eval (q:ℝ)*P.eval (q:ℝ)=_
  exact Polynomial.eval_mul.symm

theorem endpointCutoff_polynomial_is_test (j : ℕ) (P : ℝ[X]) :
    IsEndpointFixedLipschitz ((endpointCutoffPolynomial j*P).toContinuousMapOn (Icc (0:ℝ) 1)) := by
  refine ⟨?_,?_,polynomial_overlap_lipschitz _⟩ <;>
    simp [endpointCutoffPolynomial]

theorem endpointFixedLipschitz_approximation [IsFiniteMeasure ν]
    (f : Lp ℝ 2 ν) (hf : f∈endpointFixedL2 ν) (ε : ℝ) (hε : 0<ε) :
    ∃φ : C(Paper.Overlap,ℝ),IsEndpointFixedLipschitz φ ∧
      ‖ContinuousMap.toLp 2 ν ℝ φ-f‖<ε := by
  have hc:=(Metric.tendsto_nhds.mp (endpointCutoffLp_tendsto ν f hf)) (ε/2) (by linarith)
  obtain ⟨j,hj⟩:=hc.exists
  obtain ⟨P,hP⟩:=(polynomial_toLp_denseRange ν).exists_dist_lt f (ε:=ε/2) (by linarith)
  let φ:=(endpointCutoffPolynomial j*P).toContinuousMapOn (Icc (0:ℝ) 1)
  refine ⟨φ,endpointCutoff_polynomial_is_test j P,?_⟩
  have hb:=endpointCutoffLp_contraction ν j (ContinuousMap.toLp 2 ν ℝ (P.toContinuousMapOn (Icc (0:ℝ) 1))) f
  rw [endpointCutoff_polynomial_toLp] at hb
  have hP' : ‖ContinuousMap.toLp 2 ν ℝ (P.toContinuousMapOn (Icc (0:ℝ) 1))-f‖<ε/2:=by
    simpa only [dist_eq_norm,norm_sub_rev] using hP
  have hj' : ‖endpointCutoffLp ν j f-f‖<ε/2:=by simpa only [dist_eq_norm] using hj
  calc
    ‖ContinuousMap.toLp 2 ν ℝ φ-f‖≤
        ‖ContinuousMap.toLp 2 ν ℝ φ-endpointCutoffLp ν j f‖+‖endpointCutoffLp ν j f-f‖:=by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (ContinuousMap.toLp 2 ν ℝ φ-endpointCutoffLp ν j f) (endpointCutoffLp ν j f-f)
    _≤‖ContinuousMap.toLp 2 ν ℝ (P.toContinuousMapOn (Icc (0:ℝ) 1))-f‖+
        ‖endpointCutoffLp ν j f-f‖:=add_le_add hb le_rfl
    _<ε:=by linarith

def EndpointFixedLipschitzTest:={φ : C(Paper.Overlap,ℝ)//IsEndpointFixedLipschitz φ}

def endpointFixedLipschitzEmbedding [IsFiniteMeasure ν] :
    EndpointFixedLipschitzTest→endpointFixedL2 ν:=fun φ=>
  ⟨ContinuousMap.toLp 2 ν ℝ φ.val,endpointFixedLipschitz_toLp_mem ν φ.val φ.property⟩

theorem endpointFixedLipschitzEmbedding_denseRange [IsFiniteMeasure ν] :
    DenseRange (endpointFixedLipschitzEmbedding ν) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ,hφ,hb⟩:=endpointFixedLipschitz_approximation ν f.val f.property ε hε
  refine ⟨endpointFixedLipschitzEmbedding ν ⟨φ,hφ⟩,⟨⟨φ,hφ⟩,rfl⟩,?_⟩
  change dist (f: Lp ℝ 2 ν) (ContinuousMap.toLp 2 ν ℝ φ)<ε
  simpa only [dist_eq_norm,norm_sub_rev] using hb

theorem endpointFixedLipschitz_toLp_closure [IsFiniteMeasure ν] :
    closure {f : Lp ℝ 2 ν|∃φ : C(Paper.Overlap,ℝ),IsEndpointFixedLipschitz φ ∧
      ContinuousMap.toLp 2 ν ℝ φ=f}=(endpointFixedL2 ν : Set (Lp ℝ 2 ν)) := by
  apply Subset.antisymm
  · apply closure_minimal _ (isClosed_endpointFixedL2 ν)
    rintro f ⟨φ,hφ,rfl⟩
    exact endpointFixedLipschitz_toLp_mem ν φ hφ
  · intro f hf
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨φ,hφ,hb⟩:=endpointFixedLipschitz_approximation ν f hf ε hε
    exact ⟨ContinuousMap.toLp 2 ν ℝ φ,⟨φ,hφ,rfl⟩,by simpa only [dist_eq_norm,norm_sub_rev] using hb⟩

def endpointFixedLipschitzTests : Submodule ℝ C(Paper.Overlap,ℝ) where
  carrier:=IsEndpointFixedLipschitz
  zero_mem':=⟨rfl,rfl,0,LipschitzWith.const 0⟩
  add_mem':=by
    intro φ ψ hφ hψ
    rcases hφ with ⟨hφ0,hφ1,K,hK⟩
    rcases hψ with ⟨hψ0,hψ1,L,hL⟩
    refine ⟨?_,?_,K+L,?_⟩
    · change φ _+ψ _=0
      rw [hφ0,hψ0,add_zero]
    · change φ _+ψ _=0
      rw [hφ1,hψ1,add_zero]
    · exact hK.add hL
  smul_mem':=by
    intro c φ hφ
    rcases hφ with ⟨hφ0,hφ1,K,hK⟩
    refine ⟨?_,?_,‖c‖₊*K,LipschitzWith.of_dist_le_mul fun q r=>?_⟩
    · change c*φ _=0
      rw [hφ0,mul_zero]
    · change c*φ _=0
      rw [hφ1,mul_zero]
    · change dist (c*φ q) (c*φ r)≤(‖c‖₊*K:ℝ≥0)*dist q r
      rw [dist_eq_norm,←mul_sub,norm_mul]
      have hh:=mul_le_mul_of_nonneg_left (hK.dist_le_mul q r) (norm_nonneg c)
      simpa only [dist_eq_norm,NNReal.coe_mul,coe_nnnorm,mul_assoc] using hh

theorem mem_endpointFixedLipschitzTests_iff (φ : C(Paper.Overlap,ℝ)) :
    φ∈endpointFixedLipschitzTests ↔ IsEndpointFixedLipschitz φ:=Iff.rfl

def endpointFixedLipschitzLinearEmbedding [IsFiniteMeasure ν] :
    endpointFixedLipschitzTests→ₗ[ℝ]endpointFixedL2 ν:=
  LinearMap.codRestrict (endpointFixedL2 ν)
    ((ContinuousMap.toLp 2 ν ℝ).toLinearMap.comp endpointFixedLipschitzTests.subtype)
    (fun φ=>endpointFixedLipschitz_toLp_mem ν φ.val φ.property)

theorem endpointFixedLipschitzLinearEmbedding_apply [IsFiniteMeasure ν]
    (φ : endpointFixedLipschitzTests) :
    (endpointFixedLipschitzLinearEmbedding ν φ : Lp ℝ 2 ν)=
      ContinuousMap.toLp 2 ν ℝ φ.val:=rfl

theorem endpointFixedLipschitzLinearEmbedding_denseRange [IsFiniteMeasure ν] :
    DenseRange (endpointFixedLipschitzLinearEmbedding ν) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ,hφ,hb⟩:=endpointFixedLipschitz_approximation ν f.val f.property ε hε
  refine ⟨endpointFixedLipschitzLinearEmbedding ν ⟨φ,hφ⟩,⟨⟨φ,hφ⟩,rfl⟩,?_⟩
  change dist (f: Lp ℝ 2 ν) (ContinuousMap.toLp 2 ν ℝ φ)<ε
  simpa only [dist_eq_norm,norm_sub_rev] using hb

def endpointFixedLipschitzContinuousEmbedding [IsFiniteMeasure ν] :
    endpointFixedLipschitzTests→L[ℝ]endpointFixedL2 ν:=
  (endpointFixedLipschitzLinearEmbedding ν).mkContinuous
    ‖(ContinuousMap.toLp 2 ν ℝ : C(Paper.Overlap,ℝ)→L[ℝ]Lp ℝ 2 ν)‖
    (fun φ=>by
      change ‖ContinuousMap.toLp 2 ν ℝ φ.val‖≤
        ‖(ContinuousMap.toLp 2 ν ℝ : C(Paper.Overlap,ℝ)→L[ℝ]Lp ℝ 2 ν)‖*‖φ.val‖
      exact (ContinuousMap.toLp 2 ν ℝ).le_opNorm φ.val)

theorem endpointFixedLipschitzContinuousEmbedding_denseRange [IsFiniteMeasure ν] :
    DenseRange (endpointFixedLipschitzContinuousEmbedding ν):=
  endpointFixedLipschitzLinearEmbedding_denseRange ν

end FourPapersCommon
