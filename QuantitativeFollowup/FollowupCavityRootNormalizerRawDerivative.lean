module
public import QuantitativeFollowup.FollowupCavityRootNormalizerMovingPotential
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Actual simultaneous root-coordinate/covariance differentiation of the
arbitrary-profile partition. Uniform Gaussian domination is proved from the
constructed spatial Lipschitz bound and actual variance response bound. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets OverlapPaper
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def anisotropicMovingRootPartition (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) : ℝ :=
  ∫g,Real.exp (a*anisotropicMovingRootPotential D μ p i d alpha u g)∂anisotropicDisorderLaw n

def anisotropicMovingRootResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) (g : AnisotropicDisorder n) : ℝ :=
  -alpha*anisotropicRootVarianceResponse (anisotropicReplaceVariance D i (d-alpha*u)) μ i
    (gaussianSelectedScale p u g)+
  fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*u)) μ)
    (anisotropicDisorderInjection n (gaussianSelectedScale p u g))
    (anisotropicDisorderInjection n (gaussianSelectedScaleDerivative p u g))

theorem hasDerivAt_anisotropicMovingRootPartition (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) (halpha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    HasDerivAt (anisotropicMovingRootPartition D μ a p i d alpha)
      (a*∫g,Real.exp (a*anisotropicMovingRootPotential D μ p i d alpha u g)*
        anisotropicMovingRootResponse D μ p i d alpha u g ∂anisotropicDisorderLaw n) u := by
  classical
  let b:=d-alpha*u
  let A : ℝ:=(Fintype.card (AnisotropicCouplingIndex n):ℝ)*(1+Real.sqrt (u+1))
  let C : ℝ:=(Fintype.card (AnisotropicCouplingIndex n):ℝ)/(2*Real.sqrt (u/2))
  let M : ℝ:=‖anisotropicEnergyMap D‖*‖anisotropicDisorderInjection n‖
  let B : ℝ:=Real.exp (|a| *(|anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ 0|+
    alpha*(u+1)/2))
  let K : ℝ:=|a| *M*A
  let H : ℝ:=|a| *(alpha/2+M*C)
  let s : Set ℝ:=Ioo (u/2) (u+1) ∩ (fun t=>d-alpha*t)⁻¹' Ioi (b/2)
  let U:=anisotropicMovingRootPotential D μ p i d alpha
  let R:=anisotropicMovingRootResponse D μ p i d alpha
  let E:=fun t g=>Real.exp (a*U t g)
  have hA : 0≤A:=by dsimp [A];positivity
  have hC : 0≤C:=by dsimp [C];positivity
  have hM : 0≤M:=by dsimp [M];positivity
  have hB : 0≤B:=by dsimp [B];positivity
  have hK : 0≤K:=by dsimp [K];positivity
  have hH : 0≤H:=by dsimp [H];positivity
  have hsm : s∈𝓝 u := by
    apply Filter.inter_mem
    · exact isOpen_Ioo.mem_nhds (show u∈Ioo (u/2) (u+1) by constructor <;> linarith)
    · exact (show Continuous (fun t : ℝ=>d-alpha*t) by fun_prop).continuousAt.eventually
        (Ioi_mem_nhds (show b/2<d-alpha*u by dsimp [b];linarith))
  have htpos (t : ℝ) (ht : t∈s) : 0<d-alpha*t:=by
    have hh:=ht.2;change b/2<d-alpha*t at hh;dsimp [b] at hh;linarith
  have hUm (t : ℝ) : Measurable (U t) := by
    exact (contDiff_one_anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*t)) μ).continuous.measurable.comp
      ((anisotropicDisorderInjection n).continuous.measurable.comp (gaussianSelectedScale p t).continuous.measurable)
  have hRm (t : ℝ) : Measurable (R t) := by
    have hr:=(measurable_anisotropicRestartVarianceResponse_disorder
      (anisotropicReplaceVariance D i (d-alpha*t)) μ ⟨0,by norm_num⟩ 0 i).comp
      (gaussianSelectedScale p t).continuous.measurable
    have hd:=(contDiff_one_anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*t)) μ).continuous_fderiv (by norm_num)
    have hp:=(anisotropicDisorderInjection n).continuous.comp (gaussianSelectedScale p t).continuous
    have hpd:=(anisotropicDisorderInjection n).continuous.comp (gaussianSelectedScaleDerivative p t).continuous
    exact (hr.const_mul (-alpha)).add ((hd.comp hp).clm_apply hpd).measurable
  have hEm (t : ℝ) : Measurable (E t):=((hUm t).const_mul a).exp
  have hUb (t : ℝ) (ht : t∈s) (g : AnisotropicDisorder n) :
      |U t g|≤|anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ 0|+
        alpha*(u+1)/2+M*A*‖g‖ := by
    let Dt:=anisotropicReplaceVariance D i (d-alpha*t)
    let P:=anisotropicDisorderInjection n (gaussianSelectedScale p t g)
    have hL:=anisotropicMeasurePotential_lipschitz Dt μ
    rw [anisotropicReplaceVariance_energyMap] at hL
    have hl: |anisotropicMeasurePotential Dt μ P-anisotropicMeasurePotential Dt μ 0|≤
        ‖anisotropicEnergyMap D‖*‖P‖ := by
      simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,sub_zero,coe_nnnorm] using hL.dist_le_mul P 0
    have hv:=anisotropicMeasureTailPotential_variance_abs_sub_le D μ ⟨0,by norm_num⟩
      (0:AnisotropicParameter n) i (d-alpha*t) b (htpos t ht) hb
    simp only [anisotropicMeasureTailPotential_zero,Subtype.coe_mk,sub_zero] at hv
    have hab: |t-u|≤u+1:=by rw [abs_le];constructor <;> linarith [ht.1.1,ht.1.2]
    have hvar: |(d-alpha*t)-b|≤alpha*(u+1) := by
      dsimp [b]
      rw [show (d-alpha*t)-(d-alpha*u)= -alpha*(t-u) by ring,abs_mul,abs_neg,abs_of_nonneg halpha]
      exact mul_le_mul_of_nonneg_left hab halpha
    have hn : ‖P‖≤‖anisotropicDisorderInjection n‖*(A*‖g‖):=
      ((anisotropicDisorderInjection n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p t (u+1) ht.1.2.le g) (norm_nonneg _))
    have htri : |anisotropicMeasurePotential Dt μ P| ≤
        |anisotropicMeasurePotential Dt μ P-anisotropicMeasurePotential Dt μ 0|+
          |anisotropicMeasurePotential Dt μ 0| := by
      convert abs_add_le (anisotropicMeasurePotential Dt μ P-anisotropicMeasurePotential Dt μ 0)
        (anisotropicMeasurePotential Dt μ 0) using 1 <;> ring_nf
    have htri0 : |anisotropicMeasurePotential Dt μ 0| ≤
        |anisotropicMeasurePotential Dt μ 0-anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ 0|+
          |anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ 0| := by
      convert abs_add_le (anisotropicMeasurePotential Dt μ 0-anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ 0)
        (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ 0) using 1 <;> ring_nf
    change |anisotropicMeasurePotential Dt μ P|≤_
    have hpn:=mul_le_mul_of_nonneg_left hn (norm_nonneg (anisotropicEnergyMap D))
    dsimp only [M] at *
    nlinarith only [hl,hv,hvar,hpn,htri,htri0]
  have hEb (t : ℝ) (ht : t∈s) (g : AnisotropicDisorder n) :
      ‖E t g‖≤B*Real.exp (K*‖g‖) := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp only [E,B,K]
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1:=le_abs_self (a*U t g)
    rw [abs_mul] at h1
    have h2:=mul_le_mul_of_nonneg_left (hUb t ht g) (abs_nonneg a)
    nlinarith only [h1,h2]
  have hRb (t : ℝ) (ht : t∈s) (g : AnisotropicDisorder n) :
      ‖R t g‖≤alpha/2+M*C*‖g‖ := by
    have hr:=norm_anisotropicRestartVarianceResponse_le_half
      (anisotropicReplaceVariance D i (d-alpha*t)) μ (gaussianSelectedScale p t g) ⟨0,by norm_num⟩ 0 i
    have hd:=norm_fderiv_le_of_lipschitz ℝ
      (anisotropicMeasurePotential_lipschitz (anisotropicReplaceVariance D i (d-alpha*t)) μ)
      (x₀:=anisotropicDisorderInjection n (gaussianSelectedScale p t g))
    rw [anisotropicReplaceVariance_energyMap] at hd
    have hn:= (anisotropicDisorderInjection n).le_opNorm (gaussianSelectedScaleDerivative p t g)
    have hs:=norm_gaussianSelectedScaleDerivative_le p t (u/2) (by linarith) ht.1.1.le g
    have hp:= (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*t)) μ)
      (anisotropicDisorderInjection n (gaussianSelectedScale p t g))).le_opNorm
        (anisotropicDisorderInjection n (gaussianSelectedScaleDerivative p t g))
    unfold R anisotropicMovingRootResponse
    apply (norm_add_le _ _).trans
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg halpha]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left hr halpha).trans_eq (by ring)
    · apply hp.trans
      calc
        _≤‖anisotropicEnergyMap D‖* (‖anisotropicDisorderInjection n‖*(C*‖g‖)) :=
          mul_le_mul hd (hn.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _)
        _=M*C*‖g‖:=by dsimp [M];ring
  have hDB (t : ℝ) (ht : t∈s) (g : AnisotropicDisorder n) :
      ‖E t g*(a*R t g)‖≤H*B*Real.exp ((K+1)*‖g‖) := by
    rw [norm_mul,norm_mul,Real.norm_eq_abs]
    have hlin : alpha/2+M*C*‖g‖≤(alpha/2+M*C)*(1+‖g‖):=by nlinarith [norm_nonneg g]
    calc
      _≤(B*Real.exp (K*‖g‖))*(|a| *((alpha/2+M*C)*(1+‖g‖))) := by
        apply mul_le_mul (hEb t ht g) _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left ((hRb t ht g).trans hlin) (abs_nonneg a)
      _≤(B*Real.exp (K*‖g‖))*(|a| *((alpha/2+M*C)*Real.exp ‖g‖)) := by
        gcongr;simpa only [add_comm] using Real.add_one_le_exp ‖g‖
      _=H*B*Real.exp ((K+1)*‖g‖) := by dsimp [H];rw [show (K+1)*‖g‖=K*‖g‖+‖g‖ by ring,Real.exp_add];ring
  have huu : u∈s:=mem_of_mem_nhds hsm
  have hi:=hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=anisotropicDisorderLaw n) (s:=s) (F:=E) (F':=fun t g=>E t g*(a*R t g))
    (bound:=fun g=>H*B*Real.exp ((K+1)*‖g‖)) hsm
    (.of_forall fun t=>(hEm t).aestronglyMeasurable)
    (integrable_gaussian_exponential_bound (stdGaussian (AnisotropicDisorder n)) (E u) (hEm u) B K hB (hEb u huu))
    ((hEm u).mul ((hRm u).const_mul a)).aestronglyMeasurable
    (.of_forall fun g t ht=>hDB t ht g)
    ((integrable_exp_mul_norm_gaussian (stdGaussian (AnisotropicDisorder n)) (K+1)).const_mul (H*B))
    (.of_forall fun g t ht=>(hasDerivAt_anisotropicMovingRootPotential D μ p i d alpha t
      (by linarith [ht.1.1]) (htpos t ht) g).const_mul a |>.exp)
  have he : (∫g,E u g*(a*R u g)∂anisotropicDisorderLaw n)=
      a*∫g,E u g*R u g∂anisotropicDisorderLaw n := by
    simp_rw [show ∀g,E u g*(a*R u g)=a*(E u g*R u g) from fun g=>by ring]
    rw [integral_const_mul]
  convert hi.2 using 1 <;> (simp only [he,E,U,R,anisotropicMovingRootPartition]; try rfl)

end QuantitativeFollowup
