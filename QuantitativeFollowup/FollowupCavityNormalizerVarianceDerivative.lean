module
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! The actual arbitrary-profile outer partition is differentiated with
respect to one positive auxiliary variance. The response is the true
restarted-diffusion response, with Gaussian domination proved here. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n : ℕ}

def anisotropicRootVarianceResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) (g : AnisotropicDisorder n) : ℝ :=
  anisotropicRestartVarianceResponse D μ g ⟨0,by norm_num⟩ 0 i

theorem hasDerivAt_anisotropicMeasureOuterPartition_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (i : Fin n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun c=>anisotropicMeasureOuterPartition (anisotropicReplaceVariance D i c) μ a)
      (a*∫g,Real.exp (a*anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ
        (anisotropicDisorderInjection n g))*
        anisotropicRootVarianceResponse (anisotropicReplaceVariance D i b) μ i g
          ∂anisotropicDisorderLaw n) b := by
  let U:=fun c (g : AnisotropicDisorder n)=>anisotropicMeasurePotential
    (anisotropicReplaceVariance D i c) μ (anisotropicDisorderInjection n g)
  let R:=fun c=>anisotropicRootVarianceResponse (anisotropicReplaceVariance D i c) μ i
  let E:=fun c g=>Real.exp (a*U c g)
  let W:=fun g=>|a| /2*Real.exp (|a| *(b+1)/2)*E b g
  have hbm : b∈Ioo (b/2) (b+1):=by constructor <;> linarith
  have hUm (c : ℝ) : Measurable (U c):=
    (contDiff_one_anisotropicMeasurePotential _ μ).continuous.measurable.comp
      (anisotropicDisorderInjection n).continuous.measurable
  have hRm (c : ℝ) : Measurable (R c):=
    measurable_anisotropicRestartVarianceResponse_disorder _ μ _ 0 i
  have hEm (c : ℝ) : Measurable (E c):=(hUm c |>.const_mul a).exp
  have hD (c : ℝ) (hc : c∈Ioo (b/2) (b+1)) (g : AnisotropicDisorder n) :
      HasDerivAt (fun t=>U t g) (R c g) c := by
    have hd:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart D μ i g
      ⟨0,by norm_num⟩ 0 c (by linarith [hc.1])
    simpa only [anisotropicMeasureTailPotential_zero,map_zero,add_zero,U,R,
      anisotropicRootVarianceResponse] using hd
  have hUb (c : ℝ) (hc : c∈Ioo (b/2) (b+1)) (g : AnisotropicDisorder n) :
      |U c g-U b g|≤(b+1)/2 := by
    have hh:=anisotropicMeasureTailPotential_variance_abs_sub_le D μ
      ⟨0,by norm_num⟩ (anisotropicDisorderInjection n g) i c b (by linarith [hc.1]) hb
    simp only [anisotropicMeasureTailPotential_zero,Subtype.coe_mk,sub_zero,U] at hh
    have hab : |c-b|≤b+1:=by rw [abs_le];constructor <;> linarith [hc.1,hc.2]
    exact hh.trans (by nlinarith)
  have hEb (c : ℝ) (hc : c∈Ioo (b/2) (b+1)) (g : AnisotropicDisorder n) :
      E c g≤Real.exp (|a| *(b+1)/2)*E b g := by
    dsimp only [E]
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh:=le_abs_self (a*(U c g-U b g))
    rw [abs_mul] at hh
    have hmul:=mul_le_mul_of_nonneg_left (hUb c hc g) (abs_nonneg a)
    nlinarith
  have hBound (c : ℝ) (hc : c∈Ioo (b/2) (b+1)) (g : AnisotropicDisorder n) :
      ‖E c g*(a*R c g)‖≤W g := by
    have hr:=norm_anisotropicRestartVarianceResponse_le_half
      (anisotropicReplaceVariance D i c) μ g ⟨0,by norm_num⟩ 0 i
    change ‖R c g‖≤(1/2:ℝ) at hr
    rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_pos (show 0<E c g from Real.exp_pos _),Real.norm_eq_abs]
    calc
      E c g*(|a| *‖R c g‖)≤E c g*(|a| /2):=by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hr (abs_nonneg a)
      _≤(Real.exp (|a| *(b+1)/2)*E b g)*(|a| /2):=by gcongr;exact hEb c hc g
      _=W g:=by dsimp [W];ring
  have hInt:=hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=anisotropicDisorderLaw n) (s:=Ioo (b/2) (b+1))
    (F:=E) (F':=fun c g=>E c g*(a*R c g)) (bound:=W)
    (isOpen_Ioo.mem_nhds hbm)
    (.of_forall fun c=>(hEm c).aestronglyMeasurable)
    (integrable_exp_anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ a)
    ((hEm b).mul ((hRm b).const_mul a)).aestronglyMeasurable
    (.of_forall fun g c hc=>hBound c hc g)
    ((integrable_exp_anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ a).const_mul _)
    (.of_forall fun g c hc=>(hD c hc g).const_mul a |>.exp)
  have he : (∫g,E b g*(a*R b g)∂anisotropicDisorderLaw n)=
      a*∫g,E b g*R b g∂anisotropicDisorderLaw n := by
    simp_rw [show ∀g,E b g*(a*R b g)=a*(E b g*R b g) from fun g=>by ring]
    rw [integral_const_mul]
  simpa only [he,E,U,R,anisotropicMeasureOuterPartition] using hInt.2

theorem hasDerivAt_log_anisotropicMeasureOuterPartition_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (i : Fin n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun c=>Real.log (anisotropicMeasureOuterPartition
        (anisotropicReplaceVariance D i c) μ a))
      (a*∫g,anisotropicRootVarianceResponse (anisotropicReplaceVariance D i b) μ i g
        ∂anisotropicMeasureOuterLaw (anisotropicReplaceVariance D i b) μ a) b := by
  have hd:=(hasDerivAt_anisotropicMeasureOuterPartition_variance D μ a i b hb).log
    (anisotropicMeasureOuterPartition_pos _ μ a).ne'
  have he : (∫g,anisotropicRootVarianceResponse (anisotropicReplaceVariance D i b) μ i g
        ∂anisotropicMeasureOuterLaw (anisotropicReplaceVariance D i b) μ a)=
      (∫g,Real.exp (a*anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ
        (anisotropicDisorderInjection n g))*
        anisotropicRootVarianceResponse (anisotropicReplaceVariance D i b) μ i g
          ∂anisotropicDisorderLaw n)/anisotropicMeasureOuterPartition
            (anisotropicReplaceVariance D i b) μ a := by
    rw [anisotropicMeasureOuterLaw,integral_tilted]
    simp only [smul_eq_mul]
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
    rfl
  rw [he]
  convert hd using 1 <;> ring

end QuantitativeFollowup
