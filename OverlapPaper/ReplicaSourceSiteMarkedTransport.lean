module
public import FourPapersCommon.FiniteStateCascadeGibbsTransport
public import OverlapPaper.ReplicaSourceSiteCascade

@[expose] public section

/-! The marked terminal coefficient under the actual spin-field Gibbs
cascade equals the marked tanh product under its actual site-field cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace OverlapPaper
open FourPapersCommon SpinGlass.AT
set_option maxHeartbeats 1000000
variable {d : ℕ}

 theorem integral_replicaSingleSiteGibbs_product (h : ℝ) (mark : Finset (Fin d))
    (x : FiniteStateField (Fin d)) :
    (∫ ε : Configuration d, replicaSpinProduct mark ε
      ∂finiteStateGibbsKernel (fun ε => h*∑ l : Fin d, spin (ε l)) (replicaSingleSiteSpinCLM x))=
      replicaTerminalCoefficient mark (fun l => h+x l) := by
  classical
  rw [integral_finiteStateGibbsKernel]
  have he (ε : Configuration d) : replicaSingleSiteSpinCLM x ε+h*∑ l : Fin d, spin (ε l)=
      ∑ l : Fin d, (h+x l)*spin (ε l) := by
    simp only [replicaSingleSiteSpinCLM,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,
      AddHom.coe_mk,WithLp.ofLp_toLp,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    ring
  have hZ : gtStatePartition (fun ε : Configuration d => h*∑ l : Fin d, spin (ε l))
      (replicaSingleSiteSpinCLM x)=replicaTerminalBasePartition (fun l => h+x l) := by
    simp only [gtStatePartition,replicaTerminalBasePartition,he]
  simp only [gtStateGibbs,hZ,he]
  have hc (ε : Configuration d) :
      Real.exp (∑ l : Fin d, (h+x l)*spin (ε l))/replicaTerminalBasePartition (fun l => h+x l)*
      replicaSpinProduct mark ε=
      (replicaSpinProduct mark ε*Real.exp (∑ l : Fin d, (h+x l)*spin (ε l)))/
        replicaTerminalBasePartition (fun l => h+x l) := by ring
  simp_rw [hc]
  rw [←Finset.sum_div,replicaTerminalProduct_sum,
    mul_div_cancel_left₀ _ (replicaTerminalBasePartition_pos _).ne']
  rfl

 theorem replicaSourceSiteMarkedMean_eq_siteExpectation (h : ℝ) (mark : Finset (Fin d))
    (a : ℕ → ℝ) (ha : ∀ i, 0≤a i) (v : ℕ → ℝ)
    (groupOf : ℕ → Fin d → Fin d) (J : ℕ) :
    replicaSourceSiteMarkedMean h mark a v groupOf J=
      sourceKernelExpectation
        (finiteStateGaussianCascadeKernel a
          (fun i => replicaSiteCopyGaussianCLM (v i) (groupOf i))
          (replicaSourceSingleSite h 0 mark)) J
        (fun y => replicaTerminalCoefficient mark (fun l => h+y l)) 0 := by
  let T := replicaSingleSiteSpinCLM (d := d)
  let V : Configuration d → ℝ := fun ε => h*∑ l : Fin d, spin (ε l)
  have he := integral_finiteStateCascadeGibbsKernel_comp_linear V (replicaSpinProduct mark) a ha T
    (fun i => replicaSiteCopyGaussianCLM (v i) (groupOf i)) J 0
  have hF : (fun y => gtStateLogPartition V (T y))=replicaSourceSingleSite h 0 mark := by
    funext y
    rw [replicaSourceSingleSite_eq_terminal]
    simp only [zero_mul,add_zero]
    rfl
  have hG : (fun y => ∫ ε, replicaSpinProduct mark ε ∂finiteStateGibbsKernel V (T y))=
      (fun y => replicaTerminalCoefficient mark (fun l => h+y l)) := by
    funext y
    exact integral_replicaSingleSiteGibbs_product h mark y
  rw [hF,hG] at he
  simpa only [T,V,map_zero,replicaSourceSiteMarkedMean] using he

end OverlapPaper
