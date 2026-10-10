module
public import QuantitativeFollowup.CavityDeletedSpinKernelMoments
public import QuantitativeFollowup.ThreeDescendantNativeLaw

@[expose] public section

/-! The actual conditional three-descendant law obeys the deleted-coordinate
square comparison. The common conditional past and every terminal draw are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {N : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem cavityThreeDescendant_deleted_difference_square_le (D : AnisotropicSpinModel N)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin N) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase i) z.2)^2
      ∂cavityThreeDescendantLaw D μ a q)≤
      2*(∫z,(cavitySpinDifferencePairing Finset.univ z.2)^2
        ∂cavityThreeDescendantLaw D μ a q)+4 := by
  let K:=((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ
    (anisotropicFreshTerminalSpinKernel D μ a q)) ×ₖ (anisotropicFreshTerminalSpinKernel D μ a q)
  let P:=anisotropicMeasureSpinPathLaw D μ a
  let fd:=fun z : CavityThreeTerminalSpins N=>(cavitySpinDifferencePairing (Finset.univ.erase i) z)^2
  let fu:=fun z : CavityThreeTerminalSpins N=>(cavitySpinDifferencePairing Finset.univ z)^2
  have hi (f : CavityThreeTerminalSpins N→ℝ) : Integrable (fun z=>f z.2) (P ⊗ₘ K) := by
    let B : ℝ:=∑z : CavityThreeTerminalSpins N,‖f z‖
    exact bounded_real_integrable _ ((measurable_of_finite f).comp measurable_snd) B
      (fun z=>Finset.single_le_sum (fun t _=>norm_nonneg (f t)) (Finset.mem_univ z.2))
  have ho (f : CavityThreeTerminalSpins N→ℝ) : Integrable (fun p=>∫z,f z∂K p) P := by
    let B : ℝ:=∑z : CavityThreeTerminalSpins N,‖f z‖
    apply bounded_real_integrable _ ((measurable_of_finite f).stronglyMeasurable.integral_kernel (κ:=K)).measurable B
    intro p
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=K p) (.of_forall fun z=>
        Finset.single_le_sum (fun t _=>norm_nonneg (f t)) (Finset.mem_univ z))
  change (∫z,fd z.2∂P ⊗ₘ K)≤2*(∫z,fu z.2∂P ⊗ₘ K)+4
  rw [Measure.integral_compProd (hi fd),Measure.integral_compProd (hi fu)]
  calc
    _≤∫p,2*(∫z,fu z∂K p)+4∂P := integral_mono (ho fd) ((ho fu).const_mul 2 |>.add (integrable_const 4))
      (fun p=>by
        simp only [K,Kernel.prod_apply]
        exact cavitySpinKernel_three_deleted_square_le (anisotropicFreshTerminalSpinKernel D μ a q p) i)
    _=_ := by rw [integral_add ((ho fu).const_mul 2) (integrable_const 4),integral_const_mul]
              simp only [integral_const,probReal_univ,one_smul]

end QuantitativeFollowup
