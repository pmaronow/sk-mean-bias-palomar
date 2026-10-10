module
public import HexagonPaper.PathHeatFiniteTreeModelRealClock

@[expose] public section

/-! Fixed rescaling of real clocks restores the literal physical covariance
kernel in both slots, including every ancestor-terminal contribution. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {J : ℕ}

theorem pathHeatClockRawKernel_div (c : Fin J→C(I,ℝ)) (R : ℝ) (x y : Fin J×I) :
    pathHeatClockRawKernel (fun j=>pathHeatRealClockNormalizeDerivative (c j) R) x y=
      pathHeatClockRawKernel c x y/R := by
  simp only [pathHeatClockRawKernel_apply,pathHeatRealClockNormalizeDerivative_apply]
  split_ifs <;> simp

theorem pathHeatTreeMixedKernel_realClock_restored (c : Fin J→C(I,ℝ)) (R : ℝ)
    (hR : 0<R) (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) :
    pathHeatTreeMixedKernelOperator (fun j=>δ j*Real.sqrt R) (fun j k=>W j k*Real.sqrt R)
      (pathHeatClockRawKernel (fun j=>pathHeatRealClockNormalizeDerivative (c j) R))=
        pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel c) := by
  have he (a b x : ℝ) : (a*Real.sqrt R)*(b*Real.sqrt R)*(x/R)=a*b*x := by
    calc
      _ = a*b*((Real.sqrt R)^2)*(x/R) := by ring
      _ = a*b*R*(x/R) := by rw [Real.sq_sqrt hR.le]
      _ = a*b*x := by field_simp
  ext x y
  simp only [pathHeatTreeMixedKernelOperator_four_terms,smul_eq_mul,pathHeatClockRawKernel_div,he]

theorem pathHeatTreeMixedKernel_realClock_covariance_restored (c : Fin J→C(I,ℝ)) (R : ℝ)
    (hR : 0<R) (hc : ∀j q,0≤c j q) (hbound : ∀j q,c j q≤R)
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) :
    pathHeatTreeMixedKernelOperator (fun j=>δ j*Real.sqrt R) (fun j k=>W j k*Real.sqrt R)
      (pathHeatClockRawKernel (pathHeatClockReal
        (fun j=>pathHeatRealClockNormalize (c j) R hR (hc j) (hbound j))))=
        pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel c) := by
  have he : pathHeatClockReal (fun j=>pathHeatRealClockNormalize (c j) R hR (hc j) (hbound j))=
      fun j=>pathHeatRealClockNormalizeDerivative (c j) R := by
    funext j
    ext q
    rfl
  rw [he]
  exact pathHeatTreeMixedKernel_realClock_restored c R hR δ W

end HexagonPaper
