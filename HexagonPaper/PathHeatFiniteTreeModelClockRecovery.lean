module
public import HexagonPaper.PathHeatFiniteTreeModelRealClockCovariance

@[expose] public section

/-! The source's continuous physical dot-kernel determines every edge-clock
derivative continuously. A tree row has nonzero own coefficient and no self
ancestor term; subtracting its root diagonal cancels all ancestor terms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {J : ℕ}

theorem pathHeatTreeMixedClockKernel_diagonal (c : Fin J→C(I,ℝ))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (j : Fin J) (hself : W j j=0) (t : I) :
    pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel c) (j,t) (j,t)=
      (δ j)^2*c j t+∑a : Fin J,(W j a)^2*c a 1 := by
  rw [pathHeatTreeMixedKernelOperator_four_terms]
  simp [pathHeatClockRawKernel_apply,mul_ite,hself,pow_two]

theorem pathHeatTreeMixedClockKernel_recover (c : Fin J→C(I,ℝ))
    (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ) (j : Fin J) (hself : W j j=0)
    (hδ : δ j≠0) (hroot : c j 0=0) (t : I) :
    c j t=(pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel c) (j,t) (j,t)-
      pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel c) (j,0) (j,0))/(δ j)^2 := by
  rw [pathHeatTreeMixedClockKernel_diagonal c δ W j hself,
    pathHeatTreeMixedClockKernel_diagonal c δ W j hself,hroot]
  field_simp
  ring

theorem continuous_pathHeatTreeClockDerivative_of_mixedKernel
    {Z : Type*} [TopologicalSpace Z]
    (dc : Z→Fin J→C(I,ℝ)) (δ : Fin J→ℝ) (W : Fin J→Fin J→ℝ)
    (hc : Continuous (fun z=>(pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z))).uncurry))
    (j : Fin J) (hself : W j j=0) (hδ : δ j≠0) (hroot : ∀z,dc z j 0=0) :
    Continuous (fun z=>dc z j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let p : C(Z×I,(Fin J×I)×(Fin J×I)):=
    ⟨fun x=>((j,x.2),(j,x.2)),(continuous_const.prodMk continuous_snd).prodMk
      (continuous_const.prodMk continuous_snd)⟩
  let r : (Fin J×I)×(Fin J×I):=((j,0),(j,0))
  have ht : Continuous (fun x : Z×I=>
      (pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc x.1))).uncurry (p x)) :=
    continuous_eval.comp ((hc.comp continuous_fst).prodMk p.continuous)
  have hr : Continuous (fun x : Z×I=>
      (pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc x.1))).uncurry r) :=
    (continuous_eval_const r).comp (hc.comp continuous_fst)
  convert (ht.sub hr).div_const ((δ j)^2) using 1
  funext x
  exact pathHeatTreeMixedClockKernel_recover (dc x.1) δ W j hself hδ (hroot x.1) x.2

end HexagonPaper
