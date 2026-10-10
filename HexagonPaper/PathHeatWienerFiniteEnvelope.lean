module
public import HexagonPaper.PathHeatWienerFiniteConditionalResponse
public import HexagonPaper.PathHeatReferenceReordering

@[expose] public section

/-! Actual Fernique domination for finite physical Wiener samples, with
an arbitrary fixed Gaussian auxiliary law and a finite auxiliary measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L n : ℕ} {a b : ℝ}

def pathHeatWienerConditionalEnvelope (G : ℝ) (ω : (E×K)×(Fin L→WienerPath)) : ℝ :=
  Real.exp (G*(1+‖ω.1.1‖+∑l : Fin L,‖ω.2 l‖))

theorem integrable_pathHeatWienerConditionalEnvelope
    (μ : Measure E) [IsGaussian μ] (κ : Measure K) [IsFiniteMeasure κ] (G : ℝ) :
    Integrable (pathHeatWienerConditionalEnvelope (L:=L) G)
      ((μ.prod κ).prod (pathHeatWienerMeshBase (J:=Fin L))) := by
  have hg := integrable_exp_mul_norm_gaussian μ G
  have hk : Integrable (fun _ : K=>(1:ℝ)) κ := integrable_const _
  have hw : Integrable (fun w : Fin L→WienerPath=>∏l : Fin L,Real.exp (G*‖w l‖))
      (pathHeatWienerMeshBase (J:=Fin L)) :=
    Integrable.fintype_prod (fun _=>integrable_exp_norm_canonicalWienerMeasure G)
  convert ((hg.mul_prod hk).mul_prod hw).const_mul (Real.exp G) using 1
  funext ω
  simp only [pathHeatWienerConditionalEnvelope,mul_one,←Real.exp_sum,Finset.mul_sum,←Real.exp_add]
  congr 1
  simp only [mul_add,mul_one,Finset.mul_sum]
  <;> ring

theorem integrable_pathHeatWienerConditionalEnvelope_slice (G : ℝ) (aux : E×K) :
    Integrable (fun w=>pathHeatWienerConditionalEnvelope (L:=L) G (aux,w))
      (pathHeatWienerMeshBase (J:=Fin L)) := by
  have hw : Integrable (fun w : Fin L→WienerPath=>∏l : Fin L,Real.exp (G*‖w l‖))
      (pathHeatWienerMeshBase (J:=Fin L)) :=
    Integrable.fintype_prod (fun _=>integrable_exp_norm_canonicalWienerMeasure G)
  convert hw.const_mul (Real.exp (G*(1+‖aux.1‖))) using 1
  funext w
  simp only [pathHeatWienerConditionalEnvelope,←Real.exp_sum,Finset.mul_sum,←Real.exp_add]
  congr 1
  simp only [mul_add,mul_one,Finset.mul_sum]
  <;> ring

theorem continuous_pathHeatWienerFiniteConditionalState (hab : a≤b)
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : ℝ) :
    Continuous (fun ω : (E×K)×(Fin L→WienerPath)=>
      pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2) := by
  have hp := (pathHeatTreeMixedOperator (E:=ℝ) δ W).continuous.comp
    ((pathHeatTreeBernsteinOperator (E:=ℝ) n L).continuous.comp
      ((continuous_pathHeatFlatClockPath_Wiener L (c z)).comp
        (continuous_snd : Continuous (fun ω : (E×K)×(Fin L→WienerPath)=>ω.2))))
  exact continuous_const.prodMk (continuous_fst.prodMk hp)

theorem pathHeatWienerFinite_weight_bound (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatWienerAnalyticSource a b hab d C)
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : ℝ) (aux : E×K) (w : Fin L→WienerPath) :
    d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)≤
      pathHeatWienerConditionalEnvelope (C*(1+pathHeatTreeMixedBound δ W)) (aux,w) := by
  let T := pathHeatTreeMixedOperator (E:=ℝ) δ W
  let p := T (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) w))
  have hp : ‖p‖≤pathHeatTreeMixedBound δ W*(∑l : Fin L,‖w l‖) :=
    (pathHeatTreeMixedOperator_norm_apply_le δ W _).trans (mul_le_mul_of_nonneg_left
      ((norm_pathHeatTreeBernsteinSample_le n L _).trans (norm_pathHeatFlatClockPath_le L _ _))
      (pathHeatTreeMixedBound_nonneg δ W))
  have hsum : 0≤∑l : Fin L,‖w l‖ := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have hg := (le_abs_self (d.ell (projIcc a b hab z,(aux,p)))).trans
    (hsource.ell_growth (projIcc a b hab z) aux p)
  change Real.exp (d.ell (projIcc a b hab z,(aux,p)))≤
    Real.exp (C*(1+pathHeatTreeMixedBound δ W)*(1+‖aux.1‖+∑l : Fin L,‖w l‖))
  apply Real.exp_le_exp.mpr
  have hC : 0≤(C:ℝ) := C.coe_nonneg
  nlinarith [norm_nonneg aux.1,pathHeatTreeMixedBound_nonneg δ W,
    mul_nonneg hC (pathHeatTreeMixedBound_nonneg δ W),mul_nonneg hC hsum,
    mul_nonneg (mul_nonneg hC (pathHeatTreeMixedBound_nonneg δ W)) (norm_nonneg aux.1)]

theorem norm_pathHeatWienerFiniteKernel_le
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (dc : ℝ→Fin L→C(I,ℝ))
    (D : ℝ≥0) (z : ℝ) (hD : ‖pathHeatClockRawKernel (dc z)‖≤D) :
    ‖pathHeatWienerFiniteKernel n L δ W dc z‖≤
      (Real.toNNReal ((pathHeatTreeMixedBound δ W)^2*(D:ℝ)):ℝ≥0) := by
  rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) D.coe_nonneg)]
  change ‖pathHeatTreeKernelBCF L
    (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L (pathHeatClockRawKernel (dc z))))‖≤_
  exact (norm_pathHeatTreeKernelBCF_le L _).trans
    ((norm_pathHeatTreeMixedKernelOperator_apply_le δ W _).trans (by
      simpa using mul_le_mul_of_nonneg_left
        ((norm_pathHeatTreeKernelSample_le n L _).trans hD) (sq_nonneg _)))

end HexagonPaper
