module
public import HexagonPaper.PathHeatClockCoupling
public import HexagonPaper.PathHeatTreeMovingLimits

@[expose] public section

/-! The actual finite family of independent clocked Wiener histories,
assembled as one continuous edge-indexed path. No abstract sample path is
assumed. The same Wiener paths couple every parameter and every mesh. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def pathHeatFlatEdgeInjection (L : ℕ) (l : Fin L) : WienerPath→L[ℝ]C(Fin L×I,ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f=>⟨fun x=>if x.1=l then f x.2 else 0,
        continuous_prod_of_discrete_left.mpr (fun k=>by
          by_cases h : k=l
          · simpa only [h,ite_true] using f.continuous
          · simpa only [h,ite_false] using (continuous_const : Continuous (fun _ : I=>(0:ℝ))))⟩
      map_add' := by intro f g;ext x;by_cases h : x.1=l <;> simp [h]
      map_smul' := by intro c f;ext x;by_cases h : x.1=l <;> simp [h] }
    1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      change ‖if x.1=l then f x.2 else 0‖≤‖f‖
      by_cases h : x.1=l
      · simp only [h,ite_true];exact f.norm_coe_le_norm x.2
      · simp only [h,ite_false,norm_zero];exact norm_nonneg f)

@[simp] theorem pathHeatFlatEdgeInjection_apply (L : ℕ) (l : Fin L)
    (f : WienerPath) (x : Fin L×I) :
    pathHeatFlatEdgeInjection L l f x=(if x.1=l then f x.2 else 0) := rfl

theorem norm_pathHeatFlatEdgeInjection_le (L : ℕ) (l : Fin L) (f : WienerPath) :
    ‖pathHeatFlatEdgeInjection L l f‖≤‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  rw [pathHeatFlatEdgeInjection_apply]
  split_ifs
  · exact f.norm_coe_le_norm x.2
  · simp only [norm_zero];exact norm_nonneg f

def pathHeatFlatClockPath (L : ℕ) (c : Fin L→C(I,I)) (w : Fin L→WienerPath) :
    C(Fin L×I,ℝ) := ∑l : Fin L,pathHeatFlatEdgeInjection L l (w l |>.comp (c l))

@[simp] theorem pathHeatFlatClockPath_apply (L : ℕ)
    (c : Fin L→C(I,I)) (w : Fin L→WienerPath) (x : Fin L×I) :
    pathHeatFlatClockPath L c w x=w x.1 (c x.1 x.2) := by
  simp [pathHeatFlatClockPath,ContinuousMap.sum_apply,pathHeatFlatEdgeInjection_apply]

theorem norm_pathHeatFlatClockPath_le (L : ℕ)
    (c : Fin L→C(I,I)) (w : Fin L→WienerPath) :
    ‖pathHeatFlatClockPath L c w‖≤∑l : Fin L,‖w l‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  exact (norm_pathHeatFlatEdgeInjection_le _ _ _).trans (norm_pathHeatClockedWienerPath_le _ _)

theorem continuous_pathHeatFlatClockPath_family {Z : Type*} [TopologicalSpace Z] (L : ℕ)
    (c : Z→Fin L→C(I,I)) (w : Z→Fin L→WienerPath)
    (hc : ∀l,Continuous (fun z=>c z l)) (hw : ∀l,Continuous (fun z=>w z l)) :
    Continuous (fun z=>pathHeatFlatClockPath L (c z) (w z)) := by
  apply continuous_finsetSum
  intro l _
  exact (pathHeatFlatEdgeInjection L l).continuous.comp ((hw l).compCM (hc l))

theorem tendsto_pathHeatFlatClockPath_family {A : Type*} {f : Filter A} (L : ℕ)
    (c : A→Fin L→C(I,I)) (w : A→Fin L→WienerPath)
    (c₀ : Fin L→C(I,I)) (w₀ : Fin L→WienerPath)
    (hc : ∀l,Tendsto (fun i=>c i l) f (𝓝 (c₀ l)))
    (hw : ∀l,Tendsto (fun i=>w i l) f (𝓝 (w₀ l))) :
    Tendsto (fun i=>pathHeatFlatClockPath L (c i) (w i)) f
      (𝓝 (pathHeatFlatClockPath L c₀ w₀)) := by
  apply tendsto_finsetSum
  intro l _
  exact (pathHeatFlatEdgeInjection L l).continuous.continuousAt.tendsto.comp ((hw l).compCM (hc l))

theorem continuous_pathHeatFlatClockPath_Wiener (L : ℕ) (c : Fin L→C(I,I)) :
    Continuous (pathHeatFlatClockPath L c) :=
  continuous_pathHeatFlatClockPath_family L (fun _=>c) id
    (fun _=>continuous_const) (fun l=>continuous_apply l)

theorem pathHeatFlatClockPath_Bernstein_actual_mesh (n L : ℕ)
    (c : Fin L→C(I,I)) (w : Fin L→WienerPath) :
    pathHeatTreeBernsteinSynthesis n L
      (WithLp.toLp 2 (fun p : Fin L × Fin (n+1)=>w p.1 (c p.1 (bernstein.z p.2))))=
        pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L c w) := by
  rw [←pathHeatTreeBernsteinSynthesis_evaluation]
  congr 1
  ext p
  change w p.1 (c p.1 (bernstein.z p.2))=pathHeatFlatClockPath L c w (p.1,bernstein.z p.2)
  rw [pathHeatFlatClockPath_apply]

theorem tendsto_pathHeatFlatClockPath_Bernstein_moving (L : ℕ)
    (c : ℕ→Fin L→C(I,I)) (c₀ : Fin L→C(I,I)) (w : Fin L→WienerPath)
    (hc : ∀l,Tendsto (fun n=>c n l) atTop (𝓝 (c₀ l))) :
    Tendsto (fun n=>pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c n) w))
      atTop (𝓝 (pathHeatFlatClockPath L c₀ w)) :=
  tendsto_pathHeatTreeBernsteinOperator_moving L _ _
    (tendsto_pathHeatFlatClockPath_family L c (fun _=>w) c₀ w hc (fun _=>tendsto_const_nhds))

end HexagonPaper
