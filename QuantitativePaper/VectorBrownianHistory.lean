module
public import QuantitativePaper.VectorBrownianIncrements
public import QuantitativePaper.VectorHistoryProperties

@[expose] public section

/-! The constructed continuous vector Brownian path has exactly the finite
Gaussian transition-history law. The initial completion disorder is retained
through every state. Grid nodes need only be nondecreasing. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
open FourPapersCommon SpinGlass SpinGlass.Targets

def brownianGridVariance {m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) (i : Fin m) : ℝ :=
  b^2*((T i.succ : ℝ)-T i.castSucc)

theorem brownianGridVariance_nonneg {m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (hT : Monotone T) (b : ℝ) (i : Fin m) : 0 ≤ brownianGridVariance T b i := by
  apply mul_nonneg (sq_nonneg b)
  apply sub_nonneg.mpr
  exact_mod_cast hT (by simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ];omega)

def brownianGridUpdate {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) (i : ℕ)
    (p : VectorState n) (z : Field n) : VectorState n :=
  if hi : i < m then vectorStateUpdate (brownianGridVariance T b ⟨i,hi⟩) (p,z) else p

theorem measurable_brownianGridUpdate {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) (i : ℕ) :
    Measurable (Function.uncurry (brownianGridUpdate (n := n) T b i)) := by
  unfold brownianGridUpdate
  split_ifs
  · exact measurable_vectorStateUpdate _
  · exact measurable_fst

def brownianGridKernel {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) (i : ℕ) :
    Kernel (VectorState n) (VectorState n) :=
  if hi : i < m then vectorGaussianStateKernel (brownianGridVariance T b ⟨i,hi⟩)
    else Kernel.id

instance brownianGridKernel_markov {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) (i : ℕ) :
    IsMarkovKernel (brownianGridKernel (n := n) T b i) := by
  unfold brownianGridKernel
  split_ifs <;> infer_instance

theorem brownianGridKernel_eq_update {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ)
    (i : ℕ) (p : VectorState n) :
    brownianGridKernel T b i p = (fieldGaussian n).map (brownianGridUpdate T b i p) := by
  unfold brownianGridKernel brownianGridUpdate
  split_ifs
  · rw [vectorGaussianStateKernel_apply]
    rfl
  · simp [Kernel.id_apply]

def brownianGaussianGridHistory {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ)
    (p : (Couplings n × ℝ) × (Fin m → Field n)) : FiniteHistory (VectorState n) m :=
  independentHistory (brownianGridUpdate T b) m ((p.1,0),p.2)

theorem measurable_brownianGaussianGridHistory {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) :
    Measurable (brownianGaussianGridHistory (n := n) T b) :=
  (measurable_independentHistory _ (measurable_brownianGridUpdate T b) _).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem brownianGaussianGridHistory_map {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) :
    ((completionLaw n).prod (Measure.pi (fun _ : Fin m => fieldGaussian n))).map
        (brownianGaussianGridHistory T b) =
      finiteHistoryLaw (vectorBaseInitialLaw n) (brownianGridKernel T b) m := by
  have h := independentHistory_law (vectorBaseInitialLaw n) (fieldGaussian n)
    (brownianGridUpdate T b) (measurable_brownianGridUpdate T b) (brownianGridKernel T b)
    (fun _ => inferInstance) (brownianGridKernel_eq_update T b) m
  have he : (vectorBaseInitialLaw n).prod (Measure.pi (fun _ : Fin m => fieldGaussian n)) =
      ((completionLaw n).prod (Measure.pi (fun _ : Fin m => fieldGaussian n))).map
        (fun p => ((p.1,0),p.2)) := by
    unfold vectorBaseInitialLaw
    conv_lhs => rhs;rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => fieldGaussian n))]
    rw [Measure.map_prod_map _ _ (by fun_prop) measurable_id]
    rfl
  rw [he,Measure.map_map (measurable_independentHistory _ (measurable_brownianGridUpdate T b) _)
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)] at h
  exact h

def additiveGridHistory {n m : ℕ} (p : (Couplings n × ℝ) × (Fin m → Field n)) :
    FiniteHistory (VectorState n) m :=
  independentHistory (fun _ x z => (x.1,x.2+z)) m ((p.1,0),p.2)

theorem measurable_additiveGridHistory (n m : ℕ) :
    Measurable (additiveGridHistory (n := n) (m := m)) := by
  exact (measurable_independentHistory _ (fun _ => by fun_prop) _).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

def brownianGaussianGridIncrements {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ)
    (z : Fin m → Field n) : Fin m → Field n :=
  fun i => Real.sqrt (brownianGridVariance T b i) • z i

theorem measurable_brownianGaussianGridIncrements {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) :
    Measurable (brownianGaussianGridIncrements (n := n) T b) := by
  unfold brownianGaussianGridIncrements
  fun_prop

theorem brownianGaussianGridIncrements_map {n m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (hT : Monotone T) (b : ℝ) :
    (Measure.pi (fun _ : Fin m => fieldGaussian n)).map (brownianGaussianGridIncrements T b) =
      Measure.pi (fun i => fieldIncrementLaw n (brownianGridVariance T b i).toNNReal) := by
  unfold brownianGaussianGridIncrements
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  congr 1
  funext i
  unfold fieldIncrementLaw
  rw [Real.coe_toNNReal _ (brownianGridVariance_nonneg T hT b i)]

theorem brownianGaussianGridHistory_eq_additive {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ)
    (p : (Couplings n × ℝ) × (Fin m → Field n)) :
    brownianGaussianGridHistory T b p =
      additiveGridHistory (p.1,brownianGaussianGridIncrements T b p.2) := by
  funext i
  induction i using Fin.induction with
  | zero =>
    simp only [brownianGaussianGridHistory,additiveGridHistory,independentHistory_initial]
  | succ i ih =>
    rw [brownianGaussianGridHistory,independentHistory_next,
      additiveGridHistory,independentHistory_next]
    change brownianGridUpdate T b i (brownianGaussianGridHistory T b p i.castSucc) (p.2 i) = _
    rw [ih]
    simp only [brownianGridUpdate,dite_eq_left i.isLt,vectorStateUpdate,fieldShift,
      brownianGaussianGridIncrements]
    rfl

def scaledDisorderBrownianHistory {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (VectorState n) m :=
  fun i => (sample.1,b • disorderVectorBrownian (T i) sample)

theorem measurable_scaledDisorderBrownianHistory {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) :
    Measurable (scaledDisorderBrownianHistory (n := n) T b) :=
  Measurable.of_eval fun i => measurable_fst.prodMk
    ((measurable_disorderVectorBrownian _).const_smul b)

theorem scaledDisorderBrownianHistory_eq_additive {n m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (hT0 : T 0 = 0) (b : ℝ) (sample : VectorDisorderBrownianSample n) :
    scaledDisorderBrownianHistory T b sample =
      additiveGridHistory (sample.1,vectorBrownianIncrements T b sample.2) := by
  funext i
  induction i using Fin.induction with
  | zero =>
    rw [additiveGridHistory,independentHistory_initial]
    simp [scaledDisorderBrownianHistory,disorderVectorBrownian,hT0]
  | succ i ih =>
    rw [additiveGridHistory,independentHistory_next]
    change scaledDisorderBrownianHistory T b sample i.succ =
      ((additiveGridHistory (sample.1,vectorBrownianIncrements T b sample.2) i.castSucc).1,
       (additiveGridHistory (sample.1,vectorBrownianIncrements T b sample.2) i.castSucc).2+
       vectorBrownianIncrements T b sample.2 i)
    rw [← ih]
    apply Prod.ext
    · rfl
    · change b • vectorBrownian (T i.succ) sample.2 =
        b • vectorBrownian (T i.castSucc) sample.2+
        b • (vectorBrownian (T i.succ) sample.2-vectorBrownian (T i.castSucc) sample.2)
      simp [smul_sub]

theorem scaledDisorderBrownianHistory_map {n m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (hT : Monotone T) (hT0 : T 0 = 0) (b : ℝ) :
    (vectorDisorderBrownianMeasure n).map (scaledDisorderBrownianHistory T b) =
      finiteHistoryLaw (vectorBaseInitialLaw n) (brownianGridKernel T b) m := by
  let C : (Couplings n × ℝ) × (Fin m → Field n) →
      (Couplings n × ℝ) × (Fin m → Field n) :=
    Prod.map id (brownianGaussianGridIncrements T b)
  have hC : Measurable C := measurable_id.prodMap (measurable_brownianGaussianGridIncrements T b)
  have hcmap : ((completionLaw n).prod (Measure.pi (fun _ : Fin m => fieldGaussian n))).map C =
      (completionLaw n).prod (Measure.pi (fun i =>
        fieldIncrementLaw n (brownianGridVariance T b i).toNNReal)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_brownianGaussianGridIncrements T b),
      Measure.map_id,brownianGaussianGridIncrements_map T hT b]
  have hfunc : scaledDisorderBrownianHistory (n := n) T b =
      additiveGridHistory ∘ (fun sample : VectorDisorderBrownianSample n =>
        (sample.1,vectorBrownianIncrements T b sample.2)) :=
    funext (scaledDisorderBrownianHistory_eq_additive T hT0 b)
  have hcoord : brownianGaussianGridHistory (n := n) T b = additiveGridHistory ∘ C :=
    funext (brownianGaussianGridHistory_eq_additive T b)
  have hrec : Measurable (fun sample : VectorDisorderBrownianSample n =>
      (sample.1,vectorBrownianIncrements T b sample.2)) :=
    measurable_fst.prodMk ((measurable_vectorBrownianIncrements T b).comp measurable_snd)
  rw [hfunc,← Measure.map_map (measurable_additiveGridHistory n m)
    hrec,
    (hasLaw_disorderVectorBrownianIncrements T hT b).map_eq]
  change ((completionLaw n).prod (Measure.pi (fun i =>
    fieldIncrementLaw n (brownianGridVariance T b i).toNNReal))).map additiveGridHistory = _
  rw [← hcmap,Measure.map_map (measurable_additiveGridHistory n m) hC,← hcoord,
    brownianGaussianGridHistory_map]

end QuantitativePaper
