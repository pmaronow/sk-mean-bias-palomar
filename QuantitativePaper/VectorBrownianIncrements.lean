module
public import QuantitativePaper.VectorBrownian

@[expose] public section

/-! Actual finite-grid independent vector Brownian increments. Equal times,
zero scale, and zero-dimensional fields are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper

def fieldIncrementLaw (n : ℕ) (v : ℝ≥0) : Measure (Field n) :=
  (fieldGaussian n).map (fun z => Real.sqrt (v : ℝ) • z)

instance fieldIncrementLaw_probability (n : ℕ) (v : ℝ≥0) :
    IsProbabilityMeasure (fieldIncrementLaw n v) := by
  unfold fieldIncrementLaw
  infer_instance

theorem fieldIncrementLaw_eq_pi (n : ℕ) (v : ℝ≥0) :
    fieldIncrementLaw n v =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 v)).map (WithLp.toLp 2) := by
  have hscalar : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ)*z) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun _ => fun z : ℝ => Real.sqrt (v : ℝ)*z) (fun _ => by fun_prop)
  simp only [hscalar] at hpi
  unfold fieldIncrementLaw fieldGaussian SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map (by fun_prop) (by fun_prop), ← hpi,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem hasLaw_scalarBrownian_increments (m : ℕ) (T : Fin (m+1) → ℝ≥0)
    (hT : Monotone T) (b : ℝ) :
    HasLaw (fun sample : Paper.BrownianSample => fun i : Fin m =>
      b*(Paper.canonicalBrownian (T i.succ) sample-
        Paper.canonicalBrownian (T i.castSucc) sample))
      (Measure.pi (fun i => gaussianReal 0
        (b^2*((T i.succ : ℝ)-T i.castSucc)).toNNReal))
      Paper.canonicalBrownianMeasure := by
  have hi := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasIndepIncrements
    m T hT
  have hs := hi.comp (fun _ => fun z : ℝ => b*z) (fun _ => by fun_prop)
  apply hs.hasLaw_pi
  intro i
  exact FRSB.hasLaw_scaledBrownian_increment b (T i.castSucc) (T i.succ)
    (hT (by simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ];omega))

def vectorBrownianIncrements {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ)
    (sample : VectorBrownianSample n) : Fin m → Field n :=
  fun i => b • (vectorBrownian (T i.succ) sample-vectorBrownian (T i.castSucc) sample)

theorem measurable_vectorBrownianIncrements {n m : ℕ} (T : Fin (m+1) → ℝ≥0) (b : ℝ) :
    Measurable (vectorBrownianIncrements (n := n) T b) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_vectorBrownian _).sub (measurable_vectorBrownian _)).const_smul b

theorem hasLaw_vectorBrownianIncrements {n m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (hT : Monotone T) (b : ℝ) :
    HasLaw (vectorBrownianIncrements (n := n) T b)
      (Measure.pi (fun i : Fin m =>
        fieldIncrementLaw n (b^2*((T i.succ : ℝ)-T i.castSucc)).toNNReal))
      (vectorBrownianMeasure n) := by
  let f : Paper.BrownianSample → Fin m → ℝ := fun sample i =>
    b*(Paper.canonicalBrownian (T i.succ) sample-
      Paper.canonicalBrownian (T i.castSucc) sample)
  let v : Fin m → ℝ≥0 := fun i => (b^2*((T i.succ : ℝ)-T i.castSucc)).toNNReal
  have hf : Measurable f := Measurable.of_eval fun i =>
    ((Paper.measurable_canonicalBrownian _).sub (Paper.measurable_canonicalBrownian _)).const_mul b
  have hlaw : Paper.canonicalBrownianMeasure.map f =
      Measure.pi (fun i => gaussianReal 0 (v i)) :=
    (hasLaw_scalarBrownian_increments m T hT b).map_eq
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin n => Paper.canonicalBrownianMeasure)
    (f := fun _ => f) (fun _ => hf.aemeasurable)
  simp only [hlaw] at hpi
  let tr : (Fin n → Fin m → ℝ) → (Fin m → Fin n → ℝ) := fun z i j => z j i
  have htr : Measurable tr := Measurable.of_eval fun i =>
    Measurable.of_eval fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)
  have ht := FourPapersCommon.finiteProductTranspose_map
    (fun _ : Fin n => fun i : Fin m => gaussianReal 0 (v i))
  let wrap : (Fin m → Fin n → ℝ) → (Fin m → Field n) := fun z i => WithLp.toLp 2 (z i)
  have hw : Measurable wrap := by unfold wrap;fun_prop
  have hfunc : vectorBrownianIncrements (n := n) T b =
      wrap ∘ tr ∘ (fun sample j => f (sample j)) := by
    funext sample i
    ext j
    rfl
  have hfun : Measurable (fun sample : VectorBrownianSample n => fun j => f (sample j)) :=
    Measurable.of_eval fun j => hf.comp (measurable_pi_apply j)
  refine ⟨(measurable_vectorBrownianIncrements T b).aemeasurable, ?_⟩
  rw [hfunc, ← Function.comp_assoc, ← Measure.map_map (hw.comp htr) hfun,
    ← Measure.map_map hw htr]
  change (((vectorBrownianMeasure n).map (fun sample j => f (sample j))).map tr).map wrap = _
  rw [show vectorBrownianMeasure n = Measure.pi (fun _ : Fin n => Paper.canonicalBrownianMeasure) from rfl,
    hpi,ht,Measure.pi_map_pi (fun _ => by fun_prop)]
  simp only [← fieldIncrementLaw_eq_pi]
  rfl

theorem hasLaw_disorderVectorBrownianIncrements {n m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (hT : Monotone T) (b : ℝ) :
    HasLaw (fun sample : VectorDisorderBrownianSample n =>
      (sample.1,vectorBrownianIncrements T b sample.2))
      ((completionLaw n).prod (Measure.pi (fun i : Fin m =>
        fieldIncrementLaw n (b^2*((T i.succ : ℝ)-T i.castSucc)).toNNReal)))
      (vectorDisorderBrownianMeasure n) := by
  have h := hasLaw_vectorBrownianIncrements (n := n) T hT b
  refine ⟨(measurable_fst.prodMk
    ((measurable_vectorBrownianIncrements T b).comp measurable_snd)).aemeasurable, ?_⟩
  unfold vectorDisorderBrownianMeasure
  change ((completionLaw n).prod (vectorBrownianMeasure n)).map
    (Prod.map id (vectorBrownianIncrements T b)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_vectorBrownianIncrements T b),
    Measure.map_id,h.map_eq]

end QuantitativePaper
