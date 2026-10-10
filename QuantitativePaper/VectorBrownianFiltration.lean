module
public import QuantitativePaper.VectorBrownianJointLaw
public import FourPapersCommon.FiniteProductIndependence

@[expose] public section

/-! Future vector increments are independent of the complete natural past,
including the independent initial completion disorder. Consequently every
coordinate is a Brownian martingale in that enlarged filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper

def scalarBrownianPast (r : ℝ≥0) (sample : Paper.BrownianSample) : Iic r → ℝ :=
  fun s => Paper.canonicalBrownian s sample

theorem measurable_scalarBrownianPast (r : ℝ≥0) : Measurable (scalarBrownianPast r) :=
  Measurable.of_eval fun s => Paper.measurable_canonicalBrownian s

theorem indep_scalarBrownian_increment_past (r t : ℝ≥0) (hrt : r ≤ t) :
    IndepFun (fun sample => Paper.canonicalBrownian t sample-Paper.canonicalBrownian r sample)
      (scalarBrownianPast r) Paper.canonicalBrownianMeasure := by
  have hF := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isFilteredPreBrownian
    Paper.measurable_canonicalBrownian
  have hP : Measurable[Paper.canonicalBrownianFiltration r] (scalarBrownianPast r) := by
    letI : MeasurableSpace Paper.BrownianSample := Paper.canonicalBrownianFiltration r
    exact Measurable.of_eval fun s =>
      ((Filtration.stronglyAdapted_natural (fun u =>
        (Paper.measurable_canonicalBrownian u).stronglyMeasurable) s).mono
          (Paper.canonicalBrownianFiltration.mono s.property)).measurable
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le_right (hF.indep r t hrt) hP.comap_le

def disorderVectorBrownianIncrement {n : ℕ} (r t : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  disorderVectorBrownian t sample-disorderVectorBrownian r sample

theorem measurable_disorderVectorBrownianIncrement {n : ℕ} (r t : ℝ≥0) :
    Measurable (disorderVectorBrownianIncrement (n := n) r t) :=
  (measurable_disorderVectorBrownian t).sub (measurable_disorderVectorBrownian r)

theorem indep_disorderVectorBrownianIncrement_past {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t) :
    IndepFun (disorderVectorBrownianIncrement (n := n) r t)
      (fun sample : VectorDisorderBrownianSample n =>
        fun s : Iic r => vectorBrownianRecord s sample) (vectorDisorderBrownianMeasure n) := by
  let f : Fin n → Paper.BrownianSample → ℝ := fun _ sample =>
    Paper.canonicalBrownian t sample-Paper.canonicalBrownian r sample
  let g : Fin n → Paper.BrownianSample → (Iic r → ℝ) := fun _ => scalarBrownianPast r
  have hf : ∀ i,Measurable (f i) := fun _ =>
    (Paper.measurable_canonicalBrownian t).sub (Paper.measurable_canonicalBrownian r)
  have hg : ∀ i,Measurable (g i) := fun _ => measurable_scalarBrownianPast r
  have hten := FourPapersCommon.indepFun_finiteProduct
    (fun _ : Fin n => Paper.canonicalBrownianMeasure) f g hf hg
    (fun _ => indep_scalarBrownian_increment_past r t hrt)
  have hfg : Measurable (fun sample : VectorBrownianSample n => fun i => f i (sample i)) :=
    Measurable.of_eval fun i => (hf i).comp (measurable_pi_apply i)
  have hgg : Measurable (fun sample : VectorBrownianSample n => fun i => g i (sample i)) :=
    Measurable.of_eval fun i => (hg i).comp (measurable_pi_apply i)
  have hadj := FourPapersCommon.indepFun_adjoin_initial (vectorBrownianMeasure n)
    (completionLaw n) _ _ hfg hgg hten
  let wrap : (Fin n → ℝ) → Field n := WithLp.toLp 2
  let record : (Couplings n × ℝ) × (Fin n → Iic r → ℝ) → (Iic r → VectorState n) :=
    fun p s => (p.1,WithLp.toLp 2 (fun i => p.2 i s))
  have hw : Measurable wrap := by unfold wrap;fun_prop
  have hr : Measurable record := by unfold record;fun_prop
  convert hadj.comp hw hr using 1
  · funext sample
    ext i
    rfl
  · rfl
  · rfl

theorem indep_disorderVectorBrownianIncrement_filtration {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t) :
    Indep (MeasurableSpace.comap (disorderVectorBrownianIncrement (n := n) r t) inferInstance)
      (vectorBrownianFiltration n r) (vectorDisorderBrownianMeasure n) := by
  rw [vectorBrownianFiltration,Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).mp (indep_disorderVectorBrownianIncrement_past r t hrt)

theorem indep_disorderVectorBrownianIncrement_known {n : ℕ} {A : Type*} [MeasurableSpace A]
    (r t : ℝ≥0) (hrt : r ≤ t) (Z : VectorDisorderBrownianSample n → A)
    (hZ : Measurable[vectorBrownianFiltration n r] Z) :
    IndepFun (disorderVectorBrownianIncrement (n := n) r t) Z
      (vectorDisorderBrownianMeasure n) :=
  (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le_right (indep_disorderVectorBrownianIncrement_filtration r t hrt) hZ.comap_le)

theorem isFilteredPreBrownian_disorderVectorBrownian_coordinate {n : ℕ} (i : Fin n) :
    IsFilteredPreBrownian (fun r sample => disorderVectorBrownian r sample i)
      (vectorBrownianFiltration n) (vectorDisorderBrownianMeasure n) where
  hasLaw := (isBrownianReal_disorderVectorBrownian_coordinate i).hasLaw
  stronglyAdapted r := by
    have hm : Measurable[vectorBrownianFiltration n r]
        (disorderVectorBrownian (n := n) r) := (stronglyAdapted_disorderVectorBrownian n r).measurable
    exact ((show Measurable (fun z : Field n => z i) from by fun_prop).comp hm).stronglyMeasurable
  indep r t hrt := by
    have h := (indep_disorderVectorBrownianIncrement_past (n := n) r t hrt).comp
      (show Measurable (fun z : Field n => z i) from by fun_prop) measurable_id
    have heq : (fun sample : VectorDisorderBrownianSample n =>
        disorderVectorBrownian t sample i-disorderVectorBrownian r sample i) =
      (fun z : Field n => z i) ∘ disorderVectorBrownianIncrement r t := rfl
    rw [show (fun r sample => disorderVectorBrownian (n := n) r sample i) t-
        (fun r sample => disorderVectorBrownian (n := n) r sample i) r =
        (fun sample => disorderVectorBrownian t sample i-disorderVectorBrownian r sample i) from rfl,
      heq,vectorBrownianFiltration,Filtration.natural_eq_comap]
    exact (IndepFun_iff_Indep _ _ _).mp h

theorem martingale_disorderVectorBrownian_coordinate {n : ℕ} (i : Fin n) :
    Martingale (fun r sample => disorderVectorBrownian r sample i)
      (vectorBrownianFiltration n) (vectorDisorderBrownianMeasure n) := by
  let := isFilteredPreBrownian_disorderVectorBrownian_coordinate i
  exact IsPreBrownianReal.isMartingale _ _ _

end QuantitativePaper
