module
public import QuantitativePaper.VectorMeasureDisorderTilt
public import QuantitativePaper.VectorBrownianMoments

@[expose] public section

/-! Fractional tilting changes only the initial disorder law. The Wiener
factor and its independence from the complete enlarged past remain genuine
product-law consequences, for every real outer tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
variable {n : ℕ}

theorem vectorMeasureDisorderTilt_eq_prod (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) :
    vectorMeasureDisorderTilt (n := n) μ β t a =
      (vectorMeasureOuterLaw μ β t a).prod (vectorBrownianMeasure n) := by
  unfold vectorMeasureDisorderTilt vectorMeasureOuterLaw vectorDisorderBrownianMeasure
  exact (prod_withDensity_left
    (measurable_vectorMeasureOuterWeight μ β t a ht).ennreal_ofReal).symm

theorem hasLaw_vectorBrownian_samples_tilted (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) :
    HasLaw (Prod.snd : VectorDisorderBrownianSample n → VectorBrownianSample n)
      (vectorBrownianMeasure n) (vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureOuterLaw_probability (n := n) μ β t a ht
  rw [vectorMeasureDisorderTilt_eq_prod μ β t a ht]
  exact measurePreserving_snd.hasLaw

theorem vectorMeasureDisorderTilt_map_wienerFunction {A : Type*} [MeasurableSpace A]
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (f : VectorBrownianSample n → A) (hf : Measurable f) :
    (vectorMeasureDisorderTilt μ β t a).map (fun sample => f sample.2) =
      (vectorDisorderBrownianMeasure n).map (fun sample => f sample.2) := by
  change (vectorMeasureDisorderTilt μ β t a).map (f ∘ Prod.snd) =
    (vectorDisorderBrownianMeasure n).map (f ∘ Prod.snd)
  rw [← Measure.map_map hf measurable_snd, ← Measure.map_map hf measurable_snd,
    (hasLaw_vectorBrownian_samples_tilted μ β t a ht).map_eq,
    (hasLaw_vectorBrownian_samples_with_disorder n).map_eq]

theorem hasLaw_disorderVectorBrownianIncrement_tilted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) :
    HasLaw (disorderVectorBrownianIncrement (n := n) r u) (fieldIncrementLaw n (u-r))
      (vectorMeasureDisorderTilt μ β t a) := by
  refine ⟨(measurable_disorderVectorBrownianIncrement r u).aemeasurable, ?_⟩
  change (vectorMeasureDisorderTilt μ β t a).map
    (fun sample => vectorBrownian u sample.2-vectorBrownian r sample.2) = _
  rw [vectorMeasureDisorderTilt_map_wienerFunction μ β t a ht
    (fun sample : VectorBrownianSample n => vectorBrownian u sample-vectorBrownian r sample)
    ((measurable_vectorBrownian u).sub (measurable_vectorBrownian r))]
  exact (hasLaw_disorderVectorBrownianIncrement r u hru).map_eq

theorem indep_disorderVectorBrownianIncrement_past_tilted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) :
    IndepFun (disorderVectorBrownianIncrement (n := n) r u)
      (fun sample : VectorDisorderBrownianSample n =>
        fun s : Iic r => vectorBrownianRecord s sample) (vectorMeasureDisorderTilt μ β t a) := by
  let f : Fin n → Paper.BrownianSample → ℝ := fun _ sample =>
    Paper.canonicalBrownian u sample-Paper.canonicalBrownian r sample
  let g : Fin n → Paper.BrownianSample → (Iic r → ℝ) := fun _ => scalarBrownianPast r
  have hf : ∀ i, Measurable (f i) := fun _ =>
    (Paper.measurable_canonicalBrownian u).sub (Paper.measurable_canonicalBrownian r)
  have hg : ∀ i, Measurable (g i) := fun _ => measurable_scalarBrownianPast r
  have hten := FourPapersCommon.indepFun_finiteProduct
    (fun _ : Fin n => Paper.canonicalBrownianMeasure) f g hf hg
    (fun _ => indep_scalarBrownian_increment_past r u hru)
  have hfg : Measurable (fun sample : VectorBrownianSample n => fun i => f i (sample i)) :=
    Measurable.of_eval fun i => (hf i).comp (measurable_pi_apply i)
  have hgg : Measurable (fun sample : VectorBrownianSample n => fun i => g i (sample i)) :=
    Measurable.of_eval fun i => (hg i).comp (measurable_pi_apply i)
  have := vectorMeasureOuterLaw_probability (n := n) μ β t a ht
  have hadj := FourPapersCommon.indepFun_adjoin_initial (vectorBrownianMeasure n)
    (vectorMeasureOuterLaw (n := n) μ β t a) _ _ hfg hgg hten
  let wrap : (Fin n → ℝ) → Field n := WithLp.toLp 2
  let record : (Couplings n × ℝ) × (Fin n → Iic r → ℝ) → (Iic r → VectorState n) :=
    fun p s => (p.1, WithLp.toLp 2 (fun i => p.2 i s))
  have hw : Measurable wrap := by unfold wrap; fun_prop
  have hr : Measurable record := by unfold record; fun_prop
  rw [vectorMeasureDisorderTilt_eq_prod μ β t a ht]
  convert hadj.comp hw hr using 1
  · funext sample
    ext i
    rfl
  · rfl

theorem indep_disorderVectorBrownianIncrement_filtration_tilted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u) :
    Indep (MeasurableSpace.comap (disorderVectorBrownianIncrement (n := n) r u) inferInstance)
      (vectorBrownianFiltration n r) (vectorMeasureDisorderTilt μ β t a) := by
  rw [vectorBrownianFiltration, Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).mp
    (indep_disorderVectorBrownianIncrement_past_tilted μ β t a ht r u hru)

theorem indep_disorderVectorBrownianIncrement_known_tilted {A : Type*} [MeasurableSpace A]
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (Z : VectorDisorderBrownianSample n → A)
    (hZ : Measurable[vectorBrownianFiltration n r] Z) :
    IndepFun (disorderVectorBrownianIncrement (n := n) r u) Z
      (vectorMeasureDisorderTilt μ β t a) :=
  (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_right
    (indep_disorderVectorBrownianIncrement_filtration_tilted μ β t a ht r u hru) hZ.comap_le)

theorem isBrownianReal_disorderVectorBrownian_coordinate_tilted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (i : Fin n) :
    IsBrownianReal (fun r sample => disorderVectorBrownian r sample i)
      (vectorMeasureDisorderTilt μ β t a) := by
  have h := (isBrownianReal_vectorBrownian_coordinate i).toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval fun r =>
      (show Measurable (fun sample : VectorBrownianSample n =>
        Paper.canonicalBrownian r (sample i)) from
        (Paper.measurable_canonicalBrownian r).comp (measurable_pi_apply i))).aemeasurable
  refine ⟨(h.comp (hasLaw_vectorBrownian_samples_tilted μ β t a ht)).IsPreBrownianReal, ?_⟩
  exact Filter.Eventually.of_forall fun sample =>
    Paper.continuous_canonicalBrownian (sample.2 i)

theorem isFilteredPreBrownian_disorderVectorBrownian_coordinate_tilted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (i : Fin n) :
    IsFilteredPreBrownian (fun r sample => disorderVectorBrownian r sample i)
      (vectorBrownianFiltration n) (vectorMeasureDisorderTilt μ β t a) where
  hasLaw := (isBrownianReal_disorderVectorBrownian_coordinate_tilted μ β t a ht i).hasLaw
  stronglyAdapted r := by
    have hm : Measurable[vectorBrownianFiltration n r]
        (disorderVectorBrownian (n := n) r) := (stronglyAdapted_disorderVectorBrownian n r).measurable
    exact ((show Measurable (fun z : Field n => z i) from by fun_prop).comp hm).stronglyMeasurable
  indep r u hru := by
    have h := (indep_disorderVectorBrownianIncrement_past_tilted μ β t a ht r u hru).comp
      (show Measurable (fun z : Field n => z i) from by fun_prop) measurable_id
    change Indep (MeasurableSpace.comap
      (fun sample : VectorDisorderBrownianSample n =>
        disorderVectorBrownian u sample i-disorderVectorBrownian r sample i) inferInstance) _ _
    rw [vectorBrownianFiltration, Filtration.natural_eq_comap]
    exact (IndepFun_iff_Indep _ _ _).mp h

theorem martingale_disorderVectorBrownian_coordinate_tilted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (i : Fin n) :
    Martingale (fun r sample => disorderVectorBrownian r sample i)
      (vectorBrownianFiltration n) (vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  let := isFilteredPreBrownian_disorderVectorBrownian_coordinate_tilted μ β t a ht i
  exact IsPreBrownianReal.isMartingale _ _ _

end QuantitativePaper
