module
public import QuantitativePaper.VectorBrownianFiltration
public import FRSB.BrownianCrossVariance

@[expose] public section

/-! Genuine first/covariance and all norm moments of the vector Wiener
increments. The constants below are actual standard Gaussian integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper

theorem hasLaw_disorderVectorBrownianIncrement {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t) :
    HasLaw (disorderVectorBrownianIncrement (n := n) r t) (fieldIncrementLaw n (t-r))
      (vectorDisorderBrownianMeasure n) := by
  let T : Fin 2 → ℝ≥0 := ![r,t]
  have hT : Monotone T := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T]
  let v : Fin 1 → ℝ≥0 := fun i => (1^2*((T i.succ : ℝ)-T i.castSucc)).toNNReal
  have hl := (hasLaw_vectorBrownianIncrements (n := n) T hT (1 : ℝ)).comp
    (hasLaw_vectorBrownian_samples_with_disorder n)
  have he := (measurePreserving_eval (fun i : Fin 1 => fieldIncrementLaw n (v i)) 0).hasLaw.comp hl
  have hdt : ((t : ℝ)-r).toNNReal = t-r := by
    ext
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr (show (r : ℝ) ≤ t from hrt)),NNReal.coe_sub hrt]
  convert he using 1
  · funext sample
    simp [Function.comp_def,vectorBrownianIncrements,T,
      disorderVectorBrownianIncrement,disorderVectorBrownian]
  · simp [v,T,hdt]

theorem hasLaw_disorderVectorBrownianIncrement_coordinate {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (i : Fin n) :
    HasLaw (fun sample => disorderVectorBrownianIncrement r t sample i)
      (gaussianReal 0 (t-r)) (vectorDisorderBrownianMeasure n) := by
  have h := (isBrownianReal_disorderVectorBrownian_coordinate i).toIsPreBrownianReal.hasLaw_sub t r
  have hv : nndist (t : ℝ) (r : ℝ) = t-r := by
    ext
    simp only [coe_nndist,Real.dist_eq,abs_of_nonneg
      (sub_nonneg.mpr (show (r : ℝ) ≤ t from hrt)),NNReal.coe_sub hrt]
  convert! h using 1
  congr 1
  exact hv.symm

theorem integral_disorderVectorBrownianIncrement_coordinate {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (i : Fin n) :
    (∫ sample,disorderVectorBrownianIncrement r t sample i
      ∂vectorDisorderBrownianMeasure n) = 0 := by
  have he := (hasLaw_disorderVectorBrownianIncrement_coordinate r t hrt i).integral_comp
    (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ) _)
  change (∫ sample,disorderVectorBrownianIncrement r t sample i
    ∂vectorDisorderBrownianMeasure n) = ∫ z : ℝ,z ∂gaussianReal 0 (t-r) at he
  rw [he,integral_id_gaussianReal]

theorem integral_square_disorderVectorBrownianIncrement_coordinate {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (i : Fin n) :
    (∫ sample,(disorderVectorBrownianIncrement r t sample i)^2
      ∂vectorDisorderBrownianMeasure n) = (t : ℝ)-r := by
  have he := (hasLaw_disorderVectorBrownianIncrement_coordinate r t hrt i).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun z : ℝ => z^2) _)
  change (∫ sample,(disorderVectorBrownianIncrement r t sample i)^2
    ∂vectorDisorderBrownianMeasure n) = ∫ z : ℝ,z^2 ∂gaussianReal 0 (t-r) at he
  rw [he,FRSB.integral_square_centered_gaussian,NNReal.coe_sub hrt]

theorem integral_cross_disorderVectorBrownianIncrement_coordinates {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (i j : Fin n) :
    (∫ sample,disorderVectorBrownianIncrement r t sample i*
      disorderVectorBrownianIncrement r t sample j ∂vectorDisorderBrownianMeasure n) =
      if i=j then (t : ℝ)-r else 0 := by
  by_cases hij : i=j
  · subst j
    simpa only [pow_two,ite_true] using integral_square_disorderVectorBrownianIncrement_coordinate r t hrt i
  · have hInd := (iIndepFun_vectorBrownian_coordinate_samples n).comp
      (fun _ => fun sample => Paper.canonicalBrownian t sample-Paper.canonicalBrownian r sample)
      (fun _ => (Paper.measurable_canonicalBrownian t).sub (Paper.measurable_canonicalBrownian r))
    have hi := hInd.indepFun hij
    have hm : ∀ l : Fin n,Measurable (fun sample : VectorBrownianSample n =>
        Paper.canonicalBrownian t (sample l)-Paper.canonicalBrownian r (sample l)) :=
      fun l => ((Paper.measurable_canonicalBrownian t).sub
        (Paper.measurable_canonicalBrownian r)).comp (measurable_pi_apply l)
    have hpair : IndepFun (fun sample : VectorDisorderBrownianSample n =>
        disorderVectorBrownianIncrement r t sample i)
        (fun sample => disorderVectorBrownianIncrement r t sample j)
        (vectorDisorderBrownianMeasure n) := by
      apply (indepFun_iff_map_prod_eq_prod_map_map
        (((show Measurable (fun z : Field n => z i) from by fun_prop).comp
          (measurable_disorderVectorBrownianIncrement r t)).aemeasurable)
        (((show Measurable (fun z : Field n => z j) from by fun_prop).comp
          (measurable_disorderVectorBrownianIncrement r t)).aemeasurable)).mpr
      change (vectorDisorderBrownianMeasure n).map
          ((fun sample : VectorBrownianSample n =>
            (Paper.canonicalBrownian t (sample i)-Paper.canonicalBrownian r (sample i),
              Paper.canonicalBrownian t (sample j)-Paper.canonicalBrownian r (sample j))) ∘ Prod.snd) = _
      rw [← Measure.map_map ((hm i).prodMk (hm j)) measurable_snd,
        (hasLaw_vectorBrownian_samples_with_disorder n).map_eq,
        hi.map_prod_eq_prod_map_map (hm i).aemeasurable (hm j).aemeasurable]
      congr 1 <;> symm
      · change (vectorDisorderBrownianMeasure n).map
          ((fun sample : VectorBrownianSample n =>
            Paper.canonicalBrownian t (sample i)-Paper.canonicalBrownian r (sample i)) ∘ Prod.snd) = _
        rw [← Measure.map_map (hm i) measurable_snd,
          (hasLaw_vectorBrownian_samples_with_disorder n).map_eq]
      · change (vectorDisorderBrownianMeasure n).map
          ((fun sample : VectorBrownianSample n =>
            Paper.canonicalBrownian t (sample j)-Paper.canonicalBrownian r (sample j)) ∘ Prod.snd) = _
        rw [← Measure.map_map (hm j) measurable_snd,
          (hasLaw_vectorBrownian_samples_with_disorder n).map_eq]
    rw [hpair.integral_fun_mul_eq_mul_integral
      ((hasLaw_disorderVectorBrownianIncrement_coordinate r t hrt i).aemeasurable.aestronglyMeasurable)
      ((hasLaw_disorderVectorBrownianIncrement_coordinate r t hrt j).aemeasurable.aestronglyMeasurable),
      integral_disorderVectorBrownianIncrement_coordinate r t hrt i,
      integral_disorderVectorBrownianIncrement_coordinate r t hrt j,ite_eq_right hij,zero_mul]

def vectorGaussianNormMoment (n p : ℕ) : ℝ := ∫ z : Field n,‖z‖^p ∂fieldGaussian n

theorem vectorGaussianNormMoment_nonneg (n p : ℕ) : 0 ≤ vectorGaussianNormMoment n p :=
  integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _

theorem integrable_vectorGaussian_norm_pow (n p : ℕ) :
    Integrable (fun z : Field n => ‖z‖^p) (fieldGaussian n) := by
  exact (IsGaussian.memLp_id (fieldGaussian n) (p : ℝ≥0∞) (by simp)).integrable_norm_pow'

theorem integrable_disorderVectorBrownianIncrement_norm_pow {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (p : ℕ) :
    Integrable (fun sample => ‖disorderVectorBrownianIncrement r t sample‖^p)
      (vectorDisorderBrownianMeasure n) := by
  change Integrable ((fun z : Field n => ‖z‖^p) ∘ disorderVectorBrownianIncrement r t) _
  apply (hasLaw_disorderVectorBrownianIncrement r t hrt).integrable_comp
  unfold fieldIncrementLaw
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow] using
    (integrable_vectorGaussian_norm_pow n p).const_mul (Real.sqrt ((t-r : ℝ≥0) : ℝ)^p)

theorem integral_disorderVectorBrownianIncrement_norm_pow {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (p : ℕ) :
    (∫ sample,‖disorderVectorBrownianIncrement r t sample‖^p ∂vectorDisorderBrownianMeasure n) =
      Real.sqrt ((t : ℝ)-r)^p*vectorGaussianNormMoment n p := by
  have he := (hasLaw_disorderVectorBrownianIncrement r t hrt).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun z : Field n => ‖z‖^p) _)
  change (∫ sample,‖disorderVectorBrownianIncrement r t sample‖^p ∂vectorDisorderBrownianMeasure n) =
    ∫ z : Field n,‖z‖^p ∂fieldIncrementLaw n (t-r) at he
  rw [he,fieldIncrementLaw,integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,NNReal.coe_sub hrt]
  rw [integral_const_mul]
  rfl

theorem integral_disorderVectorBrownianIncrement_norm_cube {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ sample,‖disorderVectorBrownianIncrement r t sample‖^3 ∂vectorDisorderBrownianMeasure n) =
      vectorGaussianNormMoment n 3*((t : ℝ)-r)*Real.sqrt ((t : ℝ)-r) := by
  rw [integral_disorderVectorBrownianIncrement_norm_pow r t hrt 3]
  have hs := Real.sq_sqrt (sub_nonneg.mpr (show (r : ℝ) ≤ t from hrt))
  calc
    _ = vectorGaussianNormMoment n 3*(Real.sqrt ((t : ℝ)-r)^2)*Real.sqrt ((t : ℝ)-r) := by ring
    _ = _ := by rw [hs]

theorem integral_disorderVectorBrownianIncrement_norm_fourth {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ sample,‖disorderVectorBrownianIncrement r t sample‖^4 ∂vectorDisorderBrownianMeasure n) =
      vectorGaussianNormMoment n 4*((t : ℝ)-r)^2 := by
  rw [integral_disorderVectorBrownianIncrement_norm_pow r t hrt 4]
  have hs := Real.sq_sqrt (sub_nonneg.mpr (show (r : ℝ) ≤ t from hrt))
  calc
    _ = vectorGaussianNormMoment n 4*(Real.sqrt ((t : ℝ)-r)^2)^2 := by ring
    _ = _ := by rw [hs]

end QuantitativePaper
