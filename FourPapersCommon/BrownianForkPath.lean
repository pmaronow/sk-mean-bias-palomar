module
public import FourPapersCommon.BrownianFork

@[expose] public section

/-! The concrete fork as a random continuous path, its true Wiener law,
and continuity of the split parameter in the uniform path topology. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace FourPapersCommon

def forkBrownianPath (r : ℝ≥0) (sample : BrownianPair) : C(Icc (0 : ℝ) 1,ℝ) where
  toFun t := forkBrownian r (t : ℝ).toNNReal sample
  continuous_toFun := (continuous_forkBrownian r sample).comp
    (continuous_real_toNNReal.comp continuous_subtype_val)

theorem measurable_forkBrownianPath (r : ℝ≥0) : Measurable (forkBrownianPath r) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_forkBrownian _ _

theorem continuous_forkBrownianPath_split (sample : BrownianPair) :
    Continuous (fun r => forkBrownianPath r sample) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_forkBrownian_split_time sample).comp
    (continuous_fst.prodMk (continuous_real_toNNReal.comp
      (continuous_subtype_val.comp continuous_snd)))

theorem forkBrownianPath_law (r : ℝ≥0) :
    brownianPairMeasure.map (forkBrownianPath r) = Paper.canonicalWienerMeasure := by
  let R : (ℝ≥0 → ℝ) → (Icc (0 : ℝ) 1 → ℝ) := fun f t => f (t : ℝ).toNNReal
  have hR : Measurable R := Measurable.of_eval fun t => measurable_pi_apply _
  have hh := congrArg (fun P => P.map R) (forkBrownian_fullLaw r)
  rw [Measure.map_map hR (Measurable.of_eval (measurable_forkBrownian r)),
    Measure.map_map hR (Measurable.of_eval Paper.measurable_canonicalBrownian)] at hh
  apply continuousRealPathMeasure_ext
  rw [Measure.map_map measurable_continuousRealPath_coe (measurable_forkBrownianPath r)]
  change _ = (Paper.canonicalBrownianMeasure.map Paper.canonicalBrownianPath).map _
  rw [Measure.map_map measurable_continuousRealPath_coe Paper.measurable_canonicalBrownianPath]
  exact hh

@[simp] theorem forkBrownianPath_zero (sample : BrownianPair) :
    forkBrownianPath 0 sample = Paper.canonicalBrownianPath sample.2 := by
  ext t
  simp [forkBrownianPath, forkBrownian, Paper.canonicalBrownianPath]

theorem forkBrownianPath_before (r : ℝ≥0) (sample : BrownianPair)
    (t : Icc (0 : ℝ) 1) (ht : (t : ℝ).toNNReal ≤ r) :
    forkBrownianPath r sample t = Paper.canonicalBrownianPath sample.1 t :=
  forkBrownian_before _ _ ht sample

end FourPapersCommon
