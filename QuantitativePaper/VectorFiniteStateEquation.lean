module
public import QuantitativePaper.VectorFiniteState

@[expose] public section

/-! The constructed finite-profile diffusion satisfies the literal gradient
integral equation on every physical path. This is independent of any
identification with a separately tilted path law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n k : ℕ}

theorem vectorFiniteState_decomposition (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorFiniteState s β t ht r sample =
      vectorIntegratedDrift (fun q=>vectorAdditiveDrift (vectorFiniteDriftData s β t ht)
        (Real.sqrt ((1-t)*β^2)) 0 1 q sample) r+
      Real.sqrt ((1-t)*β^2) • disorderVectorBrownian r sample := by
  simpa only [vectorFiniteState,zero_add] using vectorAdditiveState_decomposition
    (vectorFiniteDriftData s β t ht) (Real.sqrt ((1-t)*β^2)) (0 : Field n) 1 r sample

theorem vectorFiniteState_integral_equation (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (r : ℝ≥0) (hr : r ≤ 1) (sample : VectorDisorderBrownianSample n) :
    vectorFiniteState s β t ht r sample = Real.sqrt ((1-t)*β^2) • disorderVectorBrownian r sample+
      ∫ q in (0 : ℝ)..(r : ℝ),
        ((1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q) •
          gradient (vectorTailRecursion s β t q sample.1 (k+2))
            (vectorFiniteState s β t ht q.toNNReal sample) := by
  have he := vectorAdditiveState_equation (vectorFiniteDriftData s β t ht)
    (Real.sqrt ((1-t)*β^2)) (0 : Field n) 1 r hr sample
  simp only [zero_add] at he
  change vectorFiniteState s β t ht r sample = Real.sqrt ((1-t)*β^2) • disorderVectorBrownian r sample+
    ∫ q in (0 : ℝ)..(r : ℝ),vectorFiniteDrift s β t q.toNNReal sample.1
      (vectorFiniteState s β t ht q.toNNReal sample) at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro q hq
  rw [uIcc_of_le r.coe_nonneg] at hq
  have hqm : ((q.toNNReal : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 := by
    rw [Real.coe_toNNReal q hq.1]
    exact ⟨hq.1,hq.2.trans (show (r : ℝ) ≤ 1 from hr)⟩
  have hq1 : q ∈ Icc (0 : ℝ) 1 :=
    ⟨hq.1,hq.2.trans (show (r : ℝ) ≤ 1 from hr)⟩
  simp only [vectorFiniteDrift,vectorFiniteTailGradient,Real.coe_toNNReal q hq.1]
  rw [projIcc_of_mem _ hq1]

end QuantitativePaper
