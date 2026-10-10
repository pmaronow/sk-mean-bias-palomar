module
public import Paper.ParisiCDFGrid

@[expose] public section

/-! Exact preservation of a coarse atomic Parisi law under nested upward rounding. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem parisiGridRound_refines (N M D : ℕ) (hD : 0 < D)
    (hMN : M+1 = D*(N+1)) (q : Paper.Overlap) :
    Paper.parisiGridRound M (Paper.parisiGridRound N q) = Paper.parisiGridRound N q := by
  apply Subtype.ext
  let i := Nat.ceil ((N+1 : ℕ)*(q : ℝ))
  have hden : (M+1 : ℝ) = (D : ℝ)*(N+1 : ℝ) := by exact_mod_cast hMN
  have hn : (N+1 : ℝ) ≠ 0 := by positivity
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  change (Nat.ceil ((M+1 : ℕ)*((i : ℝ)/(N+1 : ℕ))) : ℝ)/(M+1 : ℕ) =
    (i : ℝ)/(N+1 : ℕ)
  have he : (M+1 : ℕ)*((i : ℝ)/(N+1 : ℕ)) = ((D*i : ℕ) : ℝ) := by
    push_cast
    rw [hden]
    field_simp
  rw [he, Nat.ceil_natCast]
  push_cast
  rw [hden]
  field_simp

theorem parisiGridMeasure_refines (μ : Paper.ParisiMeasure) (N M D : ℕ) (hD : 0 < D)
    (hMN : M+1 = D*(N+1)) :
    Paper.parisiGridMeasure (Paper.parisiGridMeasure μ N) M = Paper.parisiGridMeasure μ N := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Paper.parisiGridMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (Paper.measurable_parisiGridRound M) (Paper.measurable_parisiGridRound N)]
  congr 1
  funext q
  exact parisiGridRound_refines N M D hD hMN q

end FourPapersCommon
