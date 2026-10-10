module
public import QuantitativePaper.VectorProfileGridCurvatureIdentification
public import QuantitativePaper.VectorProfileC1Response
public import QuantitativePaper.ResponseC1PhysicalIntegrals
public import QuantitativePaper.ResponseSchemeIntegrals

@[expose] public section

/-! Exact time and Stieltjes integral forms of the true finite tent signal
and denominator for the actual common-grid probability-measure mixture. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n : ℕ}

theorem vectorProfile_grid_C1_signal_eq (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam θ : ℝ) (w : ResponseC1Test) (ht : t<1) (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileC1Signal (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t (lam/β) θ ht.le hθ w=
      (n:ℝ)*(∫q in (0:ℝ)..1,
        β*(Paper.parisiCDF (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q-
          Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q)*w.value q*
        responseAveragedCurvatureReal (n:=n)
          (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t lam ht.le q):=by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
  let g:=fun q=>β*(Paper.parisiCDF (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) q-
    Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q)*w.value q*
      responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q
  have hi (a b : ℝ) : IntervalIntegrable g volume a b:=
    intervalIntegrable_response_C1_signal _ _ ρ β t lam w a b ht
  have he (i : ℕ) (hin : i∈Finset.range (vectorDyadicIndex j+3)) :
      (∫q in (s₀.q i)..(s₀.q (i+1)),β*(s₁.m i-s₀.m i)*w.value q*
        vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
          (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q)=
      (n:ℝ)*(∫q in (s₀.q i)..(s₀.q (i+1)),g q):=by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (s₀.q_mono i (by have:=Finset.mem_range.mp hin;omega))]
    intro q hq
    have hin' : i≤vectorDyadicIndex j+2:=by have:=Finset.mem_range.mp hin;omega
    have hq01 : q∈Icc (0:ℝ) 1:=⟨(s₀.q_nonneg (by omega)).trans hq.1.le,
      hq.2.le.trans (s₀.q_le_one (by omega))⟩
    have hE := vectorProfile_grid_retained_curvature_expected hn μ ν j β t lam θ ht.le hθ i hin'
      ⟨q,hq01⟩ ⟨hq.1.le,hq.2.le⟩
    have hE' : vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
        (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q=
        (n:ℝ)*responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q:=by
      simpa only [s₀,s₁,ρ,responseAveragedCurvatureReal,projIcc_of_mem zero_le_one hq01] using hE
    dsimp only [g]
    rw [hE',←FRSB.parisiSchemeMeasure_grid_eq μ (vectorDyadicIndex j),
      ←FRSB.parisiSchemeMeasure_grid_eq ν (vectorDyadicIndex j),
      Paper.parisiCDF_scheme_cell s₀ hin' ⟨hq.1.le,hq.2⟩,
      Paper.parisiCDF_scheme_cell s₁ hin' ⟨hq.1.le,hq.2⟩]
    ring
  unfold vectorProfileC1Signal
  change (∑i∈Finset.range (vectorDyadicIndex j+3),_)=(n:ℝ)*(∫q in (0:ℝ)..1,g q)
  rw [Finset.sum_congr rfl he,←Finset.mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals (a:=s₀.q) (n:=vectorDyadicIndex j+3)
      (fun i _=>hi _ _),s₀.q_zero,s₀.q_top]

end QuantitativePaper
