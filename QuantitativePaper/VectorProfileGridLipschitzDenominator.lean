module
public import QuantitativePaper.VectorProfileGridLipschitzPairing

@[expose] public section

/-! Exact Stieltjes form of the finite Xi denominator. Atoms, repeated
nodes, and both compulsory endpoint coefficients are retained literally. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n : ℕ}

theorem vectorProfile_grid_Lipschitz_denominator_eq (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam θ : ℝ) (w : ResponseLipschitzTest) (ht : t<1) (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileLipschitzDenominator (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t (lam/β) θ ht.le hθ w=
      (n:ℝ)*((∫q in (0:ℝ)..1,(w.slope q)^2*
        responseMeanHessianReal (n:=n)
          (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t lam ht.le q)+
        2*(1-t)*β*(∫q : Paper.Overlap,(w.value q)^2*
          responseAveragedCurvature (n:=n)
            (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t lam ht.le q
          ∂(Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j) : Measure Paper.Overlap))):=by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let S:=vectorProfileScheme s₀ s₁ θ hθ
  let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
  let g:=fun q=>(w.slope q)^2*responseMeanHessianReal (n:=n) ρ β t lam ht.le q
  have hi (a b : ℝ) : IntervalIntegrable g volume a b:=
    intervalIntegrable_response_Lipschitz_mean ρ β t lam w a b ht.le
  have he (i : ℕ) (hin : i∈Finset.range (vectorDyadicIndex j+3)) :
      (∫q in (s₀.q i)..(s₀.q (i+1)),(w.slope q)^2*
        vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
          (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q)=
      (n:ℝ)*(∫q in (s₀.q i)..(s₀.q (i+1)),g q):=by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (s₀.q_mono i (by have:=Finset.mem_range.mp hin;omega))]
    intro q hq
    have hin' : i≤vectorDyadicIndex j+2:=by have:=Finset.mem_range.mp hin;omega
    have hq01 : q∈Icc (0:ℝ) 1:=⟨(s₀.q_nonneg (by omega)).trans hq.1.le,
      hq.2.le.trans (s₀.q_le_one (by omega))⟩
    have hE := vectorProfile_grid_retained_physical_trace_expected hn μ ν j β t lam θ ht.le hθ i hin'
      ⟨q,hq01⟩ ⟨hq.1.le,hq.2.le⟩
    have hE' : vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
        (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q=
        (n:ℝ)*responseMeanHessianReal (n:=n) ρ β t lam ht.le q:=by
      simpa only [s₀,s₁,ρ,responseMeanHessianReal,projIcc_of_mem zero_le_one hq01] using hE
    dsimp only [g]
    rw [hE']
    ring
  have htime : (∑i∈Finset.range (vectorDyadicIndex j+3),
      ∫q in (s₀.q i)..(s₀.q (i+1)),(w.slope q)^2*
        vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
          (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q)=
      (n:ℝ)*(∫q in (0:ℝ)..1,g q):=by
    rw [Finset.sum_congr rfl he,←Finset.mul_sum,
      intervalIntegral.sum_integral_adjacent_intervals (a:=s₀.q) (n:=vectorDyadicIndex j+3)
        (fun i _=>hi _ _),s₀.q_zero,s₀.q_top]
  have hatom : (∑i∈Finset.range (vectorDyadicIndex j+2),
      (vectorProfileMass s₀ s₁ θ (i+1)-vectorProfileMass s₀ s₁ θ i)*
        (w.value (s₀.q (i+1)))^2*
        vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
          (vectorProfileRetainedTraceSquare s₀ s₁ β t i) (s₀.q (i+1)))=
      (n:ℝ)*(∫q : Paper.Overlap,(w.value q)^2*
        responseAveragedCurvature (n:=n) ρ β t lam ht.le q ∂(ρ : Measure Paper.Overlap)):=by
    have hρ : ρ=Paper.parisiSchemeMeasure S:=by
      dsimp only [ρ,S,s₀,s₁]
      rw [vector_grid_profile_scheme_eq_mix,FRSB.parisiSchemeMeasure_grid_eq]
    rw [hρ,response_integral_scheme]
    rw [←hρ]
    have hA (i : Fin (vectorDyadicIndex j+2)) :
        (w.value (Paper.parisiSchemeAtom S i))^2*
          responseAveragedCurvature (n:=n) ρ β t lam ht.le (Paper.parisiSchemeAtom S i)=
        (w.value (s₀.q (i+1)))^2*
          responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le (s₀.q (i+1)):=by
      have hq01 : s₀.q (i+1)∈Icc (0:ℝ) 1:=
        ⟨s₀.q_nonneg (by omega),s₀.q_le_one (by omega)⟩
      simp only [responseAveragedCurvatureReal,projIcc_of_mem zero_le_one hq01]
      rfl
    simp_rw [hA]
    rw [Fin.sum_univ_eq_sum_range (fun i=>(S.m (i+1)-S.m i)*
      ((w.value (s₀.q (i+1)))^2*
        responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le (s₀.q (i+1))))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hin
    have hin' : i<vectorDyadicIndex j+2:=Finset.mem_range.mp hin
    have hE := vectorProfile_grid_retained_curvature_expected hn μ ν j β t lam θ ht.le hθ i (by omega)
      (Paper.parisiSchemeAtom S ⟨i,hin'⟩) ⟨s₀.q_mono i (by omega),le_rfl⟩
    have hE' : vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
        (vectorProfileRetainedTraceSquare s₀ s₁ β t i) (s₀.q (i+1))=
        (n:ℝ)*responseAveragedCurvature (n:=n) ρ β t lam ht.le
          (Paper.parisiSchemeAtom S ⟨i,hin'⟩):=hE
    have hE'' : vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t (lam/β) θ ht.le hθ
        (vectorProfileRetainedTraceSquare s₀ s₁ β t i) (s₀.q (i+1))=
        (n:ℝ)*responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le (s₀.q (i+1)):=by
      have hq01 : s₀.q (i+1)∈Icc (0:ℝ) 1:=
        ⟨s₀.q_nonneg (by omega),s₀.q_le_one (by omega)⟩
      rw [hE']
      simp only [responseAveragedCurvatureReal,projIcc_of_mem zero_le_one hq01]
      rfl
    rw [hE'']
    change (S.m (i+1)-S.m i)*(w.value (s₀.q (i+1)))^2*
        ((n:ℝ)*responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le (s₀.q (i+1)))=
      (n:ℝ)*((S.m (i+1)-S.m i)*((w.value (s₀.q (i+1)))^2*
        responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le (s₀.q (i+1))))
    ring
  unfold vectorProfileLipschitzDenominator
  change _=(n:ℝ)*((∫q in (0:ℝ)..1,g q)+2*(1-t)*β*(∫q : Paper.Overlap,
    (w.value q)^2*responseAveragedCurvature (n:=n) ρ β t lam ht.le q ∂(ρ : Measure Paper.Overlap)))
  rw [htime,hatom]
  ring

end QuantitativePaper
