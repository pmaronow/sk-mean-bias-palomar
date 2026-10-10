module
public import HexagonPaper.MomentsBinTail
public import FourPapersCommon.MonotoneFiniteBins
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Actual superlevel-measure bound obtained from the finite monotone
quantile partition, with constants 128 and 128, sufficient for the manuscript's literal variance bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace HexagonPaper
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_quantile_superlevel_bound_128 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (I : Set ℝ) (hI : I.OrdConnected) (hDom : I⊆Ioc (0:ℝ) (1-s))
    (a ell u τ : ℝ) (hell : 0≤ell) (hu : 0<u) (hτ : 0<τ)
    (hRange : ∀w∈I,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+ell))
    (hThreshold : ∀ᵐw ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    volume.real {v | v∈I ∧ τ<vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)}
      ≤ min (volume.real I) (128*(1/((n:ℝ)*((1-t)*β^2)*u))/τ)+
        min (volume.real I) (128*(1/((n:ℝ)*((1-t)*β^2)*u))*ell*τ^(-(3/2:ℝ))) := by
  let f : ℝ→ℝ:=fun v=>(parisiFreeQuantile μ s v:ℝ)
  let ψ : ℝ→ℝ:=fun v=>vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)
  let ε:=1/((n:ℝ)*((1-t)*β^2)*u)
  let d:=Real.sqrt τ/2
  let N:=Nat.ceil (ell/d)+1
  let B : ℕ→Set ℝ:=monotoneFiniteBin I f a d
  let E : ℕ→Set ℝ:=fun k=>{v | v∈B k ∧ τ<ψ v}
  have hε : 0<ε:=by positivity
  have hd : 0<d:=by dsimp only [d];positivity
  have hf : Monotone f:=fun _ _ h=>parisiFreeQuantile_monotone μ s h
  have hfinI : volume I≠∞ := by
    exact (lt_of_le_of_lt (measure_mono hDom) (by rw [Real.volume_Ioc];exact ENNReal.ofReal_lt_top)).ne
  have heq : {v | v∈I ∧ τ<ψ v}=⋃k∈Finset.range N,E k := by
    ext v
    constructor
    · intro hv
      refine mem_iUnion.mpr ⟨monotoneBinIndex f a d v,mem_iUnion.mpr ⟨?_,⟨⟨hv.1,rfl⟩,hv.2⟩⟩⟩
      exact Finset.mem_range.mpr (monotoneBinIndex_lt_count f a d ell v hd (hRange v hv.1))
    · intro hv
      rcases mem_iUnion.mp hv with ⟨k,hk⟩
      rcases mem_iUnion.mp hk with ⟨_,hv⟩
      exact ⟨hv.1.1,hv.2⟩
  have hbin (k : ℕ) : volume.real (E k)≤64*ε/τ := by
    have hB:=monotoneFiniteBin_subset I f a d k
    have hT:=hThreshold.filter_mono (ae_mono (Measure.restrict_mono_set volume hB))
    have hR:=monotoneFiniteBin_level_range I f a d hd (fun v hv=>(hRange v hv).1) k
    exact vector_quantile_bin_superlevel_volume_64 hn μ s β t hβ ht hs hμ hmin (B k)
      (monotoneFiniteBin_ordConnected I hI f hf a d hd k) (hB.trans hDom)
      (a+(k:ℝ)*d) d u τ hd.le hu hτ
      (by dsimp only [d];rw [div_pow,Real.sq_sqrt hτ.le];norm_num : d^2≤τ/4) hR hT
  have hsum : volume.real {v | v∈I ∧ τ<ψ v}≤(N:ℝ)*(64*ε/τ) := by
    rw [heq]
    apply (measureReal_biUnion_finset_le (μ:=volume) (Finset.range N) E).trans
    apply le_trans (Finset.sum_le_sum (fun k _=>hbin k))
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact le_rfl
  have hcount : (N:ℝ)≤ell/d+2:=monotoneFiniteBins_count_bound d ell hd hell
  have hpow : τ^(-(3/2:ℝ))=(τ*Real.sqrt τ)⁻¹ := by
    rw [Real.rpow_neg hτ.le,show (3/2:ℝ)=1+1/2 by norm_num,
      Real.rpow_add hτ,Real.rpow_one,←Real.sqrt_eq_rpow]
  have hsum' : volume.real {v | v∈I ∧ τ<ψ v}≤128*ε/τ+128*ε*ell*τ^(-(3/2:ℝ)) := by
    apply hsum.trans
    have h:=mul_le_mul_of_nonneg_right hcount (show 0≤64*ε/τ by positivity)
    convert h using 1
    rw [hpow]
    dsimp only [d]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_div]
    ring
  have hwhole : volume.real {v | v∈I ∧ τ<ψ v}≤volume.real I:=
    measureReal_mono (fun _ h=>h.1) hfinI
  apply le_trans (le_min hwhole hsum')
  let A:=128*ε/τ
  let C:=128*ε*ell*τ^(-(3/2:ℝ))
  have hH : 0≤volume.real I:=measureReal_nonneg
  have hA : 0≤A:=by dsimp only [A];positivity
  have hC : 0≤C:=by dsimp only [C];positivity
  change min (volume.real I) (A+C)≤ min (volume.real I) A+min (volume.real I) C
  by_cases ha : volume.real I≤A
  · rw [min_eq_left ha]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hH hC))
  · by_cases hc : volume.real I≤C
    · rw [min_eq_left hc]
      exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hH hA))
    · rw [min_eq_right (not_le.mp ha).le,min_eq_right (not_le.mp hc).le]
      exact min_le_right _ _

end HexagonPaper
