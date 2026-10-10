module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPrintedTermwiseSecond

@[expose] public section

/-! Chapter 7: the coefficient bound for an arbitrary deterministic profile.

The source functional uses the genuine free measure and the original tree's
attachment weights.  This proof works directly with that measure; no atomic
profile or derivative identity is assumed.  The original-pair contribution is
bounded by `k²` (its exact value is `k(k-1)`).  The other five contributions
retain their actual nonnegative Stieltjes coefficients.
-/
noncomputable section
open Set MeasureTheory
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {J : ℕ}

theorem cavity_origin_weight_nonneg
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (hs : s ≤ Paper.parisiCDF μ (q j))
    (Φ : NativeStreamingOrigin T → ℝ) (hΦ : ∀o, 0 ≤ Φ o) :
    0 ≤ nativeStreamingOriginWeightIntegral μ a q T s Φ := by
  induction T generalizing s with
  | leaf =>
      change 0 ≤ (1-s)*Φ (.vertex (.root .leaf))
      exact mul_nonneg (sub_nonneg.mpr (hs.trans (Paper.parisiCDF_le_one μ _))) (hΦ _)
  | @advance j T ih =>
      change 0 ≤ nativeStreamingOriginWeightIntegral μ a q T
        (Paper.parisiCDF μ (q j)) (fun o=>Φ (nativeStreamingOriginChild o)) +
        (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-s)*Φ (.vertex (.root T.advance))
      exact add_nonneg
        (add_nonneg (ih _ le_rfl _ (fun o=>hΦ _)) (integral_nonneg (fun r=>hΦ _)))
        (mul_nonneg (sub_nonneg.mpr hs) (hΦ _))
  | @fork j T U ihT ihU =>
      change 0 ≤ nativeStreamingOriginWeightIntegral μ a q T
        (Paper.parisiCDF μ (q j)) (fun o=>Φ (nativeStreamingOriginLeft o)) +
        nativeStreamingOriginWeightIntegral μ a q U
        (Paper.parisiCDF μ (q j)) (fun o=>Φ (nativeStreamingOriginRight o)) +
        (2*Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root (.fork T U)))
      have hc : 0 ≤ 2*Paper.parisiCDF μ (q j)-s := by
        linarith [Paper.parisiCDF_nonneg μ (q j)]
      exact add_nonneg
        (add_nonneg (ihT _ le_rfl _ (fun o=>hΦ _)) (ihU _ le_rfl _ (fun o=>hΦ _)))
        (mul_nonneg hc (hΦ _))

def cavity_source_coefficient_envelope
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : ℝ :=
  let k : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let W := nativeStreamingOriginWeightIntegral μ a q T a (fun _=>1)
  k^2 + 2*k*W + W^2 +
    nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)) +
    nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>∫r, if nativeStreamingOriginLevel q o<r then (1:ℝ) else 0
        ∂parisiFreeMeasure μ a) +
    a*(parisiFreeMeasure μ a).real univ

theorem cavity_source_coefficient_envelope_nonneg_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) :
    0 ≤ cavity_source_coefficient_envelope μ a q T ∧
    cavity_source_coefficient_envelope μ a q T ≤
      4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2 +
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1 := by
  let k : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let W := nativeStreamingOriginWeightIntegral μ a q T a (fun _=>1)
  let ν := parisiFreeMeasure μ a
  have ha0 : 0≤a := ha.1
  have hroot : a ≤ Paper.parisiCDF μ (q J) :=
    scalarFloor_cdf_lower hμ (q J).property.1
  have hW : W=k-a := by
    simpa only [W,k,mul_one] using nativeStreamingOriginWeightIntegral_const μ a ha hμ q hq T a 1
  have hW0 : 0≤W := cavity_origin_weight_nonneg μ a q T a hroot _ (fun _=>by norm_num)
  have hk0 : 0≤k := Nat.cast_nonneg _
  have hWk : W≤k := by linarith [ha.1]
  have hmass : ν.real univ=1-a := by
    dsimp only [ν,Measure.real]
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  have hm0 : 0≤ν.real univ := by rw [hmass]; linarith [ha.2]
  have hm1 : ν.real univ≤1 := by rw [hmass]; linarith [ha.1]
  have hc0 : 0≤nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)) :=
    cavity_origin_weight_nonneg μ a q T a hroot _ (fun _=>Paper.parisiCDF_nonneg _ _)
  have hc : nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)) ≤ W := by
    apply (le_abs_self _).trans
    simpa only [hW,one_mul] using nativeStreamingOriginWeightIntegral_abs_le μ a ha hμ
      q hq T a hroot 1 (by norm_num) _ (fun o=>by
        rw [abs_of_nonneg (Paper.parisiCDF_nonneg _ _)]
        exact Paper.parisiCDF_le_one _ _)
  have hf (o : NativeStreamingOrigin T) :
      0 ≤ (∫r, if nativeStreamingOriginLevel q o<r then (1:ℝ) else 0 ∂ν) ∧
      |∫r, if nativeStreamingOriginLevel q o<r then (1:ℝ) else 0 ∂ν| ≤ 1 := by
    refine ⟨integral_nonneg (fun _=>by split_ifs <;> norm_num),?_⟩
    have H := norm_integral_le_of_norm_le_const (μ:=ν) (C:=1)
      (f:=fun r=>if nativeStreamingOriginLevel q o<r then (1:ℝ) else 0)
      (.of_forall fun _=>by split_ifs <;> norm_num)
    simpa only [Real.norm_eq_abs,one_mul] using H.trans (by simpa only [one_mul] using hm1)
  have hf0 : 0≤nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>∫r, if nativeStreamingOriginLevel q o<r then (1:ℝ) else 0 ∂ν) :=
    cavity_origin_weight_nonneg μ a q T a hroot _ (fun o=>(hf o).1)
  have hfW : nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>∫r, if nativeStreamingOriginLevel q o<r then (1:ℝ) else 0 ∂ν) ≤ W := by
    apply (le_abs_self _).trans
    simpa only [hW,one_mul] using nativeStreamingOriginWeightIntegral_abs_le μ a ha hμ
      q hq T a hroot 1 (by norm_num) _ (fun o=>(hf o).2)
  change 0≤k^2+2*k*W+W^2+_+_+a*ν.real univ ∧
    k^2+2*k*W+W^2+_+_+a*ν.real univ≤4*k^2+2*k+1
  constructor
  · positivity
  · have hkw : 2*k*W≤2*k^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hWk hk0]
    have hww : W^2≤k^2 := (sq_le_sq₀ hW0 hk0).mpr hWk
    have hr : a*ν.real univ≤1 := by nlinarith [ha.1,ha.2]
    nlinarith

end HexagonPaper
