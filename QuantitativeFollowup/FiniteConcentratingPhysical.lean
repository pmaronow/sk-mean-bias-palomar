module
public import QuantitativeFollowup.FiniteConcentratingDensity
public import QuantitativeFollowup.ConcentratingPhysicalBounds
public import FourPapersCommon.SquaredResponseEnvelope
public import QuantitativePaper.ResponseCurvatureLower
public import QuantitativePaper.ResponseTentPhysicalSignalBounds

@[expose] public section

/-! Actual finite-family response envelopes. The curvature, signal and
Stieltjes-density estimates refer to the genuine tilted diffusion. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 3000000

def finiteResponseDelta (μ : Paper.ParisiMeasure) (beta t lam : ℝ) (ht : t≤1)
    (S : Finset ℕ) (a : ℕ→ℝ) (ell : ℝ) : ℝ :=
  (1-t)*(∫x in (0 : ℝ)..1,responseAveragedCurvatureReal (n:=n) μ beta t lam ht x*
    finiteConcentratingBump S a ell x)

theorem finiteResponseDelta_lower (hn : 0<n) (μ : Paper.ParisiMeasure)
    (beta t lam : ℝ) (hbeta : 1≤beta) (ht : t∈Ico (0 : ℝ) 1)
    (hlam : 0≤lam) (hfloor : lam≤beta*parisiCDF μ 0)
    (S : Finset ℕ) (a : ℕ→ℝ) (ell : ℝ) (hell : 0<ell)
    (ha : ∀i∈S,0≤a i) (he : ∀i∈S,a i+ell≤1) :
    (1-t)*(responseCurvatureConstant beta)^2*(S.card : ℝ)*ell/2 ≤
      finiteResponseDelta (n:=n) μ beta t lam ht.2.le S a ell := by
  have hLower := finiteConcentrating_weighted_mass_lower S a ell hell ha he
    (responseAveragedCurvatureReal (n:=n) μ beta t lam ht.2.le)
    (continuous_responseAveragedCurvatureReal μ beta t lam ht.2)
    ((responseCurvatureConstant beta)^2) (sq_nonneg _) (by
      intro x hx
      simpa only [responseAveragedCurvatureReal,projIcc_of_mem zero_le_one hx] using
        responseAveragedCurvature_lower hn μ beta t lam beta hbeta ht hlam hfloor
          ⟨x,hx⟩ (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left
            (parisiCDF_le_one μ x) (zero_le_one.trans hbeta))))
  have hh := mul_le_mul_of_nonneg_left hLower (sub_nonneg.mpr ht.2.le)
  convert hh using 1
  · ring
  · rfl

theorem finite_concentrating_response_denominator_bound (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (beta t lam theta q d : ℝ)
    (hbeta : 0<beta) (ht : t<1) (hd : 0≤d)
    (S : Finset ℕ) (a : ℕ→ℝ) (ell : ℝ) (hell : 0<ell)
    (ha : ∀i∈S,0≤a i) (he : ∀i∈S,a i+ell≤1)
    (hdisj : (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell)))
    (hdensity : (ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix μ ν theta)).measure).restrict
      ({(0 : ℝ),q}ᶜ) ≤ ENNReal.ofReal d • volume)
    (hzero : finiteConcentratingBump S a ell q=0) :
    responseC1EnergyDenominator (n:=n) μ ν beta t lam theta ht.le
      (finiteConcentratingResponseTest S a ell hell ha he) ≤
        beta*(S.card : ℝ)*512/(105*ell)+2*d*
          finiteResponseDelta (n:=n) (parisiMix μ ν theta) beta t lam ht.le S a ell := by
  let ρ := parisiMix μ ν theta
  let w := finiteConcentratingResponseTest S a ell hell ha he
  let D := responseAveragedCurvatureReal (n:=n) ρ beta t lam ht.le
  have hY : (∫x in (0 : ℝ)..1,(w.slope x)^2*responseMeanHessianReal (n:=n) ρ beta t lam ht.le x) ≤
      beta*(S.card : ℝ)*512/(105*ell) := by
    have hh := intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_response_C1_mean ρ beta t lam w 0 1 ht.le)
      ((w.continuous_slope.pow 2).intervalIntegrable (μ:=volume) 0 1 |>.const_mul beta) (by
        intro x _
        have hb := mul_le_mul_of_nonneg_left
          (responseMeanHessian_le_beta hn ρ beta t lam hbeta ht (projIcc 0 1 zero_le_one x)) (sq_nonneg (w.slope x))
        simpa only [responseMeanHessianReal,Pi.pow_apply,mul_comm beta] using hb)
    rw [intervalIntegral.integral_const_mul] at hh
    simp only [Pi.pow_apply,w,finiteConcentratingResponseTest] at hh
    rw [finiteConcentratingSlope_unit_energy S a ell hell ha he hdisj] at hh
    convert hh using 1 <;> (try dsimp only [w,finiteConcentratingResponseTest]) <;> ring
  have hZ := finiteConcentrating_density_square_bound_on S a ell hell ha he hdisj D
    (continuous_responseAveragedCurvatureReal ρ beta t lam ht)
    (fun x=>responseAveragedCurvature_nonneg ρ beta t lam ht.le _)
    (ENNReal.ofReal beta • (parisiCDFPrimitive ρ).measure) ({(0 : ℝ),q}ᶜ) d hd hdensity (by
      intro x hx
      have hxE : x=0 ∨ x=q := by simpa only [mem_compl_iff,not_not,mem_insert_iff,mem_singleton_iff] using hx
      rcases hxE with rfl|rfl
      · exact finiteConcentratingBump_zero_outside_unit S a ell hell ha he 0 (by simp)
      · exact hzero)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hbeta.le,smul_eq_mul,
    parisiCDFPrimitive_measure] at hZ
  have hMap : (∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2
      ∂((ρ:Measure Paper.Overlap).map Subtype.val)) =
      ∫p : Paper.Overlap,D p*(finiteConcentratingBump S a ell p)^2 ∂(ρ:Measure Paper.Overlap) :=
    integral_map_of_stronglyMeasurable measurable_subtype_coe
      ((continuous_responseAveragedCurvatureReal (n:=n) ρ beta t lam ht).mul
        ((continuous_finiteConcentratingBump S a ell).pow 2)).stronglyMeasurable
  rw [hMap] at hZ
  have hZ' : beta*(∫p : Paper.Overlap,(w.value p)^2*
      responseAveragedCurvature (n:=n) ρ beta t lam ht.le p ∂(ρ:Measure Paper.Overlap)) ≤
      d*(∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x) := by
    convert hZ using 1
    congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    simp only [D,responseAveragedCurvatureReal,w,finiteConcentratingResponseTest,
      projIcc_of_mem zero_le_one (Subtype.property p)]
    ring
  have hZm := mul_le_mul_of_nonneg_left hZ' (by linarith : 0≤2*(1-t))
  unfold responseC1EnergyDenominator
  change _≤_
  have hh := add_le_add hY hZm
  convert hh using 1 <;> (try dsimp only [finiteResponseDelta,D,ρ,w,finiteConcentratingResponseTest]) <;> ring

theorem finite_concentrating_response_envelope (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (beta t lam theta q d A sigma : ℝ) (hbeta : 1≤beta) (ht : t∈Ico (0 : ℝ) 1)
    (hlam : 0≤lam) (hfloor : lam≤beta*parisiCDF (parisiMix μ ν theta) 0)
    (hd : 0<d) (hA : 0≤A) (hsigma : sigma^2=1)
    (S : Finset ℕ) (hS : S.Nonempty) (a : ℕ→ℝ) (ell : ℝ) (hell : 0<ell)
    (ha : ∀i∈S,0≤a i) (he : ∀i∈S,a i+ell≤1)
    (hdisj : (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell)))
    (hdensity : (ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix μ ν theta)).measure).restrict
      ({(0 : ℝ),q}ᶜ) ≤ ENNReal.ofReal d • volume)
    (hzero : finiteConcentratingBump S a ell q=0)
    (hSign : ∀i∈S,∀x∈Icc (a i) (a i+ell),
      A/2 ≤ sigma*(beta*(parisiCDF ν x-parisiCDF μ x))) :
    let w := finiteConcentratingResponseTest S a ell hell ha he
    let delta₀ := (1-t)*(responseCurvatureConstant beta)^2*(S.card : ℝ)*ell/2
    let B := beta*(S.card : ℝ)*512/(105*ell)
    let Y := B+2*d*finiteResponseDelta (n:=n) (parisiMix μ ν theta) beta t lam ht.2.le S a ell
    0<Y ∧ responseC1EnergyDenominator (n:=n) μ ν beta t lam theta ht.2.le w≤Y ∧
      ((1-t)*A^2/72*min (delta₀^2/B) (delta₀/d))*Y ≤
        (1-t)^3*(responseC1Signal (n:=n) μ ν beta t lam theta ht.2.le w)^2 := by
  dsimp only
  let ρ := parisiMix μ ν theta
  let w := finiteConcentratingResponseTest S a ell hell ha he
  let delta := finiteResponseDelta (n:=n) ρ beta t lam ht.2.le S a ell
  let sig := responseC1Signal (n:=n) μ ν beta t lam theta ht.2.le w
  have hcard : (0 : ℝ)<S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hb : 0<beta := zero_lt_one.trans_le hbeta
  have hlower := finiteResponseDelta_lower hn ρ beta t lam hbeta ht hlam hfloor S a ell hell ha he
  have hSigned := finiteConcentrating_signed_pairing S a ell hell
    (responseAveragedCurvatureReal (n:=n) ρ beta t lam ht.2.le)
    (fun x=>beta*(parisiCDF ν x-parisiCDF μ x))
    (continuous_responseAveragedCurvatureReal ρ beta t lam ht.2)
    (fun x=>responseAveragedCurvature_nonneg ρ beta t lam ht.2.le _) A sigma hSign (by
      have hi := intervalIntegrable_response_C1_signal (n:=n) μ ν ρ beta t lam w 0 1 ht.2
      convert hi using 1
      funext x
      simp only [w,finiteConcentratingResponseTest]
      ring)
  have hSign' : A*delta/2≤(1-t)*(sigma*sig) := by
    have hh := mul_le_mul_of_nonneg_left hSigned (sub_nonneg.mpr ht.2.le)
    convert hh using 1
    · dsimp only [delta,finiteResponseDelta]
      ring
    · dsimp only [sig,responseC1Signal,w,finiteConcentratingResponseTest]
      dsimp only [ρ]
      congr 2
      apply intervalIntegral.integral_congr
      intro x _
      ring
  have hEnvelope := squared_response_upper_envelope (1-t) A
    ((1-t)*(responseCurvatureConstant beta)^2*(S.card : ℝ)*ell/2) delta (sigma*sig)
    (beta*(S.card : ℝ)*512/(105*ell)) d (sub_pos.mpr ht.2) hA
    (mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2.le) (sq_nonneg _))
      hcard.le) hell.le |> fun h=>div_nonneg h (by norm_num))
    hlower (by positivity) hd hSign'
  refine ⟨hEnvelope.1,
    finite_concentrating_response_denominator_bound hn μ ν beta t lam theta q d hb ht.2 hd.le
      S a ell hell ha he hdisj hdensity hzero,?_⟩
  simpa only [mul_pow,hsigma,one_mul,sig] using hEnvelope.2

end QuantitativeFollowup
