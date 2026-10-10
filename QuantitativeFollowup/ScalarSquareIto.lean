module
public import QuantitativeFollowup.ScalarSourceBounds
public import FourPapersCommon.LocalItoEndpoints
public import FRSB.PolynomialMomentSources

@[expose] public section

/-! Actual squared-gradient-difference evolution along the minimizing
Parisi diffusion. Local time regularity comes from the genuine weak PDE;
closed endpoints are obtained by bounded convergence. -/
noncomputable section
open Set MeasureTheory Filter StochasticCalculus Paper FRSB FourPapersCommon
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 700000

theorem measurable_selectedState_real (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : ℝ×Paper.BrownianSample=>selectedParisiItoState β 0 hβ μ z.1.toNNReal z.2) := by
  convert (measurable_canonicalParisiItoState β 0 μ
    (fun t x=>parisiGradient β μ (t,x)) (continuous_parisiGradient β μ)
    (fun t x=>norm_parisiGradient_le_one β μ (t,x))
    (lipschitzWith_parisiGradient β hβ μ)).comp
      (measurable_real_toNNReal.prodMap measurable_id) using 1
  rfl

def scalarSquareDifferenceMoment (β : ℝ) (hβ : β≠0) (μ ν : Paper.ParisiMeasure)
    (t : ℝ≥0) : ℝ := ∫ω,
      scalarGradientDifference β μ ν (t,selectedParisiItoState β 0 hβ μ t ω)^2
        ∂canonicalBrownianMeasure

theorem scalarSquareDifferenceMoment_interval_integral (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) (gμ gν : ℝ→ℝ) (hgμ : Continuous gμ) (hgν : Continuous gν)
    (b : ℝ) (hb : b≤1) (heμ : EqOn (parisiCDF μ) gμ (Ioo (0:ℝ) b))
    (heν : EqOn (parisiCDF ν) gν (Ioo (0:ℝ) b))
    (l r : ℝ≥0) (hlr : l≤r) (hrb : (r:ℝ)<b) :
    scalarSquareDifferenceMoment β hβ μ ν r-scalarSquareDifferenceMoment β hβ μ ν l=
      ∫t in (l:ℝ)..(r:ℝ),∫ω,
        scalarClippingSquareSource β μ ν (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)
          ∂canonicalBrownianMeasure := by
  let X:=selectedParisiItoState β 0 hβ μ
  let f : ℝ→ℝ→ℝ:=fun t x=>scalarGradientDifference β μ ν (t,x)^2
  let ft : ℝ→ℝ→ℝ:=fun t x=>2*scalarGradientDifference β μ ν (t,x)*
    (continuousProfileTimeField β ν gν 1 (t,x)-continuousProfileTimeField β μ gμ 1 (t,x))
  let fx : ℝ→ℝ→ℝ:=fun t x=>2*scalarGradientDifference β μ ν (t,x)*scalarCurvatureDifference β μ ν (t,x)
  let fxx : ℝ→ℝ→ℝ:=fun t x=>2*scalarCurvatureDifference β μ ν (t,x)^2+
    2*scalarGradientDifference β μ ν (t,x)*(parisiSpatialField β ν 3 (t,x)-parisiSpatialField β μ 3 (t,x))
  have hf : Continuous (fun p : ℝ×ℝ=>f p.1 p.2) :=
    (continuous_scalarGradientDifference β μ ν).pow 2
  have hft : Continuous (fun p : ℝ×ℝ=>ft p.1 p.2) :=
    (continuous_const.mul (continuous_scalarGradientDifference β μ ν)).mul
      ((continuous_continuousProfileTimeField β ν gν hgν 1).sub
        (continuous_continuousProfileTimeField β μ gμ hgμ 1))
  have hfx : Continuous (fun p : ℝ×ℝ=>fx p.1 p.2) :=
    (continuous_const.mul (continuous_scalarGradientDifference β μ ν)).mul
      (continuous_scalarCurvatureDifference β μ ν)
  have hfxx : Continuous (fun p : ℝ×ℝ=>fxx p.1 p.2) :=
    (continuous_const.mul ((continuous_scalarCurvatureDifference β μ ν).pow 2)).add
      ((continuous_const.mul (continuous_scalarGradientDifference β μ ν)).mul
        ((continuous_parisiSpatialField β ν 3).sub (continuous_parisiSpatialField β μ 3)))
  have ht : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (fun s=>f s x) (ft t x) t := by
    intro t htt x
    have hdν:=hasDerivAt_spatialField_continuous_profile β hβ ν gν hgν 0 b le_rfl hb heν 1 t x htt
    have hdμ:=hasDerivAt_spatialField_continuous_profile β hβ μ gμ hgμ 0 b le_rfl hb heμ 1 t x htt
    simp only [parisiSpatialField_one] at hdν hdμ
    convert! (hdν.sub hdμ).pow 2 using 1 <;> dsimp [scalarGradientDifference,f,ft] <;> ring
  have hyx (t x : ℝ) : HasDerivAt (fun z=>scalarGradientDifference β μ ν (t,z))
      (scalarCurvatureDifference β μ ν (t,x)) x :=
    (hasDerivAt_parisiGradient_spatial_all β ν t x).sub
      (hasDerivAt_parisiGradient_spatial_all β μ t x)
  have hx : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (f t) (fx t x) x := by
    intro t _ x
    convert (hyx t x).pow 2 using 1 <;> simp only [f,fx,Nat.cast_ofNat,Nat.reduceSub,pow_one] <;> ring
  have hz (κ : Paper.ParisiMeasure) (t x : ℝ) (htt : t∈Ioo (0:ℝ) b) :
      HasDerivAt (fun z=>parisiHessian β κ (t,z)) (parisiSpatialField β κ 3 (t,x)) x := by
    have he : (fun z=>parisiSpatialField β κ 2 (t,z))=(fun z=>parisiHessian β κ (t,z)) :=
      funext fun z=>backwardC_eq_hessian β κ t z ⟨htt.1.le,htt.2.le.trans hb⟩
    have hd:=hasDerivAt_parisiSpatialField β κ 2 t x ⟨htt.1.le,htt.2.le.trans hb⟩
    rw [he] at hd
    exact hd
  have hxx : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (fx t) (fxx t x) x := by
    intro t htt x
    have hzd:= (hz ν t x htt).sub (hz μ t x htt)
    convert! ((hyx t x).const_mul 2).mul hzd using 1 <;> dsimp [fx,fxx,scalarCurvatureDifference] <;> ring
  have hC2 : ∀t∈Ioo (0:ℝ) b,ContDiff ℝ 2 (f t) := by
    intro t _
    exact ((contDiff_parisiGradient_spatial β ν t).sub
      (contDiff_parisiGradient_spatial β μ t)).pow 2 |>.of_le (by simp)
  have hK : ∀t∈Ioo (0:ℝ) b,∀x,‖fx t x‖≤(8:ℝ≥0) := by
    intro t _ x
    dsimp only [fx]
    simp only [norm_mul,Real.norm_ofNat]
    calc
      (2:ℝ)*‖scalarGradientDifference β μ ν (t,x)‖*‖scalarCurvatureDifference β μ ν (t,x)‖ ≤ 2*2*2 := by
        gcongr <;> first | exact norm_scalarGradientDifference_le β μ ν (t,x) | exact norm_scalarCurvatureDifference_le β μ ν (t,x)
      _=8 := by norm_num
  have hM : ∀t x,‖f t x‖≤(4:ℝ≥0) := by
    intro t x
    dsimp only [f]
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_scalarGradientDifference_le β μ ν (t,x)) 2).trans_eq (by norm_num)
  let source : ℝ→Paper.BrownianSample→ℝ:=fun t ω=>scalarClippingSquareSource β μ ν (t,X t.toNNReal ω)
  have hsm : Measurable (Function.uncurry source) :=
    (measurable_scalarClippingSquareSource β μ ν).comp
      (measurable_fst.prodMk (measurable_selectedState_real β hβ μ))
  have hB : ∀t ω,‖source t ω‖≤40*β^2 :=
    fun t ω=>norm_scalarClippingSquareSource_le β μ ν (t,X t.toNNReal ω)
  have hsource : ∀ω,∀t∈Ioo (0:ℝ) b,
      ft t (X t.toNNReal ω)+fx t (X t.toNNReal ω)*selectedParisiItoDrift β 0 hβ μ t.toNNReal ω+
        (1/2:ℝ)*fxx t (X t.toNNReal ω)*β^2=source t ω := by
    intro ω t htt
    have htt0:0≤t:=htt.1.le
    have htt1:t≤1:=htt.2.le.trans hb
    have hdr:selectedParisiItoDrift β 0 hβ μ t.toNNReal ω=
        β^2*parisiCDF μ t*parisiGradient β μ (t,X t.toNNReal ω) := by
      simp only [selectedParisiItoDrift,canonicalParisiItoDrift,Real.coe_toNNReal t htt0,
        ite_eq_left htt1,X,selectedParisiItoState]
    dsimp only [ft,fx,fxx,source]
    rw [hdr]
    have heP (κ : Paper.ParisiMeasure) (g : ℝ→ℝ) (he : EqOn (parisiCDF κ) g (Ioo (0:ℝ) b)) :
        continuousProfileTimeField β κ g 1 (t,X t.toNNReal ω)=parisiTimeField β κ 1 (t,X t.toNNReal ω) := by
      simp only [continuousProfileTimeField,parisiTimeField,he htt]
    rw [heP ν gν heν,heP μ gμ heμ]
    exact scalarClippingSquareSource_eq_generator β μ ν t (X t.toNNReal ω)
  exact ito_expectation_local_source_closed (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ)
    f ft fx fxx b hf hft.continuousOn hfx hfxx ht hx hxx hC2 8 4 hK hM source hsm
    (40*β^2) hB hsource l r hlr hrb

end QuantitativeFollowup
