module
public import QuantitativeFollowup.ScalarSquareIto
public import QuantitativeFollowup.ScalarPotentialBound

@[expose] public section

/-! Closed-endpoint evolution of the actual potential difference along the
original Parisi diffusion. A time clamp supplies a globally bounded test;
inside the physical interval it is the literal potential difference. -/
noncomputable section
open Set MeasureTheory Filter StochasticCalculus Paper FRSB FourPapersCommon
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 700000

theorem scalarPotentialDifference_interval_integral (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) (gμ gν : ℝ→ℝ) (hgμ : Continuous gμ) (hgν : Continuous gν)
    (b : ℝ) (hb0 : 0≤b) (hb : b≤1) (heμ : EqOn (parisiCDF μ) gμ (Ioo (0:ℝ) b))
    (heν : EqOn (parisiCDF ν) gν (Ioo (0:ℝ) b))
    (l r : ℝ≥0) (hlr : l≤r) (hrb : (r:ℝ)<b) :
    (∫ω,parisiPotential β ν (r,selectedParisiItoState β 0 hβ μ r ω)-
      parisiPotential β μ (r,selectedParisiItoState β 0 hβ μ r ω)∂canonicalBrownianMeasure)-
    (∫ω,parisiPotential β ν (l,selectedParisiItoState β 0 hβ μ l ω)-
      parisiPotential β μ (l,selectedParisiItoState β 0 hβ μ l ω)∂canonicalBrownianMeasure)=
      ∫t in (l:ℝ)..(r:ℝ),∫ω,
        scalarClippingPotentialSource β μ ν (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)
          ∂canonicalBrownianMeasure := by
  let X:=selectedParisiItoState β 0 hβ μ
  let τ : ℝ→ℝ:=fun t=>(projIcc 0 b hb0 t:ℝ)
  have hτc : Continuous τ:=continuous_subtype_val.comp continuous_projIcc
  have hτmem (t : ℝ) : τ t∈Icc (0:ℝ) 1:=⟨(projIcc 0 b hb0 t).property.1,
    (projIcc 0 b hb0 t).property.2.trans hb⟩
  have hτid (t : ℝ) (ht : t∈Icc (0:ℝ) b) : τ t=t := by
    simp only [τ,projIcc_of_mem _ ht]
  let f : ℝ→ℝ→ℝ:=fun t x=>parisiPotential β ν (τ t,x)-parisiPotential β μ (τ t,x)
  let ft : ℝ→ℝ→ℝ:=fun t x=>continuousProfileTimeField β ν gν 0 (t,x)-continuousProfileTimeField β μ gμ 0 (t,x)
  let fx : ℝ→ℝ→ℝ:=fun t x=>scalarGradientDifference β μ ν (τ t,x)
  let fxx : ℝ→ℝ→ℝ:=fun t x=>scalarCurvatureDifference β μ ν (τ t,x)
  have hmap : Continuous (fun p : ℝ×ℝ=>(τ p.1,p.2)):=
    (hτc.comp continuous_fst).prodMk continuous_snd
  have hf : Continuous (fun p : ℝ×ℝ=>f p.1 p.2):=
    ((continuous_parisiPotential β ν).sub (continuous_parisiPotential β μ)).comp hmap
  have hft : Continuous (fun p : ℝ×ℝ=>ft p.1 p.2):=
    (continuous_continuousProfileTimeField β ν gν hgν 0).sub
      (continuous_continuousProfileTimeField β μ gμ hgμ 0)
  have hfx : Continuous (fun p : ℝ×ℝ=>fx p.1 p.2):=
    (continuous_scalarGradientDifference β μ ν).comp hmap
  have hfxx : Continuous (fun p : ℝ×ℝ=>fxx p.1 p.2):=
    (continuous_scalarCurvatureDifference β μ ν).comp hmap
  have ht : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (fun s=>f s x) (ft t x) t := by
    intro t htt x
    have hdν:=hasDerivAt_spatialField_continuous_profile β hβ ν gν hgν 0 b le_rfl hb heν 0 t x htt
    have hdμ:=hasDerivAt_spatialField_continuous_profile β hβ μ gμ hgμ 0 b le_rfl hb heμ 0 t x htt
    have hd : HasDerivAt (fun r=>parisiPotential β ν (r,x)-parisiPotential β μ (r,x)) (ft t x) t:=hdν.sub hdμ
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds htt] with r hr
    simp only [f,hτid r ⟨hr.1.le,hr.2.le⟩]
  have hx : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (f t) (fx t x) x := by
    intro t _ x
    exact (hasDerivAt_parisiPotential_spatial_all β ν (τ t) x (hτmem t)).sub
      (hasDerivAt_parisiPotential_spatial_all β μ (τ t) x (hτmem t))
  have hxx : ∀t∈Ioo (0:ℝ) b,∀x,HasDerivAt (fx t) (fxx t x) x := by
    intro t _ x
    exact (hasDerivAt_parisiGradient_spatial_all β ν (τ t) x).sub
      (hasDerivAt_parisiGradient_spatial_all β μ (τ t) x)
  have hC2 : ∀t∈Ioo (0:ℝ) b,ContDiff ℝ 2 (f t) := by
    intro t _
    exact ((contDiff_parisiPotential_spatial β ν (τ t) (hτmem t)).sub
      (contDiff_parisiPotential_spatial β μ (τ t) (hτmem t))).of_le (by simp)
  have hK : ∀t∈Ioo (0:ℝ) b,∀x,‖fx t x‖≤(2:ℝ≥0):=
    fun t _ x=>norm_scalarGradientDifference_le β μ ν (τ t,x)
  let M : ℝ≥0:=⟨(5/2:ℝ)*β^2,by positivity⟩
  have hM : ∀t x,‖f t x‖≤M:=fun t x=>norm_parisiPotential_sub_le β ν μ (τ t) x (hτmem t)
  let source : ℝ→Paper.BrownianSample→ℝ:=fun t ω=>scalarClippingPotentialSource β μ ν (t,X t.toNNReal ω)
  have hsm : Measurable (Function.uncurry source):=
    (measurable_scalarClippingPotentialSource β μ ν).comp
      (measurable_fst.prodMk (measurable_selectedState_real β hβ μ))
  have hB : ∀t ω,‖source t ω‖≤5*β^2:=
    fun t ω=>norm_scalarClippingPotentialSource_le β μ ν (t,X t.toNNReal ω)
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
    rw [hdr,hτid t ⟨htt.1.le,htt.2.le⟩]
    have heP (κ : Paper.ParisiMeasure) (g : ℝ→ℝ) (he : EqOn (parisiCDF κ) g (Ioo (0:ℝ) b)) :
        continuousProfileTimeField β κ g 0 (t,X t.toNNReal ω)=parisiTimeField β κ 0 (t,X t.toNNReal ω) := by
      simp only [continuousProfileTimeField,parisiTimeField,he htt]
    rw [heP ν gν heν,heP μ gμ heμ]
    exact scalarClippingPotentialSource_eq_generator β μ ν t (X t.toNNReal ω) ⟨htt0,htt1⟩
  have hh:=ito_expectation_local_source_closed (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ)
    f ft fx fxx b hf hft.continuousOn hfx hfxx ht hx hxx hC2 2 M hK hM source hsm
    (5*β^2) hB hsource l r hlr hrb
  have hlb : (l:ℝ)∈Icc (0:ℝ) b:=⟨l.coe_nonneg,(NNReal.coe_le_coe.mpr hlr).trans hrb.le⟩
  simpa only [f,hτid l hlb,hτid r ⟨r.coe_nonneg,hrb.le⟩] using hh

end QuantitativeFollowup
