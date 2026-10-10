module
public import QuantitativeFollowup.VectorFirstVariation
public import QuantitativePaper.VectorFunctionalConvexity
public import Paper.JTFubini
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! The exact actual deficit first variation and its convex support
inequality, with all terminal-pairing and Fubini inputs discharged. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem continuous_vectorOverlapDeficit (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    Continuous (vectorOverlapDeficit (n:=n) μ β t a ht) :=
  continuous_transportDeficit _ (continuous_vectorMeanOverlapReal μ β t a ht)

theorem vectorOverlapDeficit_cdf_pairing (μ ν : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht q ∂(ν:Measure Paper.Overlap))-
      (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht q ∂(μ:Measure Paper.Overlap))=
    ∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
      (vectorMeanOverlapReal (n:=n) μ β t a ht r-r) := by
  let g:=fun r=>vectorMeanOverlapReal (n:=n) μ β t a ht r-r
  have hg:Continuous g:=(continuous_vectorMeanOverlapReal μ β t a ht).sub continuous_id
  have hgi:IntegrableOn g (Ioc (0:ℝ) 1) volume:=
    hg.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hν:=Paper.parisiCDF_tail_pairing ν g hgi
  have hμ:=Paper.parisiCDF_tail_pairing μ g hgi
  change (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht q ∂(ν:Measure Paper.Overlap))=
    ∫r in (0:ℝ)..1,g r*Paper.parisiCDF ν r at hν
  change (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht q ∂(μ:Measure Paper.Overlap))=
    ∫r in (0:ℝ)..1,g r*Paper.parisiCDF μ r at hμ
  rw [hν,hμ,←intervalIntegral.integral_sub
    ((Paper.parisiCDF_intervalIntegrable ν 0 1).continuousOn_mul hg.continuousOn)
    ((Paper.parisiCDF_intervalIntegrable μ 0 1).continuousOn_mul hg.continuousOn)]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only [g]
  ring

theorem hasDerivWithinAt_vectorMeasureFunctional_mix_deficit (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    HasDerivWithinAt (fun lam=>vectorMeasureFunctional n (Paper.parisiMix μ ν lam) β t a)
      (((1-t)*β^2)/2*((∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q ∂(ν:Measure Paper.Overlap))-
        (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q ∂(μ:Measure Paper.Overlap))))
        (Icc (0:ℝ) 1) 0 := by
  rw [vectorOverlapDeficit_cdf_pairing]
  exact hasDerivWithinAt_vectorMeasureFunctional_mix_moment hn μ ν β t a hβ ht

theorem vectorMeasureFunctional_convex_deficit_bound (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a) :
    (((1-t)*β^2)/2)*
      ((∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q ∂(ν:Measure Paper.Overlap))-
        (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q ∂(μ:Measure Paper.Overlap)))≤
      vectorMeasureFunctional n ν β t a-vectorMeasureFunctional n μ β t a := by
  have hc:=convexOn_vectorMeasureFunctional_mix n μ ν β t ht.le a ha
  have hd:=hasDerivWithinAt_vectorMeasureFunctional_mix_deficit hn μ ν β t a hβ ht
  have hs:=hc.le_slope_of_hasDerivWithinAt (show (0:ℝ)∈Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩)
    (show (1:ℝ)∈Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩) zero_lt_one hd
  simpa only [slope_def_field,Paper.parisiMix_one,Paper.parisiMix_zero,sub_zero,div_one] using hs

end QuantitativeFollowup
