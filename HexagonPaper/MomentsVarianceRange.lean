module
public import HexagonPaper.MomentsSuperlevels
public import FourPapersCommon.BoundedLayercake
public import FourPapersCommon.TruncatedPowerIntegrals

@[expose] public section

/-! The actual integrated quantile variance estimate from a level-range
bound.  All bin geometry, actual conditional comparisons, threshold inputs
and layer-cake integrals are proved; the essential-diameter identification
is supplied separately. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace HexagonPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_quantile_second_range_bound_128 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (I : Set ℝ) (hI : I.OrdConnected) (hDom : I⊆Ioc (0:ℝ) (1-s))
    (h a ell u : ℝ) (hh : 0<h) (hlen : volume.real I=h) (hell : 0≤ell) (hu : 0<u)
    (hRange : ∀w∈I,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+ell))
    (hThreshold : ∀ᵐw ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    (∫v in I,vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v))≤
      128*(min h ((1/((n:ℝ)*((1-t)*β^2)*u))*(1+max (Real.log (h/(1/((n:ℝ)*((1-t)*β^2)*u)))) 0))+
        ((1/((n:ℝ)*((1-t)*β^2)*u))*ell)^(2/3:ℝ)*h^(1/3:ℝ)) := by
  let ε:=1/((n:ℝ)*((1-t)*β^2)*u)
  let ψ : ℝ→ℝ:=fun v=>vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)
  let P:=volume.restrict I
  let F : ℝ→ℝ:=fun τ=>P.real {v | τ<ψ v}
  let A : ℝ→ℝ:=fun τ=>min h (128*ε/τ)
  let B : ℝ→ℝ:=fun τ=>min h (128*ε*ell*τ^(-(3/2:ℝ)))
  have hε : 0<ε:=by positivity
  let :=isFiniteMeasure_of_le (volume.restrict (Ioc (0:ℝ) (1-s))) (Measure.restrict_mono_set volume hDom)
  have hψ : Measurable ψ:=(measurable_vectorCenteredSelfOverlapSecond μ β t s ht.le).comp
    (parisiFreeQuantile_measurable μ s)
  have hψbound (v : ℝ) : 0≤ψ v ∧ ψ v≤1:=
    vectorCenteredSelfOverlapSecond_bounds hn μ β t s ht.le _
  have hiψ : Integrable ψ P :=by
    apply Integrable.of_bound hψ.aestronglyMeasurable 1
    exact .of_forall fun v=>by rw [Real.norm_of_nonneg (hψbound v).1];exact (hψbound v).2
  have hcake:=(integral_layercake_unit_interval P ψ hiψ (.of_forall fun v=>(hψbound v).1)
    (.of_forall fun v=>(hψbound v).2))
  have hiF : IntegrableOn F (Ioo 0 1):=integrable_real_superlevels_unit_interval P ψ
  have hiA : IntegrableOn A (Ioo 0 1):=integrableOn_truncated_reciprocal h (128*ε) 1 hh.le (by positivity)
  have hiB0 : IntegrableOn B (Ioi 0):=
    (integral_truncated_three_halves h (128*ε*ell) hh (by positivity)).1
  have hiB : IntegrableOn B (Ioo 0 1):=hiB0.mono_set (fun _ h=>h.1)
  have hF (τ : ℝ) : F τ=volume.real {v | v∈I ∧ τ<ψ v} := by
    dsimp only [F,P]
    rw [measureReal_restrict_apply (measurableSet_lt measurable_const hψ)]
    congr 1
    ext v
    simp only [mem_inter_iff,mem_setOf_eq,and_comm]
  have hcomp : F≤ᵐ[volume.restrict (Ioo 0 1)]fun τ=>A τ+B τ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [hF τ]
    have hb:=vector_quantile_superlevel_bound_128 hn μ s β t hβ ht hs hμ hmin I hI hDom
      a ell u τ hell hu hτ.1 hRange hThreshold
    simpa only [hlen] using hb
  have hi:=integral_mono_ae hiF (hiA.add hiB) hcomp
  have heAdd:=integral_add hiA hiB
  simp only [Pi.add_apply] at hi heAdd
  rw [heAdd] at hi
  rw [hcake]
  apply hi.trans
  have hA:=truncated_reciprocal_128_bound h ε hh hε
  have hB:=setIntegral_mono_set hiB0 (show 0≤ᵐ[volume.restrict (Ioi 0)]B from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact le_min hh.le (mul_nonneg (mul_nonneg (by positivity) hell)
      (Real.rpow_nonneg hτ.le _)))
    (show Ioo (0:ℝ) 1≤ᵐ[volume]Ioi 0 from .of_forall fun _ h=>h.1)
  have hB':=hB.trans (truncated_three_halves_128_bound h ε ell hh hε hell)
  have hnonneg : 0≤ min h (ε*(1+max (Real.log (h/ε)) 0)) :=by positivity
  change (∫τ in Ioo (0:ℝ) 1,A τ)+(∫τ in Ioo (0:ℝ) 1,B τ)≤_
  change (∫τ in Ioo (0:ℝ) 1,A τ)≤_ at hA
  change (∫τ in Ioo (0:ℝ) 1,B τ)≤_ at hB'
  change (∫τ in Ioo (0:ℝ) 1,A τ)+(∫τ in Ioo (0:ℝ) 1,B τ)≤
    128*(min h (ε*(1+max (Real.log (h/ε)) 0))+(ε*ell)^(2/3:ℝ)*h^(1/3:ℝ))
  linarith

end HexagonPaper
