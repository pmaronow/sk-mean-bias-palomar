module
public import FourPapersCommon.BoundedTimeFubini
public import FourPapersCommon.IntegrableTruncation

@[expose] public section

/-! Finite nonnegative-time interval Fubini and integrable initial-weight
extension of genuine bounded-weight expectation identities. -/
noncomputable section
open Set MeasureTheory StochasticCalculus Filter
open scoped NNReal Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_nnreal_interval_fubini (P : Measure Ω) [IsProbabilityMeasure P]
    (w : ℝ≥0→Ω→ℝ) (hw : Measurable (Function.uncurry w))
    (a b : ℝ≥0) (K : ℝ) (hb : ∀r ω,‖w r ω‖≤K) :
    Integrable (Function.uncurry w) ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod P) ∧
    (∫ω,(∫r in Ioc a b,w r ω∂nonnegativeLebesgueMeasure)∂P)=
      ∫r in Ioc a b,(∫ω,w r ω∂P)∂nonnegativeLebesgueMeasure := by
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  letI : IsFiniteMeasure ν:=⟨by simpa only [ν,Measure.restrict_apply_univ] using
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b))⟩
  have hi : Integrable (Function.uncurry w) (ν.prod P):=
    (integrable_const K).mono' hw.aestronglyMeasurable (.of_forall fun z=>hb z.1 z.2)
  exact ⟨hi,(integral_integral_swap hi).symm⟩

theorem measurable_nnreal_intervalIntegral (w : ℝ≥0→Ω→ℝ)
    (hw : Measurable (Function.uncurry w)) (a b : ℝ≥0) :
    Measurable (fun ω=>∫r in Ioc a b,w r ω∂nonnegativeLebesgueMeasure) :=
  (hw.stronglyMeasurable.integral_prod_left').measurable

theorem norm_nnreal_intervalIntegral_le (w : ℝ≥0→Ω→ℝ)
    (a b : ℝ≥0) (K : ℝ) (hb : ∀r ω,‖w r ω‖≤K) (ω : Ω) :
    ‖∫r in Ioc a b,w r ω∂nonnegativeLebesgueMeasure‖≤
      K*max ((b:ℝ)-a) 0 := by
  letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc a b)):=⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b))⟩
  have hh:=norm_integral_le_of_norm_le_const (μ:=nonnegativeLebesgueMeasure.restrict (Ioc a b))
    (.of_forall fun r=>hb r ω)
  simpa only [Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,
    ENNReal.toReal_ofReal',mul_comm] using hh

theorem integral_eq_of_truncated_weight_identity (P : Measure Ω)
    (F H W : Ω→ℝ) (hF : Measurable F) (hH : Measurable H)
    (KF KH : ℝ) (hFb : ∀ω,‖F ω‖≤KF) (hHb : ∀ω,‖H ω‖≤KH)
    (hW : Measurable W) (hWn : ∀ω,0≤W ω) (hWi : Integrable W P)
    (htest : ∀j : ℕ,(∫ω,truncateWeight W j ω*F ω∂P)=
      ∫ω,truncateWeight W j ω*H ω∂P) :
    (∫ω,W ω*F ω∂P)=∫ω,W ω*H ω∂P := by
  have hleft:=tendsto_integral_truncateWeight_mul W F hW hWn hWi hF KF hFb
  have hright:=tendsto_integral_truncateWeight_mul W H hW hWn hWi hH KH hHb
  exact tendsto_nhds_unique hleft (hright.congr (fun j=>(htest j).symm))

theorem map_nonnegativeLebesgueMeasure_restrict_interval (a b : ℝ≥0) :
    Measure.map ((↑):ℝ≥0→ℝ) (nonnegativeLebesgueMeasure.restrict (Ioc a b))=
      (volume:Measure ℝ).restrict (Ioc (a:ℝ) (b:ℝ)) := by
  let f : ℝ≥0→ℝ:=(↑)
  have hf : MeasurableEmbedding f:=measurableEmbedding_nnrealCoe_iterated
  have hp : f⁻¹' Ioc (a:ℝ) (b:ℝ)=Ioc a b := by
    ext r
    simp only [mem_preimage,mem_Ioc,f]
    exact and_congr (by norm_cast) (by norm_cast)
  rw [←hp,←hf.restrict_map]
  change (Measure.map f (Measure.comap f (volume:Measure ℝ))).restrict (Ioc (a:ℝ) (b:ℝ))=_
  rw [hf.map_comap,NNReal.range_coe,Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  ext r
  simp only [mem_inter_iff,mem_Ioc,mem_Ici]
  exact ⟨fun h=>h.1,fun h=>⟨h,a.coe_nonneg.trans h.1.le⟩⟩

theorem nnreal_intervalIntegral_eq_real (f : ℝ≥0→ℝ) (hf : Measurable f)
    (a b : ℝ≥0) (hab : a≤b) :
    (∫r in Ioc a b,f r∂nonnegativeLebesgueMeasure)=
      ∫r in (a:ℝ)..(b:ℝ),f r.toNNReal := by
  have hm : Measurable (fun r : ℝ=>f r.toNNReal):=hf.comp measurable_real_toNNReal
  have hh:=integral_map_of_stronglyMeasurable NNReal.continuous_coe.measurable hm.stronglyMeasurable
    (μ:=nonnegativeLebesgueMeasure.restrict (Ioc a b))
  rw [map_nonnegativeLebesgueMeasure_restrict_interval,
    ←intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hab)] at hh
  simpa only [Real.toNNReal_coe] using hh.symm

end FourPapersCommon
