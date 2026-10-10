module
public import QuantitativePaper.VectorGridProfileSecondCropped
public import QuantitativePaper.VectorProfileRestartIntegrability
public import QuantitativePaper.VectorProfileClosedPositiveSource
public import FourPapersCommon.ClosedBoundedSourceFTC

@[expose] public section

/-! Actual signed second-profile sources close at both restart-cell
endpoints, with a depth-independent bound on their expected reaction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorGridProfileSecondRestartMoment
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t θ : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (r : ℝ) : ℝ:=
  ∫sample : VectorDisorderBrownianSample n,
    vectorProfileCellPotentialSecondVariation
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i ((q:ℝ)+r,θ,p)
      (vectorRestartState (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j))
        β t ht q p x r.toNNReal sample) ∂vectorDisorderBrownianMeasure n

def vectorGridProfileSecondRestartSourceMean
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t θ : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (r : ℝ) : ℝ:=
  ∫sample,vectorGridProfileSecondRestartReaction μ ν j β t θ ht q p x i r.toNNReal sample
    ∂vectorDisorderBrownianMeasure n

theorem abs_vectorGridProfileSecondRestartSourceMean_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (r : ℝ) (hr0 : 0≤r) (hr : (q:ℝ)+r∈Ioo
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    |vectorGridProfileSecondRestartSourceMean μ ν j β t θ ht.le q p x i r|≤
      vectorProfileSecondReactionBound n β t := by
  have hphysical : (q:ℝ)+r∈Icc (0:ℝ) 1:=
    ⟨add_nonneg q.property.1 hr0,hr.2.le.trans
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_le_one (by omega))⟩
  let v : Paper.Overlap:=⟨(q:ℝ)+r,hphysical⟩
  have hb (sample : VectorDisorderBrownianSample n) :
      ‖vectorGridProfileSecondRestartReaction μ ν j β t θ ht.le q p x i r.toNNReal sample‖≤
        vectorProfileSecondReactionBound n β t := by
    have hh:=abs_vectorGridProfile_second_reaction_le μ ν j β t hβ ht i hi v
      ⟨hr.1.le,hr.2⟩ θ hθ p
      (vectorRestartState (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j))
        β t ht.le q p x r.toNNReal sample)
    simpa only [vectorGridProfileSecondRestartReaction,Real.norm_eq_abs,neg_mul,abs_neg,
      Real.coe_toNNReal r hr0,v] using hh
  have he:=norm_integral_le_of_norm_le_const
    (μ:=vectorDisorderBrownianMeasure n) (.of_forall hb)
  simpa only [vectorGridProfileSecondRestartSourceMean,Real.norm_eq_abs,
    Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using he

theorem vectorGridProfile_second_restart_closed
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hcell : ∀r∈Icc a b,(q:ℝ)+r∈Icc
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    let F:=vectorGridProfileSecondRestartMoment μ ν j β t θ ht.le q p x i
    let g:=vectorGridProfileSecondRestartSourceMean μ ν j β t θ ht.le q p x i
    IntegrableOn g (Ioc a b) volume ∧ F b-F a=∫r in a..b,g r := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
  let F:=vectorGridProfileSecondRestartMoment μ ν j β t θ ht.le q p x i
  let g:=vectorGridProfileSecondRestartSourceMean μ ν j β t θ ht.le q p x i
  apply closed_bounded_source_ftc F g a b (vectorProfileSecondReactionBound n β t) hab
    (continuousOn_vectorProfile_second_restart_expectation ρ s₀ s₁ β t ht.le q p x θ hθ i hi a b ha hb hcell)
  · intro r hr
    have hleft:=(hcell a ⟨le_rfl,hab⟩).1
    have hright:=(hcell b ⟨hab,le_rfl⟩).2
    exact abs_vectorGridProfileSecondRestartSourceMean_le μ ν j β t hβ ht θ hθ q p x i hi r
      (ha.trans hr.1.le) ⟨by linarith [hr.1],by linarith [hr.2]⟩
  · intro l hl u hu hlu
    have hl0 : 0≤l:=ha.trans hl.1.le
    have hu0 : 0≤u:=ha.trans hu.1.le
    let l' : ℝ≥0:=⟨l,hl0⟩
    let u' : ℝ≥0:=⟨u,hu0⟩
    have hul : l'≤u':=hlu
    have hu1 : u'≤1:=hu.2.le.trans hb
    have hleft:=(hcell a ⟨le_rfl,hab⟩).1
    have hright:=(hcell b ⟨hab,le_rfl⟩).2
    have hlcell : s₀.q i<(q:ℝ)+l:=by linarith [hl.1]
    have hucell : (q:ℝ)+u<s₀.q (i+1):=by linarith [hu.2]
    obtain ⟨hI,hD⟩:=vectorGridProfile_second_restart_cropped μ ν j β t hβ ht θ hθ q p x i hi
      l' u' hul hu1 hlcell hucell
    have hgI : IntegrableOn
        (fun r : ℝ≥0=>∫sample,vectorGridProfileSecondRestartReaction μ ν j β t θ ht.le q p x i r sample
          ∂vectorDisorderBrownianMeasure n) (Ioc l' u') nonnegativeLebesgueMeasure:=hI.integral_prod_left
    obtain ⟨hgReal,hgEq⟩:=nnreal_source_interval_to_real _ l' u' hul hgI
    have hlQ:=integrable_vectorProfile_second_restart_test ρ s₀ s₁ β t ht.le q p x θ hθ i hi l'
      (hul.trans hu1) (hcell l ⟨hl.1.le,hl.2.le⟩)
    have huQ:=integrable_vectorProfile_second_restart_test ρ s₀ s₁ β t ht.le q p x θ hθ i hi u'
      hu1 (hcell u ⟨hu.1.le,hu.2.le⟩)
    rw [integral_sub huQ hlQ] at hD
    rw [hgEq] at hD
    refine ⟨hgReal,?_⟩
    change F (u':ℝ)-F (l':ℝ)=∫r in (l':ℝ)..(u':ℝ),g r
    simpa only [F,g,vectorGridProfileSecondRestartMoment,vectorGridProfileSecondRestartSourceMean,
      Real.toNNReal_coe,s₀,s₁,ρ] using hD

end QuantitativePaper
