module
public import QuantitativeFollowup.FollowupCavityCppNativeTaylor
public import QuantitativeFollowup.FollowupCavityCppNativeFactorJets
public import QuantitativeFollowup.FollowupCavityNativeStreamingBounds
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! The genuine Taylor remainder is measurable and integrable in the split
overlap independently of the zero-response identification. Its initial
derivative is a limit of inward, measurable difference quotients. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem cpp_measurable_covariance {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : A×Ω→ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a=>covariance (fun ω=>f (a,ω)) (fun ω=>g (a,ω)) P) := by
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν:=P)).measurable
  have hj := (hg.stronglyMeasurable.integral_prod_right' (ν:=P)).measurable
  have hm : Measurable (fun z : A×Ω=>
      (f z-(∫ω,f (z.1,ω)∂P))*(g z-(∫ω,g (z.1,ω)∂P))) :=
    (hf.sub (hi.comp measurable_fst)).mul (hg.sub (hj.comp measurable_fst))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=P)).measurable

theorem measurable_followupCavityCppFunction_split
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Measurable (fun p : Paper.Overlap=>followupCavityCppFunction n β ρ hβ hρ μ a p u) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let P:=anisotropicMeasureSampleLaw D μ a
  let f : Paper.Overlap×AnisotropicDisorderBrownianSample (n+1)→ℝ :=
    fun z=>anisotropicProcessMagnetization D μ z.1 z.2 (Fin.last n)^2
  let g : Paper.Overlap×AnisotropicDisorderBrownianSample (n+1)→ℝ :=
    fun z=>anisotropicSelectedMeanSquare Finset.univ
      (cavityRestFieldProjection n (anisotropicProcessMagnetization D μ z.1 z.2))
  have hf : Measurable f :=
    ((EuclideanSpace.proj (Fin.last n)).continuous.measurable.comp
      (measurable_uncurry_anisotropicProcessMagnetization D μ)).pow_const 2
  have hg : Measurable g :=
    (continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp
      ((cavityRestFieldProjection n).continuous.measurable.comp
        (measurable_uncurry_anisotropicProcessMagnetization D μ))
  have hm:=cpp_measurable_covariance P f g hf hg
  convert! hm using 1
  funext p
  exact followupCavityCppFunction_eq_actual β ρ hβ hρ μ a p u hu

private theorem cppTaylorSchedule_antitone (p : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule p) := by
  apply antitone_nat_of_succ_le
  intro j
  rcases j with _|_|j
  · exact p.property.2
  · exact p.property.1
  · exact le_rfl

private theorem cppTaylorFactor_bound (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (T : FiniteTerminalGenealogy 2) (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C) (r : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) T F) (Icc 0 1) r u|≤
      growth (7*β^2) (FiniteCascadeGenealogy.leafCount (asGenealogy T)) r*C :=
  abs_followupCavityNativeTerminalExpectation_withinJet_le hn β ρ hβ hρ μ a ha hfloor
    _ (cppTaylorSchedule_antitone p) (by norm_num) rfl rfl T F C hC hF r u hu

theorem abs_followupCavityCppFunction_le (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |followupCavityCppFunction n β ρ hβ hρ μ a p u|≤4 := by
  have hf:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p cavityFourObservationTree
    (cavityCppFourTerminalTest n p) 2 (by norm_num) (cavityCppFourTerminalTest_abs_le p) 0 u hu
  have hg:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppEpsilonTerminalTest n) 1 (by norm_num) cavityCppEpsilonTerminalTest_abs_le 0 u hu
  have hh:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppTauTerminalTest n p) 2 (by norm_num) (cavityCppTauTerminalTest_abs_le p) 0 u hu
  simp only [withinJet,growth,one_mul] at hf hg hh
  unfold followupCavityCppFunction
  have hp : |followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n) u*
      followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
      (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) u|≤2 := by
    rw [abs_mul]
    exact (mul_le_mul hg hh (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (abs_sub _ _).trans ((add_le_add hf hp).trans_eq (by norm_num))

theorem abs_followupCavityCppFunction_firstWithinJet_le (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 u|≤336*β^2 := by
  have hf:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p cavityFourObservationTree
    (cavityCppFourTerminalTest n p) 2 (by norm_num) (cavityCppFourTerminalTest_abs_le p) 1 u hu
  have hg:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppEpsilonTerminalTest n) 1 (by norm_num) cavityCppEpsilonTerminalTest_abs_le 1 u hu
  have hg0:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppEpsilonTerminalTest n) 1 (by norm_num) cavityCppEpsilonTerminalTest_abs_le 0 u hu
  have hh:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppTauTerminalTest n p) 2 (by norm_num) (cavityCppTauTerminalTest_abs_le p) 1 u hu
  have hh0:=cppTaylorFactor_bound hn β ρ hβ hρ μ a ha hfloor p anisotropicBinaryObservationTree
    (cavityCppTauTerminalTest n p) 2 (by norm_num) (cavityCppTauTerminalTest_abs_le p) 0 u hu
  norm_num [growth,cavityFourObservationTree,anisotropicBinaryObservationTree,asGenealogy,
    FiniteCascadeGenealogy.leafCount] at hf hg hh
  simp only [withinJet,growth,one_mul] at hg0 hh0
  rw [followupCavityCppFunction_firstWithinJet_eq_factors hn β ρ hβ hρ μ a ha hfloor p u hu]
  let f:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) cavityFourObservationTree (cavityCppFourTerminalTest n p)
  let g:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)
  let h:=followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p)
  have hp : |withinJet g (Icc 0 1) 1 u*h u|≤7*β^2*4*2 := by
    rw [abs_mul];exact mul_le_mul hg hh0 (abs_nonneg _) (by positivity)
  have hq : |g u*withinJet h (Icc 0 1) 1 u|≤1*(7*β^2*4*2) := by
    rw [abs_mul];exact mul_le_mul hg0 hh (abs_nonneg _) (by positivity)
  have h1:=(abs_sub (withinJet f (Icc 0 1) 1 u) (withinJet g (Icc 0 1) 1 u*h u)).trans
    (add_le_add hf hp)
  have h2:=(abs_sub (withinJet f (Icc 0 1) 1 u-withinJet g (Icc 0 1) 1 u*h u)
    (g u*withinJet h (Icc 0 1) 1 u)).trans (add_le_add h1 hq)
  exact h2.trans_eq (by ring)

theorem measurable_followupCavityCppFunction_firstWithinJet_zero (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) :
    Measurable (fun p : Paper.Overlap=>
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0) := by
  let δ : ℕ→ℝ:=fun j=>1/((j:ℝ)+1)
  have hδ (j):δ j∈Icc (0:ℝ) 1 := by
    dsimp only [δ]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) j])
  have hδ0 (j):δ j≠0:=by dsimp only [δ];positivity
  have htδ : Tendsto δ atTop (𝓝[Icc (0:ℝ) 1\{0}] 0):=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      .of_forall fun j=>⟨hδ j,by simpa only [Set.mem_singleton_iff] using hδ0 j⟩⟩
  have hm (j):Measurable (fun p : Paper.Overlap=>
      (followupCavityCppFunction n β ρ hβ hρ μ a p (δ j)-
        followupCavityCppFunction n β ρ hβ hρ μ a p 0)/(δ j)) :=
    ((measurable_followupCavityCppFunction_split β ρ hβ hρ μ a (δ j) (hδ j)).sub
      (measurable_followupCavityCppFunction_split β ρ hβ hρ μ a 0 ⟨le_rfl,zero_le_one⟩)).div_const _
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.2
  intro p
  have hd:=hasDerivWithinAt_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p
    0 0 ⟨le_rfl,zero_le_one⟩
  have hh:=(hasDerivWithinAt_iff_tendsto_slope.mp hd).comp htδ
  simpa only [Function.comp_def,slope_def_field,sub_zero,withinJet] using hh

theorem integrable_followupCavityCppFunction_firstWithinJet_zero (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) :
    Integrable (fun p : Paper.Overlap=>
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0)
      (parisiFreeMeasure μ a) := by
  apply (integrable_const (336*β^2)).mono'
    (measurable_followupCavityCppFunction_firstWithinJet_zero hn β ρ hβ hρ μ a ha hfloor).aestronglyMeasurable
  exact .of_forall fun p=>by
    rw [Real.norm_eq_abs]
    exact abs_followupCavityCppFunction_firstWithinJet_le hn β ρ hβ hρ μ a ha hfloor p 0 ⟨le_rfl,zero_le_one⟩

theorem measurable_followupCavityCppTaylorRemainder (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) :
    Measurable (followupCavityCppTaylorRemainder n β ρ hβ hρ μ a) := by
  have hm:=(measurable_followupCavityCppFunction_split (n:=n) β ρ hβ hρ μ a 1 ⟨zero_le_one,le_rfl⟩).sub
    (measurable_followupCavityCppFunction_firstWithinJet_zero hn β ρ hβ hρ μ a ha hfloor)
  convert! hm using 1
  funext p
  change followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p=
    followupCavityCppFunction n β ρ hβ hρ μ a p 1-
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0
  linarith [followupCavityCppFunction_taylor hn β ρ hβ hρ μ a ha hfloor p]

theorem integrable_followupCavityCppTaylorRemainder (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a≤Paper.parisiCDF μ 0) :
    Integrable (followupCavityCppTaylorRemainder n β ρ hβ hρ μ a) (parisiFreeMeasure μ a) := by
  have he : Integrable (fun p : Paper.Overlap=>followupCavityCppFunction n β ρ hβ hρ μ a p 1)
      (parisiFreeMeasure μ a) := by
    apply (integrable_const (4:ℝ)).mono'
      (measurable_followupCavityCppFunction_split β ρ hβ hρ μ a 1 ⟨zero_le_one,le_rfl⟩).aestronglyMeasurable
    exact .of_forall fun p=>by
      rw [Real.norm_eq_abs]
      exact abs_followupCavityCppFunction_le hn β ρ hβ hρ μ a ha hfloor p 1 ⟨zero_le_one,le_rfl⟩
  have hh:=he.sub (integrable_followupCavityCppFunction_firstWithinJet_zero hn β ρ hβ hρ μ a ha hfloor)
  convert! hh using 1
  funext p
  change followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p=
    followupCavityCppFunction n β ρ hβ hρ μ a p 1-
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0
  linarith [followupCavityCppFunction_taylor hn β ρ hβ hρ μ a ha hfloor p]

end QuantitativeFollowup
