module
public import QuantitativePaper.VectorMeasureGradient

@[expose] public section

/-! Uniform stability and actual joint continuity of the arbitrary-profile
gradient. Every derivative estimate is proved from the constructed
potential and dimension-only actual Hessian bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

theorem vectorMeasureGradient_CDFDistance_dist_le {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    dist (vectorMeasureGradient μ β t q p x) (vectorMeasureGradient ν β t q p x)≤
      (2*((n : ℝ)*((1-t)*β^2)+(n : ℝ)))*Real.sqrt (Paper.parisiCDFDistance μ ν) := by
  have hμ : vectorMeasureGradient μ β t q p=gradient (vectorMeasureTailPotential μ β t q p) :=
    funext (vectorMeasureGradient_eq_gradient μ β t ht q p)
  have hν : vectorMeasureGradient ν β t q p=gradient (vectorMeasureTailPotential ν β t q p) :=
    funext (vectorMeasureGradient_eq_gradient ν β t ht q p)
  rw [dist_eq_norm]
  have hh := norm_gradient_sub_le_sqrt_of_uniform_sub
    (vectorMeasureTailPotential μ β t q p) (vectorMeasureTailPotential ν β t q p)
    (fun y => (hasFDerivAt_vectorMeasureTailPotential μ β t ht q p y).differentiableAt)
    (fun y => (hasFDerivAt_vectorMeasureTailPotential ν β t ht q p y).differentiableAt)
    (n : ℝ≥0) (by rw [←hμ];exact vectorMeasureGradient_lipschitz μ β t ht q p)
    (by rw [←hν];exact vectorMeasureGradient_lipschitz ν β t ht q p)
    ((n : ℝ)*((1-t)*β^2)) (Paper.parisiCDFDistance μ ν) (by positivity)
    (Paper.parisiCDFDistance_nonneg μ ν)
    (fun y => vectorMeasureTailPotential_CDFDistance_abs_sub_le μ ν β t q ht q.property p y) x
  simpa only [←hμ,←hν,NNReal.coe_natCast] using hh

theorem tendstoUniformly_vectorMeasureGradient_of_CDFDistance {n : ℕ}
    {ι : Type*} {L : Filter ι} {ν : ι→Paper.ParisiMeasure} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1)
    (hD : Tendsto (fun i => Paper.parisiCDFDistance (ν i) μ) L (𝓝 0)) :
    TendstoUniformly (fun i => fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureGradient (ν i) β t z.1 z.2.1 z.2.2)
      (fun z => vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) L := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh : Tendsto (fun i => (2*((n : ℝ)*((1-t)*β^2)+(n : ℝ)))*
      Real.sqrt (Paper.parisiCDFDistance (ν i) μ)) L (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using hD.sqrt.const_mul
      (2*((n : ℝ)*((1-t)*β^2)+(n : ℝ)))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with i hi
  intro z
  rw [dist_comm]
  exact (vectorMeasureGradient_CDFDistance_dist_le (ν i) μ β t ht z.1 z.2.1 z.2.2).trans_lt hi

theorem tendstoUniformly_vectorMeasureGradient_of_weak {n : ℕ}
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {ν : ι→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (β t : ℝ) (ht : t≤1)
    (hν : Tendsto ν L (𝓝 μ)) :
    TendstoUniformly (fun i => fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureGradient (ν i) β t z.1 z.2.1 z.2.2)
      (fun z => vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) L :=
  tendstoUniformly_vectorMeasureGradient_of_CDFDistance μ β t ht
    (FRSB.tendsto_parisiCDFDistance_of_tendsto hν)

theorem vectorMeasureGradient_time_disorder_dist_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q r : Paper.Overlap) (p z : Couplings n×ℝ) (x : Field n) :
    dist (vectorMeasureGradient μ β t q p x) (vectorMeasureGradient μ β t r z x)≤
      2*(1+(n : ℝ))*Real.sqrt (((n : ℝ)*((1-t)*β^2)/2)*dist q r+
        (vectorJointLipschitzConstant n β t : ℝ)*dist p z) := by
  let d := ((n : ℝ)*((1-t)*β^2)/2)*dist q r+
    (vectorJointLipschitzConstant n β t : ℝ)*dist p z
  have hd : 0≤d := by dsimp only [d];positivity
  have hb (y : Field n) : |vectorMeasureTailPotential μ β t q p y-
      vectorMeasureTailPotential μ β t r z y|≤1*d := by
    rw [one_mul]
    calc
      _ ≤ |vectorMeasureTailPotential μ β t q p y-vectorMeasureTailPotential μ β t r p y|+
        |vectorMeasureTailPotential μ β t r p y-vectorMeasureTailPotential μ β t r z y| := abs_sub_le _ _ _
      _ ≤ d := by
        have htime := vectorMeasureTailPotential_time_abs_sub_le μ β t q r ht q.property r.property p y
        have hdis := (vectorMeasureTailPotential_joint_lipschitz μ β t r ht r.property).dist_le_mul
          (p,y) (z,y)
        rw [Real.dist_eq,Prod.dist_eq,dist_self,max_eq_left dist_nonneg] at hdis
        exact add_le_add htime hdis
  have hq : vectorMeasureGradient μ β t q p=gradient (vectorMeasureTailPotential μ β t q p) :=
    funext (vectorMeasureGradient_eq_gradient μ β t ht q p)
  have hr : vectorMeasureGradient μ β t r z=gradient (vectorMeasureTailPotential μ β t r z) :=
    funext (vectorMeasureGradient_eq_gradient μ β t ht r z)
  rw [dist_eq_norm]
  have hh := norm_gradient_sub_le_sqrt_of_uniform_sub
    (vectorMeasureTailPotential μ β t q p) (vectorMeasureTailPotential μ β t r z)
    (fun y => (hasFDerivAt_vectorMeasureTailPotential μ β t ht q p y).differentiableAt)
    (fun y => (hasFDerivAt_vectorMeasureTailPotential μ β t ht r z y).differentiableAt)
    (n : ℝ≥0) (by rw [←hq];exact vectorMeasureGradient_lipschitz μ β t ht q p)
    (by rw [←hr];exact vectorMeasureGradient_lipschitz μ β t ht r z)
    1 d (by norm_num) hd hb x
  simpa only [←hq,←hr,NNReal.coe_natCast] using hh

theorem continuous_vectorMeasureGradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Continuous (fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb (w : Paper.Overlap×VectorParameter n) :
      dist (vectorMeasureGradient μ β t w.1 w.2.1 w.2.2)
        (vectorMeasureGradient μ β t z.1 z.2.1 z.2.2)≤
      2*(1+(n : ℝ))*Real.sqrt (((n : ℝ)*((1-t)*β^2)/2)*dist w.1 z.1+
        (vectorJointLipschitzConstant n β t : ℝ)*dist w.2.1 z.2.1)+(n : ℝ)*dist w.2.2 z.2.2 := by
    exact (dist_triangle _ _ _).trans (add_le_add
      (vectorMeasureGradient_time_disorder_dist_le μ β t ht w.1 z.1 w.2.1 z.2.1 w.2.2)
      ((vectorMeasureGradient_lipschitz μ β t ht z.1 z.2.1).dist_le_mul w.2.2 z.2.2))
  have hh : Continuous (fun w : Paper.Overlap×VectorParameter n =>
      2*(1+(n : ℝ))*Real.sqrt (((n : ℝ)*((1-t)*β^2)/2)*dist w.1 z.1+
        (vectorJointLipschitzConstant n β t : ℝ)*dist w.2.1 z.2.1)+(n : ℝ)*dist w.2.2 z.2.2) := by
    fun_prop
  apply squeeze_zero (fun w => dist_nonneg) hb
  simpa using hh.tendsto z

end QuantitativePaper
