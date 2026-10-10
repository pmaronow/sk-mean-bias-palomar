module
public import Paper.ParisiSolutionSlabs
public import Paper.ParisiTimeRegularity
public import QuantitativePaper.UniformScalarHeat

@[expose] public section

/-! The actual scalar gradient and its spatial derivatives in energy
coordinates. Gaussian noise has variance b-q, and the coefficient is
literally beta times the CDF of the original minimizing measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 2000000

def scalarEnergySpatialJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (p : ℝ×ℝ) : ℝ :=
  β^j*parisiSpatialField β μ (j+1) (p.1,β*p.2)

def scalarEnergySquareJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (p : ℝ×ℝ) : ℝ :=
  β^j*parisiSquareSpatialField β μ j (p.1,β*p.2)

theorem continuous_scalarEnergySpatialJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ) :
    Continuous (scalarEnergySpatialJet β μ j) := by
  unfold scalarEnergySpatialJet
  exact continuous_const.mul ((continuous_parisiSpatialField β μ (j+1)).comp (by fun_prop))

theorem continuous_scalarEnergySquareJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ) :
    Continuous (scalarEnergySquareJet β μ j) := by
  unfold scalarEnergySquareJet
  exact continuous_const.mul ((continuous_parisiSquareSpatialField β μ j).comp (by fun_prop))

theorem scalarEnergySpatialJet_bounded (β : ℝ) (μ : ParisiMeasure) (j : ℕ) :
    ∃ M : ℝ,0≤M ∧ ∀p,‖scalarEnergySpatialJet β μ j p‖≤M := by
  obtain ⟨M,hM⟩:=parisiSpatialField_bounded β μ j
  refine ⟨‖β^j‖*M,mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hM (0,0))),?_⟩
  intro p
  exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))

theorem scalarEnergySquareJet_bounded (β : ℝ) (μ : ParisiMeasure) (j : ℕ) :
    ∃ M : ℝ,0≤M ∧ ∀p,‖scalarEnergySquareJet β μ j p‖≤M := by
  obtain ⟨M,hM⟩:=parisiSquareSpatialField_bounded β μ j
  refine ⟨‖β^j‖*M,mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hM (0,0))),?_⟩
  intro p
  exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))

theorem hasDerivAt_scalarEnergySpatialJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    HasDerivAt (fun y=>scalarEnergySpatialJet β μ j (q,y))
      (scalarEnergySpatialJet β μ (j+1) (q,x)) x := by
  have hd:=(hasDerivAt_parisiSpatialField β μ (j+1) q (β*x) hq).comp x
    ((hasDerivAt_id x).const_mul β)
  convert hd.const_mul (β^j) using 1
  · rfl
  · dsimp [scalarEnergySpatialJet]
    rw [pow_succ]
    ring

theorem hasDerivAt_scalarEnergySquareJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (q x : ℝ) :
    HasDerivAt (fun y=>scalarEnergySquareJet β μ j (q,y))
      (scalarEnergySquareJet β μ (j+1) (q,x)) x := by
  have hd:=(hasDerivAt_parisiSquareSpatialField β μ j q (β*x)).comp x
    ((hasDerivAt_id x).const_mul β)
  convert hd.const_mul (β^j) using 1
  · rfl
  · dsimp [scalarEnergySquareJet]
    rw [pow_succ]
    ring

@[simp] theorem scalarEnergySpatialJet_zero (β : ℝ) (μ : ParisiMeasure) (p : ℝ×ℝ) :
    scalarEnergySpatialJet β μ 0 p=parisiGradient β μ (p.1,β*p.2) := by
  simp [scalarEnergySpatialJet]

@[simp] theorem scalarEnergySquareJet_zero (β : ℝ) (μ : ParisiMeasure) (p : ℝ×ℝ) :
    scalarEnergySquareJet β μ 0 p=(scalarEnergySpatialJet β μ 0 p)^2 := by
  simp [scalarEnergySquareJet]

theorem norm_scalarEnergySpatialJet_zero_le_one (β : ℝ) (μ : ParisiMeasure) (p : ℝ×ℝ) :
    ‖scalarEnergySpatialJet β μ 0 p‖≤1 := by
  rw [scalarEnergySpatialJet_zero]
  exact norm_parisiGradient_le_one β μ _

theorem heatSemigroup_scalar_scale (β : ℝ) (hβ : 0<β) (v : ℝ) (hv : 0≤v)
    (f : ℝ→ℝ) (x : ℝ) :
    heatSemigroup (β^2*v) f (β*x)=heatSemigroup v (fun y=>f (β*y)) x := by
  unfold heatSemigroup gaussianExpectation
  have hs : Real.sqrt (β^2*v)=β*Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq_eq_abs,abs_of_pos hβ]
  rw [hs]
  congr 1
  funext z
  congr 1
  ring

theorem heatGradient_scalar_scale (β : ℝ) (hβ : 0<β) (v : ℝ) (hv : 0≤v)
    (f : ℝ→ℝ) (x : ℝ) :
    heatGradient (β^2*v) f (β*x)=β⁻¹*heatGradient v (fun y=>f (β*y)) x := by
  unfold heatGradient gaussianExpectation
  have hs : Real.sqrt (β^2*v)=β*Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq_eq_abs,abs_of_pos hβ]
  rw [hs,mul_inv_rev]
  have he : (fun z : ℝ=>z*f (β*x+β*Real.sqrt v*z))=
      (fun z : ℝ=>z*f (β*(x+Real.sqrt v*z))) := by
    funext z
    congr 2
    ring
  rw [he]
  ring

theorem scalarEnergySpatialJet_mild (β : ℝ) (hβ : 0<β) (μ : ParisiMeasure)
    (b q x : ℝ) (hb : b∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) b) :
    scalarEnergySpatialJet β μ 0 (q,x)=
      heatSemigroup (b-q) (fun y=>scalarEnergySpatialJet β μ 0 (b,y)) x+
      (1/2:ℝ)*(∫s in q..b,(β*parisiCDF μ s)*heatGradient (s-q)
        (fun y=>(scalarEnergySpatialJet β μ 0 (s,y))^2) x) := by
  have hm:=parisiGradientBCF_mildOnEverySlab_all β μ b hb q hq (β*x)
  change parisiGradient β μ (q,β*x)=
    heatSemigroup (β^2*(b-q)) (fun y=>parisiGradient β μ (b,y)) (β*x)+
      parisiGradientCorrection β μ (parisiGradient β μ) b q (β*x) at hm
  simp only [scalarEnergySpatialJet_zero]
  rw [hm,heatSemigroup_scalar_scale β hβ (b-q) (sub_nonneg.mpr hq.2)]
  congr 1
  unfold parisiGradientCorrection parisiGradientSource
  rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro s hs
  rw [uIoo_of_le hq.2] at hs
  change β^2/2*(parisiCDF μ s*heatGradient (β^2*(s-q))
    (fun y=>parisiGradient β μ (s,y)^2) (β*x))=
      (1/2:ℝ)*(β*parisiCDF μ s*heatGradient (s-q)
        (fun y=>parisiGradient β μ (s,β*y)^2) x)
  rw [heatGradient_scalar_scale β hβ (s-q) (sub_nonneg.mpr hs.1.le)]
  field_simp
  <;> ring

end QuantitativePaper
