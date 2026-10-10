module
public import QuantitativePaper.VectorProfileCellSmooth
public import QuantitativePaper.VectorGaussianLowerPropagation
public import QuantitativePaper.VectorVarianceBounds

@[expose] public section

/-! True exponential partition lower bounds and linear value growth for
the actual variable-overlap affine-profile Gaussian cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellPartition (s₀ s₁ : RSBScheme k) (β t c Q : ℝ) (i j : ℕ)
    (w : ℝ×(ℝ×VectorParameter n)) : ℝ:=
  ∫z,Real.exp (vectorProfileCellExponent s₀ s₁ β t i j
    (vectorProfileCellEvaluation c Q z w)) ∂fieldGaussian n

theorem vectorProfileCellPartition_eq_step (s₀ s₁ : RSBScheme k)
    (β t c Q : ℝ) (i j : ℕ) (w : ℝ×(ℝ×VectorParameter n)) :
    vectorProfileCellPartition s₀ s₁ β t c Q i j w=
      vectorStepPartition (c*(Q-w.1)) (vectorProfileMass s₀ s₁ w.2.1 i)
        (vectorProfileRecursion s₀ s₁ β t w.2.1 w.2.2.1 j) w.2.2.2 := by
  simp only [vectorProfileCellPartition,vectorProfileCellExponent,vectorProfileCellEvaluation_eq,
    vectorProfileJointFunction,vectorStepPartition]

theorem exists_vectorProfileCellPartition_exponential_lower (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (c Q l u a b : ℝ) (hc : 0<c) (hu : u<Q)
    (ha : 0<a) (hb : b<1) (i j : ℕ) (hi : i≤k+1) :
    ∃d D : ℝ,0<d ∧ 0≤D ∧ ∀w∈vectorProfileCellCylinder (n:=n) l u a b,
      d*Real.exp (-D*‖w‖)≤vectorProfileCellPartition s₀ s₁ β t c Q i j w := by
  obtain ⟨B,L,hB,hL,hvalue⟩:=vectorProfileJointFunction_linear_growth
    (n:=n) s₀ s₁ β t ht j
  let H:=Real.sqrt (n:ℝ)*Real.sqrt (c*(Q-l))
  let d:=Real.exp (-B)*vectorGaussianNormLaplace n (-H)
  refine ⟨d,L,mul_pos (Real.exp_pos _) (vectorGaussianNormLaplace_pos _ _),hL,?_⟩
  intro w hw
  have hθ : w.2.1∈Icc (0:ℝ) 1:=⟨(ha.trans hw.2.1).le,(hw.2.2.trans hb).le⟩
  let f:=vectorProfileRecursion s₀ s₁ β t w.2.1 w.2.2.1 j
  let m:=vectorProfileMass s₀ s₁ w.2.1 i
  let v:=c*(Q-w.1)
  have hmass : m∈Icc (0:ℝ) 1:=vectorProfileMass_mem_unit s₀ s₁ i hi w.2.1 hθ
  have hfl : LipschitzWith (Real.sqrt (n:ℝ)).toNNReal f:=
    vectorProfileRecursion_lipschitz s₀ s₁ β t w.2.1 hθ w.2.2.1 j
  have hbase : |f w.2.2.2|≤B+L*‖w‖:=by
    exact (hvalue w.2 hθ).trans (add_le_add (le_refl B)
      (mul_le_mul_of_nonneg_left (norm_snd_le w) hL))
  have hsqrt : Real.sqrt v≤Real.sqrt (c*(Q-l)):=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith [hw.1.1]) hc.le)
  have hpoint (z : Field n) : -B-L*‖w‖-H*‖z‖ ≤ m*f (fieldShift v w.2.2.2 z):=by
    have hshift:=abs_fieldShift_sub_lipschitz f _ hfl v w.2.2.2 z
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at hshift
    have hh : |f (fieldShift v w.2.2.2 z)|≤B+L*‖w‖+H*‖z‖:=by
      have htri:=abs_add_le (f w.2.2.2) (f (fieldShift v w.2.2.2 z)-f w.2.2.2)
      rw [add_sub_cancel] at htri
      apply htri.trans
      apply add_le_add hbase
      apply hshift.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) (norm_nonneg _)
    have hmabs : |m*f (fieldShift v w.2.2.2 z)|≤|f (fieldShift v w.2.2.2 z)|:=by
      rw [abs_mul,abs_of_nonneg hmass.1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass.2 (abs_nonneg _)
    linarith [neg_abs_le (m*f (fieldShift v w.2.2.2 z))]
  rw [vectorProfileCellPartition_eq_step,vectorStepPartition]
  have hm:=integral_mono
    ((SYK.integrable_exp_mul_norm (ι:=Fin n) (-H)).const_mul (Real.exp (-B-L*‖w‖)))
    (integrable_exp_vectorStep f _ hfl v m w.2.2.2)
    (fun z=>by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hpoint z]))
  apply le_trans _ hm
  dsimp only [d,vectorGaussianNormLaplace]
  rw [integral_const_mul,Real.exp_sub,Real.exp_neg]
  ring_nf
  rw [Real.exp_neg]

theorem vectorProfileCellFunction_linear_growth (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (c Q l u a b : ℝ) (hc : 0<c) (hu : u<Q)
    (ha : 0<a) (hb : b<1) (i j : ℕ) (hi : i≤k+1) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀w∈vectorProfileCellCylinder (n:=n) l u a b,
      |vectorProfileCellFunction s₀ s₁ β t c Q i j w|≤B+L*‖w‖ := by
  obtain ⟨B,L,hB,hL,hbase⟩:=vectorProfileJointFunction_linear_growth
    (n:=n) s₀ s₁ β t ht j
  refine ⟨B+(n:ℝ)/2*|c*(Q-l)|,L,by positivity,hL,?_⟩
  intro w hw
  have hθ : w.2.1∈Icc (0:ℝ) 1:=⟨(ha.trans hw.2.1).le,(hw.2.2.trans hb).le⟩
  have hv : 0≤c*(Q-w.1):=mul_nonneg hc.le (sub_nonneg.mpr (hw.1.2.trans hu).le)
  have hvmax : c*(Q-w.1)≤|c*(Q-l)|:=
    (mul_le_mul_of_nonneg_left (by linarith [hw.1.1]) hc.le).trans (le_abs_self _)
  have hstep:=vectorColeHopfStep_recursion_variance_sub_bounds
    (vectorProfileScheme s₀ s₁ w.2.1 hθ) β t w.2.2.1 j
    (vectorProfileMass s₀ s₁ w.2.1 i) (vectorProfileMass_mem_unit s₀ s₁ i hi w.2.1 hθ)
    0 (c*(Q-w.1)) (le_refl _) hv w.2.2.2
  rw [vectorColeHopfStep_zero_variance,sub_zero] at hstep
  rw [←vectorProfileRecursion_eq_scheme s₀ s₁ β t w.2.1 hθ] at hstep
  obtain ⟨hstep0,hstep1⟩:=hstep
  change 0≤vectorProfileCellFunction s₀ s₁ β t c Q i j w-
    vectorProfileJointFunction s₀ s₁ β t j w.2 at hstep0
  change vectorProfileCellFunction s₀ s₁ β t c Q i j w-
    vectorProfileJointFunction s₀ s₁ β t j w.2≤_ at hstep1
  have htri:=abs_add_le (vectorProfileJointFunction s₀ s₁ β t j w.2)
    (vectorProfileCellFunction s₀ s₁ β t c Q i j w-
      vectorProfileJointFunction s₀ s₁ β t j w.2)
  rw [add_sub_cancel,abs_of_nonneg hstep0] at htri
  have hb0:=(hbase w.2 hθ).trans (add_le_add (le_refl B)
    (mul_le_mul_of_nonneg_left (norm_snd_le w) hL))
  have hvb:=mul_le_mul_of_nonneg_left hvmax (show 0≤(n:ℝ)/2 by positivity)
  linarith [hstep1]

theorem vectorProfileCellPartition_log_linear_growth (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (c Q l u a b : ℝ) (hc : 0<c) (hu : u<Q)
    (ha : 0<a) (hb : b<1) (i j : ℕ) (hi : i≤k+1)
    (hmpos : ∀θ∈Ioo (0:ℝ) 1,0<vectorProfileMass s₀ s₁ θ i) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀w∈vectorProfileCellCylinder (n:=n) l u a b,
      |Real.log (vectorProfileCellPartition s₀ s₁ β t c Q i j w)|≤B+L*‖w‖ := by
  obtain ⟨B,L,hB,hL,hvalue⟩:=vectorProfileCellFunction_linear_growth
    (n:=n) s₀ s₁ β t ht c Q l u a b hc hu ha hb i j hi
  refine ⟨B,L,hB,hL,?_⟩
  intro w hw
  have hθ : w.2.1∈Ioo (0:ℝ) 1:=⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  have hm:=hmpos w.2.1 hθ
  have hu0:=vectorProfileMass_mem_unit s₀ s₁ i hi w.2.1 ⟨hθ.1.le,hθ.2.le⟩
  have heq : Real.log (vectorProfileCellPartition s₀ s₁ β t c Q i j w)=
    vectorProfileMass s₀ s₁ w.2.1 i*vectorProfileCellFunction s₀ s₁ β t c Q i j w := by
    rw [vectorProfileCellFunction_eq_average_partition,if_neg hm.ne']
    change _=_*((_)⁻¹*Real.log (vectorProfileCellPartition s₀ s₁ β t c Q i j w))
    field_simp
  rw [heq,abs_mul,abs_of_pos hm]
  exact (mul_le_mul_of_nonneg_right hu0.2 (abs_nonneg _)).trans
    (by simpa only [one_mul] using hvalue w hw)

end QuantitativePaper
