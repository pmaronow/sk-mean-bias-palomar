module
public import QuantitativePaper.GaussianColeHopfCoordinateSmoothing
public import QuantitativePaper.GaussianColeHopfCoordinateComposition
public import QuantitativePaper.VectorProfileSignedGrowth
public import QuantitativePaper.VectorProfileSmooth

@[expose] public section

/-! The actual finite affine-mass profile is jointly smooth through both
parameter endpoints. Bounded-cylinder exponential jet bounds hold for all
real profile parameters, including zero and negative intermediate masses. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

theorem vectorProfileJointFunction_step_as_gaussianColeHopf {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (j : ℕ) (x : ℝ×VectorParameter n) :
    vectorProfileJointFunction s₀ s₁ β t (j+1) x =
      gaussianShiftColeHopf (vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j))
        (vectorProfileStepMass s₀ s₁ j x) (vectorProfileJointFunction s₀ s₁ β t j) x := by
  rw [vectorProfileJointFunction_step_eq]
  unfold gaussianShiftColeHopf
  split_ifs with hm
  · rfl
  · rw [div_eq_mul_inv,mul_comm]
    congr 2
    unfold gaussianShiftPartition
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp only
      rw [vectorProfileJointShift_add]
      simp only [one_mul,vectorProfileStepMass]

theorem vectorProfileJointFunction_smooth_exp_jets_all_theta {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (N j : ℕ) (a b : ℝ) :
    ContDiffOn ℝ N (vectorProfileJointFunction (n:=n) s₀ s₁ β t j)
      {z : ℝ×VectorParameter n | z.1∈Ioo a b} ∧
      ∃ K D : ℝ, 1 ≤ K ∧1 ≤ D ∧ ∀ r,1 ≤ r → r ≤ N →
        ∀ x : ℝ×VectorParameter n,x.1∈Ioo a b →
          ‖iteratedFDeriv ℝ r (vectorProfileJointFunction s₀ s₁ β t j) x‖ ≤ 
            (K*Real.exp (D*‖x‖))^r := by
  let U : Set (ℝ×VectorParameter n) := {z | z.1∈Ioo a b}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  induction j generalizing N with
  | zero =>
    have hf := (boundedPositiveJets_vectorRecursion_joint (n:=n) s₀ β t 0).comp_linear
      (ContinuousLinearMap.snd ℝ ℝ (VectorParameter n))
    have hf' : BoundedPositiveJets (vectorProfileJointFunction (n:=n) s₀ s₁ β t 0) := hf
    obtain ⟨K,hK,hj⟩ := boundedPositiveJets_power_bound _ hf' N
    refine ⟨(hf'.1.of_le (by simp)).contDiffOn,K,1,hK,le_rfl,?_⟩
    intro r hr0 hr x hx
    exact (hj r hr0 hr x).trans (pow_le_pow_left₀ (zero_le_one.trans hK)
      (le_mul_of_one_le_right (zero_le_one.trans hK) (Real.one_le_exp_iff.mpr (by positivity))) r)
  | succ j ih =>
    obtain ⟨hf,K,D,hK,hD,hfj⟩ := ih (N+1)
    let f := vectorProfileJointFunction (n:=n) s₀ s₁ β t j
    let m := vectorProfileStepMass (n:=n) s₀ s₁ j
    let A := vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j)
    have hshift : ∀ x∈U, ∀ z,x+A z∈U := by
      intro x hx z
      rw [vectorProfileJointShift_add]
      exact hx
    obtain ⟨B,L,hB,hL,hvalue⟩ := vectorProfileJointFunction_linear_growth_all_theta (n:=n)
      s₀ s₁ β t j a b
    have hv : ∀ x∈U, |f x| ≤ B+L*‖x‖ := fun x hx => hvalue x ⟨hx.1.le,hx.2.le⟩
    let H := (vectorJointLipschitzConstant n β t:ℝ)*‖vectorJointShift n (vectorProfileStepVariance s₀ β t j)‖
    have hlip : ∀ x∈U, ∀ z,|f (x+A z)-f x| ≤ H*‖z‖ :=
      fun x _ z => vectorProfileJointFunction_shift_lipschitz_all_theta s₀ s₁ β t _ j x z
    obtain ⟨M,hM,hmass⟩ := exists_vectorProfileMass_cylinder_bound (n:=n) s₀ s₁ (k+1-j) 0 a b
    let R := M+1
    have hR : 0 < R := by dsimp [R];linarith
    have hm (x : ℝ×VectorParameter n) (hx : x∈U) : |m x|<R := by
      have hb := hmass 0 le_rfl x ⟨hx.1.le,hx.2.le⟩
      simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
      exact hb.trans_lt (by dsimp [R];linarith)
    obtain ⟨hg,C,Q,hC,hQ,hgj⟩ := gaussianMassColeHopf_smooth_exp_jets_on_open N f U hU hf A hshift
      B L K D H R hB hL hK (zero_le_one.trans hD) hR hv hfj hlip
    let Lm : (ℝ×VectorParameter n) →L[ℝ] ℝ :=
      (s₁.m (k+1-j)-s₀.m (k+1-j)) • ContinuousLinearMap.fst ℝ ℝ (VectorParameter n)
    let Lg : (ℝ×VectorParameter n) →L[ℝ] ℝ×(ℝ×VectorParameter n) :=
      Lm.prod (ContinuousLinearMap.id ℝ (ℝ×VectorParameter n))
    let c : ℝ×(ℝ×VectorParameter n) := (s₀.m (k+1-j),0)
    have heGraph (x : ℝ×VectorParameter n) : Lg x+c=(m x,x) := by
      apply Prod.ext
      · change (s₁.m (k+1-j)-s₀.m (k+1-j))*x.1+s₀.m (k+1-j)=m x
        unfold m vectorProfileStepMass vectorProfileMass
        ring
      · simp [Lg,c]
    have hmap : ∀ x∈U,Lg x+c∈gaussianMassCylinder R U := by
      intro x hx
      rw [heGraph]
      exact ⟨abs_lt.mp (hm x hx),hx⟩
    obtain ⟨hs,C',Q',hC',hQ',hsj⟩ := affine_smooth_exp_jets_on_open N (gaussianMassColeHopf A f)
      (gaussianMassCylinder R U) (gaussianMassCylinder_open R U hU) hg Lg c U hU hmap
      C Q hC (zero_le_one.trans hQ) hgj
    have he : EqOn (vectorProfileJointFunction (n:=n) s₀ s₁ β t (j+1))
        (fun x => gaussianMassColeHopf A f (Lg x+c)) U := by
      intro x hx
      change vectorProfileJointFunction s₀ s₁ β t (j+1) x=gaussianMassColeHopf A f (Lg x+c)
      rw [heGraph]
      exact vectorProfileJointFunction_step_as_gaussianColeHopf s₀ s₁ β t j x
    refine ⟨hs.congr he,C',Q',hC',hQ',?_⟩
    intro r hr0 hr x hx
    have hev : vectorProfileJointFunction (n:=n) s₀ s₁ β t (j+1) =ᶠ[𝓝 x]
        (fun y => gaussianMassColeHopf A f (Lg y+c)) :=
      mem_of_superset (hU.mem_nhds hx) (fun y hy => he hy)
    rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hsj r hr0 hr x hx

theorem contDiff_vectorProfileJointFunction_all_theta {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (vectorProfileJointFunction (n:=n) s₀ s₁ β t j) := by
  apply contDiff_infty.mpr
  intro N
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨hf,_⟩ := vectorProfileJointFunction_smooth_exp_jets_all_theta (n:=n)
    s₀ s₁ β t N j (x.1-1) (x.1+1)
  have hU : IsOpen {z : ℝ×VectorParameter n | z.1∈Ioo (x.1-1) (x.1+1)} :=
    isOpen_Ioo.preimage continuous_fst
  exact hf.contDiffAt (hU.mem_nhds (by constructor <;> linarith))

theorem vectorProfileJointFunction_exp_jets_on_closed_cylinder {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (N j : ℕ) (a b : ℝ) :
    ∃ K D : ℝ,1 ≤ K ∧1 ≤ D ∧ ∀ r,1 ≤ r → r ≤ N →
      ∀ x : ℝ×VectorParameter n,x.1∈Icc a b →
        ‖iteratedFDeriv ℝ r (vectorProfileJointFunction s₀ s₁ β t j) x‖ ≤
          (K*Real.exp (D*‖x‖))^r := by
  obtain ⟨_,K,D,hK,hD,hj⟩ := vectorProfileJointFunction_smooth_exp_jets_all_theta (n:=n)
    s₀ s₁ β t N j (a-1) (b+1)
  refine ⟨K,D,hK,hD,?_⟩
  intro r hr0 hr x hx
  exact hj r hr0 hr x ⟨by linarith [hx.1],by linarith [hx.2]⟩

end QuantitativePaper
