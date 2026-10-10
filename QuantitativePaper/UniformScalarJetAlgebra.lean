module
public import QuantitativePaper.UniformScalarMildJets
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-! Exact low-order square-jet formulas in the actual energy coordinates.
They isolate the only highest-order term, twice p times its current jet. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 1600000

theorem scalarEnergySpatialJet_eq_iteratedDeriv (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySpatialJet β μ j (q,x)=
      iteratedDeriv j (fun y=>scalarEnergySpatialJet β μ 0 (q,y)) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ,←funext ih]
    exact (hasDerivAt_scalarEnergySpatialJet β μ j q x hq).deriv.symm

theorem scalarEnergySquareJet_eq_iteratedDeriv (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (q x : ℝ) :
    scalarEnergySquareJet β μ j (q,x)=
      iteratedDeriv j (fun y=>(scalarEnergySpatialJet β μ 0 (q,y))^2) x := by
  induction j generalizing x with
  | zero => exact scalarEnergySquareJet_zero β μ (q,x)
  | succ j ih =>
    rw [iteratedDeriv_succ,←funext ih]
    exact (hasDerivAt_scalarEnergySquareJet β μ j q x).deriv.symm

theorem scalarEnergySquareJet_expansion (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySquareJet β μ j (q,x)=
      ∑i∈Finset.range (j+1),(j.choose i:ℝ)*scalarEnergySpatialJet β μ i (q,x)*
        scalarEnergySpatialJet β μ (j-i) (q,x) := by
  have hc : ContDiff ℝ j (fun y=>scalarEnergySpatialJet β μ 0 (q,y)) := by
    simp only [scalarEnergySpatialJet_zero]
    exact ((contDiff_parisiGradient_spatial β μ q).comp (contDiff_const.mul contDiff_id)).of_le (by simp)
  rw [scalarEnergySquareJet_eq_iteratedDeriv]
  have he:=iteratedDeriv_fun_mul hc.contDiffAt hc.contDiffAt (x:=x)
  simp only [←pow_two] at he
  rw [he]
  simp_rw [←scalarEnergySpatialJet_eq_iteratedDeriv β μ _ q _ hq]

theorem scalarEnergySquareJet_one (β : ℝ) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySquareJet β μ 1 (q,x)=
      2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 1 (q,x) := by
  rw [scalarEnergySquareJet_expansion β μ 1 q x hq]
  norm_num [Finset.sum_range_succ]
  <;> ring

theorem scalarEnergySquareJet_two (β : ℝ) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySquareJet β μ 2 (q,x)=
      2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)+
        2*(scalarEnergySpatialJet β μ 1 (q,x))^2 := by
  rw [scalarEnergySquareJet_expansion β μ 2 q x hq]
  norm_num [Finset.sum_range_succ]
  <;> ring

theorem scalarEnergySquareJet_three (β : ℝ) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySquareJet β μ 3 (q,x)=
      2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 3 (q,x)+
        6*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x) := by
  rw [scalarEnergySquareJet_expansion β μ 3 q x hq]
  norm_num [Finset.sum_range_succ]
  <;> ring

theorem scalarEnergySquareJet_four (β : ℝ) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySquareJet β μ 4 (q,x)=
      2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 4 (q,x)+
        8*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 3 (q,x)+
        6*(scalarEnergySpatialJet β μ 2 (q,x))^2 := by
  rw [scalarEnergySquareJet_expansion β μ 4 q x hq]
  norm_num [Finset.sum_range_succ,show Nat.choose 4 2=6 by decide]
  <;> ring

theorem scalarEnergySquareJet_norm_bound (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (hj : j≤4) (q x C : ℝ) (hq : q∈Icc (0:ℝ) 1) (hC : 0≤C)
    (hb : ∀i≤j,‖scalarEnergySpatialJet β μ i (q,x)‖≤C) :
    ‖scalarEnergySquareJet β μ j (q,x)‖≤16*C^2 := by
  rw [scalarEnergySquareJet_expansion β μ j q x hq]
  have hterms (i : ℕ) (hi : i∈Finset.range (j+1)) :
      ‖(j.choose i:ℝ)*scalarEnergySpatialJet β μ i (q,x)*
        scalarEnergySpatialJet β μ (j-i) (q,x)‖≤(j.choose i:ℝ)*C^2 := by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hh:=mul_le_mul (hb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
      (hb (j-i) (Nat.sub_le _ _)) (norm_nonneg _) hC
    exact (by simpa only [pow_two,mul_assoc] using
      mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (j.choose i)))
  calc
    _≤∑i∈Finset.range (j+1),(j.choose i:ℝ)*C^2 :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterms)
    _≤16*C^2 := by
      rw [←Finset.sum_mul]
      have hh : (∑i∈Finset.range (j+1),(j.choose i:ℝ))≤16 := by
        interval_cases j <;> norm_num [Finset.sum_range_succ,show Nat.choose 4 2=6 by decide]
      exact mul_le_mul_of_nonneg_right hh (sq_nonneg C)

theorem scalarEnergySquareJet_remainder_bound (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (q x C : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (hC : 0≤C) (hb : ∀i<j,‖scalarEnergySpatialJet β μ i (q,x)‖≤C) :
    ‖scalarEnergySquareJet β μ j (q,x)-
      2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ j (q,x)‖≤14*C^2 := by
  have hp (i k : ℕ) (hi : i<j) (hk : k<j) :
      ‖scalarEnergySpatialJet β μ i (q,x)*scalarEnergySpatialJet β μ k (q,x)‖≤C^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul (hb i hi) (hb k hk) (norm_nonneg _) hC
  have hqpow (i : ℕ) (hi : i<j) : ‖scalarEnergySpatialJet β μ i (q,x)^2‖≤C^2 := by
    simpa only [pow_two] using hp i i hi hi
  obtain ⟨hj0,hj4⟩:=Finset.mem_Icc.mp hj
  interval_cases j
  · simp only [scalarEnergySquareJet_one β μ q x hq,sub_self,norm_zero]
    positivity
  · rw [scalarEnergySquareJet_two β μ q x hq,add_sub_cancel_left,norm_mul]
    norm_num only [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2), Real.norm_of_nonneg (by norm_num : (0:ℝ)≤6), Real.norm_of_nonneg (by norm_num : (0:ℝ)≤8)]
    nlinarith [hqpow 1 (by norm_num)]
  · rw [scalarEnergySquareJet_three β μ q x hq,add_sub_cancel_left]
    have he : 6*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)=
        6*(scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)) := by ring
    rw [he,norm_mul]
    norm_num only [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2), Real.norm_of_nonneg (by norm_num : (0:ℝ)≤6), Real.norm_of_nonneg (by norm_num : (0:ℝ)≤8)]
    nlinarith [hp 1 2 (by norm_num) (by norm_num)]
  · rw [scalarEnergySquareJet_four β μ q x hq]
    have he : 2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 4 (q,x)+
        8*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 3 (q,x)+
        6*scalarEnergySpatialJet β μ 2 (q,x)^2-
        2*scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 4 (q,x)=
        8*(scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 3 (q,x))+
          6*scalarEnergySpatialJet β μ 2 (q,x)^2 := by ring
    rw [he]
    exact (norm_add_le _ _).trans (by
      have h13 := hp 1 3 (by norm_num) (by norm_num)
      have h22 := hqpow 2 (by norm_num)
      simp only [norm_mul] at h13 h22 ⊢
      norm_num only [Real.norm_ofNat]
      nlinarith)

end QuantitativePaper
