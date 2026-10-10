module
public import QuantitativePaper.VectorSharpMassBounds
public import QuantitativePaper.VectorMeasureTail

@[expose] public section

/-! The literal sharp half-variance profile continuity bound, derived for
actual finite recursions and passed to the constructed arbitrary-measure
potential. The restarted bound uses exactly the coefficient tail integral. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorRecursion_aligned_profile_abs_sub_le_half {n k : ℕ} (s r : RSBScheme k)
    (β t : ℝ) (ht : t  ≤  1) (hq : ∀i,i  ≤  k+2 → s.q i=r.q i)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    |vectorRecursion s β t p j x-vectorRecursion r β t p j x|  ≤ 
      vectorAlignedProfileError (n := n) s r β t j/2 := by
  induction j generalizing x with
  | zero => simp [vectorRecursion,vectorAlignedProfileError]
  | succ j ih =>
    let v := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    have hv : 0  ≤  v := mul_nonneg (sub_nonneg.mpr ht)
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr
        (s.q_mono' (k+2-j) (Nat.sub_le _ _) (k+1-j) (by omega))))
    have hvr : (1-t)*(β^2*(r.q (k+2-j)-r.q (k+1-j)))=v := by
      rw [←hq _ (Nat.sub_le _ _),←hq _ (by omega)]
    simp only [vectorRecursion]
    rw [hvr]
    have hn := abs_vectorColeHopfStep_sub_le (vectorRecursion s β t p j) (vectorRecursion r β t p j)
      _ (vectorRecursion_lipschitz s β t p j) (vectorRecursion_lipschitz r β t p j)
      v (s.m (k+1-j)) (vectorAlignedProfileError (n := n) s r β t j/2)
      (s.m_nonneg (Nat.sub_le _ _)) ih x
    have hm := vectorColeHopfStep_recursion_mass_abs_sub_le_half r β t v hv p j x
      (s.m (k+1-j)) (r.m (k+1-j)) (s.m_nonneg (Nat.sub_le _ _)) (r.m_nonneg (Nat.sub_le _ _))
    rw [abs_sub_comm] at hm
    calc
      _  ≤  |vectorColeHopfStep v (s.m (k+1-j)) (vectorRecursion s β t p j) x-
          vectorColeHopfStep v (s.m (k+1-j)) (vectorRecursion r β t p j) x|+
        |vectorColeHopfStep v (s.m (k+1-j)) (vectorRecursion r β t p j) x-
          vectorColeHopfStep v (r.m (k+1-j)) (vectorRecursion r β t p j) x| := abs_sub_le _ _ _
      _  ≤  vectorAlignedProfileError (n := n) s r β t j/2+(n : ℝ)*v/2*|r.m (k+1-j)-s.m (k+1-j)| :=
        add_le_add hn hm
      _ = vectorAlignedProfileError (n := n) s r β t (j+1)/2 := by
        simp only [vectorAlignedProfileError,Finset.sum_range_succ]
        rw [abs_sub_comm]
        ring

/-- The coefficient distance on exactly the remaining overlap interval. -/
def vectorTailCDFDistance (μ ν : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  ∫a in q..1,|Paper.parisiCDF μ a-Paper.parisiCDF ν a|

theorem parisiSchemeCDFDistance_tail_cell {k : ℕ} (s r : RSBScheme k)
    (hq : ∀i,i  ≤  k+2 → s.q i=r.q i) (q : ℝ) {p : ℕ} (hp : p  ≤  k+1) :
    (∫a in max q (s.q p)..max q (s.q (p+1)),
      |Paper.parisiCDF (Paper.parisiSchemeMeasure s) a-
        Paper.parisiCDF (Paper.parisiSchemeMeasure r) a|)=
      (max q (s.q (p+1))-max q (s.q p))*|s.m p-r.m p| := by
  have hmono : max q (s.q p) ≤ max q (s.q (p+1)) := max_le_max le_rfl (s.q_mono p hp)
  have he : EqOn (fun a=>|Paper.parisiCDF (Paper.parisiSchemeMeasure s) a-
      Paper.parisiCDF (Paper.parisiSchemeMeasure r) a|)
      (fun _=>|s.m p-r.m p|) (uIoo (max q (s.q p)) (max q (s.q (p+1)))) := by
    rw [uIoo_of_le hmono]
    intro a ha
    have hqa : q<a := (le_max_left _ _).trans_lt ha.1
    have hpa : s.q p<a := (le_max_right _ _).trans_lt ha.1
    have hap : a<s.q (p+1) := (lt_max_iff.mp ha.2).resolve_left (not_lt.mpr hqa.le)
    have har : a∈Ico (r.q p) (r.q (p+1)) := by
      rw [←hq p (by omega),←hq (p+1) (by omega)]
      exact ⟨hpa.le,hap⟩
    dsimp only
    rw [Paper.parisiCDF_scheme_cell s hp ⟨hpa.le,hap⟩,
      Paper.parisiCDF_scheme_cell r hp har]
  rw [intervalIntegral.integral_congr_uIoo he,intervalIntegral.integral_const]
  simp only [smul_eq_mul]

theorem parisiSchemeCDFDistance_tail_eq_sum {k : ℕ} (s r : RSBScheme k)
    (hq : ∀i,i  ≤  k+2 → s.q i=r.q i) (q : ℝ) (hq01 : q∈Icc (0:ℝ) 1) :
    vectorTailCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) q=
      ∑p∈Finset.range (k+2),(max q (s.q (p+1))-max q (s.q p))*|s.m p-r.m p| := by
  have hp := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i=>max q (s.q i)) (n:=k+2)
    (fun p _=>Paper.parisiCDF_abs_diff_intervalIntegrable
      (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r)
      (max q (s.q p)) (max q (s.q (p+1))))
  rw [s.q_zero,s.q_top,max_eq_left hq01.1,max_eq_right hq01.2] at hp
  rw [vectorTailCDFDistance,←hp]
  apply Finset.sum_congr rfl
  intro p hp
  exact parisiSchemeCDFDistance_tail_cell s r hq q (by have := Finset.mem_range.mp hp;omega)

theorem vectorAlignedProfileError_clamped_eq_tail_distance {n k : ℕ} (s r : RSBScheme k)
    (β t q : ℝ) (hq01 : q∈Icc (0:ℝ) 1) (hgrid : ∀i,i ≤ k+2→s.q i=r.q i) :
    vectorAlignedProfileError (n:=n) (vectorClampedScheme s q hq01)
      (vectorClampedScheme r q hq01) β t (k+2)=
      (n:ℝ)*((1-t)*β^2)*
        vectorTailCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) q := by
  rw [parisiSchemeCDFDistance_tail_eq_sum s r hgrid q hq01,Finset.mul_sum]
  unfold vectorAlignedProfileError
  rw [←Finset.sum_range_reflect
    (fun p=>(n:ℝ)*((1-t)*β^2)*
      ((max q (s.q (p+1))-max q (s.q p))*|s.m p-r.m p|)) (k+2)]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have hi0 : k+1+1-l=(k+1-l)+1 := by omega
  have hi1 : k+1+2-l=(k+2-l)+1 := by omega
  rw [hi0,hi1,vectorClampedScheme_mass_succ,vectorClampedScheme_mass_succ,
    vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ]
  have hi : k+2-1-l=k+1-l := by omega
  have hs : k+2-l=k+1-l+1 := by omega
  rw [hi,hs]
  ring

theorem vectorTailRecursion_aligned_tail_distance_abs_sub_le_half {n k : ℕ} (s r : RSBScheme k)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0:ℝ) 1)
    (hgrid : ∀i,i ≤ k+2→s.q i=r.q i) (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion s β t q p (k+2) x-vectorTailRecursion r β t q p (k+2) x| ≤ 
      (n:ℝ)*((1-t)*β^2)/2*
        vectorTailCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) q := by
  have hclamp : ∀i,i ≤ k+1+2→
      (vectorClampedScheme s q hq).q i=(vectorClampedScheme r q hq).q i := by
    intro i hi
    by_cases h0 : i=0
    · subst i;simp [vectorClampedScheme,clampedSchemeOverlap]
    · simp only [vectorClampedScheme,clampedSchemeOverlap,ite_eq_right h0]
      rw [hgrid (i-1) (by omega)]
  have hh := vectorRecursion_aligned_profile_abs_sub_le_half
    (vectorClampedScheme s q hq) (vectorClampedScheme r q hq) β t ht hclamp p (k+2) x
  rw [←vectorTailRecursion_eq_clamped s β t q hq p le_rfl,
    ←vectorTailRecursion_eq_clamped r β t q hq p le_rfl,
    vectorAlignedProfileError_clamped_eq_tail_distance s r β t q hq hgrid] at hh
  convert! hh using 1 <;> ring

theorem vectorTailCDFDistance_triangle (μ ν η : Paper.ParisiMeasure)
    (q : ℝ) (hq : q ≤ 1) :
    vectorTailCDFDistance μ η q ≤ vectorTailCDFDistance μ ν q+vectorTailCDFDistance ν η q := by
  unfold vectorTailCDFDistance
  rw [←intervalIntegral.integral_add (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν q 1)
    (Paper.parisiCDF_abs_diff_intervalIntegrable ν η q 1)]
  apply intervalIntegral.integral_mono_on hq
    (Paper.parisiCDF_abs_diff_intervalIntegrable μ η q 1)
    ((Paper.parisiCDF_abs_diff_intervalIntegrable μ ν q 1).add
      (Paper.parisiCDF_abs_diff_intervalIntegrable ν η q 1))
  intro a ha
  exact abs_sub_le _ _ _

theorem vectorTailCDFDistance_le_distance (μ ν : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : vectorTailCDFDistance μ ν q ≤ Paper.parisiCDFDistance μ ν := by
  have h0 := intervalIntegral.integral_nonneg_of_forall (μ:=volume) (a:=0) (b:=q) hq.1
    (fun a=>abs_nonneg (Paper.parisiCDF μ a-Paper.parisiCDF ν a))
  have he := intervalIntegral.integral_add_adjacent_intervals
    (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 q)
    (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν q 1)
  change (∫a in q..1,|Paper.parisiCDF μ a-Paper.parisiCDF ν a|) ≤ _
  unfold Paper.parisiCDFDistance
  linarith

theorem vectorTailCDFDistance_grid_pair_le (μ ν : Paper.ParisiMeasure) (N : ℕ)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    vectorTailCDFDistance (Paper.parisiGridMeasure μ N) (Paper.parisiGridMeasure ν N) q ≤ 
      vectorTailCDFDistance μ ν q+2/(N+1:ℕ) := by
  have h1 := vectorTailCDFDistance_triangle (Paper.parisiGridMeasure μ N) μ
    (Paper.parisiGridMeasure ν N) q hq.2
  have h2 := vectorTailCDFDistance_triangle μ ν (Paper.parisiGridMeasure ν N) q hq.2
  have hμ := (vectorTailCDFDistance_le_distance (Paper.parisiGridMeasure μ N) μ q hq).trans
    (show Paper.parisiCDFDistance (Paper.parisiGridMeasure μ N) μ ≤ 1/(N+1:ℕ) by
      simpa only [Paper.parisiCDFDistance,abs_sub_comm] using Paper.parisiCDFDistance_grid_le μ N)
  have hν := (vectorTailCDFDistance_le_distance ν (Paper.parisiGridMeasure ν N) q hq).trans
    (Paper.parisiCDFDistance_grid_le ν N)
  simp only [div_eq_mul_inv,one_mul] at hμ hν ⊢
  linarith

theorem vectorTailRecursion_grid_tail_distance_abs_sub_le_half {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (N : ℕ) (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion (Paper.parisiGridRSBScheme μ N) β t q p (N+3) x-
      vectorTailRecursion (Paper.parisiGridRSBScheme ν N) β t q p (N+3) x| ≤ 
      (n:ℝ)*((1-t)*β^2)/2*(vectorTailCDFDistance μ ν q+2/(N+1:ℕ)) := by
  have hh := vectorTailRecursion_aligned_tail_distance_abs_sub_le_half
    (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRSBScheme ν N) β t q ht hq
    (fun _ _=>rfl) p x
  rw [FRSB.parisiSchemeMeasure_grid_eq,FRSB.parisiSchemeMeasure_grid_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (vectorTailCDFDistance_grid_pair_le μ ν N q hq)
    (by positivity))

theorem vectorMeasureTailPotential_tail_distance_abs_sub_le_half {n : ℕ}
    (μ ν : Paper.ParisiMeasure) (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorMeasureTailPotential μ β t q p x-vectorMeasureTailPotential ν β t q p x| ≤ 
      (n:ℝ)*((1-t)*β^2)/2*vectorTailCDFDistance μ ν q := by
  have hleft := ((tendsto_vectorDyadicTailPotential μ β t q ht hq p x).sub
    (tendsto_vectorDyadicTailPotential ν β t q ht hq p x)).abs
  have herr : Tendsto (fun j:ℕ=>(2:ℝ)/(vectorDyadicIndex j+1:ℕ)) atTop (𝓝 0) := by
    simp only [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat]
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (2:ℝ)
    convert! hh using 1
    · funext j;rw [div_pow,one_pow];ring
    · simp
  have hright := ((tendsto_const_nhds (x:=vectorTailCDFDistance μ ν q)).add herr).const_mul
    ((n:ℝ)*((1-t)*β^2)/2)
  apply le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright)
  exact Eventually.of_forall (fun j=>vectorTailRecursion_grid_tail_distance_abs_sub_le_half μ ν
    (vectorDyadicIndex j) β t q ht hq p x)

end QuantitativePaper
