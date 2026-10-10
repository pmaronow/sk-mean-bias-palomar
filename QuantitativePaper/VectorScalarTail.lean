module
public import QuantitativePaper.VectorMeasureTail
public import QuantitativePaper.VectorMeasureEndpoints

@[expose] public section

/-! The actual zero-interpolation vector potential factorizes into scalar
Parisi potentials at every overlap, not merely at the initial time. The
finite restarted recursion and the genuine moving-overlap limit prove it. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorTailRecursion_eq_full_of_time_le {n k : ℕ} (s : RSBScheme k)
    (β t q : ℝ) (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2)
    (hq : q ≤ s.q (k+2-j)) :
    vectorTailRecursion s β t q p j=vectorRecursion s β t p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have he : k+2-(j+1)=k+1-j := by omega
    have hqlo : q ≤ s.q (k+1-j) := by simpa only [he] using hq
    have hnodes : s.q (k+1-j) ≤ s.q (k+2-j) := s.q_mono' _ (by omega) _ (by omega)
    rw [vectorTailRecursion,vectorRecursion,ih (by omega) (hqlo.trans hnodes),
      max_eq_right (hqlo.trans hnodes),max_eq_right hqlo]

theorem vectorTailRecursion_eq_cell {n k : ℕ} (s : RSBScheme k)
    (β t q : ℝ) (p : Couplings n×ℝ) {i : ℕ} (hi : i ≤ k+1)
    (hq : q∈Icc (s.q i) (s.q (i+1))) (x : Field n) :
    vectorTailRecursion s β t q p (k+2) x=vectorFiniteCellPotential s β t p i q x := by
  have hj0 : k+2-i=(k+1-i)+1 := by omega
  have hprev : vectorTailRecursion s β t q p (k+1-i)=vectorRecursion s β t p (k+1-i) := by
    apply vectorTailRecursion_eq_full_of_time_le s β t q p (by omega)
    simpa only [show k+2-(k+1-i)=i+1 by omega] using hq.2
  have hbase : ∀x,vectorTailRecursion s β t q p (k+2-i) x=
      vectorFiniteCellPotential s β t p i q x := by
    intro x
    rw [hj0,vectorTailRecursion,hprev]
    simp only [show k+2-(k+1-i)=i+1 by omega,show k+1-(k+1-i)=i by omega,
      max_eq_right hq.2,max_eq_left hq.1,vectorFiniteCellPotential]
    congr 1
    ring
  have hafter : ∀j,k+2-i ≤ j → j ≤ k+2 → ∀x,
      vectorTailRecursion s β t q p j x=vectorFiniteCellPotential s β t p i q x := by
    intro j
    induction j with
    | zero => intro h0;omega
    | succ j ih =>
      intro hjlo hjhi x
      by_cases he : j+1=k+2-i
      · rw [he]
        exact hbase x
      · have hji : k+2-i ≤ j := by omega
        have hnode : s.q (k+2-j) ≤ q :=
          (s.q_mono' i (by omega) (k+2-j) (by omega)).trans hq.1
        have hlower : s.q (k+1-j) ≤ q :=
          (s.q_mono' _ (by omega) _ (by omega)).trans hnode
        rw [vectorTailRecursion,max_eq_left hnode,max_eq_left hlower,sub_self,mul_zero,mul_zero,
          vectorColeHopfStep_zero_variance]
        exact ih hji (by omega) x
  exact hafter (k+2) (Nat.sub_le _ _) le_rfl x

theorem vectorFiniteCellPotential_zero_time {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) :
    vectorFiniteCellPotential s β 0 p i q x=
      ∑l : Fin n,(Real.log 2+Paper.parisiSlabPotential s β (k+1-i) (s.m i) (s.q (i+1)) q (x l)) := by
  unfold vectorFiniteCellPotential
  rw [vectorColeHopfStep_eq_pi _ (vectorRecursion_lipschitz s β 0 p (k+1-i)).continuous]
  have he : (fun y : Fin n→ℝ=>vectorRecursion s β 0 p (k+1-i) (WithLp.toLp 2 y))=
      (fun y=>∑l : Fin n,(Real.log 2+parisiF s β (k+1-i) (y l))) := by
    funext y
    exact vectorRecursion_zero_time s β p (k+1-i) (WithLp.toLp 2 y)
  rw [he,parisiStepPi_sum _ _ (hasLinearGrowth_const_add (Real.log 2) (parisiF_hasLinearGrowth s β _))
    (measurable_const.add (parisiF_measurable s β _))]
  apply Finset.sum_congr rfl
  intro l hl
  rw [parisiStep_const_add _ _ _ (parisiF_hasLinearGrowth s β _) (parisiF_measurable s β _)]
  simp only [sub_zero,one_mul,Paper.parisiSlabPotential]

theorem vectorTailRecursion_zero_time {n k : ℕ} (s : RSBScheme k) (β q : ℝ)
    (hq : q∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorTailRecursion s β 0 q p (k+2) x=
      ∑l : Fin n,(Real.log 2+Paper.parisiFinitePotential s β (q,x l)) := by
  rcases eq_or_lt_of_le hq.2 with he|he
  · subst q
    rw [vectorTailRecursion_one s β 0 p le_rfl,vectorTerminalPotential_zero_time]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Paper.parisiFinitePotential_terminal]
    exact Real.log_mul (by norm_num) (Real.cosh_pos _).ne'
  · obtain ⟨i,hi,hcell,hstrict⟩ := Paper.exists_parisiFinite_right_cell s ⟨hq.1,he⟩
    rw [vectorTailRecursion_eq_cell s β 0 q p hi ⟨hcell.1,hcell.2.le⟩ x,
      vectorFiniteCellPotential_zero_time]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Paper.parisiFinitePotential_eq_slab s β hi hstrict ⟨hcell.1,hcell.2.le⟩]

theorem vectorMeasureTailPotential_zero_time {n : ℕ} (μ : Paper.ParisiMeasure)
    (β : ℝ) (hβ : β≠0) (q : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β 0 q p x=
      ∑l : Fin n,(Real.log 2+Paper.parisiPotential β μ (q,x l)) := by
  have hlim : Tendsto (fun j:ℕ=>∑l : Fin n,(Real.log 2+
      Paper.parisiFinitePotential (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β (q,x l)))
      atTop (𝓝 (∑l : Fin n,(Real.log 2+Paper.parisiPotential β μ (q,x l)))) := by
    apply tendsto_finsetSum
    intro l hl
    exact tendsto_const_nhds.add
      ((Paper.tendsto_actual_finiteParisiPotential β hβ μ q (x l) hq).comp tendsto_vectorDyadicIndex)
  have he : (fun j=>vectorDyadicTailPotential μ β 0 q j p x)=
      (fun j:ℕ=>∑l : Fin n,(Real.log 2+
        Paper.parisiFinitePotential (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β (q,x l))) := by
    funext j
    exact vectorTailRecursion_zero_time _ β q hq p x
  rw [←he] at hlim
  exact tendsto_nhds_unique (tendsto_vectorDyadicTailPotential μ β 0 q (by norm_num) hq p x) hlim

end QuantitativePaper
