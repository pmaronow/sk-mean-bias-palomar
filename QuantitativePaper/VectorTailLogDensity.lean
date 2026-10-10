module
public import QuantitativePaper.VectorTailGaussianCoordinates

@[expose] public section

/-! The literal normalized Gaussian posterior log density of every remaining
finite chain. Its Stieltjes coefficients telescope to total mass one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorTailHistoryPotential (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (j i : ℕ) (z : Fin j → Field n) : ℝ :=
  vectorRecursion s β t p (j-i) (historyExtended (vectorHistoryFrom s β t (k+2-j) p x j z) i).2

theorem vectorTailHistoryPotential_terminal (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (z : Fin j → Field n) :
    vectorTailHistoryPotential s β t p x j j z=
      vectorTerminalPotential n β t p (vectorHistoryFrom s β t (k+2-j) p x j z (Fin.last j)).2 := by
  unfold vectorTailHistoryPotential
  have he := historyExtended_fin (vectorHistoryFrom s β t (k+2-j) p x j z) (Fin.last j)
  simp only [Fin.val_last] at he
  rw [he,Nat.sub_self,vectorRecursion]

theorem vectorTailHistoryPotential_initial (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (z : Fin j → Field n) :
    vectorTailHistoryPotential s β t p x j 0 z=vectorRecursion s β t p j x := by
  simp [vectorTailHistoryPotential,historyExtended,vectorHistoryFrom_initial]

def vectorTailPosteriorLogDensity (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (j : ℕ) (z : (Fin j → Field n) × Configuration n) : ℝ :=
  vectorTerminalExponent n β t p (vectorHistoryFrom s β t (k+2-j) p x j z.1 (Fin.last j)).2 z.2-
    vectorTailHistoryPotential s β t p x j j z.1+
    ∑i : Fin j,s.m (k+2-j+i)*(vectorTailHistoryPotential s β t p x j (i+1) z.1-
      vectorTailHistoryPotential s β t p x j i z.1)

theorem vectorTailJointDensity_eq_exp_log (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2)
    (z : (Fin j → Field n) × Configuration n) :
    vectorTailJointDensity s β t j (vectorTailCoordinateJointMap s β t p x j z)=
      ENNReal.ofReal (Real.exp (vectorTailPosteriorLogDensity s β t p x j z)) := by
  let L := k+2-j
  let h := vectorHistoryFrom s β t L p x j z.1
  have hp (i : Fin (j+1)) : (h i).1=p := vectorHistoryFrom_disorder s β t L p x j z.1 i
  have hi (i : Fin j) : L+i ≤ k+1 := by dsimp only [L];omega
  have he (i : Fin j) : vectorProfileWeight s β t (L+i) (h i.castSucc) (h i.succ)=
      ENNReal.ofReal (Real.exp (s.m (L+i)*(vectorTailHistoryPotential s β t p x j (i+1) z.1-
        vectorTailHistoryPotential s β t p x j i z.1))) := by
    rw [vectorProfileWeight_eq_exp s β t (L+i) (hi i),hp]
    unfold vectorTailHistoryPotential
    rw [historyExtended_left,historyExtended_right]
    have h1 : k+1-(L+i)=j-(i+1) := by dsimp only [L];omega
    have h2 : k+2-(L+i)=j-i := by dsimp only [L];omega
    rw [h1,h2]
  change finiteHistoryDensity (fun i => vectorProfileWeight s β t (L+i)) j h *
    ENNReal.ofReal (terminalWeight (vectorTerminalExponent n β t (h (Fin.last j)).1 (h (Fin.last j)).2) z.2)=_
  rw [finiteHistoryDensity_eq_prod]
  simp_rw [he]
  rw [←ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),←Real.exp_sum,
    hp,terminalWeight_eq_exp,←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  rw [vectorTailPosteriorLogDensity,vectorTailHistoryPotential_terminal]
  dsimp only [h,L,vectorTerminalPotential]
  ring

theorem vectorTailPosteriorLogDensity_stieltjes (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (N : ℕ) (hN : N+1 ≤ k+2)
    (z : (Fin (N+1) → Field n) × Configuration n) :
    vectorTailPosteriorLogDensity s β t p x (N+1) z=
      vectorTerminalExponent n β t p
        (vectorHistoryFrom s β t (k+2-(N+1)) p x (N+1) z.1 (Fin.last (N+1))).2 z.2-
      s.m (k+2-(N+1))*vectorTailHistoryPotential s β t p x (N+1) 0 z.1-
      ∑i ∈ Finset.range N,(s.m (k+2-(N+1)+(i+1))-s.m (k+2-(N+1)+i))*
        vectorTailHistoryPotential s β t p x (N+1) (i+1) z.1 := by
  let L := k+2-(N+1)
  have htop : L+N=k+1 := by dsimp only [L];omega
  unfold vectorTailPosteriorLogDensity
  rw [Fin.sum_univ_eq_sum_range (fun i => s.m (L+i)*(vectorTailHistoryPotential s β t p x (N+1) (i+1) z.1-
    vectorTailHistoryPotential s β t p x (N+1) i z.1)) (N+1)]
  have hh := weighted_difference_sum (fun i => s.m (L+i))
    (fun i => vectorTailHistoryPotential s β t p x (N+1) i z.1) N
  rw [hh,htop,s.m_top,one_mul]
  simp only [L,Nat.add_zero]
  ring

theorem vectorTailStieltjesCoefficient_sum (s : RSBScheme k) (N : ℕ) (hN : N+1 ≤ k+2) :
    s.m (k+2-(N+1))+
      ∑i ∈ Finset.range N,(s.m (k+2-(N+1)+(i+1))-s.m (k+2-(N+1)+i))=1 := by
  rw [Finset.sum_range_sub (fun i => s.m (k+2-(N+1)+i)) N]
  have he : k+2-(N+1)+N=k+1 := by omega
  rw [he,s.m_top]
  simp

end QuantitativePaper
