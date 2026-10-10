module
public import HexagonPaper.EdgeLikelihoodFinite

@[expose] public section

/-! Exact endpoint/atom accounting and normalization for the finite-profile
restarted edge likelihood.  The middle sum is the Stieltjes contribution of
the profile jumps strictly between the two endpoint slots. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {n k : ℕ}

def edgeRestartHistoryPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) {N : ℕ} (p : FiniteHistory (AnisotropicParameter n) N)
    (i : ℕ) : ℝ :=
  anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-i)
    (historyExtended p i)

theorem edge_restart_finite_history_density_stieltjes
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : Paper.Overlap)
    (N : ℕ) (hN : N+1≤k+2) (p : FiniteHistory (AnisotropicParameter n) (N+1)) :
    finiteHistoryDensity (edgeRestartFiniteWeight D s q) (N+1) p =
      ENNReal.ofReal (Real.exp (
        (vectorClampedScheme s q q.property).m (N+1)*
          edgeRestartHistoryPotential D s q p (N+1)-
        (vectorClampedScheme s q q.property).m 1*
          edgeRestartHistoryPotential D s q p 0-
        ∑i ∈ Finset.range N,
          ((vectorClampedScheme s q q.property).m (i+2)-
            (vectorClampedScheme s q q.property).m (i+1))*
              edgeRestartHistoryPotential D s q p (i+1))) := by
  rw [edge_restart_finite_history_density_exp D s q (N+1) hN p]
  have he (i : Fin (N+1)) :
      anisotropicFinitePotential D (vectorClampedScheme s q q.property)
          (k+1-(i:ℕ)) (p i.succ)-
        anisotropicFinitePotential D (vectorClampedScheme s q q.property)
          (k+2-(i:ℕ)) (p i.castSucc) =
      edgeRestartHistoryPotential D s q p (i+1)-
        edgeRestartHistoryPotential D s q p i := by
    unfold edgeRestartHistoryPotential
    rw [historyExtended_left,historyExtended_right]
    rw [show k+2-((i:ℕ)+1)=k+1-(i:ℕ) by omega]
  simp_rw [he]
  congr 2
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (vectorClampedScheme s q q.property).m (i+1)*
      (edgeRestartHistoryPotential D s q p (i+1)-
        edgeRestartHistoryPotential D s q p i)) (N+1),
    weighted_difference_sum (fun i => (vectorClampedScheme s q q.property).m (i+1))
      (edgeRestartHistoryPotential D s q p) N]

theorem edge_restart_finite_history_density_normalized
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (N : ℕ) (hN : N≤k+2) :
    (∫⁻p, finiteHistoryDensity (edgeRestartFiniteWeight D s q) N p
      ∂finiteHistoryLaw
        (Measure.dirac (anisotropicDisorderInjection n g+anisotropicUnitInput D x))
        (edgeRestartFiniteBaseKernel D s q) N) = 1 := by
  have hm := congrArg (fun μ : Measure (FiniteHistory (AnisotropicParameter n) N) => μ univ)
    (edge_restart_finite_history_law_eq_withDensity D s g q x N hN)
  rw [Measure.map_apply (measurable_anisotropicFiniteRestartPhysicalHistory D s g q x N)
    MeasurableSet.univ,preimage_univ,measure_univ,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hm
  exact hm.symm

end HexagonPaper
