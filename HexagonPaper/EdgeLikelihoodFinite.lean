module
public import QuantitativeFollowup.AnisotropicVarianceRestartHistory
public import QuantitativeFollowup.AnisotropicFiniteJointDensity

@[expose] public section

/-! An actual finite-profile edge likelihood, before passing to continuous
paths and arbitrary profiles.  This is a measure equality for the constructed
restarted diffusion, including every chronological coordinate.  The reference
kernel is the genuine Gaussian increment kernel and the initial disorder and
field are fixed.  No Radon--Nikodym or transition-law identification is assumed.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {n k : ℕ}

def edgeRestartFiniteBaseKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (i : ℕ) : Kernel (AnisotropicParameter n) (AnisotropicParameter n) :=
  anisotropicFiniteBaseTransition D (vectorClampedScheme s q q.property) (i+1)

def edgeRestartFiniteWeight (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (i : ℕ) : AnisotropicParameter n → AnisotropicParameter n → ℝ≥0∞ :=
  anisotropicFiniteTransitionWeight D (vectorClampedScheme s q q.property) (i+1)

theorem edge_restart_finite_history_law_eq_withDensity
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (N : ℕ) (hN : N≤k+2) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFiniteRestartPhysicalHistory D s g q x N) =
      (finiteHistoryLaw (Measure.dirac (anisotropicDisorderInjection n g+anisotropicUnitInput D x))
        (edgeRestartFiniteBaseKernel D s q) N).withDensity
          (finiteHistoryDensity (edgeRestartFiniteWeight D s q) N) := by
  rw [anisotropicFiniteRestartPhysical_history_law D s g q x N hN]
  exact finiteHistoryLaw_withDensity _ (edgeRestartFiniteBaseKernel D s q)
    (anisotropicFiniteRestartPhysicalKernel D s q)
    (fun i => show IsMarkovKernel
      (anisotropicFiniteBaseTransition D (vectorClampedScheme s q q.property) (i+1)) from
      inferInstance)
    (fun i => inferInstance) (edgeRestartFiniteWeight D s q)
    (fun i => measurable_anisotropicFiniteTransitionWeight D
      (vectorClampedScheme s q q.property) (i+1))
    (fun i => anisotropicFiniteTransition_eq_withDensity D
      (vectorClampedScheme s q q.property) (i+1)) N

theorem edge_restart_finite_history_density_exp
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : Paper.Overlap)
    (N : ℕ) (hN : N≤k+2) (p : FiniteHistory (AnisotropicParameter n) N) :
    finiteHistoryDensity (edgeRestartFiniteWeight D s q) N p =
      ENNReal.ofReal (Real.exp (∑i : Fin N,
        (vectorClampedScheme s q q.property).m (i+1)*
          (anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+1-(i:ℕ))
              (p i.succ)-
            anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-(i:ℕ))
              (p i.castSucc)))) := by
  rw [finiteHistoryDensity_eq_prod]
  have he (i : Fin N) : edgeRestartFiniteWeight D s q i (p i.castSucc) (p i.succ) =
      ENNReal.ofReal (Real.exp ((vectorClampedScheme s q q.property).m (i+1)*
        (anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+1-(i:ℕ))
            (p i.succ)-
          anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-(i:ℕ))
            (p i.castSucc)))) := by
    unfold edgeRestartFiniteWeight
    rw [anisotropicFiniteTransitionWeight_eq_exp D (vectorClampedScheme s q q.property)
      (i+1) (by omega)]
    have h₁ : k+1+1-((i:ℕ)+1)=k+1-(i:ℕ) := by omega
    have h₂ : k+1+2-((i:ℕ)+1)=k+2-(i:ℕ) := by omega
    rw [h₁,h₂]
  simp_rw [he]
  rw [←ENNReal.ofReal_prod_of_nonneg (fun i _=>(Real.exp_pos _).le),←Real.exp_sum]

end HexagonPaper
