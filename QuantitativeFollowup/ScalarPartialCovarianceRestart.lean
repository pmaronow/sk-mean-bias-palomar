module
public import QuantitativeFollowup.ScalarPartialCovarianceResponse
public import QuantitativeFollowup.ScalarFiniteRestartPointwiseLaw

@[expose] public section

/-! The actual partial cascade covariance response uses the literal
fresh scalar restarted diffusion, at every spatial field and depth. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open SpinGlass SpinGlass.Targets FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

def scalarFiniteOverlapNode {k : ℕ} (s : RSBScheme k) (p : ℕ) (hp : p≤k+2) : Paper.Overlap :=
  ⟨s.q p,s.q_nonneg hp,s.q_le_one hp⟩

theorem scalarSchemeFutureSquareKernel_eq_restart {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (p J : ℕ) (hp : p≤J) (hJ : J≤k+2)
    (H : FiniteStateField (Fin 1)) :
    scalarSchemeFutureSquareKernel s β hβ h p J H=
      scalarFutureSquare β (Paper.parisiSchemeMeasure s)
        (scalarFiniteOverlapNode s (k+2-J) (by omega))
        (scalarFiniteOverlapNode s (k+2-p) (by omega))
        (s.q_mono' (k+2-p) (by omega) (k+2-J) (by omega)) (h+H 0) := by
  have he:=scalarSchemeEndpoint_eq_futureSquare s β hβ (k+2-J) (J-p) (by omega)
    (scalarFiniteOverlapNode s (k+2-J) (by omega))
    (scalarFiniteOverlapNode s (k+2-p) (by omega)) rfl
    (by dsimp only [scalarFiniteOverlapNode];congr 1;omega)
    (s.q_mono' (k+2-p) (by omega) (k+2-J) (by omega)) (h+H 0)
  simpa only [scalarSchemeFutureSquareKernel,scalarSiteAbsolute,scalarFiniteOverlapNode] using he

end QuantitativeFollowup
