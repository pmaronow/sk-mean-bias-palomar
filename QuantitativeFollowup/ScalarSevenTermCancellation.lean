module
public import QuantitativeFollowup.ScalarScoreContractionAlgebra

@[expose] public section

/-! Literal cancellation in the seven-term scalar response. The remaining
terminal-spin factor is displayed explicitly; its expectation is discharged
by the genuine terminal conditional law in ScalarScoreConditioning. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem scalar_seven_term_cancellation {ι : Type*} [Fintype ι]
    (d m h third a φ ε centered futureDerivative : ℝ)
    (w G H A P future toPast : ι→ℝ) (between : ι→ι→ℝ) :
    -d*m*(φ*(third+2*a*m*h)+futureDerivative)
      +centered*(-∑i,w i*(-(d/2)*(P i*(H i+A i*G i^2)+future i)))
      +d*(φ*(h^2+m*third)+2*m*h*(ε*φ-∑i,w i*G i*toPast i)
        +(1/2:ℝ)*centered*(-∑i,w i*H i*P i-2*ε*(∑i,w i*G i*P i)
          +∑i,∑j,w i*w j*G i*G j*between i j))
      =d*(φ*(h^2+2*(1-a)*m^2*h)-m*futureDerivative
        -2*m*h*(∑i,w i*G i*toPast i)
        -centered*ε*(∑i,w i*G i*P i)
        +(1/2:ℝ)*centered*(∑i,w i*A i*G i^2*P i)
        +(1/2:ℝ)*centered*(∑i,∑j,w i*w j*G i*G j*between i j)
        +(1/2:ℝ)*centered*(∑i,w i*future i))
        +2*d*φ*m*h*(ε-m) := by
  have hs : (-∑i,w i*(-(d/2)*(P i*(H i+A i*G i^2)+future i))) =
      (d/2)*((∑i,w i*H i*P i)+(∑i,w i*A i*G i^2*P i)+(∑i,w i*future i)) := by
    rw [←Finset.sum_neg_distrib,←Finset.sum_add_distrib,
      ←Finset.sum_add_distrib,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=>by ring
  rw [hs]
  ring

end QuantitativeFollowup
