module
public import QuantitativeFollowup.AnisotropicFiniteCell

@[expose] public section

/-! At every literal profile node, the actual restarted tail response equals
 the corresponding finite posterior response, including repeated nodes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 600000

def anisotropicSchemeNode (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) : Paper.Overlap :=
  ⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩

theorem anisotropicFiniteTailPotential_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) :
    anisotropicFiniteTailPotential D s (anisotropicSchemeNode s i hi)=
      anisotropicFinitePotential D s (k+2-i) := by
  unfold anisotropicFiniteTailPotential anisotropicSchemeNode
  have hidx : k+2-(k+2-i)=i := by omega
  rw [anisotropicTailRecursion_constant_suffix D s (s.q i) (k+2-i) (by omega)
    (by simpa only [hidx] using le_rfl (a := s.q i)) (by omega) le_rfl]
  exact anisotropicTailRecursion_prefix_of_le D s (s.q i) (by omega)
    (by simpa only [hidx] using le_rfl (a := s.q i))

theorem anisotropicFiniteTailMagnetization_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) (P : AnisotropicParameter n) :
    anisotropicFiniteTailMagnetization D s (anisotropicSchemeNode s i hi) P=
      anisotropicMagnetization D s (k+2-i) P := by
  unfold anisotropicFiniteTailMagnetization
  rw [anisotropicFiniteTailPotential_node D s i hi]
  rfl

end QuantitativeFollowup
