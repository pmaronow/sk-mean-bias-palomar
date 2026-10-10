module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysicalBounds
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeConvergence
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeLocalLimit

@[expose] public section

/-! A genuine C¹ field derivative of the arbitrary-profile restarted
coordinate-square expectation. The finite derivatives converge locally
uniformly by the proved common posterior modulus. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

def anisotropicDyadicRestartPosteriorSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (i : Fin n) (j : ℕ) : Field n→ℝ :=
  anisotropicFiniteRestartPosteriorSquare D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    g q (vectorDyadicTimeIndex r j) i

theorem tendsto_anisotropicDyadicRestartPosteriorSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (i : Fin n) (x : Field n) :
    Tendsto (fun j=>anisotropicDyadicRestartPosteriorSquare D μ g q r i j x) atTop
      (𝓝 (anisotropicRestartSpinSquare D μ g q x i r)) := by
  have hp:=tendsto_anisotropicVarianceRestart_node_square_le D μ i (D.variance_pos i)
    (tendsto_const_nhds (x:=D.variance i)) g q r hqr x
  simp only [anisotropicReplaceVariance_self] at hp
  have he (j : ℕ) : anisotropicDyadicRestartPosteriorSquare D μ g q r i j x=
      cavityFiniteConditionalCoordinateSquare D
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        (vectorDyadicIndex j+3) (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)
        i (Paper.parisiGridRound (vectorDyadicIndex j) r) := by
    let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let v:=vectorDyadicTimeIndex r j
    have hv : v≤vectorDyadicIndex j+3:=(vectorDyadicTimeIndex_le r j).trans (by omega)
    have hqv : (q:ℝ)≤ s.q v := by
      rw [vectorDyadicTimeIndex_node]
      exact hqr.trans (Paper.le_parisiGridRound _ r)
    have hn : anisotropicSchemeNode s v hv=Paper.parisiGridRound (vectorDyadicIndex j) r :=
      Subtype.ext (vectorDyadicTimeIndex_node μ r j)
    change anisotropicFiniteRestartPosteriorSquare D s g q v i x=_
    rw [anisotropicFiniteRestartPosteriorSquare_eq_physical D s g q v hv hqv i x,hn]
  simpa only [he] using hp

theorem anisotropicRestartSpinSquare_field_derivative_limit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (i : Fin n) :
    TendstoLocallyUniformly
      (fun j=>fderiv ℝ (anisotropicDyadicRestartPosteriorSquare D μ g q r i j))
      (fderiv ℝ (fun x=>anisotropicRestartSpinSquare D μ g q x i r)) atTop ∧
    ContDiff ℝ 1 (fun x=>anisotropicRestartSpinSquare D μ g q x i r) := by
  let f:=anisotropicDyadicRestartPosteriorSquare D μ g q r i
  let G:=fun x=>anisotropicRestartSpinSquare D μ g q x i r
  obtain ⟨G',hu,hd,hc,hs⟩:=exists_local_derivative_limit_of_pointwise f G
    (fun j=>differentiable_anisotropicFiniteRestartPosteriorSquare D _ g q _ i)
    (4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊)
    (31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2)
    (fun j=>anisotropicFiniteRestartPosteriorSquare_lipschitz D _ g q _ i)
    (fun j=>anisotropicFiniteRestartPosteriorSquare_differential_lipschitz D _ g q _ i)
    (fun x=>tendsto_anisotropicDyadicRestartPosteriorSquare D μ g q r hqr i x)
  have he : G'=fderiv ℝ G := funext fun x=>(hd x).fderiv.symm
  rw [he] at hu
  exact ⟨hu,hs⟩

theorem contDiff_anisotropicRestartSpinSquare_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (i : Fin n) :
    ContDiff ℝ 1 (fun x=>anisotropicRestartSpinSquare D μ g q x i r) :=
  (anisotropicRestartSpinSquare_field_derivative_limit D μ g q r hqr i).2

end QuantitativeFollowup
