module
public import QuantitativePaper.GaussianColeHopfCoordinateMean
public import QuantitativePaper.GaussianColeHopfCoordinateSlopeSmooth

@[expose] public section

/-! Genuine joint Gaussian Cole--Hopf smoothing through zero and negative
mass. The expectation at mass zero is identified with the actual removable
log-partition slope, and every finite-order joint jet is bounded on bounded
mass cylinders. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def gaussianMassColeHopf {n : ℕ} (A : Field n →L[ℝ] E) (f : E → ℝ) (x : ℝ×E) : ℝ :=
  gaussianShiftColeHopf A x.1 f x.2

theorem gaussianMassColeHopf_eq_smoothCoordinateSlope {n : ℕ}
    (A : Field n →L[ℝ] E) (f : E → ℝ) (U : Set E) (hf : ContinuousOn f U)
    (hshift : ∀ x∈U, ∀ z, x+A z∈U) (H : ℝ)
    (hlip : ∀ x∈U, ∀ z, |f (x+A z)-f x| ≤ H*‖z‖)
    (hd : ∀ x∈U, DifferentiableAt ℝ (gaussianMassLog A f) (0,x))
    (x : ℝ×E) (hx : x.2∈U) :
    gaussianMassColeHopf A f x = smoothCoordinateSlope (gaussianMassLog A f) x := by
  by_cases hm : x.1=0
  · simp only [gaussianMassColeHopf,gaussianShiftColeHopf,smoothCoordinateSlope,hm,ite_true]
    exact (coordinateDerivative_gaussianMassLog_zero A f U hf hshift H hlip x.2 hx
      (hd x.2 hx)).symm
  · simp only [gaussianMassColeHopf,gaussianShiftColeHopf,smoothCoordinateSlope,hm,ite_false]
    congr 1
    simp only [gaussianMassLog,gaussianShiftPartition,gaussianMassShift,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,Prod.fst_add,Prod.snd_add,
      one_mul,add_zero]

theorem gaussianMassColeHopf_smooth_exp_jets_on_open {n : ℕ} (N : ℕ)
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ (N+1) f U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x∈U, ∀ z, x+A z∈U)
    (B L K D H R : ℝ) (hB : 0≤B) (hL : 0≤L) (hK : 1≤K) (hD : 0≤D) (hR : 0<R)
    (hvalue : ∀ x∈U, |f x| ≤ B+L*‖x‖)
    (hjets : ∀ j, 1≤j → j≤N+1 → ∀ x∈U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^j)
    (hlip : ∀ x∈U, ∀ z, |f (x+A z)-f x| ≤ H*‖z‖) :
    ContDiffOn ℝ N (gaussianMassColeHopf A f) (gaussianMassCylinder R U) ∧
      ∃ C Q : ℝ, 1≤C ∧ 1≤Q ∧ ∀ j, 1≤j → j≤N →
        ∀ x∈gaussianMassCylinder R U,
        ‖iteratedFDeriv ℝ j (gaussianMassColeHopf A f) x‖ ≤ (C*Real.exp (Q*‖x‖))^j := by
  obtain ⟨hl,C,Q,hC,hQ,hj⟩ := gaussianMassLog_smooth_exp_jets_on_open (N+1) f U hU hf
    A hshift B L K D H R hB hL hK hD hR hvalue hjets hlip
  let V := gaussianMassCylinder R U
  have hV := gaussianMassCylinder_open R U hU
  have hc := gaussianMassCylinder_contract R hR U
  have hd (x : E) (hx : x∈U) : DifferentiableAt ℝ (gaussianMassLog A f) (0,x) :=
    (hl.contDiffAt (hV.mem_nhds (show (0,x)∈V from ⟨⟨by linarith, hR⟩,hx⟩))).differentiableAt (by simp)
  obtain ⟨hs,hb⟩ := smoothCoordinateSlope_smooth_exp_jets_on_open N (gaussianMassLog A f) V hV hl
    hc (fun x _ => gaussianMassLog_zero A f x) C Q hC (zero_le_one.trans hQ) hj
  have he : EqOn (gaussianMassColeHopf A f) (smoothCoordinateSlope (gaussianMassLog A f)) V :=
    fun x hx => gaussianMassColeHopf_eq_smoothCoordinateSlope A f U hf.continuousOn hshift H hlip hd x hx.2
  refine ⟨hs.congr he,C^2,2*Q,one_le_pow₀ hC,by linarith,?_⟩
  intro j hj0 hjN x hx
  have hev : gaussianMassColeHopf A f =ᶠ[𝓝 x] smoothCoordinateSlope (gaussianMassLog A f) :=
    mem_of_superset (hV.mem_nhds hx) (fun y hy => he hy)
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
  exact hb j hj0 hjN x hx

end QuantitativePaper
