module
public import QuantitativePaper.GaussianColeHopfCoordinateJets
public import QuantitativePaper.LocalExponentialJetClosure
public import QuantitativePaper.ScalarCylinderJets

@[expose] public section

/-! The genuine Gaussian log partition is jointly smooth in an independent
real mass coordinate and every prior parameter on bounded mass cylinders.
The mass may be negative or zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianMassCylinder (R : ℝ) (U : Set E) : Set (ℝ×E) := Ioo (-R) R ×ˢ U

def gaussianMassShift {n : ℕ} (A : Field n →L[ℝ] E) : Field n →L[ℝ] ℝ×E :=
  (ContinuousLinearMap.inr ℝ ℝ E).comp A

def gaussianMassLog {n : ℕ} (A : Field n →L[ℝ] E) (f : E → ℝ) (x : ℝ×E) : ℝ :=
  Real.log (gaussianShiftPartition (gaussianMassShift A) 1 (fun y => y.1*f y.2) x)

@[simp] theorem gaussianMassLog_zero {n : ℕ} (A : Field n →L[ℝ] E) (f : E → ℝ) (x : E) :
    gaussianMassLog A f (0,x) = 0 := by
  simp [gaussianMassLog,gaussianShiftPartition,gaussianMassShift]

theorem gaussianMassCylinder_open (R : ℝ) (U : Set E) (hU : IsOpen U) :
    IsOpen (gaussianMassCylinder R U) := isOpen_Ioo.prod hU

theorem gaussianMassCylinder_contract (R : ℝ) (hR : 0 < R) (U : Set E)
    (x : ℝ×E) (hx : x ∈ gaussianMassCylinder R U)
    (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    coordinateContraction r x ∈ gaussianMassCylinder R U := by
  have habs : |x.1| < R := abs_lt.mpr hx.1
  have hb : |r*x.1| < R := by
    rw [abs_mul,abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg x.1)).trans_lt (by simpa using habs)
  simpa only [coordinateContraction_apply, gaussianMassCylinder, mem_prod, mem_Ioo] using And.intro (abs_lt.mp hb) hx.2

theorem gaussianMassLog_smooth_exp_jets_on_open {n : ℕ} (N : ℕ)
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x∈U, ∀ z, x+A z∈U)
    (B L K D H R : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hK : 1 ≤ K) (hD : 0 ≤ D) (hR : 0 < R)
    (hvalue : ∀ x∈U, |f x| ≤ B+L*‖x‖)
    (hjets : ∀ j, 1 ≤ j → j ≤ N → ∀ x∈U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^j)
    (hlip : ∀ x∈U, ∀ z, |f (x+A z)-f x| ≤ H*‖z‖) :
    ContDiffOn ℝ N (gaussianMassLog A f) (gaussianMassCylinder R U) ∧
      ∃ C Q : ℝ, 1 ≤ C ∧ 1 ≤ Q ∧ ∀ j, 1 ≤ j → j ≤ N →
        ∀ x∈gaussianMassCylinder R U,
        ‖iteratedFDeriv ℝ j (gaussianMassLog A f) x‖ ≤ (C*Real.exp (Q*‖x‖))^j := by
  let V := gaussianMassCylinder R U
  have hV := gaussianMassCylinder_open R U hU
  let f₀ : ℝ×E → ℝ := fun y => f y.2
  have hf₀ : ContDiffOn ℝ N f₀ V := hf.comp contDiffOn_snd (fun _ h => h.2)
  have hv₀ : ∀ y∈V, |f₀ y| ≤ B+L*‖y‖ := by
    intro y hy
    exact (hvalue y.2 hy.2).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (norm_snd_le y) hL) B)
  have hj₀ : ∀ j, 1 ≤ j → j ≤ N → ∀ y∈V,
      ‖iteratedFDeriv ℝ j f₀ y‖ ≤ (K*Real.exp (D*‖y‖))^j := by
    intro j hj0 hj y hy
    apply (norm_iteratedFDeriv_comp_linear_on_open f U hU hf hj
      (ContinuousLinearMap.snd ℝ ℝ E) y hy.2 (ContinuousLinearMap.norm_snd_le ℝ ℝ E)).trans
    apply (hjets j hj0 hj y.2 hy.2).trans
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (norm_snd_le y) hD)) (zero_le_one.trans hK)
  obtain ⟨M,hM,hm⟩ := exists_scalar_cylinder_jet_bound (E:=E) N (fun s : ℝ => s)
    univ isOpen_univ contDiff_id.contDiffOn (-R) R (subset_univ _)
  have hmass : ∀ j, j ≤ N → ∀ y∈V,
      ‖iteratedFDeriv ℝ j (fun y : ℝ×E => y.1) y‖ ≤ M :=
    fun j hj y hy => hm j hj y ⟨hy.1.1.le,hy.1.2.le⟩
  obtain ⟨hg,C,Q,hC,hQ,hgjet⟩ := mul_smooth_exp_jets_on_open N f₀
    (fun y : ℝ×E => y.1) V hV hf₀ contDiffOn_fst B L K D M hB hL hK hD hM hv₀ hj₀ hmass
  let A₀ := gaussianMassShift A
  have heShift (y : ℝ×E) (z : Field n) : y+A₀ z=(y.1,y.2+A z) := by
    ext <;> simp [A₀,gaussianMassShift]
  have hs : ∀ y∈V, ∀ z, y+A₀ z∈V := by
    intro y hy z
    rw [heShift]
    exact ⟨hy.1,hshift y.2 hy.2 z⟩
  have hgv : ∀ y∈V, y.1*f y.2 ≤ R*B+(R*L)*‖y‖ := by
    intro y hy
    have hb := mul_le_mul (abs_lt.mpr hy.1).le (hv₀ y hy)
      (abs_nonneg _) (le_of_lt hR)
    apply (le_abs_self _).trans
    simpa only [abs_mul,f₀,mul_add,mul_assoc] using hb
  have hgl : ∀ y∈V, ∀ z,
      |(y+A₀ z).1*f (y+A₀ z).2-y.1*f y.2| ≤ (R*H)*‖z‖ := by
    intro y hy z
    rw [heShift]
    change |y.1*f (y.2+A z)-y.1*f y.2| ≤ _
    rw [←mul_sub,abs_mul]
    have hb := mul_le_mul_of_nonneg_left (hlip y.2 hy.2 z) (abs_nonneg y.1)
    apply hb.trans
    have hHz : 0 ≤ H*‖z‖ := (abs_nonneg _).trans (hlip y.2 hy.2 z)
    have hh := mul_le_mul_of_nonneg_right (abs_lt.mpr hy.1).le hHz
    simpa only [mul_assoc] using hh
  obtain ⟨hlog,J,hJ,hj⟩ := log_gaussianShiftPartition_smooth_exp_jets N
    (fun y : ℝ×E => y.1*f y.2) V hV hg A₀ hs (R*B) (R*L) C Q (R*H)
    (mul_nonneg hR.le hL) (zero_le_one.trans hC) (zero_le_one.trans hQ) hgv hgjet hgl
  exact ⟨hlog,J,Q,hJ,hQ,hj⟩

end QuantitativePaper
