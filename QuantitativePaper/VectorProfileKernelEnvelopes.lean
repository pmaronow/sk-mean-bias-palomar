module
public import QuantitativePaper.VectorProfileInteriorSmooth
public import QuantitativePaper.CommonExponentialJetEnvelope

@[expose] public section

/-! Genuine common exponential envelopes for the raw and exponential
kernels of every actual affine-profile Gaussian cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def vectorProfileCellExponent (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ)
    (y : ℝ×VectorParameter n) : ℝ:=
  vectorProfileMass s₀ s₁ y.1 i*vectorProfileJointFunction s₀ s₁ β t j y

theorem exists_vectorProfileJointFunction_common_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (N j : ℕ) (a b : ℝ) (ha : 0<a) (hb : b<1) :
    ∃ C R : ℝ,1≤C ∧ 0≤R ∧ ∀ r,r≤N→∀ y : ℝ×VectorParameter n,y.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r (vectorProfileJointFunction s₀ s₁ β t j) y‖≤C*Real.exp (R*‖y‖) := by
  obtain ⟨hs,K,D,hK,hD,hj⟩:=vectorProfileJointFunction_smooth_exp_jets_on_cylinder
    (n:=n) s₀ s₁ β t ht N j a b ha hb
  obtain ⟨B,L,hB,hL,hvalue⟩:=vectorProfileJointFunction_linear_growth (n:=n) s₀ s₁ β t ht j
  exact exists_common_exponential_jet_envelope N _ {y : ℝ×VectorParameter n|y.1∈Ioo a b}
    B L K D hB hL hK (zero_le_one.trans hD)
    (fun y hy=>hvalue y ⟨(ha.trans hy.1).le,(hy.2.trans hb).le⟩) hj

theorem contDiffAt_vectorProfileCellExponent (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (i j : ℕ) (y : ℝ×VectorParameter n) (hθ : y.1∈Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileCellExponent s₀ s₁ β t i j) y := by
  have hm : ContDiff ℝ ∞ (fun z : ℝ×VectorParameter n=>vectorProfileMass s₀ s₁ z.1 i):=by
    unfold vectorProfileMass
    fun_prop
  exact hm.contDiffAt.mul (contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j y hθ)

theorem exists_vectorProfileCellExponent_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (N i j : ℕ) (hi : i≤k+1)
    (a b : ℝ) (ha : 0<a) (hb : b<1) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ r,r≤N→∀ y : ℝ×VectorParameter n,y.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r (fun z=>Real.exp (vectorProfileCellExponent s₀ s₁ β t i j z)) y‖≤
        C*Real.exp (R*‖y‖) := by
  let U : Set (ℝ×VectorParameter n):={y|y.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  have hphys (y : ℝ×VectorParameter n) (hy : y∈U) : y.1∈Icc (0 : ℝ) 1:=
    ⟨(ha.trans hy.1).le,(hy.2.trans hb).le⟩
  obtain ⟨hf,K,D,hK,hD,hfj⟩:=vectorProfileJointFunction_smooth_exp_jets_on_cylinder
    (n:=n) s₀ s₁ β t ht N j a b ha hb
  obtain ⟨B,L,hB,hL,hvalue⟩:=vectorProfileJointFunction_linear_growth (n:=n) s₀ s₁ β t ht j
  have hv : ∀ y∈U,|vectorProfileJointFunction s₀ s₁ β t j y|≤B+L*‖y‖:=
    fun y hy=>hvalue y (hphys y hy)
  let m : ℝ×VectorParameter n→ℝ:=fun y=>vectorProfileMass s₀ s₁ y.1 i
  have hm : ContDiffOn ℝ N m U:=(contDiff_vectorProfileMass s₀ s₁ i N).comp contDiff_fst |>.contDiffOn
  obtain ⟨M,hM,hMj⟩:=exists_vectorProfileMass_cylinder_bound (n:=n) s₀ s₁ i N a b
  obtain ⟨hG,KG,DG,hKG,hDG,hGj⟩:=mul_smooth_exp_jets_on_open N
    (vectorProfileJointFunction (n:=n) s₀ s₁ β t j) m U hU hf hm B L K D M
    hB hL hK (zero_le_one.trans hD) hM hv hfj
    (fun r hr y hy=>hMj r hr y ⟨hy.1.le,hy.2.le⟩)
  have hGvalue : ∀ y∈U,vectorProfileCellExponent s₀ s₁ β t i j y≤B+L*‖y‖:=by
    intro y hy
    have hmass:=vectorProfileMass_mem_unit s₀ s₁ i hi y.1 (hphys y hy)
    apply (le_abs_self _).trans
    change |m y*vectorProfileJointFunction s₀ s₁ β t j y|≤_
    rw [abs_mul,abs_of_nonneg hmass.1]
    exact (mul_le_mul_of_nonneg_right hmass.2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hv y hy)
  exact exists_exp_common_exponential_jet_envelope N (vectorProfileCellExponent s₀ s₁ β t i j)
    U hU hG B L KG DG hL (zero_le_one.trans hKG) (zero_le_one.trans hDG) hGvalue hGj

end QuantitativePaper
