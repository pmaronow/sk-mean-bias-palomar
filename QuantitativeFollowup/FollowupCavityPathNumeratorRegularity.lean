module
public import QuantitativeFollowup.FollowupCavityPathNumerator

@[expose] public section

/-! Genuine exponential integrability envelopes for the unnormalized
physical marked density and all its joint parameter/spatial jets. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

private theorem weighted_list_exponential_smooth {E A : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set E) (f : A→E→ℝ)
    (hf : ∀a,ExponentialSmoothOn (f a) U) (cs : List (ℝ×A)) :
    ExponentialSmoothOn (fun x=>(cs.map (fun c=>c.1*f c.2 x)).sum) U := by
  induction cs with
  | nil => exact ExponentialSmoothOn.const 0 U
  | cons c cs ih =>
      have hh:=(hf c.2).compCLM (ContinuousLinearMap.lsmul ℝ ℝ c.1)
      simpa only [List.map_cons,List.sum_cons,Function.comp_def,ContinuousLinearMap.lsmul_apply,smul_eq_mul]
        using hh.add ih

private theorem weighted_list_linear_bound {E A : Type} [NormedAddCommGroup E]
    (U : Set ℝ) (f : A→ℝ×E→ℝ)
    (hf : ∀a,∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀b∈U,∀z,|f a (b,z)|≤B+L*‖z‖)
    (cs : List (ℝ×A)) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀b∈U,∀z:E,
      |(cs.map (fun c=>c.1*f c.2 (b,z))).sum|≤B+L*‖z‖ := by
  induction cs with
  | nil => exact ⟨0,0,le_rfl,le_rfl,by simp⟩
  | cons c cs ih =>
      obtain ⟨B,L,hB,hL,hb⟩:=hf c.2
      obtain ⟨C,D,hC,hD,hc⟩:=ih
      refine ⟨|c.1| * B+C,|c.1| * L+D,by positivity,by positivity,?_⟩
      intro b hb' z
      simp only [List.map_cons,List.sum_cons]
      apply (abs_add_le _ _).trans
      rw [abs_mul]
      have hh:=mul_le_mul_of_nonneg_left (hb b hb' z) (abs_nonneg c.1)
      have hi:=hc b hb' z
      nlinarith only [hh,hi]

theorem exponentialSmoothOn_cavityPathChargePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (l u : ℝ) (hl : 0<l) :
    ExponentialSmoothOn (cavityPathChargePotential D s a i T)
      ((Ioo l u)×ˢ(univ : Set (CavityPathGaussianSpace T n))) :=
  weighted_list_exponential_smooth _ _
    (fun v=>exponentialSmoothOn_cavityPathVertexPotential D s i T hj v l u hl) _

theorem cavityPathChargePotential_linear_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (l u : ℝ) (hl : 0<l) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀b∈Ioo l u,∀z : CavityPathGaussianSpace T n,
      |cavityPathChargePotential D s a i T (b,z)|≤B+L*‖z‖ :=
  weighted_list_linear_bound _ _ (fun v=>cavityPathVertexPotential_linear_bound D s i T hj v l u hl) _

theorem exponentialSmoothOn_cavityPathLogNumerator (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (σ : TerminalSpins (Configuration n) T) (l u : ℝ) (hl : 0<l) :
    ExponentialSmoothOn (cavityPathLogNumerator D s a i T σ)
      ((Ioo l u)×ˢ(univ : Set (CavityPathGaussianSpace T n))) :=
  (exponentialSmoothOn_linear ((cavityPathTerminalEnergy D s i T σ).comp
    (ContinuousLinearMap.snd ℝ ℝ (CavityPathGaussianSpace T n))) _).sub
      (exponentialSmoothOn_cavityPathChargePotential D s a i T hj l u hl)

theorem cavityPathLogNumerator_linear_bound (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (σ : TerminalSpins (Configuration n) T) (l u : ℝ) (hl : 0<l) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀b∈Ioo l u,∀z : CavityPathGaussianSpace T n,
      |cavityPathLogNumerator D s a i T σ (b,z)|≤B+L*‖z‖ := by
  obtain ⟨B,L,hB,hL,hb⟩:=cavityPathChargePotential_linear_bound D s a i T hj l u hl
  refine ⟨B,L+‖cavityPathTerminalEnergy D s i T σ‖,hB,by positivity,?_⟩
  intro b hb' z
  unfold cavityPathLogNumerator
  apply (abs_sub _ _).trans
  have hE:=(cavityPathTerminalEnergy D s i T σ).le_opNorm z
  rw [Real.norm_eq_abs] at hE
  have hh:=hb b hb' z
  nlinarith only [hE,hh]

def cavityPathNumerator (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (w : ℝ×CavityPathGaussianSpace T n) : ℝ := Real.exp (cavityPathLogNumerator D s a i T σ w)

theorem exponentialSmoothOn_cavityPathNumerator (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (σ : TerminalSpins (Configuration n) T) (l u : ℝ) (hl : 0<l) :
    ExponentialSmoothOn (cavityPathNumerator D s a i T σ)
      ((Ioo l u)×ˢ(univ : Set (CavityPathGaussianSpace T n))) := by
  obtain ⟨B,L,hB,hL,hb⟩:=cavityPathLogNumerator_linear_bound D s a i T hj σ l u hl
  apply exponentialSmoothOn_exp_of_linear_bound _ _
    (exponentialSmoothOn_cavityPathLogNumerator D s a i T hj σ l u hl) B L hL
  intro w hw
  apply (le_abs_self _).trans ((hb w.1 hw.1 w.2).trans ?_)
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (norm_snd_le w) hL)

theorem contDiffOn_cavityPathNumerator (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hj : j≤k+2) (σ : TerminalSpins (Configuration n) T) (l u : ℝ) (hl : 0<l) :
    ContDiffOn ℝ ∞ (cavityPathNumerator D s a i T σ)
      ((Ioo l u)×ˢ(univ : Set (CavityPathGaussianSpace T n))) :=
  fun w hw=>(exponentialSmoothOn_cavityPathNumerator D s a i T hj σ l u hl).smooth w hw
    |>.contDiffWithinAt

end QuantitativeFollowup
