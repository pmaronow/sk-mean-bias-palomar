module
public import QuantitativeFollowup.FollowupCavityDecouplingHamiltonian

@[expose] public section

/-! Exact product terminal partition for the genuine u=0 cavity model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavitySpinSplitEquiv (n : ℕ) : Configuration (n+1)≃Configuration n×Bool :=
  (Fin.insertNthEquiv (fun _ : Fin (n+1)=>Bool) (Fin.last n)).symm.trans (Equiv.prodComm _ _)

@[simp] theorem cavitySpinSplitEquiv_fst (n : ℕ) (σ : Configuration (n+1)) :
    (cavitySpinSplitEquiv n σ).1=cavityRestConfiguration σ := by
  funext i
  change σ ((Fin.last n).succAbove i)=σ i.castSucc
  rw [Fin.succAbove_last]
@[simp] theorem cavitySpinSplitEquiv_snd (n : ℕ) (σ : Configuration (n+1)) :
    (cavitySpinSplitEquiv n σ).2=σ (Fin.last n) := rfl

def cavityScalarTerminal (x : ℝ) : ℝ :=
  Real.log (∑b : Bool,Real.exp (x*Paper.spinSign b))

theorem followupCavityTerminal_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicGridTerminalPotential (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩)
      (anisotropicParameterPoint g x)=
      anisotropicGridTerminalPotential (followupCavityRestSpinModel n β ρ hβ hρ)
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x))+
      cavityScalarTerminal (x (Fin.last n)) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let fg:=fun σ : Configuration n=>Real.exp (anisotropicHamiltonian R
    (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x) σ)
  let fs:=fun b : Bool=>Real.exp (x (Fin.last n)*Paper.spinSign b)
  have hs : (∑σ : Configuration (n+1),Real.exp (anisotropicHamiltonian D g x σ))=
      (∑σ : Configuration n,fg σ)*(∑b : Bool,fs b) := by
    calc
      _=∑p : Configuration n×Bool,fg p.1*fs p.2 := by
        apply Fintype.sum_equiv (cavitySpinSplitEquiv n)
        intro σ
        dsimp only [D]
        rw [followupCavityHamiltonian_zero]
        simp only [fg,fs,R,cavitySpinSplitEquiv_fst,cavitySpinSplitEquiv_snd,Real.exp_add]
      _=_ := by rw [Fintype.sum_prod_type,Finset.sum_mul];apply Finset.sum_congr rfl;intro σ _;rw [Finset.mul_sum]
  have hg : 0<∑σ : Configuration n,fg σ :=
    Finset.sum_pos (fun _ _=>Real.exp_pos _) (Finset.univ_nonempty)
  have hx : 0<∑b : Bool,fs b :=
    Finset.sum_pos (fun _ _=>Real.exp_pos _) (Finset.univ_nonempty)
  unfold anisotropicGridTerminalPotential finiteLinearSoftmax finiteLinearPartition cavityScalarTerminal
  simp_rw [anisotropicTerminalLinear_apply]
  change Real.log (∑σ : Configuration (n+1),Real.exp (anisotropicHamiltonian D g x σ))=_
  rw [hs,Real.log_mul hg.ne' hx.ne']

end QuantitativeFollowup
