module
public import QuantitativeFollowup.FollowupCavityDecouplingFinite
public import QuantitativeFollowup.AnisotropicTerminalFeatures

@[expose] public section

/-! Exact old-spin terminal expectations at zero incident coupling. The
finite Gibbs normalization is factored from the actual Hamiltonian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass.AT
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

 theorem followupCavityPartition_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    gtStatePartition (fun _ : Configuration (n+1)=>0)
      (anisotropicEnergyMap (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩)
        (anisotropicParameterPoint g x))=
      gtStatePartition (fun _ : Configuration n=>0)
        (anisotropicEnergyMap (followupCavityRestSpinModel n β ρ hβ hρ)
          (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)))*
      (∑b : Bool,Real.exp (x (Fin.last n)*Paper.spinSign b)) := by
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let fg:=fun σ : Configuration n=>Real.exp (anisotropicHamiltonian R
    (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x) σ)
  let fs:=fun b : Bool=>Real.exp (x (Fin.last n)*Paper.spinSign b)
  simp only [gtStatePartition,anisotropicEnergyMap_apply,add_zero,anisotropicTerminalLinear_apply]
  calc
    _=∑p : Configuration n×Bool,fg p.1*fs p.2 := by
      apply Fintype.sum_equiv (cavitySpinSplitEquiv n)
      intro σ
      rw [followupCavityHamiltonian_zero]
      simp only [fg,fs,R,cavitySpinSplitEquiv_fst,cavitySpinSplitEquiv_snd,Real.exp_add]
    _=_ := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]

 theorem cavityTerminalRestFeature_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1))
    (f : Configuration n→ℝ) :
    anisotropicTerminalFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩)
      (fun σ=>f (cavityRestConfiguration σ)) (anisotropicParameterPoint g x)=
      anisotropicTerminalFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) f
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let Pr:=anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)
  let Zr:=gtStatePartition (fun _ : Configuration n=>0) (anisotropicEnergyMap R Pr)
  let Zs:=∑b : Bool,Real.exp (x (Fin.last n)*Paper.spinSign b)
  have hZs : Zs≠0 := (Finset.sum_pos (fun _ _=>Real.exp_pos _) Finset.univ_nonempty).ne'
  have hZr : Zr≠0 :=gtStatePartition_ne_zero _ _
  have hi (σ : Configuration (n+1)) :
      gtStateGibbs (fun _ : Configuration (n+1)=>0) (anisotropicEnergyMap D (anisotropicParameterPoint g x)) σ=
        gtStateGibbs (fun _ : Configuration n=>0) (anisotropicEnergyMap R Pr) (cavityRestConfiguration σ)*
          (Real.exp (x (Fin.last n)*Paper.spinSign (σ (Fin.last n)))/Zs) := by
    rw [gtStateGibbs,gtStateGibbs]
    dsimp only [D]
    rw [followupCavityPartition_zero]
    simp only [anisotropicEnergyMap_apply,add_zero,anisotropicTerminalLinear_apply]
    rw [followupCavityHamiltonian_zero,Real.exp_add]
    simp only [div_eq_mul_inv,mul_inv_rev,anisotropicTerminalLinear_apply,R,Pr,Zs]
    ring
  change (∫σ,f (cavityRestConfiguration σ) ∂finiteStateGibbsKernel
    (fun _ : Configuration (n+1)=>0) (anisotropicEnergyMap D (anisotropicParameterPoint g x)))=
    ∫σ,f σ ∂finiteStateGibbsKernel (fun _ : Configuration n=>0) (anisotropicEnergyMap R Pr)
  rw [integral_finiteStateGibbsKernel,integral_finiteStateGibbsKernel]
  simp_rw [hi]
  have hs : (∑σ : Configuration (n+1),
      (gtStateGibbs (fun _ : Configuration n=>0) (anisotropicEnergyMap R Pr) (cavityRestConfiguration σ)*
       (Real.exp (x (Fin.last n)*Paper.spinSign (σ (Fin.last n)))/Zs))*f (cavityRestConfiguration σ))=
      ∑p : Configuration n×Bool,
        (gtStateGibbs (fun _ : Configuration n=>0) (anisotropicEnergyMap R Pr) p.1*f p.1)*
        (Real.exp (x (Fin.last n)*Paper.spinSign p.2)/Zs) := by
    apply Fintype.sum_equiv (cavitySpinSplitEquiv n)
    intro σ
    simp only [cavitySpinSplitEquiv_fst,cavitySpinSplitEquiv_snd]
    ring
  rw [hs,Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum,←Finset.sum_div]
  change (∑σ : Configuration n,gtStateGibbs (fun _ : Configuration n=>0) (anisotropicEnergyMap R Pr) σ*f σ*
    (Zs/Zs))=_
  simp only [div_self hZs,mul_one,R,Pr]

end QuantitativeFollowup
