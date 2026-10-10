module
public import QuantitativeFollowup.FollowupCavityDecouplingCoordinates

@[expose] public section

/-! Literal u=0 Hamiltonian separation. Every incident coefficient is zero;
the old disorder and the final spin are retained explicitly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityRestConfiguration (σ : Configuration (n+1)) : Configuration n :=
  fun i=>σ i.castSucc

theorem cavityZeroCoupling_rest (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (e : AnisotropicCouplingIndex n) :
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩).coupling (cavityRestCouplingEmbedding n e)=
      (followupCavityRestSpinModel n β ρ hβ hρ).coupling e := by
  simp only [followupCavitySpinModel,followupCavityRestSpinModel,cavityRestCouplingEmbedding_fst,cavityRestCouplingEmbedding_snd,
    Fin.castSucc_inj,Fin.castSucc_ne_last,ite_false]

theorem cavityZeroCoupling_complement (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (e : AnisotropicCouplingIndex (n+1))
    (he : e∉Finset.univ.map (cavityRestCouplingEmbedding n)) :
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩).coupling e=0 := by
  have hl : e.1.2=Fin.last n := by
    by_contra h2
    have h1 : e.1.1≠Fin.last n := by
      intro h1
      have hh : Fin.last n≤e.1.2 := h1 ▸ e.2
      exact h2 (le_antisymm (Fin.le_last _) hh)
    let f : AnisotropicCouplingIndex n:=⟨(e.1.1.castPred h1,e.1.2.castPred h2),
      (Fin.castPred_le_castPred_iff (hi:=h1) (hj:=h2)).mpr e.2⟩
    have hf : cavityRestCouplingEmbedding n f=e := by
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.castSucc_castPred e.1.1 h1
      · exact Fin.castSucc_castPred e.1.2 h2
    apply he
    exact Finset.mem_map.mpr ⟨f,Finset.mem_univ _,hf⟩
  simp only [followupCavitySpinModel,hl,ite_true,followupCavityRowCoupling_zero]
  split_ifs <;> rfl

theorem followupCavityHamiltonian_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (g : AnisotropicDisorder (n+1))
    (x : QuantitativePaper.Field (n+1)) (σ : Configuration (n+1)) :
    anisotropicHamiltonian (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) g x σ=
      anisotropicHamiltonian (followupCavityRestSpinModel n β ρ hβ hρ)
        (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x) (cavityRestConfiguration σ)+
      x (Fin.last n)*Paper.spinSign (σ (Fin.last n)) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let f : AnisotropicCouplingIndex (n+1)→ℝ:=fun e=>
    D.coupling e*g e*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)
  have hs : (∑e : AnisotropicCouplingIndex (n+1),f e)=
      ∑e : AnisotropicCouplingIndex n,f (cavityRestCouplingEmbedding n e) := by
    rw [←Finset.sum_map]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    simp only [f,D,cavityZeroCoupling_complement n β ρ hβ hρ e he,zero_mul]
  unfold anisotropicHamiltonian
  change (∑e : AnisotropicCouplingIndex (n+1),f e)+fieldDot x σ=_
  rw [hs]
  unfold fieldDot
  rw [Fin.sum_univ_castSucc]
  simp only [f,D,cavityZeroCoupling_rest,cavityRestDisorderProjection_apply,
    cavityRestCouplingEmbedding_fst,cavityRestCouplingEmbedding_snd,cavityRestFieldProjection_apply,cavityRestConfiguration]
  ring

end QuantitativeFollowup
