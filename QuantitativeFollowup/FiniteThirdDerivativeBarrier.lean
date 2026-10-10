module
public import QuantitativeFollowup.ThirdDerivativeBarrier
public import FRSB.BackwardsQNonnegative
public import FRSB.BackwardsFiniteLower

@[expose] public section

/-! The explicit strict third-derivative barrier is propagated along every
actual finite Parisi cell and across its atoms by the bounded maximum principle. -/
noncomputable section
open Set Filter SignType
open scoped Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 400000

private theorem finiteCell_third_classical {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β≠0) {p : ℕ} (hp : p≤k+1) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauD β (Paper.parisiSchemeMeasure s) 3) := by
  refine ⟨(continuous_backwardTauD β _ 3).continuousOn,
    ⟨uniformSpatialConstant β 2,(uniformSpatialConstant_pos β 2).le,fun τ _ x=>
      backwardTauD_uniform_bound β _ 2 (τ,x)⟩,?_,?_,?_⟩
  · intro τ hτ x
    exact (hasDerivAt_finiteCell_backwardTauD s β hβ hp
      (backwardCell_strict_of_mem s β hβ hτ) 3 hτ x).differentiableAt
  · intro τ hτ x
    exact (hasDerivAt_backwardTauD_spatial β hβ _ 3 τ x
      (backwardCell_mem_global s β hp hτ)).differentiableAt
  · intro τ hτ x
    rw [deriv_backwardTauD_spatial β hβ _ 3 τ (backwardCell_mem_global s β hp hτ)]
    exact (hasDerivAt_backwardTauD_spatial β hβ _ 4 τ x
      (backwardCell_mem_global s β hp hτ)).differentiableAt

private theorem finiteCell_third_generator {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β≠0) {p : ℕ} (hp : p≤k+1) {τ : ℝ}
    (hτ : τ∈Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (fun z=>s.m p*backwardTauD β (Paper.parisiSchemeMeasure s) 1 z)
      (backwardTauD β (Paper.parisiSchemeMeasure s) 3) (τ,x)=
      (3*s.m p*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x))*
        backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x) := by
  have hg:=backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
  rw [backwardGenerator,(hasDerivAt_finiteCell_backwardTauD s β hβ hp
    (backwardCell_strict_of_mem s β hβ hτ) 3 hτ x).deriv,
    deriv2_backwardTauD_spatial β hβ _ 3 τ x hg,
    (hasDerivAt_backwardTauD_spatial β hβ _ 3 τ x hg).deriv,
    backwardTauForcing_three]
  dsimp only [backwardDtJet]
  ring

theorem finiteCell_thirdDerivativeBarrier_le {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β≠0) {p : ℕ} (hp : p≤k+1)
    (hinitial : ∀x : ℝ,0≤x→thirdDerivativeBarrier (backwardCellStart s β p,x)≤
      -backwardTauD β (Paper.parisiSchemeMeasure s) 3 (backwardCellStart s β p,x)) :
    ∀τ∈Icc (backwardCellStart s β p) (backwardCellEnd s β p),∀x : ℝ,0≤x→
      thirdDerivativeBarrier (τ,x)≤-backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x) := by
  let μ:=Paper.parisiSchemeMeasure s
  let a:=backwardCellStart s β p
  let b:=backwardCellEnd s β p
  let drift:=fun z=>s.m p*backwardTauD β μ 1 z
  let κ:=fun z=>3*s.m p*backwardTauD β μ 2 z
  have hD:=finiteCell_third_classical s β hβ hp
  have ha : 0≤a := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_le_one (by omega)))
  have hab : a≤b := by
    have hq:=s.q_mono p hp
    dsimp [a,b,backwardCellStart,backwardCellEnd]
    nlinarith [sq_nonneg β]
  have hB:=thirdDerivativeBarrier_classicalCell a b ha
  have hv : IsBoundedClassicalCell a b (fun z=>(-1:ℝ)*backwardTauD β μ 3 z-thirdDerivativeBarrier z) :=
    hD.const_mul.sub hB
  have hh:=hv.supersolution_nonneg hab true drift κ 3 (by norm_num)
    (fun τ hτ x hx=>(backwardTau_drift_outward β hβ μ (s.m p) τ x
      ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)).trans (by norm_num))
    (by
      intro τ hτ x hx
      have hc:=(backwardTauC_pos_le_one β hβ μ τ x
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)).2
      dsimp only [κ]
      nlinarith [s.m_nonneg hp,s.m_le_one hp])
    (by
      intro τ hτ x hx
      have hg:=backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
      have hB0 : 0≤backwardTauD β μ 1 (τ,x) :=
        backwardB_nonneg β hβ μ (backwardTime β τ) x
          (backwardTime_mem β hβ τ hg) (show 0≤x from hx.le)
      have hB1:=(abs_le.mp (backwardTauB_abs_le_one β hβ μ τ x hg)).2
      have hm0:=s.m_nonneg hp
      have hm1:=s.m_le_one hp
      have hd : drift (τ,x)∈Icc (0:ℝ) 1 := by
        dsimp only [drift]
        exact ⟨mul_nonneg hm0 hB0,by nlinarith⟩
      have hk : 0≤κ (τ,x) := mul_nonneg (mul_nonneg (by norm_num) hm0)
        (backwardTauC_pos_le_one β hβ μ τ x hg).1.le
      have hbar:=thirdDerivativeBarrier_generator_nonpos drift τ x (κ (τ,x)) hx.le hd hk
      rw [backwardGenerator_sub hD.const_mul hB drift hτ,
        backwardGenerator_const_mul hD drift hτ,
        finiteCell_third_generator s β hβ hp hτ x]
      dsimp only [κ,drift,μ] at *
      nlinarith)
    (fun x hx=>by simpa only [neg_mul,one_mul] using sub_nonneg.mpr (hinitial x hx))
    (by
      intro _ τ hτ
      have hg:=backwardCell_mem_global s β hp hτ
      have ho:=backwardD_reflect β μ (backwardTime β τ) (backwardTime_mem β hβ τ hg) 3 0
      simp only [neg_zero] at ho
      norm_num at ho
      have hz : backwardTauD β μ 3 (τ,0)=0 := by
        change backwardD β μ 3 (backwardTime β τ,0)=0
        linarith
      simp only [hz,mul_zero,thirdDerivativeBarrier_zero,sub_self,le_refl])
  intro τ hτ x hx
  simpa only [neg_mul,one_mul] using sub_nonneg.mp (hh τ hτ x hx)

theorem finiteScheme_thirdDerivativeBarrier_le {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β≠0) :
    ∀p≤k+1,∀τ∈Icc (backwardCellStart s β p) (backwardCellEnd s β p),∀x : ℝ,0≤x→
      thirdDerivativeBarrier (τ,x)≤-backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x) := by
  apply backward_scheme_coefficient_induction s β
    (fun _ τ=>∀x : ℝ,0≤x→thirdDerivativeBarrier (τ,x)≤-backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x))
  · intro x hx
    simpa only [backwardTauD,backwardTime,zero_div,sub_zero,backwardD_three_terminal,neg_mul,
      neg_neg] using thirdDerivativeBarrier_terminal_le hx
  · exact fun p hp=>finiteCell_thirdDerivativeBarrier_le s β hβ hp
  · exact fun _ _ h=>h

end QuantitativeFollowup
