module
public import OverlapPaper.ReplicaSourceSiteBaselineStep
public import OverlapPaper.ReplicaSourceSiteCascade

@[expose] public section

/-! The chronological grouped site cascade has the literal scalar Parisi
baseline. Refinement and fiber cardinalities are geometric assumptions only;
no scalar baseline identity is supplied as an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
variable {d g : ℕ}

 theorem replicaSourceSingleSite_zero (h : ℝ) (mark : Finset (Fin d))
    (H : FiniteStateField (Fin d)) :
    replicaSourceSingleSite h 0 mark H=(d : ℝ)*Real.log 2+∑ l : Fin d, Real.log (Real.cosh (h+H l)) := by
  classical
  unfold replicaSourceSingleSite replicaSourceTerminal
  simp only [zero_mul,add_zero]
  change Real.log (replicaTerminalBasePartition (fun l => h+H l)) = _
  rw [replicaTerminalBasePartition_eq,Real.log_prod (fun l _ => (mul_pos (by norm_num) (Real.cosh_pos _)).ne')]
  simp_rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) (Real.cosh_pos _).ne']
  rw [Finset.sum_add_distrib]
  simp

 theorem mixed_replica_site_shifted_baseline_step {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ) (hp : p≤k+1)
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (hrep : ∀ j, groupOf (representative j)=j) (c : ℕ) (hc : 0<c)
    (hcard : ∀ j, (Finset.univ.filter (fun l => groupOf l=j)).card=c)
    (h : ℝ) (H : FiniteStateField (Fin d)) (hH : ∀ l, H l=H (representative (groupOf l)))
    (C : ℝ) (F : FiniteStateField (Fin d) → ℝ) (hF : Measurable F)
    (hbaseline : ∀ y, (∀ l, y l=y (representative (groupOf l))) →
      F y=(∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),h+y l))+C) :
    finiteStateGaussianStep (s.m p/c)
      (replicaSiteCopyGaussianCLM (ξ.first (s.q (p+1))-ξ.first (s.q p)) groupOf) F H=
      (∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q p,h+H l))+C := by
  let W : FiniteStateField (Fin d) := WithLp.toLp 2 (fun _ => h)
  let F' := fun y => F (y-W)
  have he := mixed_replica_site_baseline_step ξ s p hp groupOf representative hrep c hc hcard
    (H+W) (fun l => by simp only [WithLp.ofLp_add,Pi.add_apply,W,WithLp.ofLp_toLp]; rw [hH l]) C F'
    (hF.comp (by fun_prop)) (by
      intro y hy
      have hsub : ∀ l, (y-W) l=(y-W) (representative (groupOf l)) := by
        intro l
        simp only [WithLp.ofLp_sub,Pi.sub_apply,W,WithLp.ofLp_toLp]
        rw [hy l]
      change F (y-W)=_
      rw [hbaseline _ hsub]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      simp only [WithLp.ofLp_sub,Pi.sub_apply,W,WithLp.ofLp_toLp]
      congr 1
      ext <;> simp)
  have hf : (fun z => F' ((H+W)+replicaSiteCopyGaussianCLM
      (ξ.first (s.q (p+1))-ξ.first (s.q p)) groupOf z))=
      fun z => F (H+replicaSiteCopyGaussianCLM
        (ξ.first (s.q (p+1))-ξ.first (s.q p)) groupOf z) := by
    funext z
    congr 1
    simp only [F']
    abel
  simpa only [finiteStateGaussianStep,hf,WithLp.ofLp_add,Pi.add_apply,W,WithLp.ofLp_toLp,add_comm] using he

/-- Actual grouped chronology, expressed on the physical scheme's reverse
levels. The partitions may use redundant Gaussian labels; each compressed
partition has its literal common fiber size. -/
 theorem replicaSourceSiteCascade_baseline {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (mark : Finset (Fin d))
    (groupOf : ℕ → Fin d → Fin d) (c : ℕ → ℕ)
    (hc : ∀ j<k+2, 0<c j)
    (hcomp : ∀ j<k+2, ∃ b : ℕ, ∃ group : Fin d → Fin b, ∃ rep : Fin b → Fin d,
      (∀ i, group (rep i)=i) ∧
      (∀ i, (Finset.univ.filter (fun l => group l=i)).card=c j) ∧
      (∀ l m, groupOf j l=groupOf j m ↔ group l=group m))
    (hrefine : ∀ j<k+1, ∀ l m, groupOf j l=groupOf j m → groupOf (j+1) l=groupOf (j+1) m)
    (j : ℕ) (hj : j≤k+2) (H : FiniteStateField (Fin d))
    (hH : ∀ l m, groupOf (j-1) l=groupOf (j-1) m → H l=H m) :
    finiteStateGaussianCascade (fun i => s.m (k+1-i)/(c i : ℝ))
      (fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i))) (groupOf i))
      (replicaSourceSingleSite h 0 mark) j H=
      (d : ℝ)*Real.log 2+∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (k+2-j),h+H l) := by
  classical
  induction j generalizing H with
  | zero =>
    simp only [finiteStateGaussianCascade,Nat.sub_zero,s.q_top,mixedPotential_terminal]
    exact replicaSourceSingleSite_zero h mark H
  | succ j ih =>
    have hj0 : j<k+2 := by omega
    rcases hcomp j hj0 with ⟨b,group,rep,hrep,hcard,hpart⟩
    let v := ξ.first (s.q (k+2-j))-ξ.first (s.q (k+1-j))
    have hp : k+1-j≤k+1 := Nat.sub_le _ _
    have hidx : k+1-j+1=k+2-j := by omega
    have hv : 0≤v := by
      dsimp [v]
      rw [←hidx]
      exact sub_nonneg.mpr (ξ.first_strictMonoOn.monotoneOn
        ⟨by linarith [s.q_nonneg (show k+1-j≤k+2 by omega)],s.q_le_one (by omega)⟩
        ⟨by linarith [s.q_nonneg (show k+1-j+1≤k+2 by omega)],s.q_le_one (by omega)⟩
        (s.q_mono _ hp))
    let F := finiteStateGaussianCascade (fun i => s.m (k+1-i)/(c i : ℝ))
      (fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i))) (groupOf i))
      (replicaSourceSingleSite h 0 mark) j
    have ha (i : ℕ) : 0 ≤ s.m (k+1-i)/(c i : ℝ) := div_nonneg
      (s.m_nonneg (show k+1-i≤k+1 from Nat.sub_le _ _)) (Nat.cast_nonneg _)
    have hFc : Measurable F := (finiteStateGaussianCascade_lipschitz _
      (replicaSourceSingleSite_lipschitz h 0 mark) _ ha _ j).continuous.measurable
    change finiteStateGaussianStep _ _ F H=_
    rw [replicaSiteCopyGaussian_step_eq_of_partition v hv (groupOf j) group hpart _ F hFc H]
    have hH' (l : Fin d) : H l=H (rep (group l)) := by
      apply hH l (rep (group l))
      simp only [Nat.succ_sub_one]
      exact (hpart _ _).mpr (by rw [hrep])
    have hb (y : FiniteStateField (Fin d)) (hy : ∀ l, y l=y (rep (group l))) :
        F y=(∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (k+1-j+1),h+y l))+(d : ℝ)*Real.log 2 := by
      have hprev (l m : Fin d) (heq : groupOf (j-1) l=groupOf (j-1) m) : y l=y m := by
        have hg : groupOf j l=groupOf j m := by
          by_cases hjz : j=0
          · simpa only [hjz,Nat.zero_sub] using heq
          · have he := hrefine (j-1) (by omega) l m heq
            simpa only [show j-1+1=j by omega] using he
        rw [hy l,hy m,(hpart l m).mp hg]
      have he := ih (by omega) y hprev
      dsimp [F]
      rw [hidx]
      linarith
    have he := mixed_replica_site_shifted_baseline_step ξ s (k+1-j) hp group rep hrep
      (c j) (hc j hj0) hcard h H hH' ((d : ℝ)*Real.log 2) F hFc hb
    simpa only [hidx,v,show k+2-(j+1)=k+1-j by omega,add_comm] using he

 theorem replicaSourceSiteCascade_baseline_zero {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (mark : Finset (Fin d))
    (groupOf : ℕ → Fin d → Fin d) (c : ℕ → ℕ)
    (hc : ∀ j<k+2, 0<c j)
    (hcomp : ∀ j<k+2, ∃ b : ℕ, ∃ group : Fin d → Fin b, ∃ rep : Fin b → Fin d,
      (∀ i, group (rep i)=i) ∧
      (∀ i, (Finset.univ.filter (fun l => group l=i)).card=c j) ∧
      (∀ l m, groupOf j l=groupOf j m ↔ group l=group m))
    (hrefine : ∀ j<k+1, ∀ l m, groupOf j l=groupOf j m → groupOf (j+1) l=groupOf (j+1) m) :
    finiteStateGaussianCascade (fun i => s.m (k+1-i)/(c i : ℝ))
      (fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i))) (groupOf i))
      (replicaSourceSingleSite h 0 mark) (k+2) 0=
      (d : ℝ)*(Real.log 2+mixedPotential ξ (Paper.parisiSchemeMeasure s) (0,h)) := by
  have he := replicaSourceSiteCascade_baseline ξ s h mark groupOf c hc hcomp hrefine
    (k+2) le_rfl 0 (fun _ _ _ => rfl)
  simpa only [Nat.sub_self,s.q_zero,WithLp.ofLp_zero,Pi.zero_apply,add_zero,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_add] using he

end OverlapPaper
