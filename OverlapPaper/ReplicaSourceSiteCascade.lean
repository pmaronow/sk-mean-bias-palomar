module
public import OverlapPaper.ReplicaSourceSiteFields
public import FourPapersCommon.FiniteStateCascadeSource

@[expose] public section

/-! The true constrained auxiliary replica cascade is bounded by the exact
single-site cascade. The marked source has the sharp one-site quadratic bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon SpinGlass.AT
set_option maxHeartbeats 1200000
variable {n d : ℕ}

 theorem replicaSourceAuxiliary_le_siteCascade (h θ : ℝ) (mark : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (hs : (replicaOverlapShell n d D η).Nonempty)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (v : ℕ → ℝ) (groupOf : ℕ → Fin d → Fin d)
    (J : ℕ) :
    finiteStateGaussianTerminalCascade (replicaSourceStatePotential (n := n) h θ mark D η) a
      (fun j => replicaGroupFieldCLM D η (v j) (groupOf j)) J 0 ≤
      (n : ℝ)*finiteStateGaussianCascade a
        (fun j => replicaSiteCopyGaussianCLM (v j) (groupOf j))
        (replicaSourceSingleSite h θ mark) J 0 := by
  classical
  rcases hs with ⟨σ,hσ⟩
  haveI : Nonempty (ReplicaSourceState n d D η) := ⟨⟨σ,hσ⟩⟩
  let T := replicaSiteRestrictedFieldCLM (n := n) D η
  let L := fun j => replicaSiteCopyGaussianCLM (v j) (groupOf j)
  let F := gtStateLogPartition (replicaSourceStatePotential (n := n) h θ mark D η)
  let f := replicaSourceSingleSite h θ mark
  have hmaps : (fun j => replicaGroupFieldCLM (n := n) D η (v j) (groupOf j)) =
      fun j => T.comp (finiteGaussianSiteLift (B := Fin n) (L j)) := by
    funext j
    exact replicaGroupFieldCLM_eq_site_lift D η (v j) (groupOf j)
  change finiteStateGaussianCascade a _ F J 0 ≤ _
  rw [hmaps]
  have he := finiteStateGaussianCascade_comp_linear T
    (fun j => finiteGaussianSiteLift (B := Fin n) (L j)) a F J 0
  simp only [map_zero] at he
  rw [he]
  have hFc := (finiteStateGaussianTerminal_lipschitz
    (replicaSourceStatePotential (n := n) h θ mark D η)).comp T.lipschitzWith
  have hfc := replicaSourceSingleSite_lipschitz h θ mark
  have hc := finiteStateGaussianCascade_mono a ha (fun j => finiteGaussianSiteLift (B := Fin n) (L j))
    (fun y => F (T y)) (finiteGaussianSiteSum (B := Fin n) f) hFc
    (finiteGaussianSiteSum_lipschitz f hfc)
    (fun y => replicaSite_constrained_terminal_le h θ mark D η ⟨σ,hσ⟩ y) J 0
  refine hc.trans_eq ?_
  rw [finiteStateGaussianCascade_site_sum a ha L f hfc J 0]
  simp only [map_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

 def replicaSourceSiteMarkedMean (h : ℝ) (mark : Finset (Fin d))
    (a : ℕ → ℝ) (v : ℕ → ℝ) (groupOf : ℕ → Fin d → Fin d) (J : ℕ) : ℝ :=
  ∫ ε : Configuration d, replicaSpinProduct mark ε
    ∂finiteStateCascadeGibbsKernel (fun ε => h*∑ l : Fin d, spin (ε l)) a
      (fun j => replicaSingleSiteSpinCLM.comp (replicaSiteCopyGaussianCLM (v j) (groupOf j))) J 0

 theorem replicaSourceSiteCascade_source_bound (h θ : ℝ) (mark : Finset (Fin d))
    (a : ℕ → ℝ) (ha : ∀ j, a j ∈ Icc 0 1)
    (v : ℕ → ℝ) (groupOf : ℕ → Fin d → Fin d) (J : ℕ) :
    finiteStateGaussianCascade a (fun j => replicaSiteCopyGaussianCLM (v j) (groupOf j))
      (replicaSourceSingleSite h θ mark) J 0 ≤
    finiteStateGaussianCascade a (fun j => replicaSiteCopyGaussianCLM (v j) (groupOf j))
      (replicaSourceSingleSite h 0 mark) J 0+
      θ*replicaSourceSiteMarkedMean h mark a v groupOf J+θ^2/2 := by
  classical
  let T := replicaSingleSiteSpinCLM (d := d)
  let L := fun j => replicaSiteCopyGaussianCLM (v j) (groupOf j)
  let V : Configuration d → ℝ := fun ε => h*∑ l : Fin d, spin (ε l)
  let P : Configuration d → ℝ := replicaSpinProduct mark
  have heθ : replicaSourceSingleSite h θ mark = fun x => gtStateLogPartition (fun ε => V ε+θ*P ε) (T x) :=
    funext (replicaSourceSingleSite_eq_terminal h θ mark)
  have he0 : replicaSourceSingleSite h 0 mark = fun x => gtStateLogPartition V (T x) := by
    funext x
    rw [replicaSourceSingleSite_eq_terminal]
    simp only [zero_mul,add_zero]
    rfl
  have hc := finiteStateGaussianTerminalCascade_source_bound V P
    (fun ε => (abs_replicaSpinProduct mark ε).le) θ a ha (fun j => T.comp (L j)) J 0
  have htθ := finiteStateGaussianCascade_comp_linear T L a (gtStateLogPartition (fun ε => V ε+θ*P ε)) J 0
  have ht0 := finiteStateGaussianCascade_comp_linear T L a (gtStateLogPartition V) J 0
  simp only [map_zero] at htθ ht0
  change finiteStateGaussianCascade a (fun j => T.comp (L j)) (gtStateLogPartition _) J 0-
    finiteStateGaussianCascade a (fun j => T.comp (L j)) (gtStateLogPartition V) J 0 ≤ _ at hc
  rw [htθ,ht0,←heθ,←he0] at hc
  change _ ≤ θ*replicaSourceSiteMarkedMean h mark a v groupOf J+θ^2/2 at hc
  linarith

end OverlapPaper
