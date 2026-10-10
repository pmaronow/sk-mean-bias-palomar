module
public import OverlapPaper.ReplicaSourceSiteStepLaw
public import OverlapPaper.ReplicaSourceSiteMarkedTransport
public import OverlapPaper.ReplicaSourcePartitionCompression

@[expose] public section

/-! Composition of the genuine normalized copy-Gaussian site cascade with
its actual scalar grouped Parisi transitions. No endpoint law is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {d g : ℕ}

 theorem integral_copyGaussianStepLaw_congr_on_partition (a v : ℝ)
    (group : Fin d → Fin g) (F : FiniteStateField (Fin d) → ℝ)
    (H : FiniteStateField (Fin d))
    (hH : ∀ l m, group l=group m → H l=H m)
    (A B : FiniteStateField (Fin d) → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : ∀ y, (∀ l m, group l=group m → y l=y m) → A y=B y) :
    (∫ y, A y ∂finiteStateGaussianStepLaw a (replicaSiteCopyGaussianCLM v group) F H)=
      ∫ y, B y ∂finiteStateGaussianStepLaw a (replicaSiteCopyGaussianCLM v group) F H := by
  apply integral_congr_ae
  apply (tilted_absolutelyContinuous _ _).ae_eq
  rw [finiteStateGaussianRawKernel_apply]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun hA hB)).mpr
  exact Filter.Eventually.of_forall fun z => hAB _ (fun l m he => by
    simp only [WithLp.ofLp_add,Pi.add_apply,replicaSiteCopyGaussianCLM_apply]
    rw [hH l m he,he])

 theorem replicaSiteCopyGaussian_stepLaw_eq_of_partition (v : ℝ) (hv : 0≤v)
    (group : Fin d → Fin g) (other : Fin d → Fin d)
    (hpart : ∀ l m, group l=group m ↔ other l=other m)
    (a : ℝ) (F : FiniteStateField (Fin d) → ℝ) (H : FiniteStateField (Fin d)) :
    finiteStateGaussianStepLaw a (replicaSiteCopyGaussianCLM v group) F H=
      finiteStateGaussianStepLaw a (replicaSiteCopyGaussianCLM v other) F H := by
  apply finiteStateGaussianStepLaw_eq_of_spectral_covariance _ _ _ a F H
  intro l m
  rw [replicaSiteCopyGaussian_spectral v hv group,replicaSiteCopyGaussian_spectral v hv other]
  simp only [hpart]

 theorem replicaSourceSiteExpectation_eq_scalarGroups {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (mark : Finset (Fin d))
    (groupOf : ℕ → Fin d → Fin d) (c b : ℕ → ℕ)
    (group : (j : ℕ) → Fin d → Fin (b j)) (rep : (j : ℕ) → Fin (b j) → Fin d)
    (hc : ∀ j<k+2, 0<c j)
    (hrep : ∀ j<k+2, ∀ i, group j (rep j i)=i)
    (hcard : ∀ j<k+2, ∀ i, (Finset.univ.filter (fun l => group j l=i)).card=c j)
    (hpart : ∀ j<k+2, ∀ l m, groupOf j l=groupOf j m ↔ group j l=group j m)
    (hrefine : ∀ j<k+1, ∀ l m, groupOf j l=groupOf j m → groupOf (j+1) l=groupOf (j+1) m)
    (j : ℕ) (hj : j≤k+2) (H : FiniteStateField (Fin d))
    (hH : ∀ l m, groupOf (j-1) l=groupOf (j-1) m → H l=H m) :
    sourceKernelExpectation
      (finiteStateGaussianCascadeKernel (fun i => s.m (k+1-i)/(c i : ℝ))
        (fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i))) (groupOf i))
        (replicaSourceSingleSite h 0 mark)) j
      (fun y => replicaTerminalCoefficient mark (replicaSiteAbsoluteField h y)) H=
    sourceKernelExpectation
      (fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s (k+1-i)) (group i) (rep i)) j
      (replicaTerminalCoefficient mark) (replicaSiteAbsoluteField h H) := by
  classical
  let a := fun i => s.m (k+1-i)/(c i : ℝ)
  let L := fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i))) (groupOf i)
  let F := replicaSourceSingleSite h 0 mark
  let Q := fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s (k+1-i)) (group i) (rep i)
  have ha (i : ℕ) : 0≤a i := div_nonneg
    (s.m_nonneg (show k+1-i≤k+1 from Nat.sub_le _ _)) (Nat.cast_nonneg _)
  have hcomp (i : ℕ) (hi : i<k+2) : ∃ b : ℕ, ∃ group : Fin d → Fin b, ∃ rep : Fin b → Fin d,
      (∀ j, group (rep j)=j) ∧
      (∀ j, (Finset.univ.filter (fun l => group l=j)).card=c i) ∧
      (∀ l m, groupOf i l=groupOf i m ↔ group l=group m) :=
    ⟨b i,group i,rep i,hrep i hi,hcard i hi,hpart i hi⟩
  have hm : Measurable (replicaTerminalCoefficient mark) := (continuous_replicaTerminalCoefficient mark).measurable
  have hsm : Measurable (fun y => replicaTerminalCoefficient mark (replicaSiteAbsoluteField h y)) :=
    hm.comp (measurable_replicaSiteAbsoluteField h)
  have hqm (i : ℕ) : IsMarkovKernel (Q i) := by
    haveI := isMarkovKernel_mixedSchemeScalarStep ξ s (p := k+1-i) (Nat.sub_le _ _)
    exact isMarkovKernel_replicaGroupKernel _ _ _
  induction j generalizing H with
  | zero => rfl
  | succ j ih =>
    have hj0 : j<k+2 := by omega
    have hp : k+1-j≤k+1 := Nat.sub_le _ _
    have hidx : k+1-j+1=k+2-j := by omega
    let U := finiteStateGaussianCascade a L F j
    have hUc : Measurable U := (finiteStateGaussianCascade_lipschitz F
      (replicaSourceSingleSite_lipschitz h 0 mark) a ha L j).continuous.measurable
    have hH' (l : Fin d) : H l=H (rep j (group j l)) := by
      apply hH l (rep j (group j l))
      simp only [Nat.succ_sub_one]
      exact (hpart j hj0 _ _).mpr (by rw [hrep j hj0])
    have hprev (y : FiniteStateField (Fin d))
        (hy : ∀ l m, groupOf j l=groupOf j m → y l=y m) :
        ∀ l m, groupOf (j-1) l=groupOf (j-1) m → y l=y m := by
      intro l m he
      apply hy l m
      by_cases hz : j=0
      · simpa only [hz,Nat.zero_sub] using he
      · have hh := hrefine (j-1) (by omega) l m he
        simpa only [show j-1+1=j by omega] using hh
    have hb (y : FiniteStateField (Fin d)) (hy : ∀ l, y l=y (rep j (group j l))) :
        U y=(∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (k+1-j+1),h+y l))+(d : ℝ)*Real.log 2 := by
      have hy' (l m : Fin d) (he : groupOf j l=groupOf j m) : y l=y m := by
        rw [hy l,hy m,(hpart j hj0 l m).mp he]
      have he := replicaSourceSiteCascade_baseline ξ s h mark groupOf c hc hcomp hrefine j (by omega) y (hprev y hy')
      change U y=_ at he
      rw [hidx]
      linarith
    have hv : 0≤ξ.first (s.q (k+2-j))-ξ.first (s.q (k+1-j)) := by
      rw [←hidx]
      exact sub_nonneg.mpr (ξ.first_strictMonoOn.monotoneOn
        ⟨by linarith [s.q_nonneg (show k+1-j≤k+2 by omega)],s.q_le_one (by omega)⟩
        ⟨by linarith [s.q_nonneg (show k+1-j+1≤k+2 by omega)],s.q_le_one (by omega)⟩ (s.q_mono _ hp))
    have hmap : (finiteStateGaussianStepLaw (a j) (L j) U H).map (replicaSiteAbsoluteField h)=Q j (replicaSiteAbsoluteField h H) := by
      dsimp [a,L,Q]
      rw [←replicaSiteCopyGaussian_stepLaw_eq_of_partition _ hv (group j) (groupOf j)
        (fun l m => (hpart j hj0 l m).symm)]
      have he := mixed_replica_site_baseline_stepLaw ξ s (k+1-j) hp (group j) (rep j) (hrep j hj0)
        (c j) (hc j hj0) (hcard j hj0) h H hH' ((d : ℝ)*Real.log 2) U hUc hb
      simpa only [hidx] using he
    have hEm := sourceKernelExpectation_measurable (finiteStateGaussianCascadeKernel a L F) _ hsm j
    have hGm := sourceKernelExpectation_measurable Q _ hm j
    change (∫ y, sourceKernelExpectation (finiteStateGaussianCascadeKernel a L F) j _ y
      ∂finiteStateGaussianStepKernel (a j) (L j) U H)=_
    rw [finiteStateGaussianStepKernel_apply (a j) (L j) U hUc]
    calc
      _ = ∫ y, sourceKernelExpectation Q j (replicaTerminalCoefficient mark) (replicaSiteAbsoluteField h y)
          ∂finiteStateGaussianStepLaw (a j) (L j) U H :=
        integral_copyGaussianStepLaw_congr_on_partition (a j) _ (groupOf j) U H
          (fun l m he => hH l m (by simpa only [Nat.succ_sub_one] using he)) _ _ hEm
          (hGm.comp (measurable_replicaSiteAbsoluteField h))
          (fun y hy => ih (by omega) y (hprev y hy))
      _ = ∫ y, sourceKernelExpectation Q j (replicaTerminalCoefficient mark) y
          ∂(finiteStateGaussianStepLaw (a j) (L j) U H).map (replicaSiteAbsoluteField h) :=
        (integral_map (measurable_replicaSiteAbsoluteField h).aemeasurable hGm.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]; rfl

end OverlapPaper
