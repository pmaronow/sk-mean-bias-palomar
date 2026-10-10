module
public import OverlapPaper.ReplicaSourceChronologicalLaw
public import FourPapersCommon.MixedFiniteKernelConcatenation

@[expose] public section

/-! Exact moment transport through fixed replica groups. The scalar endpoint
kernels are the genuine normalized Cole--Hopf transitions, including repeated
levels; every finite group coordinate remains in the product probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace OverlapPaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000

theorem sourceKernelExpectation_congr_kernels {A : Type*} [MeasurableSpace A]
    (Q R : ℕ → Kernel A A) (j : ℕ) (hQR : ∀ i<j, Q i=R i)
    (f : A → ℝ) (x : A) : sourceKernelExpectation Q j f x=
      sourceKernelExpectation R j f x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [sourceKernelExpectation]
    rw [hQR j (by omega)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => ih (fun i hi => hQR i (by omega)) y

theorem sourceKernelExpectation_split {A : Type*} [MeasurableSpace A]
    (Q : ℕ → Kernel A A) (j n : ℕ) (f : A → ℝ) (x : A) :
    sourceKernelExpectation Q (j+n) f x=
      sourceKernelExpectation (fun i => Q (j+i)) n (sourceKernelExpectation Q j f) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (∫ y, sourceKernelExpectation Q (j+n) f y ∂Q (j+n) x)=
      ∫ y, sourceKernelExpectation (fun i => Q (j+i)) n (sourceKernelExpectation Q j f) y ∂Q (j+n) x
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => ih y)

theorem integral_replicaGroupKernel_product {g d : ℕ}
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (group : Fin d → Fin g) (rep : Fin g → Fin d)
    (hrep : ∀ i, group (rep i)=i) (f : Fin g → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (x : Fin d → ℝ) :
    (∫ y, (∏ i : Fin g, f i (y (rep i))) ∂replicaGroupKernel κ group rep x)=
      ∏ i : Fin g, ∫ y, f i y ∂κ (x (rep i)) := by
  haveI (i : Fin g) : IsProbabilityMeasure (κ (x (rep i))) := inferInstance
  have hm : Measurable (fun y : Fin d → ℝ => ∏ i : Fin g, f i (y (rep i))) := by
    exact Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply _))
  rw [replicaGroupKernel_apply]
  rw [integral_map (measurable_replicaGroupCopy group).aemeasurable hm.aestronglyMeasurable]
  simp only [replicaGroupCopy,hrep]
  exact integral_fintype_prod_eq_prod f

theorem scalar_reverse_endpoint_mean {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p n : ℕ) (hn : p+n≤k+2)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C)
    (hb : ∀ x, |f x|≤C) (x : ℝ) :
    sourceKernelExpectation (fun i => mixedSchemeScalarStep ξ s (p+n-1-i)) n f x=
      ∫ y, f y ∂mixedSchemeEndpointKernel ξ s p n x := by
  induction n generalizing p x with
  | zero => simp only [sourceKernelExpectation,mixedSchemeEndpointKernel,Kernel.id_apply,integral_dirac]
  | succ n ih =>
    have hp : p≤k+1 := by omega
    haveI := isMarkovKernel_mixedSchemeScalarStep ξ s hp
    haveI := isMarkovKernel_mixedSchemeEndpointKernel ξ s (p+1) n (by omega)
    have hi : Integrable f ((mixedSchemeEndpointKernel ξ s (p+1) n ∘ₖ mixedSchemeScalarStep ξ s p) x) :=
      source_bounded_integrable _ f hf C hb
    have hK : mixedSchemeEndpointKernel ξ s p (n+1)=
        mixedSchemeEndpointKernel ξ s (p+1) n ∘ₖ mixedSchemeScalarStep ξ s p := by
      simpa only [Nat.add_comm 1 n,mixedSchemeEndpointKernel,Kernel.comp_id,Nat.add_zero]
        using mixedSchemeEndpointKernel_add ξ s p 1 n
    rw [hK]
    rw [Kernel.integral_comp hi]
    change (∫ y, sourceKernelExpectation (fun i => mixedSchemeScalarStep ξ s (p+(n+1)-1-i)) n f y
      ∂mixedSchemeScalarStep ξ s (p+(n+1)-1-n) x)=_
    rw [show p+(n+1)-1-n=p by omega]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      rw [sourceKernelExpectation_congr_kernels _
        (fun i => mixedSchemeScalarStep ξ s ((p+1)+n-1-i)) n
        (fun i hi => by congr 1; omega)]
      exact ih (p+1) (by omega) y

theorem replicaGroup_reverse_endpoint_product {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p n : ℕ) (hn : p+n≤k+2)
    (group : Fin d → Fin g) (rep : Fin g → Fin d) (hrep : ∀ i, group (rep i)=i)
    (f : Fin g → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (C : Fin g → ℝ) (hC : ∀ i, 0≤C i) (hb : ∀ i x, |f i x|≤C i)
    (x : Fin d → ℝ) :
    sourceKernelExpectation
      (fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s (p+n-1-i)) group rep) n
      (fun y => ∏ i : Fin g, f i (y (rep i))) x=
      ∏ i : Fin g, ∫ y, f i y ∂mixedSchemeEndpointKernel ξ s p n (x (rep i)) := by
  induction n generalizing p x with
  | zero => simp only [sourceKernelExpectation,mixedSchemeEndpointKernel,Kernel.id_apply,integral_dirac]
  | succ n ih =>
    have hp : p≤k+1 := by omega
    haveI := isMarkovKernel_mixedSchemeScalarStep ξ s hp
    haveI := isMarkovKernel_mixedSchemeEndpointKernel ξ s (p+1) n (by omega)
    let F := fun i y => ∫ z, f i z ∂mixedSchemeEndpointKernel ξ s (p+1) n y
    have hFm (i : Fin g) : Measurable (F i) := (hf i).stronglyMeasurable.integral_kernel.measurable
    change (∫ y, sourceKernelExpectation
      (fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s (p+(n+1)-1-i)) group rep) n _ y
      ∂replicaGroupKernel (mixedSchemeScalarStep ξ s (p+(n+1)-1-n)) group rep x)=_
    rw [show p+(n+1)-1-n=p by omega]
    have hinner (y : Fin d → ℝ) : sourceKernelExpectation
        (fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s (p+(n+1)-1-i)) group rep) n
        (fun y => ∏ i : Fin g, f i (y (rep i))) y=∏ i : Fin g, F i (y (rep i)) := by
      rw [sourceKernelExpectation_congr_kernels _
        (fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s ((p+1)+n-1-i)) group rep) n
        (fun i hi => by congr 2; omega)]
      exact ih (p+1) (by omega) y
    simp_rw [hinner]
    rw [integral_replicaGroupKernel_product _ group rep hrep F hFm]
    apply Finset.prod_congr rfl
    intro i hi
    have hint : Integrable (f i) ((mixedSchemeEndpointKernel ξ s (p+1) n ∘ₖ mixedSchemeScalarStep ξ s p) (x (rep i))) :=
      source_bounded_integrable _ _ (hf i) (C i) (hb i)
    rw [show n+1=1+n by omega,mixedSchemeEndpointKernel_add ξ s p 1 n]
    simp only [mixedSchemeEndpointKernel,Kernel.comp_id,Nat.add_zero]
    rw [Kernel.integral_comp hint]

def replicaCommonKernel {d : ℕ} (κ : Kernel ℝ ℝ) (i0 : Fin d) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  replicaGroupKernel κ (fun _ => (0 : Fin 1)) (fun _ => i0)

theorem integral_replicaCommonKernel {d : ℕ} (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] (i0 : Fin d) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (x : Fin d → ℝ) :
    (∫ y, f y ∂replicaCommonKernel κ i0 x)=∫ y, f (fun _ => y) ∂κ (x i0) := by
  haveI (i : Fin 1) : IsProbabilityMeasure (κ (x i0)) := inferInstance
  rw [replicaCommonKernel,replicaGroupKernel_apply,
    integral_map (measurable_replicaGroupCopy (fun _ => (0 : Fin 1))).aemeasurable hf.aestronglyMeasurable]
  have hm : Measurable (fun y : ℝ => f (fun _ : Fin d => y)) := hf.comp (by fun_prop)
  exact integral_comp_eval (μ := fun _ : Fin 1 => κ (x i0))
    (i := (0 : Fin 1)) hm.aestronglyMeasurable

theorem replicaCommon_reverse_endpoint_mean {k d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p n : ℕ) (hn : p+n≤k+2)
    (i0 : Fin d) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x|≤C) (x : ℝ) :
    sourceKernelExpectation
      (fun i => replicaCommonKernel (mixedSchemeScalarStep ξ s (p+n-1-i)) i0) n f (fun _ => x)=
      ∫ y, f (fun _ => y) ∂mixedSchemeEndpointKernel ξ s p n x := by
  induction n generalizing p x with
  | zero => simp only [sourceKernelExpectation,mixedSchemeEndpointKernel,Kernel.id_apply,integral_dirac]
  | succ n ih =>
    have hp : p≤k+1 := by omega
    haveI := isMarkovKernel_mixedSchemeScalarStep ξ s hp
    haveI := isMarkovKernel_mixedSchemeEndpointKernel ξ s (p+1) n (by omega)
    change (∫ y, sourceKernelExpectation
      (fun i => replicaCommonKernel (mixedSchemeScalarStep ξ s (p+(n+1)-1-i)) i0) n f y
      ∂replicaCommonKernel (mixedSchemeScalarStep ξ s (p+(n+1)-1-n)) i0 (fun _ => x))=_
    rw [show p+(n+1)-1-n=p by omega,integral_replicaCommonKernel _ i0 _
      (sourceKernelExpectation_measurable _ f hf n)]
    have hinner (y : ℝ) : sourceKernelExpectation
        (fun i => replicaCommonKernel (mixedSchemeScalarStep ξ s (p+(n+1)-1-i)) i0) n f (fun _ => y)=
        ∫ z, f (fun _ => z) ∂mixedSchemeEndpointKernel ξ s (p+1) n y := by
      rw [sourceKernelExpectation_congr_kernels _
        (fun i => replicaCommonKernel (mixedSchemeScalarStep ξ s ((p+1)+n-1-i)) i0) n
        (fun i hi => by congr 2; omega)]
      exact ih (p+1) (by omega) y
    simp_rw [hinner]
    have hK : mixedSchemeEndpointKernel ξ s p (n+1)=
        mixedSchemeEndpointKernel ξ s (p+1) n ∘ₖ mixedSchemeScalarStep ξ s p := by
      simpa only [Nat.add_comm 1 n,mixedSchemeEndpointKernel,Kernel.comp_id,Nat.add_zero]
        using mixedSchemeEndpointKernel_add ξ s p 1 n
    have hm : Measurable (fun y : ℝ => f (fun _ : Fin d => y)) := hf.comp (by fun_prop)
    rw [hK,Kernel.integral_comp (source_bounded_integrable _ _ hm C (fun y => hb _))]

theorem replicaIndependent_reverse_terminal_coefficient {k d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ) (hp : p≤k+2)
    (mark : Finset (Fin d)) (x : Fin d → ℝ) :
    sourceKernelExpectation
      (fun i => replicaGroupKernel (mixedSchemeScalarStep ξ s (k+1-i)) id id) (k+2-p)
      (replicaTerminalCoefficient mark) x=
      ∏ l ∈ mark, mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q p,x l) := by
  classical
  let f : Fin d → ℝ → ℝ := fun l y => if l∈mark then Real.tanh y else 1
  have hf (l : Fin d) : Measurable (f l) := by dsimp [f]; split_ifs <;> fun_prop
  have hb (l : Fin d) (y : ℝ) : |f l y|≤1 := by
    dsimp [f]; split_ifs
    · exact le_of_lt (Real.abs_tanh_lt_one y)
    · norm_num
  have he := replicaGroup_reverse_endpoint_product ξ s p (k+2-p) (by omega)
    id id (fun _ => rfl) f hf (fun _ => 1) (fun _ => zero_le_one) hb x
  have hi : (fun i => replicaGroupKernel (g := d) (d := d)
      (mixedSchemeScalarStep ξ s (p+(k+2-p)-1-i)) id id)=
      (fun i => replicaGroupKernel (g := d) (d := d) (mixedSchemeScalarStep ξ s (k+1-i)) id id) := by
    funext i; congr 2; omega
  rw [hi] at he
  have ht : (fun y : Fin d → ℝ => ∏ l, f l (y l))=replicaTerminalCoefficient mark := by
    funext y; simp only [f,replicaTerminalCoefficient,Finset.prod_ite_mem_eq]
  change sourceKernelExpectation _ _ (fun y => ∏ l, f l (y l)) x=_ at he
  rw [ht] at he
  simp only [id_eq] at he
  rw [he]
  haveI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p (k+2-p) (by omega)
  have hmean (l : Fin d) : (∫ y, f l y ∂mixedSchemeEndpointKernel ξ s p (k+2-p) (x l))=
      if l∈mark then mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q p,x l) else 1 := by
    dsimp [f]
    split_ifs
    · exact (mixedGradient_eq_terminalTanh_average ξ s hp _).symm
    · simp
  simp only [hmean,Finset.prod_ite_mem_eq]

end OverlapPaper
