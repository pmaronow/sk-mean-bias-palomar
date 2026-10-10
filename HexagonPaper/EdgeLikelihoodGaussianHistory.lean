module
public import HexagonPaper.EdgeLikelihoodFinite
public import QuantitativePaper.VectorBrownianHistory
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerProjection

@[expose] public section

/-! The finite edge reference measure is the observation of the actual
affine vector Wiener path with the physical diagonal covariance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {n k : ℕ}

private theorem finiteHistoryLaw_congr_prefix {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (κ η : ℕ → Kernel A A) (N : ℕ)
    (h : ∀i, i<N → κ i=η i) : finiteHistoryLaw ν κ N=finiteHistoryLaw ν η N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [finiteHistoryLaw,finiteHistoryLaw,ih (fun i hi=>h i (by omega)),h N (by omega)]

def edgeReferenceBrownianHistory (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (N : ℕ)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (AnisotropicParameter n) N :=
  fun i => anisotropicDisorderInjection n g+anisotropicUnitInput D x+
    anisotropicUnitInput D (disorderVectorBrownian (anisotropicRestartElapsed s q i) sample)

theorem measurable_edgeReferenceBrownianHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (N : ℕ) : Measurable (edgeReferenceBrownianHistory D s g q x N) := by
  apply Measurable.of_eval
  intro i
  exact measurable_const.add ((anisotropicUnitInput D).continuous.measurable.comp
    (measurable_disorderVectorBrownian _))

theorem edge_reference_brownian_history_law
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (N : ℕ) (hN : N≤k+2) :
    (vectorDisorderBrownianMeasure n).map (edgeReferenceBrownianHistory D s g q x N)=
      finiteHistoryLaw (Measure.dirac (anisotropicDisorderInjection n g+anisotropicUnitInput D x))
        (edgeRestartFiniteBaseKernel D s q) N := by
  let T : Fin (N+1) → ℝ≥0 := fun i => anisotropicRestartElapsed s q i
  have hT : Monotone T := by
    intro i j hij
    exact Real.toNNReal_le_toNNReal (sub_le_sub_right
      (max_le_max_left (q:ℝ) (s.q_mono' j (by omega) i (by exact_mod_cast hij))) _)
  have hT0 : T 0=0 := by
    simp only [T,anisotropicRestartElapsed,Fin.val_zero,s.q_zero,
      max_eq_left q.property.1,sub_self,Real.toNNReal_zero]
  let P₀ := anisotropicDisorderInjection n g+anisotropicUnitInput D x
  let Φ : VectorState n → AnisotropicParameter n := fun z => P₀+anisotropicUnitInput D z.2
  have hΦ : Measurable Φ := measurable_const.add
    ((anisotropicUnitInput D).continuous.measurable.comp measurable_snd)
  let η : ℕ → Kernel (AnisotropicParameter n) (AnisotropicParameter n) := fun i =>
    if i<N then edgeRestartFiniteBaseKernel D s q i else Kernel.id
  have hη : ∀i,IsMarkovKernel (η i) := by
    intro i
    dsimp only [η]
    split_ifs
    · change IsMarkovKernel
        (anisotropicFiniteBaseTransition D (vectorClampedScheme s q q.property) (i+1))
      infer_instance
    · infer_instance
  have hsection : ∀i z,(brownianGridKernel T 1 i z).map Φ=η i (Φ z) := by
    intro i z
    by_cases hi : i<N
    · have he : brownianGridVariance T 1 ⟨i,hi⟩=
          max (q:ℝ) (s.q (i+1))-max (q:ℝ) (s.q i) := by
        simp only [brownianGridVariance,one_pow,one_mul,T,
          anisotropicRestartElapsed,Fin.val_succ,Fin.val_castSucc,
          Real.coe_toNNReal _ (sub_nonneg.mpr (le_max_left _ _))]
        ring
      have hinput : anisotropicSchemeInput D (vectorClampedScheme s q q.property)
          (k+1-i)=Real.sqrt (brownianGridVariance T 1 ⟨i,hi⟩) • anisotropicUnitInput D := by
        unfold anisotropicSchemeInput
        rw [show k+1+2-(k+1-i)=i+2 by omega,
          show k+1+1-(k+1-i)=i+1 by omega,
          vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ,he]
        rfl
      rw [brownianGridKernel,dif_pos hi,vectorGaussianStateKernel_apply]
      rw [Measure.map_map hΦ (show Measurable
        (fun v : Field n => (z.1,fieldShift (brownianGridVariance T 1 ⟨i,hi⟩) z.2 v)) by
        unfold fieldShift
        fun_prop)]
      dsimp only [η]
      rw [if_pos hi]
      change (fieldGaussian n).map (Φ ∘ fun v=>vectorStateUpdate
        (brownianGridVariance T 1 ⟨i,hi⟩) (z,v))=
        (anisotropicFiniteBaseTransition D (vectorClampedScheme s q q.property) (i+1)) (Φ z)
      rw [anisotropicFiniteBaseTransition,finiteStateGaussianRawKernel_apply,
        fieldGaussian_eq_stdGaussian]
      congr 1
      funext v
      rw [show k+1+1-(i+1)=k+1-i by omega,hinput]
      simp only [Function.comp_def,Φ,vectorStateUpdate,fieldShift,map_add,map_smul,
        ContinuousLinearMap.smul_apply]
      abel
    · rw [brownianGridKernel,dif_neg hi]
      dsimp only [η]
      rw [if_neg hi,Kernel.id_apply,Kernel.id_apply]
      simp only [Measure.map_dirac]
  have hproj := finiteHistoryLaw_map_states (vectorBaseInitialLaw n)
    (brownianGridKernel T 1) η (fun _=>inferInstance) hη Φ hΦ hsection N
  have hinit : (vectorBaseInitialLaw n).map Φ=Measure.dirac P₀ := by
    unfold vectorBaseInitialLaw
    rw [Measure.map_map hΦ (by fun_prop)]
    change (completionLaw n).map (fun _=>P₀+anisotropicUnitInput D 0)=_
    simp
  rw [hinit] at hproj
  have hmap : Measurable (fun p : FiniteHistory (VectorState n) N => fun i=>Φ (p i)) :=
    Measurable.of_eval (fun i=>hΦ.comp (measurable_pi_apply i))
  have hlaw := scaledDisorderBrownianHistory_map (n:=n) T hT hT0 1
  rw [←hlaw,Measure.map_map hmap (measurable_scaledDisorderBrownianHistory T 1)] at hproj
  have hf : (fun p : FiniteHistory (VectorState n) N=>fun i=>Φ (p i)) ∘
      scaledDisorderBrownianHistory T 1=edgeReferenceBrownianHistory D s g q x N := by
    funext sample i
    simp only [Function.comp_def,scaledDisorderBrownianHistory,one_smul,Φ,
      edgeReferenceBrownianHistory,P₀,T]
  rw [hf] at hproj
  exact hproj.trans (finiteHistoryLaw_congr_prefix _ η (edgeRestartFiniteBaseKernel D s q)
    N (fun i hi=>by dsimp only [η];rw [if_pos hi]))

theorem edge_restart_finite_brownian_likelihood
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (N : ℕ) (hN : N≤k+2) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFiniteRestartPhysicalHistory D s g q x N)=
      ((vectorDisorderBrownianMeasure n).map
        (edgeReferenceBrownianHistory D s g q x N)).withDensity
          (finiteHistoryDensity (edgeRestartFiniteWeight D s q) N) := by
  rw [edge_reference_brownian_history_law D s g q x N hN]
  exact edge_restart_finite_history_law_eq_withDensity D s g q x N hN

end HexagonPaper
