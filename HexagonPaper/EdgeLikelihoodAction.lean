module
public import HexagonPaper.EdgeLikelihoodFiniteStieltjes
public import HexagonPaper.EdgeLikelihoodGaussianHistory
public import QuantitativeFollowup.AnisotropicFiniteMeasureAgreement
public import QuantitativeFollowup.AnisotropicVarianceClampedMeasure
public import QuantitativeFollowup.AnisotropicFiniteNodeResponse

@[expose] public section

/-! The finite reference edge density is the literal native potential action,
independently of the finite representation of the profile. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {n k : ℕ}

private theorem tailRecursion_raise_below_node
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : ℝ)
    (J : ℕ) (hJ : J≤k+2) (j : ℕ) (hj : j≤J) :
    anisotropicTailRecursion D s q j=
      anisotropicTailRecursion D s (max q (s.q (k+2-J))) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hl : s.q (k+2-J) ≤ s.q (k+1-j) :=
      s.q_mono' (k+1-j) (by omega) (k+2-J) (by omega)
    have hu : s.q (k+2-J) ≤ s.q (k+2-j) :=
      s.q_mono' (k+2-j) (by omega) (k+2-J) (by omega)
    rw [anisotropicTailRecursion,anisotropicTailRecursion,ih (by omega),
      max_assoc,max_eq_right hu,max_assoc,max_eq_right hl]

theorem edge_native_potential_at_clamped_node
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (q : Paper.Overlap)
    (i : ℕ) (hi : i≤k+2) (P : AnisotropicParameter n) :
    anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s)
        (anisotropicClampOverlap q (anisotropicSchemeNode s i hi)) P=
      anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-i) P := by
  rw [anisotropicMeasureTailPotential_scheme_eq_finite]
  change anisotropicTailRecursion D s (max (q:ℝ) (s.q i)) (k+2) P=_
  have hi' : k+2-(k+2-i)=i := by omega
  rw [anisotropicTailRecursion_constant_suffix D s (max (q:ℝ) (s.q i))
    (k+2-i) (by omega) (by rw [hi'];exact le_max_right _ _) (by omega) le_rfl]
  have he:=tailRecursion_raise_below_node D s (q:ℝ) (k+2-i) (by omega)
    (k+2-i) le_rfl
  rw [hi'] at he
  rw [←he,anisotropicTailRecursion_eq_clamped D s q q.property (by omega)]

def edgeReferenceParameter (D : AnisotropicSpinModel n) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n)
    (r : Paper.Overlap) : AnisotropicParameter n :=
  anisotropicDisorderInjection n g+anisotropicUnitInput D x+
    anisotropicUnitInput D (disorderVectorBrownian ((r:ℝ)-(q:ℝ)).toNNReal sample)

def edgeSuffixAction (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (Z : Paper.Overlap → AnisotropicParameter n) : ℝ :=
  ∫r,anisotropicMeasureTailPotential D μ (anisotropicClampOverlap q r)
      (Z (anisotropicClampOverlap q r)) ∂(μ:Measure Paper.Overlap)

def edgeSuffixLikelihood (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (Z : Paper.Overlap → AnisotropicParameter n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (
    anisotropicMeasureTailPotential D μ ⟨1,by norm_num⟩ (Z ⟨1,by norm_num⟩)-
      edgeSuffixAction D μ q Z))

theorem edge_restart_finite_reference_density_action
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    finiteHistoryDensity (edgeRestartFiniteWeight D s q) (k+2)
        (edgeReferenceBrownianHistory D s g q x (k+2) sample)=
      edgeSuffixLikelihood D (Paper.parisiSchemeMeasure s) q
        (edgeReferenceParameter D g q x sample) := by
  let p:=edgeReferenceBrownianHistory D s g q x (k+2) sample
  let Z:=edgeReferenceParameter D g q x sample
  have hpot (i : ℕ) (hi : i≤k+2) :
      edgeRestartHistoryPotential D s q p i=
        anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s)
          (anisotropicClampOverlap q (anisotropicSchemeNode s i hi))
          (Z (anisotropicClampOverlap q (anisotropicSchemeNode s i hi))) := by
    rw [edge_native_potential_at_clamped_node D s q i hi]
    unfold edgeRestartHistoryPotential
    congr 1
    have hp : historyExtended p i=p ⟨i,by omega⟩ := by
      simpa only [Fin.val_mk] using historyExtended_fin p ⟨i,by omega⟩
    rw [hp]
    rfl
  rw [edge_restart_finite_history_density_stieltjes D s q (k+1) (by omega)]
  change ENNReal.ofReal (Real.exp (
    (vectorClampedScheme s q q.property).m (k+2)*edgeRestartHistoryPotential D s q p (k+2)-
    (vectorClampedScheme s q q.property).m 1*edgeRestartHistoryPotential D s q p 0-
    ∑i ∈ Finset.range (k+1),
      ((vectorClampedScheme s q q.property).m (i+2)-
        (vectorClampedScheme s q q.property).m (i+1))*edgeRestartHistoryPotential D s q p (i+1)))=_
  have hmTop : (vectorClampedScheme s q q.property).m (k+2)=1 := by
    simpa only [Nat.add_assoc,s.m_top] using vectorClampedScheme_mass_succ s q q.property (k+1)
  have hmOne : (vectorClampedScheme s q q.property).m 1=0 := by
    simpa only [Nat.zero_add,s.m_zero] using vectorClampedScheme_mass_succ s q q.property 0
  rw [hmTop,hmOne,one_mul,zero_mul,sub_zero]
  have htop : anisotropicClampOverlap q (anisotropicSchemeNode s (k+2) le_rfl)=
      (⟨1,by norm_num⟩:Paper.Overlap) := by
    apply Subtype.ext
    simp only [anisotropicClampOverlap_coe,anisotropicSchemeNode,s.q_top,
      max_eq_right q.property.2]
  rw [hpot (k+2) le_rfl,htop]
  unfold edgeSuffixLikelihood edgeSuffixAction
  congr 2
  congr 1
  rw [FRSB.integral_parisiSchemeMeasure,
    ←Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      ((vectorClampedScheme s q q.property).m (i+2)-
        (vectorClampedScheme s q q.property).m (i+1))*
          edgeRestartHistoryPotential D s q p (i+1)) (k+1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : (i:ℕ)<k+1:=i.isLt
  rw [show (i:ℕ)+2=((i:ℕ)+1)+1 by omega,vectorClampedScheme_mass_succ,
    vectorClampedScheme_mass_succ,hpot (i+1) (by omega)]
  congr 2

end HexagonPaper
