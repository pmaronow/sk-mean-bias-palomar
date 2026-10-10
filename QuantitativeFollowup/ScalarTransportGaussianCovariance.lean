module
public import QuantitativeFollowup.ScalarGaussianHistoryCurve
public import QuantitativeFollowup.ScalarFiniteDensityScores

@[expose] public section

/-! The Gaussian input derivative of the actual transported scalar scheme
has exactly the covariance derivative d*phi(q_i wedge q_j). -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

 theorem scalarCoefficientHistoryLinear_congr (c d : ℕ→ℝ) (n : ℕ)
    (he : ∀l : Fin n,c l=d l) :
    scalarCoefficientHistoryLinear c n=scalarCoefficientHistoryLinear d n := by
  ext z i
  simp only [scalarCoefficientHistoryLinear_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [he l]

 theorem scalarTransportGaussianHistory_eq_actual (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) :
    scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)=
      scalarCoefficientHistoryLinear (fun l=>Real.sqrt (β^2*
        ((FRSB.forwardSchemeTime (scalarTransportScheme s φ L hφ h0 h1 u hu) 1 (l+1):ℝ)-
          FRSB.forwardSchemeTime (scalarTransportScheme s φ L hφ h0 h1 u hu) 1 l))) (k+2) := by
  apply scalarCoefficientHistoryLinear_congr
  intro l
  unfold scalarSchemeTransportCoefficient
  rw [scalarSchemeHistoryClock_coe _ (l+1) (by have:=l.isLt;omega),
    scalarSchemeHistoryClock_coe _ l (by have:=l.isLt;omega),
    scalarTransportScheme_overlap s φ L hφ h0 h1 u hu (l+1) (by have:=l.isLt;omega),
    scalarTransportScheme_overlap s φ L hφ h0 h1 u hu l (by have:=l.isLt;omega)]
  have hi : scalarSchemeTransportNode s l=⟨s.q l,s.q_nonneg (by have:=l.isLt;omega),
      s.q_le_one (by have:=l.isLt;omega)⟩ := by
    apply Subtype.ext
    exact scalarSchemeTransportNode_coe s l (by have:=l.isLt;omega)
  have hj : scalarSchemeTransportNode s (l+1)=⟨s.q (l+1),s.q_nonneg (by have:=l.isLt;omega),
      s.q_le_one (by have:=l.isLt;omega)⟩ := by
    apply Subtype.ext
    exact scalarSchemeTransportNode_coe s (l+1) (by have:=l.isLt;omega)
  rw [hi,hj]
  congr 2
  ring

 theorem scalarTransportGaussianHistory_covariance (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (i j : Fin (k+3)) :
    gaussianLinearCovariance
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)) i j=
      β^2*(s.q (min (i:ℕ) (j:ℕ))+u*φ (scalarSchemeTransportNode s (min (i:ℕ) (j:ℕ)))) := by
  let r := scalarTransportScheme s φ L hφ h0 h1 u hu
  rw [scalarTransportGaussianHistory_eq_actual s β φ L hφ h0 h1 u hu,
    scalarGaussianHistory_covariance_zero β (FRSB.forwardSchemeTime r 1)
      (FRSB.forwardSchemeTime_monotone r 1) (FRSB.forwardSchemeTime_zero r 1) (k+2) i j,
    scalarSchemeHistoryClock_coe r i (by have:=i.isLt;omega),
    scalarSchemeHistoryClock_coe r j (by have:=j.isLt;omega)]
  have hmin : min (r.q i) (r.q j)=r.q (min (i:ℕ) (j:ℕ)) := by
    by_cases hij : (i:ℕ)≤j
    · rw [min_eq_left hij,min_eq_left (r.q_mono' j (by have:=j.isLt;omega) i hij)]
    · have hji := le_of_not_ge hij
      rw [min_eq_right hji,min_eq_right (r.q_mono' i (by have:=i.isLt;omega) j hji)]
  rw [hmin]
  have hi : min (i:ℕ) (j:ℕ)≤k+2 := by have:=i.isLt;have:=j.isLt;omega
  rw [scalarTransportScheme_overlap s φ L hφ h0 h1 u hu _ hi]
  congr 3
  apply congrArg φ
  apply Subtype.ext
  exact (scalarSchemeTransportNode_coe s _ hi).symm

 theorem hasDerivAt_scalarTransportGaussianCovariance (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (i j : Fin (k+3)) :
    HasDerivAt (fun u=>gaussianLinearCovariance
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)) i j)
      (β^2*φ (scalarSchemeTransportNode s (min (i:ℕ) (j:ℕ)))) 0 := by
  have hS : {u : ℝ | |u| *(L:ℝ)<1}∈𝓝 (0:ℝ) := by
    apply (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds
    simp
  have he : (fun u=>gaussianLinearCovariance
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)) i j)=ᶠ[𝓝 (0:ℝ)]
      (fun u=>β^2*(s.q (min (i:ℕ) (j:ℕ))+u*φ (scalarSchemeTransportNode s (min (i:ℕ) (j:ℕ))))) :=
    Filter.Eventually.mono hS fun u hu => scalarTransportGaussianHistory_covariance s β φ L hφ h0 h1 u hu i j
  have hd := (((hasDerivAt_id (0:ℝ)).mul_const
    (φ (scalarSchemeTransportNode s (min (i:ℕ) (j:ℕ))))).const_add
      (s.q (min (i:ℕ) (j:ℕ)))).const_mul (β^2)
  simpa only [one_mul,id_eq] using hd.congr_of_eventuallyEq he

end QuantitativeFollowup
