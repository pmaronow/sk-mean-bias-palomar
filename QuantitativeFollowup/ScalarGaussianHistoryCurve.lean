module
public import QuantitativeFollowup.ScalarGaussianClockCovariance
public import QuantitativeFollowup.ScalarTransportScheme

@[expose] public section

/-! Actual derivatives of the cumulative Gaussian input along increasing
finite-level transports. Repeated levels have identically zero increments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 def scalarHistoryIncrementMask (n : ℕ) (l : Fin n) :
    QuantitativePaper.Field n→L[ℝ] QuantitativePaper.Field (n+1) :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n=>ℝ) l).smulRight
    (WithLp.toLp 2 (fun i : Fin (n+1) => if (l:ℕ) < (i:ℕ) then (1:ℝ) else 0))

 theorem scalarHistoryIncrementMask_apply (n : ℕ) (l : Fin n)
    (z : QuantitativePaper.Field n) (i : Fin (n+1)) :
    scalarHistoryIncrementMask n l z i=if (l:ℕ) < (i:ℕ) then z l else 0 := by
  simp [scalarHistoryIncrementMask,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

 theorem scalarCoefficientHistoryLinear_eq_masks (c : ℕ→ℝ) (n : ℕ) :
    scalarCoefficientHistoryLinear c n=∑l : Fin n,c l • scalarHistoryIncrementMask n l := by
  ext z i
  rw [scalarCoefficientHistoryLinear_apply]
  simp only [sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,
    Pi.smul_apply,smul_eq_mul,scalarHistoryIncrementMask_apply]
  exact Finset.sum_congr rfl (fun l _ => by split_ifs <;> simp)

 theorem hasDerivAt_scalarCoefficientHistoryLinear (c dc : ℝ→ℕ→ℝ) (n : ℕ) (u : ℝ)
    (hc : ∀l : Fin n,HasDerivAt (fun v=>c v l) (dc u l) u) :
    HasDerivAt (fun v=>scalarCoefficientHistoryLinear (c v) n)
      (scalarCoefficientHistoryLinear (dc u) n) u := by
  simp_rw [scalarCoefficientHistoryLinear_eq_masks]
  apply HasDerivAt.fun_sum
  intro l _
  convert! (hc l).smul_const (scalarHistoryIncrementMask n l) using 1

variable {k : ℕ}

 def scalarSchemeTransportNode (s : RSBScheme k) (i : ℕ) : Paper.Overlap :=
  projIcc 0 1 zero_le_one (s.q i)

 theorem scalarSchemeTransportNode_coe (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) :
    (scalarSchemeTransportNode s i:ℝ)=s.q i := by
  change (projIcc 0 1 zero_le_one (s.q i):ℝ)=s.q i
  rw [projIcc_of_mem zero_le_one ⟨s.q_nonneg hi,s.q_le_one hi⟩]


 def scalarSchemeTransportCoefficient (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (i : ℕ) : ℝ :=
  Real.sqrt (β^2*(s.q (i+1)-s.q i+
    u*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))))

 def scalarSchemeTransportCoefficientDerivative (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (i : ℕ) : ℝ :=
  if s.q i=s.q (i+1) then 0 else
    β^2*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))/
      (2*scalarSchemeTransportCoefficient s β φ u i)

 theorem scalarSchemeTransport_variance_pos (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (i : ℕ) (hi : i≤k+1) (hne : s.q i≠s.q (i+1)) :
    0<β^2*(s.q (i+1)-s.q i+
      u*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))) := by
  have hq : s.q i<s.q (i+1) := lt_of_le_of_ne (s.q_mono i hi) hne
  have hnodes : scalarSchemeTransportNode s i<scalarSchemeTransportNode s (i+1) := by
    change (scalarSchemeTransportNode s i:ℝ)<(scalarSchemeTransportNode s (i+1):ℝ)
    rw [scalarSchemeTransportNode_coe s i (by omega),scalarSchemeTransportNode_coe s (i+1) (by omega)]
    exact hq
  have ht := strictMono_scalarLevelTransport φ L hφ h0 h1 u hu hnodes
  change (scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ)<
    (scalarLevelTransport φ u (scalarSchemeTransportNode s (i+1)):ℝ) at ht
  rw [scalarLevelTransport_eq_affine φ L hφ h0 h1 u hu.le,
    scalarLevelTransport_eq_affine φ L hφ h0 h1 u hu.le] at ht
  rw [scalarSchemeTransportNode_coe s i (by omega),scalarSchemeTransportNode_coe s (i+1) (by omega)] at ht
  apply mul_pos (sq_pos_of_ne_zero hβ)
  linarith

 theorem hasDerivAt_scalarSchemeTransportCoefficient (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (i : ℕ) (hi : i≤k+1) :
    HasDerivAt (fun v=>scalarSchemeTransportCoefficient s β φ v i)
      (scalarSchemeTransportCoefficientDerivative s β φ u i) u := by
  by_cases he : s.q i=s.q (i+1)
  · have hn : scalarSchemeTransportNode s i=scalarSchemeTransportNode s (i+1) := by unfold scalarSchemeTransportNode;rw [he]
    simp only [scalarSchemeTransportCoefficient,he,hn,sub_self,mul_zero,add_zero,Real.sqrt_zero,
      scalarSchemeTransportCoefficientDerivative,ite_eq_left he]
    exact hasDerivAt_const u 0
  · have hp := scalarSchemeTransport_variance_pos s β hβ φ L hφ h0 h1 u hu i hi he
    have hd : HasDerivAt (fun v : ℝ=>β^2*(s.q (i+1)-s.q i+
        v*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))))
        (β^2*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))) u := by
      simpa only [zero_add,one_mul,id_eq] using
        (((hasDerivAt_id u).mul_const
          (φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))).const_add (s.q (i+1)-s.q i)).const_mul (β^2)
    simpa only [scalarSchemeTransportCoefficient,scalarSchemeTransportCoefficientDerivative,
      ite_eq_right he] using hd.sqrt hp.ne'

 theorem hasDerivAt_scalarTransportGaussianHistory (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) :
    HasDerivAt (fun v=>scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ v) (k+2))
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ u) (k+2)) u :=
  hasDerivAt_scalarCoefficientHistoryLinear _ _ _ _ fun i =>
    hasDerivAt_scalarSchemeTransportCoefficient s β hβ φ L hφ h0 h1 u hu i (by have:=i.isLt;omega)

end QuantitativeFollowup
