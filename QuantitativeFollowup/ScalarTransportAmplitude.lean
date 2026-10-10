module
public import QuantitativeFollowup.ScalarAmplitudeNodes
public import QuantitativeFollowup.ScalarTransportObservableFamily

@[expose] public section

/-! The actual increasing finite-level transport has a genuinely smooth
Gaussian-amplitude curve. Every repeated level has identically zero
amplitude, while every nonzero variance stays positive in the neighborhood. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal BigOperators
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportAmplitude (s : RSBScheme k) (β : ℝ) (φ : C(Paper.Overlap,ℝ))
    (u : ℝ) : QuantitativePaper.Field (k+2) :=
  WithLp.toLp 2 (fun i : Fin (k+2) => scalarSchemeTransportCoefficient s β φ u i)

@[simp] theorem scalarTransportAmplitude_apply (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (i : Fin (k+2)) :
    scalarTransportAmplitude s β φ u i=scalarSchemeTransportCoefficient s β φ u i := rfl

theorem contDiffAt_scalarTransportAmplitude (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) : ContDiffAt ℝ ∞ (scalarTransportAmplitude s β φ) u := by
  have hc (i : Fin (k+2)) : ContDiffAt ℝ ∞ (fun v => scalarSchemeTransportCoefficient s β φ v i) u := by
    by_cases he : s.q i=s.q (i+1)
    · have hn : scalarSchemeTransportNode s i=scalarSchemeTransportNode s (i+1) := by
        unfold scalarSchemeTransportNode;rw [he]
      simp only [scalarSchemeTransportCoefficient,he,hn,sub_self,mul_zero,add_zero,Real.sqrt_zero]
      exact contDiffAt_const
    · have hp := scalarSchemeTransport_variance_pos s β hβ φ L hφ h0 h1 u hu i (by have:=i.isLt;omega) he
      exact (show ContDiffAt ℝ ∞ (fun v : ℝ => β^2*(s.q (i+1)-s.q i+
        v*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i)))) u by fun_prop).sqrt hp.ne'
  have hpi : ContDiffAt ℝ ∞ (fun u : ℝ => fun i : Fin (k+2) => scalarSchemeTransportCoefficient s β φ u i) u :=
    contDiffAt_pi.mpr hc
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+2) => ℝ)).symm.contDiff.contDiffAt.comp u hpi

theorem scalarTransportAmplitude_square (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (i : Fin (k+2)) :
    (scalarTransportAmplitude s β φ u i)^2=β^2*
      ((scalarTransportScheme s φ L hφ h0 h1 u hu).q (i+1)-(scalarTransportScheme s φ L hφ h0 h1 u hu).q i) := by
  let r := scalarTransportScheme s φ L hφ h0 h1 u hu
  have hi : (i:ℕ)≤k+1 := by omega
  have he : scalarSchemeTransportCoefficient s β φ u i=Real.sqrt (β^2*(r.q (i+1)-r.q i)) := by
    rw [scalarSchemeTransportCoefficient]
    dsimp only [r]
    rw [scalarTransportScheme_overlap s φ L hφ h0 h1 u hu (i+1) (by omega),
      scalarTransportScheme_overlap s φ L hφ h0 h1 u hu i (by omega)]
    have hni : scalarSchemeTransportNode s i=⟨s.q i,s.q_nonneg (by omega),s.q_le_one (by omega)⟩ := by
      apply Subtype.ext;exact scalarSchemeTransportNode_coe s i (by omega)
    have hnj : scalarSchemeTransportNode s (i+1)=⟨s.q (i+1),s.q_nonneg (by omega),s.q_le_one (by omega)⟩ := by
      apply Subtype.ext;exact scalarSchemeTransportNode_coe s (i+1) (by omega)
    rw [hni,hnj]
    congr 1
    ring
  rw [scalarTransportAmplitude_apply,he]
  exact Real.sq_sqrt (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (r.q_mono i hi)))

theorem scalarAmplitudePrefixField_eq_history (c : ℕ → ℝ) (n : ℕ)
    (z : QuantitativePaper.Field n) (p : Fin (n+1)) :
    scalarAmplitudeField (WithLp.toLp 2 (fun i : Fin n => c i),scalarAmplitudePrefixMask n p z,0)=
      scalarCoefficientHistoryLinear c n z p := by
  rw [scalarAmplitudeField,zero_add,scalarCoefficientHistoryLinear_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [scalarAmplitudePrefixMask_apply]
  by_cases hi : (i:ℕ)<p
  · simp [hi,mul_comm]
  · simp [hi]

theorem scalarAmplitudeField_eq_history_last (c : ℕ → ℝ) (n : ℕ) (z : QuantitativePaper.Field n) :
    scalarAmplitudeField (WithLp.toLp 2 (fun i : Fin n => c i),z,0)=
      scalarCoefficientHistoryLinear c n z (Fin.last n) := by
  have he : scalarAmplitudePrefixMask n n z=z := by
    ext i
    rw [scalarAmplitudePrefixMask_apply,ite_eq_left i.isLt]
  simpa only [Fin.val_last,he] using scalarAmplitudePrefixField_eq_history c n z (Fin.last n)

theorem scalarTransportAmplitude_node_potential (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) (z : QuantitativePaper.Field (k+2)) :
    scalarAmplitudeNodePotential s p (scalarTransportAmplitude s β φ u,z,0)=
      scalarTransportNodePotential s β φ p u
        (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z p) := by
  rw [scalarAmplitudeNodePotential_eq_potential s (scalarTransportScheme s φ L hφ h0 h1 u hu)
    β hβ (fun _ => rfl) _ (scalarTransportAmplitude_square s β φ L hφ h0 h1 u hu)
    p (by omega),scalarTransportScheme_measure]
  rw [scalarTransportAmplitude,scalarAmplitudePrefixField_eq_history]
  rfl

theorem scalarTransportAmplitude_node_gradient (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) (z : QuantitativePaper.Field (k+2)) :
    scalarAmplitudeNodeGradient s p (scalarTransportAmplitude s β φ u,z,0)=
      scalarTransportNodeGradient s β φ p u
        (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z p) := by
  rw [scalarAmplitudeNodeGradient_eq_gradient s (scalarTransportScheme s φ L hφ h0 h1 u hu)
    β hβ (fun _ => rfl) _ (scalarTransportAmplitude_square s β φ L hφ h0 h1 u hu)
    p (by omega),scalarTransportScheme_measure]
  rw [scalarTransportAmplitude,scalarAmplitudePrefixField_eq_history]
  rfl

end QuantitativeFollowup
