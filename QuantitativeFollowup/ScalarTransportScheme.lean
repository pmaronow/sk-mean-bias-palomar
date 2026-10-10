module
public import QuantitativeFollowup.ScalarTransportContinuity
public import Paper.ParisiSchemeMeasure

@[expose] public section

/-! Actual finite RSB schemes transported by a small increasing level map.
The finite atomic law is proved to be the literal pushforward, retaining
zero-weight atoms and repeated overlap levels. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportScheme (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ) (hθ : |θ| *L<1) :
    RSBScheme k where
  m := s.m
  q i := (scalarLevelTransport φ θ (projIcc 0 1 zero_le_one (s.q i)) : ℝ)
  m_zero := s.m_zero
  m_top := s.m_top
  m_mono := s.m_mono
  q_zero := by
    rw [s.q_zero]
    rw [projIcc_of_mem zero_le_one (by constructor <;> norm_num : (0 : ℝ)∈Icc 0 1)]
    change (scalarLevelTransport φ θ (0 : Paper.Overlap) : ℝ)=0
    rw [scalarLevelTransport_root φ h0 θ]
    rfl
  q_top := by
    rw [s.q_top]
    rw [projIcc_of_mem zero_le_one (by constructor <;> norm_num : (1 : ℝ)∈Icc 0 1)]
    change (scalarLevelTransport φ θ (1 : Paper.Overlap) : ℝ)=1
    rw [scalarLevelTransport_eq_affine φ L hφ h0 h1 θ hθ.le,h1,mul_zero,add_zero]
    rfl
  q_mono i hi := (strictMono_scalarLevelTransport φ L hφ h0 h1 θ hθ).monotone
    ((monotone_projIcc zero_le_one) (s.q_mono i hi))

@[simp] theorem scalarTransportScheme_mass (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ) (hθ : |θ| *L<1) (i : ℕ) :
    (scalarTransportScheme s φ L hφ h0 h1 θ hθ).m i=s.m i := rfl

theorem scalarTransportScheme_overlap (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ) (hθ : |θ| *L<1)
    (i : ℕ) (hi : i≤k+2) :
    (scalarTransportScheme s φ L hφ h0 h1 θ hθ).q i=s.q i+
      θ*φ ⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ := by
  change (scalarLevelTransport φ θ (projIcc 0 1 zero_le_one (s.q i)) : ℝ)=_
  rw [projIcc_of_mem zero_le_one ⟨s.q_nonneg hi,s.q_le_one hi⟩,
    scalarLevelTransport_eq_affine φ L hφ h0 h1 θ hθ.le]

theorem scalarTransportScheme_atom (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ) (hθ : |θ| *L<1)
    (i : Fin (k+1)) :
    Paper.parisiSchemeAtom (scalarTransportScheme s φ L hφ h0 h1 θ hθ) i=
      scalarLevelTransport φ θ (Paper.parisiSchemeAtom s i) := by
  apply Subtype.ext
  change (scalarLevelTransport φ θ (projIcc 0 1 zero_le_one (s.q (i+1))) : ℝ)=_
  rw [projIcc_of_mem zero_le_one ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩]
  rfl

theorem scalarTransportScheme_measure (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ) (hθ : |θ| *L<1) :
    Paper.parisiSchemeMeasure (scalarTransportScheme s φ L hφ h0 h1 θ hθ)=
      scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ θ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Paper.parisiSchemeRawMeasure (scalarTransportScheme s φ L hφ h0 h1 θ hθ)=
    (Paper.parisiSchemeRawMeasure s).map (scalarLevelTransport φ θ)
  rw [←Measure.mapₗ_apply_of_measurable (continuous_scalarLevelTransport_parameter φ θ).measurable]
  simp only [Paper.parisiSchemeRawMeasure,map_sum,map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.mapₗ_apply_of_measurable (continuous_scalarLevelTransport_parameter φ θ).measurable]
  simp only [Measure.map_dirac,scalarTransportScheme_mass,scalarTransportScheme_atom,RingHom.id_apply]

end QuantitativeFollowup
