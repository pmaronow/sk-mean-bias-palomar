module
public import FourPapersCommon.ThreefoldSchemeRefinement
public import FourPapersCommon.MixtureCoordinateVariance

@[expose] public section

/-! The actual clocked overlap scheme realizing a positive interaction
amplitude by two cancelling base steps and one active increasing step.
Every inserted node has the original mass, so its overlap law is unchanged. -/
noncomputable section
open Set MeasureTheory Real
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.Targets
set_option maxHeartbeats 1200000

def coordinateScheduleBase {k : ℕ} (ξ : AdmissibleEvenMixture) (p : ℕ)
    (s : RSBScheme k) (i : ℕ) : ℝ :=
  ξ.coordinateBaseIncrement p (s.q i) (s.q (i+1))

def coordinateScheduleActive {k : ℕ} (p : ℕ) (M : ℝ) (s : RSBScheme k) (i : ℕ) : ℝ :=
  M^2*(p : ℝ)*(s.q (i+1)^(p-1)-s.q i^(p-1))

theorem coordinateScheduleBase_nonneg {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) :
    0≤coordinateScheduleBase ξ p s i :=
  ξ.coordinateBaseIncrement_nonneg p ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
    ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ (s.q_mono i hi)

theorem coordinateScheduleActive_nonneg {k : ℕ} (p : ℕ) (M : ℝ)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) :
    0≤coordinateScheduleActive p M s i := by
  unfold coordinateScheduleActive
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (sub_nonneg.mpr (pow_le_pow_left₀ (s.q_nonneg (by omega)) (s.q_mono i hi) _))

def coordinateScheduleFirstNode {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (s : RSBScheme k) (i : ℕ) : ℝ :=
  (ξ.amplitudeCoordinate p hp c).clock (s.q i)+
    t*coordinateScheduleActive p M s i/(ξ.amplitudeCoordinate p hp c).variance

def coordinateScheduleSecondNode {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (s : RSBScheme k) (i : ℕ) : ℝ :=
  coordinateScheduleFirstNode ξ p hp c M t s i+
    t*coordinateScheduleBase ξ p s i/(ξ.amplitudeCoordinate p hp c).variance

theorem coordinateScheduleNodes_ordered {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) :
    ∀i≤k+1,(mixedClockScheme (ξ.amplitudeCoordinate p hp c) s).q i≤
      coordinateScheduleFirstNode ξ p hp c M t s i ∧
      coordinateScheduleFirstNode ξ p hp c M t s i≤coordinateScheduleSecondNode ξ p hp c M t s i ∧
      coordinateScheduleSecondNode ξ p hp c M t s i≤
        (mixedClockScheme (ξ.amplitudeCoordinate p hp c) s).q (i+1) := by
  intro i hi
  have hbase:=coordinateScheduleBase_nonneg ξ p s i hi
  have hactive:=coordinateScheduleActive_nonneg p M s i hi
  have hv:=(ξ.amplitudeCoordinate p hp c).variance_pos
  have he:=ξ.amplitudeCoordinate_increment_scaled p hp c M t hc (a:=s.q i) (b:=s.q (i+1))
    ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
    ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
  change (ξ.amplitudeCoordinate p hp c).first (s.q (i+1))-
    (ξ.amplitudeCoordinate p hp c).first (s.q i)=
      coordinateScheduleBase ξ p s i+t*coordinateScheduleActive p M s i at he
  dsimp only [mixedClockScheme_q,coordinateScheduleFirstNode,coordinateScheduleSecondNode]
  refine ⟨le_add_of_nonneg_right (div_nonneg (mul_nonneg ht.1 hactive) hv.le),
    le_add_of_nonneg_right (div_nonneg (mul_nonneg ht.1 hbase) hv.le),?_⟩
  unfold AdmissibleEvenMixture.clock
  apply (le_div_iff₀ hv).2
  have heq : ((ξ.amplitudeCoordinate p hp c).first (s.q i)/
      (ξ.amplitudeCoordinate p hp c).variance+
        t*coordinateScheduleActive p M s i/(ξ.amplitudeCoordinate p hp c).variance+
        t*coordinateScheduleBase ξ p s i/(ξ.amplitudeCoordinate p hp c).variance)*
      (ξ.amplitudeCoordinate p hp c).variance =
    (ξ.amplitudeCoordinate p hp c).first (s.q i)+t*coordinateScheduleActive p M s i+
      t*coordinateScheduleBase ξ p s i := by field_simp [hv.ne']
  rw [heq]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hbase]

def coefficientScheduleClockScheme {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) : RSBScheme (3*k+4) :=
  threefoldScheme (mixedClockScheme (ξ.amplitudeCoordinate p hp c) s)
    (coordinateScheduleFirstNode ξ p hp c M t s)
    (coordinateScheduleSecondNode ξ p hp c M t s)
    (coordinateScheduleNodes_ordered ξ p hp c M t ht hc s)

theorem parisiSchemeMeasure_coefficientSchedule {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) :
    Paper.parisiSchemeMeasure (coefficientScheduleClockScheme ξ p hp c M t ht hc s)=
      mixedMeasure (ξ.amplitudeCoordinate p hp c) (Paper.parisiSchemeMeasure s) := by
  rw [coefficientScheduleClockScheme,parisiSchemeMeasure_threefold,mixedMeasure_scheme]

theorem coefficientSchedule_original_node {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) (i : ℕ) :
    (coefficientScheduleClockScheme ξ p hp c M t ht hc s).q (3*i)=
      (ξ.amplitudeCoordinate p hp c).clock (s.q i) := by
  simp only [coefficientScheduleClockScheme,threefoldScheme_q_original,mixedClockScheme_q]

/-- The three variances are, in chronological order, active-up, base-up,
base-down. Backwards recursion therefore uses base-down, base-up, active-up. -/
theorem coefficientSchedule_three_variances {k : ℕ} (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2≤p∧Even p) (c : {c : ℝ//0<c}) (M t : ℝ)
    (ht : t∈Icc 0 1) (hc : (c : ℝ)^2=t*M^2) (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) :
    let r:=coefficientScheduleClockScheme ξ p hp c M t ht hc s
    (ξ.amplitudeCoordinate p hp c).variance*(r.q (3*i+1)-r.q (3*i))=
        t*coordinateScheduleActive p M s i ∧
    (ξ.amplitudeCoordinate p hp c).variance*(r.q (3*i+2)-r.q (3*i+1))=
        t*coordinateScheduleBase ξ p s i ∧
    (ξ.amplitudeCoordinate p hp c).variance*(r.q (3*(i+1))-r.q (3*i+2))=
        (1-t)*coordinateScheduleBase ξ p s i := by
  dsimp only
  simp only [coefficientScheduleClockScheme,threefoldScheme_q_original,
    threefoldScheme_q_first,threefoldScheme_q_second,mixedClockScheme_q,
    coordinateScheduleFirstNode,coordinateScheduleSecondNode]
  have hv:=(ξ.amplitudeCoordinate p hp c).variance_pos
  have he:=ξ.amplitudeCoordinate_increment_scaled p hp c M t hc (a:=s.q i) (b:=s.q (i+1))
    ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
    ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
  change (ξ.amplitudeCoordinate p hp c).first (s.q (i+1))-
    (ξ.amplitudeCoordinate p hp c).first (s.q i)=
      coordinateScheduleBase ξ p s i+t*coordinateScheduleActive p M s i at he
  unfold AdmissibleEvenMixture.clock
  constructor
  · field_simp [hv.ne']
    ring
  constructor
  · field_simp [hv.ne']
    ring
  · field_simp [hv.ne']
    nlinarith [he]

end FourPapersCommon
