module
public import QuantitativeFollowup.ParisiFreeMeasure
public import FourPapersCommon.ProbabilityIntegralContinuity
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Genuine transport of scalar overlap laws. Clamping defines the family for
all real parameters; near zero it is the literal affine level transport,
strictly increasing and preserving the prescribed root atom. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

 def scalarLevelTransport (φ : C(Paper.Overlap,ℝ)) (θ : ℝ) (q : Paper.Overlap) : Paper.Overlap :=
  projIcc 0 1 zero_le_one ((q : ℝ)+θ*φ q)

 theorem continuous_scalarLevelTransport (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : ℝ×Paper.Overlap => scalarLevelTransport φ z.1 z.2) :=
  by
  convert! (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
    ((continuous_subtype_val.comp continuous_snd).add (continuous_fst.mul (φ.continuous.comp continuous_snd))) using 1

 def scalarTransportMeasure (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (θ : ℝ) : Paper.ParisiMeasure :=
  μ.map (scalarLevelTransport φ θ)

 theorem scalarLevelTransport_zero (φ : C(Paper.Overlap,ℝ)) (q : Paper.Overlap) : scalarLevelTransport φ 0 q=q := by
  apply Subtype.ext
  simp only [scalarLevelTransport,zero_mul,add_zero,projIcc_of_mem zero_le_one q.property]

 theorem scalarTransportMeasure_zero (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) :
    scalarTransportMeasure μ φ 0=μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [scalarTransportMeasure,ProbabilityMeasure.toMeasure_map]
  rw [show scalarLevelTransport φ 0=id from funext (scalarLevelTransport_zero φ),Measure.map_id]

 theorem scalarLevelTransport_eq_affine (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ)
    (hθ : |θ| *L ≤ 1) (q : Paper.Overlap) :
    (scalarLevelTransport φ θ q : ℝ)=(q : ℝ)+θ*φ q := by
  have ha := hφ.dist_le_mul q 0
  have hb := hφ.dist_le_mul q 1
  change |φ q-φ 0| ≤ (L : ℝ)*|(q : ℝ)-0| at ha
  change |φ q-φ 1| ≤ (L : ℝ)*|(q : ℝ)-1| at hb
  have hq0 : 0 ≤ (q : ℝ) := q.property.1
  have hq1 : (q : ℝ) ≤ 1 := q.property.2
  have hp0 : |φ q| ≤ L*(q : ℝ) := by
    simpa only [h0,Real.dist_eq,sub_zero,dist_eq_norm,Real.norm_eq_abs,abs_of_nonneg hq0] using ha
  have hp1 : |φ q| ≤ L*(1-(q : ℝ)) := by
    simpa only [h1,Real.dist_eq,sub_zero,dist_eq_norm,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hq1),neg_sub] using hb
  have hmul0 : |θ*φ q| ≤ (q : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ |θ| *(L*(q : ℝ)) := mul_le_mul_of_nonneg_left hp0 (abs_nonneg _)
      _ ≤ (q : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hθ hq0]
  have hmul1 : |θ*φ q| ≤ 1-(q : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ |θ| *(L*(1-(q : ℝ))) := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
      _ ≤ 1-(q : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hθ (sub_nonneg.mpr hq1)]
  have he : (q : ℝ)+θ*φ q∈Icc (0 : ℝ) 1 :=
    ⟨by linarith [neg_abs_le (θ*φ q)],by linarith [le_abs_self (θ*φ q)]⟩
  simp only [scalarLevelTransport,projIcc_of_mem zero_le_one he]

 theorem strictMono_scalarLevelTransport (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ)
    (hθ : |θ| *L < 1) : StrictMono (scalarLevelTransport φ θ) := by
  intro p q hpq
  have hreal : (p : ℝ)<q := hpq
  have hd := hφ.dist_le_mul q p
  change |φ q-φ p| ≤ (L : ℝ)*|(q : ℝ)-p| at hd
  have hpd : |φ q-φ p| ≤ L*((q : ℝ)-p) := by
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hreal)] using hd
  have hs : |θ*(φ q-φ p)| < (q : ℝ)-p := by
    rw [abs_mul]
    calc
      _ ≤ |θ| *(L*((q : ℝ)-p)) := mul_le_mul_of_nonneg_left hpd (abs_nonneg _)
      _ < (q : ℝ)-p := by nlinarith [mul_lt_mul_of_pos_right hθ (sub_pos.mpr hreal)]
  change (scalarLevelTransport φ θ p : ℝ)<scalarLevelTransport φ θ q
  rw [scalarLevelTransport_eq_affine φ L hφ h0 h1 θ hθ.le,
    scalarLevelTransport_eq_affine φ L hφ h0 h1 θ hθ.le]
  linarith [neg_abs_le (θ*(φ q-φ p))]

end QuantitativeFollowup
