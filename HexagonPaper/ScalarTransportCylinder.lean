module
public import QuantitativeFollowup.ScalarTwoTransport

@[expose] public section

/-! A compact cylinder of small increasing transports. Its inverse is
jointly continuous in the parameter and overlap, so relabelled directions
vary continuously without moving, dropping, or regularizing any atom. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

abbrev ScalarTransportParameter (δ : ℝ) := Icc (-δ) δ

theorem scalarTransportParameter_small (δ : ℝ) (L : ℝ≥0) (hsmall : δ*L<1)
    (u : ScalarTransportParameter δ) : |(u:ℝ)| *L<1 :=
  (mul_le_mul_of_nonneg_right (abs_le.mpr u.property) L.coe_nonneg).trans_lt hsmall

def scalarTransportCylinder (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) :
    ScalarTransportParameter δ×Paper.Overlap → ScalarTransportParameter δ×Paper.Overlap :=
  fun z => (z.1,scalarLevelTransport φ z.1 z.2)

theorem continuous_scalarTransportCylinder (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) :
    Continuous (scalarTransportCylinder φ δ) := by
  exact continuous_fst.prodMk ((continuous_scalarLevelTransport φ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

def scalarTransportCylinderHomeomorph (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) :
    (ScalarTransportParameter δ×Paper.Overlap) ≃ₜ (ScalarTransportParameter δ×Paper.Overlap) :=
  (Equiv.ofBijective (scalarTransportCylinder φ δ) (by
    constructor
    · intro x y hxy
      have hparam := congrArg (fun z : ScalarTransportParameter δ×Paper.Overlap => z.1) hxy
      change x.1=y.1 at hparam
      apply Prod.ext hparam
      have hlevel := congrArg Prod.snd hxy
      simp only [scalarTransportCylinder,hparam] at hlevel
      exact (strictMono_scalarLevelTransport φ L hφ h0 h1 y.1
        (scalarTransportParameter_small δ L hsmall y.1)).injective hlevel
    · intro z
      obtain ⟨q,hq⟩ := surjective_scalarLevelTransport φ h0 h1 z.1 z.2
      exact ⟨(z.1,q),Prod.ext rfl hq⟩)).toHomeomorphOfContinuousClosed
    (continuous_scalarTransportCylinder φ δ)
    (continuous_scalarTransportCylinder φ δ).isClosedMap

@[simp] theorem scalarTransportCylinderHomeomorph_apply (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (z : ScalarTransportParameter δ×Paper.Overlap) :
    scalarTransportCylinderHomeomorph φ L hφ h0 h1 δ hsmall z=
      (z.1,scalarLevelTransport φ z.1 z.2) := rfl

def scalarCylinderRelabelledDirection (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (u : ScalarTransportParameter δ) : C(Paper.Overlap,ℝ) :=
  ⟨fun q => φ ((scalarTransportCylinderHomeomorph φ L hφ h0 h1 δ hsmall).symm (u,q)).2,
    φ.continuous.comp (continuous_snd.comp
      ((scalarTransportCylinderHomeomorph φ L hφ h0 h1 δ hsmall).symm.continuous.comp
        (continuous_const.prodMk continuous_id)))⟩

theorem scalarCylinderRelabelledDirection_transport (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (u : ScalarTransportParameter δ) (q : Paper.Overlap) :
    scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall u
      (scalarLevelTransport φ u q)=φ q := by
  change φ ((scalarTransportCylinderHomeomorph φ L hφ h0 h1 δ hsmall).symm
    ((scalarTransportCylinderHomeomorph φ L hφ h0 h1 δ hsmall) (u,q))).2=φ q
  rw [Homeomorph.symm_apply_apply]

theorem scalarCylinderRelabelledDirection_eq (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (u : ScalarTransportParameter δ) :
    scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall u=
      scalarRelabelledDirection φ φ L hφ h0 h1 u
        (scalarTransportParameter_small δ L hsmall u) := by
  ext p
  obtain ⟨q,rfl⟩ := surjective_scalarLevelTransport φ h0 h1 u p
  rw [scalarCylinderRelabelledDirection_transport,scalarRelabelledDirection_transport]

theorem continuous_scalarCylinderRelabelledDirection (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) :
    Continuous (scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact φ.continuous.comp (continuous_snd.comp
    (scalarTransportCylinderHomeomorph φ L hφ h0 h1 δ hsmall).symm.continuous)

end HexagonPaper
