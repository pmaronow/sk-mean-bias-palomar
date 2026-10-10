module
public import QuantitativeFollowup.ScalarGaussianHistoryCurve
public import FourPapersCommon.SignedAffineCellSplitting
public import FourPapersCommon.ThreefoldSchemeRefinement

@[expose] public section

/-! Actual nonnegative same-mass refinements for a signed transport of
scalar overlap levels. The refined measure is exactly the transported
original measure, including every zero-length and zero-mass cell. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

def scalarTransportCellSlope (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (i : ℕ) : ℝ :=
  φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i)

def scalarTransportCellBase (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (i : ℕ) : ℝ :=
  s.q (i+1)-s.q i-δ*|scalarTransportCellSlope s φ i|

def scalarTransportCellActive (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (i : ℕ) : ℝ :=
  2*δ*|scalarTransportCellSlope s φ i|

theorem scalarTransportCellSlope_abs_le (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (i : ℕ) (hi : i ≤ k+1) :
    |scalarTransportCellSlope s φ i| ≤ (L:ℝ)*(s.q (i+1)-s.q i) := by
  have hh := hφ.dist_le_mul (scalarSchemeTransportNode s (i+1)) (scalarSchemeTransportNode s i)
  rw [Real.dist_eq,Subtype.dist_eq,Real.dist_eq,
    scalarSchemeTransportNode_coe s (i+1) (by omega),
    scalarSchemeTransportNode_coe s i (by omega),abs_of_nonneg (sub_nonneg.mpr (s.q_mono i hi))] at hh
  exact hh

theorem scalarTransportCellBase_nonneg (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ*L ≤ 1)
    (i : ℕ) (hi : i ≤ k+1) : 0 ≤ scalarTransportCellBase s φ δ i := by
  have hb := mul_le_mul_of_nonneg_left (scalarTransportCellSlope_abs_le s φ L hφ i hi) hδ
  have hc := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr (s.q_mono i hi))
  dsimp only [scalarTransportCellBase]
  nlinarith [hb,hc]

def scalarTransportFirstRefinedNode (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (δ u : ℝ) (i : ℕ) : ℝ :=
  s.q i+u*φ (scalarSchemeTransportNode s i)+
    signedAffineCellScale (scalarTransportCellSlope s φ i) (signedAffineCellTime δ u)*
      scalarTransportCellActive s φ δ i

def scalarTransportSecondRefinedNode (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (δ u : ℝ) (i : ℕ) : ℝ :=
  scalarTransportFirstRefinedNode s φ δ u i+
    signedAffineCellTime δ u*scalarTransportCellBase s φ δ i

theorem scalarTransport_parameter_small (L : ℝ≥0) (δ u : ℝ)
    (hsmall : δ*L < 1) (hu : |u| ≤ δ) : |u| *L < 1 :=
  (mul_le_mul_of_nonneg_right hu L.coe_nonneg).trans_lt hsmall

theorem scalarTransportRefinedNodes_ordered (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ) :
    ∀i ≤ k+1,
      (scalarTransportScheme s φ L hφ h0 h1 u (scalarTransport_parameter_small L δ u hsmall hu)).q i ≤ 
        scalarTransportFirstRefinedNode s φ δ u i ∧
      scalarTransportFirstRefinedNode s φ δ u i ≤ scalarTransportSecondRefinedNode s φ δ u i ∧
      scalarTransportSecondRefinedNode s φ δ u i ≤ 
        (scalarTransportScheme s φ L hφ h0 h1 u (scalarTransport_parameter_small L δ u hsmall hu)).q (i+1) := by
  intro i hi
  have hb := scalarTransportCellBase_nonneg s φ L hφ δ hδ.le hsmall.le i hi
  have hp := signedAffineCellSplitting_order (s.q (i+1)-s.q i)
    (scalarTransportCellSlope s φ i) δ u hδ hu hb
  have he := signedAffineCellSplitting_sum (s.q (i+1)-s.q i)
    (scalarTransportCellSlope s φ i) δ u hδ.ne'
  rw [scalarTransportScheme_overlap s φ L hφ h0 h1 u _ i (by omega),
    scalarTransportScheme_overlap s φ L hφ h0 h1 u _ (i+1) (by omega)]
  have hni : (⟨s.q i,s.q_nonneg (by omega),s.q_le_one (by omega)⟩ : Paper.Overlap)=
      scalarSchemeTransportNode s i := by
    apply Subtype.ext
    exact (scalarSchemeTransportNode_coe s i (by omega)).symm
  have hnj : (⟨s.q (i+1),s.q_nonneg (by omega),s.q_le_one (by omega)⟩ : Paper.Overlap)=
      scalarSchemeTransportNode s (i+1) := by
    apply Subtype.ext
    exact (scalarSchemeTransportNode_coe s (i+1) (by omega)).symm
  rw [hni,hnj]
  dsimp only [scalarTransportFirstRefinedNode,scalarTransportSecondRefinedNode,
    scalarTransportCellActive,scalarTransportCellBase]
  constructor
  · linarith [hp.1]
  constructor
  · linarith [hp.2.1]
  · dsimp only [scalarTransportCellSlope] at *
    linarith [hp.2.2,he]

def scalarTransportRefinedScheme (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ) : RSBScheme (3*k+4) :=
  threefoldScheme
    (scalarTransportScheme s φ L hφ h0 h1 u (scalarTransport_parameter_small L δ u hsmall hu))
    (scalarTransportFirstRefinedNode s φ δ u) (scalarTransportSecondRefinedNode s φ δ u)
    (scalarTransportRefinedNodes_ordered s φ L hφ h0 h1 δ u hδ hsmall hu)

theorem scalarTransportRefinedScheme_measure (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ) :
    Paper.parisiSchemeMeasure (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu)=
      scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u := by
  rw [scalarTransportRefinedScheme,parisiSchemeMeasure_threefold,scalarTransportScheme_measure]

theorem scalarTransportRefinedScheme_three_cells (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ) (i : ℕ) (hi : i ≤ k+1) :
    let r:=scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu
    r.q (3*i+1)-r.q (3*i)=
      signedAffineCellScale (scalarTransportCellSlope s φ i) (signedAffineCellTime δ u)*
        scalarTransportCellActive s φ δ i ∧
    r.q (3*i+2)-r.q (3*i+1)=signedAffineCellTime δ u*scalarTransportCellBase s φ δ i ∧
    r.q (3*(i+1))-r.q (3*i+2)=
      (1-signedAffineCellTime δ u)*scalarTransportCellBase s φ δ i := by
  dsimp only
  simp only [scalarTransportRefinedScheme,threefoldScheme_q_original,
    threefoldScheme_q_first,threefoldScheme_q_second]
  rw [scalarTransportScheme_overlap s φ L hφ h0 h1 u _ i (by omega),
    scalarTransportScheme_overlap s φ L hφ h0 h1 u _ (i+1) (by omega)]
  have he := signedAffineCellSplitting_sum (s.q (i+1)-s.q i)
    (scalarTransportCellSlope s φ i) δ u hδ.ne'
  have hni : (⟨s.q i,s.q_nonneg (by omega),s.q_le_one (by omega)⟩ : Paper.Overlap)=
      scalarSchemeTransportNode s i := by
    apply Subtype.ext
    exact (scalarSchemeTransportNode_coe s i (by omega)).symm
  have hnj : (⟨s.q (i+1),s.q_nonneg (by omega),s.q_le_one (by omega)⟩ : Paper.Overlap)=
      scalarSchemeTransportNode s (i+1) := by
    apply Subtype.ext
    exact (scalarSchemeTransportNode_coe s (i+1) (by omega)).symm
  rw [hni,hnj]
  dsimp only [scalarTransportFirstRefinedNode,scalarTransportSecondRefinedNode,
    scalarTransportCellActive,scalarTransportCellBase,scalarTransportCellSlope] at *
  constructor
  · ring
  constructor
  · ring
  · linarith [he]

end QuantitativeFollowup
