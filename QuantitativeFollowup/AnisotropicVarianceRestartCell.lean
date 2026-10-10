module
public import QuantitativeFollowup.AnisotropicVarianceRestartState
public import QuantitativeFollowup.AnisotropicWhitenedFiniteTransition

@[expose] public section

/-! The actual backward Gaussian identity on every remaining restarted
anisotropic cell. Physical time is q+elapsed, including a partial first
cell; the drift and Itô pairing are derived from the constructed state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem anisotropicFiniteRestart_cell_drift (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (i : ℕ) (hi : i≤k+1) (r : ℝ≥0)
    (hr : (q:ℝ)+(r:ℝ)∈Ioo (s.q i) (s.q (i+1))) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveDrift (anisotropicFiniteRestartDriftData D s g q) 1 x (vectorRestartHorizon q) r sample=
      s.m i • gradient (vectorColeHopfStep (s.q (i+1)-((q:ℝ)+r)) (s.m i)
        (anisotropicWhitenedFinitePotential D s (k+1-i) g))
          (anisotropicFiniteRestartState D s g q x r sample) := by
  have hr1 : (q:ℝ)+(r:ℝ)≤1:=hr.2.le.trans (s.q_le_one (by omega))
  have hrr : r≤vectorRestartHorizon q:=by
    rw [←NNReal.coe_le_coe,vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
    linarith
  rw [vectorAdditiveDrift,if_pos hrr]
  change anisotropicWhitenedFiniteDrift D s g ((q:ℝ).toNNReal+r) 0
    (anisotropicFiniteRestartState D s g q x r sample)=_
  unfold anisotropicWhitenedFiniteDrift
  rw [NNReal.coe_add,Real.coe_toNNReal (q:ℝ) q.property.1,
    Paper.parisiCDF_scheme_cell s hi ⟨hr.1.le,hr.2⟩]
  change s.m i • anisotropicNoiseMap D (anisotropicFiniteTailMagnetization D s _
    (anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicFiniteRestartState D s g q x r sample)))=_
  rw [←gradient_anisotropicWhitenedFiniteTailPotential,
    anisotropicWhitenedFiniteTailPotential_eq_cell D s _ i hi]
  · simp only [projIcc_of_mem _ ⟨add_nonneg q.property.1 r.coe_nonneg,hr1⟩]
  · simpa only [projIcc_of_mem _ ⟨add_nonneg q.property.1 r.coe_nonneg,hr1⟩] using ⟨hr.1.le,hr.2.le⟩

theorem anisotropicFiniteRestart_cell_backward_pairing (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : ℕ) (hi : i≤k+1)
    (v : ℝ) (hv : v∈Icc (s.q i) (s.q (i+1))) (hqv : (q:ℝ)≤v)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (v-(q:ℝ)).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(G (sample.1,
      anisotropicFiniteRestartState D s g q x (s.q (i+1)-(q:ℝ)).toNNReal sample)-
      vectorJointResponse (anisotropicWhitenedFiniteJointPotential D s (k+1-i) g) G
        (s.q (i+1)-v) (s.m i) (sample.1,
          anisotropicFiniteRestartState D s g q x (v-(q:ℝ)).toNNReal sample)))
        (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(G (sample.1,
      anisotropicFiniteRestartState D s g q x (s.q (i+1)-(q:ℝ)).toNNReal sample)-
      vectorJointResponse (anisotropicWhitenedFiniteJointPotential D s (k+1-i) g) G
        (s.q (i+1)-v) (s.m i) (sample.1,
          anisotropicFiniteRestartState D s g q x (v-(q:ℝ)).toNNReal sample))
        ∂vectorDisorderBrownianMeasure n)=0 := by
  let a : ℝ≥0:=(v-(q:ℝ)).toNNReal
  let Q : ℝ≥0:=(s.q (i+1)-(q:ℝ)).toNNReal
  have ha : (a:ℝ)=v-(q:ℝ):=Real.coe_toNNReal _ (sub_nonneg.mpr hqv)
  have hQ : (Q:ℝ)=s.q (i+1)-(q:ℝ):=Real.coe_toNNReal _ (sub_nonneg.mpr (hqv.trans hv.2))
  have haQ : a≤Q:=by rw [←NNReal.coe_le_coe,ha,hQ];linarith [hv.2]
  have hh:=vector_jointResponse_endpoint_martingale_past
    (anisotropicWhitenedFiniteJointResponseData D s (k+1-i) g hG)
    (vectorItoCharacteristics_anisotropicFiniteRestartState D s g q x)
    (by norm_num : (1:ℝ)^2=1) (by norm_num : (0:ℝ)<1) a Q haQ
    (fun r hr sample=>by
      have hphysical : (q:ℝ)+(r:ℝ)∈Ioo (s.q i) (s.q (i+1)):=by
        have hleft : (a:ℝ)<r:=hr.1
        have hright : (r:ℝ)<Q:=hr.2
        rw [ha] at hleft
        rw [hQ] at hright
        constructor <;> linarith [hv.1]
      have hd:=anisotropicFiniteRestart_cell_drift D s g q x i hi r hphysical sample
      have hvar : (Q:ℝ)-(r:ℝ)=s.q (i+1)-((q:ℝ)+r):=by rw [hQ];ring
      simpa only [one_smul,one_mul,hvar,anisotropicWhitenedFiniteJointPotential_apply] using hd)
    Z hZ C hC
  have hvariance : (Q:ℝ)-(a:ℝ)=s.q (i+1)-v:=by rw [ha,hQ];ring
  simpa only [one_mul,hvariance,a,Q] using hh

end QuantitativeFollowup
