module
public import HexagonPaper.CavityFixedRowJets
public import HexagonPaper.CavityTreeUnitCouplings
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFeatureJets

@[expose] public section

/-! Native incident-row observable jets use actual full coupling/field
Taylor derivatives. Schwarz exchange is justified by the proved arbitrary
profile C-infinity potential, including zero Gaussian coupling scales. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact generic square first jet, with its actual derivative. -/
theorem cavityNativeSquare_first (F : E→ℝ) (hF : ContDiff ℝ ∞ F) (H K : E) :
    fderiv ℝ (fun Q=>(F Q)^2) H K=2*F H*fderiv ℝ F H K := by
  rw [((hF.differentiable (by simp) H).hasFDerivAt.pow 2).fderiv]
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,ContinuousLinearMap.smul_apply,smul_eq_mul,nsmul_eq_mul]

theorem cavityNativeSquare_second (F : E→ℝ) (hF : ContDiff ℝ ∞ F) (H K : E) :
    fderiv ℝ (fun Q=>fderiv ℝ (fun R=>(F R)^2) Q K) H K=
      2*(fderiv ℝ F H K)^2+2*F H*fderiv ℝ (fun Q=>fderiv ℝ F Q K) H K := by
  have hD : ContDiff ℝ ∞ (fun Q=>fderiv ℝ F Q K):=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun Q=>fderiv ℝ (fun R=>(F R)^2) Q K)=fun Q=>2*F Q*fderiv ℝ F Q K :=
    funext fun Q=>cavityNativeSquare_first F hF Q K
  have h:=((((hF.differentiable (by simp) H).hasFDerivAt.const_mul 2).mul
    ((hD.differentiable (by simp) H).hasFDerivAt))).fderiv
  simp only [Pi.mul_def] at h
  rw [he,h]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem cavityNativeDirectionalSquare_second (U : E→ℝ) (hU : ContDiff ℝ ∞ U) (H b K : E) :
    fderiv ℝ (fun Q=>fderiv ℝ (fun R=>(fderiv ℝ U R b)^2) Q K) H K=
      2*(fderiv ℝ (fun Q=>fderiv ℝ U Q K) H b)^2+
        2*fderiv ℝ U H b*
          fderiv ℝ (fun Q=>fderiv ℝ (fun R=>fderiv ℝ U R K) Q K) H b := by
  have hF : ContDiff ℝ ∞ (fun Q=>fderiv ℝ U Q b) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have h2:=cavity_directional_second_symmetry U hU H b K
  have h3:=cavity_directional_third_exchange U hU H b K
  rw [cavityNativeSquare_second _ hF]
  rw [h2,h3]

variable {n : ℕ}

theorem cavityFixedRow_native_field_unitCouplings (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
      (anisotropicCouplingRescaling D P) (anisotropicCoordinateDirection n i)=
        anisotropicMeasureTailMagnetization D μ q P i := by
  have he : (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) ∘
      anisotropicCouplingRescaling D=anisotropicMeasureTailPotential D μ q :=
    funext (cavityTree_native_tail_unitCouplings D μ q)
  have hd := ((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.differentiable
    (by simp) (anisotropicCouplingRescaling D P)).hasFDerivAt.comp P
      (anisotropicCouplingRescaling D).hasFDerivAt
  rw [he] at hd
  have hh:=congrArg (fun L : AnisotropicParameter n→L[ℝ]ℝ=>L (anisotropicCoordinateDirection n i)) hd.fderiv
  rw [ContinuousLinearMap.comp_apply] at hh
  have hb : anisotropicCouplingRescaling D (anisotropicCoordinateDirection n i)=
      anisotropicCoordinateDirection n i := anisotropicCouplingRescaling_field D _
  rw [hb] at hh
  exact hh.symm

theorem contDiff_cavityFixedRow_native_pair_response (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    ContDiff ℝ ∞ (fun P=>anisotropicTailPairResponse D μ q P e) := by
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  have hu:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have h : ContDiff ℝ ∞ (fun P=>fderiv ℝ U P (anisotropicCouplingDirection e)) :=
    (hu.fderiv_right (m:=∞) (by simp)).clm_apply (contDiff_const (c:=anisotropicCouplingDirection e))
  exact h.comp (anisotropicCouplingRescaling D).contDiff

theorem cavityFixedRow_native_magnetization_row_first (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) (i : Fin n) :
    fderiv ℝ (fun Q=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
      Q (anisotropicCoordinateDirection n i))
      (anisotropicCouplingRescaling D P) (anisotropicCouplingDirection e)=
    fderiv ℝ (fun Q=>anisotropicTailPairResponse D μ q Q e) P
      (anisotropicCoordinateDirection n i) := by
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  have hu:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have hs:ContDiff ℝ ∞ (fun Q=>fderiv ℝ U Q (anisotropicCouplingDirection e)) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have he := (hs.differentiable (by simp) (anisotropicCouplingRescaling D P)).hasFDerivAt.comp P
    (anisotropicCouplingRescaling D).hasFDerivAt
  rw [cavity_directional_second_symmetry U hu]
  change _=fderiv ℝ ((fun Q=>fderiv ℝ U Q (anisotropicCouplingDirection e)) ∘
    anisotropicCouplingRescaling D) P (anisotropicCoordinateDirection n i)
  rw [he.fderiv,ContinuousLinearMap.comp_apply]
  rw [show anisotropicCouplingRescaling D (anisotropicCoordinateDirection n i)=
    anisotropicCoordinateDirection n i from anisotropicCouplingRescaling_field D _]

end HexagonPaper
