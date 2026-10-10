module
public import HexagonPaper.CavityVertexCancellationRestartSquare
public import QuantitativeFollowup.AnisotropicSpinSecondFinite
public import QuantitativeFollowup.AnisotropicVarianceDerivative

@[expose] public section

/-! Pointwise binary-feature curvature at every genuine restarted field.
Clamping keeps the complete starting-level atom in the current posterior
square before passing to the actual all-profile derivative limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n k : ℕ}

 theorem cavityFinite_clamped_coordinate_square_current (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme s q q.property) (k+2) P i q=
      (anisotropicFiniteTailMagnetization D s q P i)^2 := by
  let c:=vectorClampedScheme s q q.property
  have hnode : scalarSchemeTransportNode c 1=q := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe c 1 (by omega),vectorClampedScheme_overlap_succ,
      s.q_zero,max_eq_left q.property.1]
  have ht:=cavityFiniteFutureSquare_current D c (k+2) (by omega)
  rw [show k+1+2-(k+2)=1 by omega,hnode] at ht
  change cavityFiniteConditionalCoordinateSquare D c (k+2) P i q=_
  rw [cavityFiniteConditionalCoordinateSquare_eq_futureSquare,ht]
  change (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass c) (cavityFiniteEnergyInput D c) (k+2))
    (anisotropicEnergyMap D P) (anisotropicSpinFeature i))^2=_
  rw [anisotropicFiniteSpin_energy_first,anisotropicFiniteTailMagnetization_clamped,
    anisotropicMagnetization_eq_spin_mean]
  rfl

 theorem cavityFinite_tail_spin_second_total_integral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q)) P
        (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)=
      1-∫r,cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme s q q.property)
        (k+2) P i (anisotropicClampOverlap q r) ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
  let c:=vectorClampedScheme s q q.property
  let H:=anisotropicEnergyMap D P
  let K:=cavityCoordinateFeature i
  have hb:=finiteStateCascadeBinaryFeature_second (fun _ : Configuration n=>0)
    (anisotropicSchemeMass c) (anisotropicSchemeMass_nonneg c) (cavityFiniteEnergyInput D c)
    (k+2) H K (cavityCoordinateFeature_binary i)
  have ha0 : anisotropicSchemeMass c 0=1 := by simp [anisotropicSchemeMass,c.m_top]
  have haJ : anisotropicSchemeMass c (k+2)=0 := by
    unfold anisotropicSchemeMass
    rw [show k+1+1-(k+2)=0 by omega]
    exact c.m_zero
  have haS : anisotropicSchemeMass c (k+2+1)=0 := by
    unfold anisotropicSchemeMass
    rw [show k+1+1-(k+2+1)=0 by omega]
    exact c.m_zero
  rw [ha0,sub_self,zero_mul,sub_zero,haJ,zero_mul] at hb
  simp_rw [←finiteStateCascadePairMoment_eq_splitLaw _ _ (anisotropicSchemeMass_nonneg c)] at hb
  have he : (∫r,cavityFiniteConditionalCoordinateSquare D c (k+2) P i r
        ∂(Paper.parisiSchemeMeasure c:Measure Paper.Overlap))=
      ∑p∈Finset.range (k+2),(anisotropicSchemeMass c p-anisotropicSchemeMass c (p+1))*
        finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass c)
          (cavityFiniteEnergyInput D c) (p+1) ((k+2)-(p+1)) H K K := by
    rw [integral_scalarScheme_reverse]
    conv_lhs => rw [show k+1+2=(k+2)+1 by omega,Finset.sum_range_succ]
    have hz : (scalarSchemeMass c (k+2)-scalarSchemeMass c (k+2+1))*
        cavityFiniteConditionalCoordinateSquare D c (k+2) P i
          (scalarSchemeTransportNode c (k+1+1-(k+2)))=0 := by
      change (anisotropicSchemeMass c (k+2)-anisotropicSchemeMass c (k+2+1))*_=0
      rw [haJ,haS,sub_self,zero_mul]
    rw [hz,add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    rw [cavityFiniteConditionalCoordinateSquare_eq_futureSquare,
      show k+1+1-p=k+1+2-(p+1) by omega,
      cavityFiniteFutureSquare_node D c (k+2) (p+1) (by omega) (by
        have hh:=Finset.mem_range.mp hp
        omega)]
    rfl
  rw [←he] at hb
  have hh : fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q)) P
      (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)=
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass c) (cavityFiniteEnergyInput D c) (k+2))) H K K := by
    unfold anisotropicFiniteTailPotential
    rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
    change anisotropicFiniteSpinSecond D c (k+2) P i=_
    exact anisotropicFiniteSpinSecond_eq_energy D c (k+2) P i
  rw [hh,←integral_anisotropicClampedSchemeMeasure]
  linarith

end HexagonPaper
