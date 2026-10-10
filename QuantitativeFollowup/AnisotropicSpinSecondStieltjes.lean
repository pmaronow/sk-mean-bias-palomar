module
public import QuantitativeFollowup.AnisotropicSpinSecondPairing
public import QuantitativeFollowup.AnisotropicSpinConditionalLimit
public import QuantitativeFollowup.AnisotropicProcessEnergy

@[expose] public section

/-! Atom-exact tested binary-feature response at every actual finite node.
The constructed Wiener transition law and repeated-level Stieltjes boundary
give the right CDF and the strict future, without a posterior identity premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

def anisotropicFiniteTailSpinSecond (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (e : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s q))
    P (anisotropicCoordinateDirection n e) (anisotropicCoordinateDirection n e)

def anisotropicTailSpinSecond (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (e : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
    P (anisotropicCoordinateDirection n e) (anisotropicCoordinateDirection n e)

theorem anisotropicSchemeNode_eq_scalar_spin (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) :
    anisotropicSchemeNode s i hi=scalarSchemeTransportNode s i := by
  apply Subtype.ext
  exact (scalarSchemeTransportNode_coe s i hi).symm

theorem anisotropicFiniteTailSpinSecond_node (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (hi : i ≤ k+2) (P : AnisotropicParameter n) (e : Fin n) :
    anisotropicFiniteTailSpinSecond D s (anisotropicSchemeNode s i hi) P e=
      anisotropicFiniteSpinSecond D s (k+2-i) P e := by
  unfold anisotropicFiniteTailSpinSecond anisotropicFiniteSpinSecond
  rw [anisotropicFiniteTailPotential_node]

theorem anisotropicFiniteTailSpinResponse_eq_feature_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) (P : AnisotropicParameter n)
    (e : Fin n) :
    anisotropicFiniteTailSpinResponse D s (anisotropicSchemeNode s i hi) P e=
      anisotropicFiniteFeatureMean D s (k+2-i) (anisotropicSpinFeature e) P := by
  rw [anisotropicFiniteTailSpinResponse_node]
  rfl

theorem anisotropicFinite_spin_second_node_stieltjes_pairing (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+2)
    (e : Fin n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    let q:=anisotropicSchemeNode s i hi
    (∫p,Z p*anisotropicFiniteTailSpinSecond D s q
      (anisotropicFiniteProcessParameter D s q (g,p.2)) e ∂vectorDisorderBrownianMeasure n)+
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*
        (∫p,Z p*(anisotropicFiniteTailSpinResponse D s q
          (anisotropicFiniteProcessParameter D s q (g,p.2)) e)^2 ∂vectorDisorderBrownianMeasure n)+
      (∫r,if q < r then (∫p,Z p*(anisotropicFiniteTailSpinResponse D s r
        (anisotropicFiniteProcessParameter D s r (g,p.2)) e)^2 ∂vectorDisorderBrownianMeasure n) else 0
          ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∫p,Z p ∂vectorDisorderBrownianMeasure n := by
  let F:=fun r : Paper.Overlap=>∫p,Z p*(anisotropicFiniteTailSpinResponse D s r
    (anisotropicFiniteProcessParameter D s r (g,p.2)) e)^2 ∂vectorDisorderBrownianMeasure n
  have hnode (u : ℕ) (hu : u ≤ k+2) : F (scalarSchemeTransportNode s u)=
      ∫p,Z p*(anisotropicFiniteFeatureMean D s (k+2-u) (anisotropicSpinFeature e)
        (anisotropicFinitePhysicalParameter D s g (s.q u).toNNReal p))^2
          ∂vectorDisorderBrownianMeasure n := by
    rw [←anisotropicSchemeNode_eq_scalar_spin s u hu]
    apply integral_congr_ae
    exact .of_forall fun p=>by
      dsimp only
      rw [anisotropicFiniteTailSpinResponse_eq_feature_node]
      rfl
  have he:=anisotropicFinite_spin_second_wholePast_pairing D s g i hi e Z hZ hZi
  have hs:=scalarScheme_stieltjes_boundary s (k+2-i) (Nat.sub_le _ _) F
  have hcancel : k+2-(k+2-i)=i := by omega
  rw [hcancel,hnode i hi] at hs
  have hsum : (∑r∈Finset.range (k+2-i),(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
      F (scalarSchemeTransportNode s (k+1-r)))=
      ∑r∈Finset.range (k+2-i),(anisotropicSchemeMass s r-anisotropicSchemeMass s (r+1))*
        (∫p,Z p*(anisotropicFiniteFeatureMean D s (r+1) (anisotropicSpinFeature e)
          (anisotropicFinitePhysicalParameter D s g (s.q (k+1-r)).toNNReal p))^2
            ∂vectorDisorderBrownianMeasure n) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hh:=Finset.mem_range.mp hr
    rw [hnode (k+1-r) (by omega),show k+2-(k+1-r)=r+1 by omega]
    rfl
  rw [hsum] at hs
  change anisotropicSchemeMass s (k+2-i)*_+_= _ at hs
  rw [add_assoc,hs] at he
  dsimp only
  simp_rw [anisotropicFiniteTailSpinSecond_node,anisotropicFiniteTailSpinResponse_eq_feature_node]
  rw [←anisotropicSchemeNode_eq_scalar_spin s i hi] at he
  have hcur (p : VectorDisorderBrownianSample n) :
      anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal p=
        anisotropicFiniteProcessParameter D s (anisotropicSchemeNode s i hi) (g,p.2) := by rfl
  simp_rw [hcur] at he
  simpa only [add_assoc,F] using he

end QuantitativeFollowup
