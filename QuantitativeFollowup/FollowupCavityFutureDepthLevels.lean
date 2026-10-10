module
public import QuantitativeFollowup.FollowupCavityGraftedCubicMoments
public import QuantitativePaper.VectorProfileMeasure

@[expose] public section

/-! On the literal free Stieltjes measure, the finite future depth has
exactly the prescribed physical overlap, including repeated scheme nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 900000

theorem ae_parisiFreeMeasure_profile_atom (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) :
    ∀ᵐq∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a,
      ∃i : vectorPosteriorFeatureIndex k,q=vectorProfileAtom s i := by
  rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,vectorProfileFreeMeasure,
    ae_finsetSum_measure_iff]
  intro i _
  apply Measure.ae_smul_measure
  rw [ae_dirac_eq]
  exact ⟨i,rfl⟩

theorem cavityFiniteFutureDepth_level_profile_atom (s : RSBScheme k) (J : ℕ)
    (hJ : J≤k+2) (i : vectorPosteriorFeatureIndex k)
    (hfuture : cavityProfileLevel s J<vectorProfileAtom s i) :
    cavityProfileLevel s (cavityFiniteFutureDepth s J (vectorProfileAtom s i))=vectorProfileAtom s i := by
  let t:=vectorPosteriorFeatureTime i
  have ht : t≤k+2 := by cases i <;> dsimp [t,vectorPosteriorFeatureTime] <;> omega
  have hi : vectorProfileAtom s i=scalarSchemeTransportNode s t := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe s t ht]
    rfl
  have htlarge : k+2-J<t := by
    by_contra hn
    have htle : t≤k+2-J := by omega
    have hh:=s.q_mono' (k+2-J) (by omega) t htle
    have hx : (cavityProfileLevel s J:ℝ)<(vectorProfileAtom s i:ℝ) := hfuture
    rw [hi,scalarSchemeTransportNode_coe s t ht,cavityProfileLevel,
      scalarSchemeTransportNode_coe s _ (by omega)] at hx
    linarith
  let p:=k+2-t
  have hp : p≤J := by dsimp [p]; omega
  have htime : k+2-p=t := by dsimp [p]; omega
  have hd:=cavityFiniteFutureDepth_node s J p hJ hp
  apply Subtype.ext
  rw [cavityProfileLevel,scalarSchemeTransportNode_coe s _ (by
    have hh:=cavityFiniteFutureDepth_le s J (vectorProfileAtom s i);omega)]
  rw [hi,scalarSchemeTransportNode_coe s t ht]
  simpa only [hi,htime] using hd.2

theorem ae_cavityFiniteFutureDepth_level (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (J : ℕ) (hJ : J≤k+2) :
    ∀ᵐq∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a,
      cavityProfileLevel s J<q → cavityProfileLevel s (cavityFiniteFutureDepth s J q)=q := by
  filter_upwards [ae_parisiFreeMeasure_profile_atom s a ha has hq] with q hq'
  obtain ⟨i,rfl⟩:=hq'
  exact cavityFiniteFutureDepth_level_profile_atom s J hJ i

end QuantitativeFollowup
