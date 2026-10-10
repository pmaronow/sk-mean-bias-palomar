module
public import QuantitativePaper.VectorMeasureSitePermutationMoments

@[expose] public section

/-! The coefficient-one deleted-site variance comparison under the actual
tilted SK law. Exchangeability is proved by native site transport, rather
than supplied as a hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {N : ℕ}
set_option maxHeartbeats 1800000

def cavityDeletedSiteSelfOverlap (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (i : Fin N) (sample : VectorDisorderBrownianSample N) : ℝ :=
  (∑j ∈ Finset.univ.erase i,(vectorMeasureSpinMean μ β t ht q sample j)^2)/((N:ℝ)-1)

theorem cavityDeletedSiteSelfOverlap_eq (hN : 1<N) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin N) :
    cavityDeletedSiteSelfOverlap μ β t ht q i = fun sample =>
      ((N:ℝ)*vectorMeasureSelfSquare μ β t ht q sample-vectorMeasureSiteSquare μ β t ht q i sample)/((N:ℝ)-1) := by
  funext sample
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin N)))
    (f := fun j => (vectorMeasureSpinMean μ β t ht q sample j)^2) (Finset.mem_univ i)
  unfold cavityDeletedSiteSelfOverlap vectorMeasureSelfSquare vectorMeasureSiteSquare
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  field_simp
  linarith

theorem cavityDeletedSiteSelfOverlap_variance_eq (hN : 1<N) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin N) :
    variance (cavityDeletedSiteSelfOverlap μ β t ht q i) (vectorMeasureDisorderTilt μ β t a) =
      (((N:ℝ)^2-2*(N:ℝ))*variance (vectorMeasureSelfSquare (n:=N) μ β t ht q)
        (vectorMeasureDisorderTilt μ β t a)+variance (vectorMeasureSiteSquare μ β t ht q i)
          (vectorMeasureDisorderTilt μ β t a))/((N:ℝ)-1)^2 := by
  let P := vectorMeasureDisorderTilt (n:=N) μ β t a
  let S := vectorMeasureSelfSquare (n:=N) μ β t ht q
  let f := vectorMeasureSiteSquare μ β t ht q i
  haveI := vectorMeasureDisorderTilt_probability (n:=N) μ β t a ht
  have hS : MemLp S 2 P := memLp_vectorMeasureSelfSquare μ β t a ht q
  have hf : MemLp f 2 P := memLp_vectorMeasureSiteSquare μ β t a ht q i
  have hNS : MemLp (fun z => (N:ℝ)*S z) 2 P := hS.const_mul _
  have hc : covariance S f P = variance S P :=
    covariance_vectorMeasureSelfSquare_site_eq_variance (by omega) μ β t a ht q i
  have hnum : variance (fun z => (N:ℝ)*S z-f z) P =
      ((N:ℝ)^2-2*(N:ℝ))*variance S P+variance f P := by
    change variance ((fun z => (N:ℝ)*S z)-f) P = _
    rw [←covariance_self (hNS.sub hf).aemeasurable,
      covariance_sub_sub hNS hf hNS hf,
      covariance_const_mul_left,covariance_const_mul_right,covariance_const_mul_left,
      covariance_const_mul_right,covariance_self hS.aemeasurable,covariance_self hf.aemeasurable,
      hc,covariance_comm f S,hc]
    ring
  rw [cavityDeletedSiteSelfOverlap_eq hN]
  have he : (fun z => ((N:ℝ)*S z-f z)/((N:ℝ)-1))=
      fun z => (((N:ℝ)-1)⁻¹)*((N:ℝ)*S z-f z) := by funext z; ring
  change variance (fun z => ((N:ℝ)*S z-f z)/((N:ℝ)-1)) P = _
  rw [he,variance_const_mul,hnum]
  dsimp only [P,S,f]
  rw [inv_pow]
  ring

theorem cavityDeletedSiteSelfOverlap_variance_le (hN : 1<N) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin N) :
    variance (cavityDeletedSiteSelfOverlap μ β t ht q i) (vectorMeasureDisorderTilt μ β t a) ≤
      variance (vectorMeasureSelfSquare (n:=N) μ β t ht q) (vectorMeasureDisorderTilt μ β t a)+
        1/(4*((N:ℝ)-1)^2) := by
  haveI := vectorMeasureDisorderTilt_probability (n:=N) μ β t a ht
  have hsite := variance_le_sq_of_bounded
    (μ := vectorMeasureDisorderTilt (n:=N) μ β t a)
    (X := vectorMeasureSiteSquare μ β t ht q i)
    (.of_forall (vectorMeasureSiteSquare_bounds μ β t ht q i))
    (measurable_vectorMeasureSiteSquare μ β t ht q i).aemeasurable
  norm_num at hsite
  rw [cavityDeletedSiteSelfOverlap_variance_eq hN]
  have hN' : 1<(N:ℝ) := by exact_mod_cast hN
  have hn : 0<((N:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hn).2
  have hv := variance_nonneg (vectorMeasureSelfSquare (n:=N) μ β t ht q)
    (vectorMeasureDisorderTilt μ β t a)
  have hcancel : (1/(4*((N:ℝ)-1)^2))*((N:ℝ)-1)^2 = (1/4:ℝ) := by
    field_simp [ne_of_gt (sub_pos.mpr hN')]
  rw [add_mul,hcancel]
  nlinarith

end QuantitativeFollowup
