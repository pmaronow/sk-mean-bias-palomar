module
public import QuantitativePaper.VectorRootInterpolationTime
public import QuantitativePaper.VectorRootCorrection
public import QuantitativePaper.VectorCascadeReplicaDefect

@[expose] public section

/-! The exact signed covariance telescope is the weighted actual split-spin
replica defect, with the physical CDF correction canceled explicitly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2400000
variable {n k : ℕ}

theorem vectorOverlap_self (hn : 0<n) (σ : Configuration n) : overlap n σ σ=1 := by
  have hs (i:Fin n) : Paper.spinSign (σ i)*Paper.spinSign (σ i)=(1:ℝ):=by
    cases σ i <;> simp [Paper.spinSign]
  unfold overlap
  simp_rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hn' : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  field_simp

theorem vectorRootCovarianceMoment_gap (hn : 0<n) (s : RSBScheme k) (β t a : ℝ)
    (ha : 0≤a) (hq : s.q 1=0) (p : ℕ) (hp : p≤k+1) :
    finiteStateCascadeCovarianceMoment (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
      (vectorRootInterpolationScaledDirection (n:=n) s β t) p (k+2-p) 0
      (cascadeCovarianceGap (finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β))
        (fun j=>finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j)) (k+1) p)=
      (n:ℝ)*β^2/2*((∫z,(overlap n z.1 z.2-(vectorRootInterpolationOverlap s p:ℝ))^2∂
        finiteStateCascadeSplitLaw (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
          (vectorRootInterpolationScaledDirection (n:=n) s β t) p (k+2-p) 0)-
        (vectorRootInterpolationOverlap s p:ℝ)^2) := by
  haveI:=isProbabilityMeasure_finiteStateCascadeSplitLaw (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection (n:=n) s β t) p (k+2-p) 0
  have he : cascadeCovarianceGap (finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β))
      (fun j=>finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j)) (k+1) p=
      fun σ τ=>(n:ℝ)*β^2/2*((overlap n σ τ-(vectorRootInterpolationOverlap s p:ℝ))^2-
        (vectorRootInterpolationOverlap s p:ℝ)^2) := by
    funext σ τ
    rw [vectorRootInterpolation_covariance_gap hn s β hq p hp]
    dsimp only [vectorRootInterpolationOverlap]
    ring
  rw [he,finiteStateCascadeCovarianceMoment,integral_const_mul,
    integral_sub Integrable.of_finite (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]

theorem vectorRootCovarianceDiagonal_gap (hn : 0<n) (s : RSBScheme k) (β t a : ℝ)
    (ha : 0≤a) (hq : s.q 1=0) :
    finiteStateCascadeDiagonalMoment (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
      (vectorRootInterpolationScaledDirection (n:=n) s β t) (k+2) 0
      (cascadeCovarianceGap (finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β))
        (fun j=>finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j)) (k+1) 0)=
      -(n:ℝ)*β^2/2 := by
  haveI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection (n:=n) s β t) (k+2)
  have he (σ : Configuration n) :
      cascadeCovarianceGap (finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β))
        (fun j=>finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j)) (k+1) 0 σ σ=
        -(n:ℝ)*β^2/2 := by
    rw [vectorRootInterpolation_covariance_gap hn s β hq 0 (by omega),vectorOverlap_self hn σ]
    simp only [Nat.sub_zero,s.q_top]
    ring
  unfold finiteStateCascadeDiagonalMoment
  simp_rw [he]
  simp

theorem finiteVectorRootInterpolationTime_eq_replica_defects (hn : 0<n) (s : RSBScheme k)
    (β a : ℝ) (ha : 0≤a) (hq : s.q 1=0) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    finiteVectorRootInterpolationTime (n:=n) s β a ha t=
      -β^2/4*∑p∈Finset.range (k+1),(vectorRootInterpolationMass s a p-vectorRootInterpolationMass s a (p+1))*
        (∫z,(overlap n z.1 z.2-(vectorRootInterpolationOverlap s (p+1):ℝ))^2∂
          finiteStateCascadeSplitLaw (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
            (vectorRootInterpolationScaledDirection (n:=n) s β t) (p+1) (k+2-(p+1)) 0) := by
  let mass:=vectorRootInterpolationMass s a
  let L:=vectorRootInterpolationScaledDirection (n:=n) s β t
  let D:=fun p=>(∫z,(overlap n z.1 z.2-(vectorRootInterpolationOverlap s p:ℝ))^2∂
    finiteStateCascadeSplitLaw (fun _ : Configuration n=>0) mass L p (k+2-p) 0)
  have hm0 : mass 0=1:=by simp [mass,vectorRootInterpolationMass,s.m_top]
  rw [finiteVectorRootInterpolationTime_eq_signed_responses s β a ha t ht]
  have htel:=finiteStateCascade_fixed_total_covariance_telescope (fun _ : Configuration n=>0) mass
    (vectorRootInterpolationMass_nonneg s a ha) L (vectorRootInterpolationDirection (n:=n) s β)
    (k+2) (k+1) (by omega) 0 (vectorInterpolationDisorderDirection n β)
  rw [show k+2-(k+1)=1 by omega] at htel
  rw [htel,vectorRootCovarianceDiagonal_gap hn s β t a ha hq]
  change ((1/2:ℝ)*(-(n:ℝ)*β^2/2+(mass 0-1)*_+
    ∑p∈Finset.range (k+1),(mass (p+1)-mass p)*_))/(n:ℝ)+_= _
  rw [hm0,sub_self,zero_mul,add_zero]
  have he : (∑p∈Finset.range (k+1),(mass (p+1)-mass p)*
      finiteStateCascadeCovarianceMoment (fun _ : Configuration n=>0) mass L (p+1) (k+2-(p+1)) 0
        (cascadeCovarianceGap (finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β))
          (fun j=>finiteStateSpectralCovariance (vectorRootInterpolationDirection (n:=n) s β j)) (k+1) (p+1)))=
      -((n:ℝ)*β^2/2)*(∑p∈Finset.range (k+1),(mass p-mass (p+1))*D (p+1))+
        ((n:ℝ)*β^2/2)*(∑p∈Finset.range (k+1),(mass p-mass (p+1))*(vectorRootInterpolationOverlap s (p+1):ℝ)^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [vectorRootCovarianceMoment_gap hn s β t a ha hq (p+1) (by have:=Finset.mem_range.mp hp;omega)]
    dsimp only [D,mass,L]
    ring
  rw [he,vectorRootInterpolation_square_correction s a hq]
  have hn' : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  dsimp only [mass,L,D]
  field_simp
  ring

end QuantitativePaper
