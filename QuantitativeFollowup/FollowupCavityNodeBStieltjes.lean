module
public import QuantitativeFollowup.FollowupCavityNodeBDerivative
public import QuantitativeFollowup.FollowupCavityParameters

@[expose] public section

/-! Literal finite-node last-field covariance response. The future square
is the actual normalized continuation average of the binary terminal spin,
and the strict future Stieltjes integral retains every endpoint atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

/-- Genuine conditional square of the coordinate magnetization, under the
actual finite Gaussian continuation kernels from the given history. -/
def cavityFiniteConditionalCoordinateSquare (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (P : AnisotropicParameter n) (i : Fin n)
    (r : Paper.Overlap) : ℝ :=
  let d:=cavityFiniteFutureDepth s J r
  ∫y,(∫σ,Paper.spinSign (σ i) ∂finiteStateCascadeGibbsKernel
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y)^2
    ∂OverlapPaper.sourceKernelLaw (fun l=>finiteStateGaussianCascadeKernel
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      (gtStateLogPartition (fun _ : Configuration n=>0)) (d+l)) (J-d) (anisotropicEnergyMap D P)

theorem cavityFiniteConditionalCoordinateSquare_eq_futureSquare (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (P : AnisotropicParameter n) (i : Fin n) (r : Paper.Overlap) :
    cavityFiniteConditionalCoordinateSquare D s J P i r=
      cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P) (cavityCoordinateFeature i) r := by
  exact (cavityFiniteFutureSquare_eq_conditional_integral D s J
    (anisotropicEnergyMap D P) (cavityCoordinateFeature i) r).symm

theorem hasDerivAt_anisotropicFinitePotential_variance_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (p : ℕ) (hp : p≤k+2) (P : AnisotropicParameter n) :
    HasDerivAt (fun b=>anisotropicFinitePotential (anisotropicReplaceVariance D i b) s (k+2-p) P)
      ((1/2 : ℝ)*(1-s.q p-
        ∫r,if scalarSchemeTransportNode s p<r then
          ((r:ℝ)-s.q p)*cavityFiniteConditionalCoordinateSquare D s (k+2-p) P i r else 0
          ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))) (D.variance i) := by
  have hd:=hasDerivAt_anisotropicFinitePotential_variance_self D s i (k+2-p) P
  rw [cavityFiniteNodeBResponse_stieltjes D s (k+2-p) (by omega)
    (anisotropicEnergyMap D P) (cavityCoordinateFeature i) (cavityCoordinateFeature_binary i)] at hd
  rw [show k+2-(k+2-p)=p by omega] at hd
  simp_rw [cavityFiniteConditionalCoordinateSquare_eq_futureSquare]
  exact hd

/-- Source eq:nodeb for the genuine free finite Parisi measure. The initial
root atom is removed without altering the strict future response. -/
theorem cavity_finite_node_b (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (p : ℕ) (hp : p≤k+2) (P : AnisotropicParameter n)
    (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0) :
    HasDerivAt (fun b=>anisotropicFinitePotential (anisotropicReplaceVariance D i b) s (k+2-p) P)
      ((1/2 : ℝ)*(1-s.q p-
        ∫r,if scalarSchemeTransportNode s p<r then
          ((r:ℝ)-s.q p)*cavityFiniteConditionalCoordinateSquare D s (k+2-p) P i r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)) (D.variance i) := by
  have hd:=hasDerivAt_anisotropicFinitePotential_variance_self D s i (k+2-p) P
  rw [cavityFiniteNodeBResponse_free_stieltjes D s (k+2-p) (by omega) a ha has hq
    (anisotropicEnergyMap D P) (cavityCoordinateFeature i) (cavityCoordinateFeature_binary i)] at hd
  rw [show k+2-(k+2-p)=p by omega] at hd
  simp_rw [cavityFiniteConditionalCoordinateSquare_eq_futureSquare]
  exact hd

/-- The literal last-field coefficient response in the physical one-site
row model, including both row endpoints. The row coupling is held fixed. -/
theorem followup_cavity_finite_node_b (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (u : ℝ) (hu : u ∈ Icc 0 1)
    (s : RSBScheme k) (p : ℕ) (hp : p ≤ k+2) (P : AnisotropicParameter (n+1))
    (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0) :
    HasDerivAt (fun b=>anisotropicFinitePotential
      (anisotropicReplaceVariance (followupCavitySpinModel n β ρ hβ hρ u hu) (Fin.last n) b)
      s (k+2-p) P)
      ((1/2 : ℝ)*(1-s.q p-
        ∫r,if scalarSchemeTransportNode s p<r then
          ((r:ℝ)-s.q p)*cavityFiniteConditionalCoordinateSquare
            (followupCavitySpinModel n β ρ hβ hρ u hu) s (k+2-p) P (Fin.last n) r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)) (followupCavityB n β ρ u) := by
  simpa only [followupCavitySpinModel_variance_last] using
    cavity_finite_node_b (followupCavitySpinModel n β ρ hβ hρ u hu) s (Fin.last n) p hp P a ha has hq

end QuantitativeFollowup
