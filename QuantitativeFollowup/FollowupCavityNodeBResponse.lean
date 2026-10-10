module
public import QuantitativeFollowup.FollowupCavityBinaryNodeStieltjes
public import FourPapersCommon.FiniteStateCascadePropagation

@[expose] public section

/-! The actual propagated Gaussian generator for a single binary covariance
coordinate. Its complete finite-cell sum is the strict future Stieltjes
integral, including repeated nodes and atoms at the starting node. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

private theorem weighted_cell_telescope (Q a F : ℕ→ℝ) (J : ℕ) :
    (∑j∈Finset.range J,(Q j-Q (j+1))*(1+∑p∈Finset.range j,
      (a (p+1)-a p)*F (p+1)))=
    Q 0-Q J+∑p∈Finset.range J,(a (p+1)-a p)*(Q (p+1)-Q J)*F (p+1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    simp only [sub_self,mul_zero,zero_mul,add_zero]
    rw [mul_add,mul_one,Finset.mul_sum]
    have hs : (∑p∈Finset.range J,(a (p+1)-a p)*(Q (p+1)-Q J)*F (p+1))+
        (∑p∈Finset.range J,(Q J-Q (J+1))*((a (p+1)-a p)*F (p+1)))=
        ∑p∈Finset.range J,(a (p+1)-a p)*(Q (p+1)-Q (J+1))*F (p+1) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    linarith

def cavityFiniteBinaryGenerator (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j J : ℕ) (H K : FiniteStateField (Configuration n)) : ℝ :=
  OverlapPaper.sourceKernelExpectation (fun r=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) (gtStateLogPartition (fun _ : Configuration n=>0)) (j+r))
    (J-j) (fun y=>fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j)) y K K+
      anisotropicSchemeMass s j*(fderiv ℝ (finiteStateGaussianTerminalCascade
        (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j) y K)^2) H

def cavityFiniteNodeBResponse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : ℕ) (H K : FiniteStateField (Configuration n)) : ℝ :=
  (1/2 : ℝ)*∑j∈Finset.range J,(s.q (k+2-j)-s.q (k+1-j))*
    cavityFiniteBinaryGenerator D s j J H K

theorem cavityFiniteBinaryGenerator_eq_future_squares (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j J : ℕ) (hj : j≤J)
    (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) :
    cavityFiniteBinaryGenerator D s j J H K=
      1+∑p∈Finset.range j,(anisotropicSchemeMass s (p+1)-anisotropicSchemeMass s p)*
        finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
          (cavityFiniteEnergyInput D s) (p+1) (J-(p+1)) H K K := by
  have he:=finiteStateCascadeHessian_propagated_pair_decomposition
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) j (J-j) H K K
  rw [Nat.add_sub_of_le hj] at he
  have ha0 : anisotropicSchemeMass s 0=1 := by simp [anisotropicSchemeMass,s.m_top]
  have hp : fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J) H
        (finiteStatePointwiseProduct K K)=1 := by
    rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg s)]
    letI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) J
    simp [finiteStatePointwiseProduct_apply,hK]
  rw [ha0,hp] at he
  simp only [sub_self,zero_mul,add_zero] at he
  simpa only [cavityFiniteBinaryGenerator,pow_two,mul_assoc] using he

theorem cavityFiniteNodeBResponse_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (hJ : J≤k+2)
    (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) :
    cavityFiniteNodeBResponse D s J H K=
      (1/2 : ℝ)*(1-s.q (k+2-J)-
        ∫q,if scalarSchemeTransportNode s (k+2-J)<q then
          ((q:ℝ)-s.q (k+2-J))*cavityFiniteFutureSquare D s J H K q else 0
          ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap)) := by
  let Q:=fun j=>s.q (k+2-j)
  let F:=fun p=>finiteStateCascadePairMoment (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p (J-p) H K K
  have hresp : cavityFiniteNodeBResponse D s J H K=
      (1/2 : ℝ)*∑j∈Finset.range J,(Q j-Q (j+1))*(1+
        ∑p∈Finset.range j,(anisotropicSchemeMass s (p+1)-anisotropicSchemeMass s p)*F (p+1)) := by
    unfold cavityFiniteNodeBResponse
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [cavityFiniteBinaryGenerator_eq_future_squares D s j J (Finset.mem_range.mp hj).le H K hK]
    congr 1
    dsimp [Q]
    rw [show k+2-(j+1)=k+1-j by omega]
  rw [hresp,weighted_cell_telescope]
  have hs:=scalarScheme_stieltjes_boundary s J hJ
    (fun q=>((q:ℝ)-s.q (k+2-J))*cavityFiniteFutureSquare D s J H K q)
  rw [scalarSchemeTransportNode_coe s _ (by omega)] at hs
  simp only [sub_self,zero_mul,mul_zero,zero_add] at hs
  have he : (∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
      ((scalarSchemeTransportNode s (k+1-r):ℝ)-s.q (k+2-J))*
        cavityFiniteFutureSquare D s J H K (scalarSchemeTransportNode s (k+1-r)))=
      -(∑p∈Finset.range J,(anisotropicSchemeMass s (p+1)-anisotropicSchemeMass s p)*
        (Q (p+1)-Q J)*F (p+1)) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [show k+1-p=k+2-(p+1) by omega,
      cavityFiniteFutureSquare_node D s J (p+1) hJ (by have:=Finset.mem_range.mp hp;omega),
      scalarSchemeTransportNode_coe s _ (by omega)]
    dsimp [Q,F,scalarSchemeMass,anisotropicSchemeMass]
    ring
  have hs' : -(∑p∈Finset.range J,(anisotropicSchemeMass s (p+1)-anisotropicSchemeMass s p)*
      (Q (p+1)-Q J)*F (p+1))=
      ∫q,if scalarSchemeTransportNode s (k+2-J)<q then
        ((q:ℝ)-s.q (k+2-J))*cavityFiniteFutureSquare D s J H K q else 0
        ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
    calc
      _ = _ := he.symm
      _ = _ := by simpa only [mul_assoc] using hs
  dsimp only [Q]
  rw [Nat.sub_zero,s.q_top]
  rw [←hs']
  ring


theorem cavityFiniteNodeBResponse_free_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (H K : FiniteStateField (Configuration n)) (hK : ∀σ,K σ*K σ=1) :
    cavityFiniteNodeBResponse D s J H K=
      (1/2 : ℝ)*(1-s.q (k+2-J)-
        ∫q,if scalarSchemeTransportNode s (k+2-J)<q then
          ((q:ℝ)-s.q (k+2-J))*cavityFiniteFutureSquare D s J H K q else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
  have he : (∫q,if scalarSchemeTransportNode s (k+2-J)<q then
      ((q:ℝ)-s.q (k+2-J))*cavityFiniteFutureSquare D s J H K q else 0
      ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∫q,if scalarSchemeTransportNode s (k+2-J)<q then
        ((q:ℝ)-s.q (k+2-J))*cavityFiniteFutureSquare D s J H K q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
    rw [←vectorProfile_free_root_decomposition s a ha has hq,
      integral_add_measure (by apply (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
        (integrable_vectorProfileFreeMeasure s a _)]
    rw [integral_smul_measure,integral_dirac]
    have hz : ¬scalarSchemeTransportNode s (k+2-J)<zeroOverlap :=
      not_lt_of_ge (scalarSchemeTransportNode s _).property.1
    rw [if_neg hz,smul_zero,zero_add,vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
  rw [cavityFiniteNodeBResponse_stieltjes D s J hJ H K hK,he]

end QuantitativeFollowup
