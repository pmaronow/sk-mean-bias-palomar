module
public import QuantitativeFollowup.FollowupCavityMixtureUniformLogJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterIntegralJets

@[expose] public section

/-! A common normalized-mean jet bound for every Gaussian input map.
Both the root tilt and the retained posterior normalization are included. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff Topology
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityOuterPosteriorMean_uniform_jet_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (s : ℝ) (N r : ℕ) (G : ℕ→ℝ) (hG : ∀i,0≤G i) :
    ∃B : ℝ,0≤B ∧ ∀(L : ℕ→Field n→L[ℝ]FiniteStateField S)
      (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
      (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
      (W : (Fin N→Field n)→L[ℝ]FiniteStateField S),
      (∀i,i≤r → ∀H,‖iteratedFDeriv ℝ i f H‖≤G i) →
      ∀H,‖iteratedFDeriv ℝ r (cavityOuterPosteriorMean V a L s N R f W) H‖≤B :=by
  obtain ⟨K,hK,hKB⟩:=cavityOuterPosteriorLogDensity_uniform_positive_jets
    (n:=n) (J:=J) V a ha ha1 hdec s N r
  let B:=gaussianWeightedJetCoefficient 1 K G r
  have hB:0≤B:=gaussianWeightedJetCoefficient_nonneg 1 K (zero_le_one.trans hK) G hG r
  refine ⟨B,hB,?_⟩
  intro L R f hf W hfb H
  obtain ⟨hi,he⟩:=cavityOuterPosteriorMean_iteratedFDeriv_integral V a ha ha1 hdec L s N r R f hf W H
  rw [he]
  have hh:=norm_integral_le_of_norm_le
    ((integrable_cavityOuterPosterior_exp V a ha L s N R H).const_mul B)
    (f:=fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r (fun Q=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q p) •
        f (Q+R p.1+W p.2.1)) H)
    (.of_forall fun p=>by
      let D:=fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p
      let F:=fun Q=>f (Q+R p.1+W p.2.1)
      have hD:ContDiff ℝ ∞ D:=
        (contDiff_cavityOuterPosteriorLogDensity_joint V a ha L s N R p.2.2).comp
          (contDiff_id.prodMk (contDiff_const (c:=(p.1,p.2.1))))
      have hF:ContDiff ℝ ∞ F:=hf.1.comp ((contDiff_id.add contDiff_const).add contDiff_const)
      have hFj(i)(hir:i≤r)(Q):‖iteratedFDeriv ℝ i F Q‖≤G i:=by
        have hshift:F=(fun Q=>f (Q+(R p.1+W p.2.1))):=by funext Q;dsimp only [F];rw [add_assoc]
        rw [hshift,iteratedFDeriv_comp_add_right]
        exact hfb i hir _
      have hb:=norm_iteratedFDeriv_exp_mul_observable_le D F
        (hD.of_le (by simp)) (hF.of_le (by simp)) 1 K (zero_le_one.trans hK) G hG
        (fun i hi hir Q=>hKB L R i hi hir Q p) hFj le_rfl H
      simpa only [D,F,B,one_mul,smul_eq_mul] using hb)
  rw [integral_const_mul,integral_cavityOuterPosterior_exp V a ha L s N R H,mul_one] at hh
  exact hh

end QuantitativeFollowup
