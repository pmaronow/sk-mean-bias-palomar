module
public import FourPapersCommon.FiniteStateCascadePosteriorJets

@[expose] public section

/-! Genuine positive-order spatial jet bounds independent of cascade depth.
The induction differentiates the actual normalized Gaussian posterior and
uses its telescoping nonnegative mass coefficients. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators NNReal ContDiff
namespace FourPapersCommon
open QuantitativePaper OverlapPaper SpinGlass.AT
variable {S:Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n:ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem exists_uniform_finiteStateCascade_jet_bound (S:Type) [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (n r:ℕ) (hr:1 ≤ r):
    ∃C:ℝ,0 ≤ C ∧ ∀(V:S→ℝ)(a:ℕ→ℝ)(ha:∀i,0 ≤ a i)(ha1:a 0 ≤ 1)
      (hdec:Antitone a)(L:ℕ→Field n→L[ℝ]FiniteStateField S)(j:ℕ)(H:FiniteStateField S),
      ‖iteratedFDeriv ℝ r (finiteStateGaussianTerminalCascade V a L j) H‖ ≤ C := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases h1:r=1
    · subst r
      exact ⟨1,by norm_num,fun V a ha ha1 hdec L j H=>
        norm_finiteStateCascade_firstJet_le_one V a ha L j H⟩
    · have hr2:2 ≤ r:=by omega
      choose C hC0 hC using (fun i:Fin (r-1)=>ih (i+1) (by omega) (by omega))
      let K:ℝ:=3+∑i:Fin (r-1),C i
      have hsum:0 ≤ ∑i:Fin (r-1),C i:=Finset.sum_nonneg fun i _=>hC0 i
      have hK1:1 ≤ K:=by dsimp only [K];linarith
      refine ⟨((r-1).factorial:ℝ)*K^(r-1),by positivity,?_⟩
      intro V a ha ha1 hdec L j H
      have hB (i:ℕ)(hi:1 ≤ i)(hir:i ≤ r-1)(j:ℕ)(Q:FiniteStateField S)
          (z:(Fin j→Field n)×S):
          ‖iteratedFDeriv ℝ i (fun u=>cascadePosteriorLogDensity V a L j u z) Q‖ ≤ K^i:=by
        let b:Fin (r-1):=⟨i-1,by omega⟩
        have hb:(b:ℕ)+1=i:=by dsimp only [b];omega
        have hUi:∀j Q,‖iteratedFDeriv ℝ i (finiteStateGaussianTerminalCascade V a L j) Q‖ ≤ C b:=by
          intro j Q
          have hh:=hC b V a ha ha1 hdec L j Q
          rw [hb] at hh
          exact hh
        have hTi (w Q:FiniteStateField S)(σ:S):
            ‖iteratedFDeriv ℝ i (fun u=>V σ+(u+w) σ) Q‖ ≤ 1:=by
          by_cases hi1:i=1
          · rw [hi1]
            exact norm_cascadeTerminal_affine_firstJet_le_one V w Q σ
          · rw [cascadeTerminal_affine_higherJet_zero V w Q σ i (by omega),norm_zero]
            norm_num
        have hh:=norm_cascadePosteriorLogDensity_jet_le V a ha ha1 hdec L i 1 (C b)
          (hC0 b) hUi hTi j Q z
        have hCb:C b ≤ ∑i:Fin (r-1),C i:=Finset.single_le_sum (fun i _=>hC0 i) (Finset.mem_univ b)
        have hk:1+C b ≤ K:=by dsimp only [K];linarith
        exact hh.trans (hk.trans (le_self_pow₀ hK1 (by omega)))
      have hh:=norm_finiteStateCascade_jet_from_posterior V a ha ha1 hdec L (r-1) K
        (zero_le_one.trans hK1) hB j (r-1) le_rfl H
      have he:r-1+1=r:=by omega
      rw [he] at hh
      exact hh

def finiteStateSpatialJetBound (S:Type) [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (n r:ℕ):ℝ:=
  if hr:1 ≤ r then Classical.choose (exists_uniform_finiteStateCascade_jet_bound S n r hr) else 0

theorem finiteStateSpatialJetBound_nonneg (S:Type) [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (n r:ℕ):0 ≤ finiteStateSpatialJetBound S n r:=by
  unfold finiteStateSpatialJetBound
  split_ifs with hr
  · exact (Classical.choose_spec (exists_uniform_finiteStateCascade_jet_bound S n r hr)).1
  · rfl

theorem norm_finiteStateCascade_jet_le_uniform (V:S→ℝ)(a:ℕ→ℝ)
    (ha:∀i,0 ≤ a i)(ha1:a 0 ≤ 1)(hdec:Antitone a)
    (L:ℕ→Field n→L[ℝ]FiniteStateField S)(j r:ℕ)(hr:1 ≤ r)(H:FiniteStateField S):
    ‖iteratedFDeriv ℝ r (finiteStateGaussianTerminalCascade V a L j) H‖ ≤ 
      finiteStateSpatialJetBound S n r:=by
  unfold finiteStateSpatialJetBound
  rw [dif_pos hr]
  exact (Classical.choose_spec (exists_uniform_finiteStateCascade_jet_bound S n r hr)).2 V a ha ha1 hdec L j H

end FourPapersCommon
