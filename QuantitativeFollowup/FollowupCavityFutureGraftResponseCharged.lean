module
public import QuantitativeFollowup.FollowupCavityFutureGraftResponseStieltjes

@[expose] public section

/-! The complete charged strict-future branch of the physical streaming
law, with a genuine second closed streaming derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem response_hasDerivWithinAt_list_sum {I : Type}
    (xs : List I) (f : I→ℝ→ℝ) (f' : I→ℝ) (S : Set ℝ) (u : ℝ)
    (h : ∀i,HasDerivWithinAt (f i) (f' i) S u) :
    HasDerivWithinAt (fun y=>(xs.map (fun i=>f i y)).sum) (xs.map f').sum S u := by
  induction xs with
  | nil => simpa only [List.map_nil,List.sum_nil] using hasDerivWithinAt_const u S (0:ℝ)
  | cons i xs ih =>
      simpa only [List.map_cons,List.sum_cons,Pi.add_apply] using (h i).fun_add ih

def followupCavityFutureGraftStreamingExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) (u : ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*followupCavityFutureGraftStieltjesExpectation n β ρ hβ hρ s a T c.2 F u)).sum

def followupCavityFutureGraftStreamingResponse (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*followupCavityFutureGraftStieltjesResponse D s a T c.2 F)).sum

theorem followupCavityFutureGraftStreamingExpectation_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityFutureGraftStreamingExpectation n β ρ hβ hρ s a T F u=
      cavityFutureFreshExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (fun r=>F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)) := by
  classical
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let R:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>
    F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  have hR:=measurable_followupCavityPhysicalRecordObservable T (cavityFutureResponseSampleObservable T F)
  rw [cavityFutureResponseSampleObservable_record] at hR
  obtain ⟨C,hC,hRb⟩:=exists_followupCavityPhysicalRecordObservable_bound T (cavityFutureResponseSampleObservable T F)
  rw [cavityFutureResponseSampleObservable_record] at hRb
  unfold followupCavityFutureGraftStreamingExpectation cavityFutureFreshExpectation
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  rw [followupCavityFutureGraftStieltjesExpectation_eq_actual β ρ hβ hρ s a ha has hq T c.2 F u hu,
    integral_cavityRecorded_vertex_futureFresh D s a ha has hq T c.2 R hR C hC hRb]

theorem hasDerivWithinAt_followupCavityFutureGraftStreamingExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityFutureGraftStreamingExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2*followupCavityFutureGraftStreamingResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T F) (Icc (0:ℝ) 1) u := by
  classical
  unfold followupCavityFutureGraftStreamingExpectation followupCavityFutureGraftStreamingResponse
  rw [←List.sum_map_mul_left]
  have he (c : ℝ×FiniteCascadeRecordVertex (trimRoot T)) :
      followupCavityAlpha n β ρ/2*(c.1*followupCavityFutureGraftStieltjesResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T c.2 F)=
      c.1*(followupCavityAlpha n β ρ/2*followupCavityFutureGraftStieltjesResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T c.2 F) := by ring
  simp_rw [he]
  apply response_hasDerivWithinAt_list_sum
  intro c
  exact (hasDerivWithinAt_followupCavityFutureGraftStieltjesExpectation hn β ρ hβ hρ
    s a ha has hq T c.2 F u hu).const_mul c.1

end QuantitativeFollowup
