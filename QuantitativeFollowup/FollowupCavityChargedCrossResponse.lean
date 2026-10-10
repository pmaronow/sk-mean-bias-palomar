module
public import QuantitativeFollowup.FollowupCavityCrossGraftResponse
public import QuantitativeFollowup.FollowupCavityPairProductBounds

@[expose] public section

/-! The current-CDF and cross-vertex branches can be differentiated a
second time by their actual enlarged-tree laws. Every coefficient is
the genuine fixed-profile charge; zero and repeated cells are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_weighted_list {A : Type*} (cs : List (ℝ × A))
    (f : A → ℝ → ℝ) (df : A → ℝ) (S : Set ℝ) (u : ℝ)
    (hf : ∀c, HasDerivWithinAt (f c) (df c) S u) :
    HasDerivWithinAt (fun v => (cs.map (fun c => c.1*f c.2 v)).sum)
      (cs.map (fun c => c.1*df c.2)).sum S u := by
  induction cs with
  | nil => simpa only [List.map_nil,List.sum_nil] using (hasDerivWithinAt_const u S (0 : ℝ))
  | cons c cs ih =>
    convert! ((hf c.2).const_mul c.1).add ih using 1 <;>
      simp only [List.map_cons,List.sum_cons,Pi.add_apply]

def followupCavityCurrentGraftFamily (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c =>
    c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
      followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
        (cavityCrossGraftSampleObservable T c.2 c.2 (anisotropicVertexOverlap s c.2) F) u)).sum

def followupCavityCurrentGraftDerivative (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c =>
    c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft c.2 c.2))
          (cavityCrossGraftSampleObservable T c.2 c.2 (anisotropicVertexOverlap s c.2) F))))).sum

theorem followupCavityCurrentGraftFamily_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityCurrentGraftFamily n β ρ hβ hρ s a T F u=
      cavityCurrentFreshExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (fun r => F (spins (trimRoot T) r.2)) := by
  unfold followupCavityCurrentGraftFamily cavityCurrentFreshExpectation
  simp_rw [followupCavityCrossGraftExpectation_eq_marked β ρ hβ hρ s a hq T _ _ _ F u hu]

theorem hasDerivWithinAt_followupCavityCurrentGraftFamily
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityCurrentGraftFamily n β ρ hβ hρ s a T F)
      (followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu) (Icc (0 : ℝ) 1) u := by
  unfold followupCavityCurrentGraftFamily followupCavityCurrentGraftDerivative
  let cs := (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c => (c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2),c.2))
  have hh := hasDerivWithinAt_weighted_list cs
    (fun v => followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeCrossVertexGraft v v))
      (cavityCrossGraftSampleObservable T v v (anisotropicVertexOverlap s v) F))
    (fun v => followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeCrossVertexGraft v v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v v))
        (cavityCrossGraftSampleObservable T v v (anisotropicVertexOverlap s v) F))) (Icc (0 : ℝ) 1) u
    (fun v => hasDerivWithinAt_followupCavityCrossGraftExpectation hn β ρ hβ hρ s a ha has hq T v v _ F u hu)
  convert! hh using 1 <;> simp only [cs,List.map_map,Function.comp_def,
    followupCavityCurrentGraftFamily,followupCavityCurrentGraftDerivative]

def followupCavityCrossGraftFamily (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) : ℝ :=
  let cs := finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  (cs.map (fun c => c.1*(cs.map (fun d => d.1*
    followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeCrossVertexGraft c.2 d.2))
      (cavityCrossGraftSampleObservable T c.2 d.2 (cavityProfileLevel s
        (finiteCascadeCommonPathDepth (trimRoot T) c.2 d.2)) F) u)).sum)).sum

def followupCavityCrossGraftDerivative (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ℝ :=
  let cs := finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  (cs.map (fun c => c.1*(cs.map (fun d => d.1*
    (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeCrossVertexGraft c.2 d.2))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft c.2 d.2))
        (cavityCrossGraftSampleObservable T c.2 d.2 (cavityProfileLevel s
          (finiteCascadeCommonPathDepth (trimRoot T) c.2 d.2)) F))))).sum)).sum

theorem followupCavityCrossGraftFamily_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityCrossGraftFamily n β ρ hβ hρ s a T F u=
      cavityFreshFreshExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        (fun r => F (spins (trimRoot T) r.2)) := by
  unfold followupCavityCrossGraftFamily cavityFreshFreshExpectation
  simp_rw [followupCavityCrossGraftExpectation_eq_marked β ρ hβ hρ s a hq T _ _ _ F u hu,
    cavityPhysicalCommonOverlap_eq_profileLevel]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  ring

theorem hasDerivWithinAt_followupCavityCrossGraftFamily
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityCrossGraftFamily n β ρ hβ hρ s a T F)
      (followupCavityCrossGraftDerivative n β ρ hβ hρ s a T F u hu) (Icc (0 : ℝ) 1) u := by
  let cs := finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let f := fun v w y => followupCavityPhysicalExpectation n β ρ hβ hρ s a
    (.advance (finiteCascadeCrossVertexGraft v w))
    (cavityCrossGraftSampleObservable T v w (cavityProfileLevel s
      (finiteCascadeCommonPathDepth (trimRoot T) v w)) F) y
  let df := fun v w => followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a
    (.advance (finiteCascadeCrossVertexGraft v w))
    (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
      (cavityCrossGraftSampleObservable T v w (cavityProfileLevel s
        (finiteCascadeCommonPathDepth (trimRoot T) v w)) F))
  have hi (v) := hasDerivWithinAt_weighted_list cs (f v) (df v) (Icc (0 : ℝ) 1) u
    (fun w => hasDerivWithinAt_followupCavityCrossGraftExpectation hn β ρ hβ hρ s a ha has hq T v w _ F u hu)
  have hh := hasDerivWithinAt_weighted_list cs
    (fun v y => (cs.map (fun d => d.1*f v d.2 y)).sum)
    (fun v => (cs.map (fun d => d.1*df v d.2)).sum) (Icc (0 : ℝ) 1) u hi
  unfold followupCavityCrossGraftFamily followupCavityCrossGraftDerivative
  convert! hh using 1

end QuantitativeFollowup
