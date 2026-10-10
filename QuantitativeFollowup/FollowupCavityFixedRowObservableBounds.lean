module
public import QuantitativeFollowup.FollowupCavityFixedRowDefinitions

@[expose] public section

/-! The fixed-row retained-node tests are actual finite energy responses.
Their bounded smooth field factories supply the outer Gaussian numerator
calculus, with no posterior observable bound assumed. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000

def cavityFixedRowLastFieldSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (H : FiniteStateField (Configuration (n+1))) : ℝ :=
  (cavityFiniteEnergyFeatureMean (fun _=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) d
    (WithLp.toLp 2 (fun sigma : Configuration (n+1)=>Paper.spinSign (sigma (Fin.last n)))) H)^2

def cavityFixedRowRestFieldSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (H : FiniteStateField (Configuration (n+1))) : ℝ :=
  cavityFiniteEnergyRestOverlap (fun _=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) d
    (fun i : Fin n=>WithLp.toLp 2 (fun sigma : Configuration (n+1)=>Paper.spinSign (sigma i.castSucc))) H

theorem boundedJets_cavityFixedRowLastFieldSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) : BoundedJets (cavityFixedRowLastFieldSquare D s d) := by
  have hf:=boundedJets_cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) d
    (WithLp.toLp 2 (fun sigma : Configuration (n+1)=>Paper.spinSign (sigma (Fin.last n))))
  change BoundedJets (fun H=>(cavityFiniteEnergyFeatureMean
    (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d
    (WithLp.toLp 2 (fun sigma : Configuration (n+1)=>Paper.spinSign (sigma (Fin.last n)))) H)^2)
  simpa only [pow_two] using hf.mul hf

theorem boundedJets_cavityFixedRowRestFieldSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) : BoundedJets (cavityFixedRowRestFieldSquare D s d) :=
  boundedJets_cavityFiniteEnergyRestOverlap _ _ (anisotropicSchemeMass_nonneg s) _ _ _

theorem boundedJets_cavityFixedRowProductFieldSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) :
    BoundedJets (fun H=>cavityFixedRowLastFieldSquare D s d H*cavityFixedRowRestFieldSquare D s d H) :=
  (boundedJets_cavityFixedRowLastFieldSquare D s d).mul
    (boundedJets_cavityFixedRowRestFieldSquare D s d)

theorem cavityFixedRowLastSquare_eq_field (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (z) :
    cavityFixedRowLastSquare D s d z=
      cavityFixedRowLastFieldSquare D s d (cavityFixedRowLineField (k+2) d z.1 z.2) := rfl

theorem cavityFixedRowRestSquare_eq_field (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (z) :
    cavityFixedRowRestSquare D s d z=
      cavityFixedRowRestFieldSquare D s d (cavityFixedRowLineField (k+2) d z.1 z.2) := rfl

theorem exists_cavityFixedRowObservable_bounds (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) :
    ∃B : ℝ,0≤B ∧ ∀z,‖cavityFixedRowLastSquare D s d z‖≤B ∧
      ‖cavityFixedRowRestSquare D s d z‖≤B ∧
      ‖cavityFixedRowLastSquare D s d z*cavityFixedRowRestSquare D s d z‖≤B := by
  obtain ⟨Cf,hCf,hf⟩:=(boundedJets_cavityFixedRowLastFieldSquare D s d).2 0
  obtain ⟨Cg,hCg,hg⟩:=(boundedJets_cavityFixedRowRestFieldSquare D s d).2 0
  obtain ⟨Ch,hCh,hh⟩:=(boundedJets_cavityFixedRowProductFieldSquare D s d).2 0
  refine ⟨Cf+Cg+Ch,by positivity,?_⟩
  intro z
  have hfb:=hf (cavityFixedRowLineField (k+2) d z.1 z.2)
  have hgb:=hg (cavityFixedRowLineField (k+2) d z.1 z.2)
  have hhb:=hh (cavityFixedRowLineField (k+2) d z.1 z.2)
  simp only [norm_iteratedFDeriv_zero] at hfb hgb hhb
  rw [cavityFixedRowLastSquare_eq_field,cavityFixedRowRestSquare_eq_field]
  exact ⟨by linarith,by linarith,by linarith⟩

end QuantitativeFollowup
