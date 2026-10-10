module
public import QuantitativeFollowup.FollowupCavityRootCharges
public import FourPapersCommon.FiniteCascadeCrossVertexMarks
public import FourPapersCommon.FiniteCascadeVertexCharges

@[expose] public section

/-! Physical conditional terminal marks at two arbitrary retained cavity
vertices. They use genuine independent normalized future cascades and
delete back to the unchanged physical recorded law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def anisotropicVertexMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n))
    (z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :=
  fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) v.depth)
      (v.field z.1 z.2) K

def anisotropicCrossVertexMarkedLaw (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) :=
  finiteCascadeCrossVertexMarkedLaw (fun _ : Configuration n => 0) (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) v w
      (anisotropicTrimmedRecordedTreeLaw D s a T)

instance anisotropicCrossVertexMarkedLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) :
    IsProbabilityMeasure (anisotropicCrossVertexMarkedLaw D s a T v w) :=
  finiteCascadeCrossVertexMarkedLaw_probability _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _

theorem anisotropicCrossVertexMarkedLaw_fst (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) :
    (anisotropicCrossVertexMarkedLaw D s a T v w).fst =
      anisotropicTrimmedRecordedTreeLaw D s a T :=
  finiteCascadeCrossVertexMarkedLaw_fst _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _

theorem integral_anisotropicCrossVertexMarkedLaw_product (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C)
    (K M : FiniteStateField (Configuration n)) :
    (∫z,F z.1*K z.2.1*M z.2.2 ∂anisotropicCrossVertexMarkedLaw D s a T v w) =
      ∫z,F z*anisotropicVertexMean D s v K z*anisotropicVertexMean D s w M z
        ∂anisotropicTrimmedRecordedTreeLaw D s a T :=
  integral_finiteCascadeCrossVertexMarkedLaw_product _ _ (anisotropicSchemeMass_nonneg s)
    _ _ _ _ F hF C hC hFb K M

end QuantitativeFollowup
