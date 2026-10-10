module
public import HexagonPaper.CavityFixedRowJetMeasurable

@[expose] public section

/-! Sectionwise parameter continuity and record measurability suffice for
actual measurable parameter jets and their Bochner integration. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped Topology ContDiff
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
variable {A F : Type} [MeasurableSpace A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] {n : ℕ}

local instance instCavitySectionsJetMeasurable (r : ℕ) :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin r=>Field n) F) := borel _
local instance instCavitySectionsJetBorel (r : ℕ) :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin r=>Field n) F) := ⟨rfl⟩
local instance instCavitySectionsJetSecondCountable (r : ℕ) :
    SecondCountableTopology (ContinuousMultilinearMap ℝ (fun _ : Fin r=>Field n) F) :=
  instCavityJetMultilinearSecondCountable (n:=n) (F:=F) r

theorem measurable_cavityFiniteFunctional_sections (f : A×Field n→F)
    (hf : ∀ θ,Measurable (fun a=>f (a,θ)))
    (hc : ∀ a,Continuous (fun θ=>f (a,θ))) : Measurable f := by
  have hm := measurable_uncurry_of_continuous_of_measurable
    (u:=fun θ a=>f (a,θ)) hc hf
  exact hm.comp measurable_swap

theorem measurable_cavityFiniteIteratedFDeriv_sections (f : A×Field n→F)
    (hf : ∀ θ,Measurable (fun a=>f (a,θ)))
    (hs : ∀ a,ContDiff ℝ ∞ (fun θ=>f (a,θ))) (r : ℕ) :
    Measurable (fun u : A×Field n=>iteratedFDeriv ℝ r (fun θ=>f (u.1,θ)) u.2) :=
  measurable_cavityFiniteIteratedFDeriv f
    (measurable_cavityFiniteFunctional_sections f hf (fun a=>(hs a).continuous)) hs r

theorem aestronglyMeasurable_cavityFiniteIteratedFDeriv_sections
    (f : A×Field n→F) (hf : ∀ θ,Measurable (fun a=>f (a,θ)))
    (hs : ∀ a,ContDiff ℝ ∞ (fun θ=>f (a,θ))) (r : ℕ)
    (θ : Field n) (ν : Measure A) :
    AEStronglyMeasurable (fun a=>iteratedFDeriv ℝ r (fun p=>f (a,p)) θ) ν :=
  ((measurable_cavityFiniteIteratedFDeriv_sections f hf hs r).comp
    (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable

end HexagonPaper
