module
public import QuantitativeFollowup.FollowupCavityMixtureLinearSpatial
public import QuantitativeFollowup.FollowupCavityMixtureMovingHeat
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Honest compact-band spatial jets package into the exact moving heat
interface. The parameter is never differentiated. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000
variable {n : ℕ}

def cavityMovingHeatData_of_compact_spatial_family
    (F : ℝ×Field n→ℝ) (l r : ℝ) (hlr : l≤r)
    (hF : CavityJointSpatialTwoJets (fun z:Icc l r×Field n=>F (z.1,z.2)))
    (B K : ℝ) (hB : 0≤B) (hK : 0≤K)
    (hb : ∀b:Icc l r,∀i,i≤2 → ∀y,
      ‖iteratedFDeriv ℝ i (fun x=>F (b,x)) y‖≤B*Real.exp (K*‖y‖)) :
    CavityMovingRowHeatData F l r :=by
  let C:=fun z:ℝ×Field n=>(projIcc l r hlr z.1,z.2)
  have hc:Continuous C:=(continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  have hv:Continuous (fun z:ℝ×Field n=>F (projIcc l r hlr z.1,z.2)):=hF.value.comp hc
  have hh:Continuous (fun z:ℝ×Field n=>fderiv ℝ (fderiv ℝ
    (fun x=>F (projIcc l r hlr z.1,x))) z.2):=hF.second.comp hc
  refine ⟨?_,?_,?_,B,K,hB,hK,?_,?_,?_⟩
  · intro b hb
    exact (hF.smooth ⟨b,⟨hb.1.le,hb.2.le⟩⟩).of_le (by simp)
  · apply hv.continuousOn.congr
    intro z hz
    dsimp only
    rw [projIcc_of_mem hlr ⟨hz.1.1.le,hz.1.2.le⟩]
  · apply hh.continuousOn.congr
    intro z hz
    dsimp only
    rw [projIcc_of_mem hlr ⟨hz.1.1.le,hz.1.2.le⟩]
  · intro b hbb y
    simpa only [norm_iteratedFDeriv_zero] using hb ⟨b,⟨hbb.1.le,hbb.2.le⟩⟩ 0 (by omega) y
  · intro b hbb y
    simpa only [norm_iteratedFDeriv_one] using hb ⟨b,⟨hbb.1.le,hbb.2.le⟩⟩ 1 (by omega) y
  · intro b hbb y
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact hb ⟨b,⟨hbb.1.le,hbb.2.le⟩⟩ 2 le_rfl y

theorem exists_cavityMovingHeatData_comp_linear
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℝ×E→ℝ) (l r : ℝ) (hlr : l≤r)
    (hF : CavityJointSpatialTwoJets (fun z:Icc l r×E=>F (z.1,z.2)))
    (A : Field n→L[ℝ]E) (B K : ℝ) (hB : 0≤B) (hK : 0≤K)
    (hb : ∀b:Icc l r,∀i,i≤2 → ∀y,
      ‖iteratedFDeriv ℝ i (fun x=>F (b,x)) y‖≤B*Real.exp (K*‖y‖)) :
    Nonempty (CavityMovingRowHeatData (fun z:ℝ×Field n=>F (z.1,A z.2)) l r) :=by
  let J:ℝ:=1+‖A‖+‖A‖^2
  have hJ:0≤J:=by dsimp only [J];positivity
  refine ⟨cavityMovingHeatData_of_compact_spatial_family _ l r hlr
    (hF.comp_linear A) (B*J) (K*‖A‖) (mul_nonneg hB hJ)
    (mul_nonneg hK (norm_nonneg _)) ?_⟩
  intro b i hi y
  have hj:‖A‖^i≤J:=by
    interval_cases i <;> simp only [pow_zero,pow_one,J] <;> nlinarith [norm_nonneg A,sq_nonneg ‖A‖]
  have he:Real.exp (K*‖A y‖)≤Real.exp ((K*‖A‖)*‖y‖):=by
    apply Real.exp_le_exp.mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (A.le_opNorm y) hK
  apply (norm_cavitySpatialJet_comp_linear (hF.smooth b) A i y).trans
  have h1:=mul_le_mul_of_nonneg_right (hb b i hi (A y)) (pow_nonneg (norm_nonneg A) i)
  have h2:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB)
    (pow_nonneg (norm_nonneg A) i)
  have h3:=mul_le_mul_of_nonneg_left hj
    (mul_nonneg hB (Real.exp_pos ((K*‖A‖)*‖y‖)).le)
  exact h1.trans (h2.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using h3))

end QuantitativeFollowup
