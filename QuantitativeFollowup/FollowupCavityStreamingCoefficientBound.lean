module
public import QuantitativeFollowup.FollowupCavityMarkedCovariance
public import FourPapersCommon.FiniteCascadeVertexWeights

@[expose] public section

/-! The actual nonnegative vertex weights and free-measure masses give
the source coefficient bound. The original-leaf count is bounded by its
square; each of the other five coefficients retains its literal weight. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
variable {k:ℕ}

def cavityStreamingCoefficientEnvelope (s:RSBScheme k) (a:ℝ)
    (T:FiniteTerminalGenealogy (k+2)) : ℝ:=
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:ℝ:=(cs.map Prod.fst).sum
  L^2+2*L*W+W^2+
    (cs.map (fun c=>c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2))).sum+
    (cs.map (fun c=>c.1*(∫q:Paper.Overlap,if anisotropicVertexOverlap s c.2<q then (1:ℝ) else 0
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum+
    a*(parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ

theorem anisotropicTrimmedVertexCharges_nonneg (s:RSBScheme k) (a:ℝ) (has:a ≤ s.m 1)
    (T:FiniteTerminalGenealogy (k+2)) :
    ∀c∈finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T),0≤c.1 := by
  apply finiteCascadeVertexCharges_nonneg (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_antitone s)
    (anisotropicSchemeMass_le_one s 0) a (trimRoot T)
  have hc:=finiteCascadeTreeRootCoefficient_previous_ge (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (trimRoot T) (by omega)
  have hm:anisotropicSchemeMass s (k+2-1-1)=s.m 1:=by
    simp only [anisotropicSchemeMass]
    congr 1
    omega
  rw [hm] at hc
  exact has.trans hc

theorem cavityStreamingCoefficientEnvelope_nonneg_le (s:RSBScheme k) (a:ℝ)
    (ha:a∈Icc (0:ℝ) 1) (has:a ≤ s.m 1) (T:FiniteTerminalGenealogy (k+2)) :
    0≤cavityStreamingCoefficientEnvelope s a T ∧
      cavityStreamingCoefficientEnvelope s a T≤
        4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
          2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1 := by
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:ℝ:=(cs.map Prod.fst).sum
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  have hL:0≤L:=Nat.cast_nonneg _
  have ha0:0≤a:=ha.1
  have ha1:a≤1:=ha.2
  have hc:∀c∈cs,0≤c.1:=anisotropicTrimmedVertexCharges_nonneg s a has T
  have hW:W=L-a:=by
    dsimp only [W,cs,L]
    rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hW0:0≤W:=List.sum_nonneg (by
    intro x hx
    obtain ⟨c,hc',rfl⟩:=List.mem_map.mp hx
    exact hc c hc')
  have hWL:W≤L:=by linarith
  have hmass:ν.real univ=1-a:=by
    dsimp only [ν,Measure.real]
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  have hm0:0≤ν.real univ:=by rw [hmass];linarith
  have hm1:ν.real univ≤1:=by rw [hmass];linarith
  have ht (v:FiniteCascadeRecordVertex (trimRoot T)) :
      0≤(∫q:Paper.Overlap,if anisotropicVertexOverlap s v<q then (1:ℝ) else 0∂ν) ∧
      (∫q:Paper.Overlap,if anisotropicVertexOverlap s v<q then (1:ℝ) else 0∂ν)≤1 := by
    constructor
    · exact integral_nonneg (fun q=>by split <;> norm_num)
    · apply (le_abs_self _).trans
      have hb:=norm_integral_le_of_norm_le_const (μ:=ν) (C:=1)
        (f:=fun q:Paper.Overlap=>if anisotropicVertexOverlap s v<q then (1:ℝ) else 0)
        (.of_forall fun q=>by split <;> norm_num)
      simpa only [Real.norm_eq_abs,one_mul] using hb.trans (by simpa only [one_mul] using hm1)
  have hcurr0:0≤(cs.map (fun c=>c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
      (anisotropicVertexOverlap s c.2))).sum:=List.sum_nonneg (by
    intro x hx
    obtain ⟨c,hc',rfl⟩:=List.mem_map.mp hx
    exact mul_nonneg (hc c hc') (Paper.parisiCDF_nonneg _ _))
  have hcurr:(cs.map (fun c=>c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
      (anisotropicVertexOverlap s c.2))).sum≤W:=by
    apply List.sum_le_sum
    intro c hcc
    exact (mul_le_mul_of_nonneg_left (Paper.parisiCDF_le_one _ _) (hc c hcc)).trans_eq (mul_one _)
  have hfuture0:0≤(cs.map (fun c=>c.1*(∫q:Paper.Overlap,
      if anisotropicVertexOverlap s c.2<q then (1:ℝ) else 0∂ν))).sum:=List.sum_nonneg (by
    intro x hx
    obtain ⟨c,hc',rfl⟩:=List.mem_map.mp hx
    exact mul_nonneg (hc c hc') (ht c.2).1)
  have hfuture:(cs.map (fun c=>c.1*(∫q:Paper.Overlap,
      if anisotropicVertexOverlap s c.2<q then (1:ℝ) else 0∂ν))).sum≤W:=by
    apply List.sum_le_sum
    intro c hcc
    exact (mul_le_mul_of_nonneg_left (ht c.2).2 (hc c hcc)).trans_eq (mul_one _)
  change 0≤L^2+2*L*W+W^2+_+_+a*ν.real univ ∧
    L^2+2*L*W+W^2+_+_+a*ν.real univ≤4*L^2+2*L+1
  constructor
  · positivity
  · have hLW:2*L*W≤2*L^2:=by nlinarith [mul_le_mul_of_nonneg_left hWL hL]
    have hWW:W^2≤L^2:=(sq_le_sq₀ hW0 hL).mpr hWL
    have hroot:a*ν.real univ≤1:=by nlinarith
    nlinarith

end QuantitativeFollowup
