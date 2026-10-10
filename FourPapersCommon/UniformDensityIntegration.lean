module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

/-! Uniform expectations for bounded observables when normalized densities
converge in L¹ and the observables converge uniformly. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
variable {Ω Q : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem tendstoUniformly_integral_density_mul
    (Wj : ℕ → Ω → ℝ) (W : Ω → ℝ) (Fj : ℕ → Q → Ω → ℝ) (F : Q → Ω → ℝ)
    (hWj : ∀ j, Integrable (Wj j) P) (hW : Integrable W P)
    (hWn : ∀ j ω, 0 ≤ Wj j ω) (hmass : ∀ j, ∫ ω, Wj j ω ∂P = 1)
    (hL : Tendsto (fun j => ∫ ω, |Wj j ω-W ω| ∂P) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C) (hFj : ∀ j q, Measurable (Fj j q))
    (hF : ∀ q, Measurable (F q)) (hBj : ∀ j q ω, ‖Fj j q ω‖ ≤ C)
    (hB : ∀ q ω, ‖F q ω‖ ≤ C)
    (hU : TendstoUniformly (fun j (z : Q × Ω) => Fj j z.1 z.2)
      (fun z => F z.1 z.2) atTop) :
    TendstoUniformly (fun j q => ∫ ω, Wj j ω*Fj j q ω ∂P)
      (fun q => ∫ ω, W ω*F q ω ∂P) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let δ := ε/(2*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδb : δ+C*δ < ε := by
    dsimp [δ]
    field_simp
    nlinarith
  have hu := (Metric.tendstoUniformly_iff.mp hU) δ hδ
  have hl := hL.eventually (gt_mem_nhds hδ)
  filter_upwards [hu,hl] with j hj hLj
  intro q
  have hi := (hWj j).mul_bdd (hFj j q).aestronglyMeasurable (.of_forall fun ω => hBj j q ω)
  have hi' := hW.mul_bdd (hF q).aestronglyMeasurable (.of_forall fun ω => hB q ω)
  have hd : Integrable (fun ω => |Wj j ω-W ω|) P := by
    simpa only [Pi.sub_apply] using ((hWj j).sub hW).abs
  have hg : Integrable (fun ω => δ*Wj j ω+C*|Wj j ω-W ω|) P :=
    ((hWj j).const_mul δ).add (hd.const_mul C)
  have hb (ω : Ω) : ‖Wj j ω*Fj j q ω-W ω*F q ω‖ ≤ δ*Wj j ω+C*|Wj j ω-W ω| := by
    have he : Wj j ω*Fj j q ω-W ω*F q ω =
        Wj j ω*(Fj j q ω-F q ω)+(Wj j ω-W ω)*F q ω := by ring
    rw [he]
    calc
      _ ≤ ‖Wj j ω*(Fj j q ω-F q ω)‖+‖(Wj j ω-W ω)*F q ω‖ := norm_add_le _ _
      _ ≤ Wj j ω*δ+|Wj j ω-W ω| *C := by
        simp only [norm_mul,Real.norm_of_nonneg (hWn j ω),Real.norm_eq_abs]
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (hWn j ω)
          simpa only [Real.dist_eq,abs_sub_comm] using (hj (q,ω)).le
        · exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hB q ω) (abs_nonneg _)
      _ = _ := by ring
  rw [dist_eq_norm, norm_sub_rev, ← integral_sub hi hi']
  calc
    _ ≤ ∫ ω, ‖Wj j ω*Fj j q ω-W ω*F q ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, δ*Wj j ω+C*|Wj j ω-W ω| ∂P := integral_mono (hi.sub hi').norm hg hb
    _ = δ+C*(∫ ω, |Wj j ω-W ω| ∂P) := by
      rw [integral_add ((hWj j).const_mul δ) (hd.const_mul C),
        integral_const_mul,integral_const_mul,hmass j,mul_one]
    _ ≤ δ+C*δ := by gcongr
    _ < ε := hδb

end FourPapersCommon
