module
public import FourPapersCommon.MixedModel

@[expose] public section

/-! An actual quadratic admissible covariance, with its literal identity clock.
This allows scalar finite Gaussian cascades to use the same actual model APIs
as arbitrary mixtures, without changing their probability laws. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon
namespace AdmissibleEvenMixture

def quadratic (v : ℝ) (hv : 0<v) : AdmissibleEvenMixture where
  coefficient n := if n=2 then v/2 else 0
  nonneg n := by split_ifs <;> positivity
  active_even n hn := by
    have he : n=2 := by by_contra he; simp only [he,ite_false] at hn; exact hn rfl
    subst n
    exact ⟨le_rfl,by decide⟩
  nonzero := ⟨2,by simp only [ite_true]; linarith⟩
  summable := by
    have he : (fun n : ℕ=>(2 : ℝ)^n*(if n=2 then v/2 else 0))=
        fun n : ℕ=>if n=2 then (2 : ℝ)^2*(v/2) else 0 := by
      funext n
      split_ifs <;> simp_all
    rw [he]
    exact summable_of_ne_finset_zero (s := {2}) (by intro n hn; simp_all)

@[simp] theorem quadratic_value (v : ℝ) (hv : 0<v) (q : ℝ) :
    (quadratic v hv).value q=v/2*q^2 := by
  unfold value quadratic
  have he : (fun n : ℕ=>(if n=2 then v/2 else 0)*q^n)=
      fun n : ℕ=>if n=2 then v/2*q^2 else 0 := by
    funext n
    split_ifs <;> simp_all
  rw [he,tsum_ite_eq]

@[simp] theorem quadratic_first (v : ℝ) (hv : 0<v) (q : ℝ) :
    (quadratic v hv).first q=v*q := by
  unfold first quadratic
  have he : (fun n : ℕ=>(n : ℝ)*(if n=2 then v/2 else 0)*q^(n-1))=
      fun n : ℕ=>if n=2 then v*q else 0 := by
    funext n
    by_cases hn : n=2
    · subst n
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      simp only [ite_true]
      ring
    · simp only [hn,ite_false,mul_zero,zero_mul]
  rw [he,tsum_ite_eq]

@[simp] theorem quadratic_variance (v : ℝ) (hv : 0<v) :
    (quadratic v hv).variance=v := by simp [variance]

@[simp] theorem quadratic_clock (v : ℝ) (hv : 0<v) (q : ℝ) :
    (quadratic v hv).clock q=q := by simp [clock,hv.ne']

@[simp] theorem quadratic_unitClock (v : ℝ) (hv : 0<v) :
    (quadratic v hv).unitClock=id := by
  funext q
  apply Subtype.ext
  simp only [unitClock,quadratic_clock,id_eq]

end AdmissibleEvenMixture

@[simp] theorem mixedMeasure_quadratic (v : ℝ) (hv : 0<v) (μ : Paper.ParisiMeasure) :
    mixedMeasure (AdmissibleEvenMixture.quadratic v hv) μ=μ := by
  apply Subtype.ext
  change MeasureTheory.Measure.map _ (μ : MeasureTheory.Measure Paper.Overlap)=_
  rw [AdmissibleEvenMixture.quadratic_unitClock,MeasureTheory.Measure.map_id]
  rfl

@[simp] theorem mixedBeta_quadratic (v : ℝ) (hv : 0<v) :
    mixedBeta (AdmissibleEvenMixture.quadratic v hv)=Real.sqrt v := by
  simp [mixedBeta]

@[simp] theorem mixedPotential_quadratic (v : ℝ) (hv : 0<v) (μ : Paper.ParisiMeasure)
    (p : ℝ×ℝ) :
    mixedPotential (AdmissibleEvenMixture.quadratic v hv) μ p=Paper.parisiPotential (Real.sqrt v) μ p := by
  simp [mixedPotential]

@[simp] theorem mixedGradient_quadratic (v : ℝ) (hv : 0<v) (μ : Paper.ParisiMeasure)
    (p : ℝ×ℝ) :
    mixedGradient (AdmissibleEvenMixture.quadratic v hv) μ p=Paper.parisiGradient (Real.sqrt v) μ p := by
  simp [mixedGradient]

end FourPapersCommon
