module
public import QuantitativeFollowup.AnisotropicPosteriorLemma
public import QuantitativePaper.GOECompletionLaw
public import QuantitativePaper.GOEFeatureCovariance
public import QuantitativePaper.VectorInterpolationNoise

@[expose] public section

/-! The printed isotropic SK interpolation as a concrete instance of the
independent upper-triangular anisotropic Gaussian model. Its independent
diagonal variables are compressed to the genuine common completion noise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1200000
variable {n : ℕ}

def standardSKAnisotropicModel (n : ℕ) (β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) :
    AnisotropicSpinModel n where
  variance _ := (1-t)*β^2
  variance_pos _ := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  coupling e := if e.1.1=e.1.2 then β*Real.sqrt t*(Real.sqrt (2/(n:ℝ))/2)
    else β*Real.sqrt t/Real.sqrt (n:ℝ)

def standardSKCouplingEquiv (n : ℕ) : AnisotropicCouplingIndex n ≃ Edge n ⊕ Fin n where
  toFun e := if h : e.1.1<e.1.2 then Sum.inl ⟨e.1,h⟩ else Sum.inr e.1.1
  invFun e := match e with
    | .inl e => ⟨e.1,e.2.le⟩
    | .inr i => ⟨(i,i),le_rfl⟩
  left_inv e := by
    by_cases h : e.1.1<e.1.2
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      apply Subtype.ext
      have he : e.1.1=e.1.2 := le_antisymm e.2 (not_lt.mp h)
      exact Prod.ext rfl he
  right_inv e := by
    cases e with
    | inl e => simp only [dif_pos e.2]
    | inr i => simp

def standardSKRawDisorder (ω : AnisotropicDisorder n) : Couplings n × (Fin n→ℝ) :=
  (fun e=>ω ⟨e.1,e.2.le⟩,fun i=>ω ⟨(i,i),le_rfl⟩)

theorem measurable_standardSKRawDisorder : Measurable (standardSKRawDisorder (n:=n)) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval fun e=>(EuclideanSpace.proj ⟨e.1,e.2.le⟩ : AnisotropicDisorder n→L[ℝ]ℝ).measurable
  · exact Measurable.of_eval fun i=>(EuclideanSpace.proj ⟨(i,i),le_rfl⟩ : AnisotropicDisorder n→L[ℝ]ℝ).measurable

theorem anisotropicDisorderLaw_standardSKRawDisorder (n : ℕ) :
    (anisotropicDisorderLaw n).map standardSKRawDisorder=goeRawLaw n := by
  let e:=standardSKCouplingEquiv n
  let R:=MeasurableEquiv.piCongrLeft (fun _ : Edge n ⊕ Fin n=>ℝ) e
  let S:=MeasurableEquiv.sumPiEquivProdPi (fun _ : Edge n ⊕ Fin n=>ℝ)
  have he : standardSKRawDisorder (n:=n)=S ∘ R ∘ WithLp.ofLp := by
    funext ω
    apply Prod.ext
    · funext i
      have h:=MeasurableEquiv.piCongrLeft_apply_apply e (β:=fun _=>ℝ) ω.ofLp ⟨i.1,i.2.le⟩
      have hi : e ⟨i.1,i.2.le⟩=Sum.inl i := by simp [e,standardSKCouplingEquiv,i.2]
      rw [hi] at h
      exact h.symm
    · funext i
      have h:=MeasurableEquiv.piCongrLeft_apply_apply e (β:=fun _=>ℝ) ω.ofLp ⟨(i,i),le_rfl⟩
      have hi : e ⟨(i,i),le_rfl⟩=Sum.inr i := by simp [e,standardSKCouplingEquiv]
      rw [hi] at h
      exact h.symm
  rw [anisotropicDisorderLaw,he,←Measure.map_map S.measurable
    (R.measurable.comp (WithLp.measurable_ofLp 2 _)),←Measure.map_map R.measurable
    (WithLp.measurable_ofLp 2 _),stdGaussian_map_ofLp]
  rw [show (Measure.pi (fun _ : AnisotropicCouplingIndex n=>gaussianReal 0 1)).map R=
      Measure.pi (fun _ : Edge n ⊕ Fin n=>gaussianReal 0 1) from
    Measure.pi_map_piCongrLeft e (fun _=>gaussianReal 0 1)]
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Edge n ⊕ Fin n=>gaussianReal 0 1)).map_eq

def standardSKDisorderCompression (ω : AnisotropicDisorder n) : Couplings n × ℝ :=
  goeCompression n (standardSKRawDisorder ω)

theorem measurable_standardSKDisorderCompression : Measurable (standardSKDisorderCompression (n:=n)) :=
  (measurable_goeCompression n).comp measurable_standardSKRawDisorder

theorem anisotropicDisorderLaw_standardSKDisorderCompression (n : ℕ) (hn : 0<n) :
    (anisotropicDisorderLaw n).map standardSKDisorderCompression=completionLaw n := by
  change (anisotropicDisorderLaw n).map (goeCompression n ∘ standardSKRawDisorder)=_
  rw [←Measure.map_map (measurable_goeCompression n)
    measurable_standardSKRawDisorder,anisotropicDisorderLaw_standardSKRawDisorder,
    goeRawLaw_compression n hn]

theorem standardSKAnisotropicHamiltonian (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (ω : AnisotropicDisorder n) (x : Field n) (σ : Configuration n) :
    anisotropicHamiltonian (standardSKAnisotropicModel n β t hβ ht) ω x σ=
      vectorTerminalExponent n β t (standardSKDisorderCompression ω) x σ := by
  classical
  have hs : (∑e : AnisotropicCouplingIndex n,
      (standardSKAnisotropicModel n β t hβ ht).coupling e*ω e*
        Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))=
      (∑e : Edge n,β*Real.sqrt t/Real.sqrt (n:ℝ)*ω ⟨e.1,e.2.le⟩*
        Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))+
      ∑i : Fin n,β*Real.sqrt t*(Real.sqrt (2/(n:ℝ))/2)*ω ⟨(i,i),le_rfl⟩ := by
    rw [←(standardSKCouplingEquiv n).symm.sum_comp,Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro e _
      simp only [standardSKCouplingEquiv,Equiv.coe_fn_symm_mk,standardSKAnisotropicModel,
        ne_of_lt e.2,ite_false]
    · apply Finset.sum_congr rfl
      intro i _
      simp only [standardSKCouplingEquiv,Equiv.coe_fn_symm_mk,standardSKAnisotropicModel,
        ite_true]
      calc
        _=(β*Real.sqrt t*(Real.sqrt (2/(n:ℝ))/2)*ω ⟨(i,i),le_rfl⟩)*
            (Paper.spinSign (σ i))^2 := by ring
        _=_ := by rw [Paper.spinSign_sq,mul_one]
  rw [anisotropicHamiltonian,hs]
  simp only [vectorTerminalExponent,standardSKDisorderCompression,goeCompression,
    goeDiagonalTrace_eq,standardSKRawDisorder,energy,Paper.skHamiltonian,zero_mul,add_zero]
  simp only [mul_add,Finset.mul_sum]
  congr 1
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro e _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

end QuantitativeFollowup
