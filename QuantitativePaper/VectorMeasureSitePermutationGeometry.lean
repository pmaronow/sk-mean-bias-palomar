module
public import QuantitativePaper.VectorSiteSymmetry
public import QuantitativePaper.VectorBrownian

@[expose] public section

/-! Actual site permutations of the triangular SK disorder and independent
Wiener coordinates. The unordered edge is put back in its increasing order. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1200000
variable {n : ℕ}

def orderedSiteEdge (i j : Fin n) (h : i ≠ j) : Edge n :=
  if hij : i < j then ⟨(i,j),hij⟩ else ⟨(j,i),lt_of_le_of_ne (not_lt.mp hij) h.symm⟩

theorem orderedSiteEdge_comm (i j : Fin n) (h : i ≠ j) :
    orderedSiteEdge j i h.symm = orderedSiteEdge i j h := by
  unfold orderedSiteEdge
  split_ifs with hij hji <;> apply Subtype.ext <;> simp_all <;> omega

def siteEdgeMap (π : Equiv.Perm (Fin n)) (e : Edge n) : Edge n :=
  orderedSiteEdge (π e.1.1) (π e.1.2) (π.injective.ne (ne_of_lt e.2))

theorem siteEdgeMap_inverse (π : Equiv.Perm (Fin n)) (e : Edge n) :
    siteEdgeMap π.symm (siteEdgeMap π e) = e := by
  unfold siteEdgeMap
  by_cases h : π e.1.1 < π e.1.2
  · simp only [orderedSiteEdge,dif_pos h,Equiv.symm_apply_apply]
    rw [dif_pos e.2]
  · simp only [orderedSiteEdge,dif_neg h,Equiv.symm_apply_apply]
    rw [dif_neg (not_lt_of_ge e.2.le)]

def siteEdgePermutation (π : Equiv.Perm (Fin n)) : Edge n ≃ Edge n where
  toFun := siteEdgeMap π
  invFun := siteEdgeMap π.symm
  left_inv := siteEdgeMap_inverse π
  right_inv := by intro e; exact siteEdgeMap_inverse π.symm e

def siteFieldPermutation (π : Equiv.Perm (Fin n)) : Field n ≃ₗᵢ[ℝ] Field n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ π.symm

@[simp] theorem siteFieldPermutation_apply (π : Equiv.Perm (Fin n))
    (x : Field n) (i : Fin n) : siteFieldPermutation π x i = x (π i) := rfl

def siteSpinPermutation (π : Equiv.Perm (Fin n)) : Configuration n ≃ Configuration n :=
  Equiv.piCongrLeft' (fun _ : Fin n => Bool) π.symm

@[simp] theorem siteSpinPermutation_apply (π : Equiv.Perm (Fin n))
    (σ : Configuration n) (i : Fin n) : siteSpinPermutation π σ i = σ (π i) := rfl

def siteDisorderPermutation (π : Equiv.Perm (Fin n)) :
    (Couplings n × ℝ) ≃ᵐ (Couplings n × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Edge n => ℝ)
    (siteEdgePermutation π).symm).prodCongr (MeasurableEquiv.refl ℝ)

@[simp] theorem siteDisorderPermutation_apply (π : Equiv.Perm (Fin n))
    (p : Couplings n × ℝ) :
    siteDisorderPermutation π p = (fun e => p.1 (siteEdgeMap π e),p.2) := by
  apply Prod.ext
  · funext e
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (siteEdgePermutation π).symm (β:=fun _ => ℝ) p.1 ((siteEdgePermutation π) e)
    change (MeasurableEquiv.piCongrLeft (fun _ : Edge n => ℝ)
      (siteEdgePermutation π).symm) p.1 e = p.1 ((siteEdgePermutation π) e)
    simpa only [Equiv.symm_apply_apply] using h
  · rfl

def siteBrownianPermutation (π : Equiv.Perm (Fin n)) :
    VectorBrownianSample n ≃ᵐ VectorBrownianSample n :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => Paper.BrownianSample) π.symm

def siteSamplePermutation (π : Equiv.Perm (Fin n)) :
    VectorDisorderBrownianSample n ≃ᵐ VectorDisorderBrownianSample n :=
  (siteDisorderPermutation π).prodCongr (siteBrownianPermutation π)

theorem measurePreserving_siteDisorderPermutation (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (siteDisorderPermutation π) (completionLaw n) (completionLaw n) := by
  have hp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Edge n => ℝ) (siteEdgePermutation π).symm)
      (couplingLaw n) (couplingLaw n) :=
    measurePreserving_piCongrLeft (fun _ : Edge n => gaussianReal 0 1)
      (siteEdgePermutation π).symm
  exact hp.prod (MeasurePreserving.id _)

theorem measurePreserving_siteBrownianPermutation (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (siteBrownianPermutation π)
      (vectorBrownianMeasure n) (vectorBrownianMeasure n) :=
  measurePreserving_piCongrLeft (fun _ : Fin n => Paper.canonicalBrownianMeasure) π.symm

theorem measurePreserving_siteSamplePermutation (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (siteSamplePermutation π)
      (vectorDisorderBrownianMeasure n) (vectorDisorderBrownianMeasure n) :=
  (measurePreserving_siteDisorderPermutation π).prod
    (measurePreserving_siteBrownianPermutation π)

@[simp] theorem disorderVectorBrownian_site_permutation (π : Equiv.Perm (Fin n))
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    disorderVectorBrownian r (siteSamplePermutation π sample) =
      siteFieldPermutation π (disorderVectorBrownian r sample) := by
  ext i
  simp [disorderVectorBrownian,vectorBrownian,siteSamplePermutation,
    siteBrownianPermutation,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
    MeasurableEquiv.prodCongr,Equiv.prodCongr]

end QuantitativePaper
