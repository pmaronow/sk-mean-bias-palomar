module
public import QuantitativePaper.VectorPrefixEuclideanLaw

@[expose] public section

/-! The actual incident-site Gaussian block and its unchanged complement.
Negating that block implements the true one-site symmetry of every prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2000000

def siteGaussianPredicate {n N:ℕ} (i:Fin n):VectorPrefixGaussianIndex n N→Prop
  | .inl none=>False
  | .inl (some e)=>e.val.1=i ∨ e.val.2=i
  | .inr j=>j.2=i

instance siteGaussianPredicate_decidable {n N:ℕ} (i:Fin n):
    DecidablePred (siteGaussianPredicate (N:=N) i):=by
  intro a
  unfold siteGaussianPredicate
  split <;> infer_instance

abbrev SiteGaussianIndex {n N:ℕ} (i:Fin n):={a:VectorPrefixGaussianIndex n N//siteGaussianPredicate i a}
abbrev SiteComplementIndex {n N:ℕ} (i:Fin n):={a:VectorPrefixGaussianIndex n N//¬siteGaussianPredicate i a}

def siteGaussianSign {n N:ℕ} (i:Fin n) (a:VectorPrefixGaussianIndex n N):ℝ:=
  if siteGaussianPredicate i a then -1 else 1

theorem abs_siteGaussianSign {n N:ℕ} (i:Fin n) (a:VectorPrefixGaussianIndex n N):
    |siteGaussianSign i a|=1:=by
  unfold siteGaussianSign
  split_ifs <;> norm_num

def siteGaussianReflection {n N:ℕ} (i:Fin n):
    VectorPrefixGaussianSpace n N→L[ℝ]VectorPrefixGaussianSpace n N:=
  coordinateSignCLM (siteGaussianSign i) (abs_siteGaussianSign i)

theorem siteGaussianReflection_gaussian_map {n N:ℕ} (i:Fin n):
    (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)).map
      (siteGaussianReflection i)=SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N):=
  standardGaussianMeasure_coordinateSign_map (siteGaussianSign i) (abs_siteGaussianSign i)

theorem siteGaussianSplit_law {n N:ℕ} (i:Fin n):
    (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)).map
      (gaussianCoordinateSplit (siteGaussianPredicate i))=
      (SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)).prod
        (SYK.standardGaussianMeasureOnEuclidean (SiteComplementIndex (N:=N) i)):=
  standardGaussianMeasure_gaussianCoordinateSplit_map (siteGaussianPredicate i)

theorem siteGaussianSign_edge {n N:ℕ} (i:Fin n) (e:Edge n):
    siteGaussianSign (N:=N) i (.inl (some e))=siteSign i e.val.1*siteSign i e.val.2:=by
  have hneq:e.val.1≠e.val.2:=ne_of_lt e.property
  by_cases h1:e.val.1=i <;> by_cases h2:e.val.2=i
  · exact (hneq (h1.trans h2.symm)).elim
  · simp [siteGaussianSign,siteGaussianPredicate,siteSign,h1,h2]
  · simp [siteGaussianSign,siteGaussianPredicate,siteSign,h1,h2]
  · simp [siteGaussianSign,siteGaussianPredicate,siteSign,h1,h2]

theorem vectorPrefixEuclideanCoordinates_site_reflection {n N:ℕ} (i:Fin n)
    (z:VectorPrefixGaussianSpace n N):
    vectorPrefixEuclideanCoordinates n N (siteGaussianReflection i z)=
      (siteDisorderReflection i (vectorPrefixEuclideanCoordinates n N z).1,
        fun j=>siteFieldReflection i ((vectorPrefixEuclideanCoordinates n N z).2 j)):=by
  apply Prod.ext
  · apply Prod.ext
    · funext e
      change siteGaussianSign i (.inl (some e))*z (.inl (some e))=_
      rw [siteGaussianSign_edge]
      rfl
    · change Real.sqrt (1/2:ℝ)*(siteGaussianSign i (.inl none)*z (.inl none))=_
      simp [siteGaussianSign,siteGaussianPredicate,siteDisorderReflection,vectorPrefixEuclideanCoordinates]
  · funext j
    ext l
    change siteGaussianSign i (.inr (j,l))*z (.inr (j,l))=_
    simp only [siteGaussianSign,siteGaussianPredicate,siteFieldReflection_apply,siteSign]
    rfl

theorem siteGaussianJoin_neg {n N:ℕ} (i:Fin n)
    (g:EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i))
    (b:EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)):
    gaussianCoordinateJoin (siteGaussianPredicate i) (-g,b)=
      siteGaussianReflection i (gaussianCoordinateJoin (siteGaussianPredicate i) (g,b)):=by
  ext a
  change (if ha:siteGaussianPredicate i a then (-g) ⟨a,ha⟩ else b ⟨a,ha⟩)=
    siteGaussianSign i a*(if ha:siteGaussianPredicate i a then g ⟨a,ha⟩ else b ⟨a,ha⟩)
  by_cases ha:siteGaussianPredicate i a <;> simp [siteGaussianSign,ha]

def siteStateReflection {n:ℕ} (i:Fin n) (x:VectorState n):VectorState n:=
  (siteDisorderReflection i x.1,siteFieldReflection i x.2)

theorem vectorCoordinateUpdate_site_reflection {n k:ℕ} (s:RSBScheme k)
    (i:Fin n) (β t:ℝ) (j:ℕ) (x:VectorState n) (z:Field n):
    vectorCoordinateUpdate s β t j (siteStateReflection i x) (siteFieldReflection i z)=
      siteStateReflection i (vectorCoordinateUpdate s β t j x z):=by
  unfold vectorCoordinateUpdate
  split_ifs
  · unfold vectorStateUpdate siteStateReflection
    exact Prod.ext rfl (fieldShift_site_reflection i _ x.2 z)
  · rfl

private theorem independentHistory_postmap {State Noise:Type*}
    (u:ℕ→State→Noise→State) (r:State→State) (v:Noise→Noise)
    (hu:∀j x z,u j (r x) (v z)=r (u j x z)) (N:ℕ)
    (p:State×(Fin N→Noise)):
    independentHistory u N (r p.1,fun j=>v (p.2 j))=
      fun j=>r (independentHistory u N p j):=by
  induction N with
  | zero=>rfl
  | succ N ih=>
    funext j
    refine Fin.lastCases ?_ (fun l=>?_) j
    · simp only [independentHistory,Fin.snoc_last]
      rw [ih (p.1,fun i=>p.2 i.castSucc),hu]
    · simp only [independentHistory,Fin.snoc_castSucc]
      rw [ih (p.1,fun i=>p.2 i.castSucc)]

theorem vectorPrefixEuclideanHistory_site_reflection {n k:ℕ} (s:RSBScheme k)
    (i:Fin n) (β t:ℝ) (N:ℕ) (z:VectorPrefixGaussianSpace n N) (j:Fin (N+1)):
    vectorPrefixEuclideanHistory s β t N (siteGaussianReflection i z) j=
      siteStateReflection i (vectorPrefixEuclideanHistory s β t N z j):=by
  simp only [vectorPrefixEuclideanHistory_apply,vectorPrefixEuclideanCoordinates_site_reflection]
  unfold vectorPrefixHistory
  have hi:=independentHistory_postmap (vectorCoordinateUpdate s β t) (siteStateReflection i)
    (siteFieldReflection i) (vectorCoordinateUpdate_site_reflection s i β t) N
    (((vectorPrefixEuclideanCoordinates n N z).1,0),(vectorPrefixEuclideanCoordinates n N z).2)
  have he:siteStateReflection i ((vectorPrefixEuclideanCoordinates n N z).1,0)=
      (siteDisorderReflection i (vectorPrefixEuclideanCoordinates n N z).1,0):=by
    simp [siteStateReflection]
  rw [he] at hi
  exact congrFun hi j

end QuantitativePaper
