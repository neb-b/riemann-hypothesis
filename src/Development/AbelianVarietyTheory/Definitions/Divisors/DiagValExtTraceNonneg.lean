module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open MeasureTheory
open scoped ContDiff ComplexOrder ENNReal

namespace GlobalTheory

namespace HermFrame

variable {m l n n' : Type} [Fintype m] [Fintype l] [Fintype n] [Fintype n'] [DecidableEq m]
  [DecidableEq l]


omit [Fintype n'] in
theorem chg_submatrix {m' : Type} [Fintype m'] (A : Matrix n n' ℂ) (H : Matrix n n ℂ) (e : m' ≃ n)
    {l' : Type} (f : l' → n') :
    chg (A.submatrix e f) (H.submatrix e e) = (chg A H).submatrix f f := by
  ext a b
  simp only [chg, Matrix.mul_apply, submatrix_apply, transpose_apply, conjTranspose_apply]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun j _ => by rw [← e.sum_comp]

variable (A₁ : Matrix m m ℂ) (B : Matrix m l ℂ) (A₂ : Matrix l l ℂ) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ)


omit [DecidableEq m] [DecidableEq l] in
theorem chg_fromBlocks : chg (fromBlocks A₁ B 0 A₂) H = fromBlocks (chg A₁ H.toBlocks₁₁)
    (A₁ᵀ * (H.toBlocks₁₁ * Bᴴᵀ + H.toBlocks₁₂ * A₂ᴴᵀ)) ((Bᵀ * H.toBlocks₁₁ + A₂ᵀ * H.toBlocks₂₁) * A₁ᴴᵀ)
    ((Bᵀ * H.toBlocks₁₁ + A₂ᵀ * H.toBlocks₂₁) * Bᴴᵀ + (Bᵀ * H.toBlocks₁₂ + A₂ᵀ * H.toBlocks₂₂) * A₂ᴴᵀ) := by
  conv_lhs => rw [← fromBlocks_toBlocks H]
  simp [chg, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_add,
    Matrix.mul_assoc]



omit [DecidableEq l] in
variable {A₁ H} in
theorem quotGram_chg (hA : IsUnit A₁.det) (hH : IsUnit (subGram H).det) :
    quotGram (chg (fromBlocks A₁ B 0 A₂) H) = chg A₂ (quotGram H) := by
  have h₁ : IsUnit A₁ᵀ.det := by rwa [det_transpose]
  have h₂ : IsUnit A₁ᴴᵀ.det := by rw [det_transpose, det_conjTranspose]; exact hA.star
  have h₃ : IsUnit H.toBlocks₁₁.det := hH
  rw [chg_fromBlocks]
  simp only [quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, chg, Matrix.mul_inv_rev, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ h₂, nonsing_inv_mul_cancel_left _ _ h₁, Matrix.mul_add,
    Matrix.add_mul, nonsing_inv_mul_cancel_left _ _ h₃, mul_nonsing_inv_cancel_left _ _ h₃,
    Matrix.mul_sub, Matrix.sub_mul]
  abel


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem extTrace_eq (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (ξ η : E) :
    extTrace K z ξ η = kappa * (secondForm K z ξ * secondFormAdj K z η).trace := by
  have hh := hp.mono fun x hx => hx.isHermitian
  have hu := hp.self_of_nhds.det_pos.ne'.isUnit
  have hs := (posDef_subGram hp.self_of_nhds).det_pos.ne'.isUnit
  rw [extTrace, extFormAdj_eq_neg_secondForm h hh hu hs, extForm_eq_neg_secondFormAdj h hh hu hs,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg]

end HermFrame

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

namespace VB.Chart

variable {E F : X.Modules} {r s : ℕ} (c₀ : Chart E r) (c : Chart F s) {U : X.Opens}
  {y : CxPts p σ}

theorem crd_app (φ : F ⟶ E) (t : Γ(F, U)) (hy : y ∈ ptsIn p σ U) (h : y ∈ ptsIn p σ c.U) :
    c₀.crd p σ (φ.app U t) y =
      (Matrix.of fun a b => c₀.crd p σ (φ.app c.U (c.e b)) y a) *ᵥ c.crd p σ t y := by
  have hW := mem_ptsIn_inf.2 ⟨hy, h⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← c₀.crd_resM _ inf_le_left hW, ← app_resM,
    ← (c.isFrame.basis inf_le_right).sum_repr (resM F _ t), map_sum, crd_sum]
  funext a
  simp only [Scheme.Modules.Hom.app_smul, crd_smul, IsFrame.basis_apply, app_resM,
    c₀.crd_resM _ _ hW, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end VB.Chart

namespace Met

variable {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {U : X.Opens} {y : CxPts p σ} {ι : Type}

def gram (t : ι → Γ(E, U)) (y : CxPts p σ) : Matrix ι ι ℂ := Matrix.of fun a b => h.form (t a) (t b) y

theorem gram_eq [Fintype ι] (c : Chart E r) (hc : y ∈ ptsIn p σ c.U) (t : ι → Γ(E, U))
    (hy : y ∈ ptsIn p σ U) :
    h.gram t y = chg (Matrix.of fun a b => c.crd p σ (t b) y a) (h.G c y) := by
  ext a b
  rw [chg_apply, gram, of_apply, h.form_eq c hc _ _ hy]
  rfl

theorem IsCInf.gram {h : Met p σ E r} (H : h.IsCInf) [Fintype ι] (t : ι → Γ(E, U))
    (hy : y ∈ ptsIn p σ U) : MInfAt (h.gram t) y := by
  have h₀ := h.isVB.mem_pick y
  refine (MInfAt.chg (A := fun z => Matrix.of fun a b => (h.isVB.pick y).crd p σ (t b) z a)
    (fun a b => Chart.vInfAt_crd _ _ hy h₀ a) (H _ y h₀)).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds h₀, (isOpen_ptsIn _).mem_nhds hy] with z h₁ h₂
  exact h.gram_eq _ h₁ t h₂

theorem IsConj.gram {h : Met p σ E r} {h' : Met p σ' E r} (H : h.IsConj h') (t : ι → Γ(E, U))
    {y' : CxPts p σ'} (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hy : y ∈ ptsIn p σ U) :
    h'.gram t y' = (h.gram t y).map star := by
  ext a b
  exact H.form_eq _ _ e hy

end Met

namespace VBExt.AdaptedChart

variable {S : ShortComplex X.Modules} {r s : ℕ} (hS : S.ShortExact) (a a' : AdaptedChart S r s)
  {U : X.Opens} {y : CxPts p σ}

def sub : Chart S.X₁ r := ⟨a.U, a.e, a.he⟩

def quot : Chart S.X₃ s := ⟨a.U, _, a.ht⟩

def frame : Fin r ⊕ Fin s → Γ(S.X₂, a.U) := Sum.elim (fun i => S.f.app a.U (a.e i)) a.t

def mid : Chart S.X₂ (r + s) :=
  ⟨a.U, a.frame ∘ finSumFinEquiv.symm,
    (isFrame_sumElim hS a.he a.ht).comp_equiv finSumFinEquiv.symm⟩

theorem crd_frame (hy : y ∈ ptsIn p σ a.U) (i j : Fin r ⊕ Fin s) :
    (a.mid hS).crd p σ (a.frame j) y (finSumFinEquiv i) = (1 : Matrix _ _ ℂ) i j := by
  have := congrFun ((a.mid hS).crd_frame hy (finSumFinEquiv j)) (finSumFinEquiv i)
  simpa [mid, Pi.single_apply, Matrix.one_apply] using this


variable (p σ) in
def tr (y : CxPts p σ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
  ((a.mid hS).tr p σ (a'.mid hS) y).submatrix finSumFinEquiv finSumFinEquiv

theorem tr_apply (i j : Fin r ⊕ Fin s) :
    a.tr p σ hS a' y i j = (a.mid hS).crd p σ (a'.frame j) y (finSumFinEquiv i) := by
  simp [tr, Chart.tr, mid]

theorem tr_eq (hy : y ∈ ptsIn p σ a.U) (hy' : y ∈ ptsIn p σ a'.U) :
    a.tr p σ hS a' y = fromBlocks (a.sub.tr p σ a'.sub y) (a.tr p σ hS a' y).toBlocks₁₂ 0
      (a.quot.tr p σ a'.quot y) := by
  have h₁ (i) (j : Fin r) : a.tr p σ hS a' y i (.inl j) =
      Sum.elim (fun i => a.sub.tr p σ a'.sub y i j) 0 i := by
    rw [tr_apply]
    refine (congrFun ((a.mid hS).crd_app a.sub S.f (a'.e j) hy' hy) _).trans ?_
    have e (b : Fin r) := a.crd_frame hS hy i (.inl b)
    simp only [mulVec, dotProduct, of_apply]
    refine (Finset.sum_congr rfl fun b _ => congrArg (· * _) (e b)).trans ?_
    rcases i with i | i <;> simp [Matrix.one_apply, Chart.tr, sub]
  have h₂ (i j : Fin s) : a.tr p σ hS a' y (.inr i) (.inr j) = a.quot.tr p σ a'.quot y i j := by
    rw [tr_apply]
    refine Eq.symm ((congrFun (a.quot.crd_app (a.mid hS) S.g (a'.t j) hy' hy) _).trans ?_)
    have e₁ (b : Fin r) : a.quot.crd p σ (S.g.app a.U (a.frame (.inl b))) y = 0 := by
      rw [show S.g.app a.U (a.frame (.inl b)) = 0 from congr(($(S.zero)).app a.U (a.e b)),
        Chart.crd_zero]
    have e₂ (b : Fin s) : a.quot.crd p σ (S.g.app a.U (a.frame (.inr b))) y = Pi.single b 1 :=
      a.quot.crd_frame hy b
    simp only [mulVec, dotProduct, of_apply]
    have e₃ (b) : (a.mid hS).e (finSumFinEquiv b) = a.frame b := by simp [mid]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun b _ => ?_)
      (Finset.sum_congr rfl fun b _ => congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans (e₂ b)) i))).trans ?_
    · exact mul_eq_zero_of_left (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans (e₁ b)) i) _
    · simp [Pi.single_apply, frame]
  ext (i | i) (j | j)
  exacts [h₁ _ j, rfl, h₁ _ j, h₂ i j]

end VBExt.AdaptedChart

namespace Met

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) {y : CxPts p σ} (a a' : AdaptedChart S r s)


include hS in
theorem gram_frame (hy : y ∈ ptsIn p σ a.U) :
    h.gram a.frame y = (h.G (a.mid hS) y).submatrix finSumFinEquiv finSumFinEquiv := by
  ext i j
  rw [submatrix_apply, ← h.form_frame _ hy]
  simp [gram, AdaptedChart.mid]


include hS in
theorem posDef_gram_frame (hy : y ∈ ptsIn p σ a.U) : (h.gram a.frame y).PosDef := by
  rw [h.gram_frame hS a hy]
  exact (h.posDef _ y hy).submatrix finSumFinEquiv.injective

theorem gram_frame_trans (hy : y ∈ ptsIn p σ a.U) (hy' : y ∈ ptsIn p σ a'.U) :
    h.gram a'.frame y = chg (a.tr p σ hS a' y) (h.gram a.frame y) := by
  rw [h.gram_frame hS a hy, h.gram_frame hS a' hy', AdaptedChart.tr, chg_submatrix,
    ← h.trans _ _ y hy]


include hS h₁ h₃ in
theorem exists_adapted (y : CxPts p σ) : ∃ a : AdaptedChart S r s, y ∈ ptsIn p σ a.U :=
  (VBExt.exists_adaptedChart hS h₁ h₃ _).imp fun _ => mem_ptsIn.2

def quot : Met p σ S.X₃ s :=
  ofCover h₃ AdaptedChart.quot (exists_adapted hS h₁ h₃) (fun a y => quotGram (h.gram a.frame y))
    fun a _ hy => posDef_quotGram (h.posDef_gram_frame hS a hy)

theorem quot_G (hy : y ∈ ptsIn p σ a.U) :
    (h.quot hS h₁ h₃).G a.quot y = quotGram (h.gram a.frame y) :=
  ofCover_G (c := AdaptedChart.quot) (fun a a' y hy hy' => by
    rw [h.gram_frame_trans hS a a' hy hy', a.tr_eq hS a' hy hy', quotGram_chg _ _
      ((isUnit_iff_isUnit_det _).1 (a.sub.isUnit_tr a'.sub hy hy'))
      (posDef_subGram (h.posDef_gram_frame hS a hy)).det_pos.ne'.isUnit]) hy

variable {h}

theorem IsCInf.quot (H : h.IsCInf) : (h.quot hS h₁ h₃).IsCInf := isCInf_of_exists fun y => by
  obtain ⟨a, hy⟩ := exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, hy, MInfAt.congr (A := fun z => quotGram (h.gram a.frame z)) (fun i j => ?_) ?_⟩
  · exact (H.gram a.frame hy).comp (Ψ := fun M => quotGram (of M) i j)
      (T := {M | IsUnit (subGram (of M)).det}) (isOpen_iff_mem_nhds.2 fun M hM =>
        (mContDiffAt_id M).subGram.eventually_isUnit hM)
      (posDef_subGram (h.posDef_gram_frame hS a hy)).det_pos.ne'.isUnit
      fun M hM => (mContDiffAt_id M).quotGram hM i j
  · filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz using h.quot_G hS h₁ h₃ a hz

theorem IsConj.quot {h' : Met p σ' S.X₂ (r + s)} (H : h.IsConj h') :
    (h.quot hS h₁ h₃).IsConj (h'.quot hS h₁ h₃) := isConj_of_exists fun y y' e => by
  obtain ⟨a, hy⟩ := exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, hy, ?_⟩
  rw [h.quot_G hS h₁ h₃ a hy, h'.quot_G hS h₁ h₃ a ((mem_ptsIn_iff_of_conj e).2 hy), H.gram _ e hy]
  generalize h.gram a.frame y = M
  have e₁ : (M.map star).toBlocks₁₁⁻¹ = M.toBlocks₁₁⁻¹.map star :=
    congrArg transpose (dualGram_map_star M.toBlocks₁₁)
  rw [quotGram, quotGram, e₁]
  ext i j
  simp [Matrix.mul_apply, toBlocks₂₁, toBlocks₁₂, toBlocks₂₂, map_sum, map_mul]

end Met

namespace Met

variable {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {i : F ⟶ E}

variable {h}

end Met

namespace Met

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) {y : CxPts p σ} (a a' : AdaptedChart S r s)
  {D : ℕ} (c c' : AlgChart p σ D)


variable {h}


variable (h) (c c' : AlgChart p σ 1)

variable {h}

end Met

namespace VMetric

section Seq

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : VMetric p S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

def quot : VMetric p S.X₃ s :=
  ⟨h₃, fun σ => (h.met σ).quot hS h₁ h₃, fun σ σ' => (h.conj σ σ').quot hS h₁ h₃⟩


variable {h} in
theorem IsCInf.quot (H : h.IsCInf) : (h.quot hS h₁ h₃).IsCInf := fun σ => (H σ).quot hS h₁ h₃

end Seq

variable {E F : X.Modules} {r s : ℕ} (h : VMetric p E r)


variable (fl : Vert.Flag E r) (i : Fin r)

abbrev stepSeq : ShortComplex X.Modules := .mk (fl.step i) (fl.π i) (Limits.cokernel.condition _)

theorem stepSeq_shortExact : (stepSeq fl i).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

variable {h}

end VMetric

end GlobalTheory
