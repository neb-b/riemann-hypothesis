module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

noncomputable def ratioLine (m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)) : HermLine (GlobalTheory κ) where
  a := 0
  h z := m₁.ρ z / m₀.ρ z
  pos z hz := by
    have hz0 : z ≠ 0 := fun h0 => by
      obtain ⟨i, hi⟩ := hz ()
      exact hi (congrFun h0 _)
    exact div_pos (m₁.pos z hz0) (m₀.pos z hz0)
  smul c z hc := by
    have : (fun p : Ix κ => c p.1 * z p) = c () • z := by
      funext p
      rfl
    have hc0 : ‖c ()‖ ≠ 0 := norm_ne_zero_iff.mpr (hc ())
    rw [this, m₀.smul, m₁.smul, mul_div_mul_left _ _ hc0]
    simp

theorem tele_ptsIntegral_neg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => - g z) = - ptsIntegral P φ g := by
  have hsd : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> ring
  unfold ptsIntegral
  split_ifs with h
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_neg]
    congr 1
    funext y
    simp_rw [hsd]
    rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
    congr 1
    funext w
    by_cases hw : w ∈ fibre P h.choose y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hw]
  · simp

theorem tele_one_homog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  have h0 : m = 0 := by
    by_contra hne
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
    exact hm rfl
  subst h0
  simp

theorem tele_divSupp_one {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hW, -⟩
  have h1 := hW.1
  rw [Ideal.span_singleton_one, sup_top_eq] at h1
  exact h1.1.ne_top (top_le_iff.1 h1.2)

theorem fam_degZero (I : AllFam) (hI : I.IsFamily) {P : Ideal (MRing (GlobalTheory κ))} {n : ℕ}
    (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine (GlobalTheory κ)) (hL : ∀ j, IsSmoothHerm (L j))
    (B : HermLine (GlobalTheory κ)) (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    I Unit (GlobalTheory κ) P (n + 1) (Fin.snoc L B) = ptsIntegral P (pot L) fun z => Real.log (B.h z) := by
  obtain ⟨-, -, h3⟩ := hI Unit (GlobalTheory κ)
  have hP1 : (1 : MRing (GlobalTheory κ)) ∉ P := by
    intro h1
    have htop : P = ⊤ := (Ideal.eq_top_iff_one P).2 h1
    have h4 := hP.2.2.2
    rw [htop] at h4
    haveI : Subsingleton (MRing (GlobalTheory κ) ⧸ (⊤ : Ideal (MRing (GlobalTheory κ)))) :=
      Ideal.Quotient.subsingleton_iff.2 rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at h4
    exact WithBot.bot_ne_coe h4
  rw [h3 P n L B 1 0 hP hL hB (fun k => by rw [hB0]; simp) tele_one_homog hP1]
  unfold recR
  rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
  unfold arInt
  have hln : logNorm B 1 = fun z => -Real.log (B.h z) := by
    funext z
    simp [logNorm, Real.log_inv]
  rw [hln, tele_ptsIntegral_neg, neg_neg]
  rfl

theorem tele_herm_ext {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  obtain ⟨a, h, _, _⟩ := A
  obtain ⟨a', h', _, _⟩ := B
  simp only at ha hh
  subst ha
  subst hh
  rfl

theorem tele_rho_zero (m : ConeMetric (C := ℂ) (ι := Ix κ)) : m.ρ 0 = 0 := by
  have h := m.smul 0 0
  simpa using h

theorem tele_ofCone_tensor (m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)) :
    HermLine.ofCone m₁ = (HermLine.ofCone m₀).tensor (ratioLine m₀ m₁) := by
  apply tele_herm_ext
  · show (1 : Unit → ℤ) = 1 + 0
    simp
  · funext z
    show m₁.ρ z = m₀.ρ z * (m₁.ρ z / m₀.ρ z)
    by_cases hz : z = 0
    · subst hz
      rw [tele_rho_zero, tele_rho_zero]
      simp
    · rw [mul_div_cancel₀ _ (m₀.pos z hz).ne']

theorem tele_smooth_ofCone {m : ConeMetric (C := ℂ) (ι := Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  show ContDiffOn ℝ _ m.ρ _
  refine hm.mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem tele_smooth_ratio {m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) : IsSmoothHerm (ratioLine m₀ m₁) := by
  have hsub : {z : Ix κ → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ⊆ {z | z ≠ 0} := by
    intro z hz h0
    obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  show ContDiffOn ℝ _ (fun z => m₁.ρ z / m₀.ρ z) _
  exact (h₁.mono hsub).div (h₀.mono hsub) fun z hz => (m₀.pos z (hsub hz)).ne'

def tele_perm {n : ℕ} (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' i).symm

theorem tele_comp_perm {α : Type*} {n : ℕ} (F : Fin (n + 1) → α) (i : Fin (n + 1)) :
    F ∘ tele_perm i = Fin.snoc (F ∘ i.succAbove) (F i) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [tele_perm]
  · simp [tele_perm]

def tele_fam (m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)) (N i : ℕ) : Fin N → HermLine (GlobalTheory κ) :=
  fun j => if j.val < i then HermLine.ofCone m₁ else HermLine.ofCone m₀

theorem tele_fam_succAbove (m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) (hi : i < D + 1) (k : ℕ)
    (hk : k = i ∨ k = i + 1) :
    tele_fam m₀ m₁ (D + 1) k ∘ (⟨i, hi⟩ : Fin (D + 1)).succAbove = tele_fam m₀ m₁ D i := by
  funext j
  simp only [Function.comp, tele_fam]
  have hv : (Fin.succAbove (⟨i, hi⟩ : Fin (D + 1)) j).val = if j.val < i then j.val else j.val + 1 := by
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega
  rw [hv]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tele_fam_smooth {m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) (N i : ℕ) (j : Fin N) : IsSmoothHerm (tele_fam m₀ m₁ N i j) := by
  unfold tele_fam
  split_ifs
  · exact tele_smooth_ofCone h₁
  · exact tele_smooth_ofCone h₀

theorem top_sub_top (I : AllFam) (hI : I.IsFamily) {x : Ix κ → Ω} {m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)}
    {μ : Measure (Ix κ → ℂ)} (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  have h₀ : IsSmoothMetric m₀ := hg₀.semipos.1
  have h₁ : IsSmoothMetric m₁ := hg₁.semipos.1
  have hP := hg₀.arith
  obtain ⟨hperm, hadd, -⟩ := hI Unit (GlobalTheory κ)
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, F = fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) :=
    ⟨_, rfl⟩
  have hF0 : F 0 = top I x m₀ D := by
    rw [hF, top]
    show I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) 0) = _
    congr 1
    try (funext j; simp [tele_fam])
  have hFD : F (D + 1) = top I x m₁ D := by
    rw [hF, top]
    show I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (D + 1)) = _
    congr 1
    try (funext j; simp [tele_fam, j.isLt])
  have hstep : ∀ i ∈ Finset.range (D + 1), F (i + 1) - F i =
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsm : ∀ k j, IsSmoothHerm (tele_fam m₀ m₁ (D + 1) k j) := tele_fam_smooth h₀ h₁ (D + 1)
    have hσ : ∀ k, F k = I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (tele_fam m₀ m₁ (D + 1) k ∘ tele_perm ⟨i, hi⟩) := by
      intro k
      rw [hF]
      exact (hperm _ _ _ _ hP (hsm k)).symm
    rw [hσ (i + 1), hσ i, tele_comp_perm, tele_comp_perm,
      tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl), tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have e1 : tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ = HermLine.ofCone m₁ := by simp [tele_fam]
    have e2 : tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ = HermLine.ofCone m₀ := by simp [tele_fam]
    rw [e1, e2, tele_ofCone_tensor m₀ m₁, hadd _ _ _ _ _ hP (tele_fam_smooth h₀ h₁ D i)
      (tele_smooth_ofCone h₀) (tele_smooth_ratio h₀ h₁), add_sub_cancel_left,
      fam_degZero I hI hP (tele_fam m₀ m₁ D i) (tele_fam_smooth h₀ h₁ D i) (ratioLine m₀ m₁)
        (tele_smooth_ratio h₀ h₁) rfl]
    congr 1
    all_goals first
      | rfl
      | (funext j z
         simp only [pot, mixPot, tele_fam]
         split_ifs <;> rfl)
  rw [← hFD, ← hF0, ← Finset.sum_range_sub F (D + 1)]
  exact Finset.sum_congr rfl hstep

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def i2bdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem i2bdeg_add (m n : (Σ k, ι k) →₀ ℕ) : i2bdeg (m + n) = i2bdeg m + i2bdeg n := by
  funext k
  simp [i2bdeg, Finset.sum_add_distrib]


open Classical in
def i2comp (a : K → ℕ) (h : MRing ι) : MRing ι :=
  ∑ m ∈ h.support.filter (fun m => i2bdeg m = a), monomial m (AddMonoidAlgebra.coeff h m)

open Classical in
theorem coeff_i2comp (a : K → ℕ) (h : MRing ι) (m : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (i2comp a h) m = if i2bdeg m = a then AddMonoidAlgebra.coeff h m else 0 := by
  unfold i2comp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h0 : AddMonoidAlgebra.coeff h m = 0 <;> by_cases e : i2bdeg m = a <;> simp [Finset.mem_filter, mem_support_iff, h0, e]

theorem isMultiHomog_iff_coeff (s : MRing ι) (a : K → ℕ) :
    IsMultiHomog s a ↔ ∀ m, AddMonoidAlgebra.coeff s m ≠ 0 → i2bdeg m = a := by
  constructor
  · intro h m hm
    funext k
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    exact congrFun (h m (mem_support_iff.mp hm)) k

def i2compHom (a : K → ℕ) : MRing ι →+ MRing ι where
  toFun := i2comp a
  map_zero' := by
    classical
    ext m
    rw [coeff_i2comp]
    simp
  map_add' x y := by
    classical
    ext m
    change AddMonoidAlgebra.coeff (i2comp a (x + y)) m =
      AddMonoidAlgebra.coeff (i2comp a x) m + AddMonoidAlgebra.coeff (i2comp a y) m
    rw [coeff_i2comp, coeff_i2comp, coeff_i2comp, AddMonoidAlgebra.coeff_add]
    change (if i2bdeg m = a then AddMonoidAlgebra.coeff x m + AddMonoidAlgebra.coeff y m else 0) = _
    split_ifs <;> simp

theorem i2comp_add (a : K → ℕ) (x y : MRing ι) : i2comp a (x + y) = i2comp a x + i2comp a y :=
  (i2compHom a).map_add x y

theorem i2comp_zero (a : K → ℕ) : i2comp a (0 : MRing ι) = 0 := (i2compHom a).map_zero

theorem isMultiHomog_i2comp (a : K → ℕ) (h : MRing ι) : IsMultiHomog (i2comp a h) a := by
  classical
  rw [isMultiHomog_iff_coeff]
  intro m hm
  rw [coeff_i2comp] at hm
  by_contra e
  exact hm (ite_eq_right e)

theorem i2comp_of_homog {a b : K → ℕ} {h : MRing ι} (hh : IsMultiHomog h b) :
    i2comp a h = if b = a then h else 0 := by
  classical
  rw [isMultiHomog_iff_coeff] at hh
  ext m
  rw [coeff_i2comp]
  by_cases hm : AddMonoidAlgebra.coeff h m = 0
  · split_ifs <;> simp [hm]
  · have := hh m hm
    subst this
    split_ifs <;> simp_all

theorem i2comp_self {a : K → ℕ} {h : MRing ι} (hh : IsMultiHomog h a) : i2comp a h = h := by
  rw [i2comp_of_homog hh, ite_eq_left rfl]

theorem eq_sum_multihomogeneous_components (r : MRing ι) :
    r = ∑ b ∈ r.support.image i2bdeg, i2comp b r := by
  classical
  ext m
  rw [coeff_sum]
  simp_rw [coeff_i2comp]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))

theorem mem_mHom_iff (s : MRing ι) (a : K → ℕ) : s ∈ mHom ι a ↔ IsMultiHomog s a := by
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => intro m hm; simp at hm
    | add x y _ _ hx hy =>
      rw [isMultiHomog_iff_coeff] at hx hy ⊢
      intro m hm
      rw [AddMonoidAlgebra.coeff_add] at hm
      change AddMonoidAlgebra.coeff x m + AddMonoidAlgebra.coeff y m ≠ 0 at hm
      by_cases h0 : AddMonoidAlgebra.coeff x m = 0
      · rw [h0, zero_add] at hm
        exact hy m hm
      · exact hx m h0
    | smul n x _ hx =>
      rw [isMultiHomog_iff_coeff] at hx ⊢
      intro m hm
      rw [coeff_smul] at hm
      exact hx m (fun h0 => hm (by rw [h0, smul_zero]))
  · intro hs
    exact Submodule.subset_span hs

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  rw [isMultiHomog_iff_coeff] at hf hg ⊢
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, i2bdeg_add, hf x.1 (left_ne_zero_of_mul hx0), hg x.2 (right_ne_zero_of_mul hx0)]

theorem i2bdeg_apply_add (m n : (Σ k, ι k) →₀ ℕ) (k : K) :
    i2bdeg (m + n) k = i2bdeg m k + i2bdeg n k := by
  simp [i2bdeg, Finset.sum_add_distrib]

open Classical in
theorem i2comp_mul_right {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (a : K → ℕ)
    (g : MRing ι) : i2comp a (g * f) = if c ≤ a then i2comp (a - c) g * f else 0 := by
  rw [isMultiHomog_iff_coeff] at hf
  ext m
  rw [coeff_i2comp]
  split_ifs with hm hca hca
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : AddMonoidAlgebra.coeff f x.2 = 0
    · simp [h0]
    · have e2 := hf x.2 h0
      have e : i2bdeg x.1 = a - c := by
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun hm k
        have h3 := congrFun e2 k
        simp only [Pi.sub_apply]
        rw [← h2, h1, h3, Nat.add_sub_cancel]
      rw [ite_eq_left e]
  · simp only [AddMonoidAlgebra.coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h0 : AddMonoidAlgebra.coeff f x.2 = 0
    · simp [h0]
    · exfalso
      apply hca
      have e2 := hf x.2 h0
      intro k
      have h1 := i2bdeg_apply_add x.1 x.2 k
      rw [hx] at h1
      have h2 := congrFun hm k
      have h3 := congrFun e2 k
      rw [← h2, h1, h3]
      exact Nat.le_add_left _ _
  · rw [coeff_mul]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : AddMonoidAlgebra.coeff f x.2 = 0
    · simp [h0]
    · by_cases e : i2bdeg x.1 = a - c
      · exfalso
        apply hm
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun e k
        have h3 := congrFun (hf x.2 h0) k
        have h4 := hca k
        simp only [Pi.sub_apply] at h2
        rw [h1, h2, h3, Nat.sub_add_cancel h4]
      · simp [e]
  · simp

open Classical in
theorem i2comp_mem {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) (a : K → ℕ) {u : MRing ι}
    (hu : u ∈ F) : i2comp a u ∈ F := by
  classical
  obtain ⟨S, hS, rfl⟩ := hF
  revert a
  induction hu using Submodule.span_induction with
  | mem x hx =>
    intro a
    obtain ⟨b, hb⟩ := hS x hx
    rw [i2comp_of_homog hb]
    split_ifs
    · exact Ideal.subset_span hx
    · exact zero_mem _
  | zero => intro a; rw [i2comp_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro a; rw [i2comp_add]; exact add_mem (hx a) (hy a)
  | smul r x _ hx =>
    intro a
    rw [smul_eq_mul, eq_sum_multihomogeneous_components r, Finset.sum_mul]
    have : i2comp a (∑ b ∈ r.support.image i2bdeg, i2comp b r * x) =
        ∑ b ∈ r.support.image i2bdeg, i2comp a (i2comp b r * x) := map_sum (i2compHom a) _ _
    rw [this]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [mul_comm, i2comp_mul_right (isMultiHomog_i2comp b r)]
    split_ifs
    · exact Ideal.mul_mem_right _ _ (hx _)
    · exact zero_mem _

theorem isMultiHomogIdeal_sup_span {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (F ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hF
  refine ⟨S ∪ {f}, fun g hg => ?_, (Ideal.span_union S {f}).symm⟩
  rcases hg with hg | hg
  · exact hS g hg
  · rw [Set.mem_singleton_iff] at hg
    exact ⟨c, hg ▸ hf⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

