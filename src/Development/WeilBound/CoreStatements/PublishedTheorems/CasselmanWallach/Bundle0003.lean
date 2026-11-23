module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonalOfCalculus
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceOrthogonality

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

lemma nc_sum (f : Fin n × Fin n → ℂ) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε a ≠ ε b then f (a, b) else 0 := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

lemma s1 (g : Fin n → Fin n → ℂ) (c : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if c = a then g a b else 0) else 0) =
      ∑ b, if ε c ≠ ε b then g c b else 0 := by
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp
  · intro a _ hac
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm hac]
  · simp

lemma s2 (g : Fin n → Fin n → ℂ) (d : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if b = d then g a b else 0) else 0) =
      ∑ a, if ε a ≠ ε d then g a d else 0 := by
  rw [Finset.sum_comm, Finset.sum_eq_single d]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp
  · intro b _ hbd
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hbd]
  · simp

lemma comm_apply (hgl : IsGlRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T x) (hgl a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp

lemma pt (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (a b : Fin n) (x y : V) :
    inner ℂ (E a b (E c d x)) (A (E a b y)) =
      inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0)
      + (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0)
      - (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) := by
  have hsgn : adjSign ε c d = 1 := by simp [adjSign, hcd]
  have h1 : inner ℂ (E c d (E a b x)) (A (E a b y)) = inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) := by
    rw [huni c d, hsgn, one_mul, ← hA d c hcd.symm, comm_apply hgl d c a b y]
    rw [map_add (f := _), map_sub, inner_add_right, inner_sub_right]
    split_ifs <;> (try simp) <;> ring
  rw [comm_apply hgl a b c d x, inner_add_left, h1, inner_sub_left]
  split_ifs <;> (try simp) <;> ring

lemma key (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (x y : V) :
    beta ε E A (E c d x) y = beta ε E A x (E d c y) := by
  have e : ∀ a b, (if ε a ≠ ε b then inner ℂ (E a b (E c d x)) (A (E a b y)) else 0) =
      (if ε a ≠ ε b then inner ℂ (E a b x) (A (E a b (E d c y))) else 0)
      + (if ε a ≠ ε b then (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) else 0)
      + (if ε a ≠ ε b then (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) else 0) := by
    intro a b
    by_cases hab : ε a ≠ ε b
    · simp only [if_pos hab]
      exact pt hgl huni hA hcd a b x y
    · simp only [if_neg hab]
      simp
  have h1 := s1 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E d b y))) c
  have h4 := s1 (ε := ε) (fun a b => inner ℂ (E c b x) (A (E a b y))) d
  have h2 := s2 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E a c y))) d
  have h3 := s2 (ε := ε) (fun a b => inner ℂ (E a d x) (A (E a b y))) c
  simp only [beta, nc_sum]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, hcd]
  ring

lemma beta_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    beta ε E A (∑ i ∈ s, f i) w = ∑ i ∈ s, beta ε E A (f i) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, map_sum, sum_inner]
  exact Finset.sum_comm

lemma beta_sum_right {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    beta ε E A v (∑ i ∈ s, f i) = ∑ i ∈ s, beta ε E A v (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, map_sum, inner_sum]
  exact Finset.sum_comm

lemma Lsym (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z)) (v w : V) :
    beta ε E A (casimirK ε E v) w = beta ε E A v (casimirK ε E w) := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, beta_sum_left, beta_sum_right]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  rw [key hgl huni hA hab.symm, key hgl huni hA hab]

lemma beta_smul_left (r : ℝ) (v w : V) :
    beta ε E A ((r : ℂ) • v) w = (r : ℂ) * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

lemma beta_smul_right (r : ℂ) (v w : V) :
    beta ε E A v (r • w) = r * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

end EigenspaceOrthogonality

theorem eigenspaces_orthogonal_of_calculus : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt := by
  intro hA0 hA11b n ε V _ _ E h ι b μ hB φ ν ν' v w hne hv hw
  obtain ⟨-, -, hZ, -⟩ := hA0 n ε V E h
  obtain ⟨hfc, -⟩ := hA11b n ε V E h ι b μ hB
  have hcomm : ∀ c d, ε c = ε d → ∀ z, fc b μ φ (E c d z) = E c d (fc b μ φ z) := by
    intro c d hcd z
    have heig : ∀ i, Eig ε E (μ i) (E c d (b i)) := by
      intro i
      have hz := congrArg (fun T : Module.End ℂ V => T (b i)) (hZ c d hcd)
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hz
      show casimirK ε E (E c d (b i)) = ((μ i : ℝ) : ℂ) • E c d (b i)
      rw [sub_eq_zero.mp hz, show casimirK ε E (b i) = ((μ i : ℝ) : ℂ) • b i from hB.eig i, map_smul]
    have hT : (fc b μ φ).comp (E c d) = (E c d).comp (fc b μ φ) := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply]
      rw [hfc φ (μ i) _ (heig i), hfc φ (μ i) _ (hB.eig i), map_smul]
    exact LinearMap.congr_fun hT z
  have hL := EigenspaceOrthogonality.Lsym (A := fc b μ φ) h.gl h.uni hcomm v w
  rw [show casimirK ε E v = ((ν : ℝ) : ℂ) • v from hv,
    show casimirK ε E w = ((ν' : ℝ) : ℂ) • w from hw,
    EigenspaceOrthogonality.beta_smul_left, EigenspaceOrthogonality.beta_smul_right] at hL
  have hm : (((ν : ℝ) : ℂ) - ((ν' : ℝ) : ℂ)) * beta ε E (fc b μ φ) v w = 0 := by
    rw [sub_mul, hL, sub_self]
  rcases mul_eq_zero.mp hm with h0 | h0
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h0)) hne
  · exact h0

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EnvelopingAlgebraGrowthBound
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace IdentityFiltrationBound

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def W (n k : ℕ) : Finset (List (Fin n × Fin n)) := (List.finite_length_le (Fin n × Fin n) k).toFinset

lemma mem_W {k : ℕ} {l : List (Fin n × Fin n)} : l ∈ W n k ↔ l.length ≤ k := by
  simp [W]

def wd (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (l.map fun p => E p.1 p.2).prod

def N (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : ℝ := ∑ l ∈ W n k, ‖wd E l v‖

lemma N_nonneg (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : 0 ≤ N E k v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma le_N (E : Fin n → Fin n → Module.End ℂ V) {k : ℕ} {l : List (Fin n × Fin n)} (hl : l.length ≤ k)
    (v : V) : ‖wd E l v‖ ≤ N E k v :=
  Finset.single_le_sum (f := fun l => ‖wd E l v‖) (fun _ _ => norm_nonneg _) (mem_W.2 hl)

lemma U_bound (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (u : Module.End ℂ V) (hu : u ∈ U E k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v, ‖u v‖ ≤ c * N E k v := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun v => by simpa [wd] using le_N E hl v⟩
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨d, hd, h'⟩ := hy
    refine ⟨c + d, add_nonneg hc hd, fun v => ?_⟩
    calc ‖(x + y) v‖ ≤ ‖x v‖ + ‖y v‖ := by simpa using norm_add_le (x v) (y v)
      _ ≤ c * N E k v + d * N E k v := add_le_add (h v) (h' v)
      _ = (c + d) * N E k v := by ring
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    refine ⟨‖a‖ * c, mul_nonneg (norm_nonneg _) hc, fun v => ?_⟩
    calc ‖(a • x) v‖ = ‖a‖ * ‖x v‖ := by simp [norm_smul]
      _ ≤ ‖a‖ * (c * N E k v) := mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
      _ = ‖a‖ * c * N E k v := by ring

lemma quad {x y P Q : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : x ^ 2 ≤ P * y ^ 2 + Q * x * y) : x ≤ (Q + Real.sqrt P) * y := by
  by_contra hc
  push Not at hc
  have hs := Real.sq_sqrt hP
  have hs0 := Real.sqrt_nonneg P
  have hxpos : 0 < x := lt_of_le_of_lt (mul_nonneg (add_nonneg hQ hs0) hy) hc
  have h1 : Real.sqrt P * y ≤ x := by nlinarith [mul_nonneg hQ hy]
  nlinarith [mul_pos hxpos (sub_pos.2 hc), mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hy)]

lemma step (E : Fin n → Fin n → Module.End ℂ V) (ε : Fin n → Bool) (κ μ c : ℝ) (k : ℕ)
    (hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hc0 : 0 ≤ c)
    (hc : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
      ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v)
    (v : V) (hv : casimirK ε E v = (μ : ℂ) • v) (hμ : 0 ≤ μ) :
    N E (k + 1) v ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * c + ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) *
      Real.sqrt (1 + μ) * N E k v := by
  have hx : 0 ≤ N E (k + 1) v := N_nonneg E _ v
  have hy : 0 ≤ N E k v := N_nonneg E _ v
  set x := N E (k + 1) v with hxdef
  set y := N E k v with hydef
  set M : ℝ := ((W n (k + 1)).card : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hκ := abs_nonneg κ
  have key : ∀ l : List (Fin n × Fin n), l.length ≤ k + 1 →
      ‖wd E l v‖ ^ 2 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by
    intro l hl
    cases l with
    | nil =>
      have h1 : ‖wd E [] v‖ ≤ y := le_N E (l := []) (k := k) (Nat.zero_le _) v
      have h2 : 0 ≤ ‖wd E [] v‖ := norm_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hc0 hx) hy,
        mul_nonneg (add_nonneg (mul_nonneg zero_le_two hμ) hκ) (sq_nonneg y)]
    | cons p l' =>
      have hl' : l'.length ≤ k := by simpa using hl
      have hwy : ‖wd E l' v‖ ≤ y := le_N E hl' v
      have hz := hc l' hl' v
      have hOw : casimirK ε E (wd E l' v) =
          (casimirK ε E * wd E l' - wd E l' * casimirK ε E) v + (μ : ℂ) • wd E l' v := by
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul]
        abel
      have hsplit : wd E (p :: l') v = E p.1 p.2 (wd E l' v) := by
        simp [wd, Module.End.mul_apply]
      rw [hsplit]
      have hle : ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 := by
        calc ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ b, ‖E p.1 b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun b => ‖E p.1 b (wd E l' v)‖ ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_univ _)
          _ ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun a => ∑ b, ‖E a b (wd E l' v)‖ ^ 2)
                (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      have hin : (inner ℂ (wd E l' v) (casimirK ε E (wd E l' v))).re ≤
          ‖wd E l' v‖ * ‖(casimirK ε E * wd E l' - wd E l' * casimirK ε E) v‖ + μ * ‖wd E l' v‖ ^ 2 := by
        have hself : (inner ℂ (wd E l' v) (wd E l' v)).re = ‖wd E l' v‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [hOw, inner_add_right, Complex.add_re, inner_smul_right, Complex.re_ofReal_mul, hself]
        have := (Complex.re_le_norm (inner ℂ (wd E l' v)
          ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v))).trans (norm_inner_le_norm _ _)
        linarith
      rw [hcas] at hle
      have hw0 := norm_nonneg (wd E l' v)
      have hz0 := norm_nonneg ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v)
      have e1 := mul_le_mul hwy hz hz0 hy
      have e2 : ‖wd E l' v‖ ^ 2 ≤ y ^ 2 := by nlinarith
      have e3 := mul_le_mul_of_nonneg_left e2 hμ
      have e4 := mul_le_mul_of_nonneg_left e2 hκ
      have hk : -κ * ‖wd E l' v‖ ^ 2 ≤ |κ| * ‖wd E l' v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [neg_abs_le κ]) (sq_nonneg _)
      nlinarith [sq_nonneg y]
  have hR0 : 0 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by positivity
  have hsum : x ≤ M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    calc x = ∑ l ∈ W n (k + 1), ‖wd E l v‖ := rfl
      _ ≤ ∑ l ∈ W n (k + 1), Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) :=
          Finset.sum_le_sum fun l hl => (le_abs_self _).trans (Real.abs_le_sqrt (key l (mem_W.1 hl)))
      _ = M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by simp [hM]
  have hsq : x ^ 2 ≤ M ^ 2 * ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    have := Real.sq_sqrt hR0
    have h0 := mul_nonneg hM0 (Real.sqrt_nonneg ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y))
    nlinarith
  have hA : 0 ≤ 2 * μ + |κ| + 1 := by positivity
  have hq := quad (P := M ^ 2 * (2 * μ + |κ| + 1)) (Q := 2 * M ^ 2 * c) hx hy (by positivity) (by positivity)
    (by linarith)
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0] at hq
  have ha : Real.sqrt (2 * μ + |κ| + 1) ≤ Real.sqrt (2 + |κ|) * Real.sqrt (1 + μ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ht : 1 ≤ Real.sqrt (1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have h1 := mul_le_mul_of_nonneg_left ht (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * M ^ 2 * c) hy)
  have h2 := mul_le_mul_of_nonneg_left ha (mul_nonneg hM0 hy)
  nlinarith

end IdentityFiltrationBound

open IdentityFiltrationBound in
theorem SymmetricPowerMatrix : A0 → A1 → CasimirIsRealScalar → A6 := by
  intro h0 h1 h3 n ε V _ _ E hE
  obtain ⟨κ, hκ⟩ := h3 n ε V E hE
  obtain ⟨-, -, -, h0c⟩ := h0 n ε V E hE
  obtain ⟨hmono, -, -, -, hcomm, hK2, -⟩ := h1 n ε V E hE
  have hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 :=
    fun w => (h0c κ hκ w).1
  have grow : ∀ k : ℕ, ∃ G : ℝ, 0 ≤ G ∧ ∀ μ v, 0 ≤ μ → Eig ε E μ v →
      N E k v ≤ G * Real.sqrt (1 + μ) ^ k * ‖v‖ := by
    intro k
    induction k with
    | zero =>
      refine ⟨(W n 0).card, Nat.cast_nonneg _, fun μ v _ _ => ?_⟩
      simp only [pow_zero, mul_one]
      calc N E 0 v = ∑ l ∈ W n 0, ‖wd E l v‖ := rfl
        _ ≤ ∑ l ∈ W n 0, ‖v‖ := Finset.sum_le_sum fun l hl => by
            have := mem_W.1 hl
            cases l with
            | nil => simp [wd]
            | cons p l => simp at this
        _ = _ := by simp
    | succ k ih =>
      obtain ⟨G, hG, hG'⟩ := ih
      have hc : ∀ l : List (Fin n × Fin n), ∃ c : ℝ, 0 ≤ c ∧ (l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v) := by
        intro l
        by_cases hl : l.length ≤ k
        · have hmem : wd E l ∈ U E k := hmono _ _ hl (Submodule.subset_span ⟨l, le_rfl, rfl⟩)
          have hin := hcomm 2 k _ hK2 _ hmem
          have h' : 2 + k - 1 = k + 1 := by omega
          rw [h'] at hin
          obtain ⟨c, hc, hc'⟩ := U_bound E (k + 1) _ hin
          exact ⟨c, hc, fun _ => hc'⟩
        · exact ⟨0, le_rfl, fun h => absurd h hl⟩
      choose c hc0 hc using hc
      have hC : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ (∑ l ∈ W n k, c l) * N E (k + 1) v :=
        fun l hl v => (hc l hl v).trans (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (mem_W.2 hl)) (N_nonneg _ _ _))
      have hC0 : 0 ≤ ∑ l ∈ W n k, c l := Finset.sum_nonneg fun i _ => hc0 i
      refine ⟨(2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
        ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * G, by positivity, fun μ v hμ hv => ?_⟩
      have hst := step E ε κ μ _ k hcas hC0 hC v hv hμ
      calc N E (k + 1) v ≤ _ := hst
        _ ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
            ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * Real.sqrt (1 + μ) *
              (G * Real.sqrt (1 + μ) ^ k * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hG' μ v hμ hv) (by positivity)
        _ = _ := by ring
  intro k u hu
  obtain ⟨c, hc, hc'⟩ := U_bound E k u hu
  obtain ⟨G, hG, hG'⟩ := grow k
  refine ⟨c * G, mul_nonneg hc hG, fun μ v hμ hv => ?_⟩
  calc ‖u v‖ ≤ c * N E k v := hc' v
    _ ≤ c * (G * Real.sqrt (1 + μ) ^ k * ‖v‖) := mul_le_mul_of_nonneg_left (hG' μ v hμ hv) hc
    _ = _ := by ring

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusOfBasic
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace FunctionalCalculusInner

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

theorem fc_basis (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (i : ι) :
    fc b μ φ (b i) = ((φ (μ i) : ℝ) : ℂ) • b i := by
  unfold fc
  exact b.constr_basis ℂ _ i

theorem repr_fc (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (v : V) (i : ι) :
    b.repr (fc b μ φ v) i = ((φ (μ i) : ℝ) : ℂ) * b.repr v i := by
  have key : (b.coord i).comp (fc b μ φ) = ((φ (μ i) : ℝ) : ℂ) • b.coord i := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, fc_basis, map_smul,
      LinearMap.smul_apply, Module.Basis.repr_self]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Finsupp.single_apply, hji]
  exact LinearMap.congr_fun key v

theorem inner_basis_left (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  classical
  have key : (innerₛₗ ℂ (b i) : V →ₗ[ℂ] ℂ) = b.coord i := by
    refine b.ext fun j => ?_
    show inner ℂ (b i) (b j) = b.repr (b j) i
    rw [Module.Basis.repr_self, orthonormal_iff_ite.mp hb i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  exact LinearMap.congr_fun key y

theorem inner_eq_sum (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (x y : V) (s : Finset ι)
    (hs : (b.repr x).support ⊆ s) :
    inner ℂ x y = ∑ i ∈ s, starRingEnd ℂ (b.repr x i) * b.repr y i := by
  have hx : x = ∑ i ∈ s, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs]
    intro i _
    simp
  conv_lhs => rw [hx]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_basis_left b hb]

theorem fc_id (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : Module.Basis ι ℂ V) (μ : ι → ℝ)
    (h : ∀ i, Eig ε E (μ i) (b i)) : fc b μ (fun x => x) = casimirK ε E :=
  b.ext fun i => by rw [fc_basis]; exact (h i).symm

theorem re_conj_mul (z : ℂ) (r : ℝ) : (starRingEnd ℂ z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := by
  rw [mul_left_comm, Complex.conj_mul']
  norm_cast

theorem re_inner_fc (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (w : V) :
    (inner ℂ w (fc b μ φ w)).re = ∑ i ∈ (b.repr w).support, φ (μ i) * ‖b.repr w i‖ ^ 2 := by
  rw [inner_eq_sum b hb w _ _ subset_rfl, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_fc, re_conj_mul]

end FunctionalCalculusInner

open FunctionalCalculusInner in
theorem functional_calculus_of_basic : A0 → FunctionalCalculusLaws := by
  intro _ n ε V _ _ E _ ι b μ hb
  have hid := fc_id ε E b μ hb.eig
  refine ⟨fun φ ν v hv => ?_, fun φ x y => ?_, fun φ ψ hφψ w => ?_, fun φ ψ => ?_, fun φ ψ => ?_,
    fun c => ?_, hid⟩
  · refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h1 : b.repr (casimirK ε E v) i = b.repr ((ν : ℂ) • v) i := by rw [show casimirK ε E v = (ν : ℂ) • v from hv]
    rw [← hid, repr_fc] at h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    rw [repr_fc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases h0 : b.repr v i = 0
    · simp [h0]
    · have : μ i = ν := by
        have := mul_right_cancel₀ h0 h1
        exact_mod_cast this
      rw [this]
  · have hs : (b.repr (fc b μ φ x)).support ⊆ (b.repr x).support := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [repr_fc] at hi
      exact right_ne_zero_of_mul hi
    rw [inner_eq_sum b hb.on _ _ _ hs, inner_eq_sum b hb.on _ _ _ subset_rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_fc, repr_fc, map_mul, Complex.conj_ofReal]
    ring
  · rw [re_inner_fc b hb.on, re_inner_fc b hb.on]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hφψ _ (hb.nonneg i)) (sq_nonneg _)
  · refine b.ext fun i => ?_
    simp only [fc_basis, LinearMap.add_apply, Complex.ofReal_add, add_smul]
  · refine b.ext fun i => ?_
    simp only [fc_basis, Module.End.mul_apply, map_smul, smul_smul, Complex.ofReal_mul, mul_comm]
  · refine b.ext fun i => ?_
    simp [fc_basis]

end PositivityTheory.CW

end
end

