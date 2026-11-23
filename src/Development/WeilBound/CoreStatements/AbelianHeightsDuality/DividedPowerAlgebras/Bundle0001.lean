module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsFilEqBot
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] {I : Ideal R} {J J' : Ideal B} {L : Ideal C}

theorem Sup.one_mem_fil (δ : DividedPowers J) : (1 : B) ∈ fil δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem Sup.dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem Sup.fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨l, h1, h2, rfl⟩, _, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, by simp⟩
  · rcases List.mem_append.1 hp with h | h
    exacts [h1 p h, h1' p h]
  · simp only [List.map_append, List.sum_append]; omega

theorem Sup.exists_fil_eq_bot {δ : DividedPowers J} (h : IsNilDP δ) : ∃ N, ∀ n, N ≤ n → fil δ n = ⊥ := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [fil, Ideal.span_eq_bot]
  rintro _ ⟨l, h1, h2, rfl⟩
  exact h l h1 (hn.trans h2)

theorem Sup.isPDNilpotent_of_family (δ : DividedPowers J) (s : Set B) (hs : J = Ideal.span s) (F : ℕ → Ideal B)
    (h0 : (1 : B) ∈ F 0) (hm : ∀ m n, F m * F n ≤ F (m + n)) (hg : ∀ x ∈ s, ∀ n, δ.dpow n x ∈ F n)
    (N : ℕ) (hN : ∀ n, N ≤ n → F n = ⊥) : IsNilDP δ := by
  subst hs
  have hdp : ∀ y ∈ Ideal.span s, ∀ n, δ.dpow n y ∈ F n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hg x hx
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [δ.dpow_zero (Ideal.zero_mem _)]; exact h0
      · rw [δ.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hm _ _ (Ideal.mul_mem_mul (ihx k.1) (ihy k.2))
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ Ideal.span s) →
      (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ F (l.map Prod.fst).sum := by
    intro l hl
    induction l with
    | nil => exact h0
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hm _ _ (Ideal.mul_mem_mul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq])))
  refine ⟨N, fun l hl h ↦ ?_⟩
  have := hprod l hl
  rwa [hN _ h, Ideal.mem_bot] at this

theorem Sup.sup_map_eq_span (f : R →+* B) : J ⊔ I.map f = Ideal.span ((J : Set B) ∪ f '' I) := by
  rw [Ideal.span_union, Ideal.span_eq]; rfl

theorem nil_sup (κ : DividedPowers I) (δ : DividedPowers J) (f : R →+* B) (δ' : DividedPowers J')
    (hJ : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B)) (h₂ : IsDPMorphism κ δ' f)
    (hκ : IsNilDP κ) (hδ : IsNilDP δ) : IsNilDP δ' := by
  obtain ⟨N₁, k₁⟩ := Sup.exists_fil_eq_bot hκ
  obtain ⟨N₂, k₂⟩ := Sup.exists_fil_eq_bot hδ
  let F : ℕ → Ideal B := fun n ↦ ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = n}, (fil κ p.1.1).map f * fil δ p.1.2
  have hF : ∀ a b n, a + b = n → (fil κ a).map f * fil δ b ≤ F n := fun a b n h ↦
    le_iSup (fun p : {p : ℕ × ℕ // p.1 + p.2 = n} ↦ (fil κ p.1.1).map f * fil δ p.1.2) ⟨(a, b), h⟩
  have one : (1 : B) ∈ (fil κ 0).map f := by
    simpa using Ideal.mem_map_of_mem f (Sup.one_mem_fil κ)
  refine Sup.isPDNilpotent_of_family δ' _ (hJ.trans (Sup.sup_map_eq_span f)) F ?_ (fun m n ↦ ?_) ?_ (N₁ + N₂) fun n hn ↦ ?_
  · simpa using hF 0 0 0 rfl (Ideal.mul_mem_mul one (Sup.one_mem_fil δ))
  · simp only [F, Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
    rintro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩
    refine le_trans ?_ (hF (c + a) (d + b) _ (by simp only at h h'; omega))
    rw [mul_mul_mul_comm, ← Ideal.map_mul]
    exact Ideal.mul_mono (Ideal.map_mono (Sup.fil_mul_le _ _ _)) (Sup.fil_mul_le _ _ _)
  · rintro x (hx | ⟨r, hr, rfl⟩) n
    · have := h₁.2 (n := n) x hx
      simp only [RingHom.id_apply] at this
      rw [this]
      simpa using hF 0 n n (zero_add n) (Ideal.mul_mem_mul one (Sup.dpow_mem_fil δ hx n))
    · rw [h₂.2 r hr]
      simpa using hF n 0 n rfl (Ideal.mul_mem_mul (Ideal.mem_map_of_mem f (Sup.dpow_mem_fil κ hr n)) (Sup.one_mem_fil δ))
  · simp only [F, iSup_eq_bot]
    rintro ⟨⟨a, b⟩, h⟩
    simp only at h ⊢
    by_cases ha : N₁ ≤ a
    · rw [k₁ a ha, Ideal.map_bot, Ideal.bot_mul]
    · rw [k₂ b (by omega), Ideal.mul_bot]

theorem isDPMorphism_sup (κ : DividedPowers I) (δ : DividedPowers J) (f : R →+* B) (δ' : DividedPowers J')
    (hJ : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B)) (h₂ : IsDPMorphism κ δ' f)
    (θ : DividedPowers L) (g : B →+* C) (k₁ : IsDPMorphism δ θ g) (k₂ : IsDPMorphism κ θ (g.comp f)) :
    IsDPMorphism δ' θ g := by
  refine IsDPMorphism.on_span δ' θ (hJ.trans (Sup.sup_map_eq_span f)) ?_ ?_
  · rintro x (hx | ⟨r, hr, rfl⟩)
    · exact k₁.1 (Ideal.mem_map_of_mem _ hx)
    · exact k₂.1 (Ideal.mem_map_of_mem _ hr)
  · rintro n x (hx | ⟨r, hr, rfl⟩)
    · have := h₁.2 (n := n) x hx
      simp only [RingHom.id_apply] at this
      rw [this]
      exact (k₁.2 x hx).symm
    · rw [h₂.2 r hr]
      exact (k₂.2 r hr).symm

end FubiniStudyChowHeightFormula₂.Adr
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {B : Type} [CommRing B]

theorem e_succ_mem_aug (Q : PDPoly B) (n : ℕ) : Q.e (n + 1) ∈ Q.aug := Ideal.subset_span ⟨n, rfl⟩

def liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    liftAlg Q c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem exists_lift_and_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 →
      (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) →
      ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧
    ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  intro B _ Q
  refine ⟨fun C _ f c h0 hm ↦ ?_, ?_⟩
  · letI := f.toAlgebra
    exact ⟨(liftAlg Q c h0 hm).toRingHom, fun b ↦ (liftAlg Q c h0 hm).commutes b,
      fun n ↦ liftAlg_e Q c h0 hm n⟩
  · let d : ℕ → B := fun n ↦ if n = 0 then 1 else 0
    have h0 : d 0 = 1 := by simp [d]
    have hm : ∀ m n, d m * d n = ((m + n).choose m : B) * d (m + n) := by
      intro m n
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [d, hm, hn]
    let ε := liftAlg Q d h0 hm
    have hε : ∀ n, ε (Q.e n) = d n := liftAlg_e Q d h0 hm
    have hmem : ∀ p, p - algebraMap B Q.P (ε p) ∈ Q.aug := by
      intro p
      have hp : p ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        rw [hε]
        rcases n with _ | n
        · simp [d, Q.e_zero]
        · simpa [d] using e_succ_mem_aug Q n
      | zero => simp
      | add x y _ _ hx hy =>
        have : x + y - algebraMap B Q.P (ε (x + y)) =
            (x - algebraMap B Q.P (ε x)) + (y - algebraMap B Q.P (ε y)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this]; exact add_mem hx hy
      | smul b x _ hx =>
        have : b • x - algebraMap B Q.P (ε (b • x)) = algebraMap B Q.P b * (x - algebraMap B Q.P (ε x)) := by
          rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
        rw [this]; exact Q.aug.mul_mem_left _ hx
    refine ⟨ε, fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩⟩
    · have hle : Q.aug ≤ RingHom.ker ε := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨n, rfl⟩
        simp [RingHom.mem_ker, hε, d]
      exact RingHom.mem_ker.1 (hle hp)
    · have := hmem p
      rwa [hp, map_zero, sub_zero] at this

end FubiniStudyChowHeightFormula₂.Adr
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries Finset

variable {B : Type} [CommRing B]

def ser (g : ℕ → B) (a : B) : B⟦X⟧ := PowerSeries.mk fun n ↦ a ^ n * g n

theorem ser_zero {g : ℕ → B} (h0 : g 0 = 1) : ser g 0 = 1 := by
  ext n
  rcases n with _ | n <;> simp [ser, h0, coeff_one]

theorem ser_add {g : ℕ → B} (hmul : ∀ m n, g m * g n = ((m + n).choose m : B) * g (m + n)) (a b : B) :
    ser g (a + b) = ser g a * ser g b := by
  ext n
  simp only [ser, coeff_mul, coeff_mk, (Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have := hmul p.1 p.2
  rw [e] at this
  rw [nsmul_eq_mul]
  linear_combination (-(a ^ p.1 * b ^ p.2)) * this

theorem ser_mul (g : ℕ → B) (a b : B) : ser g (a * b) = rescale a (ser g b) := by
  ext n
  simp only [ser, coeff_rescale, coeff_mk, mul_pow, mul_assoc]

def IsExp (f : B⟦X⟧) : Prop := ∀ m n, coeff m f * coeff n f = ((m + n).choose m : B) * coeff (m + n) f

theorem IsExp.mul {f g : B⟦X⟧} (hf : IsExp f) (hg : IsExp g) : IsExp (f * g) := by
  intro m n
  simp only [coeff_mul]
  have e : ((m + n).choose m : B) * ∑ p ∈ HasAntidiagonal.antidiagonal (m + n), coeff p.1 f * coeff p.2 g =
      ∑ i ∈ HasAntidiagonal.antidiagonal m, ∑ p ∈ HasAntidiagonal.antidiagonal (m + n),
        (p.1.choose i.1 : B) * (p.2.choose i.2 : B) * (coeff p.1 f * coeff p.2 g) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, Nat.add_choose_eq, ← Finset.sum_mul]
    push_cast
    rfl
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.HasAntidiagonal.mem_antidiagonal.1 hi
  rw [Finset.mul_sum]
  refine Finset.sum_of_injOn (fun k : ℕ × ℕ ↦ (i.1 + k.1, i.2 + k.2)) ?_ ?_ ?_ ?_
  · intro k _ l _ h
    simp only [Prod.mk.injEq, add_right_inj] at h
    exact Prod.ext h.1 h.2
  · intro k hk
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
  · intro p hp hn
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h1 : p.1 < i.1
    · simp [Nat.choose_eq_zero_of_lt h1]
    by_cases h2 : p.2 < i.2
    · simp [Nat.choose_eq_zero_of_lt h2]
    refine absurd ⟨(p.1 - i.1, p.2 - i.2), Finset.mem_coe.2 (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)), ?_⟩ hn
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · intro k _
    have a := hf i.1 k.1
    have b := hg i.2 k.2
    simp only
    linear_combination (coeff i.2 g * coeff k.2 g) * a + (((i.1 + k.1).choose i.1 : B) * coeff (i.1 + k.1) f) * b

theorem pre_of_gens (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B) (h0 : ∀ i, g i 0 = 1)
    (h1 : ∀ i, g i 1 = x i) (hm : ∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x))
    (hmul : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (hrel : ∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 →
      (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) :
    ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  classical
  let Φ : (ι →₀ B) → B⟦X⟧ := fun c ↦ c.prod fun i a ↦ ser (g i) a
  let l : (ι →₀ B) →ₗ[B] B := Finsupp.linearCombination B x
  have hl : ∀ c, l c = c.sum fun i a ↦ a * x i := fun c ↦ rfl
  have Φadd : ∀ c c', Φ (c + c') = Φ c * Φ c' := fun c c' ↦
    Finsupp.prod_add_index' (fun i ↦ ser_zero (h0 i)) fun i ↦ ser_add (hmul i)
  have Φ0 : Φ 0 = 1 := Finsupp.prod_zero_index
  have Φs : ∀ i a, Φ (Finsupp.single i a) = ser (g i) a := fun i a ↦
    Finsupp.prod_single_index (ser_zero (h0 i))
  have Φwd : ∀ c c', l c = l c' → Φ c = Φ c' := fun c c' h ↦ by
    have : Φ (c - c') = 1 := hrel _ (by rw [← hl, map_sub, h, sub_self])
    rw [← sub_add_cancel c c', Φadd, this, one_mul]
  have hJ : ∀ y, y ∈ Ideal.span (Set.range x) ↔ ∃ c, l c = y := fun y ↦
    Finsupp.mem_span_range_iff_exists_finsupp
  have Φsm : ∀ a c, Φ (a • c) = rescale a (Φ c) := fun a c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => rw [smul_zero, Φ0, map_one]
    | add c c' h h' => rw [smul_add, Φadd, Φadd, h, h', map_mul]
    | single i b => rw [Finsupp.smul_single, Φs, Φs, smul_eq_mul, ser_mul]
  have key : ∀ c, coeff 0 (Φ c) = 1 ∧ coeff 1 (Φ c) = l c ∧
      (∀ n, n ≠ 0 → coeff n (Φ c) ∈ Ideal.span (Set.range x)) ∧ IsExp (Φ c) := fun c ↦ by
    induction c using Finsupp.induction_linear with
    | zero =>
      rw [Φ0]
      refine ⟨by simp, by simp, fun n hn ↦ by simp [coeff_one, hn], fun m n ↦ ?_⟩
      rcases m with _ | m <;> rcases n with _ | n <;> simp [coeff_one]
    | add c c' h h' =>
      rw [Φadd]
      refine ⟨by rw [coeff_mul]; simp [h.1, h'.1, -coeff_zero_eq_constantCoeff], ?_, fun n hn ↦ ?_,
        h.2.2.2.mul h'.2.2.2⟩
      · rw [coeff_mul, Finset.Nat.antidiagonal_succ]
        simp [h.1, h'.1, h.2.1, h'.2.1, -coeff_zero_eq_constantCoeff, add_comm]
      · rw [coeff_mul]
        refine Ideal.sum_mem _ fun p hp ↦ ?_
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        by_cases h1 : p.1 = 0
        · exact Ideal.mul_mem_left _ _ (h'.2.2.1 _ (by omega))
        · exact Ideal.mul_mem_right _ _ (h.2.2.1 _ h1)
    | single i b =>
      rw [Φs]
      refine ⟨by simp [ser, h0], by simp [ser, h1, l], fun n hn ↦ ?_, fun m n ↦ ?_⟩
      · rw [ser, coeff_mk]; exact Ideal.mul_mem_left _ _ (hm i n hn)
      · simp only [ser, coeff_mk, pow_add]
        linear_combination (b ^ m * b ^ n) * hmul i m n
  let γ : ℕ → B → B := fun n y ↦ if h : ∃ c, l c = y then coeff n (Φ h.choose) else 0
  have hγ : ∀ n c, γ n (l c) = coeff n (Φ c) := fun n c ↦ by
    have h : ∃ c', l c' = l c := ⟨c, rfl⟩
    simp only [γ, dif_pos h, Φwd _ _ h.choose_spec]
  refine ⟨γ, ⟨fun n y hy ↦ dif_neg fun h ↦ hy ((hJ y).2 h), ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i n ↦ ?_⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ, (key c).1]
  · intro y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ, (key c).2.1]
  · intro n hn y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ]; exact (key c).2.2.1 n hn
  · intro n y hy z hz
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    obtain ⟨c', rfl⟩ := (hJ z).1 hz
    simp only [← map_add (f := _), hγ, Φadd, coeff_mul]
  · intro n a y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [← smul_eq_mul, ← map_smul, hγ, hγ, Φsm, coeff_rescale]
  · intro m n y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    simp only [hγ]
    exact (key c).2.2.2 m n
  · have : x i = l (Finsupp.single i 1) := by simp [l]
    rw [this, hγ, Φs]; simp [ser]

end FubiniStudyChowHeightFormula₂.Adr
end
end

