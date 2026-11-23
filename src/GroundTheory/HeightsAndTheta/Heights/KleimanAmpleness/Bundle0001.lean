module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

namespace EulerSES

variable {F : Type} [Field F] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]

def cyc (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) (n : ℕ) : Submodule F (A n) :=
  C n ⊓ LinearMap.ker (d n)

def bnd (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) : (n : ℕ) → Submodule F (A n)
  | 0 => ⊥
  | n + 1 => (C n).map (d n)

abbrev coh (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) (n : ℕ) : Type :=
  ↥(cyc C d n) ⧸ (bnd C d n).comap (cyc C d n).subtype

end EulerSES

open EulerSES

def EulerSES.Statement : Prop :=
  ∀ (F : Type) [Field F] (A B C : ℕ → Type) [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module F (C n)]
    (CA : ∀ n, Submodule F (A n)) (CB : ∀ n, Submodule F (B n)) (CC : ∀ n, Submodule F (C n))
    (dA : ∀ n, A n →ₗ[F] A (n + 1)) (dB : ∀ n, B n →ₗ[F] B (n + 1)) (dC : ∀ n, C n →ₗ[F] C (n + 1))
    (f : ∀ n, A n →ₗ[F] B n) (g : ∀ n, B n →ₗ[F] C n) (N : ℕ),
    (∀ n, ∀ x ∈ CA n, dA n x ∈ CA (n + 1)) → (∀ n, ∀ x ∈ CB n, dB n x ∈ CB (n + 1)) →
    (∀ n, ∀ x ∈ CC n, dC n x ∈ CC (n + 1)) →
    (∀ n, ∀ x ∈ CA n, dA (n + 1) (dA n x) = 0) → (∀ n, ∀ x ∈ CB n, dB (n + 1) (dB n x) = 0) →
    (∀ n, ∀ x ∈ CC n, dC (n + 1) (dC n x) = 0) →
    (∀ n, ∀ x ∈ CA n, f n x ∈ CB n) → (∀ n, ∀ y ∈ CB n, g n y ∈ CC n) →
    (∀ n, ∀ x ∈ CA n, dB n (f n x) = f (n + 1) (dA n x)) →
    (∀ n, ∀ y ∈ CB n, dC n (g n y) = g (n + 1) (dB n y)) →
    (∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0) →
    (∀ n, ∀ x ∈ CA n, g n (f n x) = 0) →
    (∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y) →
    (∀ n, ∀ z ∈ CC n, ∃ y ∈ CB n, g n y = z) →
    (∀ n, FiniteDimensional F (coh CA dA n)) → (∀ n, FiniteDimensional F (coh CB dB n)) →
    (∀ n, FiniteDimensional F (coh CC dC n)) →
    Subsingleton (coh CA dA (N + 1)) →
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CB dB n) : ℤ) =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CA dA n) : ℤ) +
        ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CC dC n) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def PolyOfDiffsExact.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℚ),
    (∀ k, ∃ q : MvPolynomial K ℚ, ∀ m : K → ℤ, h m - h (m - Pi.single k 1) = eval (fun j => (m j : ℚ)) q) →
    ∃ p : MvPolynomial K ℚ, ∀ m : K → ℤ, h m = eval (fun j => (m j : ℚ)) p

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KerAltSucc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def Staircase.bdry {R : Type} [CommRing R] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (d : ∀ n, A n →ₗ[R] A (n + 1)) : ∀ n, Submodule R (A n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d n)

abbrev Staircase.H {R : Type} [CommRing R] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (d : ∀ n, A n →ₗ[R] A (n + 1)) (n : ℕ) : Type :=
  LinearMap.ker (d n) ⧸ (Staircase.bdry d n).comap (LinearMap.ker (d n)).subtype

def Staircase.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (D : ℕ → ℕ → Type) [∀ p q, AddCommGroup (D p q)] [∀ p q, Module R (D p q)]
    (v : ∀ p q, D p q →ₗ[R] D (p + 1) q) (h : ∀ p q, D p q →ₗ[R] D p (q + 1))
    (A : ℕ → Type) [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] (dA : ∀ p, A p →ₗ[R] A (p + 1))
    (a : ∀ p, A p →ₗ[R] D p 0)
    (C : ℕ → Type) [∀ q, AddCommGroup (C q)] [∀ q, Module R (C q)] (dC : ∀ q, C q →ₗ[R] C (q + 1))
    (c : ∀ q, C q →ₗ[R] D 0 q),
    (∀ p q, (v p (q + 1)).comp (h p q) = (h (p + 1) q).comp (v p q)) →
    (∀ p, (a (p + 1)).comp (dA p) = (v p 0).comp (a p)) →
    (∀ q, (c (q + 1)).comp (dC q) = (h 0 q).comp (c q)) →
    (∀ p, LinearMap.ker (a p) = ⊥) →
    (∀ p, LinearMap.ker (h p 0) = LinearMap.range (a p)) →
    (∀ p q, LinearMap.ker (h p (q + 1)) = LinearMap.range (h p q)) →
    (∀ q, LinearMap.ker (c q) = ⊥) →
    (∀ q, LinearMap.ker (v 0 q) = LinearMap.range (c q)) →
    (∀ p q, LinearMap.ker (v (p + 1) q) = LinearMap.range (v p q)) →
    ∀ n, Nonempty (Staircase.H dA n ≃ₗ[R] Staircase.H dC n)

def Staircase.alt (R : Type) [CommRing R] (m : ℕ) : R →ₗ[R] R :=
  if m % 2 = 1 then LinearMap.id else 0

theorem Staircase.alt_comm (R : Type) [CommRing R] (p q : ℕ) :
    (Staircase.alt R p).comp (Staircase.alt R q) = (Staircase.alt R q).comp (Staircase.alt R p) := by
  unfold Staircase.alt
  split_ifs <;> simp

theorem Staircase.ker_alt_zero (R : Type) [CommRing R] :
    LinearMap.ker (Staircase.alt R 0) = LinearMap.range (LinearMap.id : R →ₗ[R] R) := by
  simp [Staircase.alt]

theorem Staircase.ker_alt_succ (R : Type) [CommRing R] (q : ℕ) :
    LinearMap.ker (Staircase.alt R (q + 1)) = LinearMap.range (Staircase.alt R q) := by
  unfold Staircase.alt
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · rw [if_pos (by omega), if_neg (by omega)]
    simp
  · rw [if_neg (by omega), if_pos (by omega)]
    simp

theorem Staircase.hyps :
    (∀ p q : ℕ, (Staircase.alt ℤ p).comp (Staircase.alt ℤ q) = (Staircase.alt ℤ q).comp (Staircase.alt ℤ p)) ∧
    (∀ p : ℕ, (LinearMap.id : ℤ →ₗ[ℤ] ℤ).comp (Staircase.alt ℤ p) = (Staircase.alt ℤ p).comp LinearMap.id) ∧
    LinearMap.ker (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = ⊥ ∧
    LinearMap.ker (Staircase.alt ℤ 0) = LinearMap.range (LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
    (∀ q : ℕ, LinearMap.ker (Staircase.alt ℤ (q + 1)) = LinearMap.range (Staircase.alt ℤ q)) :=
  ⟨Staircase.alt_comm ℤ, fun p => by simp, LinearMap.ker_id, Staircase.ker_alt_zero ℤ, Staircase.ker_alt_succ ℤ⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqBundleLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open scoped Pointwise

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]

section Local

variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)

theorem exists_sum_mul_pow_eq_one (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (n : ℕ) : ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ n = 1 := by
  let f' : Fin k → A := fun l => ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.span, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, Subtype.ext ?_⟩
    simpa [f'] using hs
  have h1 := Ideal.span_pow_eq_top _ htop n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.span, Submodule.mem_span_range_iff_exists_fun] at h1
  obtain ⟨d, hd⟩ := h1
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [f'] using this

theorem mem_of_forall_pow_mul_mem (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (P : Submodule A Ω) {z : Ω} (hz : ∀ l, ∃ m : ℕ, f l ^ m * z ∈ P) : z ∈ P := by
  choose m hm using hz
  obtain ⟨d, hd, hsum⟩ := exists_sum_mul_pow_eq_one A f c hf hc hs (Finset.univ.sup m)
  have key : z = ∑ l, (⟨d l * f l ^ (Finset.univ.sup m - m l), mul_mem (hd l) (pow_mem (hf l) _)⟩ : A) •
      (f l ^ m l * z) := by
    simp only [Subalgebra.smul_def, smul_eq_mul]
    calc z = (∑ l, d l * f l ^ Finset.univ.sup m) * z := by rw [hsum, one_mul]
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
        ring
  rw [key]
  exact sum_mem fun l _ => P.smul_mem _ (hm l)

theorem fg_and_invertible_of_frame (L : Submodule A Ω) (b : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1) (hb : ∀ l, b l ≠ 0)
    (hL : ∀ l e, (∃ n : ℕ, f l ^ n * e ∈ L) ↔ ∃ a : Ω, (∃ n : ℕ, f l ^ n * a ∈ A) ∧ e = a * b l) :
    L.FG ∧ ∃ L' : Submodule A Ω, L * L' = 1 := by
  have hgen : ∀ l, ∃ n : ℕ, f l ^ n * b l ∈ L := fun l =>
    (hL l (b l)).2 ⟨1, ⟨0, by rw [pow_zero, one_mul]; exact one_mem A⟩, (one_mul _).symm⟩
  choose n hn using hgen
  set g : Fin k → Ω := fun l => f l ^ n l * b l with hg
  have hloc : ∀ l, ∀ e ∈ L, ∃ a : Ω, (∃ m : ℕ, f l ^ m * a ∈ A) ∧ e = a * b l := fun l e he =>
    (hL l e).1 ⟨0, by rw [pow_zero, one_mul]; exact he⟩
  have hLG : L = Submodule.span A (Set.range g) := by
    apply le_antisymm
    · intro e he
      apply mem_of_forall_pow_mul_mem A f c hf hc hs
      intro l
      obtain ⟨a, ⟨m, hm⟩, rfl⟩ := hloc l e he
      refine ⟨m + n l, ?_⟩
      have : f l ^ (m + n l) * (a * b l) = (⟨f l ^ m * a, hm⟩ : A) • g l := by
        rw [Subalgebra.smul_def, smul_eq_mul, hg]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hn l
  refine ⟨hLG ▸ Submodule.fg_span (Set.finite_range g), 1 / L, le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro p hp q hq
    rw [mul_comm]
    exact (Submodule.mem_div_iff_forall_mul_mem.1 hq) p hp
  · rw [Submodule.one_le]
    apply mem_of_forall_pow_mul_mem A f c hf hc hs
    intro l
    have hbd : ∀ s, ∃ m : ℕ, f l ^ m * (g s / b l) ∈ A := by
      intro s
      obtain ⟨a, ⟨m, hm⟩, hgs⟩ := hloc l (g s) (hn s)
      refine ⟨m, ?_⟩
      rw [hgs, mul_div_assoc, div_self (hb l), mul_one]
      exact hm
    choose M hM using hbd
    set K := Finset.univ.sup M with hK
    have hy : f l ^ K / b l ∈ 1 / L := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      intro e he
      rw [hLG] at he
      induction he using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨s, rfl⟩ := hz
        rw [Submodule.mem_one]
        refine ⟨⟨f l ^ (K - M s) * (f l ^ M s * (g s / b l)), mul_mem (pow_mem (hf l) _) (hM s)⟩, ?_⟩
        change f l ^ (K - M s) * (f l ^ M s * (g s / b l)) = f l ^ K / b l * g s
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ s))]
        ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
      | smul a u _ hu =>
        have : f l ^ K / b l * (a • u) = a • (f l ^ K / b l * u) := by
          rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul]
          ring
        rw [this]
        exact Submodule.smul_mem _ a hu
    refine ⟨n l + K, ?_⟩
    have : f l ^ (n l + K) * 1 = g l * (f l ^ K / b l) := by
      rw [hg, mul_one, pow_add]
      field_simp [hb l]
    rw [this]
    exact Submodule.mul_mem_mul (hn l) hy

end Local

section Lift

variable {A B : Subalgebra S Ω}

theorem span_span_of_le (hAB : A ≤ B) (T : Set Ω) :
    Submodule.span B (Submodule.span A T : Set Ω) = Submodule.span B T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul a u _ hu => exact Submodule.smul_mem _ (⟨a, hAB a.2⟩ : B) hu
  · exact Submodule.span_mono Submodule.subset_span

theorem fg_span_of_le (hAB : A ≤ B) {L : Submodule A Ω} (hL : L.FG) :
    (Submodule.span B (L : Set Ω)).FG := by
  obtain ⟨T, rfl⟩ := hL
  rw [span_span_of_le hAB]
  exact Submodule.fg_span T.finite_toSet

theorem mul_span_eq_one_of_le (hAB : A ≤ B) {L L' : Submodule A Ω} (h : L * L' = 1) :
    Submodule.span B (L : Set Ω) * Submodule.span B (L' : Set Ω) = 1 := by
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have hpq : p * q ∈ L * L' := Submodule.mul_mem_mul hp hq
    rw [h, Submodule.mem_one] at hpq
    obtain ⟨a, ha⟩ := hpq
    exact Submodule.mem_one.2 ⟨⟨a, hAB a.2⟩, ha⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ L * L' := h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [Submodule.mul_eq_span_mul_set] at h1
    exact (span_span_of_le hAB ((L : Set Ω) * (L' : Set Ω))).le (Submodule.subset_span h1)

end Lift

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

