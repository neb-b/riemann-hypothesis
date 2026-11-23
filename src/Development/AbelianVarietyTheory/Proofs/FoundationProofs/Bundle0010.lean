module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
section
noncomputable section

open Classical
open scoped BigOperators

namespace GlobalTheory.FinWeil

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

structure IsHeis (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) : Prop where
  sg_sg : ∀ r, σ (σ r) = r
  w_add : w + σ w = 1
  add_left : ∀ x y z, γ (x + y) z = γ x z * γ y z
  add_right : ∀ x y z, γ x (y + z) = γ x y * γ x z
  alt : ∀ x, γ x x = 1
  adj : ∀ r x y, γ (r • x) y = γ x (σ r • y)
  zero : ∀ v, W 0 v = v
  comp : ∀ x y v, W x (W y v) = γ (w • x) y • W (x + y) v

def SelfDual (γ : X → X → ℂ) (A : Submodule R X) : Prop := ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1

def Fixes (W : X → M →ₗ[ℂ] M) (A : Submodule R X) (v : M) : Prop := ∀ a ∈ A, W a v = v

def idx (A B : Submodule R X) : ℕ := A.toAddSubgroup.relIndex B.toAddSubgroup

def sumOp (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  ∑ᶠ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, W ((Quotient.out q : B.toAddSubgroup) : X) v

def normOp (lam : ℕ →* ℂ) (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  (lam (idx A B))⁻¹ • sumOp W A B v

def GoodNorm (σ : R →+* R) (lam : ℕ →* ℂ) : Prop :=
  (∀ n, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
    lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧
    ((∀ r ∈ P, σ r ∈ P) → lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P)

def Adj (A B : Submodule R X) : Prop :=
  ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x}

namespace IsHeis

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h

theorem skew (x y : X) : γ x y * γ y x = 1 := by
  have h1 := h.alt (x + y)
  rw [h.add_left, h.add_right, h.add_right, h.alt, h.alt] at h1
  simpa using h1

theorem ne_zero (x y : X) : γ x y ≠ 0 := left_ne_zero_of_mul_eq_one (h.skew x y)

theorem zero_left (y : X) : γ 0 y = 1 := by
  have h1 := h.add_left 0 0 y
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero 0 y)).1 h1.symm

theorem zero_right (x : X) : γ x 0 = 1 := by
  have h1 := h.add_right x 0 0
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero x 0)).1 h1.symm

theorem neg_left (x y : X) : γ (-x) y = (γ x y)⁻¹ := by
  have h1 := h.add_left (-x) x y
  rw [neg_add_cancel, h.zero_left] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem neg_right (x y : X) : γ x (-y) = (γ x y)⁻¹ := by
  have h1 := h.add_right x (-y) y
  rw [neg_add_cancel, h.zero_right] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem swap (x y : X) : γ y x = (γ x y)⁻¹ := eq_inv_of_mul_eq_one_right (h.skew x y)

theorem swap_eq_one {x y : X} (hxy : γ x y = 1) : γ y x = 1 := by rw [h.swap, hxy, inv_one]

theorem nsmul_left (n : ℕ) (x y : X) : γ (n • x) y = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_left]
  | succ n ih => rw [succ_nsmul, h.add_left, ih, pow_succ]

theorem nsmul_right (n : ℕ) (x y : X) : γ x (n • y) = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_right]
  | succ n ih => rw [succ_nsmul, h.add_right, ih, pow_succ]

theorem comm (x y : X) (v : M) : W x (W y v) = γ x y • W y (W x v) := by
  have h1 : γ (w • x) y = γ x y * γ (w • y) x := by
    have h2 : γ x y = γ (w • x) y * γ (σ w • x) y := by rw [← h.add_left, ← add_smul, h.w_add, one_smul]
    rw [h2, h.adj (σ w), h.sg_sg, mul_assoc, h.skew, mul_one]
  rw [h.comp, h.comp, smul_smul, h1, add_comm]

theorem iso {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) : γ x y = 1 := (hA x).1 hx y hy

theorem comp_of_mem {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) (v : M) :
    W x (W y v) = W (x + y) v := by
  rw [h.comp, h.iso hA (A.smul_mem w hx) hy, one_smul]

theorem neg_comp (x : X) (v : M) : W (-x) (W x v) = γ (w • -x) x • v := by
  rw [h.comp, neg_add_cancel, h.zero]

end IsHeis

end GlobalTheory.FinWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
section
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.OnePoint

universe u v w

section Algebra

variable {K : Type u} [Field K]

theorem exists_algHom_of_isIntegrallyClosedIn {L : Type w} [Field L] [Algebra K L]
    [IsIntegrallyClosedIn K L] {A : Type v} [CommRing A] [Algebra K A] [Algebra.IsIntegral K A]
    (φ : A →ₐ[K] L) : ∃ ψ : A →ₐ[K] K, (Algebra.ofId K L).comp ψ = φ := by
  have hmem : ∀ a : A, φ a ∈ (Algebra.ofId K L).range := fun a ↦
    (isIntegrallyClosedIn_iff.mp ‹_›).2 ((Algebra.IsIntegral.isIntegral (R := K) a).map φ)
  let e := AlgEquiv.ofInjective (Algebra.ofId K L) (algebraMap K L).injective
  refine ⟨(e.symm : _ →ₐ[K] K).comp (φ.codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict _ hmem a))

end Algebra

section Scheme

variable {K : Type u} [Field K]

theorem epi_of_nonempty {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g :=
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective g

theorem point_ext {X T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K))
    {s s' : Spec (.of K) ⟶ X} (h : g ≫ s = g ≫ s') : s = s' :=
  have := epi_of_nonempty g
  (cancel_epi g).mp h

theorem exists_section_of_locallyQuasiFinite {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ F) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ x₀ : Spec (.of K) ⟶ F, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₀ = x ∧
      x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₁ = x →
        x₁ = x₀ := by
  suffices H : ∃ x₀ : Spec (.of K) ⟶ F,
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₀ = x by
    obtain ⟨x₀, h₀⟩ := H
    refine ⟨x₀, h₀, point_ext (Spec.map (CommRingCat.ofHom (algebraMap K L))) ?_,
      fun x₁ h₁ ↦ point_ext _ (h₁.trans h₀.symm)⟩
    rw [reassoc_of% h₀, hx, Category.comp_id]
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (Classical.arbitrary _))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨q, hq.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hqf : φ.hom.QuasiFinite := by
    have : LocallyQuasiFinite (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.QuasiFinite K A := hqf
  have : Module.Finite K A := .of_quasiFinite
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  let a' : A →ₐ[K] L := ⟨a.hom, fun c ↦ DFunLike.congr_fun hc c⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIntegrallyClosedIn a'
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext t
  exact DFunLike.congr_fun hψ t

end Scheme
end GlobalTheory.OnePoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyNumeratorCoeffNormLeOne
section
open Polynomial

namespace GlobalTheory

theorem exists_gauss_size_polynomial (K : Type) [NormedField K] [IsUltrametricDist K] :
    ∃ G : K[X] → ℝ, (∀ p, 0 ≤ G p) ∧ (∀ p i, ‖p.coeff i‖ ≤ G p) ∧
      (∀ p r, (∀ i, ‖p.coeff i‖ ≤ r) → G p ≤ r) ∧
      (∀ p q, G (p * q) = G p * G q) ∧ (∀ p q, G (p + q) ≤ max (G p) (G q)) ∧
      (∀ a, G (C a) = ‖a‖) ∧ G X = 1 := by
  let v : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have hv : ∀ a, v a = ‖a‖ := fun _ => rfl
  have hna : IsNonarchimedean v := fun a b => IsUltrametricDist.norm_add_le_max a b
  refine ⟨gaussNorm v 1, fun p => gaussNorm_nonneg v p zero_le_one, fun p i => ?_,
    fun p r hr => ?_, fun p q => gaussNorm_mul hna one_pos p q,
    fun p q => isNonarchimedean_gaussNorm v hna zero_le_one p q, fun a => ?_, ?_⟩
  · simpa [hv] using le_gaussNorm v p zero_le_one i
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v 1 p
    rw [hi, hv, one_pow, mul_one]
    exact hr i
  · rw [gaussNorm_C, hv]
  · rw [← monomial_one_one_eq_X, gaussNorm_monomial, hv]
    simp

theorem isogeny_numerator_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (A B A' B' : K) (n h : K[X]),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖A'‖ ≤ 1 → ‖B'‖ ≤ 1 → (∀ i, ‖h.coeff i‖ ≤ 1) →
      (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
        = n ^ 3 + C A' * n * h ^ 4 + C B' * h ^ 6 → ∀ i, ‖n.coeff i‖ ≤ 1 := by
  intro K _ _ A B A' B' n h hA hB hA' hB' hh heq
  obtain ⟨G, h0, hle, hub, hmul, hadd, hC, hX⟩ := exists_gauss_size_polynomial K
  have hone : G 1 = 1 := by simpa using hC 1
  have hpow : ∀ p (k : ℕ), G (p ^ k) = G p ^ k := by
    intro p k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hneg : ∀ p, G (-p) ≤ G p := fun p =>
    hub _ _ fun i => by rw [coeff_neg, norm_neg]; exact hle p i
  have hadd' : ∀ p q r, G p ≤ r → G q ≤ r → G (p + q) ≤ r := fun p q r hp hq =>
    (hadd p q).trans (max_le hp hq)
  have hsub : ∀ p q r, G p ≤ r → G q ≤ r → G (p - q) ≤ r := fun p q r hp hq => by
    rw [sub_eq_add_neg]
    exact hadd' _ _ _ hp ((hneg q).trans hq)
  have hmul' : ∀ p q r s, G p ≤ r → G q ≤ s → G (p * q) ≤ r * s := fun p q r s hp hq => by
    rw [hmul]
    exact mul_le_mul hp hq (h0 q) ((h0 p).trans hp)
  have hpow' : ∀ p r (k : ℕ), G p ≤ r → G (p ^ k) ≤ r ^ k := fun p r k hp => by
    rw [hpow]
    exact pow_le_pow_left₀ (h0 p) hp k
  have hder : ∀ p, G (derivative p) ≤ G p := fun p =>
    hub _ _ fun i => by
      rw [coeff_derivative, norm_mul]
      have h1 : ‖((i : K) + 1)‖ ≤ 1 := by
        exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (i + 1)
      calc ‖p.coeff (i + 1)‖ * ‖((i : K) + 1)‖ ≤ G p * 1 :=
            mul_le_mul (hle p _) h1 (norm_nonneg _) (h0 p)
        _ = G p := mul_one _
  have hh1 : G h ≤ 1 := hub _ _ hh
  suffices hn : G n ≤ 1 from fun i => (hle n i).trans hn
  by_contra hg
  push Not at hg
  set g := G n with hgdef
  have hX1 : G X ≤ 1 := hX.le
  have hcub : G (X ^ 3 + C A * X + C B) ≤ 1 := by
    refine hadd' _ _ _ (hadd' _ _ _ ?_ ?_) ?_
    · simpa using hpow' X 1 3 hX1
    · simpa using hmul' (C A) X 1 1 (by rw [hC]; exact hA) hX1
    · rw [hC]; exact hB
  have h2n : G (2 * n) ≤ g := by
    rw [two_mul]
    exact hadd' _ _ _ le_rfl le_rfl
  have hW : G (derivative n * h - 2 * n * derivative h) ≤ g := by
    refine hsub _ _ _ ?_ ?_
    · simpa using hmul' _ _ g 1 (hder n) hh1
    · simpa using hmul' _ _ g 1 h2n ((hder h).trans hh1)
  have hL : G ((X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2)
      ≤ g ^ 2 := by
    simpa using hmul' _ _ 1 (g ^ 2) hcub (hpow' _ g 2 hW)
  have hgg : g ≤ g ^ 2 := by nlinarith
  have h1g : 1 ≤ g ^ 2 := hg.le.trans hgg
  have hA2 : G (C A' * n * h ^ 4) ≤ g ^ 2 := by
    refine le_trans ?_ hgg
    simpa using hmul' _ _ (1 * g) (1 ^ 4)
      (hmul' (C A') n 1 g (by rw [hC]; exact hA') le_rfl) (hpow' h 1 4 hh1)
  have hB2 : G (C B' * h ^ 6) ≤ g ^ 2 := by
    refine le_trans ?_ h1g
    simpa using hmul' (C B') _ 1 (1 ^ 6) (by rw [hC]; exact hB') (hpow' h 1 6 hh1)
  have hn3 : n ^ 3 = (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
      - C A' * n * h ^ 4 - C B' * h ^ 6 := by
    rw [heq]; ring
  have h3 : G (n ^ 3) ≤ g ^ 2 := by
    rw [hn3]
    exact hsub _ _ _ (hsub _ _ _ hL hA2) hB2
  rw [hpow, ← hgdef] at h3
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterateDerivativeFunMulSubstLeibniz
section
open Polynomial

namespace GlobalTheory

theorem iterate_derivation_mul_antidiagonal {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (D : Derivation R S S) (a b : S) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : n.choose ij.2 = n.choose ij.1 := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, map_nsmul, Derivation.leibniz, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    simp only [smul_eq_mul, ← nsmul_add]
    congr 1
    ring

theorem iterate_derivativeFun_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      (((PowerSeries.derivativeFun)^[l] (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1), l.choose p •
          ((((PowerSeries.derivativeFun)^[p] φ).subst a : PowerSeries k) *
            ((PowerSeries.derivativeFun)^[l - p] ψ).subst a) := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  have hit : ∀ (n : ℕ) (f : PowerSeries k),
      (PowerSeries.derivativeFun)^[n] f = (⇑(PowerSeries.derivative (R := k)))^[n] f := by
    intro n f
    induction n generalizing f with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      rfl
  simp only [hit]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [iterate_derivation_mul_antidiagonal,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => l.choose i • ((⇑(PowerSeries.derivative (R := k)))^[i] φ *
        (⇑(PowerSeries.derivative (R := k)))^[j] ψ)) l,
    ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_nsmul, map_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableBoundedMulOfSummableNormSq
section
open Complex Filter Topology

namespace GlobalTheory

theorem lSeriesSummable_bounded_mul_of_summable_normSq :
    ∀ (e : ℕ) (θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => θ n * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e θ g s he hs hθ hg
  have h1 := hg s hs
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ ((2 * (e : ℝ) + s) - 1) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) ?_
  intro n
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have e1 : (((2 * e + 1 : ℕ) : ℝ) + s) = (2 * (e : ℝ) + s) + 1 := by push_cast; ring
    rw [Complex.ofReal_re, e1, Real.rpow_add_one hn'.ne', Real.rpow_sub_one hn'.ne']
    have hN : (0 : ℝ) < (n : ℝ) ^ (2 * (e : ℝ) + s) := Real.rpow_pos_of_pos hn' _
    generalize (n : ℝ) ^ (2 * (e : ℝ) + s) = N at hN ⊢
    have hb : ‖θ n * g n‖ ≤ ‖g n‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθ n)
    calc ‖θ n * g n‖ / N ≤ ‖g n‖ / N := by gcongr
      _ ≤ (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 := by
        have : (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 - ‖g n‖ / N
            = (‖g n‖ - n) ^ 2 / (2 * N * n) := by field_simp; ring
        have h3 : 0 ≤ (‖g n‖ - n) ^ 2 / (2 * N * n) := by positivity
        linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPow
section
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem powerSeries_pow_eq_expand_zmod (p : ℕ) [hp : Fact p.Prime] (g : PowerSeries (ZMod p)) :
    g ^ p = PowerSeries.expand p hp.out.ne_zero g := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) (f := g) p hp.out.ne_zero
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

theorem powerSeries_eq_sum_X_pow_mul_pow (p : ℕ) [hp : Fact p.Prime] (F : PowerSeries (ZMod p)) :
    ∃ G : Fin p → PowerSeries (ZMod p),
      F = ∑ j : Fin p, PowerSeries.X ^ (j : ℕ) * G j ^ p := by
  have hp0 : 0 < p := hp.out.pos
  refine ⟨fun j => PowerSeries.mk fun i => PowerSeries.coeff (p * i + j) F, ?_⟩
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [powerSeries_pow_eq_expand_zmod, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_expand]
  rw [Finset.sum_eq_single (⟨n % p, Nat.mod_lt n hp0⟩ : Fin p)]
  · have h1 : n % p ≤ n := Nat.mod_le n p
    have h2 : p ∣ n - n % p := Nat.dvd_sub_mod n
    simp only [h1, h2, if_true, PowerSeries.coeff_mk]
    congr 1
    rw [Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro j _ hj
    split_ifs with h1 h2
    · exfalso
      apply hj
      ext
      simp only
      have hj' : (j : ℕ) < p := j.2
      obtain ⟨c, hc⟩ := h2
      have : n = p * c + j := by omega
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj']
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem laurentSeries_eq_sum_single_mul_pow :
    ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p),
      f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  intro p hp f
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set N : ℕ := f.order.natAbs with hN
  set m : ℕ := (f.order + p * N).toNat with hm
  have hm' : ((m : ℕ) : ℤ) = f.order + p * N := by
    rw [hm, Int.toNat_of_nonneg]
    have : (f.order.natAbs : ℤ) = |f.order| := Int.natCast_natAbs _
    rw [hN, this]
    have h2 : -f.order ≤ |f.order| := neg_le_abs _
    have h3 : 0 ≤ |f.order| := abs_nonneg _
    nlinarith
  obtain ⟨G, hG⟩ := powerSeries_eq_sum_X_pow_mul_pow p (PowerSeries.X ^ m * f.powerSeriesPart)
  refine ⟨fun j => HahnSeries.single (-(N : ℤ)) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ _ (G j), ?_⟩
  have key : f = HahnSeries.single (-(p * N : ℤ)) (1 : ZMod p) *
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.X ^ m * f.powerSeriesPart) := by
    conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart f]
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, hm',
      mul_one]
    congr 2
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, hG, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, map_pow, mul_pow, HahnSeries.single_pow, one_pow]
  have : (p • (-(N : ℤ))) = -(p * N : ℤ) := by rw [nsmul_eq_mul]; ring
  rw [this]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralBis
section
namespace GlobalTheory.IntegralNormAlgebraMap

theorem norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact a.2

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := fun y => by
    change ‖y‖₊ ≤ 1 ↔ _
    exact_mod_cast Iff.rfl
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
      (fun a => (hv _).2 (norm_algebraMap_le_one a))
  have h : IsIntegral v.integer x :=
    IsIntegral.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl) hx
  exact (hv x).1 (Valuation.Integers.mem_of_integral (Valuation.integer.integers v) h)

end GlobalTheory.IntegralNormAlgebraMap
end

