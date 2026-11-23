module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.KmapA

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem val_eq_one_iff {K : Type} [Field K] (A : ValuationSubring K) {y : K} (hy : y ≠ 0) :
    A.valuation y = 1 ↔ y ∈ A ∧ y⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨(A.valuation_le_one_iff y).1 h.le, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨h1, h2⟩
    have hu : IsUnit (⟨y, h1⟩ : A) :=
      isUnit_iff_exists_inv.2 ⟨⟨y⁻¹, h2⟩, Subtype.ext (by simp [hy])⟩
    exact (A.valuation_eq_one_iff _).1 hu

theorem un_map (X : Tower Ω ε) (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) (m : ℕ) (f : X.Kˣ)
    (hf : f ∈ X.Un m) : Units.map φ.toMonoidHom f ∈ X.Un m := by
  intro W hW
  obtain ⟨g, hg⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom g, ?_⟩
  have hx : ((f : X.K) / (g : X.K) ^ m) ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ g.ne_zero)
  rw [val_eq_one_iff _ hx] at hg
  have hx' : φ ((f : X.K) / (g : X.K) ^ m) ≠ 0 := (map_ne_zero φ).2 hx
  have e : ((Units.map φ.toMonoidHom f : X.Kˣ) : X.K) / ((Units.map φ.toMonoidHom g : X.Kˣ) : X.K) ^ m =
      φ ((f : X.K) / (g : X.K) ^ m) := by
    simp [map_div₀, map_pow]
  rw [e, val_eq_one_iff _ hx']
  refine ⟨ValuationSubring.mem_comap.1 hg.1, ?_⟩
  rw [← map_inv₀]
  exact ValuationSubring.mem_comap.1 hg.2

theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (n : ℕ) (a : X.Khat l) (f : X.Kˣ)
    (he : AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = X.cls l n (Units.map φ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply] at he ⊢
  have h2 := AdicCompletion.map_val_apply (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) a
  refine Eq.trans h2 ?_
  rw [he]
  rfl

theorem kmap_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) :
    ∀ a ∈ X.A l, X.kmap l φ a ∈ X.A l := by
  have h : X.A l ≤ (X.A l).comap (X.kmap l φ) := by
    refine Submodule.span_le.2 (fun x hx => ?_)
    refine Submodule.subset_span (fun n => ?_)
    obtain ⟨f, hf, he⟩ := hx n
    exact ⟨_, un_map X φ hφ (l ^ n) f hf, eval_kmap X l φ n x f he⟩
  intro a ha
  exact h ha

end GlobalTheory.KZ.KmapA


open GlobalTheory.KZ.KmapA in
theorem GlobalTheory.KZ.kmap_A_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (l : ℕ) [Fact l.Prime], (∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) ∧
      ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l := by
  intro Ω _ _ _ ε X hinj hhol l _
  have hY := _root_.GlobalTheory.KZ.Tower.overY_comap_sl_gal ε X hinj hhol
  exact ⟨fun g => kmap_mem_A X l _ (fun W hW => (hY W hW).1 g),
    fun s => kmap_mem_A X l _ (fun W hW => (hY W hW).2 s)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGalois
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_valuation_eq_one_iff {K : Type} [Field K] (V : ValuationSubring K) {x : K} (hx : x ≠ 0) :
    V.valuation x = 1 ↔ x ∈ V ∧ x⁻¹ ∈ V := by
  rw [← V.valuation_le_one_iff, ← V.valuation_le_one_iff, map_inv₀]
  have h0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  constructor
  · intro h; simp [h]
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ (pos_iff_ne_zero.2 h0) |>.2 hlt
    exact absurd h2 (not_le.2 this)

theorem vs_comap_valuation_eq_one_iff {K : Type} [Field K] (φ : K →+* K) (V : ValuationSubring K) {x : K}
    (hx : x ≠ 0) : (V.comap φ).valuation x = 1 ↔ V.valuation (φ x) = 1 := by
  rw [vs_valuation_eq_one_iff _ hx, vs_valuation_eq_one_iff _ ((map_ne_zero φ).2 hx),
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀]

theorem Tower.Un_map {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (φ : X.K →+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ)) (m : ℕ) {f : X.Kˣ} (hf : f ∈ X.Un m)
    (u : X.Kˣ) (hu : (u : X.K) = φ (f : X.K)) : u ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom a, ?_⟩
  have hne : (f : X.K) / (a : X.K) ^ m ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ a.ne_zero)
  rw [vs_comap_valuation_eq_one_iff φ W hne, map_div₀, map_pow] at ha
  rw [hu]
  exact ha

theorem Tower.Un_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m →
      (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧
        ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  intro Ω _ _ _ ε X hε hj m f hf
  refine ⟨fun g u hu => ?_, fun s u hu => ?_⟩
  · exact X.Un_map (X.sl g).toRingEquiv.toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).1 g) m hf u hu
  · exact X.Un_map (X.gal s).toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).2 s) m hf u hu

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelation
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.Sat

theorem mdiff_comp_sl (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) := by
  have hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val := by simp
  exact hf.comp (UpperHalfPlane.mdifferentiable_smul hg)

theorem gamma_le {K L : ℕ} (hd : K ∣ L) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  have c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y) := fun x y h => by
    have := congrArg (ZMod.castHom hd (ZMod K)) h
    simpa using this
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ 1 (by simpa using h1)
  · simpa using c _ 0 (by simpa using h2)
  · simpa using c _ 0 (by simpa using h3)
  · simpa using c _ 1 (by simpa using h4)

theorem alg (m : ℕ) (P : ℕ → ℂ) (x y : ℂ)
    (h : ∑ i ∈ Finset.range (m + 1 + 1), P i * x ^ i * y ^ (m + 1 - i) = 0) :
    (P (m + 1) * x) ^ (m + 1) +
      ∑ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = 0 := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
  have key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) =
      P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j)) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)
    have e1 : m - j = k := by omega
    have e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have : (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1))) := by
    simp only [Nat.sub_self, pow_zero, mul_one]; ring
  rw [this]
  linear_combination (P (m + 1) ^ m) * h

theorem sat : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  intro Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq
  obtain ⟨-, hiff, -, -, hmem⟩ := _root_.GlobalTheory.FN.germ_ringHom_and_restrict
  have hring := _root_.GlobalTheory.FN.mem_ring_iff_inR ε.range
  have inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g) := fun f g hf hg =>
    (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))
  have inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k) := fun f k hf =>
    (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)
  have hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i) := fun i => _root_.GlobalTheory.FN.inR_mdifferentiable _ _ (hp i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso; apply hpn; funext τ; have := heq τ; simpa using this
    · exact ⟨m, rfl⟩
  have hHs : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im
  have hHc : IsPreconnected Hs := by
    apply Convex.isPreconnected
    show Convex ℝ {z : ℂ | 0 < z.im}
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with rfl | hs'
    · simp at hst; subst hst; simpa using hy
    · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]
  have dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs := fun f hf => (hiff f).1 hf
  have upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ := fun f τ => by
    simp only [up, UpperHalfPlane.ofComplex_apply]
  obtain ⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by
    by_contra hc; push_neg at hc; exact hb0 (funext hc)
  obtain ⟨h', hh'd, hAD, hmon⟩ := _root_.GlobalTheory.quotient_integral_holomorphic Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b)
    (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc
    ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _))
    ⟨τ0, hmem τ0, by rw [upc]; exact hτ0⟩
    (fun z _ => alg m (fun i => p i (UpperHalfPlane.ofComplex z)) (a (UpperHalfPlane.ofComplex z))
      (b (UpperHalfPlane.ofComplex z)) (heq _))
  set h : ℍ → ℂ := fun τ => h' τ with hh
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hiff]
    refine hh'd.congr fun z hz => ?_
    show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ := fun τ => by
    have := hAD τ (hmem τ); simpa only [upc] using this
  obtain ⟨N, w, hN, hLv, -⟩ := hp (m + 1)
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ := by
    intro γ hγ
    have hγM := gamma_le (Dvd.intro N rfl) hγ
    have hγN := gamma_le (Dvd.intro_left M rfl) hγ
    have hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0 := by
      intro τ
      have E1 := hPA (γ • τ)
      have E2 := hPA τ
      have E3 := hLv γ hγN τ
      have E4 := hab γ hγM τ
      simp only
      linear_combination (-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4
    rcases _root_.GlobalTheory.fn_mul_eq_zero_dom _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0
    · intro τ; have := congrFun h0 τ; simpa [sub_eq_zero] using this
    · exfalso
      have hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0 := fun τ => congrFun h0 τ
      rcases _root_.GlobalTheory.fn_mul_eq_zero_dom _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1
      · exact hb0 h1
      · apply hτ0
        have := congrFun h1 (γ⁻¹ • τ0)
        simpa using this
  refine ⟨h, ?_, hPA⟩
  refine _root_.GlobalTheory.FN.inR_of_integral Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN)
    hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_
  intro τ
  have := hmon τ (hmem τ)
  simpa only [upc] using this

end GlobalTheory.FN.Sat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransform
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory

open GlobalTheory.Sieg

lemma Sieg.cthS_ee_pow (w : ℂ) (n : ℕ) : ee w ^ n = ee ((n : ℂ) * w) := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma Sieg.cthS_negI_pow (c : ℕ) (hc : Nat.Coprime c 6) : (-Complex.I) ^ (c ^ 2) = -Complex.I := by
  have h2 : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hodd : Odd c := by
    rcases Nat.even_or_odd c with h | h
    · exfalso
      obtain ⟨j, hj⟩ := h
      have : 2 ∣ Nat.gcd c 2 := Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl
      rw [h2] at this
      omega
    · exact h
  obtain ⟨j, rfl⟩ := hodd
  have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
  rw [this, pow_succ, pow_mul]
  have h4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  rw [h4, one_pow, one_mul]

theorem Sieg.cth_modular_S (c : ℕ) (τ : ℍ) (z : ℂ) (h1 : 1 < c) (hc : Nat.Coprime c 6)
    (hz : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) :
    cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [inv_neg]

  have hB : th ((c : ℂ) * z) τ ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (_root_.GlobalTheory.ThZero.th_eq_zero_iff τ _).1 h
    exact hz m n hmn

  have hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (_root_.GlobalTheory.ThZero.th_eq_zero_iff _ _).1 h
    rw [hS] at hmn
    apply hz n (-m)
    have : (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ))) := by field_simp
    rw [this, hmn]
    push_cast
    field_simp
    ring
  rw [_root_.GlobalTheory.Sieg.ThQuot.cth_eq_th_quot c _ _ h1 hc hB', _root_.GlobalTheory.Sieg.ThQuot.cth_eq_th_quot c _ _ h1 hc hB]
  rw [show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]
  rw [_root_.GlobalTheory.Sieg.ThInv.th_S τ z, _root_.GlobalTheory.Sieg.ThInv.th_S τ ((c : ℂ) * z)]
  have hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) := by
    rw [Sieg.cthS_ee_pow]
    congr 1
    push_cast
    ring
  have hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hI : (-Complex.I) ≠ 0 := by simp
  rw [mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (x : Ω) (hx : x ≠ 0) (i : ℕ) :
    A.valuation ((σ ^ i) x / x - 1) < 1 := by
  induction i with
  | zero => simp [hx]
  | succ i ih =>
    have hy0 : (σ ^ i) x ≠ 0 := (map_ne_zero (σ ^ i)).2 hx
    have hle : A.valuation ((σ ^ i) x / x) ≤ 1 := by
      have e : (σ ^ i) x / x = ((σ ^ i) x / x - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ih.le (by simp))
    have key : (σ ^ (i + 1)) x / x - 1 =
        (σ ((σ ^ i) x) / (σ ^ i) x - 1) * ((σ ^ i) x / x) + ((σ ^ i) x / x - 1) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [key]
    apply Valuation.map_add_lt _ _ ih
    rw [map_mul]
    calc A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * A.valuation ((σ ^ i) x / x)
        ≤ A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * 1 := by gcongr
      _ < 1 := by simpa using hσ _ hy0


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.mem_of_wild_of_pow_mem_open_normal :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (H : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)), H.Normal → IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∀ (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) (n : ℕ), ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ^ n ∈ H → σ ∈ H := by
  intro E Ω _ _ _ _ _ A v hA H _ hH σ n hn hσ hpow
  change Ω ≃ₐ[E] Ω at σ
  have hv : A.valuation (n : Ω) = 1 := by
    have h1 : ¬ A.valuation (n : Ω) < 1 := by
      intro h
      apply hn
      rw [← hA]
      simpa using h
    have h2 : A.valuation (n : Ω) ≤ 1 := by
      simpa using A.valuation_le_one (n : A)
    exact le_antisymm h2 (not_lt.1 h1)
  have hn0 : (n : Ω) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → Ω, ∀ z, s z = ∑ i ∈ Finset.range n, (σ ^ i) z :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ z, (σ ^ n) z = z → σ (s z) = s z := by
    intro z hz
    have e1 := Finset.sum_range_succ (fun i => (σ ^ i) z) n
    have e2 := Finset.sum_range_succ' (fun i => (σ ^ i) z) n
    simp only [hz, pow_zero, AlgEquiv.one_apply] at e1 e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsdef, map_sum]
    have e3 : ∑ i ∈ Finset.range n, σ ((σ ^ i) z) = ∑ i ∈ Finset.range n, (σ ^ (i + 1)) z :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ', AlgEquiv.mul_apply]
    rw [e3]
    exact add_right_cancel (e2.symm.trans e1)
  have hk : ∀ w, σ w = w → ∀ k : ℕ, (σ ^ k) w = w := by
    intro w hw k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hw]
  have hne : ∀ z, z ≠ 0 → s z ≠ 0 := by
    intro z hz h0
    have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero
        (fun i _ => _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ z hz i)
    have e : ∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1) = s z / z - n := by
      simp [hsdef, Finset.sum_sub_distrib, Finset.sum_div]
    rw [e, h0, zero_div, zero_sub, Valuation.map_neg, hv] at hlt
    exact lt_irrefl _ hlt
  have hfix : ∀ y : Ω, (σ ^ n) y = y → σ y = y := by
    intro y hy
    have hsy := hs y hy
    have h1 : ∀ i, (σ ^ i) ((n : Ω) * y - s y) = n * (σ ^ i) y - s y := fun i => by
      rw [map_sub, map_mul, map_natCast, hk (s y) hsy i]
    have hsz : s ((n : Ω) * y - s y) = 0 := by
      rw [hsdef, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have hz : (n : Ω) * y - s y = 0 := by
      by_contra h
      exact hne _ h hsz
    have hy' : s y = n * y := (sub_eq_zero.1 hz).symm
    have e := congrArg σ hy'
    rw [hsy, map_mul, map_natCast, hy'] at e
    exact (mul_left_cancel₀ hn0 e).symm
  haveI : IsGalois E Ω := inferInstance
  have hcl : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := H.isClosed_of_isOpen hH
  have hH' := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hcl⟩ : ClosedSubgroup (Ω ≃ₐ[E] Ω))
  have hmem : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply hfix
    exact (IntermediateField.mem_fixedField_iff H y).1 hy _ hpow
  rw [hH'] at hmem
  exact hmem

end GlobalTheory
end

