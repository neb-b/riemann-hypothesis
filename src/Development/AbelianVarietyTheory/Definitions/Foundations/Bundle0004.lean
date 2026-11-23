module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
section
noncomputable section

namespace GlobalTheory.Doubling

open scoped NNReal
open MeasureTheory

section Iwasawa

variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)

theorem hom_pos {H : Type} [Group H] (δ : H →* ℝ≥0) (p : H) : 0 < δ p :=
  pos_iff_ne_zero.2 ((Group.isUnit p).map δ).ne_zero

def IsIwasawa : Prop := (∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) ∧ ∀ p : P, (p : G) ∈ K → δ p = 1


open Classical in
def iwAbs (g : G) : ℝ≥0 := by
  classical
  exact if h : ∃ p : P, ∃ k ∈ K, g = p * k then δ h.choose else 1

theorem iwAbs_pos (g : G) : 0 < iwAbs (δ := δ) (K := K) g := by
  unfold iwAbs; split_ifs
  · exact hom_pos δ _
  · exact one_pos

variable {δ K}

theorem iwAbs_mul_of_triv (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) {k : G} (hk : k ∈ K) :
    iwAbs (δ := δ) (K := K) (p * k) = δ p := by
  have e : ∃ p' : P, ∃ k' ∈ K, (p : G) * k = p' * k' := ⟨p, k, hk, rfl⟩
  rw [iwAbs, dite_eq_left e]
  obtain ⟨k', hk', e'⟩ := e.choose_spec
  have h1 := h (p⁻¹ * e.choose) (by
    have : ((p⁻¹ * e.choose : P) : G) = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← e', inv_mul_cancel_left]
    rw [this]; exact mul_mem hk (inv_mem hk'))
  rw [← mul_inv_cancel_left p e.choose, map_mul, h1, mul_one]

namespace IsIwasawa

variable (h : IsIwasawa δ K)
include h

theorem iwAbs_mul (p : P) {k : G} (hk : k ∈ K) : iwAbs (δ := δ) (K := K) (p * k) = δ p := iwAbs_mul_of_triv h.2 p hk

theorem iwAbs_coe (p : P) : iwAbs (δ := δ) (K := K) p = δ p := by simpa using h.iwAbs_mul p (one_mem K)

theorem iwAbs_of_mem {k : G} (hk : k ∈ K) : iwAbs (δ := δ) (K := K) k = 1 := by simpa using h.iwAbs_mul 1 hk

theorem iwAbs_left (p : P) (g : G) : iwAbs (δ := δ) (K := K) (p * g) = δ p * iwAbs (δ := δ) (K := K) g := by
  obtain ⟨p', k, hk, rfl⟩ := h.1 g
  rw [← mul_assoc, ← Subgroup.coe_mul, h.iwAbs_mul _ hk, h.iwAbs_mul _ hk, map_mul]

theorem iwAbs_right (g : G) {k : G} (hk : k ∈ K) : iwAbs (δ := δ) (K := K) (g * k) = iwAbs (δ := δ) (K := K) g := by
  obtain ⟨p', k', hk', rfl⟩ := h.1 g
  rw [mul_assoc, h.iwAbs_mul _ (mul_mem hk' hk), h.iwAbs_mul _ hk']

end IsIwasawa

variable [TopologicalSpace G] [IsTopologicalGroup G]


omit [IsTopologicalGroup G] in
theorem triv_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (p : P)
    (hp : (p : G) ∈ K) : δ p = 1 := by
  obtain ⟨C, hC⟩ := ((hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image hδ).bddAbove
  have key : ∀ q : P, (q : G) ∈ K → δ q ≤ 1 := fun q hq => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    exact absurd (hC ⟨q ^ n, pow_mem hq n, map_pow δ q n⟩) (not_le.2 hn)
  refine le_antisymm (key p hp) ?_
  have := key p⁻¹ (inv_mem hp)
  rwa [map_inv, inv_le_one₀ (hom_pos δ p)] at this

omit [IsTopologicalGroup G] in
theorem isIwasawa_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : IsIwasawa δ K := ⟨h, triv_of_isCompact hP hδ hK⟩

theorem continuous_of_prod (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {X : Type} [TopologicalSpace X] {f : G → X}
    (hf : Continuous fun x : P × K => f (x.1 * x.2)) : Continuous f := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : G × K ≃ₜ G × K :=
    { toFun := fun x => (x.1 * x.2, x.2), invFun := fun x => (x.1 * (x.2 : G)⁻¹, x.2)
      left_inv := fun x => by simp, right_inv := fun x => by simp
      continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  have hc : IsClosedMap fun x : P × K => (x.1 : G) * x.2 :=
    (isClosedMap_fst_of_compactSpace.comp e.isClosedMap).comp
      (hP.isClosedEmbedding_subtypeVal.prodMap (Topology.IsClosedEmbedding.id (X := K))).isClosedMap
  exact (hc.isQuotientMap (by fun_prop) fun g => by
    obtain ⟨p, k, hk, rfl⟩ := h g; exact ⟨(p, ⟨k, hk⟩), rfl⟩).continuous_iff.2 hf

theorem IsIwasawa.continuous_iwAbs (h : IsIwasawa δ K) (hP : IsClosed (P : Set G)) (hδ : Continuous δ)
    (hK : IsCompact (K : Set G)) : Continuous (iwAbs (δ := δ) (K := K)) :=
  continuous_of_prod hP hK h.1 ((hδ.comp continuous_fst).congr fun x => (h.iwAbs_mul x.1 x.2.2).symm)

end Iwasawa

def npow (r : ℝ≥0) (t : ℂ) : ℂ := ((r : ℝ) : ℂ) ^ t

theorem npow_mul (r r' : ℝ≥0) (t : ℂ) : npow (r * r') t = npow r t * npow r' t := by
  rw [npow, NNReal.coe_mul, Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg r.2 r'.2 t

theorem npow_add {r : ℝ≥0} (hr : 0 < r) (t t' : ℂ) : npow r (t + t') = npow r t * npow r t' :=
  Complex.cpow_add _ _ (by exact_mod_cast hr.ne')

@[simp] theorem npow_zero (r : ℝ≥0) : npow r 0 = 1 := Complex.cpow_zero _
@[simp] theorem one_npow (t : ℂ) : npow 1 t = 1 := by simp [npow]

theorem norm_npow {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : ‖npow r t‖ = (r : ℝ) ^ t.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hr t

theorem npow_ne_zero {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_npow hr]; exact (Real.rpow_pos_of_pos hr _).ne'

theorem npow_eq_exp {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t = Complex.exp (Real.log r * t) := by
  rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log r.coe_nonneg]

theorem continuous_npow {X : Type} [TopologicalSpace X] {f : X → ℝ≥0} (hf : Continuous f) (h : ∀ x, 0 < f x) (t : ℂ) :
    Continuous fun x => npow (f x) t := by
  simp only [npow_eq_exp (h _)]
  exact ((Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp hf).log fun x => (NNReal.coe_pos.2 (h x)).ne')).mul continuous_const).cexp

section Induced

variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)

def IndLaw (Φ : G → ℂ) : Prop := ∀ (p : P) (g : G), Φ (p * g) = χ p * npow (δ p) t * Φ g

def kSpan (Φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = fun g => Φ (g * k)}

def IsKFinite (Φ : G → ℂ) : Prop := FiniteDimensional ℂ (kSpan K Φ)

variable {K}

theorem isKFinite_iff {Φ : G → ℂ} : IsKFinite K Φ ↔
    ∃ W : Submodule ℂ (G → ℂ), FiniteDimensional ℂ W ∧ ∀ k ∈ K, (fun g => Φ (g * k)) ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩

theorem IsKFinite.of_invariant {Φ : G → ℂ} (h : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : IsKFinite K Φ :=
  isKFinite_iff.2 ⟨ℂ ∙ Φ, inferInstance, fun k hk => by
    rw [show (fun g => Φ (g * k)) = Φ from funext fun g => h g k hk]; exact Submodule.mem_span_singleton_self _⟩

theorem IsKFinite.add {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K (Φ + Ψ) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', _, hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W ⊔ W', inferInstance, fun k hk => Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩

theorem IsKFinite.mul_invariant {Φ f : G → ℂ} (h : IsKFinite K Φ) (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    IsKFinite K fun g => Φ g * f g := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  refine isKFinite_iff.2 ⟨W.map (LinearMap.mulRight ℂ f), inferInstance, fun k hk => ⟨_, hW k hk, funext fun g => ?_⟩⟩
  simp [hf g k hk]

theorem IsKFinite.translate {Φ : G → ℂ} (h : IsKFinite K Φ) {k : G} (hk : k ∈ K) : IsKFinite K fun g => Φ (g * k) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  exact isKFinite_iff.2 ⟨W, inferInstance, fun k' hk' => by simpa only [mul_assoc] using hW _ (mul_mem hk' hk)⟩

variable (K)

def indSpace [TopologicalSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {Φ | IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ}
  zero_mem' := ⟨fun _ _ => by simp, continuous_zero, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨fun p g => by simp only [Pi.add_apply, h.1 p g, h'.1 p g, mul_add],
    h.2.1.add h'.2.1, h.2.2.add h'.2.2⟩
  smul_mem' := fun c Φ h => ⟨fun p g => by simp only [Pi.smul_apply, h.1 p g, smul_eq_mul]; ring,
    h.2.1.const_smul c, by
      have := h.2.2.mul_invariant (f := fun _ => c) fun _ _ _ => rfl
      simp only [mul_comm _ c] at this
      exact this⟩

def flatSec (Φ : G → ℂ) (s₀ s : ℂ) : G → ℂ := fun g => Φ g * npow (iwAbs (δ := δ) (K := K) g) (s - s₀)

variable {δ K χ t}

@[simp] theorem flatSec_self (Φ : G → ℂ) (s₀ : ℂ) : flatSec (δ := δ) (K := K) Φ s₀ s₀ = Φ := funext fun g => by simp [flatSec]

namespace IsIwasawa

variable (h : IsIwasawa δ K)
include h

theorem indLaw_flatSec {Φ : G → ℂ} {ρ s₀ : ℂ} (hΦ : IndLaw δ χ (s₀ + ρ) Φ) (s : ℂ) :
    IndLaw δ χ (s + ρ) (flatSec (δ := δ) (K := K) Φ s₀ s) := fun p g => by
  rw [flatSec, flatSec, hΦ, h.iwAbs_left, npow_mul, show s + ρ = (s₀ + ρ) + (s - s₀) by ring,
    npow_add (hom_pos δ p) _ (s - s₀)]
  ring

theorem norm_le {Φ : G → ℂ} (hΦ : IndLaw δ χ t Φ) {C : ℝ} (hC : ∀ k ∈ K, ‖Φ k‖ ≤ C) (g : G) :
    ‖Φ g‖ ≤ C * (iwAbs (δ := δ) (K := K) g : ℝ) ^ t.re := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  rw [hΦ, h.iwAbs_mul _ hk, norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem flatSec_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) {Φ : G → ℂ}
    {ρ s₀ : ℂ} (hΦ : Φ ∈ indSpace δ K χ (s₀ + ρ)) (s : ℂ) : flatSec (δ := δ) (K := K) Φ s₀ s ∈ indSpace δ K χ (s + ρ) :=
  ⟨h.indLaw_flatSec hΦ.1 s, hΦ.2.1.mul (continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos (δ := δ) (K := K)) _),
    hΦ.2.2.mul_invariant (f := fun g => npow (iwAbs (δ := δ) (K := K) g) (s - s₀)) fun g k hk => by rw [h.iwAbs_right g hk]⟩

theorem npow_iwAbs_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (t : ℂ) :
    (fun g => npow (iwAbs δ K g) t) ∈ indSpace δ K 1 t :=
  ⟨fun p g => by simp [h.iwAbs_left, npow_mul], continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos (δ := δ) (K := K)) _,
    .of_invariant fun g k hk => by rw [h.iwAbs_right g hk]⟩

end IsIwasawa

end Induced

section ZetaNonvanishing₂

variable {H : Type} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def coef (π : H → X → X) (x y : X) : H → ℂ := fun g => inner ℂ y (π g x)

variable [MeasurableSpace H] (m : Measure H)

def pairInt (f c : H → ℂ) : ℂ := ∫ g, f g * starRingEnd ℂ (c g) ∂m

def PairConv (f c : H → ℂ) : Prop := Integrable (fun g => f g * starRingEnd ℂ (c g)) m

end ZetaNonvanishing₂

end GlobalTheory.Doubling

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Letter
section
noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.OverY (X : Tower Ω ε) (W : ValuationSubring X.K) : Prop :=
  (∀ c : Ω, algebraMap Ω X.K c ∈ W) ∧ X.jK ∈ W

def Tower.Un (X : Tower Ω ε) (m : ℕ) : Set X.Kˣ :=
  {f | ∀ W, X.OverY W → ∃ g : X.Kˣ, W.valuation ((f : X.K) / (g : X.K) ^ m) = 1}

abbrev Tower.Kl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := TensorProduct ℤ ℤ_[l] (Additive X.Kˣ)

abbrev idl (l : ℕ) [Fact l.Prime] : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])}

abbrev Tower.Khat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := AdicCompletion (idl l) (X.Kl l)

def Tower.cls (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) :
    X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l))) :=
  Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul f)

def Tower.ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Set (X.Khat l) :=
  {a | ∀ n : ℕ, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f}

def Tower.A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Khat l) := Submodule.span ℤ_[l] (X.ASet l)

def Tower.kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))))

abbrev Tower.Fn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := (Fin 2 → ℤ_[l]) → X.Khat l

def Tower.Pol (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) : Set (X.Fn l) :=
  {b | ∃ c : Fin (w + 1) → X.Khat l, (∀ i, c i ∈ X.A l) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}

def mZl (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ_[l] := m.map (Int.castRingHom ℤ_[l])

def Tower.act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

def Gam (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def Tower.BSet (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Set (X.Fn l) :=
  {b | b ∈ X.Pol l w ∧ ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b}

def Tower.B (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Fn l) := Submodule.span ℤ_[l] (X.BSet N l w)

def IsDiam (N l d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l ∧ (en γ 1 1 : ZMod N) = d

def sgD (N l d : ℕ) : SL(2, ℤ) := Classical.epsilon (IsDiam N l d)

def Tower.diam (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (d : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def Tower.heckeT (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (q : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) +
    X.act l ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])

def Tower.heckeU (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  ∑ j ∈ Finset.range l, X.act l !![1, (j : ℤ); 0, (l : ℤ)]

def Tower.galB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1])
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

inductive Letter
  | T (q : ℕ)
  | U
  | D (d : ℕ)

def Tower.op (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : Letter → (X.Fn l →ₗ[ℤ_[l]] X.Fn l)
  | Letter.T q => X.heckeT N l q
  | Letter.U => X.heckeU l
  | Letter.D d => X.diam N l d

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
section
noncomputable section

namespace GlobalTheory.AlmostEt

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

structure IsDerOn (B : Subalgebra A S) (D : S → M) : Prop where
  add : ∀ x ∈ B, ∀ y ∈ B, D (x + y) = D x + D y
  mul : ∀ x ∈ B, ∀ y ∈ B, D (x * y) = x • D y + y • D x
  alg : ∀ a : A, D (algebraMap A S a) = 0

structure IsTrData (B C : Subalgebra A S) (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) : Prop where
  le : B ≤ C
  e_mem : e ∈ B
  a_mem : ∀ i, a i ∈ C
  b_mem : ∀ i, b i ∈ C
  tr_mem : ∀ x ∈ C, tr x ∈ B
  tr_add : ∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y
  tr_mul : ∀ β ∈ B, ∀ x ∈ C, tr (β * x) = β * tr x
  left : ∀ x ∈ C, ∑ i, a i * tr (b i * x) = e * x
  right : ∀ x ∈ C, ∑ i, b i * tr (a i * x) = e * x
  sum : ∑ i, a i * b i = e

end General

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_pow (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simpa using T.q0
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]

def zS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.ζ n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [(T.prim n).pow_eq_one]; exact isIntegral_one)⟩

def qS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.qq n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [qq_pow]; exact isIntegral_algebraMap)⟩

def levelAlg (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) {zS T n, qS T n}

def towerAlg (T : Tower p Ω) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) (Set.range (zS T) ∪ Set.range (qS T))

abbrev Frac (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ :=
  Ω ⧸ LinearMap.range (Algebra.linearMap (integralClosure (O0 p) Ω) Ω)

end Tower

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.Inhab

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

end General

section Examples

end Examples

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

end Tower

end GlobalTheory.AlmostEt.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def rowT (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val + (p : ℤ) ^ n * w.1,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * w.2)

def pieceT (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

def pieceTRaw (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

end GlobalTheory.KummerEisensteinGalois
end
end

