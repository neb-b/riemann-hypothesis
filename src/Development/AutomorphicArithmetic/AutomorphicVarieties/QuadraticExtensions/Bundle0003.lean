module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

namespace UpperTheory.V.Two.DyadicOrbitIndex

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [e]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  have e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n := by simp
  rw [e1, e2]
  exact map_dvd_iff Rat.ringOfIntegersEquiv.symm

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hc : IsCoprime ((l : ℕ) : ℤ) n :=
      ((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd
    obtain ⟨a, b, hab⟩ := hc
    have h1 : A.valuation ((a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    have h2 : (a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    rw [h2, map_one] at h1
    exact lt_irrefl _ h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have := Rat.ringOfIntegersEquiv.symm_apply_apply x
      rw [← this]; simp⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]
  simp

private theorem smul_val_lt [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hA ⊢
  rcases hA with h | h
  · exact Or.inl h
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h'
    have e : g⁻¹ • ((n : Ω))⁻¹ = ((n : Ω))⁻¹ := by
      show (g⁻¹ : G ℚ Ω) ((n : Ω))⁻¹ = _
      rw [map_inv₀, map_natCast]
    rwa [e] at h'

end UpperTheory.V.Two.DyadicOrbitIndex

open UpperTheory.V.Two.DyadicOrbitIndex in
theorem UpperTheory.V.Two.orbIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (V : Subgroup (G ℚ Ω)) [V.Normal] (A₀ : ValuationSubring Ω), p.Prime → A₀.valuation (p : Ω) < 1 → (V ⊔ Dec (F := ℚ) A₀).index ≠ 0 → OrbLe V p (V ⊔ Dec (F := ℚ) A₀).index := by
  intro Ω _ _ _ p V hV A₀ hp h0 hi
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)) := Nat.finite_of_card_ne_zero hi
  haveI := Fintype.ofFinite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀))
  refine ⟨Finset.univ.image fun q : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀) => q.out • A₀, ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
  · intro B hB
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hB
    exact smul_val_lt _ _ _ h0
  · intro A hA
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A₀ h0) (isPlaceOver_vQ A hA)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V ⊔ Dec (F := ℚ) A₀) g
    have hm : (h⁻¹ : G ℚ Ω) ∈ ((V ⊔ Dec (F := ℚ) A₀ : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := inv_mem h.2
    rw [Subgroup.normal_mul] at hm
    obtain ⟨v, hv, d, hd, e⟩ := hm
    set r := (QuotientGroup.mk g : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)).out with hr
    refine ⟨r • A₀, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, r * v * r⁻¹, hV.conj_mem v hv r, ?_⟩
    have hd' : d • A₀ = A₀ := (mem_Dec (F := ℚ)).1 hd
    have eg : g = r * v * d := by
      have e' : v * d = (h : G ℚ Ω)⁻¹ := e
      rw [mul_assoc, e', hh]; group
    rw [eg, mul_smul (r * v) d, hd', smul_smul]
    congr 1; group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QzEnd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.qzEnd :
    ∀ (l : ℕ) [Fact l.Prime] (f : QZ l →ₗ[ℤ_[l]] QZ l), ∃ c : ℤ_[l], ∀ x, f x = c • x := by
  intro l _ f
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hz : ∀ q : ℚ_[l], QZ.mk l q = 0 ↔ ‖q‖ ≤ 1 := by
    intro q
    show (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro h
      exact ⟨⟨q, h⟩, rfl⟩
  set x : ℕ → QZ l := fun k => QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) with hx
  have hA : ∀ (c : ℤ_[l]) (k : ℕ), c • x k = 0 ↔ ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro c k
    show QZ.mk l ((c : ℚ_[l]) * ((l : ℚ_[l]) ^ k)⁻¹) = 0 ↔ _
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by positivity
    rw [hz, norm_mul, norm_inv, Padic.norm_p_pow, mul_inv_le_iff₀ hpos, one_mul]
    exact Iff.rfl
  have hC : ∀ (k : ℕ) (y : QZ l), (l ^ k) • y = 0 → ∃ a : ℤ_[l], y = a • x k := by
    intro k y hy
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) y
    have h1 : QZ.mk l ((l : ℚ_[l]) ^ k * q) = 0 := by
      rw [← hy]
      show _ = (Submodule.Quotient.mk ((l ^ k) • q) : ℚ_[l] ⧸ ZlSub l)
      rw [nsmul_eq_mul]
      push_cast
      rfl
    rw [hz] at h1
    refine ⟨⟨(l : ℚ_[l]) ^ k * q, h1⟩, ?_⟩
    show QZ.mk l q = QZ.mk l (((l : ℚ_[l]) ^ k * q) * ((l : ℚ_[l]) ^ k)⁻¹)
    congr 1
    field_simp
  have hstep : ∀ k, x k = (l : ℤ_[l]) • x (k + 1) := by
    intro k
    show QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) = QZ.mk l ((l : ℚ_[l]) * ((l : ℚ_[l]) ^ (k + 1))⁻¹)
    congr 1
    rw [pow_succ]
    field_simp
  have hkill : ∀ k, (l ^ k) • x k = 0 := by
    intro k
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], hA]
    push_cast
    rw [PadicInt.norm_p_pow]
  have hex : ∀ k, ∃ a : ℤ_[l], f (x k) = a • x k := by
    intro k
    apply hC
    rw [← map_nsmul, hkill, map_zero]
  choose a ha using hex
  have hdiff : ∀ k, ‖a (k + 1) - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [← hA, sub_smul, sub_eq_zero, ← ha k, hstep k, map_smul, ha (k + 1)]
    exact smul_comm _ _ _
  have hr : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hcs : CauchySeq a := by
    refine cauchySeq_of_le_geometric ((l : ℝ)⁻¹) 1 hr (fun n => ?_)
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdiff n
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
  have hmono : ∀ k m, k ≤ m → ‖a m - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
      rw [sub_self, norm_zero]
      positivity
    | succ m hkm ih =>
      have := PadicInt.nonarchimedean (a (m + 1) - a m) (a m - a k)
      rw [sub_add_sub_cancel] at this
      refine this.trans (max_le ((hdiff m).trans ?_) ih)
      exact zpow_le_zpow_right₀ hl.le (by omega)
  have hck : ∀ k, ‖c - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have ht : Filter.Tendsto (fun m => ‖a m - a k‖) Filter.atTop (nhds ‖c - a k‖) :=
      (hc.sub_const (a k)).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨k, fun m hm => hmono k m hm⟩)
  have hfx : ∀ k, f (x k) = c • x k := by
    intro k
    have := (hA (c - a k) k).2 (hck k)
    rw [sub_smul, sub_eq_zero] at this
    rw [this, ha k]
  refine ⟨c, fun y => ?_⟩
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 y
  obtain ⟨b, rfl⟩ := hC k y hk
  rw [map_smul, hfx, smul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.RkTransport
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.rkTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ),
      XRk l N (cycU l (⊤ : Subgroup (G K Ω))) r ↔ XRk l N (cycU l (galOf F K Ω)) r := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ N r
  have hDI : ∀ A : ValuationSubring Ω,
      (Dec (F := F) A).comap (galEmb F K Ω) = Dec (F := K) A ∧
      (Ine (F := F) A).comap (galEmb F K Ω) = Ine (F := K) A := by
    intro A
    have hD : (Dec (F := F) A).comap (galEmb F K Ω) = Dec (F := K) A := by
      ext σ
      rw [Subgroup.mem_comap, mem_Dec, mem_Dec]
      rfl
    refine ⟨hD, ?_⟩
    ext σ
    rw [Subgroup.mem_comap]
    exact and_congr (SetLike.ext_iff.1 hD σ) Iff.rfl
  obtain ⟨hE, -, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (σ : G K Ω), galEmb F K Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := K) A :=
    fun A σ => by rw [← (hDI A).1]; rfl
  have hI : ∀ (A : ValuationSubring Ω) (σ : G K Ω), galEmb F K Ω σ ∈ Ine (F := F) A ↔ σ ∈ Ine (F := K) A :=
    fun A σ => by rw [← (hDI A).2]; rfl
  have hle : cycU l (galOf F K Ω) ≤ galOf F K Ω := inf_le_left
  let e : cycU l (⊤ : Subgroup (G K Ω)) → cycU l (galOf F K Ω) :=
    fun u => ⟨galEmb F K Ω u.1, galEmb_mem F K Ω u.1, u.2.2⟩
  let e' : cycU l (galOf F K Ω) → cycU l (⊤ : Subgroup (G K Ω)) :=
    fun u => ⟨toGal K hle u, trivial, u.2.2⟩
  have hee : ∀ u, e (e' u) = u := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have hee' : ∀ u, e' (e u) = u := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have he : Continuous e := (hE.continuous.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e' := by
    refine Continuous.subtype_mk ?_ _
    exact hE.continuous_iff.2 continuous_subtype_val
  have hm : ∀ a b, e (a * b) = e a * e b := fun a b => Subtype.ext (map_mul (galEmb F K Ω) a.1 b.1)
  have hm' : ∀ a b, e' (a * b) = e' a * e' b := fun a b => Subtype.ext (map_mul (toGal K hle) a b)
  constructor
  · intro h
    refine CardLe.of_injective h (fun φ => ⟨φ.1 ∘ e, φ.2.1.comp_continuous he,
      fun a b => by simp only [Function.comp, hm]; exact φ.2.2.1 _ _,
      fun A u hu => φ.2.2.2.1 A (e u) ((hI A u.1).2 hu),
      fun A hA u hu => φ.2.2.2.2 A hA (e u) ((hD A u.1).2 hu)⟩) fun φ ψ hh => Subtype.ext (funext fun u => ?_)
    have := congrFun (congrArg Subtype.val hh) (e' u)
    simpa only [Function.comp, hee] using this
  · intro h
    refine CardLe.of_injective h (fun φ => ⟨φ.1 ∘ e', φ.2.1.comp_continuous he',
      fun a b => by simp only [Function.comp, hm']; exact φ.2.2.1 _ _,
      fun A u hu => φ.2.2.2.1 A (e' u) ((hI A (e' u).1).1 hu),
      fun A hA u hu => φ.2.2.2.2 A hA (e' u) ((hD A (e' u).1).1 hu)⟩) fun φ ψ hh => Subtype.ext (funext fun u => ?_)
    have := congrFun (congrArg Subtype.val hh) (e u)
    simpa only [Function.comp, hee'] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SubqLen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.subqLen :
    ∀ (l : ℕ) [Fact l.Prime] (N : Submodule ℤ_[l] (QZ l)) (Q P : Type) [AddCommGroup Q] [Module ℤ_[l] Q] [AddCommGroup P] [Module ℤ_[l] P] (π : N →ₗ[ℤ_[l]] Q) (j : P →ₗ[ℤ_[l]] Q),
      Function.Surjective π → Function.Injective j → (∀ x : P, (l : ℤ_[l]) • x = 0) → Module.length ℤ_[l] P ≤ 1 := by
  intro l _ N Q P _ _ _ _ π j hπ hj htor
  have key : ∀ a b : QZ l, ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) b
    have step : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := by
      intro x y h
      by_cases hy : y = 0
      · subst hy
        refine ⟨0, ?_⟩
        rw [norm_zero] at h
        rw [norm_le_zero_iff.mp h, zero_smul]
      · refine ⟨⟨x / y, ?_⟩, ?_⟩
        · rw [PadicInt.mem_subring_iff, norm_div]
          exact div_le_one_of_le₀ h (norm_nonneg _)
        · show x = (x / y) * y
          rw [div_mul_cancel₀ _ hy]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · obtain ⟨c, hc⟩ := step x y h
      exact ⟨c, Or.inl (by rw [hc]; rfl)⟩
    · obtain ⟨c, hc⟩ := step y x h
      exact ⟨c, Or.inr (by rw [hc]; rfl)⟩
  have hQ : ∀ q1 q2 : Q, ∃ c : ℤ_[l], q1 = c • q2 ∨ q2 = c • q1 := by
    intro q1 q2
    obtain ⟨n1, rfl⟩ := hπ q1
    obtain ⟨n2, rfl⟩ := hπ q2
    obtain ⟨c, h | h⟩ := key (n1 : QZ l) (n2 : QZ l)
    · refine ⟨c, Or.inl ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
    · refine ⟨c, Or.inr ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
  have hP : ∀ x y : P, x ≠ 0 → y ∈ Submodule.span ℤ_[l] {x} := by
    intro x y hx
    obtain ⟨c, h | h⟩ := hQ (j y) (j x)
    · rw [← map_smul] at h
      rw [hj h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · rw [← map_smul] at h
      have hxy := hj h
      by_cases hc : IsUnit c
      · obtain ⟨u, rfl⟩ := hc
        have hy : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x := by
          rw [hxy, smul_smul, Units.inv_mul, one_smul]
        rw [hy]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · exfalso
        have hn : ‖c‖ < 1 := PadicInt.mem_nonunits.mp hc
        obtain ⟨d, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd c).mp hn
        apply hx
        rw [hxy, mul_comm, mul_smul, htor, smul_zero]
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · rw [Module.length_eq_zero]
    exact zero_le
  · haveI : IsSimpleModule ℤ_[l] P := by
      rw [isSimpleModule_iff]
      refine IsSimpleOrder.mk (fun S => ?_)
      by_cases hS : S = ⊥
      · exact Or.inl hS
      · right
        obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hS
        rw [eq_top_iff]
        intro y _
        exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS)) (hP x y hx0)
    rw [Module.length_eq_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SupIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem relIndex_sup_normal {Γ : Type} [Group Γ] (K D H : Subgroup Γ) [K.Normal] (hD : D ≤ H) :
    H.relIndex (K ⊔ D) = H.relIndex K := by
  classical
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ D)) fun a b h => ?_) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun a => Quotient.ind' fun b => ?_
    intro h
    simp only [Quotient.map'_mk''] at h
    rw [Quotient.eq''] at h ⊢
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun y => ?_
    obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_left.mp y.2
    refine ⟨Quotient.mk'' ⟨k, hk⟩, ?_⟩
    simp only [Quotient.map'_mk'']
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hy : (y : Γ) = k * d := hkd.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hy, inv_mul_cancel_left]
    exact hD hd

theorem UpperTheory.V.Two.supIndex :
    ∀ (Γ : Type) [Group Γ] (K W D : Subgroup Γ) [K.Normal] [W.Normal], W.index ≠ 0 → (K ⊔ D).index ≠ 0 → ((W ⊓ K) ⊔ D).index ≠ 0 ∧ ((W ⊓ K) ⊔ D).index ≤ W.index * (K ⊔ D).index := by
  intro Γ _ K W D _ _ hW hKD
  have hLKD : (W ⊓ K) ⊔ D ≤ K ⊔ D := sup_le_sup_right inf_le_right D
  have hDL : D ≤ (W ⊓ K) ⊔ D := le_sup_right
  have hWKL : W ⊓ K ≤ (W ⊓ K) ⊔ D := le_sup_left
  have h1 : ((W ⊓ K) ⊔ D).index = ((W ⊓ K) ⊔ D).relIndex K * (K ⊔ D).index := by
    rw [← relIndex_sup_normal K D _ hDL, Subgroup.relIndex_mul_index hLKD]
  have h2 : ((W ⊓ K) ⊔ D).relIndex K ∣ W.index := by
    have h := Subgroup.relIndex_dvd_of_le_left K hWKL
    rw [Subgroup.inf_relIndex_right] at h
    exact h.trans (Subgroup.relIndex_dvd_index_of_normal W K)
  have h3 : ((W ⊓ K) ⊔ D).relIndex K ≠ 0 := fun h => hW (Nat.eq_zero_of_zero_dvd (h ▸ h2))
  have h4 : ((W ⊓ K) ⊔ D).relIndex K ≤ W.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hW) h2
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact mul_ne_zero h3 hKD
  · rw [h1]
    exact Nat.mul_le_mul_right _ h4
end

