module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Imports
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

namespace GlobalTheory.ComplementTypes


open NumberField in
open scoped ComplexConjugate in
theorem _root_.GlobalTheory.ComplementTypes.types (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q r g g' : ℕ)
    (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ)) (hty : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty)
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = (r : ℂ) * ∑ τ : E →+* ℂ, τ (H.bar a : E) + ∑ j, ty' j (a : E)) :
    r ≤ p ∧ r ≤ q ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H (p - r) (q - r) ty' := by
  classical
  let c : E →+* E := (IsCMField.complexConj E).toAlgHom.toRingHom
  have hcc : ∀ x, c (c x) = x := fun x => by simp [c]
  let t : (Fin r × (E →+* ℂ)) ⊕ Fin g' → (E →+* ℂ) := Sum.elim (fun k => k.2.comp c) ty'
  have hsum : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = ∑ k, t k (a : E) := by
    intro a
    rw [h a, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [t, c, H.bar_eq]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq ty t hsum
  have key : ∀ τ : E →+* ℂ, Nat.card {i // ty i = τ} = r + Nat.card {j // ty' j = τ} := by
    intro τ
    have hc1 : ∀ σ : E →+* ℂ, σ.comp c = τ ↔ σ = τ.comp c := fun σ =>
      ⟨fun hσ => by ext x; rw [← hσ]; simp [hcc], fun hσ => by ext x; rw [hσ]; simp [hcc]⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_congr (e.subtypeEquiv (p := fun i => ty i = τ) (q := fun k => t k = τ) fun i => by
        simp only [he]), Fintype.card_subtype,
      Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, hc1, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    congr 1
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  have hconj : conj H.rt0 = -H.rt0 := by
    have hsq : conj H.rt0 ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'
    · exfalso
      have hre := Complex.conj_eq_iff_re.1 h'
      have h2 := H.sqrt_neg_disc_sq
      rw [← hre] at h2
      have h3 := congrArg Complex.re h2
      simp [pow_two] at h3
      nlinarith [mul_self_nonneg H.rt0.re]
    · exact h'
  have hne : -H.rt0 ≠ H.rt0 := by
    intro h0
    have h1 : H.rt0 = 0 := by linear_combination -h0 / 2
    have h2 := H.sqrt_neg_disc_sq
    rw [h1] at h2
    have h3 := congrArg Complex.re h2
    simp at h3
    have := H.d_prime.two_le
    omega
  have hroot : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ1, h1⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨τ0, h0⟩
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj]⟩
  obtain ⟨τ2, h2⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj, hne]⟩
    · exact ⟨τ0, by rw [h0]; exact hne⟩
  have hp := (hty τ1).1 h1
  have hq := (hty τ2).2 h2
  have k1 := key τ1
  have k2 := key τ2
  refine ⟨by omega, by omega, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · have := (hty τ).1 hτ
    have := key τ
    omega
  · have := (hty τ).2 hτ
    have := key τ
    omega

end GlobalTheory.ComplementTypes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
section
open NumberField

namespace GlobalTheory.HomTrace

lemma finrank_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.finrank ℂ (X →+ ℂ) = Module.finrank ℤ X := by
  rw [(addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).finrank_eq, Module.finrank_linearMap]
  simp

lemma finite_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.Finite ℂ (X →+ ℂ) :=
  Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).symm

theorem trace_eq_finrank_mul_sum (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (a : 𝓞 E) (f : (X →+ ℂ) →ₗ[ℂ] (X →+ ℂ))
    (hf : ∀ l x, f l x = l (a • x)) :
    LinearMap.trace ℂ (X →+ ℂ) f = (Module.finrank (𝓞 E) X : ℂ) * ∑ τ : E →+* ℂ, τ (a : E) := by
  classical
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X with hr
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) hr.le
  let j : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) v
  let F : Submodule (𝓞 E) X := Submodule.span (𝓞 E) (Set.range v)
  have hF : Module.finrank (𝓞 E) F = r := by simpa using finrank_span_eq_card hv
  have h0 : Module.finrank (𝓞 E) (X ⧸ F) = 0 := by
    have := F.finrank_quotient_add_finrank
    omega
  have htor : ∀ x : X, ∃ n : ℤ, n ≠ 0 ∧ ∃ y, j y = n • x := by
    intro x
    rw [Module.finrank_eq_zero_iff] at h0
    obtain ⟨c, hc, hx⟩ := h0 (Submodule.Quotient.mk x)
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc)
    refine ⟨n, hn, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    have h1 : n • x ∈ F := by
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul]
      exact F.smul_mem _ hx
    rw [show F = LinearMap.range j from (Fintype.range_linearCombination _ _).symm] at h1
    exact h1
  let R : (X →+ ℂ) →ₗ[ℂ] ((Fin r → 𝓞 E) →+ ℂ) :=
    { toFun := fun l => l.comp j.toAddMonoidHom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ l y, R l y = l (j y) := fun _ _ => rfl
  have hinj : Function.Injective R := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro l hl
    ext x
    obtain ⟨n, hn, y, hy⟩ := htor x
    have h1 : l (j y) = 0 := by rw [← hR, hl]; rfl
    rw [hy, map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn)
  have := finite_hom X
  have := finite_hom (Fin r → 𝓞 E)
  have hdY : Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) = r * Module.finrank ℚ E := by
    rw [finrank_hom, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  have hdim : Module.finrank ℂ (X →+ ℂ) = Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) := by
    rw [hdY, finrank_hom, finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank, mul_comm]
  let e := LinearMap.linearEquivOfInjective R hinj hdim
  let g : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hg : Function.Injective g := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp g hg
  let w : Fin r × (E →+* ℂ) → ((Fin r → 𝓞 E) →+ ℂ) := fun p =>
    ((p.2.comp (algebraMap (𝓞 E) E)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ => 𝓞 E) p.1)
  have hw : ∀ p y, w p y = p.2 (y p.1 : E) := fun _ _ => rfl
  have hwli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨i, τ⟩
    refine Fintype.linearIndependent_iff.1 hli (fun φ => c (i, φ)) ?_ τ
    funext y
    have h1 := DFunLike.congr_fun hc (Pi.single i y)
    rw [AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i] at h1
    · simpa [hw, g] using h1
    · intro k _ hk
      simp [hw, Pi.single_eq_of_ne hk]
    · simp
  let b := basisOfLinearIndependentOfCardEqFinrank' w hwli (by
    rw [hdY, Fintype.card_prod, Fintype.card_fin, Embeddings.card])
  let c := b.map e.symm
  have hc : ∀ p, R (c p) = w p := fun p => by
    have : e (c p) = b p := by simp [c]
    rw [← show b p = w p by simp [b], ← this]; rfl
  have hfc : ∀ p, f (c p) = p.2 (a : E) • c p := fun p => by
    apply hinj
    refine AddMonoidHom.ext fun y => ?_
    rw [map_smul, hR, hf, ← j.map_smul, ← hR, hc, AddMonoidHom.smul_apply, hw, hw]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℂ c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, hfc, Fintype.sum_prod_type]

end GlobalTheory.HomTrace
end

