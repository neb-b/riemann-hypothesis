module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KummerTwistRelationAndFixedField
section
namespace GlobalTheory

private theorem pow_apply_eq_pow_mul_of_apply_eq_mul {F Ω : Type} [Field F] [Field Ω]
    [Algebra F Ω] (σ : Ω ≃ₐ[F] Ω) (ρ ζ : Ω) (hζ : ζ ∈ Set.range (algebraMap F Ω))
    (hσ : σ ρ = ζ * ρ) (k : ℕ) : (σ ^ k) ρ = ζ ^ k * ρ := by
  obtain ⟨z, rfl⟩ := hζ
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hσ, map_mul, AlgEquiv.commutes, ih]
    ring

private theorem sum_pow_apply_pow_mem_bot_of_kummer {F Ω : Type} [Field F] [Field Ω]
    [Algebra F Ω] (n : ℕ) (σ : Ω ≃ₐ[F] Ω) (ρ ζ : Ω) (c : F) (hρ : ρ ^ n = algebraMap F Ω c)
    (hζ : IsPrimitiveRoot ζ n) (hζF : ζ ∈ Set.range (algebraMap F Ω)) (hσ : σ ρ = ζ * ρ)
    (i : ℕ) : ∑ k ∈ Finset.range n, (σ ^ k) (ρ ^ i) ∈ (⊥ : Subalgebra F Ω) := by
  have hk : ∀ k, (σ ^ k) (ρ ^ i) = (ζ ^ i) ^ k * ρ ^ i := by
    intro k
    rw [map_pow, pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ k]
    ring
  simp_rw [hk, ← Finset.sum_mul]
  by_cases h1 : ζ ^ i = 1
  · rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    obtain ⟨m, rfl⟩ := (hζ.pow_eq_one_iff_dvd i).1 h1
    rw [pow_mul, hρ, ← map_pow, ← map_natCast (algebraMap F Ω) n, ← map_mul]
    exact Subalgebra.algebraMap_mem _ _
  · rw [geom_sum_eq h1, ← pow_mul, mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div, zero_mul]
    exact Subalgebra.zero_mem _

theorem kummer_twist_relation_and_fixed_field :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n q : ℕ) (ρ ζ : Ω) (c : F) (σ : Ω ≃ₐ[F] Ω) (φ : Ω →+* Ω), 0 < n → ρ ^ n = algebraMap F Ω c → φ (algebraMap F Ω c) = algebraMap F Ω c → (∀ a : F, φ (algebraMap F Ω a) ∈ Set.range (algebraMap F Ω)) → (∀ ξ : Ω, ξ ^ n = 1 → ξ ∈ Set.range (algebraMap F Ω)) → IsPrimitiveRoot ζ n → σ ρ = ζ * ρ → φ ζ = ζ ^ q → ∀ x ∈ IntermediateField.adjoin F ({ρ} : Set Ω), φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ Set.range (algebraMap F Ω)) := by
  intro F Ω _ _ _ _ n q ρ ζ c σ φ hn hρ hφc hφF hroots hζ hσ hφζ x hx
  have hζF : ζ ∈ Set.range (algebraMap F Ω) := hroots ζ hζ.pow_eq_one
  refine ⟨?_, fun hsx => ?_⟩
  ·
    have hρ' : φ (σ ρ) = (σ ^ q) (φ ρ) := by
      by_cases h0 : ρ = 0
      · simp [h0]
      · have hc : algebraMap F Ω c ≠ 0 := by rw [← hρ]; exact pow_ne_zero _ h0

        have hξ : (φ ρ / ρ) ^ n = 1 := by
          rw [div_pow, ← map_pow, hρ, hφc, div_self hc]
        obtain ⟨e, he⟩ := hroots _ hξ
        have hφρ : φ ρ = algebraMap F Ω e * ρ := by rw [he, div_mul_cancel₀ _ h0]
        rw [hσ, map_mul, hφζ, hφρ, map_mul, AlgEquiv.commutes,
          pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ q]
        ring
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hρ'
    | algebraMap a =>
      obtain ⟨b, hb⟩ := hφF a
      rw [AlgEquiv.commutes, ← hb]
      exact ((σ ^ q).commutes b).symm
    | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
    | inv y _ hy => simp only [map_inv₀, hy]
    | mul y z _ _ hy hz => simp only [map_mul, hy, hz]
  ·
    have halg : IsAlgebraic F ρ :=
      ⟨Polynomial.X ^ n - Polynomial.C c, (Polynomial.monic_X_pow_sub_C c hn.ne').ne_zero,
        by simp [hρ]⟩
    have hx' : x ∈ Algebra.adjoin F {ρ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
      exact (IntermediateField.mem_toSubalgebra _ _).2 hx
    have havg : ∀ y ∈ Algebra.adjoin F {ρ},
        ∑ k ∈ Finset.range n, (σ ^ k) y ∈ (⊥ : Subalgebra F Ω) := by
      intro y hy
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
      rw [Polynomial.aeval_eq_sum_range]
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [map_sum, map_smul]
      rw [Finset.sum_comm]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      rw [← Finset.smul_sum]
      exact Subalgebra.smul_mem _
        (sum_pow_apply_pow_mem_bot_of_kummer n σ ρ ζ c hρ hζ hζF hσ i) _
    have hall : ∀ k : ℕ, (σ ^ k) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hsx, ih]
    have hsum := havg x hx'
    simp_rw [hall, Finset.sum_const, Finset.card_range] at hsum
    obtain ⟨b, hb⟩ := Algebra.mem_bot.1 hsum
    have hn0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hn0' : (n : Ω) ≠ 0 := by
      rw [← map_natCast (algebraMap F Ω) n]; exact (map_ne_zero _).2 hn0
    refine ⟨b / n, ?_⟩
    rw [map_div₀, hb, map_natCast, nsmul_eq_mul]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod
section
open Module TensorProduct

namespace GlobalTheory.ZModPerp

theorem exists_eq_nsmul_zmod {n r N : ℕ} [NeZero n] (h : r * N = n) (y : ZMod n)
    (hy : N • y = 0) : ∃ z : ZMod n, y = r • z := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using h.symm)
  have h1 : ((N * y.val : ℕ) : ZMod n) = 0 := by
    simpa [nsmul_eq_mul] using hy
  rw [ZMod.natCast_eq_zero_iff] at h1
  replace h1 : N * r ∣ N * y.val := by rwa [mul_comm N r, h]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hN) h1
  refine ⟨(k : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val y, hk]
  simp [nsmul_eq_mul]

theorem dvd_of_forall_mul_eq_zero {n : ℕ} [NeZero n] (x y : ZMod n)
    (h : ∀ a : ZMod n, a * x = 0 → a * y = 0) : x ∣ y := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right x.val n
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x.val n
  have h1 : (m : ZMod n) * x = 0 := by
    have : ((m * x.val : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨k, ?_⟩
      calc m * x.val = m * (Nat.gcd x.val n * k) := by rw [← hk]
        _ = (Nat.gcd x.val n * m) * k := by ring
        _ = n * k := by rw [← hm]
    simpa using this
  obtain ⟨z, hz⟩ := exists_eq_nsmul_zmod hm.symm y (by simpa [nsmul_eq_mul] using h _ h1)
  have h2 := congrArg (Int.cast : ℤ → ZMod n) (Nat.gcd_eq_gcd_ab x.val n)
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val] at h2
  rw [hz, nsmul_eq_mul, h2, mul_assoc]
  exact dvd_mul_right _ _

theorem isPrincipalIdealRing_zmod (n : ℕ) : IsPrincipalIdealRing (ZMod n) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)

theorem baer_zmod (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) := by
  intro I g
  obtain ⟨x, rfl⟩ := ((isPrincipalIdealRing_zmod n).principal I).principal
  have hx : x ∈ Submodule.span (ZMod n) {x} := Submodule.mem_span_singleton_self x
  obtain ⟨c, hc⟩ := dvd_of_forall_mul_eq_zero x (g ⟨x, hx⟩) fun a ha => by
    rw [← smul_eq_mul, ← map_smul]
    have : a • (⟨x, hx⟩ : Submodule.span (ZMod n) {x}) = 0 := Subtype.ext ha
    rw [this, map_zero]
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have : (⟨a • x, hy⟩ : Submodule.span (ZMod n) {x}) = a • ⟨x, hx⟩ := rfl
  rw [this, map_smul g, hc]
  simp [mul_assoc]

theorem exists_dual_ne_zero {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {q : M} (hq : q ≠ 0) : ∃ f : Dual (ZMod n) M, f q ≠ 0 := by
  obtain ⟨x, hx⟩ := ((isPrincipalIdealRing_zmod n).principal
    (LinearMap.ker (LinearMap.toSpanSingleton (ZMod n) M q))).principal
  have hx' : ∀ a : ZMod n, a • q = 0 ↔ x ∣ a := fun a => by
    rw [← Ideal.mem_span_singleton, ← Ideal.submodule_span_eq, ← hx]
    simp
  obtain ⟨c, hc, hc0⟩ : ∃ c : ZMod n, c * x = 0 ∧ c ≠ 0 := by
    by_contra! H
    have := dvd_of_forall_mul_eq_zero x 1 fun a ha => by simp [H a ha]
    exact hq (by simpa using (hx' 1).mpr this)
  have H : ∀ a : ZMod n, a • q = 0 → (RingHom.id (ZMod n)) a • c = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := (hx' a).mp ha
    simp only [RingHom.id_apply, smul_eq_mul]
    linear_combination b * hc
  let φ := LinearPMap.mkSpanSingleton' q c H
  obtain ⟨f, hf⟩ := (baer_zmod n).extension_property φ.domain.subtype
    φ.domain.subtype_injective φ.toFun
  refine ⟨f, ?_⟩
  have := LinearMap.congr_fun hf ⟨q, Submodule.mem_span_singleton_self q⟩
  have h2 := LinearPMap.mkSpanSingleton'_apply_self q c H (Submodule.mem_span_singleton_self q)
  have h3 : f q = c := this.trans h2
  rwa [h3]

theorem baer_of_free {n : ℕ} [NeZero n] (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M] : Module.Baer (ZMod n) M := by
  let b := Module.Free.chooseBasis (ZMod n) M
  refine Module.Baer.of_equiv b.equivFun.symm fun I g => ?_
  choose l hl using fun i => baer_zmod n I ((LinearMap.proj i).comp g)
  exact ⟨LinearMap.pi l, fun x hx => funext fun i => hl i x hx⟩

theorem exists_eq_nsmul_of_free {n r N : ℕ} [NeZero n] (h : r * N = n) {M : Type*}
    [AddCommGroup M] [Module (ZMod n) M] [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (y : M) (hy : N • y = 0) : ∃ z : M, y = r • z := by
  let b := Module.Free.chooseBasis (ZMod n) M
  choose z hz using fun i => exists_eq_nsmul_zmod h (b.equivFun y i) (by
    rw [← Pi.smul_apply, ← map_nsmul, hy, map_zero, Pi.zero_apply])
  refine ⟨b.equivFun.symm z, b.equivFun.injective ?_⟩
  rw [map_nsmul, LinearEquiv.apply_symm_apply]
  exact funext hz

theorem free_of_isCompl {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') : Module.Free R T' := by
  let e := Submodule.prodEquivOfIsCompl T T' h
  have : Module.Finite R T := Module.Finite.of_surjective (T.projectionOnto T' h)
    (Submodule.projectionOnto_surjective h)
  have : Module.Finite R T' := Module.Finite.of_surjective (T'.projectionOnto T h.symm)
    (Submodule.projectionOnto_surjective h.symm)
  have : Module.Projective R T' :=
    Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)
  refine Module.free_of_flat_of_finrank_eq R T' (finrank R M - finrank R T) fun P => ?_
  let := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T') :=
    (e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)
  have := e'.finrank_eq
  rw [finrank_prod, finrank_baseChange, finrank_baseChange] at this
  omega

end GlobalTheory.ZModPerp

namespace GlobalTheory

open ZModPerp

theorem orthogonal_free_of_perfect_alt_zmod :
    ∀ (N r : ℕ) [NeZero (r * N)] (Γ : Type) [AddCommGroup Γ] [Module (ZMod (r * N)) Γ]
      [Module.Free (ZMod (r * N)) Γ] [Module.Finite (ZMod (r * N)) Γ]
      (e : LinearMap.BilinForm (ZMod (r * N)) Γ), e.IsAlt → Function.Bijective e →
      (∀ H : Submodule (ZMod (r * N)) Γ, e.orthogonal (e.orthogonal H) = H) ∧
      ∀ T : Submodule (ZMod (r * N)) Γ, Module.Free (ZMod (r * N)) T →
        (∃ T', IsCompl T T') ∧ Module.Free (ZMod (r * N)) (e.orthogonal T) ∧
        (∀ t ∈ T, N • t = 0 ↔ ∃ t' ∈ T, t = r • t') ∧
        ∀ a : Γ, (∀ t ∈ T, r • e a t = 0) ↔ ∃ h ∈ e.orthogonal T, r • a = r • h := by
  intro N r _ Γ _ _ _ _ e halt hbij
  have hmem : ∀ (H : Submodule (ZMod (r * N)) Γ) (x : Γ),
      x ∈ e.orthogonal H ↔ ∀ y ∈ H, e x y = 0 := fun H x => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun y _ => ⟨halt.isRefl _ _, halt.isRefl _ _⟩
  have hkill : ∀ x : Γ, (r * N) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (r * N)), ZMod.natCast_self, zero_smul]
  refine ⟨fun H => le_antisymm (fun x hx => ?_) (fun x hx => ?_), fun T hT => ?_⟩
  · by_contra hxH
    obtain ⟨f, hf⟩ := exists_dual_ne_zero (n := r * N) (q := H.mkQ x)
      (by simpa using hxH)
    obtain ⟨b, hb⟩ := hbij.2 (f ∘ₗ H.mkQ)
    have hb' : b ∈ e.orthogonal H := (hmem _ _).mpr fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero H).mpr hy,
        map_zero]
    have := halt.isRefl _ _ ((hmem _ _).mp hx b hb')
    rw [hb] at this
    exact hf this
  · exact (hmem _ _).mpr fun y hy => halt.isRefl _ _ ((hmem _ _).mp hy x hx)
  · obtain ⟨p, hp⟩ := (baer_of_free (n := r * N) T).extension_property T.subtype
      T.subtype_injective LinearMap.id
    have hp' : ∀ t : T, p t = t := fun t => LinearMap.congr_fun hp t
    have hc : IsCompl T (LinearMap.ker p) := LinearMap.isCompl_of_proj hp'
    refine ⟨⟨_, hc⟩, ?_, fun t ht => ⟨fun h => ?_, ?_⟩, fun a => ⟨fun h => ?_, ?_⟩⟩
    · have := free_of_isCompl hc
      have : Module.Free (ZMod (r * N)) (Γ ⧸ T) :=
        Module.Free.of_equiv (Submodule.quotientEquivOfIsCompl T _ hc).symm
      have E : e.orthogonal T ≃ₗ[ZMod (r * N)] T.dualAnnihilator :=
        (LinearEquiv.ofBijective e hbij).ofSubmodules _ _ (by
          ext f
          obtain ⟨b, rfl⟩ := hbij.2 f
          simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator, hmem]
          constructor
          · rintro ⟨x, hx, hxb⟩
            rw [← hxb]
            exact hx
          · exact fun h => ⟨b, h, rfl⟩)
      exact Module.Free.of_equiv (E.trans T.dualQuotEquivDualAnnihilator.symm).symm
    · obtain ⟨z, hz⟩ := exists_eq_nsmul_of_free (n := r * N) rfl (⟨t, ht⟩ : T) (Subtype.ext h)
      exact ⟨z, z.2, congrArg Subtype.val hz⟩
    · rintro ⟨t', -, rfl⟩
      rw [← mul_smul, mul_comm, hkill]
    · obtain ⟨l, hl⟩ := exists_eq_nsmul_of_free (n := r * N) (mul_comm N r)
        (M := Dual (ZMod (r * N)) T) (e a ∘ₗ T.subtype) (LinearMap.ext fun t => h t t.2)
      obtain ⟨b, hb⟩ := hbij.2 (l ∘ₗ p)
      refine ⟨a - N • b, (hmem _ _).mpr fun y hy => ?_, ?_⟩
      · have h1 : e a y = N • l ⟨y, hy⟩ := LinearMap.congr_fun hl ⟨y, hy⟩
        have h2 : e b y = l ⟨y, hy⟩ := by
          rw [hb, LinearMap.comp_apply, hp' ⟨y, hy⟩]
        rw [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, sub_self]
      · rw [smul_sub, ← mul_smul, hkill, sub_zero]
    · rintro ⟨h, hh, hah⟩ t ht
      rw [← LinearMap.smul_apply, ← map_nsmul, hah, map_nsmul, LinearMap.smul_apply,
        (hmem _ _).mp hh t ht, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SubstTwoVariablesIdentities
section
namespace GlobalTheory

open MvPowerSeries

theorem hasSubst_pair {τ k : Type} [CommRing k] {z w : MvPowerSeries τ k}
    (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    HasSubst (![z, w] : Fin 2 → MvPowerSeries τ k) :=
  hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simpa

theorem subst_pair_subst_X {k : Type} [CommRing k] (x : PowerSeries k) (i : Fin 2)
    {a : Fin 2 → PowerSeries k} (ha : HasSubst a) :
    subst a (x.subst (X i : MvPowerSeries (Fin 2) k)) = x.subst (a i) := by
  have h1 : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext _
  exact subst_X ha i

theorem subst_pair_subst_shear {k : Type} [CommRing k] (h : MvPowerSeries (Fin 2) k)
    {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) :
    subst (![z, w] : Fin 2 → PowerSeries k)
      (subst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) =
      subst (![z, z + w] : Fin 2 → PowerSeries k) h := by
  have ha : HasSubst (![z, w] : Fin 2 → PowerSeries k) := hasSubst_pair hz hw
  have h1 : HasSubst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext s
  fin_cases s
  · exact subst_X ha 0
  · show subst _ (X 0 + X 1 : MvPowerSeries (Fin 2) k) = z + w
    rw [subst_add ha, subst_X ha, subst_X ha]
    rfl

theorem X_one_dvd_iff_subst_eq_zero {k : Type} [CommRing k] (g : MvPowerSeries (Fin 2) k) :
    X 1 ∣ g ↔ subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) g = 0 := by
  have ha : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) :=
    hasSubst_pair PowerSeries.constantCoeff_X (map_zero _)
  constructor
  · rintro ⟨q, rfl⟩
    rw [subst_mul ha, subst_X ha]
    exact zero_mul _
  · intro hg
    have h1 : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have h2 := subst_comp_subst_apply ha h1 g
    rw [hg, ← coe_substAlgHom h1, map_zero] at h2
    have h3 : rescale (![1, 0] : Fin 2 → k) g = 0 := by
      rw [rescale_eq_subst, h2]
      congr 1
      funext s
      fin_cases s
      · show (1 : k) • (X 0 : MvPowerSeries (Fin 2) k) = substAlgHom h1 (X ())
        rw [substAlgHom_X, one_smul]
      · show (0 : k) • (X 1 : MvPowerSeries (Fin 2) k) = substAlgHom h1 0
        rw [map_zero, zero_smul]
    rw [X_dvd_iff]
    intro m hm
    have h4 := congrArg (coeff m) h3
    rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp)] at h4
    simpa [hm] using h4

theorem subst_two_variables_identities : ∀ (k : Type) [Field k], (∀ h : MvPowerSeries (Fin 2) k, (MvPowerSeries.X 1 ∣ MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h ↔ MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) h = 0) ∧ ∀ z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) = MvPowerSeries.subst (![z, z + w] : Fin 2 → PowerSeries k) h) ∧ ∀ x z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = x.subst z ∧ MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) = x.subst w := by
  intro k _
  refine ⟨fun h => ⟨?_, fun z w hz hw => subst_pair_subst_shear h hz hw⟩, fun x z w hz hw =>
    ⟨subst_pair_subst_X x 0 (hasSubst_pair hz hw), subst_pair_subst_X x 1 (hasSubst_pair hz hw)⟩⟩
  rw [X_one_dvd_iff_subst_eq_zero,
    subst_pair_subst_shear h PowerSeries.constantCoeff_X (map_zero _), add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmPairingEqOneOfOddOfDiag
section
open scoped BigOperators
open Matrix

namespace GlobalTheory

private lemma eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one {U : Type} [CommGroup U] (k : ℕ) (b : ℤ) (hb : (k : ℤ) ∣ 2 * b - 1)
    (u : U) (hu : u ^ k = 1) (h : u ^ b * u ^ b = 1) : u = 1 := by
  obtain ⟨m, hm⟩ := hb
  have h2 : u ^ (2 * b) = 1 := by rw [two_mul, _root_.zpow_add]; exact h
  have hk : u ^ (k : ℤ) = 1 := by rw [zpow_natCast]; exact hu
  have hsplit : 2 * b = k * m + 1 := by linarith
  rw [hsplit, _root_.zpow_add, _root_.zpow_mul, hk, _root_.one_zpow, one_mul, _root_.zpow_one] at h2
  exact h2

private lemma eq_one_of_hom_eq_one_on_basis {X U : Type} [AddCommGroup X] [CommGroup U] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ X) (f : X → U) (hf : ∀ x x', f (x + x') = f x * f x')
    (he : ∀ i, f (e i) = 1) (x : X) : f x = 1 := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    simpa using h
  let g : X →+ Additive U :=
    { toFun := fun x => Additive.ofMul (f x)
      map_zero' := by simp [h0]
      map_add' := fun x x' => by simp [hf] }
  have hg : g.toIntLinearMap = 0 := e.ext fun i => by simp [g, he]
  have hx := LinearMap.congr_fun hg x
  simpa [g] using hx

theorem symm_pairing_eq_one_of_odd_of_diag :
    ∀ (X U : Type) [AddCommGroup X] [CommGroup U] (d k : ℕ) (e : Module.Basis (Fin d) ℤ X) (b : ℤ), Odd k → (k : ℤ) ∣ 2 * b - 1 → ∀ δ : X → X → U, (∀ x x' y, δ (x + x') y = δ x y * δ x' y) → (∀ x y, δ x y = δ y x) → (∀ x y, δ x y ^ k = 1) → (∀ i, δ (e i) (e i) ^ b = 1) → (∀ i j, δ (e i + e j) (e i + e j) ^ b = 1) → ∀ x y, δ x y = 1 := by
  intro X U _ _ d k e b _ hb δ hadd hsymm hk1 hdiag hdiag2
  have hadd2 : ∀ x y y', δ x (y + y') = δ x y * δ x y' := by
    intro x y y'
    rw [hsymm x, hadd, hsymm y, hsymm y']
  have hoff : ∀ i j, δ (e i) (e j) = 1 := by
    intro i j
    have h := hdiag2 i j
    rw [hadd, hadd2, hadd2, hsymm (e j) (e i), _root_.mul_zpow, _root_.mul_zpow, _root_.mul_zpow, hdiag i, hdiag j] at h
    apply eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one k b hb _ (hk1 _ _)
    simpa using h
  have hrow : ∀ i y, δ (e i) y = 1 := fun i =>
    eq_one_of_hom_eq_one_on_basis e (δ (e i)) (hadd2 (e i)) (hoff i)
  intro x y
  exact eq_one_of_hom_eq_one_on_basis e (fun x => δ x y) (fun x x' => hadd x x' y) (fun i => hrow i y) x

end GlobalTheory
end

