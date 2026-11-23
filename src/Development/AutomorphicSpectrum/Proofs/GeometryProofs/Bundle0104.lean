module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanValueBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindex
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem aeval_mul_homog {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {A : Type} [CommRing A] [Algebra ℤ A]
    (g : MRing J₀) (a : K₀ → ℕ) (hg : IsMultiHomog g a) (u : (Σ k, J₀ k) → A) (t : K₀ → A) :
    aeval (fun p => u p * t p.1) g = aeval u g * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, J₀ k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, t k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_comp_ringHom {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (u : σ → A)
    (g : MvPolynomial σ ℤ) : aeval (fun p => φ (u p)) g = φ (aeval u g) := by
  induction g using MvPolynomial.induction_on with
  | C m => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X]

theorem pow_mul_pow_sub_eq {F : Type} [Field F] (x b : F) (hb : b ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    x ^ j * b ^ (n - j) = (x / b) ^ j * b ^ n := by
  have h : b ^ n = b ^ j * b ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [h, div_pow]
  field_simp

theorem ratio_relation_at_complex_points :
    ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)]
      [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
      (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀)
      (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 →
      (∀ j, IsMultiHomog (c j) a) →
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) →
      ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ,
        SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w →
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ y₀ y bk bx i q r n c a hy hqr hr hc hrel z hz hzr w hw
  have hcone : ∀ g : MRing J₀, IsMultiHomog g a →
      mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        MvPolynomial.C (i (aeval y₀ g)) * ∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k := by
    intro g hg
    have h1 : mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        aeval (fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)) g := by
      simp only [mConeMap]
      rw [aeval_rename]
      have e : ((fun p : (Σ k, J k) => (MvPolynomial.C (y p) : MvPolynomial K Ω) * MvPolynomial.X p.1) ∘
          GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) =
          fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1) := by
        funext p
        obtain ⟨k, b⟩ := p
        simp [GlobalTheory.CompanionTheory.Ar.Chg.blkV, hy]
      rw [e]
    rw [h1, aeval_mul_homog g a hg (fun p => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω)) (fun k => MvPolynomial.X (bk k))]
    congr 1
    exact aeval_comp_ringHom ((MvPolynomial.C : Ω →+* MvPolynomial K Ω).comp i) y₀ g
  have hXq : mConeMap y (MvPolynomial.X q) = MvPolynomial.C (y q) * MvPolynomial.X r.1 := by
    simp [mConeMap, hqr]
  have hXr : mConeMap y (MvPolynomial.X r) = MvPolynomial.C (y r) * MvPolynomial.X r.1 := by
    simp [mConeMap]
  let F : MRing J := ∑ j ∈ Finset.range (n + 1),
    rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j) * MvPolynomial.X q ^ j * MvPolynomial.X r ^ (n - j)
  have hF : F ∈ mCoordIdeal y := by
    show mConeMap y F = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_mul, map_pow, hcone _ (hc _), hXq, hXr]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        MvPolynomial.C (i (aeval y₀ (c j))) * (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) *
            (MvPolynomial.C (y q) * MvPolynomial.X r.1) ^ j * (MvPolynomial.C (y r) * MvPolynomial.X r.1) ^ (n - j) =
          (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) * MvPolynomial.X r.1 ^ n *
            MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have e1 : y q ^ j * y r ^ (n - j) = (y q / y r) ^ j * y r ^ n := pow_mul_pow_sub_eq _ _ hr hjn
      have e2 : (MvPolynomial.X r.1 : MvPolynomial K Ω) ^ n = MvPolynomial.X r.1 ^ j * MvPolynomial.X r.1 ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (MvPolynomial.C (y q) : MvPolynomial K Ω) ^ j * MvPolynomial.C (y r) ^ (n - j) =
          MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← e1]; simp only [map_mul, map_pow]
      rw [mul_pow, mul_pow, e2]
      have e4 : (MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) : MvPolynomial K Ω) =
          MvPolynomial.C (i (aeval y₀ (c j))) * MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← map_mul]; congr 1; ring
      rw [e4, ← e3]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, hrel]
    simp
  obtain ⟨s, hs, he⟩ := hw
  have hev := hz.2 F hF
  have hren : ∀ j, eval z (map (Int.castRingHom ℂ) (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j))) =
      (∏ k, s k ^ a k) * eval w (map (Int.castRingHom ℂ) (c j)) := by
    intro j
    rw [map_rename, eval_rename]
    have : z ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx = fun p => s p.1 * w p := he
    rw [this, eval_smul_homog (c j) a (hc j) s w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [F, map_sum, map_mul, map_pow, map_X, eval_X, hren] at hev
  have hP : (∏ k, s k ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)
  have hfin : (∏ k, s k ^ a k) * z r ^ n *
      ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
    rw [← hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [mul_assoc ((∏ k, s k ^ a k) * _), pow_mul_pow_sub_eq _ _ hzr hjn]
    ring
  exact (mul_eq_zero.1 hfin).resolve_left (mul_ne_zero hP (pow_ne_zero _ hzr))

end GlobalTheory.CompanionTheory.Ar.Rel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem labels_all_once : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H)
    (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧
      Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c
  classical
  have hre : H.rt0.re = 0 := by
    have h : (H.rt0 * H.rt0).re = (-(H.d : ℂ)).re := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h
    have h' : (H.rt0 * H.rt0).im = (-(H.d : ℂ)).im := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h'
    have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
    have h1 : H.rt0.re * H.rt0.im = 0 := by linarith
    have h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0 := by nlinarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact mul_self_eq_zero.1 h3
    · nlinarith [mul_self_nonneg H.rt0.re]
  have hconj0 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h0
    have h := H.sqrt_neg_disc_sq
    rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h
    exact H.d_prime.ne_zero h
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    apply hne
    have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · exact h3
  have hsq : ∀ τ : E →+* ℂ, (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    intro τ
    have e1 := congrArg (fun x : 𝓞 E => τ (algebraMap (𝓞 E) E x)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at e1
    rw [H.sqrt_neg_disc_sq]
    exact e1
  have hpm : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 :=
    fun τ => sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ)
  have hcc : ∀ τ : E →+* ℂ, τ (IsCMField.complexConj E (H.rt : E)) = -τ (H.rt : E) := by
    intro τ
    rw [IsCMField.complexEmbedding_complexConj]
    rcases hpm τ with h | h
    · rw [h, hconj0]
    · rw [h, map_neg, hconj0]
  refine ⟨?_, ?_⟩
  · have k1 : ∀ (τ : CMType H) (x : 𝓞 E), ((labelEmb c (Sum.inl τ) x : ℂ)) = τ.1 (x : E) :=
      fun _ _ => rfl
    have k2 : ∀ (τ : CMType H) (x : 𝓞 E),
        ((labelEmb c (Sum.inr τ) x : ℂ)) = τ.1 ((H.bar x : 𝓞 E) : E) := fun _ _ => rfl
    have ext' : ∀ τ τ' : E →+* ℂ, (∀ x : 𝓞 E, τ (x : E) = τ' (x : E)) → τ = τ' := by
      intro τ τ' h
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
    rintro (τ | τ) (τ' | τ') h
    · refine congrArg Sum.inl (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h x)
      rwa [k1, k1] at e
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k1, k2, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e.symm
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k2, k1, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e
    · refine congrArg Sum.inr (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h (H.bar.symm x))
      rwa [k2, k2, RingEquiv.apply_symm_apply] at e
  · let e : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq, τ.2, hconj0]
            exact hneg⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq]
            rcases hpm τ.1 with h | h
            · exact absurd h τ.2
            · rw [h, map_neg, hconj0, neg_neg]⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq])
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq]) }
    have hc : Nat.card (CMType H ⊕ CMType H) = Nat.card (E →+* ℂ) :=
      Nat.card_congr ((Equiv.sumCongr (Equiv.refl _) e).trans (Equiv.sumCompl _))
    rw [hc, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ]

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnit
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.FlatLine

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]

theorem aeval_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (MvPolynomial.comp_aeval_apply (R := ℤ) z σ.toIntAlgHom f).symm

theorem ptsOver_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) : (fun p => σ (z p)) ∈ ptsOver 𝕜 P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_embed, hz.2 f hf, map_zero]

theorem hasVal_embed {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜)
    {z : (Σ k, ι k) → L} {val : L} (h : HasVal y a u z val) : HasVal y a u (fun p => σ (z p)) (σ val) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_embed]
    exact (map_ne_zero σ).2 hfz
  · rw [aeval_embed, aeval_embed, hgz, map_mul]

theorem isSmoothHerm_powH {A : HermLine ι} (hA : IsSmoothHerm A) (k : ℕ) : IsSmoothHerm (powH A k) :=
  ContDiffOn.pow hA k

theorem ptHt_pow (A : HermLine ι) (k : ℕ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) :
    ptHt (fun b => (((k : ℤ) * A.a b : ℤ) : ℝ)) (fun z => (k : ℝ) * Real.log (A.h z)) L w = k * lineHt A L w := by
  have e : ∀ v : FinitePlace L, ∑ b, (((k : ℤ) * A.a b : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) =
      (k : ℝ) • ∑ b, (A.a b : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  simp only [ptHt, lineHt, e]
  rw [← smul_finsum, ← Finset.mul_sum, smul_eq_mul]
  ring

theorem exists_arch_bound {y : (Σ k, ι k) → Ω} {d : ℕ} (hAr : IsArithVar (mCoordIdeal y) d) (hB : Birational y)
    {A : HermLine ι} {k : ℕ} {u : Ω} {c : ℝ} (hS : IsSmoothHerm A)
    (hV : VertBound y (fun b => k * A.a b) u c) :
    ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, val ≠ 0 → HasVal y (fun b => k * A.a b) u z val →
      |(k : ℝ) * Real.log (A.h z) - Real.log ‖val‖| ≤ C := by
  obtain ⟨hu, q, m, hq, hm, -, h1, h2⟩ := hV
  have hP := isSmoothHerm_powH hS k
  obtain ⟨C₁, hC₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound K ι Ω y d hAr hB (powH A k) q m u hP hq hm h1
  obtain ⟨C₂, hC₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound K ι Ω y d hAr hB (powH A k).inv q m u⁻¹ (isSmoothHerm_inv hP) hq hm h2
  refine ⟨max C₁ C₂, fun z hz val hv hval => ?_⟩
  have hp : 0 < A.h z := A.pos z hz.1
  have hn : 0 < ‖val‖ := norm_pos_iff.2 hv
  have b₁ : ‖val‖ ≤ Real.exp C₁ * A.h z ^ k := hC₁ z hz val hval
  have b₂ : ‖val⁻¹‖ ≤ Real.exp C₂ * (A.h z ^ k)⁻¹ := hC₂ z hz val⁻¹ (hasVal_inv hu hz hv hval)
  have l₁ : Real.log ‖val‖ ≤ C₁ + k * Real.log (A.h z) := by
    have := Real.log_le_log hn b₁
    rwa [Real.log_mul (Real.exp_pos _).ne' (pow_pos hp k).ne', Real.log_exp, Real.log_pow] at this
  have l₂ : -Real.log ‖val‖ ≤ C₂ - k * Real.log (A.h z) := by
    have := Real.log_le_log (norm_pos_iff.2 (inv_ne_zero hv)) b₂
    rwa [norm_inv, Real.log_inv, Real.log_mul (Real.exp_pos _).ne' (inv_pos.2 (pow_pos hp k)).ne', Real.log_exp,
      Real.log_inv, Real.log_pow, ← sub_eq_add_neg] at this
  rw [abs_le]
  constructor
  · have := le_max_left C₁ C₂
    linarith
  · have := le_max_right C₁ C₂
    linarith

end GlobalTheory.CompanionTheory.Ar.Ht.FlatLine


open GlobalTheory.CompanionTheory.Ar.Ht.FlatLine in
theorem GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  intro K _ ι _ Ω _ y d hAr hB A k u c hS hk hG hV
  obtain ⟨C, hC⟩ := exists_arch_bound hAr hB hS hV
  refine ⟨(c + C) / k, fun L _ _ w hw => ?_⟩
  obtain ⟨val, hv, hval⟩ := hG L w hw
  have hU := _root_.GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound K ι Ω y d hAr hB (fun b => k * A.a b) u c hV
    (fun z => (k : ℝ) * Real.log (A.h z)) L w hw val hv hval
  rw [ptHt_pow] at hU
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  set S := ∑ σ : L →+* ℂ, ((k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖) with hSdef
  have hSb : |S| ≤ (Module.finrank ℚ L : ℝ) * C := by
    calc |S| ≤ ∑ σ : L →+* ℂ, |(k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : L →+* ℂ, C := Finset.sum_le_sum fun σ _ =>
          hC _ (ptsOver_embed σ hw) _ ((map_ne_zero σ).2 hv) (hasVal_embed σ hval)
      _ = (Module.finrank ℚ L : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]
  have hm : |(Module.finrank ℚ L : ℝ)⁻¹ * S| ≤ C := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul_le_iff₀ hd]
    exact hSb
  have hT : |(k : ℝ) * lineHt A L w| ≤ c + C := by
    have := abs_sub_abs_le_abs_sub ((k : ℝ) * lineHt A L w) ((Module.finrank ℚ L : ℝ)⁻¹ * S)
    linarith
  rw [le_div_iff₀ hk']
  rwa [abs_mul, abs_of_pos hk', mul_comm] at hT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem not_inFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) {r : ℕ} (hr : r.Prime) :
    ¬ InFibre ξ r ⟨centre z, h⟩ := by
  intro hf
  apply hf
  have hs : genMap ξ ⟨centre z, h⟩ (r : X.presheaf.stalk (centre z)) = (r : Ω) := map_natCast _ r
  have hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
  have hu : IsUnit (r : X.presheaf.stalk (centre z)) := CxVal.isUnit _ (by
    rw [hz]; exact_mod_cast hr.ne_zero)
  refine ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hs⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).val, ?_⟩
  rw [map_units_inv, hu', hs]

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

theorem sabMap_cast_φ {S₁ S₂ : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f f' : S₁ ⟶ S₂} (e : f = f')
    (m : SABMap t₁ t₂ f) : (e ▸ m : SABMap t₁ t₂ f').φ = m.φ := by
  subst e
  rfl

theorem exists_sabMap (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f) :
    ∃ m : SABMap 𝔐.t 𝔐₀.t h, 𝔐.m.φ = m.φ ≫ 𝔐₀.m.φ := by
  obtain ⟨m, e⟩ := sabCancel pullCubCancel E H _ _ _ Y.t 𝔐₀.t 𝔐.t 𝔐₀.f h 𝔐₀.m (hf ▸ 𝔐.m)
  exact ⟨m, by rw [← e, sabMap_cast_φ]⟩

theorem mem_abLocus_iff (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f)
    (x : 𝔐.X) : x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus 𝔐₀.t.G := by
  obtain ⟨m, -⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  have hp : IsPullback m.φ 𝔐.t.G.hom 𝔐₀.t.G.hom h := m.cart.1
  exact (abLocus_pullback abLocusOne 𝔐₀.t.semi hp x).symm

end Cover

section Maps

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem finrank_comp' {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C) :
    (letI := (g.comp f).toAlgebra; Module.finrank A C) =
      (letI := f.toAlgebra; Module.finrank A B) * (letI := g.toAlgebra; Module.finrank B C) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank A B C).symm

theorem coordsAt_orbit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w w' : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (ho : SameOrbit w' w) : CoordsAt ξ y z w' := by
  obtain ⟨c, hc, rfl⟩ := ho
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := hw.1 k
    exact ⟨a, IsUnit.mk0 _ (mul_ne_zero (hc k) ha.ne_zero)⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := IsUnit.mk0 _ fun h0 => ha.ne_zero (by simp [h0])
    obtain ⟨h1, h2⟩ := hw.2 k a ha'
    refine ⟨h1, fun b => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 b
    exact ⟨r, hr, by simp only [e]; ring⟩

end Maps

section Orbit

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_sub_orbit {A B : HermLine J} (hab : A.a = B.a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) - Real.log (B.h w) = Real.log (A.h z) - Real.log (B.h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [log_h_smul A hc hz, log_h_smul B hc hz, hab]
  ring

theorem log_sum_orbit {X : Type} (s : Finset X) {A : HermLine J} {B : X → HermLine J}
    (hab : A.a = -∑ x ∈ s, (B x).a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ x ∈ s, Real.log ((B x).h w) = Real.log (A.h z) + ∑ x ∈ s, Real.log ((B x).h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  simp only [log_h_smul _ hc hz, Finset.sum_add_distrib]
  have : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ = -∑ x ∈ s, ∑ k, ((B x).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hab, ← Finset.sum_mul, ← neg_mul]
    simp [Finset.sum_apply]
  rw [this]
  ring

theorem pullDeg_neg_sum {K₀ : Type} {X : Type} {κ : K₀ → K} (hκ : Function.Injective κ) (s : Finset X) (f : X → K₀ → ℤ) :
    pullDeg κ (-∑ x ∈ s, f x) = -∑ x ∈ s, pullDeg κ (f x) := by
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    simp [pullDeg, hκ.extend_apply, Finset.sum_apply]
  · simp [pullDeg, Function.extend_apply' _ _ _ hk, Finset.sum_apply]

theorem log_tensor_pull {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {κ : K₀ → K}
    {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (A : HermLine J₀) (T : HermLine J) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((pullHerm hv A).tensor T).h z) = Real.log (A.h fun p => z (v p)) + Real.log (T.h z) :=
  Real.log_mul ((pullHerm hv A).pos z hz).ne' (T.pos z hz).ne'

end Orbit

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

