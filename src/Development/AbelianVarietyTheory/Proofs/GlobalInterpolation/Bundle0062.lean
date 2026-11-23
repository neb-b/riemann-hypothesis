module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIff
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OverCompare

def genSums (F : Type) {E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) :
    AddSubgroup (Fin k → E ⊗[F] R) where
  carrier := {u | ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j}
  zero_mem' := ⟨0, fun _ => zero_mem _, by funext i; simp⟩
  add_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    refine ⟨t + t', fun j => add_mem (ht j) (ht' j), ?_⟩
    funext i
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨-t, fun j => neg_mem (ht j), ?_⟩
    funext i
    simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem tmul_mem_genSums {F E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
    {x : Fin k → E} (hx : x ∈ Submodule.span ℤ (Set.range l)) {s : R} (hs : s ∈ S₂) :
    (fun i => x i ⊗ₜ[F] s) ∈ genSums F l R S₂ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨fun j => c j • s, fun j => zsmul_mem hs _, ?_⟩
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul]

theorem exists_int_generators {E : Type} [Field E] [NumberField E] {k : ℕ}
    (Λ : Submodule (𝓞 E) (Fin k → E)) [Module.Finite (𝓞 E) Λ] :
    ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧
      ∀ x ∈ Λ, x ∈ Submodule.span ℤ (Set.range l) := by
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  refine ⟨m, fun j => (s j : Fin k → E), fun j => (s j).2, fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem exists_generators_mem_latS_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  intro F E _ _ _ _ _ k Λ hΛ
  obtain ⟨m, l, hl, hgen⟩ := exists_int_generators Λ
  refine ⟨m, l, hl, fun R _ _ S₂ u => ⟨fun hu => ?_, ?_⟩⟩
  · show u ∈ genSums F l R S₂
    have hst : ∀ s ∈ tensInt (F := F) R (intOE E) S₂, ∀ v ∈ genSums F l R S₂,
        s • v ∈ genSums F l R S₂ := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem x hx =>
        rintro _ ⟨t, ht, rfl⟩
        rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
        · have e : ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j := by
            funext i
            simp [Finset.mul_sum, Algebra.smul_def]
          rw [show ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j from e]
          exact sum_mem fun j _ =>
            tmul_mem_genSums l R S₂ (hgen _ (Λ.smul_mem a (hl j))) (ht j)
        · refine ⟨fun j => (y : R) * t j, fun j => mul_mem y.2 (ht j), ?_⟩
          funext i
          simp [Finset.mul_sum]
      | zero => intro v _; rw [zero_smul]; exact zero_mem _
      | one => intro v hv; rwa [one_smul]
      | add x y _ _ hx hy => intro v hv; rw [add_smul]; exact add_mem (hx v hv) (hy v hv)
      | neg x _ hx => intro v hv; rw [neg_smul]; exact neg_mem (hx v hv)
      | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy v hv)
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact tmul_mem_genSums l R S₂ (hgen y hy) (one_mem _)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hst a a.2 x hx
  · rintro ⟨t, ht, rfl⟩
    have e : (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
        ∑ j, (⟨(1 : E) ⊗ₜ[F] t j, Subring.subset_closure (Or.inr ⟨⟨t j, ht j⟩, rfl⟩)⟩ :
          tensInt (F := F) R (intOE E) S₂) • (fun i => inclE (F := F) R (l j i)) := by
      funext i
      simp [inclE, Subring.smul_def]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l j, hl j, rfl⟩)

end GlobalTheory.OverCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSecondFunctional
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.SecondFunctional

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem mem_primeOf_prPbar {σ : E →ₐ[F] E}
    {φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hφ : IsSplitting σ v φ) (a : intV E v) :
    a ∈ primeOf (prPbar φ) ↔ Valued.v (prPbar φ a) < 1 := by
  refine ⟨fun h => ?_, fun h => Ideal.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    have hc : Valued.v (prPbar φ c) ≤ 1 := ((hφ.2.2 c).1 c.2).2
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le' hx

theorem exists_max {ι : Type} (g : ι → WithZero (Multiplicative ℤ)) (t : WithZero (Multiplicative ℤ))
    (ht : t ≠ 0) (hb : ∀ y, t * g y ≤ 1) (y₁ : ι) (h₁ : g y₁ ≠ 0) : ∃ y₀, ∀ y, g y ≤ g y₀ := by
  obtain ⟨n, ⟨y₀, hy₀⟩, hn⟩ := Int.exists_greatest_of_bdd (P := fun n => ∃ y, g y = WithZero.exp n)
    ⟨-WithZero.log t, fun z ⟨y, hy⟩ => by
      have := hb y
      rw [hy, ← WithZero.exp_log ht, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      omega⟩ ⟨_, y₁, (WithZero.exp_log h₁).symm⟩
  refine ⟨y₀, fun y => ?_⟩
  by_cases hy : g y = 0
  · rw [hy]; exact zero_le'
  · rw [hy₀, ← WithZero.exp_log hy, WithZero.exp_le_exp]
    exact hn _ ⟨y, (WithZero.exp_log hy).symm⟩

theorem hform_add_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y z : n → A) : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (a : A) : hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_nsmul_left {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (T : ℕ) : hform σ J (T • x) y = T * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 800000 in
theorem exists_second_functional :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) (L₁ L₂ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ y ∈ L₁, ∀ x ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → ∀ (T : ℕ), T ≠ 0 → (∀ x ∈ L₂, T • x ∈ L₁) → (∃ x ∈ L₂, x ∉ L₁ ∧ ∀ i, prPbar s (x i) = 0) → ∃ f : L₂ →ₗ[intV E v] (intV E v ⧸ primeOf (prPbar s)), Function.Surjective f ∧ (∀ x : L₂, x.1 ∈ L₁ → f x = 0) ∧ ∀ x : L₂, (∀ i, prPbar s (x.1 i) = 0) → f x = 0 := by
  intro F E _ _ _ _ _ σ v s hs k J L₁ L₂ h1 h2 T hT hTL ⟨x, hx2, hx1, hx0⟩
  obtain ⟨H, hH⟩ : ∃ H : (Fin k → E ⊗[F] v.adicCompletion F) → E ⊗[F] v.adicCompletion F,
    ∀ y, H y = hform (sigR σ (v.adicCompletion F)) J x y := ⟨_, fun _ => rfl⟩
  have e2 : ∀ a, prPbar s a = (s a).2 := fun _ => rfl
  have hfst : ∀ y, (s (H y)).1 = 0 := by
    intro y
    have : ∀ i, prP s (sigR σ (v.adicCompletion F) (x i)) = 0 := fun i =>
      (congrArg Prod.fst (hs.2.1 (x i))).trans (hx0 i)
    show prP s (H y) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, hform, map_sum, map_mul, this, zero_mul, Finset.sum_const_zero]
  have hTK : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT)
  obtain ⟨y₁, hy₁, hy₁'⟩ : ∃ y ∈ L₂, H y ∉ intV E v := by
    by_contra hc
    push_neg at hc
    exact hx1 ((h2 x).2 fun y hy => hH y ▸ hc y hy)
  have hgt : 1 < Valued.v (prPbar s (H y₁)) := by
    by_contra hc
    exact hy₁' ((hs.2.2 _).2 ⟨by rw [hfst]; exact zero_mem _, not_lt.1 hc⟩)
  obtain ⟨y₀, hy₀⟩ := exists_max (fun y : L₂ => Valued.v (prPbar s (H y))) (Valued.v (T : v.adicCompletion F))
    (by simpa using hTK) (fun y => by
      have h := ((hs.2.2 _).1 ((h2 _).1 (hTL x hx2) y y.2)).2
      rw [hform_nsmul_left, ← e2, map_mul, map_natCast, ← hH] at h
      rw [← map_mul]; exact h) ⟨y₁, hy₁⟩ (ne_of_gt (lt_trans zero_lt_one hgt))
  obtain ⟨c, hc⟩ : ∃ c, c = prPbar s (H y₀) := ⟨_, rfl⟩
  replace hy₀ : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ Valued.v c := hc ▸ hy₀
  have hc1 : 1 < Valued.v c := lt_of_lt_of_le hgt (hy₀ ⟨y₁, hy₁⟩)
  have hcv : 0 < Valued.v c := lt_trans zero_lt_one hc1
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hcv; exact lt_irrefl _ hcv
  obtain ⟨d, hd⟩ : ∃ d, d = s.symm (0, c⁻¹) := ⟨_, rfl⟩
  have hd2 : ∀ y, prPbar s (H y * d) = prPbar s (H y) / c := fun y => by
    rw [map_mul, e2 d, hd, s.apply_symm_apply, div_eq_mul_inv]
  have hmem : ∀ y : L₂, H y * d ∈ intV E v := fun y => by
    refine (hs.2.2 _).2 ⟨?_, ?_⟩
    · rw [map_mul, Prod.fst_mul, hfst, zero_mul]; exact zero_mem _
    · show Valued.v (prPbar s (H y * d)) ≤ 1
      rw [hd2, map_div₀, div_le_one₀ hcv]
      exact hy₀ y
  let g : L₂ →ₗ[intV E v] intV E v :=
    { toFun := fun y => ⟨H y * d, hmem y⟩
      map_add' := fun y z => Subtype.ext (by
        show H (y.1 + z.1) * d = H y * d + H z * d
        simp only [hH, hform_add_right, add_mul])
      map_smul' := fun a y => Subtype.ext (by
        show H ((a : E ⊗[F] v.adicCompletion F) • y.1) * d = a * (H y * d)
        simp only [hH, hform_smul_right, mul_assoc]) }
  have hg : ∀ y : L₂, prPbar s (g y) = prPbar s (H y) / c := fun y => hd2 y
  have hz : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ 1 → (primeOf (prPbar s)).mkQ (g y) = 0 := by
    intro y hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_primeOf_prPbar hs, hg, map_div₀,
      div_lt_one₀ hcv]
    exact lt_of_le_of_lt hy hc1
  refine ⟨(primeOf (prPbar s)).mkQ ∘ₗ g, fun b => ?_, fun y hy => hz y ?_, fun y hy => hz y ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨a • y₀, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_primeOf_prPbar hs, map_smul,
      smul_eq_mul, AddSubgroupClass.coe_sub, Subring.coe_mul, map_sub, map_mul, hg, ← hc, div_self hc0]
    simp
  · rw [hH]; exact ((hs.2.2 _).1 (h1 y hy x hx2)).2
  · have : prPbar s (H y) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hH, hform, map_sum, map_mul, hy, mul_zero, Finset.sum_const_zero]
    rw [this]; simp

end GlobalTheory.SecondFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTensorCoord
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.RootSplitting

section General

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem one_tmul_injective {a b : K} (h : (1 : E) ⊗ₜ[F] a = (1 : E) ⊗ₜ[F] b) : a = b :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := K)
    (algebraMap F E).injective h

theorem algebraMap_tmul (t : F) :
    (algebraMap F E t) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (algebraMap F K t) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_basis (hdeg : Module.finrank F E = 2) (θ : E) (hθ : θ ∉ (algebraMap F E).range) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = θ := by
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    exact hθ ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdeg]), ?_, ?_⟩ <;> simp

theorem exists_coord (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ) (x : E) :
    ∃ p q : F, x = p • (1 : E) + q • θ :=
  ⟨b.repr x 0, b.repr x 1, by
    have := b.sum_repr x
    rw [Fin.sum_univ_two, h0, h1] at this
    exact this.symm⟩

theorem exists_algHom (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ)
    (t n : F) (hθ : θ * θ = (-n) • (1 : E) + t • θ) (r : K) (hr : r * r = (-n) • (1 : K) + t • r) :
    ∃ φ : E →ₐ[F] K, φ θ = r := by
  let f : E →ₗ[F] K := b.constr F ![1, r]
  have f0 : f 1 = 1 := by rw [← h0]; simp [f]
  have f1 : f θ = r := by rw [← h1]; simp [f]
  refine ⟨AlgHom.ofLinearMap f f0 fun x y => ?_, f1⟩
  obtain ⟨p, q, rfl⟩ := exists_coord b h0 h1 x
  obtain ⟨p', q', rfl⟩ := exists_coord b h0 h1 y
  simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, hθ, hr, map_add (f := _), map_smul,
    f0, f1]

theorem exists_tensor_coord (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ)
    (x : E ⊗[F] K) : ∃ a c : K, x = (1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul e k =>
    obtain ⟨p, q, rfl⟩ := exists_coord b h0 h1 e
    exact ⟨p • k, q • k, by rw [TensorProduct.add_tmul, TensorProduct.smul_tmul,
      TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, c, rfl⟩ := hx
    obtain ⟨a', c', rfl⟩ := hy
    exact ⟨a + a', c + c', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩

theorem exists_ringEquiv (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (θ : E) (r r' : K) (hne : r - r' ≠ 0)
    (ht : (θ + σ θ) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (r + r'))
    (hn : (θ * σ θ) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (r * r')) :
    ∃ (s : E ⊗[F] K ≃+* K × K) (φ : E →ₐ[F] K), φ θ = r ∧ φ (σ θ) = r' ∧
      ∀ (e : E) (k : K), s (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k) := by
  obtain ⟨t, ht'⟩ := hfix (θ + σ θ) (by rw [map_add (f := _), hσ, add_comm])
  obtain ⟨n, hn'⟩ := hfix (θ * σ θ) (by rw [map_mul, hσ, mul_comm])
  have htK : algebraMap F K t = r + r' := by
    rw [← ht', algebraMap_tmul] at ht; exact one_tmul_injective ht
  have hnK : algebraMap F K n = r * r' := by
    rw [← hn', algebraMap_tmul] at hn; exact one_tmul_injective hn
  have hθ : θ ∉ (algebraMap F E).range := by
    rintro ⟨a, rfl⟩
    rw [AlgHom.commutes, ← map_add (f := _)] at ht'
    rw [AlgHom.commutes, ← map_mul] at hn'
    obtain rfl := (algebraMap F E).injective ht'
    obtain rfl := (algebraMap F E).injective hn'
    rw [map_add (f := _)] at htK
    rw [map_mul] at hnK
    apply hne
    have : (r - r') ^ 2 = 0 := by
      linear_combination (-(r + r' + 2 * algebraMap F K a)) * htK + 4 * hnK
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  obtain ⟨b, h0, h1⟩ := exists_basis hdeg θ hθ
  obtain ⟨φ, hφ⟩ := exists_algHom b h0 h1 t n
    (by simp only [Algebra.smul_def, map_neg, ht', hn']; ring) r
    (by simp only [Algebra.smul_def, map_neg, htK, hnK]; ring)
  have hφ' : φ (σ θ) = r' := by
    have := congrArg φ ht'
    rw [AlgHom.commutes, map_add (f := _), hφ, htK] at this
    exact (add_left_cancel this).symm
  let g : E ⊗[F] K →ₐ[F] K × K :=
    (Algebra.TensorProduct.lift φ (AlgHom.id F K) fun _ _ => Commute.all _ _).prod
      (Algebra.TensorProduct.lift (φ.comp σ) (AlgHom.id F K) fun _ _ => Commute.all _ _)
  have hg : ∀ (e : E) (k : K), g (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k) := fun e k => rfl
  have hg2 : ∀ a c : K, g ((1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c) = (a + r * c, a + r' * c) := by
    intro a c
    rw [map_add (f := _), hg, hg, hφ, hφ']; simp
  refine ⟨RingEquiv.ofBijective g ⟨?_, ?_⟩, φ, hφ, hφ', hg⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := exists_tensor_coord b h0 h1 x
    rw [hg2, Prod.mk_eq_zero] at hx
    have hc : c = 0 := by
      have : (r - r') * c = 0 := by linear_combination hx.1 - hx.2
      exact (mul_eq_zero.1 this).resolve_left hne
    have ha : a = 0 := by simpa [hc] using hx.1
    simp [ha, hc]
  · rintro ⟨a, c⟩
    refine ⟨(1 : E) ⊗ₜ[F] (c - r' * ((a - c) / (r - r'))) + θ ⊗ₜ[F] ((a - c) / (r - r')), ?_⟩
    rw [hg2]
    congr 1
    · field_simp; ring
    · ring

end General

theorem exists_isSplitting (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F)) (θ : E)
    (r r' : v.adicCompletionIntegers F) (hθ : IsIntegral ℤ θ) (hu : IsUnit (r - r'))
    (ht : (θ + σ θ) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] ((r : v.adicCompletion F) + r'))
    (hn : (θ * σ θ) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] ((r : v.adicCompletion F) * r')) :
    ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      IsSplitting σ v s ∧
      s (θ ⊗ₜ[F] (1 : v.adicCompletion F)) =
        ((r : v.adicCompletion F), (r' : v.adicCompletion F)) := by
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  have huK : ((r : v.adicCompletion F) - r') * u = 1 := by exact_mod_cast congrArg Subtype.val hu'
  have hne : (r : v.adicCompletion F) - r' ≠ 0 := left_ne_zero_of_mul_eq_one huK
  obtain ⟨s, φ, h1, h2, hs⟩ := exists_ringEquiv σ hdeg hσ hfix θ _ _ hne ht hn
  have hint : ∀ x : E, IsIntegral ℤ x → φ x ∈ v.adicCompletionIntegers F := by
    intro x hx
    obtain ⟨p, hp, hp0⟩ := map_isIntegral_int φ hx
    have h4 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
      ⟨p.map (Int.castRingHom _), hp.map _, by
        rw [Polynomial.eval₂_map]
        exact (congrArg (fun f => Polynomial.eval₂ f (φ x) p) (RingHom.ext_int _ _)).trans hp0⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h4
    exact hy ▸ y.2
  have hone : ∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a; rw [hs]; simp
  refine ⟨s, ⟨hone, fun x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, by rw [hs, h1, h2]; simp⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e k =>
      have : sigR σ (v.adicCompletion F) (e ⊗ₜ[F] k) = σ e ⊗ₜ[F] k := rfl
      rw [this, hs, hs, hσ]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩
      · simp only [hs, mul_one]
        exact ⟨hint _ a.2, hint _ (IsIntegral.map (σ : E →+* E).toIntAlgHom a.2)⟩
      · simp only [hone]; exact ⟨a.2, a.2⟩
    | zero => simp
    | one => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · have hm : ∀ a ∈ v.adicCompletionIntegers F, (1 : E) ⊗ₜ[F] a ∈ intV E v := fun a ha =>
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hθm : θ ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v :=
      GlobalTheory.OverCompare.tmul_mem_intV (⟨θ, hθ⟩ : 𝓞 E)
    have hc : ((s x).1 - (s x).2) * u ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem hx.1 hx.2) u.2
    have : x = (1 : E) ⊗ₜ[F] ((s x).2 - r' * (((s x).1 - (s x).2) * u)) +
        θ ⊗ₜ[F] (1 : v.adicCompletion F) * (1 : E) ⊗ₜ[F] (((s x).1 - (s x).2) * u) := by
      apply s.injective
      rw [map_add (f := _), map_mul, hone, hone, hs, h1, h2]
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_mul]
        linear_combination (-((s x).1 - (s x).2)) * huK
      · simp only [Prod.snd_add, Prod.snd_mul]; ring
    rw [this]
    exact add_mem (hm _ (sub_mem hx.2 (mul_mem r'.2 hc))) (mul_mem hθm (hm _ hc))

end GlobalTheory.RootSplitting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemRangeBcOfTransposeMulEqOne
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare

theorem mem_range_bc_of_transpose_mul_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {n : Type} [Fintype n] [DecidableEq n] (A B : GL n S)
    (hAB : (A : Matrix n n S)ᵀ * (B : Matrix n n S) = 1) (hA : A ∈ (bc (n := n) f).range) :
    B ∈ (bc (n := n) f).range := by
  obtain ⟨a, rfl⟩ := hA
  let a' : GL n R := ⟨((a⁻¹ : GL n R) : Matrix n n R)ᵀ, (a : Matrix n n R)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  refine ⟨a', Units.ext ?_⟩
  have h1 : ((bc f a' : GL n S) : Matrix n n S) = ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ := by
    ext i j; rfl
  have h2 : ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ * ((bc f a : GL n S) : Matrix n n S)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, map_inv, Units.mul_inv, Matrix.transpose_one]
  rw [h1]
  calc ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ
      = ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ *
          (((bc f a : GL n S) : Matrix n n S)ᵀ * (B : Matrix n n S)) := by rw [hAB, Matrix.mul_one]
    _ = (B : Matrix n n S) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem mem_stabGL_iff_of_dual_frames : ∀ (K : Type) [Field K] (O : ValuationSubring K) (k : ℕ)
    (J : Matrix (Fin k) (Fin k) K) (b c g h : GL (Fin k) K) (Λ Λ' : Submodule O (Fin k → K)),
    GlobalTheory.OverCompare.IsFrame Λ b → GlobalTheory.OverCompare.IsFrame Λ' c →
    (b : Matrix (Fin k) (Fin k) K)ᵀ * J * (c : Matrix (Fin k) (Fin k) K) = 1 →
    (g : Matrix (Fin k) (Fin k) K)ᵀ * J * (h : Matrix (Fin k) (Fin k) K) = J →
    (g ∈ stabGL Λ ↔ h ∈ stabGL Λ') := by
  intro K _ O k J b c g h Λ Λ' hb hc hJ hg
  have hJ' : ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
      ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = J := by
    have e1 : ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
        (b : Matrix (Fin k) (Fin k) K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc _ = ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
          ((b : Matrix (Fin k) (Fin k) K)ᵀ * J * (c : Matrix (Fin k) (Fin k) K)) *
          ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) := by rw [hJ, Matrix.mul_one]
      _ = (((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
          (b : Matrix (Fin k) (Fin k) K)ᵀ) * J * ((c : Matrix (Fin k) (Fin k) K) *
          ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have key : ((b⁻¹ * g * b : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
      ((c⁻¹ * h * c : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 := by
    calc _ = (b : Matrix (Fin k) (Fin k) K)ᵀ * ((g : Matrix (Fin k) (Fin k) K)ᵀ *
          (((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
          ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) * (h : Matrix (Fin k) (Fin k) K)) *
          (c : Matrix (Fin k) (Fin k) K) := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ', hg, hJ]
  rw [hb.mem_stabGL_iff, hc.mem_stabGL_iff]
  refine ⟨mem_range_bc_of_transpose_mul_eq_one _ _ _ key,
    mem_range_bc_of_transpose_mul_eq_one _ _ _ ?_⟩
  have := congrArg Matrix.transpose key
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

end GlobalTheory.OverCompare
end

