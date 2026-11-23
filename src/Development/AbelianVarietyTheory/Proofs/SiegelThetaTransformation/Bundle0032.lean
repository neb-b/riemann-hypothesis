module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticDoubledHermitianCoordinates
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem cc_cc (a : E) : cc (cc a) = a := by
  unfold cc
  exact IsCMField.complexConj_apply_apply E a

theorem cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a := by
  unfold cc
  exact Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem sum_trace {ι : Type} [Fintype ι] (B : Module.Basis ι ℚ E) (b d : E) :
    ∑ j, Algebra.trace ℚ E (b * cc (B j)) * B.repr d j = Algebra.trace ℚ E (b * cc d) := by

  have hd : cc d = ∑ j, B.repr d j • cc (B j) := by
    conv_lhs => rw [← B.sum_repr d]
    unfold cc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_rat_smul _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

theorem vec_inl (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = y₁ a - y₂ a := by
  simp [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

theorem vec_inr (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) = X.κ0 / 4 * ∑ c, (y₁ c + y₂ c) * X.Gm c a := by
  simp only [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem split_form (y₁ y₂ z₁ z₂ : Fin r → E) :
    ∑ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inl a)) -
      ∑ a, cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inr a)) * (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) =
      -(X.κ0 / 2) * herm X.Gm y₂ z₂ - -(X.κ0 / 2) * herm X.Gm y₁ z₁ := by

  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by unfold cc; exact map_add _ a b
  have hsub : ∀ a b : E, cc (a - b) = cc a - cc b := fun a b => by unfold cc; exact map_sub _ a b
  have hsum : ∀ f : Fin r → E, cc (∑ c, f c) = ∑ c, cc (f c) := fun f => by
    unfold cc; exact map_sum _ _ _
  have hk : cc (X.κ0 / 4) = -(X.κ0 / 4) := by
    have h4 : cc (4 : E) = 4 := by unfold cc; exact map_ofNat _ 4
    have hd : cc (X.κ0 / 4) = cc X.κ0 / cc 4 := by unfold cc; exact map_div₀ _ _ _
    rw [hd, h4, DblPer.cc_kappa X, neg_div]
  simp only [vec_inl, vec_inr, cc_mul, hadd, hsub, hsum, hk, X.Gm_herm, herm]
  simp only [Finset.mul_sum, Finset.sum_mul]

  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

noncomputable def dv (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) : Fin r ⊕ Fin r → E :=
  Sum.elim (vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)))
    (vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)))) ᵥ* dblT X

theorem dv_add (u v) : dv X bas (u + v) = dv X bas u + dv X bas v := by
  have h₁ : Sum.elim ((u + v).1 ∘ Sum.inl) ((u + v).2 ∘ Sum.inl) =
      Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) + Sum.elim (v.1 ∘ Sum.inl) (v.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((u + v).1 ∘ Sum.inr) (-((u + v).2 ∘ Sum.inr)) =
      Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) + Sum.elim (v.1 ∘ Sum.inr) (-(v.2 ∘ Sum.inr)) := by
    ext (i | i)
    · rfl
    · simp only [Sum.elim_inr, Pi.neg_apply, Function.comp_apply, Prod.snd_add, Pi.add_apply]
      ring
  unfold dv
  rw [h₁, h₂, vecQ_add, vecQ_add, ← Matrix.add_vecMul, Sum.elim_add_add]

theorem dv_smul (q : ℚ) (u) : dv X bas (q • u) = q • dv X bas u := by
  have h₁ : Sum.elim ((q • u).1 ∘ Sum.inl) ((q • u).2 ∘ Sum.inl) =
      q • Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((q • u).1 ∘ Sum.inr) (-((q • u).2 ∘ Sum.inr)) =
      q • Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) := by
    ext (i | i) <;> simp
  have h₃ : ∀ f g' : Fin r → E, Sum.elim (q • f) (q • g') = q • Sum.elim f g' := fun f g' => by
    ext (i | i) <;> rfl
  unfold dv
  rw [h₁, h₂, vecQ_smul, vecQ_smul, h₃, Matrix.smul_vecMul]

noncomputable def crdMap : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ]
    ((QI E r → ℚ) × (QI E r → ℚ)) where
  toFun u := (fun p => Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)),
    fun p => (Module.finBasis ℚ E).repr (dv X bas u (Sum.inl p.1)) p.2)
  map_add' u v := by
    ext p <;> simp [dv_add, add_mul]
  map_smul' q u := by
    ext p <;> simp [dv_smul]

theorem crdMap_pair (u v) : (crdMap X bas u).1 ⬝ᵥ (crdMap X bas v).2 =
    Algebra.trace ℚ E (∑ a, dv X bas u (Sum.inr a) * cc (dv X bas v (Sum.inl a))) := by
  have e₁ : ∀ p : QI E r, (crdMap X bas u).1 p =
      Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)) := fun p => rfl
  have e₂ : ∀ p : QI E r, (crdMap X bas v).2 p =
      (Module.finBasis ℚ E).repr (dv X bas v (Sum.inl p.1)) p.2 := fun p => rfl
  simp only [dotProduct, e₁, e₂]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.sum_prod_type, map_sum (Algebra.trace ℚ E)]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [sum_trace (Module.finBasis ℚ E) (dv X bas u (Sum.inr a)) (dv X bas v (Sum.inl a))]

theorem dbl_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ), IsSympl X bas → ∃ F : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ] ((QI E r → ℚ) × (QI E r → ℚ)), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) ∧ ∀ (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) (y₁ y₂ : Fin r → E), y₁ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) → y₂ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) → (∀ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = ∑ j, (F u).2 (a, j) • Module.finBasis ℚ E j) ∧ ∀ a j, (F u).1 (a, j) = Algebra.trace ℚ E ((Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc (Module.finBasis ℚ E j)) := by
  intro E _ _ _ r X g bas hs
  refine ⟨crdMap X bas, fun u v => ?_, fun u y₁ y₂ h₁ h₂ => ?_⟩
  ·
    have hsum : ∀ f : Fin r → E, cc (∑ a, f a) = ∑ a, cc (f a) := fun f => by
      unfold cc; exact map_sum _ _ _
    have hsw : (crdMap X bas u).2 ⬝ᵥ (crdMap X bas v).1 =
        Algebra.trace ℚ E (∑ a, cc (dv X bas v (Sum.inr a)) * dv X bas u (Sum.inl a)) := by
      rw [dotProduct_comm, crdMap_pair, ← trace_cc, hsum]
      simp only [cc_mul, cc_cc]
    rw [crdMap_pair, hsw, ← map_sub]
    unfold dv
    rw [split_form, map_sub, ← EF_def, ← EF_def, EF_vecQ hs, EF_vecQ hs]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Pi.neg_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_neg, neg_mul]
    ring
  · subst h₁ h₂
    exact ⟨fun a => ((Module.finBasis ℚ E).sum_repr _).symm, fun a j => rfl⟩

end GlobalTheory.SW.DblLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GenLatCmp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_std (v : Fin n → E) : v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff (v i)

theorem std_eq : Formalism.L2.Pj.stdLat E n = stdL E n := by
  apply le_antisymm
  · intro v hv
    rw [mem_std] at hv
    have : v = ∑ i, (⟨v i, hv i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_std]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

theorem span_smul_le (k : ℕ) (A B : Lt E n) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (k : E) • v ∈ B := by
  have e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← e]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [e]; exact h v hv

theorem natCast_smul_mem (k : ℕ) {A : Lt E n} {v : Fin n → E} (hv : v ∈ A) : (k : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.toAddSubgroup.nsmul_mem hv k

theorem fg_of_smul_le {Λ : Lt E n} {s : ℕ} (hs : 0 < s) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ.FG := by
  have h0 : (stdL E n).FG := Submodule.fg_span (Set.finite_range _)
  have h1 := h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))
  refine h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩
  have : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  simp [smul_smul, this]

variable [IsCMField E]

theorem herm_one_eq (x y : Fin n → E) :
    herm 1 x y = cc (∑ j, IsCMField.complexConj E (x j) * y j) := by
  simp [herm, cc, Matrix.one_apply]

theorem unimod_iff (Λ : Lt E n) : (⟨Λ⟩ : GenLat E n).Unimod ↔
    ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  rw [mem_range_iff, herm_one_eq]
  refine ⟨Base.isIntegral_cc, fun h => ?_⟩
  simpa [cc] using Base.isIntegral_cc h

theorem smul_mem_std {Λ : Lt E n} (hU : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {s : ℕ}
    (h : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n := by
  intro v hv
  rw [← std_eq, mem_std]
  intro i
  have := (hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))
  convert this using 1
  simp [herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]

theorem genLat_vset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Lt E n), (∀ bad M : ℕ, 0 < bad → Odd M → Λ ∈ Vset E n (2 * bad * M) → (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt bad ∧ (⟨Λ⟩ : GenLat E n).TrivAt M ∧ ∃ N, NOK Λ N M) ∧ (∀ M N : ℕ, 0 < M → (⟨Λ⟩ : GenLat E n).Unimod → (⟨Λ⟩ : GenLat E n).TrivAt M → NOK Λ N M → Λ ∈ Vset E n M) ∧ (∀ M M' : ℕ, M ∣ M' → Λ ∈ Vset E n M' → Λ ∈ Vset E n M) ∧ stdLat E n = stdL E n := by
  intro E _ _ _ n Λ
  refine ⟨?_, ?_, ?_, std_eq⟩
  · rintro bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩
    have t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m := fun m hm =>
      ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩
    refine ⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right,
      t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩
    · exact (Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM
    · rw [span_smul_le]
      intro v hv
      refine ⟨?_, natCast_smul_mem _ hv⟩
      rw [std_eq] at hv
      rw [mul_comm, Nat.cast_mul, mul_smul]
      exact natCast_smul_mem M (h2 v hv)
  · rintro M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩
    rw [unimod_iff] at hU
    rw [std_eq, span_smul_le] at h1 h2 h3
    have h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := fun v hv => (h3 v hv).1
    have h5 := smul_mem_std hU h4
    refine ⟨fg_of_smul_le hN.pos h5, hU, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      exact ⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩
    · exact ⟨k, hk0, hk, h1, h2⟩
  · rintro M M' hM ⟨a, b, s, hs, hc, h⟩
    exact ⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩

end GlobalTheory.Dict.GenLatCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem form_eq_zero_of_im {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → V → ℂ)
    (h1 : ∀ w, IsLinearMap ℂ (fun z => f z w)) (h2 : ∀ z, IsLinearMap ℝ (f z)) (S : Set V)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ u ∈ S, ∀ v ∈ S, (f u v).im = 0) (z w : V) : f z w = 0 := by
  have key : ∀ z w, (f z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem u hu =>
      induction hw using Submodule.span_induction with
      | mem v hv => exact h u hu v hv
      | zero => rw [(h2 u).map_zero, zero_im]
      | add a b _ _ ha hb => rw [(h2 u).map_add (f := _), add_im, ha, hb, add_zero]
      | smul t a _ ha => rw [(h2 u).map_smul, smul_im, ha, smul_zero]
    | zero => rw [(h1 w).map_zero, zero_im]
    | add a b _ _ ha hb => rw [(h1 w).map_add (f := _), add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [← Complex.coe_smul, (h1 w).map_smul, smul_eq_mul, im_ofReal_mul, ha, mul_zero]
  have h3 := key (I • z) w
  rw [(h1 w).map_smul, smul_eq_mul, I_mul_im] at h3
  exact Complex.ext h3 (key z w)

theorem hermForm_eq_of_im {g : ℕ} (M M' : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ u ∈ S, ∀ v ∈ S, (hermForm M (a * u) v).im = (hermForm M' u (b * v)).im) (z w : Fin g → ℂ) :
    hermForm M (a * z) w = hermForm M' z (b * w) := by
  refine sub_eq_zero.1 (form_eq_zero_of_im (fun z w => hermForm M (a * z) w - hermForm M' z (b * w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) S hS
    (fun u hu v hv => by rw [sub_im, h u hu v hv, sub_self]) z w)
  · simp only [hermForm, mul_add, add_dotProduct]; ring
  · simp only [hermForm, mul_smul_comm, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hermForm, mul_add, star_add, mulVec_add, dotProduct_add]; ring
  · simp only [hermForm, mul_smul_comm, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_eq_hermForm (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hx X bas idx x z w = hermForm (ThFr.Hm X bas idx x) z w := (hermForm_Hm bas idx x z w).symm

theorem span_range_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range (pv X idx x)) = ⊤ := by
  have col (s : Fin g → Fin g ⊕ Fin g) (t : Fin g → ℝ) :
      perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) ∈ Submodule.span ℝ (Set.range (pv X idx x)) := by
    have : perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) =
        ∑ k, t k • pv X idx x (bas (Pi.single (s k) 1)) := by
      funext i
      simp [mulVec, dotProduct, pv, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine eq_top_iff.2 fun z _ => ?_
  have hu := isUnit_det_perMat idx hs hx
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  set τ := tauMat X bas idx x with hτ
  set y := hMat X bas idx x *ᵥ z with hy
  obtain ⟨t, ht⟩ : ∃ t : Fin g → ℝ, τ.map Complex.im *ᵥ t = fun k => (y k).im :=
    ⟨(τ.map Complex.im)⁻¹ *ᵥ _, by rw [mulVec_mulVec, mul_nonsing_inv _ hY, one_mulVec]⟩
  have h1 : y = (fun k => (((y - τ *ᵥ fun k => (t k : ℂ)) k).re : ℂ)) + τ *ᵥ fun k => (t k : ℂ) := by
    funext k
    apply Complex.ext
    · simp
    · have := congrFun ht k
      simp only [mulVec, dotProduct, map_apply] at this
      simp [mulVec, dotProduct, this]
  have hAB : perMat X bas idx Sum.inl x * τ = perMat X bas idx Sum.inr x :=
    mul_nonsing_inv_cancel_left _ _ hu
  have h2 : z = perMat X bas idx Sum.inl x *ᵥ y := by
    rw [hy, mulVec_mulVec, hMat, mul_nonsing_inv _ hu, one_mulVec]
  rw [h2, h1, mulVec_add, mulVec_mulVec, hAB]
  exact add_mem (col _ _) (col _ _)

theorem span_image_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L : Lt E r)
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ := by
  rw [eq_top_iff, ← span_range_pv idx hs hx, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem L hL v
  have : pv X idx x v = (k : ℝ)⁻¹ • pv X idx x (k • v) := by
    funext i
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [pv, pv, per_zsmul]
    simp only [Function.comp_apply, Pi.smul_apply, zsmul_eq_mul, real_smul, ofReal_inv, Pi.mul_apply, Pi.intCast_apply,
      ofReal_intCast]
    rw [inv_mul_cancel_left₀ hk']
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hv, rfl⟩)

theorem pv_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) :
    pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
  funext fun _ => per_smul X x a v _

theorem EF_smul_left (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) := by
  have h (b : E) : IsCMField.complexConj E (IsCMField.complexConj E a * b) = a * IsCMField.complexConj E b := by
    rw [map_mul, IsCMField.complexConj_apply_apply]
  simp only [EF_def, herm, cc, Pi.smul_apply, smul_eq_mul, h]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hx_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  intro E _ _ _ r X g bas idx n hs _ x hx
  have him {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v) :
      (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    im_hermForm_Hm idx hs hx u v
  simp only [hx_eq_hermForm]
  refine ⟨fun z w => ?_, fun z hz => hermForm_Hm_pos idx hs hx hz, him hx, fun a z w => ?_,
    pv_smul idx x, fun u v h => ?_, fun L hL => ⟨span_image_pv idx hs hx L hL, fun M _ h z w => ?_⟩,
    fun ga hga => ⟨hga.lact_mem hx, fun v => ?_, fun h τ i => ?_, fun z w => ?_⟩⟩
  · have hH := Hm_isHermitian idx hs hx
    rw [hermForm, hermForm, ← RCLike.star_def, ← star_dotProduct_star, star_mulVec, star_star, hH.eq,
      dotProduct_mulVec]
  · refine hermForm_eq_of_im _ _ (fun j => rowType X (idx j) a) (fun j => rowType X (idx j) (cc a)) _
      (span_range_pv idx hs hx) ?_ z w
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have h1 := him hx (a • u) v
    have h2 := him hx u (cc a • v)
    rw [pv_smul] at h1 h2
    rw [EF_smul_left] at h1
    exact h1.trans h2.symm
  · obtain ⟨m, rfl⟩ := vecQ_surjective X bas u
    obtain ⟨m', rfl⟩ := vecQ_surjective X bas v
    have h' (t) : EF X (vecQ X bas m) (vecQ X bas t) = EF X (vecQ X bas m') (vecQ X bas t) := by
      have := (him hx (vecQ X bas m) (vecQ X bas t)).symm.trans (h ▸ him hx (vecQ X bas m') (vecQ X bas t))
      exact_mod_cast this
    simp only [EF_vecQ hs] at h'
    congr 1
    funext j
    rcases j with j | j
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)
  · have := hermForm_eq_of_im M (ThFr.Hm X bas idx x) 1 1 _ (span_image_pv idx hs hx L hL) (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [_root_.one_mul, _root_.one_mul, h u hu v hv, him hx]) z w
    rwa [_root_.one_mul, _root_.one_mul] at this
  · rw [pv, per_lact x hga, pv]
  · have e1 : mat (lact ga x) τ = (ga : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have e2 : FD.gram τ.1 X.Gm (mat (lact ga x) τ) = FD.gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hga]
    have h' := h τ i
    unfold dmin at h' ⊢
    rwa [e2]
  · have := hermForm_eq_of_im (ThFr.Hm X bas idx (lact ga x)) (ThFr.Hm X bas idx x) 1 1 _
      (span_range_pv idx hs hx) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      have h1 := him (hga.lact_mem hx) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v)
      rw [pv, pv, per_lact x hga, per_lact x hga, EF_def, hga, ← EF_def] at h1
      rw [_root_.one_mul, _root_.one_mul, him hx]
      exact h1) z w
    rwa [_root_.one_mul, _root_.one_mul] at this

end GlobalTheory.Dict
end

