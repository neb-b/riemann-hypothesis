module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExt

open NumberField IsDedekindDomain GlobalTheory.ChowHt GlobalTheory.Adelic

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def locDeg (K : Type) [Field K] [NumberField K] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)

theorem mk_algebraMap (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    FinitePlace.mk w (algebraMap K L x) = FinitePlace.mk (w.under (𝓞 K)) x ^ locDeg K w := by
  set v := w.under (𝓞 K) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos _ _
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos _ _
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, locDeg, zero_pow (Nat.mul_pos he hf).ne']
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  have h0 : v.valuation K x ≠ 0 := (v.valuation K).ne_zero_iff.2 hx
  rw [FinitePlace.mk_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding', FinitePlace.norm_embedding',
    ← HeightOneSpectrum.valuation_liesOver L v w x, map_pow, WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZeroMulInt.toNNReal_neg_apply _ h0, hn, locDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem finite_fiber (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have h : (v.asIdeal.primesOver (𝓞 L)).Finite := Set.toFinite _
  refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩

theorem sum_locDeg (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w ∈ (finite_fiber (L := L) v).toFinset, locDeg K w = Module.finrank K L := by
  classical
  have hsumN : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [← hsumN]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime,
    ⟨(congrArg HeightOneSpectrum.asIdeal (((finite_fiber (L := L) v).mem_toFinset).1 hw)).symm⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) fun _ _ => rfl
  refine ⟨⟨q.1, q.2.1, fun h0 => v.ne_bot ?_⟩, (Set.Finite.mem_toFinset _).2 (HeightOneSpectrum.ext q.2.2.over.symm),
    rfl⟩
  have h1 : v.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 L)) := q.2.2.over
  rw [h1, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem finsum_locDeg_mul (g : HeightOneSpectrum (𝓞 K) → ℝ) (hg : (Function.support g).Finite) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L), (locDeg K w : ℝ) * g (w.under (𝓞 K)) = Module.finrank K L * ∑ᶠ v, g v := by
  classical
  have hS : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ Function.support g}.Finite :=
    (hg.biUnion fun v _ => finite_fiber (L := L) v).subset fun w hw => Set.mem_biUnion hw rfl
  rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun w hw => by
      simpa using right_ne_zero_of_mul hw,
    finsum_eq_sum g hg, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := hg.toFinset) (g := fun w => w.under (𝓞 K)) fun w hw => by simpa using hw]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← sum_locDeg v, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun w hw => by rw [(Set.Finite.mem_toFinset _).1 hw]
  ext w
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩

theorem sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = Module.finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  have hfib : ∀ τ : K →+* ℂ, (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ).card =
      Module.finrank K L := by
    intro τ
    let _ : Algebra K ℂ := τ.toAlgebra
    let e : {σ : L →+* ℂ // σ.comp (algebraMap K L) = τ} ≃ (L →ₐ[K] ℂ) :=
      { toFun := fun σ => ⟨σ.1, fun a => congrFun (congrArg DFunLike.coe σ.2) a⟩
        invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
        left_inv := fun σ => rfl
        right_inv := fun φ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, AlgHom.card]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp (algebraMap K L))
    (fun σ => f (σ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, hfib τ,
    nsmul_eq_mul]

end Places

theorem iSup_pow {ι : Type} [Finite ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) :
    ⨆ i, a i ^ m = (⨆ i, a i) ^ m := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  refine le_antisymm (ciSup_le fun j => pow_le_pow_left₀ (ha j) (le_ciSup (Set.finite_range _).bddAbove j) m) ?_
  rw [← hi]
  exact le_ciSup (f := fun i => a i ^ m) (Set.finite_range _).bddAbove i

theorem finite_support_log_iSup {K ι : Type} [Field K] [NumberField K] [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (⨆ k, v (z k))).Finite := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  refine (Set.finite_iUnion fun k : {k // z k ≠ 0} => FinitePlace.hasFiniteMulSupport k.2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  refine hv ?_
  have : ⨆ k, v (z k) = 1 := le_antisymm (ciSup_le fun k => by
      rcases eq_or_ne (z k) 0 with h0 | h0
      · rw [h0, map_zero]; exact zero_le_one
      · exact (h ⟨k, h0⟩).le)
    ((h ⟨k₀, hk₀⟩).ge.trans (le_ciSup (f := fun k => v (z k)) (Set.finite_range _).bddAbove k₀))
  simp only [this, Real.log_one]

theorem finsum_log_iSup_algebraMap {K L ι : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ k, w (algebraMap K L (z k))) =
      Module.finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (z k)) := by
  obtain ⟨k₀, -⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := L)).symm,
    ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm,
    ← finsum_locDeg_mul _ ((finite_support_log_iSup hz).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn)]
  refine finsum_congr fun w => ?_
  rw [← Real.log_pow, ← iSup_pow _ fun _ => apply_nonneg _ _]
  exact congrArg Real.log (iSup_congr fun k => mk_algebraMap w (z k))

theorem pointHeight_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K),
      y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw _ K' _ _ _ _ _ y hy
  classical
  have hz : (fun k => ∑ j, algebraMap F K (w j k) * y j) ≠ 0 := fun h => by
    have hp := finSize_pos hw (algebraMap F K) AbsoluteValue.trivial hy
    have h' : ∀ k, ∑ j, algebraMap F K (w j k) * y j = 0 := congrFun h
    simp [finSize, h'] at hp
  have h₁ := finsum_log_iSup_algebraMap (L := K') hz
  have h₂ := sum_comp_algebraMap (L := K')
    fun τ : K →+* ℂ => Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, RingHom.comp_apply] at h₂
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < Module.finrank K K' := by exact_mod_cast Module.finrank_pos
  rw [pointHeight_eq, pointHeight_eq, h₂, ← Module.finrank_mul_finrank ℚ K K']
  simp only [finSize, ← FinitePlace.coe_apply]
  rw [h₁]
  push_cast
  field_simp

end GlobalTheory.Adelic.HeightExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRoots
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

open Polynomial

theorem not_dvd_den_of_padic_norm_le_one (p : ℕ) [Fact p.Prime] (c : ℚ)
    (hc : ‖(c : ℚ_[p])‖ ≤ 1) : ¬ p ∣ c.den := by
  intro hd
  have hden : ‖((c.den : ℤ) : ℚ_[p])‖ < 1 :=
    Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have hnum : ‖((c.num : ℤ) : ℚ_[p])‖ < 1 := by
    have h1 : ((c.num : ℤ) : ℚ_[p]) = (c : ℚ_[p]) * ((c.den : ℤ) : ℚ_[p]) := by
      have : (c.num : ℚ) = c * (c.den : ℤ) := by
        rw [Int.cast_natCast, Rat.mul_den_eq_num]
      exact_mod_cast congrArg (fun x : ℚ => (x : ℚ_[p])) this
    rw [h1, norm_mul]
    calc ‖(c : ℚ_[p])‖ * ‖((c.den : ℤ) : ℚ_[p])‖ ≤ 1 * ‖((c.den : ℤ) : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have hpn : (p : ℤ) ∣ c.num := Padic.norm_intCast_lt_one_iff.1 hnum
  have hcop := c.reduced
  have h2 : p ∣ c.num.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs]; exact (dvd_abs _ _).2 hpn
  have h3 := Nat.dvd_gcd h2 hd
  rw [hcop.gcd_eq_one] at h3
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 h3)

theorem padic_denom_coeff_of_roots_bounded :
    ∀ (p : ℕ) [Fact p.Prime] (q : Polynomial ℚ), q.Monic → ∀ k : ℕ,
      (∀ μ : PadicAlgCl p, (q.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      ∀ i, ∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ (k * q.natDegree) * m : ℕ) : ℚ) * q.coeff i = a := by
  intro p _ q hq k hroot i
  have hp : p.Prime := Fact.out
  by_cases hi : q.natDegree < i
  · refine ⟨1, Nat.coprime_one_left _, 0, ?_⟩
    rw [coeff_eq_zero_of_natDegree_lt hi]; simp
  push_neg at hi
  have hQm : (q.map (algebraMap ℚ (PadicAlgCl p))).Monic := hq.map _
  have hQd : (q.map (algebraMap ℚ (PadicAlgCl p))).natDegree = q.natDegree := natDegree_map _
  have hB := GlobalTheory.norm_coeff_natDegree_sub_le_pow_of_roots_le (PadicAlgCl p) _ hQm ((p : ℝ) ^ k)
    hroot (q.natDegree - i) (by omega)
  rw [hQd, Nat.sub_sub_self hi, coeff_map] at hB
  have hn : ‖((q.coeff i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (k * q.natDegree) := by
    have e : algebraMap ℚ (PadicAlgCl p) (q.coeff i) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((q.coeff i : ℚ) : ℚ_[p]) := by
      rw [eq_ratCast, map_ratCast]
    rw [e, PadicAlgCl.norm_extends] at hB
    refine hB.trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le)
      (Nat.mul_le_mul_left k (Nat.sub_le _ _))
  set c : ℚ := ((p ^ (k * q.natDegree) : ℕ) : ℚ) * q.coeff i with hcdef
  have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (k * q.natDegree) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    rw [hcdef]
    push_cast
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    calc ((p : ℝ) ^ (k * q.natDegree))⁻¹ * ‖((q.coeff i : ℚ) : ℚ_[p])‖
        ≤ ((p : ℝ) ^ (k * q.natDegree))⁻¹ * (p : ℝ) ^ (k * q.natDegree) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hp0.le)
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  refine ⟨c.den, ?_, c.num, ?_⟩
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_den_of_padic_norm_le_one p c hc))
  · rw [← Rat.den_mul_eq_num c, hcdef]
    push_cast
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelUniformisedGeometricFree
section
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem mk_out_of_le {T P L : Subgroup H} (hTP : T ≤ P) (x : H) :
    DoubleCoset.mk P L (Quotient.out (DoubleCoset.mk T L x)) = DoubleCoset.mk P L x := by
  obtain ⟨t, ht, l, hl, h⟩ := DoubleCoset.mk_out_eq_mul T L x
  rw [h, DoubleCoset.eq]
  exact ⟨t⁻¹, P.inv_mem (hTP ht), l⁻¹, L.inv_mem hl, by group⟩

theorem locPart_inf_conj {T P L : Subgroup H} (hTP : T ≤ P) {p : H} (hp : p ∈ P) (y : H) :
    GlobalTheory.LKLoc.locPart T (P ⊓ L.map (MulAut.conj y).toMonoidHom) p = GlobalTheory.LKLoc.locPart T L (p * y) := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, ⟨_, l, hl, rfl⟩, rfl⟩
    exact ⟨hg, l, hl, by group⟩
  · rintro ⟨hg, l, hl, rfl⟩
    refine ⟨hg, y * l * y⁻¹, ⟨?_, l, hl, rfl⟩, by group⟩
    have e : y * l * y⁻¹ = p⁻¹ * (p * y * l * (p * y)⁻¹) * p := by group
    rw [e]
    exact P.mul_mem (P.mul_mem (P.inv_mem hp) (hTP hg)) hp

theorem dsum_eq_zero_of_par (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ) (hTP : T ≤ P)
    (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x)
    (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x)
    (hy : ∀ y : H, dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U
      (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) :
    dsum T L U Ψ = 0 := by
  set F : DoubleCoset.Quotient (T : Set H) (L : Set H) → ℂ := fun q => wt T L U Ψ (Quotient.out q) with hF
  set π : DoubleCoset.Quotient (T : Set H) (L : Set H) → DoubleCoset.Quotient (P : Set H) (L : Set H) :=
    fun q => DoubleCoset.mk P L (Quotient.out q) with hπ
  have hdef : dsum T L U Ψ = ∑ᶠ q, F q := rfl
  rw [hdef]
  by_cases hfin : (Function.support F).Finite
  swap
  · exact finsum_of_infinite_support hfin
  rw [finsum_eq_sum F hfin, ← Finset.sum_fiberwise_of_maps_to (g := π)
    (t := hfin.toFinset.image π) (fun _ h => Finset.mem_image_of_mem _ h)]
  refine Finset.sum_eq_zero fun r _ => ?_
  obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk P L y = r := ⟨Quotient.out r, DoubleCoset.out_eq' _⟩
  set Ly := P ⊓ L.map (MulAut.conj y).toMonoidHom with hLy
  have hLyP : ∀ k ∈ Ly, k ∈ P := fun k hk => (Subgroup.mem_inf.1 hk).1
  set G : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → ℂ :=
    fun q => wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) with hG
  set φ : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → DoubleCoset.Quotient (T : Set H) (L : Set H) :=
    fun q => DoubleCoset.mk T L (Quotient.out q * y) with hφ
  set A : Set (DoubleCoset.Quotient (T : Set H) (Ly : Set H)) := {q | Quotient.out q ∈ P} with hA
  have h0 : ∑ᶠ q, G q = 0 := hy y
  have hsuppG : Function.support G ⊆ A := by
    intro q hq
    by_contra hn
    have hn' : Quotient.out q ∉ P := hn
    apply hq
    show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) = 0
    simp only [wt, if_neg hn', mul_zero]
  have hGF : ∀ q ∈ A, G q = F (φ q) := by
    intro q hq
    have hq' : Quotient.out q ∈ P := hq
    show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) =
      wt T L U Ψ (Quotient.out (DoubleCoset.mk T L (Quotient.out q * y)))
    rw [wt_out U hT hΨl hΨr]
    simp only [wt, if_pos hq', hLy, locPart_inf_conj hTP hq' y]
  have hinj : Set.InjOn φ A := by
    intro q₁ h₁ q₂ h₂ h
    obtain ⟨t, ht, l, hl, e⟩ := (@DoubleCoset.eq _ _ T L _ _).1 h
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂, DoubleCoset.eq]
    refine ⟨t, ht, y * l * y⁻¹, Subgroup.mem_inf.2 ⟨?_, l, hl, rfl⟩, ?_⟩
    · have e' : y * l * y⁻¹ = (t * Quotient.out q₁)⁻¹ * Quotient.out q₂ := by
        rw [show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]
        group
      rw [e']
      exact P.mul_mem (P.inv_mem (P.mul_mem (hTP ht) h₁)) h₂
    · rw [show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]
      group
  have himg : φ '' A = {q | π q = DoubleCoset.mk P L y} := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q', hq', rfl⟩
      simp only [hπ, hφ, mk_out_of_le hTP, DoubleCoset.eq]
      exact ⟨(Quotient.out q')⁻¹, P.inv_mem hq', 1, L.one_mem, by group⟩
    · intro hq
      obtain ⟨p, hp, l, hl, e⟩ := (@DoubleCoset.eq _ _ P L _ _).1 hq
      obtain ⟨t, ht, k, hk, ek⟩ := DoubleCoset.mk_out_eq_mul T Ly p⁻¹
      refine ⟨DoubleCoset.mk T Ly p⁻¹, ?_, ?_⟩
      · show Quotient.out (DoubleCoset.mk T Ly p⁻¹) ∈ P
        rw [ek]
        exact P.mul_mem (P.mul_mem (hTP ht) (P.inv_mem hp)) (hLyP k hk)
      · obtain ⟨_, l', hl', rfl⟩ := Subgroup.mem_inf.1 hk
        simp only [hφ]
        rw [ek, ← DoubleCoset.out_eq' q, DoubleCoset.eq]
        refine ⟨t⁻¹, T.inv_mem ht, l'⁻¹ * l⁻¹, L.mul_mem (L.inv_mem hl') (L.inv_mem hl), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [e]
        group
  have hGA : ∑ᶠ q, G q = ∑ᶠ q ∈ A, G q := by
    rw [← finsum_mem_inter_support, Set.inter_eq_right.2 hsuppG, finsum_mem_support]
  rw [← h0, hGA, finsum_mem_congr rfl hGF,
    ← finsum_mem_image hinj, himg]
  refine (finsum_mem_eq_sum_of_inter_support_eq F ?_).symm
  ext q
  simp [Finset.mem_filter, Set.Finite.mem_toFinset]
  tauto

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLifts

theorem prime_eq_of_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ P.asIdeal) (h2 : (q : 𝓞 K) ∈ P.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact P.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem places_apart {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (h : L.Is μ0) (t : T) :
    (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q t → ¬ Lev.IsConjPl PP PP') ∧ Disjoint L.Pg (L.Q t) := by
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hP k hk
    obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h.Q_pl t PP hP
    have h1 : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← hc]
      rw [← Ideal.absNorm_eq_natCard]
      exact Ideal.absNorm_mem PP.asIdeal
    exact hne k (prime_eq_of_mem PP hq (D.host.g_prime k) h1 hk)
  refine ⟨fun PP hP PP' hP' hc => ?_, Finset.disjoint_left.2 fun PP hP hP' => ?_⟩
  · rcases hP' with hP' | hP'
    · exact GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg h.Pg PP hP PP' hP' hc
    · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
      obtain ⟨c, hc', e⟩ := hc _ (L.C.P.overP hk)
      have e' : c = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
      exact hQ PP' hP' k (e' ▸ hc')
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    exact hQ PP hP' k (L.C.P.overP hk)

theorem lifts_exist : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m), (∀ (t : T) (g0 : G0 R.Pg D.R.r), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) ∧ ∀ g0 : G0 R.Pg D.R.r, ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i
  obtain ⟨c, hc⟩ := h.βV i
  obtain ⟨c', hc'⟩ := h.βW i
  refine ⟨fun t => ?_, ?_⟩
  · exact GlobalTheory.ParahoricLift.liftsExist (Vc D i) (R.βV i) (R.datVt i t) _ _ hc (places_apart _ h t).1 (places_apart _ h t).2
  · refine GlobalTheory.ParahoricLift.liftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) _ _ hc' (fun PP hP PP' hP' => ?_)
      (Finset.disjoint_empty_right _)
    exact (places_apart _ h A.μ0).1 PP hP PP' (hP'.imp id fun h0 => absurd h0 (Finset.notMem_empty _))

end GlobalTheory.StepLifts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCard
section
set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem ker_isMaximal_card {E k : Type} [Field E] [NumberField E] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : 𝓞 E →+* k) :
    (RingHom.ker f).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ RingHom.ker f) = p ^ h := by
  have hp : p.Prime := Fact.out
  have hmem : ((p : ℕ) : 𝓞 E) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker f ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hp.ne_zero (Nat.cast_eq_zero.1 hmem)
  have hmax : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hne
  refine ⟨hmax, ?_⟩
  haveI : Finite (𝓞 E ⧸ RingHom.ker f) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI : Fintype (𝓞 E ⧸ RingHom.ker f) := Fintype.ofFinite _
  letI : Field (𝓞 E ⧸ RingHom.ker f) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E ⧸ RingHom.ker f) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker f)), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ RingHom.ker f) p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem primeBelow_isMaximal_card (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (τ : E →+* ℂ) :
    (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  haveI := charP_residueField_of_irreducible X
  rw [primeBelow_eq_ker]
  exact ker_isMaximal_card p (red io X τ)

end GlobalTheory.PrimePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceKq
section
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKMid

theorem t2Space_kq {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    T2Space (KQ p K r) := by
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℚ_[p] (KQ p K r)
  let φ : KQ p K r →ₗ[ℚ_[p]] (Module.Free.ChooseBasisIndex ℚ_[p] (KQ p K r) → ℚ_[p]) :=
    Finsupp.lcoeFun ∘ₗ b.repr.toLinearMap
  have hinj : Function.Injective φ := by
    intro x y h
    apply b.repr.injective
    exact DFunLike.coe_injective h
  exact T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)

end GlobalTheory.LKMid
end
end

