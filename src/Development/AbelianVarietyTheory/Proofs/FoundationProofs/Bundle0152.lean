module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishes
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeU
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RightRepU

lemma adj_repL (L l : ℕ) (j : Fin l) :
    (repL L l (some j)).adjugate = !![(1:ℤ), 0; -((L:ℤ) * ((j:ℕ):ℤ)), (l:ℤ)] := by
  simp [repL, Matrix.adjugate_fin_two_of]

lemma dvd_10 {L : ℕ} (γ : Gamma0 L) : (L:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)

lemma not_dvd_00 {L l : ℕ} (hl : l.Prime) (hlL : l ∣ L) (γ : Gamma0 L) :
    ¬ (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 0 0 := by
  intro h
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc' : (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hlL) (dvd_10 γ)
  have h1 : (l:ℤ) ∣ 1 := by
    rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hc' _)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hl.one_lt.ne' (by exact_mod_cast this)

end GlobalTheory.EisM.RightRepU

namespace GlobalTheory.EisM.RightRepU

theorem rrep (L l : ℕ) (hl : l.Prime) (hlL : l ∣ L) (hL : 0 < L) :
    RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  haveI := Fact.mk hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hpr : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hlpos : (0:ℤ) < l := by exact_mod_cast hl.pos
  simp only [RRep, adj_repL]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, γ⟩ -
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul]
      rw [hdet, Matrix.det_fin_two_of]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_of_dvd_right (dvd_10 γ) _)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using not_dvd_00 hl hlL γ
  · rintro ⟨j, γ⟩ - ⟨j', γ'⟩ - h
    simp only at h
    have e := fun r s => congrArg (fun M : M2 => M r s) h
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    obtain ⟨c1, hc1⟩ := dvd_10 γ
    obtain ⟨c1', hc1'⟩ := dvd_10 γ'
    have hLz : (0:ℤ) < L := by exact_mod_cast hL
    have hk : (L:ℤ) * ((((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0) = (L:ℤ) * ((l:ℤ) * (c1' - c1)) := by
      rw [hc1, hc1', ← h00] at h10
      linear_combination h10
    have hk2 := mul_left_cancel₀ hLz.ne' hk
    have hdv : (l:ℤ) ∣ (((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0 := ⟨_, hk2⟩
    have hjj := (hpr.dvd_or_dvd hdv).resolve_right (not_dvd_00 hl hlL γ)
    have hj0 : ((j':ℕ):ℤ) - (j:ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hjj
      have := j.isLt; have := j'.isLt
      rw [abs_lt]; constructor <;> omega
    have hjeq : j = j' := Fin.ext (by omega)
    subst hjeq
    have h10' : ((γ : SL(2,ℤ)) : M2) 1 0 = ((γ' : SL(2,ℤ)) : M2) 1 0 := by
      rw [← h00] at h10
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h10)
    have h11' : ((γ : SL(2,ℤ)) : M2) 1 1 = ((γ' : SL(2,ℤ)) : M2) 1 1 := by
      rw [← h01] at h11
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h11)
    refine Prod.ext rfl (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ (fun r s => ?_)))
    fin_cases r <;> fin_cases s
    · exact h00
    · exact h01
    · exact h10'
    · exact h11'
  · rintro δ ⟨hdet, hc, ha⟩
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨c1, hc1⟩ := hc
    obtain ⟨L1, hL1⟩ := hlL
    have hLl : (L:ℤ) = l * L1 := by rw [hL1]; push_cast; ring
    have hd : (l:ℤ) ∣ δ 1 1 := by
      have : (l:ℤ) ∣ δ 0 0 * δ 1 1 :=
        ⟨1 + L1 * c1 * δ 0 1, by linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * c1 * hLl⟩
      exact (hpr.dvd_or_dvd this).resolve_left ha
    obtain ⟨d1, hd1⟩ := hd
    have ha0 : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨x, hx⟩ : ∃ x : ZMod l, x = -(c1 : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ := ⟨_, rfl⟩
    let j : Fin l := ⟨x.val, ZMod.val_lt x⟩
    have hj : (l:ℤ) ∣ c1 + ((j:ℕ):ℤ) * δ 0 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [j, ZMod.natCast_val, ZMod.cast_id', id]
      rw [hx, mul_assoc, inv_mul_cancel₀ ha0]; ring
    obtain ⟨m, hm⟩ := hj
    let M : M2 := !![δ 0 0, δ 0 1; (L:ℤ) * m, d1 + L1 * ((j:ℕ):ℤ) * δ 0 1]
    have hM : M.det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hlpos.ne'
      linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * L * hm - ((j:ℕ):ℤ) * δ 0 0 * δ 0 1 * hLl - δ 0 0 * hd1
    let g : SL(2,ℤ) := ⟨M, hM⟩
    have hmem : g ∈ Gamma0 L := by
      rw [Gamma0_mem]; simp [g, M]
    refine ⟨(j, ⟨g, hmem⟩), trivial, ?_⟩
    ext r s
    fin_cases r <;> fin_cases s
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -(L:ℤ) * hm - hc1
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -hd1 - ((j:ℕ):ℤ) * δ 0 1 * hLl

end GlobalTheory.EisM.RightRepU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivial
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3.LamInj

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] [CharZero E] :
    Function.Injective (algebraMap ℤ_[l] E) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have e := PadicInt.unitCoeff_spec h0
  rw [e, map_mul, map_pow, map_natCast] at hx
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[l] E)).ne_zero h
  · exact pow_ne_zero _ hl h

theorem gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem gamma_le_gam (N l : ℕ) : CongruenceSubgroup.Gamma (N * l) ≤ Gam N l := by
  intro δ hδ
  have h1 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro l rfl : N ∣ N * l) hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro_left N rfl : l ∣ N * l) hδ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩

theorem fst_eq_zero_of_triv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E →
    ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) →
    y = 0 := by
  intro Ω _ _ _ ε X _ _ N l w _ hN E _ _ hE y G hp hG
  exact _root_.GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv Ω ε X l E (algebraMap_injective l E) w (Gam N l) (N * l)
    (Nat.mul_pos hN (Fact.out : l.Prime).pos) (gamma_le_gam N l) (y, G) hp hG

end GlobalTheory.KZ.H3.LamInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerIntegerDecompositionByTau
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow_eq_one' (T : Tower p Ω) (m : ℕ) : T.ζ (m + 1) ^ p ^ m = T.ζ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, T.ζpow, ih]

theorem exists_pow_eq_zeta_one (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ e : ℕ, (T.ζ N ^ j) ^ e = T.ζ 1 := by
  have hN : N ≠ 0 := by rintro rfl; simp at hjN; omega
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hglt : Nat.gcd j (p ^ (M + 1)) < p ^ (M + 1) :=
    lt_of_le_of_lt (Nat.le_of_dvd hj0 (Nat.gcd_dvd_left _ _)) hjN
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hglt
  obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_right j (p ^ (M + 1)))
  have haM : a ≤ M := by
    by_contra h
    have : a = M + 1 := by omega
    subst this
    have h2 : p ^ (M + 1) ∣ j := hga ▸ Nat.gcd_dvd_left _ _
    exact absurd (Nat.le_of_dvd hj0 h2) (by omega)
  obtain ⟨t, ht⟩ : Nat.gcd j (p ^ (M + 1)) ∣ p ^ M := hga ▸ pow_dvd_pow p haM
  refine ⟨m * t, ?_⟩
  rw [← pow_mul, ← zeta_pow_eq_one' T M, Basic.zeta_pow_eq_iff]
  have h1 : j * m ≡ Nat.gcd j (p ^ (M + 1)) [MOD p ^ (M + 1)] := by
    unfold Nat.ModEq; rw [hm, Nat.mod_eq_of_lt hglt]
  have h2 := h1.mul_right t
  rw [← ht] at h2
  rw [← mul_assoc]; exact h2

theorem isInt_zeta (T : Tower p Ω) (N : ℕ) : IsInt (p := p) (T.ζ N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [(T.prim N).pow_eq_one]; exact isIntegral_one

theorem ggeo_zeta (T : Tower p Ω) (N : ℕ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) : g (T.ζ N) = T.ζ N := by
  apply hg
  refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos N) 1, ?_⟩
  simp [(T.prim N).pow_eq_one]

end GlobalTheory.K5.Decomp

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isInt_qq (T : Tower p Ω) (N : ℕ) : IsInt (p := p) (T.qq N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [Basic.qq_pow]; exact isIntegral_algebraMap

theorem exists_mult (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ s : Ω, IsInt (p := p) s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧ s * (T.ζ N ^ j - 1) = T.ζ 1 - 1 := by
  obtain ⟨e, he⟩ := exists_pow_eq_zeta_one T N j hj0 hjN
  refine ⟨∑ i ∈ Finset.range e, (T.ζ N ^ j) ^ i, ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun i _ => ((isInt_zeta T N).pow j).pow i
  · intro g hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, ggeo_zeta T N hg]
  · rw [geom_sum_mul, he]

end GlobalTheory.K5.Decomp


open GlobalTheory.K5.Decomp in
theorem GlobalTheory.K5.Decomp.decomp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt (p := p) y → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧ IsInt (p := p) w ∧
    (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq N y hy hfix
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer p Ω hΩ T N y hfix
  have hci := GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion p Ω hΩ T N c hc hy
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hs : ∀ j, ∃ s : Ω, IsInt (p := p) s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧
      (0 < j → j < p ^ N → s * (T.ζ N ^ j - 1) = T.ζ 1 - 1) := by
    intro j
    by_cases h : 0 < j ∧ j < p ^ N
    · obtain ⟨s, h1, h2, h3⟩ := exists_mult T N j h.1 h.2
      exact ⟨s, h1, h2, fun _ _ => h3⟩
    · exact ⟨0, isIntegral_zero, fun g _ => map_zero g, fun a b => absurd ⟨a, b⟩ h⟩
  choose s hsi hsg hse using hs
  refine ⟨c 0, ∑ j ∈ Finset.range (p ^ N), s j * c j * T.qq N ^ j, hci 0 hpos, hc 0, ?_, ?_, ?_⟩
  · refine IsIntegral.sum _ fun j hj => ?_
    exact ((hsi j).mul (hci j (Finset.mem_range.1 hj))).mul ((isInt_qq T N).pow j)
  · intro g hg
    have hg1 := (Subgroup.mem_inf.1 hg).1
    have hg2 : g (T.qq N) = T.qq N := (Subgroup.mem_inf.1 hg).2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, hsg _ g hg1, hc _ g hg1, hg2]
  · obtain ⟨M, hM⟩ : ∃ M, p ^ N = M + 1 := ⟨p ^ N - 1, by omega⟩
    have key : ∀ i < M, s (i + 1) * (T.ζ N ^ (i + 1) - 1) = T.ζ 1 - 1 := fun i hi =>
      hse (i + 1) (Nat.succ_pos i) (by omega)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, hsg _ τ hτ, hc _ τ hτ, hτq N]
    rw [hM, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range M, s (i + 1) * c (i + 1) * (T.ζ N * T.qq N) ^ (i + 1) =
        s (i + 1) * c (i + 1) * T.qq N ^ (i + 1) + (T.ζ 1 - 1) * (c (i + 1) * T.qq N ^ (i + 1)) := by
      intro i hi
      rw [← key i (Finset.mem_range.1 hi)]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFinite
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem func_eq_lam : ∀ (S : Set (ℕ → ℂ)) (B : ℕ) (φ : (ℕ → ℂ) → ℂ), 0 ∈ S → (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ φ (a + b) = φ a + φ b) → (∀ c : ℂ, ∀ a ∈ S, c • a ∈ S ∧ φ (c • a) = c * φ a) → (∀ a ∈ S, (∀ n < B, a n = 0) → a = 0) → ∃ c : ℕ → ℂ, ∀ a ∈ S, φ a = lam B c a := by
  intro S B φ h0 hadd hsmul hdet
  classical
  let W : Submodule ℂ (ℕ → ℂ) :=
    { carrier := S
      add_mem' := fun {a b} ha hb => (hadd a ha b hb).1
      zero_mem' := h0
      smul_mem' := fun c a ha => (hsmul c a ha).1 }
  let φW : W →ₗ[ℂ] ℂ :=
    { toFun := fun a => φ a
      map_add' := fun a b => (hadd a a.2 b b.2).2
      map_smul' := fun c a => (hsmul c a a.2).2 }
  let r : W →ₗ[ℂ] (Fin B → ℂ) :=
    { toFun := fun a i => (a : ℕ → ℂ) i
      map_add' := fun a b => by ext i; rfl
      map_smul' := fun c a => by ext i; rfl }
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    refine hdet a a.2 (fun n hn => ?_)
    have := congrFun ha ⟨n, hn⟩
    simpa [r] using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective r hr
  let ψ : (Fin B → ℂ) →ₗ[ℂ] ℂ := φW.comp g
  refine ⟨fun n => if h : n < B then ψ (Pi.single ⟨n, h⟩ 1) else 0, fun a ha => ?_⟩
  have h1 : φ a = ψ (r ⟨a, ha⟩) := by
    show φW ⟨a, ha⟩ = φW (g (r ⟨a, ha⟩))
    rw [← LinearMap.comp_apply g r, hg, LinearMap.id_apply]
  rw [h1, LinearMap.pi_apply_eq_sum_univ ψ (r ⟨a, ha⟩), EisM.lam,
    Finset.sum_range (fun n => (if h : n < B then ψ (Pi.single ⟨n, h⟩ 1) else 0) * a n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [i.2, dif_pos, Fin.eta, r, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  have hs : (fun j : Fin B => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzFormulaPeriodicWeight
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem lipschitz_periodic : ∀ (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 2 ≤ j → 0 < L → 0 < z.im → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro j L φ z hj hL hz
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have htrm : ∀ w : ℂ, trm (k + 2) 0 w = (w ^ (k + 2))⁻¹ := fun w => by simp [trm]
  set f : ℤ → ℂ := fun d => φ (d : ZMod L) * ((z + d) ^ (k + 2))⁻¹ with hf_def
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖φ x‖ ≤ M := ⟨∑ x, ‖φ x‖, fun x =>
    Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ x)⟩
  have hs0 : ∀ w : ℂ, Summable fun d : ℤ => ((w + d) ^ (k + 2))⁻¹ := fun w => by
    have := EisensteinSeries.linear_right_summable w 1 (k := ((k + 2 : ℕ) : ℤ)) (by push_cast; omega)
    simp only [Int.cast_one, one_mul, zpow_natCast] at this
    exact this
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((hs0 z).norm.mul_left M) fun d => ?_
    simp only [f, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hlim : Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d) atTop (𝓝 (∑' d, f d)) :=
    hfs.hasSum.comp (tendsto_atTop_finset_of_monotone
      (fun a b hab => Finset.Icc_subset_Icc (by omega) (by omega)) fun x => ⟨x.natAbs, Finset.mem_Icc.mpr
        ⟨by rw [Int.natCast_natAbs]; exact neg_abs_le x, by rw [Int.natCast_natAbs]; exact le_abs_self x⟩⟩)
  have hval : ∑' d, f d = (-2 * π * Complex.I / L) ^ (k + 2) / (k + 2 - 1).factorial *
      ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 2 - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
    set C : ℂ := (-2 * π * Complex.I) ^ (k + 2) / (k + 1).factorial with hC
    set w : ℕ → ℂ := fun r => (z + r) / L with hw_def
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hwim : ∀ r : ℕ, 0 < (w r).im := fun r => by
      simp only [w, Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]; positivity
    set q : ℕ → ℂ := fun r => cexp (2 * π * Complex.I * w r) with hq_def
    have hq : ∀ r, ‖q r‖ < 1 := fun r => UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w r, hwim r⟩
    set g : ℕ → ℕ → ℂ := fun r m => ((m + 1 : ℕ) : ℂ) ^ (k + 1) * q r ^ (m + 1) with hg_def
    have hgs : ∀ r, Summable (g r) := fun r => by
      have h0 : Summable (fun n : ℕ => (n : ℂ) ^ (k + 1) * q r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (k + 1) (hq r)
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℂ) ^ (k + 1) * q r ^ n) 1).mpr h0
      refine h1.congr fun m => ?_
      simp only [g, Nat.cast_add, Nat.cast_one]
    have hres : ∀ r : Fin L, HasSum (fun n : ℤ => f (n * L + (r : ℕ)))
        (φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2) * (C * ∑' m, g r m)) := by
      intro r
      have hid := EisensteinSeries.qExpansion_identity_pnat (k := k + 1) (by omega) ⟨w r, hwim r⟩
      rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ (k + 1) *
        cexp (2 * π * Complex.I * ((⟨w r, hwim r⟩ : ℍ) : ℂ)) ^ n)] at hid
      have h1 : HasSum (fun n : ℤ => ((w r + n) ^ (k + 2))⁻¹) (C * ∑' m, g r m) := by
        convert (hs0 (w r)).hasSum using 1
        simp only [one_div] at hid
        rw [hid]
      have h2 := h1.mul_left (φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2))
      refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr h2
      simp only [f]
      have e1 : (((n * L + (r : ℕ) : ℤ)) : ZMod L) = ((r : ℕ) : ZMod L) := by push_cast; simp
      have e2 : z + (((n * L + (r : ℕ) : ℤ)) : ℂ) = L * (w r + n) := by
        simp only [w]; push_cast; field_simp; ring
      rw [e1, e2, mul_pow, mul_inv, inv_pow]; ring
    let e : Fin L × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv L).symm
    have he : ∀ p : Fin L × ℤ, e p = p.2 * L + ((p.1 : ℕ) : ℤ) := fun p => by
      simp [e, Int.divModEquiv_symm_apply]
    have hfe : HasSum (f ∘ e) (∑' d, f d) := by rw [e.hasSum_iff]; exact hfs.hasSum
    have hg2 : HasSum (fun r : Fin L => φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2) * (C * ∑' m, g r m))
        (∑' d, f d) :=
      hfe.prod_fiberwise fun r => by
        convert hres r using 1
        funext n; simp only [Function.comp_apply, he]
    have hsum : ∑ r : Fin L, φ ((r : ℕ) : ZMod L) * ∑' m, g r m = ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 1) *
        hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (f := fun (r : Fin L) m => φ ((r : ℕ) : ZMod L) * g r m)
        (fun r _ => (hgs r).mul_left _)]
      refine tsum_congr fun m => ?_
      rw [Fin.sum_univ_eq_sum_range (fun y => φ (y : ZMod L) * g y m) L]
      simp only [hat, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : q y ^ (m + 1) = cexp (2 * π * Complex.I * (y * (((m + 1 : ℕ) : ℤ) : ℂ)) / L) *
          cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
        rw [hq_def, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        simp only [w]; push_cast; field_simp; ring
      simp only [g, this]; ring
    rw [hg2.unique (hasSum_fintype _), show k + 2 - 1 = k + 1 by omega, ← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hC, div_pow]; ring
  rw [← hval]
  refine hlim.congr fun R => Finset.sum_congr rfl fun d _ => ?_
  simp [f, htrm]

end GlobalTheory.EisM
end
end

