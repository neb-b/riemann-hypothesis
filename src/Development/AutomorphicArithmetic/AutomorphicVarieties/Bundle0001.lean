module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace UpperTheory.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]

def IsConjOm (σ : Ω ≃+* Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (σ x) = starRingEnd ℂ (j x)

include E in
theorem IsConjOm.cyc {σ : Ω ≃+* Ω} (h : IsConjOm σ) : cyclotomicCharacter Ω l σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ ζ hζ.pow_eq_one
  have h1 : σ ζ * ζ = 1 := by
    apply j.injective
    have : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hN0
    rw [map_mul, hj, map_one, Complex.conj_mul', this]
    simp
  rw [hspec, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val,
    Nat.cast_one] at h1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  exact eq_neg_of_add_eq_zero_left h1

variable [IsCMField E]

theorem IsConjOm.isLift {σ : Ω ≃+* Ω} (h : IsConjOm σ) : IsLift (cE E) σ := by
  obtain ⟨j, hj⟩ := h
  intro x
  apply j.injective
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E Ω)) x).symm

omit [IsCMField E] in
include E in
theorem exists_isConjOm : ∃ σ : Ω ≃+* Ω, IsConjOm σ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  let c : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  exact ⟨(c.restrictNormal Ω).toRingEquiv, j.toRingHom, fun x => c.restrictNormal_commutes Ω x⟩

omit [IsCMField E] in
include E in
theorem twScal_conj {σ : Ω ≃+* Ω} (h : IsConjOm σ) (e : ℕ) : twScal l σ (e : ℤ) = (-1) ^ e := by
  rw [twScal, h.cyc (E := E), zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
  simp

private theorem mem_eig (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ) (z : Z1 (qzTw D (e : ℤ))) (s : ℤ_[l]) :
    (Submodule.Quotient.mk z : H1 (qzTw D (e : ℤ))) ∈ (cAct D e).eigenspace ((-1) ^ e * s) ↔
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) - s • z.1 g = qzTw D e g m - m := by
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h.isLift z
  have hs : (-1 : ℤ_[l]) ^ e * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Module.End.mem_eigenspace_iff, cAct, galois_action_cohomology_eq_conj D e h.isLift, e₁, ← Submodule.Quotient.mk_smul]
  refine (mk_eq_mk_iff _ _ _).trans ?_
  have key : ∀ g, z₁.1 g - (((-1 : ℤ_[l]) ^ e * s) • z).1 g =
      (-1 : ℤ_[l]) ^ e • (z.1 (conjGS D h.isLift g) - s • z.1 g) := fun g => by
    rw [f₁, twScal_conj (E := E) h, smul_sub, smul_smul]; rfl
  simp only [key]
  refine ⟨fun ⟨m, hm⟩ => ⟨(-1 : ℤ_[l]) ^ e • m, fun g => ?_⟩, fun ⟨m, hm⟩ => ⟨(-1 : ℤ_[l]) ^ e • m, fun g => ?_⟩⟩
  · rw [map_smul, ← smul_sub, ← hm, smul_smul, hs, one_smul]
  · rw [map_smul, ← smul_sub, ← hm]

end UpperTheory.V

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
section
noncomputable section

open NumberField

namespace UpperTheory.V

open Formalism.HC UpperTheory.Top

structure BConst where
  R0 : AbF → ℕ
  Rl : ℕ → AbF → ℕ
  CK : ℝ
  CK_pos : 0 < CK

def BConst.R (K : BConst) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) : ℕ := K.R0 M + ∑ l ∈ B', K.Rl l (L l)

def BConst.J (K : BConst) (Ct eps : ℝ) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) : ℝ :=
  2 ^ (K.R M B' L + 2) * (2 * K.CK * Ct / eps) ^ K.R M B' L

def admitted (A1 Ct : ℝ) (e t : ℝ → ℕ) : Prop :=
  ∀ x ≥ (2 : ℝ), 2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ A1 ∧ 2 ≤ t x ∧ (t x : ℝ) ≤ x ^ Ct

def PrimePair (m q d : ℕ) : Prop := q.Prime ∧ q % 8 = 3 ∧ d.Prime ∧ d % 16 = 7 ∧ (q * d).Coprime m

def OddPrimesWithRootsOfUnity (B' : Finset ℕ) (L : ℕ → AbF) : Prop := ∀ l ∈ B', l.Prime ∧ l ≠ 2 ∧ (L l).HasMu l

def InRange (J X Y : ℝ) : Prop := X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X

def BaAt (M : AbF) (eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsCompField M (e x) q d E → BoundedHeightTwoPlaceCondition E (t x) (Real.exp (x ^ (4 * eps / 5)))

def BbAt (K : BConst) (B' : Finset ℕ) (L : ℕ → AbF) (eps : ℝ) (t : ℝ → ℕ) (x : ℝ) : Prop :=
  ∀ l ∈ B', ∀ [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField (L l) L₀ →
    ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l (Nat.log l (K.Rl l (L l)) + 3) L₀ L₁ →
      VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5)))

def IsBWindow (K : BConst) (Ct eps : ℝ) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) (e t : ℝ → ℕ) (q d : ℕ) (X Y : ℝ) : Prop :=
  InRange (K.J Ct eps M B' L) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → BaAt M eps e t q d x ∧ BbAt K B' L eps t x

def BShape (K : BConst) (Ct : ℝ)
    (P : ℝ → AbF → Finset ℕ → (ℕ → AbF) → (ℝ → ℕ) → (ℝ → ℕ) → ℕ → ℕ → ℝ → ℝ → Prop) : Prop :=
  ∀ (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF), OddPrimesWithRootsOfUnity B' L → ∀ eps A1 : ℝ, 0 < eps → eps < 1 / 52 →
    ∃ X0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X ≥ X0, ∀ q d : ℕ, PrimePair M.m q d →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * K.J Ct eps M B' L)) → ∃ Y : ℝ, P eps M B' L e t q d X Y

def ThmBab (K : BConst) (Ct : ℝ) : Prop := BShape K Ct (IsBWindow K Ct)

def ThmBc (Ct : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (M : AbF) (A1 : ℝ) (e t : ℝ → ℕ), admitted A1 Ct e t → ∀ x ≥ (2 : ℝ), ∀ q d : ℕ, PrimePair M.m q d →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsCompField M (e x) q d E →
      VVminusLe E (t x) (minusBound C M.deg (Module.finrank ℚ E) (condF E) (t x))

def ThmBcFree : Prop :=
  ∃ C : ℝ, ∀ (M : AbF) (e t q d : ℕ), 2 ≤ e → 2 ≤ t → PrimePair M.m q d →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsCompField M e q d E →
      VVminusLe E t (minusBound C M.deg (Module.finrank ℚ E) (condF E) t)

def Lchi (ψ : PChar) (l : ℕ) : AbF := AbF.cyc (l * ψ.N)

def Jchi (K : BConst) (Ct eps : ℝ) (ψ : PChar) : ℝ := K.J Ct eps (AbF.ofChar ψ) (Bchi ψ) (Lchi ψ)

def HVAt (ψ : PChar) (C eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField ψ (e x) q d E →
    VVplusLe E (t x) (((condF E : ℝ) * t x) ^ C + C * Real.exp (x ^ (4 * eps / 5)))

def ThmHV (K : BConst) (Ct : ℝ) : Prop :=
  ∀ ψ : PChar, ∃ (C : ℝ) (r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ eps A1 : ℝ, 0 < eps → eps < 1 / 52 →
    ∃ X0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X ≥ X0, ∀ q d : ℕ, PrimePair ψ.N q d →
      2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) →
      (∀ y ∈ [ψ.N, ordC ψ, pK ψ, hStar ψ, pOne ψ, r₁, r₂], y < q ∧ y < d) →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * Jchi K Ct eps ψ)) →
      ∀ Y : ℝ, IsBWindow K Ct eps (AbF.ofChar ψ) (Bchi ψ) (Lchi ψ) e t q d X Y →
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → HVAt ψ C eps e t q d x

def JointWin (Ct : ℝ) : Prop :=
  ∀ (ψ : PChar) (eps A1 : ℝ), 0 < eps → eps < 1 / 52 → ∀ e t : ℝ → ℕ, admitted A1 Ct e t →
    ∃ (J C P X0 : ℝ), 0 < J ∧ ∀ X ≥ X0, ∀ q d : ℕ, PrimePair ψ.N q d →
      2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) → P < (q : ℝ) → P < (d : ℝ) →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
      ∃ Y : ℝ, InRange J X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
        BaAt (AbF.ofChar ψ) eps e t q d x ∧ HVAt ψ C eps e t q d x

theorem thmBc_iff {Ct : ℝ} (hC : 1 ≤ Ct) : ThmBc Ct ↔ ThmBcFree := by
  classical
  constructor
  · rintro ⟨C, H⟩
    refine ⟨C, fun M e t q d he ht hp E _ _ _ hE => ?_⟩
    set x : ℝ := max ((2 : ℝ) ^ e) t with hx
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hx2 : (2 : ℝ) ≤ x := ht2.trans (le_max_right _ _)
    have hA : admitted 2 Ct (fun y => if y = x then e else 2) (fun y => if y = x then t else 2) := by
      intro y hy
      have h1 : y ≤ y ^ Ct := Real.self_le_rpow_of_one_le (by linarith) hC
      have h2 : y ≤ y ^ (2 : ℝ) := Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
      by_cases hyx : y = x
      · simp only [if_pos hyx]
        exact ⟨he, le_trans (hyx ▸ le_max_left _ _) h2, ht, le_trans (hyx ▸ le_max_right _ _) h1⟩
      · simp only [if_neg hyx]
        refine ⟨le_rfl, ?_, le_rfl, by push_cast; linarith⟩
        rw [Real.rpow_two]
        gcongr
    have := H M 2 _ _ hA x hx2 q d hp E (by simpa only [if_true] using hE)
    simpa only [if_true] using this
  · rintro ⟨C, H⟩
    exact ⟨C, fun M A1 e t ha x hx q d hp E _ _ _ hE => H M _ _ q d (ha x hx).1 (ha x hx).2.2.1 hp E hE⟩

theorem primeSetBoundData_of_primitiveChar (ψ : PChar) : OddPrimesWithRootsOfUnity (Bchi ψ) (Lchi ψ) := fun _ hl =>
  ⟨(prime_of_mem_Bchi hl).1, (prime_of_mem_Bchi hl).2, AbF.hasMu_cyc (prime_of_mem_Bchi hl).1.pos (NeZero.pos _)⟩

theorem BConst.J_pos (K : BConst) {Ct eps : ℝ} (hC : 0 < Ct) (he : 0 < eps) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) :
    0 < K.J Ct eps M B' L := by
  have := K.CK_pos
  unfold BConst.J
  positivity

theorem jointWin_of {K : BConst} {Ct : ℝ} (hC : 0 < Ct) (hB : ThmBab K Ct) (hV : ThmHV K Ct) : JointWin Ct := by
  intro ψ eps A1 h0 h1 e t ha
  obtain ⟨X0, H⟩ := hB (AbF.ofChar ψ) (Bchi ψ) (Lchi ψ) (primeSetBoundData_of_primitiveChar ψ) eps A1 h0 h1
  obtain ⟨C, r₁, r₂, -, -, H'⟩ := hV ψ
  obtain ⟨X1, H'⟩ := H' eps A1 h0 h1
  refine ⟨Jchi K Ct eps ψ, C, (([ψ.N, ordC ψ, pK ψ, hStar ψ, pOne ψ, r₁, r₂].sum : ℕ) : ℝ), max X0 X1,
    K.J_pos hC h0 _ _ _, fun X hX q d hp a b c c' hl => ?_⟩
  obtain ⟨Y, hY⟩ := H e t ha X ((le_max_left _ _).trans hX) q d hp hl
  refine ⟨Y, hY.1, fun x u v => ⟨(hY.2 x u v).1,
    H' e t ha X ((le_max_right _ _).trans hX) q d hp a b (fun y hy => ?_) hl Y hY x u v⟩⟩
  have := List.le_sum_of_mem hy
  exact ⟨this.trans_lt (by exact_mod_cast c), this.trans_lt (by exact_mod_cast c')⟩

end UpperTheory.V

end
end

