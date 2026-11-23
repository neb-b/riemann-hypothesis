module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PermutationWordGelfandPolynomialModShorter
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

theorem exists_invol {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → Eˣ),
      (∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum → σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a) ∧
      (∀ a b, a < (bs.map (fun b => (b.2 : ℕ))).sum → b < (bs.map (fun b => (b.2 : ℕ))).sum →
        ptEntryL bs a b = if b = σ a then (t a : E) else 0) ∧
      (∀ c, c + 1 < (bs.map (fun b => (b.2 : ℕ))).sum →
        (σ c = σ (c + 1) + 1 ∧ t (c + 1) = t c) ∨ σ c < σ (c + 1)) := by
  induction bs with
  | nil => exact ⟨id, 1, by simp, by simp, by simp⟩
  | cons p bs ih =>
    obtain ⟨u, s⟩ := p
    obtain ⟨σ, t, h1, h2, h3⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = m at h1 h2 h3 ⊢
    refine ⟨fun a => if a < s then s - 1 - a else s + σ (a - s),
      fun a => if a < s then u else t (a - s), fun a ha => ?_, fun a b ha hb => ?_, fun c hc => ?_⟩
    · by_cases h : a < s
      · have h' : (s : ℕ) - 1 - a < s := by omega
        simp only [if_pos h, if_pos h']
        omega
      · obtain ⟨h4, h5⟩ := h1 (a - s) (by omega)
        have h' : ¬ (s : ℕ) + σ (a - s) < s := by omega
        simp only [if_neg h, if_neg h', Nat.add_sub_cancel_left, h5]
        omega
    · simp only [ptEntryL]
      by_cases h : a < s
      · simp only [if_pos h]
        by_cases h' : b < s
        · rw [if_pos ⟨h, h'⟩]
          exact if_congr (by omega) rfl rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · simp only [if_neg h]
        rw [if_neg (by omega)]
        by_cases h' : b < s
        · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_pos (by omega), h2 _ _ (by omega) (by omega)]
          exact if_congr (by omega) rfl rfl
    · by_cases h : c + 1 < s
      · have h' : c < s := by omega
        simp only [if_pos h, if_pos h']
        exact Or.inl ⟨by omega, trivial⟩
      · by_cases h' : c < s
        · simp only [if_neg h, if_pos h']
          exact Or.inr (by omega)
        · simp only [if_neg h, if_neg h']
          have e : c + 1 - s = c - s + 1 := by omega
          rw [e]
          rcases h3 (c - s) (by omega) with ⟨h4, h5⟩ | h4
          · exact Or.inl ⟨by omega, h5⟩
          · exact Or.inr (by omega)

theorem simple_sum {E : Type} [CommRing E] {r : ℕ} (w : Pt E (r + 1))
    (Z A C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ (r - (b : ℕ)))
    (hA : ∀ i j, i < j → A i j = 0) (hC : ∀ i j, j < i → C i j = 0)
    (h : ∀ a b, ∑ i, A a i * Z i b = ∑ i, Z a i * C i b) :
    ∑ j : Fin r, A j.succ j.castSucc = -∑ j : Fin r, C j.castSucc j.succ := by
  obtain ⟨σ₀, t, h1, h2, h3⟩ := exists_invol w.blocks
  rw [w.size] at h1 h2 h3
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ₀ a, (h1 a a.2).1⟩
  have hinv : Function.Involutive σ' := fun a => Fin.ext (h1 a a.2).2
  let σ : Fin (r + 1) ≃ Fin (r + 1) := hinv.toPerm
  have hσ : ∀ a, (σ a : ℕ) = σ₀ a := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := hinv
  let z : Fin (r + 1) → Eˣ := fun a => t a * (-1) ^ (r - (σ a : ℕ))
  have hZ' : ∀ a b, Z a b = if b = σ a then (z a : E) else 0 := by
    intro a b
    rw [hZ, Pt.mat, h2 _ _ a.2 b.2]
    by_cases hb : b = σ a
    · rw [if_pos hb, if_pos (by rw [hb, hσ]), hb]; simp [z]
    · rw [if_neg hb, if_neg (fun e : (b : ℕ) = σ₀ a => hb (Fin.ext e)), zero_mul]
  have key : ∀ a c, A a c * z c = z a * C (σ a) (σ c) := by
    intro a c
    have := h a (σ c)
    simpa [hZ'] using this
  have term : ∀ a c : Fin (r + 1), (if (a : ℕ) = c + 1 then A a c else 0) =
      -(if (σ c : ℕ) = σ a + 1 then C (σ a) (σ c) else 0) := by
    intro a c
    by_cases hac : (a : ℕ) = c + 1
    · rw [if_pos hac]
      rcases h3 c (hac ▸ a.2) with ⟨h4, h5⟩ | h4
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [← hac] at h5
        rw [if_pos h4]
        have hz : z a = -z c := by
          have := (σ c).2
          have e : r - (σ a : ℕ) = r - (σ c : ℕ) + 1 := by omega
          simp only [z, e, h5, pow_succ]
          simp
        have := key a c
        rw [hz, Units.val_neg, mul_comm, neg_mul, ← mul_neg] at this
        exact (Units.mul_right_inj _).1 this
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [if_neg (by omega), neg_zero]
        have := key a c
        rw [hC _ _ h4, mul_zero] at this
        exact (Units.mul_left_eq_zero _).1 this
    · rw [if_neg hac]
      by_cases h4 : (σ c : ℕ) = σ a + 1
      · rw [if_pos h4]
        have h5 := h3 (σ a) (h4 ▸ (σ c).2)
        rw [← h4, ← hσ, ← hσ, hσσ, hσσ] at h5
        have h6 : a < c := by
          rcases h5 with ⟨h5, -⟩ | h5
          · exact absurd h5 hac
          · exact h5
        have := key a c
        rw [hA _ _ h6, zero_mul] at this
        rw [(Units.mul_right_eq_zero _).1 this.symm, neg_zero]
      · rw [if_neg h4, neg_zero]
  have hs : ∀ M : Fin (r + 1) → Fin (r + 1) → E,
      ∑ a : Fin (r + 1), ∑ c : Fin (r + 1), (if (a : ℕ) = c + 1 then M a c else 0) =
        ∑ j : Fin r, M j.succ j.castSucc := by
    intro M
    rw [Fin.sum_univ_succ]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun (c : Fin (r + 1)) _ =>
      if_neg (show ¬ ((0 : Fin (r + 1)) : ℕ) = c + 1 by simp)), zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j.castSucc]
    · simp
    · intro b _ hb
      exact if_neg fun e => hb (Fin.ext (Nat.add_right_cancel e).symm)
    · simp
  rw [← hs A, ← hs (fun a c => C c a)]
  simp only [term, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm, ← σ.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← σ.sum_comp]
  simp only [hσσ]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem hf_sum_l {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm (∑ i, c i • v i) y = ∑ i, c i * hf L S.Hm (v i) y := by
  classical
  refine Finset.induction_on Finset.univ (by simp [hf]) fun i s hi ih => ?_
  rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]

theorem hf_sum_r {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm y (∑ i, c i • v i) = ∑ i, L.cj (c i) * hf L S.Hm y (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hf_cj L S.herm.1, hf_sum_l, map_sum]
  simp only [map_mul, hf_cj L S.herm.1]

theorem coef_eq (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) (n : S.GLV)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : ∀ j, n (g j) = ∑ i, s i j • g i) (j : Fin r) :
    S.coef g gs n j = s j.castSucc j.succ := by
  simp [Frames.coef, Frames.h, hs, hf_sum_l, dual]

end

theorem psi_eq_psi' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := exists_matrix S S.f S.T S.gram h hh.1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := exists_matrix S S.f' S.T' S.gram' h hh.2
  obtain ⟨C, ⟨hC0, hC1⟩, hC⟩ := exists_matrix S S.f' S.T' S.gram' h⁻¹ (inv_mem hh.2)
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hh.1.1.1
  have hcan : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have hneg : ∀ j : Fin r, s' j.castSucc j.succ = -C j.castSucc j.succ := by
    intro j
    have e : hf L S.Hm (h (h⁻¹ (S.f' j.succ))) (S.es' j) = 0 := by
      rw [hcan, S.dual', if_neg (Fin.castSucc_lt_succ (i := j)).ne']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hC, map_sum] at e
    simp only [map_smul, hf_sum_l] at e
    simp only [hs', hf_sum_l, S.dual', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    rw [Finset.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne, hs1', hC1] at e
    · linear_combination e
    · rintro i - ⟨h1, h2⟩
      by_cases hi : i < j.castSucc
      · rw [hs0' _ _ hi, mul_zero]
      · rw [hC0, zero_mul]
        have h1' : (i : ℕ) ≠ j := fun e => h1 (Fin.ext e)
        have h2' : (i : ℕ) ≠ j + 1 := fun e => h2 (Fin.ext e)
        have h3' : ¬ (i : ℕ) < j := hi
        change (j : ℕ) + 1 < i
        omega
    · simp
    · simp
  have main := simple_sum S.w S.Zh (cT L s) C S.relevant
    (fun i j hij => by rw [cT, hs0 _ _ hij, map_zero]) hC0 (fun a b => by
      have e := hiso (h⁻¹ (S.f' b)) (S.f a)
      rw [hcan, hs, hC, hf_sum_l, hf_sum_r] at e
      simpa [cT, Frames.Zh, Frames.h, mul_comm] using e)
  have e : ∑ j, S.coef S.f' S.es' h j = L.cj (∑ j, S.coef S.f S.es h j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coef_eq S _ _ S.dual h s hs, coef_eq S _ _ S.dual' h s' hs', hneg, map_sum,
      Finset.sum_neg_distrib]
    exact main.symm
  simp only [Frames.psi, Frames.psi', Frames.psiOf]
  rw [e, ← L.local_additive_char_conj, map_mul, AlgEquiv.commutes]

end GlobalTheory.HL.CharAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfAMemAdjoinLow
section
open GlobalTheory.SmoothForms

noncomputable section

open GlobalTheory.SmoothForms.PermWord

namespace GlobalTheory.SmoothForms.GelfGen

theorem exists_eig {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (Y : Matrix (Fin n) (Fin n) K) :
    ∃ l : Fin n → K, ∀ j : ℕ, (Y ^ j).trace = ∑ i, l i ^ j := by
  classical
  set f : Module.End K (Fin n → K) := Matrix.toLin' Y
  have htr : ∀ j, (Y ^ j).trace = ∑ μ ∈ (Formalism.SA.P.finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
    intro j
    rw [← Formalism.SA.P.trace_pow_eq_sum, ← Matrix.toLin'_pow, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  set S := (Formalism.SA.P.finite_eig f).toFinset
  let d : K → ℕ := fun μ => Module.finrank K (f.maxGenEigenspace μ)
  let σ := Σ μ : S, Fin (d μ)
  have hsum : ∀ j, ∑ x : σ, (x.1 : K) ^ j = (Y ^ j).trace := by
    intro j
    rw [htr, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    simp [d]
  have hcard : Fintype.card σ = n := by
    have := hsum 0
    simp at this
    exact_mod_cast this
  let e := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => ((e i).1 : K), fun j => by rw [← hsum, ← e.sum_comp]⟩

theorem newton_closure {K : Type} [Field K] [Algebra ℂ K] {n : ℕ} (l : Fin n → K) (P : ℕ → K → Prop)
    (h1 : P 0 1) (h0 : ∀ j, P j 0) (hadd : ∀ j x y, P j x → P j y → P j (x + y))
    (hsmul : ∀ j (c : ℂ) x, P j x → P j (c • x)) (hmul : ∀ i j x y, P i x → P j y → P (i + j) (x * y))
    (hbase : ∀ j, 1 ≤ j → j ≤ n → P j (∑ i, l i ^ j)) : ∀ j, 1 ≤ j → P j (∑ i, l i ^ j) := by
  classical
  let Q : ℕ → MvPolynomial (Fin n) ℂ → Prop := fun j p => P j (MvPolynomial.aeval l p)
  have hps : ∀ j, MvPolynomial.aeval l (MvPolynomial.psum (Fin n) ℂ j) = ∑ i, l i ^ j := by
    intro j; simp [MvPolynomial.psum]
  have qadd : ∀ j x y, Q j x → Q j y → Q j (x + y) := fun j x y hx hy => by
    simpa [Q] using hadd j _ _ hx hy
  have qC : ∀ j (c : ℂ) x, Q j x → Q j (MvPolynomial.C c * x) := fun j c x hx => by
    rw [MvPolynomial.C_mul']; simpa [Q] using hsmul j c _ hx
  have qmul : ∀ i j x y, Q i x → Q j y → Q (i + j) (x * y) := fun i j x y hx hy => by
    simpa [Q] using hmul i j _ _ hx hy
  have qsign : ∀ j m x, Q j x → Q j ((-1) ^ m * x) := fun j m x hx => by
    have : ((-1 : MvPolynomial (Fin n) ℂ)) ^ m = MvPolynomial.C ((-1) ^ m) := by simp
    rw [this]; exact qC j _ x hx
  have qsub : ∀ j x y, Q j x → Q j y → Q j (x - y) := fun j x y hx hy => by
    rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← pow_one (-1 : MvPolynomial (Fin n) ℂ)]
    exact qadd j _ _ hx (qsign j 1 y hy)
  have qsum : ∀ j (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MvPolynomial (Fin n) ℂ), (∀ a ∈ s, Q j (g a)) →
      Q j (∑ a ∈ s, g a) := fun j s g hg =>
    Finset.sum_induction _ (Q j) (qadd j) (by simpa [Q] using h0 j) hg
  have qbase : ∀ j, 1 ≤ j → j ≤ n → Q j (MvPolynomial.psum (Fin n) ℂ j) := fun j h1 h2 => by
    simpa [Q, hps] using hbase j h1 h2
  have hesymm : ∀ k, Q k (MvPolynomial.esymm (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa [Q] using h1
      by_cases hkn : n < k
      · have : MvPolynomial.esymm (Fin n) ℂ k = 0 := by
          simp only [MvPolynomial.esymm]
          rw [Finset.powersetCard_eq_empty.2 (by rw [Finset.card_univ, Fintype.card_fin]; exact hkn), Finset.sum_empty]
        rw [this]; simpa [Q] using h0 k
      have hm := MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k
      have hQ : Q k ((k : MvPolynomial (Fin n) ℂ) * MvPolynomial.esymm (Fin n) ℂ k) := by
        rw [hm]
        refine qsign _ _ _ (qsum _ _ _ fun a ha => ?_)
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (ih a.1 ha.2) (qbase a.2 (by omega) (by omega))
        rwa [ha.1] at this
      have := qC k ((k : ℂ)⁻¹) _ hQ
      rwa [← mul_assoc, ← map_natCast MvPolynomial.C k, ← map_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk.ne'), map_one, one_mul] at this
  have hpsum : ∀ k, 1 ≤ k → Q k (MvPolynomial.psum (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hkn : k ≤ n
      · exact qbase k hk hkn
      rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℂ k (by omega)]
      refine qsub _ _ _ ?_ (qsum _ _ _ fun a ha => ?_)
      · rw [mul_assoc, ← map_natCast MvPolynomial.C k]
        exact qsign _ _ _ (qC _ _ _ (hesymm k))
      · rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (hesymm a.1) (ih a.2 (by omega) (by omega))
        rwa [ha.1] at this
  intro j hj
  simpa [Q, hps] using hpsum j hj

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem trace_symb (E : Fin n → Fin n → A) (k : ℕ) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (((Matrix.of (gen n)) ^ (k + 1)).trace, c) ∈ symb E (k + 1) := by
  set C := Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)
  let R := MvPolynomial (Fin n × Fin n) ℂ
  let K := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) K]
    exact (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective _ _)
  obtain ⟨l, hl⟩ := exists_eig ((Matrix.of (gen n)).map (algebraMap R K))
  have htr : ∀ j, algebraMap R K ((Matrix.of (gen n)) ^ j).trace = ∑ i, l i ^ j := by
    intro j
    rw [← hl, ← Matrix.map_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  let P : ℕ → K → Prop := fun j p => ∃ q : R, ∃ c ∈ C, algebraMap R K q = p ∧ (q, c) ∈ symb E j
  have key := newton_closure l P
    ⟨1, 1, one_mem _, map_one _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (fun j => ⟨0, 0, zero_mem _, map_zero _, zero_mem _⟩)
    (by
      rintro j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q + q', c + c', add_mem hc hc', map_add _ _ _, by simpa using add_mem h h'⟩)
    (by
      rintro j a _ ⟨q, c, hc, rfl, h⟩
      refine ⟨a • q, a • c, Subalgebra.smul_mem _ hc a, ?_, by simpa using Submodule.smul_mem _ a h⟩
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def])
    (by
      rintro i j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q * q', c * c', mul_mem hc hc', map_mul _ _ _, by simpa using symb_mul E h h'⟩)
    (by
      intro j hj1 hjn
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      refine ⟨_, gelfA E k, Algebra.subset_adjoin ⟨⟨k, by omega⟩, rfl⟩, htr _, ?_⟩
      rw [trace_pow_eq]
      unfold gelfA
      exact sum_mem_symb E (fun idx : Fin (k + 1) → Fin n => idx) fun idx a => idx (a + 1))
    (k + 1) (by omega)
  obtain ⟨q, c, hc, hq, h⟩ := key
  rw [← htr] at hq
  rw [hinj hq] at h
  exact ⟨c, hc, h⟩

theorem exists_symb_low (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by
  have key := perm_sum_mem (Matrix.of (gen n))
    (fun j p => ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val), (p, c) ∈ symb E j)
    ⟨1, one_mem _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (by
      rintro k j p ⟨c, hc, h⟩
      obtain ⟨c', hc', h'⟩ := trace_symb E k
      exact ⟨c' * c, mul_mem hc' hc, by rw [← Prod.mk_mul_mk]; exact symb_mul E h' h⟩)
    d π (fun _ => 0)
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Matrix.of_apply] at key
  simp only [List.prod_ofFn]
  exact key

theorem permWord_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) (π : Equiv.Perm (Fin d)) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      wordMap E d (permMat n d π) - c ∈ filt E d := by
  obtain ⟨c, hc, h⟩ := exists_symb_low E d π
  refine ⟨c, hc, shorter_le_filt E d ?_⟩
  have h2 := symb_sub hE (sum_mem_symb E (fun (K : Fin d → Fin n) a => K (π a)) fun K => K)
  have h1 := symb_sub hE h
  have h3 := sub_mem h2 h1
  rw [sub_sub_sub_cancel_right] at h3
  rw [wordMap_permMat]
  exact h3

theorem low_le (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) ≤ Algebra.adjoin ℂ (Set.range (gelfA E)) :=
  Algebra.adjoin_mono (by rintro _ ⟨k, rfl⟩; exact ⟨k.val, rfl⟩)

theorem central_of_filt_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) :
    ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  induction d with
  | zero =>
    intro z hz _
    have : filt E 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    obtain ⟨_, ⟨M, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (filt_succ d hz)
    obtain ⟨M₀, h1, h2⟩ := _root_.GlobalTheory.matrix_commutant_lift_mod_stable _ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
      ((filt E d).comap (wordMap E d))
      (by rintro _ ⟨p, rfl⟩; exact ⟨(p.2, p.1), (polar_conjTranspose d p.1 p.2).symm⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← _root_.GlobalTheory.SmoothForms.commutator_wordMap A n E hE]
        exact filt_ad hE d _ _ hN) M
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← _root_.GlobalTheory.SmoothForms.commutator_wordMap A n E hE]
        have h3 := neg_mem (filt_ad hE d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h3 : M₀ ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
      refine _root_.GlobalTheory.SmoothForms.bicomm_permMat n d M₀ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {M₀} := by
        refine Algebra.adjoin_le ?_
        rintro x hx _ rfl
        exact (h2 x hx).symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)) ⊔
          filt E d).comap (wordMap E d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := permWord_low hE d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    obtain ⟨c, hc1, u, hu, hcu⟩ := Submodule.mem_sup.1 (h4 h3)
    have h5 : wordMap E d M + y - c ∈ filt E d := by
      have h6 : wordMap E d (M - M₀) ∈ filt E d := h1
      have := add_mem (add_mem h6 hu) hy
      convert this using 1
      rw [map_sub, ← hcu]; abel
    have h7 := ih _ h5 fun a b => by
      rw [mul_sub, sub_mul, hc, gelf_adjoin_comm hE (low_le E hc1)]
    simpa using add_mem h7 hc1

theorem gelfA_mem_filt (E : Fin n → Fin n → A) (m : ℕ) : gelfA E m ∈ filt E (m + 2) := by
  refine shorter_le_filt E _ (Submodule.sum_mem _ fun idx _ => ?_)
  rw [← wd_ofFn E (fun a : Fin (m + 1) => idx a) fun a => idx (a + 1)]
  exact wd_mem_shorter E (by simp)

end GlobalTheory.SmoothForms.GelfGen

theorem GlobalTheory.SmoothForms.gelfA_mem_adjoin_low : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ m : ℕ, gelfA E m ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  intro A _ _ n E hE m
  exact GlobalTheory.SmoothForms.GelfGen.central_of_filt_low hE (m + 2) _ (GlobalTheory.SmoothForms.GelfGen.gelfA_mem_filt E m)
    (_root_.GlobalTheory.SmoothForms.commute_gelfA A n E hE m)

end
end

