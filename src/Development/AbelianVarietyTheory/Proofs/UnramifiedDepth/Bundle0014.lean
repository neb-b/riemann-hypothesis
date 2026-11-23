module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import ReciprocityTheory.DualLattices.FormalChartAtZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdeal
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.ChainStep

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) :
    V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right (by simpa using hb))

theorem int_mul_mm {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one

def intRing (V : VF C) : Subring C where
  carrier := {a | V.Ge 0 a}
  mul_mem' ha hb := VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' ha hb := VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' ha := VF.Ge.neg ha

theorem add_pow_congr {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM ((a + b) ^ (V.l ^ n) - (a ^ (V.l ^ n) + b ^ (V.l ^ n))) := by
  have h : ∃ r : intRing V, ((⟨a, ha⟩ : intRing V) + ⟨b, hb⟩) ^ (V.l ^ n) =
      (⟨a, ha⟩ : intRing V) ^ (V.l ^ n) + (⟨b, hb⟩ : intRing V) ^ (V.l ^ n) + (V.l : intRing V) * r := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : intRing V) ⟨b, hb⟩ n
    first
      | exact ⟨r, hr⟩
      | exact ⟨_, by rw [hr, mul_assoc, mul_assoc]⟩
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (fun z : intRing V => (z : C)) hr
  push_cast at h2
  rw [h2, add_sub_cancel_left]
  exact mm_mul_int mm_l r.2

theorem sum_pow_congr {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) (n : ℕ) :
    V.MM ((∑ i ∈ s, f i) ^ (V.l ^ n) - ∑ i ∈ s, f i ^ (V.l ^ n)) := by
  induction s using Finset.induction_on with
  | empty => simpa [V.l_prime.ne_zero] using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h' := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 := add_pow_congr (h a (Finset.mem_insert_self a s)) (VF.Ge.sum h') n
    have h2 := mm_add h1 (ih h')
    convert h2 using 1
    ring

theorem even_val_add {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d)).val ↔ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2,
    Nat.add_mod, Nat.mod_mod_of_dvd _ h2]
  simp

theorem big_add {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (h : X.big g a) (s : ℕ) :
    X.big g (a + ((2 * s : ℕ) : ZMod d)) := by
  fin_cases g
  · exact (hA.2 _).2 ((even_val_add hA.1 a s).2 ((hA.2 _).1 h))
  · have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
    refine (h1 _).2 fun h2 => (h1 _).1 h ?_
    exact (hA.2 _).2 ((even_val_add hA.1 a s).1 ((hA.2 _).1 h2))

theorem mm_of_tan {d : ℕ} {I J : Type} [Fintype I] [Fintype J] {G : Cart V d I J} (S : Sys G)
    (z : I → C) (h : ∀ k, V.MM (∑ c, z c * S.tan c k)) (c : I) : V.MM (z c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : z c = ∑ k, (∑ b, z b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, z b * S.tan b k * S.U⁻¹ k c = z b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [h2]
  exact mm_sum fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem rank_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  intro C _ V d _ I J _ _ X hA g a hbig i S Z D hD s hs m y hy hyi N x hx hxi hker
  set F : Finset (I g) := Finset.univ.filter (fun c => D.lev c = s) with hF
  have hFm : ∀ c, c ∈ F ↔ D.lev c = s := fun c => by simp [hF]
  have hDi : D.i = i := hD.2.2.1
  have hDl : D.l = V.l := hD.2.1
  have hDv : D.v = V.v := hD.1
  have hgood : ∀ c ∈ F, D.good c := fun c hc =>
    D.pure_good c (by rw [(hFm c).1 hc, hDi]; omega)
  let w : Fin N → I g → C := fun ν c => ∑ δ, x ν δ * y δ c
  have hw : ∀ ν c, V.Ge 0 (w ν c) := fun ν c => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (hy δ c)
  have hG : ∀ c ∈ F, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 := hD.good (hgood c hc)
    rwa [hD.2.2.2.2 c (by rw [(hFm c).1 hc]; omega), (hFm c).1 hc] at h1
  have hal : ∀ c ∈ F, ∀ e, V.Ge 0 ((V.l : C) * D.al c 2 e) := fun c hc e =>
    hDl ▸ hD.l_mul_al_two_int (hgood c hc) e
  have key := X.R1 hA g _ (big_add X hA g a hbig s) N
    (fun ν => ∑ c ∈ F, w ν c • S.tan c) (fun ν => ∑ c ∈ F, teich V.l (w ν c) (S.cur c))
    (fun ν => Cart.Good.comb F (fun c _ => hw ν c) hG) ?_ ?_
  · omega
  · intro ν k
    rw [Cart.scaledSecond_sum]
    have e1 : ∑ c ∈ F, w ν c ^ (V.l ^ 2) * (X.G g).V2 (S.cur c) k =
        ∑ e, (∑ c ∈ F, w ν c ^ (V.l ^ 2) * ((V.l : C) * D.al c 2 e)) * S.tan e k := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := hD.2.2.2.1 c 2 k (by norm_num)
      simp only [Sys.al, Sys.cur_zero_inl] at h1
      simp only [Cart.V2, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e1]
    refine mm_sum fun e _ => mm_mul_int ?_ (tan_int S e k)
    by_cases he : D.lev e = s + 1
    · have h1 := hker ν e he
      have h2 : V.MM (∑ c ∈ F, (w ν c ^ (V.l ^ 2) - ∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) *
          ((V.l : C) * D.al c 2 e)) :=
        mm_sum fun c hc => mm_mul_int
          (sum_pow_congr (fun δ _ => (hx ν δ).mul_int (hy δ c)) 2) (hal c hc e)
      have e2 : ∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ F, (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2) =
          ∑ c ∈ F, (∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) * ((V.l : C) * D.al c 2 e) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun δ _ => by
          rw [mul_pow]; ring
      convert mm_add h1 h2 using 1
      rw [e2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    · refine mm_sum fun c hc => int_mul_mm ((hw ν c).pow _) ?_
      have hc' := (hFm c).1 hc
      rw [D.al_two c (by rw [hc', hDi]; omega) e,
        D.g_supp c (by rw [hc', hDi]; omega) e (by rw [hc']; exact he), hDl, zero_add,
        mul_inv_cancel_left₀ VF.l_ne_zero]
      refine mm_mul_int mm_l ?_
      have := D.lam_int c e
      rw [hDv] at this
      simpa [VF.Ge] using this
  · intro co hco hmm
    refine hxi co hco (hyi (fun δ => ∑ ν, co ν * x ν δ)
      (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) ?_)
    refine mm_of_tan S _ fun k => ?_
    convert hmm k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hF, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : D.lev c = s
    · simp only [hc, if_true, w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun δ _ => by ring
    · simp [hc]

end GlobalTheory.ChainStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartFirstOrderMemSpan
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma chartFirstOrder_mem_span {S : Type} [CommRing S] {g : ℕ} (a : Fin g → S)
    (x : TrivSqZeroExt S (Fin g → S))
    (hx : x ∈ Ideal.span (Set.range fun i => (TrivSqZeroExt.inl (a i) : TrivSqZeroExt S (Fin g → S)))) :
    x.fst ∈ Ideal.span (Set.range a) ∧ ∀ j, x.snd j ∈ Ideal.span (Set.range a) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨Ideal.subset_span ⟨i, rfl⟩, fun j => by simp⟩
  | zero => exact ⟨by simp, fun j => by simp⟩
  | add y z _ _ hy hz =>
    exact ⟨by simpa using add_mem hy.1 hz.1, fun j => by simpa using add_mem (hy.2 j) (hz.2 j)⟩
  | smul r y _ hy =>
    refine ⟨?_, fun j => ?_⟩
    · rw [smul_eq_mul, TrivSqZeroExt.fst_mul]
      exact Ideal.mul_mem_left _ _ hy.1
    · rw [smul_eq_mul, TrivSqZeroExt.snd_mul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      exact add_mem (Ideal.mul_mem_left _ _ (hy.2 j)) (Ideal.mul_mem_left _ _ hy.1)

theorem chart_fAdd_firstOrder :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) := by
  intro H R₀ _ g B K ch S _ _ a ha

  have nat : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (T' : Type) [CommRing T'] [Algebra R₀ T']
      (φ : T →ₐ[R₀] T') (x y : Fin g → T), (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ k, φ (fAdd ch.F x y k) = fAdd ch.F (fun i => φ (x i)) (fun i => φ (y i)) k := by
    intro T _ _ T' _ _ φ x y hx hy k
    have h := ((H (ch.F k) T (Sum.elim x y)).2 (by rintro (i | i); exacts [hx i, hy i])).1 T' φ
    unfold fAdd
    rw [h]
    congr 1
    funext i
    cases i <;> rfl

  let T := TrivSqZeroExt S (Fin g → S)
  let a' : Fin g → T := fun i => TrivSqZeroExt.inl (a i)
  let e' : Fin g → T := fun j => TrivSqZeroExt.inr (Pi.single j 1)
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => (ha i).map (TrivSqZeroExt.inlHom S (Fin g → S))
  have he' : ∀ i, IsNilpotent (e' i) := fun i => ⟨2, by
    rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩
  have hfst : ∀ k, (fAdd ch.F a' e' k).fst = a k := by
    intro k
    have h := nat T S (TrivSqZeroExt.fstHom R₀ S (Fin g → S)) a' e' ha' he' k
    have h2 := congrFun (ch.F_unit S a ha) k
    rw [← h2]
    exact h
  refine ⟨fun k j => (fAdd ch.F a' e' k).snd j, ?_, ?_⟩
  · intro k j
    let J : Ideal T := Ideal.span (Set.range a')
    have h := nat T (T ⧸ J) (Ideal.Quotient.mkₐ R₀ J) a' e' ha' he' k
    have h0 : (fun i => Ideal.Quotient.mkₐ R₀ J (a' i)) = 0 := by
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    have hn : ∀ i, IsNilpotent (Ideal.Quotient.mkₐ R₀ J (e' i)) := fun i => (he' i).map _
    rw [h0, ch.F_comm _ 0 _ (fun _ => IsNilpotent.zero) hn, ch.F_unit _ _ hn] at h
    have hm : fAdd ch.F a' e' k - e' k ∈ J := Ideal.Quotient.eq.1 h
    have := (chartFirstOrder_mem_span a _ hm).2 j
    rw [TrivSqZeroExt.snd_sub] at this
    have h1 : (1 : Matrix (Fin g) (Fin g) S) k j = (e' k).snd j := by
      simp only [e', TrivSqZeroExt.snd_inr, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1]
    exact this
  · intro e he
    let l : (Fin g → S) →ₗ[R₀] S :=
      { toFun := fun v => v ⬝ᵥ e
        map_add' := fun v w => add_dotProduct _ _ _
        map_smul' := fun r v => smul_dotProduct _ _ _ }
    have hl : ∀ v, l v = v ⬝ᵥ e := fun _ => rfl
    let φ : T →ₐ[R₀] S := TrivSqZeroExt.lift (AlgHom.id R₀ S) l
      (fun v w => by
        simp only [hl, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [mul_mul_mul_comm, he, mul_zero])
      (fun r v => by simp [hl])
      (fun r v => by simp [hl, mul_comm])
    have hφ : ∀ x : T, φ x = x.fst + x.snd ⬝ᵥ e := fun _ => rfl
    funext k
    have h := nat T S φ a' e' ha' he' k
    have e1 : (fun i => φ (a' i)) = a := by
      funext i; simp [hφ, a']
    have e2 : (fun i => φ (e' i)) = e := by
      funext i; simp [hφ, e']
    rw [e1, e2, hφ, hfst] at h
    rw [← h]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffDvdOfAevalAddSqZero
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma polCoef_taylor {R₀ A : Type} [CommRing R₀] [CommRing A] [Algebra R₀ A] {g : ℕ}
    (a : Fin g → A) (i : Fin g) (ε : A) (hε : ε * ε = 0) (G : MvPolynomial (Fin g) R₀) :
    MvPolynomial.aeval (a + Pi.single i ε) G
      = MvPolynomial.aeval a G + MvPolynomial.aeval a (MvPolynomial.pderiv i G) * ε := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add f h hf hh => simp only [map_add (f := _), hf, hh]; ring
  | mul_X f j hf =>
    simp only [map_mul, hf, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add (f := _),
      MvPolynomial.pderiv_X, Pi.add_apply]
    by_cases hij : j = i
    · subst hij
      simp only [Pi.single_eq_same, map_one]
      linear_combination (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) * hε
    · simp only [Pi.single_eq_of_ne hij, map_zero]
      ring

private lemma polCoef_pderiv {R₀ : Type} [CommRing R₀] (p : ℕ) {g N : ℕ}
    (G : MvPolynomial (Fin g) R₀)
    (H : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S,
      (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G)
    {A : Type} [CommRing A] [Algebra R₀ A] (hpA : (p : A) = 0) (x : Fin g → A)
    (hx : ∀ j, x j ^ N = 0) (i : Fin g) :
    MvPolynomial.aeval x (MvPolynomial.pderiv i G) = 0 := by
  have hpS : (p : DualNumber A) = 0 := by
    rw [← map_natCast (algebraMap A (DualNumber A)), hpA, map_zero]
  let φ : A →ₐ[R₀] DualNumber A := IsScalarTower.toAlgHom R₀ A (DualNumber A)
  let a : Fin g → DualNumber A := fun j => φ (x j)
  have h1 := H (DualNumber A) hpS a (Pi.single i DualNumber.eps)
    (fun j => by simp only [a]; rw [← map_pow, hx, map_zero])
    (fun j k => by
      by_cases hj : j = i
      · by_cases hk : k = i
        · subst hj; subst hk
          rw [Pi.single_eq_same, DualNumber.eps_mul_eps]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
      · rw [Pi.single_eq_of_ne hj, zero_mul])
  rw [polCoef_taylor a i _ DualNumber.eps_mul_eps] at h1
  have h2 : MvPolynomial.aeval a (MvPolynomial.pderiv i G) * DualNumber.eps = 0 :=
    add_eq_left.mp h1
  have h3 : MvPolynomial.aeval a (MvPolynomial.pderiv i G)
      = φ (MvPolynomial.aeval x (MvPolynomial.pderiv i G)) := by
    rw [MvPolynomial.comp_aeval_apply]
  rw [h3] at h2
  generalize MvPolynomial.aeval x (MvPolynomial.pderiv i G) = y at h2 ⊢
  have := congrArg TrivSqZeroExt.snd h2
  simpa [φ, TrivSqZeroExt.algebraMap_eq_inl] using this

private lemma polCoef_span {R : Type} [CommRing R] {g N : ℕ} (f : MvPolynomial (Fin g) R)
    (hf : f ∈ Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)) :
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → AddMonoidAlgebra.coeff f m = 0 := by
  rw [Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, rfl⟩ := hf
  intro m hm
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h j
  simp only [Finsupp.single_eq_same] at this
  exact absurd (hm j) (not_lt.mpr this)

theorem coeff_dvd_of_aeval_add_sq_zero :
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff G m = p * r) := by
  intro R₀ _ p hp g N G H m hm ⟨i, hi⟩
  let I : Ideal R₀ := Ideal.span {(p : R₀)}
  let R := R₀ ⧸ I
  let J : Ideal (MvPolynomial (Fin g) R) :=
    Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)
  let A := MvPolynomial (Fin g) R ⧸ J
  have hpR : (p : R) = 0 := by
    have : (Ideal.Quotient.mk I) (p : R₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    simpa using this
  have hpA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap R A), hpR, map_zero]
  let x : Fin g → A := fun j => Ideal.Quotient.mk J (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    simp only [x]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have h4 := polCoef_pderiv p G H hpA x hx i
  have h5 : ∀ f : MvPolynomial (Fin g) R₀, MvPolynomial.aeval x f
      = Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R₀ R) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C]; rfl
    | add f h hf hh => simp only [map_add (f := _), hf, hh]
    | mul_X f j hf => simp only [map_mul, hf, MvPolynomial.aeval_X, MvPolynomial.map_X, x]
  rw [h5, Ideal.Quotient.eq_zero_iff_mem] at h4
  have hpos : 1 ≤ m i := by
    rcases Nat.eq_zero_or_pos (m i) with h | h
    · exact absurd (h ▸ dvd_zero p) hi
    · exact h
  have h6 := polCoef_span _ h4 (m - Finsupp.single i 1)
    (fun j => lt_of_le_of_lt (by simp) (hm j))
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hpos
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_pderiv, tsub_add_cancel_of_le hle] at h6
  have h7 : AddMonoidAlgebra.coeff G m * (m i : R₀) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : (((m - Finsupp.single i 1 : Fin g →₀ ℕ) i : ℕ) : R₀) + 1 = (m i : R₀) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub hpos]; simp
    rw [e] at h6
    exact h6
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h7
  have hc : IsCoprime (p : R₀) (m i : R₀) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hi)
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨u * AddMonoidAlgebra.coeff G m + v * s, by
    linear_combination (-AddMonoidAlgebra.coeff G m) * huv - v * hs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffIntegralOnExponentsSubstOfLowerSet
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.LowerSubst

open MvPowerSeries

variable {C : Type} [Field C] (V : VF C) {σ : Type} (P : (σ →₀ ℕ) → Prop)

def IntOn (g : MvPowerSeries σ C) : Prop := ∀ μ, P μ → V.Ge 0 (coeff μ g)

theorem intOn_one : IntOn V P (1 : MvPowerSeries σ C) := by
  intro α _
  rw [coeff_one]
  split_ifs with h
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intOn_mul (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f g : MvPowerSeries σ C}
    (hf : IntOn V P f) (hg : IntOn V P g) : IntOn V P (f * g) := by
  intro α hα
  rw [coeff_mul]
  refine VF.Ge.sum fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact VF.Ge.mul_int (hf _ (hP α _ (hx ▸ le_self_add) hα)) (hg _ (hP α _ (hx ▸ le_add_self) hα))

theorem intOn_prod (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ C) (h : ∀ i ∈ s, IntOn V P (f i)) : IntOn V P (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOn V P) (fun _ _ => intOn_mul V P hP) (intOn_one V P) h

theorem intOn_pow (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f : MvPowerSeries σ C} (hf : IntOn V P f)
    (n : ℕ) : IntOn V P (f ^ n) := by
  induction n with
  | zero => simpa using intOn_one V P
  | succ n ih => rw [pow_succ]; exact intOn_mul V P hP ih hf

theorem subst_int_on_lower :
    ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  intro C _ V σ τ _ _ P hP γ T hγ hT0 hT α hα
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT0
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs γ α)]
  refine VF.Ge.sum fun β _ => ?_
  have hp : IntOn V P (β.prod fun s e => T s ^ e) :=
    intOn_prod V P hP _ _ fun s _ => intOn_pow V P hP (hT s) (β s)
  rw [smul_eq_mul]
  exact VF.Ge.mul_int (hγ β) (hp α hα)

end GlobalTheory.LowerSubst
end

