module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ChainEmbInj
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section NV

variable {K σ : Type} [Field K]

theorem nv_mul {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F * G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_mul F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem nv_add {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F + G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem nv_pow {v : σ} {F : MvPolynomial σ K} (h1 : v ∉ F.vars) (n : ℕ) : v ∉ (F ^ n).vars := by
  intro h
  exact h1 (MvPolynomial.vars_pow F n h)

theorem nv_prod {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∏ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.vars_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact nv_mul (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

theorem nv_sum {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∑ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact nv_add (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

theorem nv_X {v u : σ} (h : v ≠ u) : v ∉ (X u : MvPolynomial σ K).vars := by
  classical
  rw [MvPolynomial.vars_X, Finset.mem_singleton]
  exact h

theorem nv_rename {τ : Type} {v : σ} (f : τ → σ) (h : ∀ x, f x ≠ v) (y : MvPolynomial τ K) : v ∉ (rename f y).vars := by
  classical
  intro hv
  obtain ⟨x, _, hx⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename f y hv)
  exact h x hx

theorem cth_rename {τ : Type} (f : τ → σ) (hf : Function.Injective f) (x : τ) (n : ℕ) (y : MvPolynomial τ K) :
    cth (f x) n (rename f y) = rename f (cth x n y) := by
  induction y using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [rename_monomial, cth_monomial, cth_monomial, rename_monomial, Finsupp.mapDomain_apply_of_injective hf]
  | add p q hp hq => rw [map_add (f := _), cth_add, cth_add, map_add (f := _), hp, hq]

theorem cth_X_pow (v : σ) (b z : ℕ) : cth v b ((X v : MvPolynomial σ K) ^ z) = (z.choose b) • (X v : MvPolynomial σ K) ^ z := by
  rw [X_pow_eq_monomial, cth_monomial, Finsupp.single_eq_same, one_mul, ← Nat.cast_smul_eq_nsmul K,
    smul_monomial, smul_eq_mul, mul_one]

end NV

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem chainEmb_inj (N r t : ℕ) : Function.Injective (chainEmb N r t) := by
  intro a b h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem Ehat_eq {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      ∑ c, X (chainEmb N r D.T.t (tieW hT i, c)) * X (chainEmb N r D.T.t (tieE hT i, c)) := by
  have e1 : finPos N (D.T.pos i) = Fin.castSucc (tieW hT i) := by
    apply Fin.ext
    simp only [finPos, tieW, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  have e2 : finPos N (D.T.pos i + 1) = Fin.castSucc (tieE hT i) := by
    apply Fin.ext
    simp only [finPos, tieE, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  rw [BlockData.Ehat, e1, e2]
  rfl

def pairP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    MvPolynomial (Fin N × Fin r) (KK O) :=
  ∑ c, X (tieW hT i, c) * X (tieE hT i, c)

theorem Ehat_eq' {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      rename (chainEmb N r D.T.t) (pairP O r hT i) := by
  rw [Ehat_eq hT i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [pairP, map_sum, rename_X]

theorem tieW_ne_tieE {D : BlockData N} (hT : TieOK D) (i i' : Fin D.T.t) : tieW hT i ≠ tieE hT i' := by
  intro h
  have := congrArg Fin.val h
  simp only [tieW, tieE] at this
  exact hT.sep i' i this.symm

theorem nv_Ehat {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.castSucc i)) (h2 : v ≠ scalS N r D.T.t (Fin.castSucc i))
    (h3 : ∀ c, v ≠ chainEmb N r D.T.t (tieW hT i, c)) (h4 : ∀ c, v ≠ chainEmb N r D.T.t (tieE hT i, c)) :
    v ∉ (D.Ehat O (r := r) i).vars := by
  rw [Ehat_eq hT i]
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

theorem nv_Eplus (D : BlockData N) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.last D.T.t)) (h2 : v ≠ scalS N r D.T.t (Fin.last D.T.t))
    (h3 : ∀ c, v ≠ Sum.inl (Fin.castSucc D.uPos, c)) (h4 : ∀ c, v ≠ xiVar N r D.T.t c) :
    v ∉ (D.Eplus O (r := r)).vars := by
  unfold BlockData.Eplus
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

theorem nv_xi {t b : ℕ} {v : BVar N r t} (h : ∀ c, v ≠ xiVar N r t c) {g : MvPolynomial (BVar N r t) (KK O)}
    (hg : g ∈ XiPolZ O N r t b) : v ∉ g.vars := by
  intro hv
  obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support v).1 hv
  have h1 := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 (Submodule.mem_inf.1 hg).1 hm
  obtain ⟨c, hc⟩ := h1.1 v hvm
  exact h c hc

def OddV (D : BlockData N) : BVar N r D.T.t → Prop
  | Sum.inl (a, _) => a ≠ Fin.castSucc D.uPos ∧ a ≠ Fin.last N
  | Sum.inr (l, _) => l ≠ Fin.last D.T.t

theorem tail_chain (D : BlockData N) (jp : ℕ) (a0 : Fin N) (ha0 : a0 ≠ D.uPos) (c : Fin r) (b : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    cth (chainEmb N r D.T.t (a0, c)) b (tailP O r D jp y g) = tailP O r D jp (cth (a0, c) b y) g := by
  have hfree : ∀ F : MvPolynomial (BVar N r D.T.t) (KK O), chainEmb N r D.T.t (a0, c) ∉ F.vars →
      ∀ μ ∈ F.support, μ (chainEmb N r D.T.t (a0, c)) = 0 := by
    intro F h μ hμ
    by_contra hne
    exact h ((MvPolynomial.mem_vars_iff_mem_support _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hne⟩)
  have hE : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r)).vars := by
    refine nv_Eplus D ?_ ?_ ?_ ?_
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalS]
    · intro c' h
      simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
      exact ha0 (Fin.castSucc_injective _ h.1)
    · intro c' h
      simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
      exact Fin.castSucc_ne_last _ h.1
  have hP : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
      X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) (KK O)).vars := by
    refine nv_mul (nv_mul (nv_pow hE jp) (nv_prod _ fun i _ => nv_pow (nv_X ?_) _)) (nv_pow (nv_X ?_) _)
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalZ]
  have hg' : chainEmb N r D.T.t (a0, c) ∉ g.vars := by
    refine nv_xi (fun c' h => ?_) hg
    simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Fin.castSucc_ne_last _ h.1
  have key : ∀ Y : MvPolynomial (Fin N × Fin r) (KK O), tailP O r D jp Y g =
      (D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
        X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus) * (g * rename (chainEmb N r D.T.t) Y) := by
    intro Y
    unfold tailP
    ring
  rw [key, key, cth_mul_free _ _ (hfree _ hP), cth_mul_free _ _ (hfree _ hg'),
    cth_rename _ (chainEmb_inj N r D.T.t)]

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultAt
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem val_digit {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (μ : σ → ℕ) :
    (∏ v, (ρ v + L v * μ v).factorial).factorization p =
      (∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v)).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, -⟩ := h2 σ t' ρ' hlt
  set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
  set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
  have hU0 : U ≠ 0 := (hunit e').1
  have hUv : padicValRat p U = 0 := (hunit e').2
  have key : ((∏ v, (ρ v + L v * μ v).factorial : ℕ) : ℚ) =
      ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) * U := by
    push_cast
    rw [hU, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : odd v
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_pos hv] at this ⊢
      rw [(hodd v hv).1, this]
      ring
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_neg hv] at this ⊢
      rw [(hend v hv).1, (hend v hv).2]
      simp only [zero_add, mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one, zero_add] at this ⊢
      rw [← this]
      simp
  have hQ0 : ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.2 fun v _ =>
      mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hv := congrArg (padicValRat p) key
  rw [padicValRat.mul hQ0 hU0, hUv, add_zero, padicValRat.of_nat, padicValRat.of_nat] at hv
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact_mod_cast hv

def tdeg (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (x : X.TT × Bool) : ℕ :=
  multideg (ioExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b)) x

def TrueDegAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∏ x : X.TT × Bool, (tdeg C0 CE1 CE2 X j b x).factorial = facSeg X j ∧
      ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) = lgSeg X j

def CoarseMultAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p ≤
        (expFact (mu0 C0 CE1 CE2 X j b)).factorization X.p + lgSeg X j

theorem kapNumAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hT : TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  obtain ⟨hT1, hT2⟩ := hT X hD1 hH hc j b hb
  have hM1 := hM X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b

  obtain ⟨M, hM0, hEM, hMv⟩ := expFact_mul X.p (tdeg C0 CE1 CE2 X j b) (ioExp C0 CE1 CE2 X j b μ0) (fun x => rfl)
  rw [hT1] at hEM
  have hMv' : M.factorization X.p ≤ X.m * lgSeg X j := by
    rw [← hT2, Finset.mul_sum]
    refine hMv.trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    simp

  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  have hvd := val_digit h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) μ0
  have hE0 : expFact (ioExp C0 CE1 CE2 X j b μ0) ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hmu0 : expFact μ0 = ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
  have hR0 : Rblk C0 CE1 CE2 X j b ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP1 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
      symLev X.p C0 CE1 CE2 X j v * μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP2 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hP3 : (∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hsplit : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (μ0 v).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) =
      (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
        (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) * ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hvE : (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p =
      (PhiB C0 CE1 CE2 X j b).factorization X.p + (expFact μ0).factorization X.p := by
    rw [expFact_ioExp, Nat.factorization_mul hR0 hP1, Finsupp.add_apply, hvd, hsplit, Nat.factorization_mul hP2 hP3,
      Finsupp.add_apply, hmu0]
    unfold PhiB
    rw [Nat.factorization_mul hR0 hP2, Finsupp.add_apply]
    ring
  have hvF : (facSeg X j).factorization X.p = (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p +
      M.factorization X.p := by
    rw [← hEM, Nat.factorization_mul hE0 hM0, Finsupp.add_apply]

  have hdv : expFact μ0 ∣ ∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial := by
    have h := dvdAt C0 CE1 CE2 X j b hb μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b)
    unfold Nblk at h
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (specConst_ne _ _ _)) h
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hle : (expFact μ0).factorization X.p ≤ (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p :=
    (Nat.factorization_le_iff_dvd (by rw [hmu0]; exact hP3) hc0).2 hdv X.p
  constructor
  · rw [hvF, hvE]
    have : X.m * lgSeg X j ≤ (X.m + 1) * lgSeg X j := Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  · rw [hvF, hvE]
    omega

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LevOfSymVar
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem lev_of_symVar (v : BV C0 CE1 CE2 X j) (i : Fin (segS X.TT j)) (h : (symVar C0 CE1 CE2 X j v).1.1 = topOdd X j i) :
    symLev X.p C0 CE1 CE2 X j v = (X.seg C0 CE1 CE2 j).P X.p i := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · by_cases ha : (a : ℕ) < 2 * segS X.TT j
    · simp only [symVar, symLev, dif_pos ha] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg ha] at h
      exact absurd h.symm (topOdd_ne_end X j i)
  · by_cases hl : (l : ℕ) < (X.seg C0 CE1 CE2 j).t
    · simp only [symVar, symLev, dif_pos hl] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg hl] at h
      exact absurd h.symm (topOdd_ne_end X j i)

theorem coarse_dvd (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    (X.seg C0 CE1 CE2 j).P X.p i ∣
      (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) ((topOdd X j i, β), c) := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.dvd_sum fun v _ => ?_
  show _ ∣ (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), c)
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [lev_of_symVar C0 CE1 CE2 X j v i (by rw [h])]
    exact dvd_mul_right _ _
  · exact dvd_zero _

theorem coarse_spec (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool)
    (hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      ((topOdd X j i, β), 0) = 0 := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  show (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), 0) = 0
  rw [Finsupp.single_apply, if_neg]
  intro h
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · simp only [symVar] at h
    split_ifs at h <;> exact Fin.succ_ne_zero _ (congrArg Prod.snd h)
  · simp only [symVar] at h
    split_ifs at h with hl
    · have e := topOdd_inj X j (congrArg (fun z => z.1.1) h)
      have : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (i : ℕ) := congrArg Fin.val e
      omega
    · exact topOdd_ne_end X j i (congrArg (fun z => z.1.1) h).symm

theorem ioExp_mod (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    ioExp C0 CE1 CE2 X j b μ ((topOdd X j i, β), c) % (X.seg C0 CE1 CE2 j).P X.p i =
      if β then b.rz i c else b.ry i c := by
  unfold ioExp
  rw [Finsupp.add_apply, baseExp_odd]
  obtain ⟨k, hk⟩ := coarse_dvd C0 CE1 CE2 X j μ i β c
  rw [hk]
  have hlt : (if β then b.rz i c else b.ry i c) < (X.seg C0 CE1 CE2 j).P X.p i := by
    split_ifs
    · exact (hb.1.1 i c).1
    · exact (hb.1.1 i c).2
  set P := (X.seg C0 CE1 CE2 j).P X.p i
  have e1 : ∀ (cond : Prop) [Decidable cond] (T : ℕ), (if cond then P * T else 0) = P * (if cond then T else 0) := by
    intro cond _ T
    split_ifs <;> simp
  rw [e1, add_assoc, ← mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LiftSubstStart
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  ∑ b : Fin (X.m + 1), C (dW O w (hhLetters X.TT) 1 (topStart X j, true) b) * MvPolynomial.X ((topStart X j, true), b) *
    C (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ b a))

def locExpr (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j0 : Fin (numSeg X.TT)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  xvL X O w g j0 0 * ∏ c : Fin X.m, (∏ j : Fin (numSeg X.TT), xvL X O w g j 0 ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), xvL X O w g j c.succ ^ (X.p ^ segG X.TT j - 1))

theorem liftSubst_start (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (MvPolynomial.X ((topStart X j, true), a)) =
      MvPolynomial.map (algebraMap O (KK O)) (xvL X O w g j a) := by
  rw [liftSubst_X_vec X.p X.n' O w (hhLetters X.TT) 1 g hg (topStart X j, true) a rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [xvL, map_sum, map_mul, map_C, map_X, sigMat_apply]
  rfl

theorem locR_lift (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j0 : Fin (numSeg X.TT)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (locR O X j0) =
      MvPolynomial.map (algebraMap O (KK O)) (locExpr X O w g j0) := by
  unfold locR locC locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, liftSubst_start X O w g hg]

def LocalDivisibilityBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      (C S.w : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O) ∣ locExpr X O S.w g j0

theorem loc4Ord_of (h : LocalDivisibilityBound) : LocalOrderBound := by
  intro X _ O _ _ _ _ S hS hD h2 j0 g hg hpl
  obtain ⟨Q, hQ⟩ := h X O S hS hD h2 j0 g hg hpl
  unfold InWjRg
  rw [locR_lift X O S.w g hg j0, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

