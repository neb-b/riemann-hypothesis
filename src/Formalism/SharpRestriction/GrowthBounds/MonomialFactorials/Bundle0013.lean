module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Gen

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]

theorem gc_bdd_gen (be : V → V → ℚ_[p]) (hsm : ∀ (c : ℚ_[p]) u v, be (c • u) v = c * be u v)
    (hsum : ∀ (n : ℕ) (s : Finset (Fin n)) (f : Fin n → V) v, be (∑ i ∈ s, f i) v = ∑ i ∈ s, be (f i) v)
    (L : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hLW : ∀ x ∈ L, x ∈ W) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hz : ∀ v, be 0 v = 0 := by
    intro v
    simpa using hsm 0 0 v

  let x' : Fin n → W := fun i => ⟨x i, hLW _ (hx i)⟩
  have hli : LinearIndependent ℚ_[p] x' := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hg' : ∑ j ∈ s, g j • x j = 0 := by
      have := congrArg Subtype.val hg
      simpa [x'] using this
    have h1 := congrArg (fun u => be u (y i)) hg'
    rw [hsum n s (fun j => g j • x j) (y i), hz] at h1
    simp only [hsm, hxy] at h1
    rw [Finset.sum_eq_single i] at h1
    · simpa [hpD] using h1
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  simpa using hli.fintype_card_le_finrank

theorem bad_le_sub (be : V → V → ℚ_[p]) (L L₁ : Submodule ℤ_[p] V) (hle : L₁ ≤ L) (D : ℤ) (n₁ : ℕ)
    (hn : Module.finrank ℤ_[p] L₁ = n₁)
    (hb : BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0}) :
    Formalism.GM.M.bad p be L D ≤ (Module.finrank ℤ_[p] L - n₁) + Formalism.GM.M.bad p be L₁ D := by
  have hgc : Formalism.GM.M.goodCount p be L₁ D ≤ Formalism.GM.M.goodCount p be L D := by
    unfold Formalism.GM.M.goodCount
    apply csSup_le_csSup hb
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · rintro n ⟨x, y, hx, hy, h⟩
      exact ⟨x, y, fun i => hle (hx i), fun i => hle (hy i), h⟩
  unfold Formalism.GM.M.bad
  rw [hn]
  omega

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

private theorem fockK_eq_lemma {k σ : Type} [Field k] (F G : MvPolynomial σ k) (s : Finset (σ →₀ ℕ))
    (hs : F.support ⊆ s) :
    Formalism.GM.M.fockK F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k)) := by
  unfold Formalism.GM.M.fockK
  apply Finset.sum_subset hs
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

theorem bejj_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (c • u) v = c * bejj p (r := r) G j jp u v := by
  unfold bejj
  rw [map_smul, fockK_eq_lemma _ v _ MvPolynomial.support_smul]
  unfold Formalism.GM.M.fockK
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem bejj_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bejj p (r := r) G j jp (f i) v := by
  classical
  unfold bejj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_div]
  congr 1
  set S := (∑ i ∈ s, G.phiAll p (r := r) j jp (f i)).support ∪
    s.biUnion (fun i => (G.phiAll p (r := r) j jp (f i)).support) with hS
  rw [fockK_eq_lemma _ v S Finset.subset_union_left]
  rw [Finset.sum_congr rfl (fun i hi => fockK_eq_lemma (G.phiAll p (r := r) j jp (f i)) v S
    ((Finset.subset_biUnion_of_mem (fun i => (G.phiAll p (r := r) j jp (f i)).support) hi).trans
      Finset.subset_union_right))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_sum, Finset.sum_mul, Finset.sum_mul]

theorem bejj_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bejj p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  obtain ⟨W, hW, hLW⟩ := exists_fd_Ljj p (r := r) G j jp
  haveI := hW
  exact gc_bdd_gen p (bejj p (r := r) G j jp) (bejj_smul_left p G j jp)
    (fun n s f v => bejj_sum_left p G j jp s f v) (Ljj p (r := r) G j jp) W hLW D

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestOrth (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧ LinearIndependent ℤ_[X.p] e ∧
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) ∧
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) ∧
      n₁ ≤ Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤
        n₁ + Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
          (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋

def RestWin (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) → LinearIndependent ℤ_[X.p] e →
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) →
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) →
      (∑ aPlus ∈ X.winA, (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
        (X.winA.card : ℝ) * (5 / X.L.Y * n₁)

variable {C0 CE1 CE2 X}

theorem restPlusB_of (CM : ℝ) (hY : 0 < X.L.Y) (hO : RestOrth C0 CE1 CE2 X CM) (hW : RestWin C0 CE1 CE2 X CM) :
    RestPlusB C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  obtain ⟨n₁, e, he, hli, horth, hval, hn1, hrk⟩ := hO dl hdl aTop haTop x hx
  have hwin := hW dl hdl aTop haTop x hx n₁ e he hli horth hval
  have hspan : Submodule.span ℤ_[X.p] (Set.range e) ≤
      Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 :=
    Submodule.span_le.2 (by
      rintro _ ⟨a, rfl⟩
      exact he a)
  have hrank : Module.finrank ℤ_[X.p] (Submodule.span ℤ_[X.p] (Set.range e)) = n₁ := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hstep : ∀ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) ≤
      ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) +
        (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    intro aPlus _
    have h := bad_le_sub X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Submodule.span ℤ_[X.p] (Set.range e)) hspan ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ n₁ hrank
      (bejj_bdd X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2 _)
    have h' : bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ ≤
        (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁) +
          Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
            (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := h
    exact_mod_cast h'
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h1 : ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) ≤
      (Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
        (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    exact_mod_cast (by omega)
  have hc : (0 : ℝ) ≤ 5 / X.L.Y := div_nonneg (by norm_num) hY.le
  have h2 : 5 / X.L.Y * (n₁ : ℝ) ≤ 5 / X.L.Y *
      (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hn1) hc
  have hcard : (0 : ℝ) ≤ (X.winA.card : ℝ) := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h1 hcard
  have h4 := mul_le_mul_of_nonneg_left h2 hcard
  nlinarith [hwin, h3, h4]

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankLjjSpan
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem Ljj_span_fd (j : Fin G.T.t → ℕ) (jp : ℕ) :
    FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
    have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
      rw [← bY.span_eq] at h3
      have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
      rw [Submodule.map_span, ← Set.range_comp] at h4
      exact h4
    have hg2 := xi_mem_span p G (G.B - jp) g hg
    show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
    have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
        (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
        MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    have hmul := Submodule.mul_mem_mul hy3 hg2
    rw [Submodule.span_mul_span] at hmul
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨(a, ⟨m, hm⟩), rfl⟩
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have hle2 : Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) ≤ W := by
    rw [Submodule.span_le]
    intro x hx
    exact hle hx
  exact Submodule.finiteDimensional_of_le hle2

theorem finrank_Ljj_span (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) =
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) :=
  finrank_eq_span_gen (R := ℤ_[p]) (K := ℚ_[p]) _

end Lvl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ValFactSumLe
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

section Arith

variable (p : ℕ) [hp : Fact p.Prime]

theorem val_fact_sum_le {ι : Type} (s : Finset ι) (f : ι → ℕ) (L : ℕ) (hL : Nat.log p (∑ i ∈ s, f i) ≤ L) :
    padicValNat p (∑ i ∈ s, f i)! ≤ padicValNat p (∏ i ∈ s, (f i)!) + s.card * L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hL
    have hL' : Nat.log p (∑ i ∈ s, f i) ≤ L := le_trans (Nat.log_mono_right (Nat.le_add_left _ _)) hL
    have ih' := ih hL'
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_eq_ite, if_neg ha]
    generalize hT : ∑ i ∈ s, f i = T at *
    have hC : (f a + T).choose (f a) * (f a)! * T ! = (f a + T)! := by
      have h5 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (f a) T)
      rwa [Nat.add_sub_cancel_left] at h5
    have hv : padicValNat p ((f a + T).choose (f a)) ≤ L := by
      have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + T) (k := f a)
      rw [Nat.factorization_def _ hp.out] at h1
      rw [← Nat.padicValNat_def] at h1
      exact h1.trans hL
    have hc0 : (f a + T).choose (f a) ≠ 0 := (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    have hpr : (∏ i ∈ s, (f i)!) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
    rw [← hC, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (mul_ne_zero hc0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hc0 (Nat.factorial_ne_zero _), (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.factorial_ne_zero _) hpr]
    nlinarith

end Arith

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def letOf : M.BVar N r G.T.t → Fin (N + 1)
  | Sum.inl (a', _) => a'
  | Sum.inr (i, false) => zLet G i
  | Sum.inr (i, true) => sLet G i

theorem wL_eq (a : Fin (N + 1)) (v : M.BVar N r G.T.t) : wL (r := r) G a v = if letOf G v = a then 1 else 0 := by
  rcases v with ⟨a', c⟩ | ⟨i, _ | _⟩ <;> rfl

theorem weight_eq (a : Fin (N + 1)) (μ : M.BVar N r G.T.t →₀ ℕ) :
    Finsupp.weight (wL (r := r) G a) μ = ∑ v ∈ Finset.univ.filter (fun v => letOf G v = a), μ v := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [wL_eq]
  split_ifs <;> simp

theorem val_letters_le (μ : M.BVar N r G.T.t →₀ ℕ) (d : Fin (N + 1) → ℕ)
    (hw : ∀ a, Finsupp.weight (wL (r := r) G a) μ = d a) (L : ℕ) (hL : ∀ a, Nat.log p (d a) ≤ L) :
    padicValNat p (∏ a, (d a)!) ≤ padicValNat p (μ.prod fun _ k => k !) + ((N + 1) * r + (G.T.t + 1) * 2) * L := by
  classical
  have hprod : ∀ {α : Type} (s : Finset α) (g : α → ℕ), (∀ i ∈ s, g i ≠ 0) →
      padicValNat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValNat p (g i) := by
    intro α s g hg
    induction s using Finset.induction_on with
    | empty => simp [Nat.padicValNat_def, multiplicity_one_right]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]
  have hμ : (μ.prod fun _ k => k !) = ∏ v, (μ v)! := Finsupp.prod_fintype _ _ (fun _ => rfl)
  rw [hμ, hprod _ _ (fun _ _ => Nat.factorial_ne_zero _), hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)]
  have hfib : ∀ a, padicValNat p (d a)! ≤ ∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), padicValNat p (μ v)! +
      (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L := by
    intro a
    have hd : d a = ∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), μ v := by rw [← hw a, weight_eq]
    have h6 := val_fact_sum_le p (Finset.univ.filter (fun v => letOf (r := r) G v = a)) μ L (by rw [← hd]; exact hL a)
    rw [hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)] at h6
    rw [hd]
    exact h6
  calc ∑ a, padicValNat p (d a)!
      ≤ ∑ a, (∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), padicValNat p (μ v)! +
          (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L) := Finset.sum_le_sum (fun a _ => hfib a)
    _ = ∑ v, padicValNat p (μ v)! + (Finset.univ : Finset (M.BVar N r G.T.t)).card * L := by
        rw [Finset.sum_add_distrib, Finset.sum_fiberwise, ← Finset.sum_mul,
          Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (letOf (r := r) G v))]
    _ = _ := by
        simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

