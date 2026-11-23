module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001
public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem bideterminantDominance : BideterminantDominance := by
  classical
  intro R _ r n K sz hsz I m hm
  have hm' : m ∈ (∏ k : Fin K, initMinor R (I k) (hsz k)).support := hm
  refine ⟨fun k => ?_, ?_⟩
  · have h := support_prod_le_of_additive (rowPart k) (rowPart_zero k)
      (rowPart_add k) Finset.univ (fun k' => initMinor R (I k') (hsz k'))
      (fun k' => min k (sz k'))
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').1 k)
      m hm'
    exact h.trans_eq (sum_min_eq_shapeDeg sz hsz k)
  · have h := support_prod_eq_of_additive rowTot rowTot_zero
      rowTot_add Finset.univ (fun k' => initMinor R (I k') (hsz k')) sz
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').2)
      m hm'
    have h2 := sum_min_eq_shapeDeg sz hsz n
    have h3 : ∑ t : Fin n with t.val < n, shapeDeg sz t =
        ∑ t : Fin n, shapeDeg sz t :=
      Finset.sum_congr (Finset.filter_true_of_mem fun t _ => t.isLt) fun _ _ => rfl
    have h4 : ∑ k' : Fin K, min n (sz k') = ∑ k' : Fin K, sz k' :=
      Finset.sum_congr rfl fun k' _ => min_eq_right (hsz k')
    exact h.trans (h4.symm.trans (h2.trans h3))

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColLexInitMinor
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lcminor_initMinor_eq (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs = ∑ σ : Equiv.Perm (Fin s),
      monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
        (((Equiv.Perm.sign σ : ℤ) : R)) := by
  rw [initMinor, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply]
  rw [← mul_one (((Equiv.Perm.sign σ : ℤ) : R)), ← C_mul_monomial, monomial_sum_one,
    Units.smul_def, zsmul_eq_mul]
  congr 1

theorem colLexInitMinor_of (h : MinorExpLt) : ColLexInitMinor := by
  intro R _ _ r n s I hs hI
  rw [lcminor_initMinor_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin s)))]
  simp only [Equiv.Perm.one_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one]
  set g := ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin s)),
    monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
      (((Equiv.Perm.sign σ : ℤ) : R)) with hg_def
  set e := ∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 with he
  have hdf : (colLex r n).degree (monomial e (1 : R)) = e := by
    classical
    rw [MonomialOrder.degree_monomial]
    simp
  by_cases hg : g = 0
  · rw [hg, add_zero, hdf, MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩
  · have hne : (Finset.univ.erase (1 : Equiv.Perm (Fin s))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      apply hg
      rw [hg_def, h0, Finset.sum_empty]
    have hlt : (colLex r n).toSyn ((colLex r n).degree g) <
        (colLex r n).toSyn ((colLex r n).degree (monomial e (1 : R))) := by
      rw [hdf]
      refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
      obtain ⟨σ0, hσ0⟩ := hne
      rw [Finset.sup_lt_iff (lt_of_le_of_lt bot_le (h r n s I hs hI σ0 (Finset.ne_of_mem_erase hσ0)))]
      intro σ hσ
      exact lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (h r n s I hs hI σ (Finset.ne_of_mem_erase hσ))
    rw [MonomialOrder.degree_add_of_lt hlt, MonomialOrder.leadingCoeff_add_of_lt hlt, hdf,
      MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lccomp_weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    (Finsupp.weight (colW r n) m) t = ∑ a : Fin r, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [colW, Pi.single_apply]

theorem columnSums_holds : ColSums := by
  intro R _ r n ν f hf m hm t
  have h1 := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [← lccomp_weight_colW_apply, h1 (mem_support_iff.mp hm)]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColumnLexBideterminant
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem columnLexBideterminant_of_initialMinor (h : ColLexInitMinor) : ColumnLexBideterminant := by
  intro R _ _ r n K sz hsz I hI
  have hm : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      (colLex r n).leadingCoeff (initMinor R (I k) (hsz k)) = 1 :=
    fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).2
  have hreg : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      IsRegular ((colLex r n).leadingCoeff (initMinor R (I k) (hsz k))) := by
    intro k hk
    rw [hm k hk]
    exact isRegular_one
  refine ⟨?_, ?_⟩
  · unfold bideterminant bidetExp
    rw [MonomialOrder.degree_prod_of_regular hreg]
    exact Finset.sum_congr rfl fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).1
  · unfold bideterminant
    rw [MonomialOrder.leadingCoeff_prod_of_regular hreg]
    exact Finset.prod_eq_one hm

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleMap : DualWeylMap := by
  intro R S _ _ φ r n ν f hf
  rw [lsat_mem_dualWeyl] at hf ⊢
  refine ⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩
  rw [← lsat_map_colAddGen, hf.2 l j hlj, map_rename]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleMul : DualWeylMul := fun _ _ _ _ _ _ _ _ =>
  ⟨fun hf hg => dualWeyl_mul hf hg, one_mem_dualWeyl⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section NonDomMain

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEv (R : Type*) [CommRing R] (r n : ℕ) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun o => o.elim 0 X

lemma ndEv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (colAddGen R l j g) = g := by
  have : (ndEv R r n).comp (colAddGen R (r := r) l j) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, colAddGen, aeval_X, AlgHom.id_apply]
    split_ifs <;> simp [ndEv]
  exact congrArg (fun φ => φ g) this

lemma ndEv_pderiv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (pderiv none (colAddGen R l j g)) = ndE R r n l j g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [colAddGen, derivation_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hp, ndEv_colAddGen, ndEv_colAddGen, smul_eq_mul, smul_eq_mul]
    congr 1
    simp only [ndE, mkDerivation_X, colAddGen, aeval_X]
    split_ifs <;> simp [ndEv, Derivation.leibniz, pderiv_X]

lemma nd_pderiv_none_rename (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, add_zero]
  | mul_X p v hp => simp [Derivation.leibniz, hp, pderiv_X]

lemma ndE_eq_zero {l j : Fin n} {f : MvPolynomial (Fin r × Fin n) R}
    (h : colAddGen R l j f = rename some f) : ndE R r n l j f = 0 := by
  rw [← ndEv_pderiv_colAddGen, h, nd_pderiv_none_rename, map_zero]

lemma nd_iter_Eul_l {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n l f = c • f) (k : ℕ) :
    ndEul R r n l ((ndF R r n l j)^[k] f) = (c - k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_l hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c - ((k : R) + 1) = (c - k) - 1 by ring, sub_smul (c - k) 1, one_smul]

lemma nd_iter_Eul_j {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n j f = c • f) (k : ℕ) :
    ndEul R r n j ((ndF R r n l j)^[k] f) = (c + k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_j hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c + ((k : R) + 1) = (c + k) + 1 by ring, add_smul (c + k) 1, one_smul]

lemma nd_iter_E {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {cl cj : R}
    (hl : ndEul R r n l f = cl • f) (hj : ndEul R r n j f = cj • f) (hE : ndE R r n l j f = 0)
    (k : ℕ) :
    ndE R r n l j ((ndF R r n l j)^[k + 1] f) =
      (((k : R) + 1) * (cl - cj - k)) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero =>
    rw [zero_add, Function.iterate_one, nd_comm_EF hlj, hE, map_zero, hl, hj]
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add, one_mul, sub_zero]
    rw [sub_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' (ndF R r n l j) (k + 1) f, nd_comm_EF hlj, ih,
      Derivation.map_smul, nd_iter_Eul_l hlj hl, nd_iter_Eul_j hlj hj,
      ← Function.iterate_succ_apply' (ndF R r n l j) k f, ← sub_smul, ← add_smul]
    congr 1
    push_cast; ring

theorem nd_main [IsDomain R] [CharZero R] (ν : Fin n → ℕ) {l j : Fin n} (hlj : l < j)
    (hν : ν l < ν j) (f : MvPolynomial (Fin r × Fin n) R)
    (hhom : IsWeightedHomogeneous (colW r n) f ν) (hinv : colAddGen R l j f = rename some f) :
    f = 0 := by
  have hne : l ≠ j := ne_of_lt hlj
  have hl := ndEul_homog (R := R) hhom l
  have hj := ndEul_homog (R := R) hhom j
  have hE := ndE_eq_zero hinv
  set G : ℕ → MvPolynomial (Fin r × Fin n) R := fun k => (ndF R r n l j)^[k] f with hG

  have hN : G (ν l + 1) = 0 := by
    apply ndEul_neg_eq_zero l
    rw [hG]; dsimp only
    rw [nd_iter_Eul_l hne hl, Nat.cast_succ, show (ν l : R) - ((ν l : R) + 1) = -1 by ring,
      neg_one_smul]

  have hstep : ∀ k, G (k + 1) = 0 → G k = 0 := by
    intro k hk
    have h1 := nd_iter_E hne hl hj hE k
    rw [show (ndF R r n l j)^[k + 1] f = G (k + 1) from rfl, hk, map_zero] at h1
    have hc : (((k : R) + 1) * ((ν l : R) - (ν j : R) - k)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      have : (ν l : R) - (ν j : R) - k = (((ν l : ℤ) - ν j - k : ℤ) : R) := by push_cast; ring
      rw [this, Int.cast_ne_zero]
      omega
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  have hdown : ∀ d k, G (k + d) = 0 → G k = 0 := by
    intro d
    induction d with
    | zero => intro k hk; simpa using hk
    | succ d ih =>
      intro k hk
      exact hstep k (ih (k + 1) (by rw [show k + 1 + d = k + (d + 1) by omega]; exact hk))
  have := hdown (ν l + 1) 0 (by simpa using hN)
  simpa [hG] using this

theorem dualWeylModuleNonDominant : DualWeylNonDom := by
  intro R _ _ _ r n ν ⟨l, j, hlj, hν⟩
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [dualWeyl, Submodule.mem_inf, mem_weightedHomogeneousSubmodule] at hf
  obtain ⟨hhom, hinv⟩ := hf
  have h1 := Submodule.mem_iInf _ |>.1 hinv l
  have h2 := Submodule.mem_iInf _ |>.1 h1 j
  have h3 := Submodule.mem_iInf _ |>.1 h2 hlj
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply] at h3
  exact nd_main ν hlj hν f hhom h3

end NonDomMain

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lsat_spec_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

theorem lsat_spec_rename {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp
      (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rename_X]

theorem lsat_eval_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n)
    (x : Option (Fin r × Fin n) → R) :
    (aeval x).comp (colAddGen R l j) = (aeval (x ∘ some)).comp (colAdd R l j (x none)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

theorem dualWeylModuleMemIff : DualWeylPoint := by
  intro R _ _ _ r n ν f
  rw [lsat_mem_dualWeyl]
  refine and_congr_right fun _ => forall₂_congr fun l j => imp_congr_right fun _ => ?_
  constructor
  · intro h c
    let ψ : Option (Fin r × Fin n) → MvPolynomial (Fin r × Fin n) R :=
      fun o => Option.elim o (C c) X
    have h1 : aeval ψ (colAddGen R l j f) = aeval ψ (rename some f) := by rw [h]
    have e1 : aeval ψ (colAddGen R l j f) = colAdd R l j c f := by
      rw [← AlgHom.comp_apply, lsat_spec_colAddGen]
    have e2 : aeval ψ (rename some f) = f := by
      rw [← AlgHom.comp_apply, lsat_spec_rename, AlgHom.id_apply]
    rw [← e1, h1, e2]
  · intro h
    apply MvPolynomial.funext
    intro x
    have e := congrArg (fun φ => φ f) (lsat_eval_colAddGen (R := R) l j x)
    simp only [AlgHom.comp_apply, h] at e
    change aeval x (colAddGen R l j f) = aeval x (rename some f)
    rw [e, aeval_rename]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowGraded : DualWeylRowGraded := by
  classical
  intro R _ r n ν μ f hf
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨hcol, hadd⟩ := hf
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hcol hd
    · exact absurd rfl hd
  · let w' : Option (Fin r × Fin n) → (Fin r → ℕ) := fun o => Option.elim o 0 (rowW r n)
    have key : ∀ F : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R,
        (∀ v, IsWeightedHomogeneous w' (F v) (rowW r n v)) → ∀ φ : MvPolynomial (Fin r × Fin n) R,
        weightedHomogeneousComponent w' μ (aeval F φ) =
          aeval F (weightedHomogeneousComponent (rowW r n) μ φ) := by
      intro F hF φ
      refine MvPolynomial.induction_on' φ (fun u a => ?_) (fun p q hp hq => ?_)
      · have hm : IsWeightedHomogeneous w' (aeval F (monomial u a)) (Finsupp.weight (rowW r n) u) := by
          rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, algebraMap_eq]
          have := (isWeightedHomogeneous_C w' a).mul
            (IsWeightedHomogeneous.prod u.support (fun i => F i ^ u i) (fun i => u i • rowW r n i)
              fun i _ => (hF i).pow (u i))
          rwa [zero_add] at this
        have hm0 : IsWeightedHomogeneous (rowW r n) (monomial u a) (Finsupp.weight (rowW r n) u) :=
          isWeightedHomogeneous_monomial _ _ _ rfl
        rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm),
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm0)]
        split_ifs <;> simp
      · simp only [map_add (f := _), hp, hq]
    let G : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R := fun v =>
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
    have hG : ∀ v, IsWeightedHomogeneous w' (G v) (rowW r n v) := by
      intro v
      simp only [G]
      split_ifs
      · refine (isWeightedHomogeneous_X R w' (some v)).add ?_
        have := (isWeightedHomogeneous_X R w' none).mul (isWeightedHomogeneous_X R w' (some (v.1, l)))
        rw [show w' none = 0 from rfl, zero_add] at this
        exact this
      · exact isWeightedHomogeneous_X R w' (some v)
    have hGs : ∀ v, IsWeightedHomogeneous w' ((fun v : Fin r × Fin n =>
        (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) v) (rowW r n v) :=
      fun v => isWeightedHomogeneous_X R w' (some v)
    have hA : colAddGen R (r := r) l j = aeval G := rfl
    have hB : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        aeval (fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) := by
      ext v; simp
    have h1 := hadd l j hlj
    rw [hA, hB] at h1 ⊢
    rw [← key G hG, ← key _ hGs, h1]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowActionStable : DualWeylRowStable := by
  intro R _ r n ν g f hf
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hw, hc⟩ := hf
  refine ⟨isWH_algHom (rowAct R g) (colW r n) (colW r n)
    (rowAct_X_isWH g) hw, ?_⟩
  intro l j hlj
  rw [colAddGen_rowAct, rename_rowAct, hc l j hlj]

end Formalism.GradedWeylDivisibility
end
end

