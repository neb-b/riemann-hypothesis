module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariablesStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ σ : SL(2, ℤ), ∃ C : ℂ[X], ∀ τ : ℍ, slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  first | exact @GlobalTheory.EichlerChange.polySlash_eichler_smul | exact GlobalTheory.EichlerChange.polySlash_eichler_smul | (intros; apply GlobalTheory.EichlerChange.polySlash_eichler_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalDiagPolyValuedInvariantTranslationTZpowMul
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem evalDiag_T_step (w n : ℕ) (V : ℍ → ℂ[X]) (hV : ∀ τ, V τ ∈ degreeLT ℂ (w + 1))
    (hT : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ)
    (τ : ℍ) :
    (V (ModularGroup.T ^ (n : ℤ) • τ)).eval ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  have hm : mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := ModularGroup.coe_T_zpow _
  have hc : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + n := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [← hT τ, eval_polySlash w _ _ _ (hV _), hm, hc]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    simp
  · rw [hm]
    simp

theorem evalDiag_T_invariant : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  intro w n V hV hT m
  have step := evalDiag_T_step w n V hV hT
  simp only [zpow_mul]
  induction m using Int.induction_on with
  | zero => intro τ; simp
  | succ k ih =>
    intro τ
    rw [zpow_add_one, mul_smul, ih, step]
  | pred k ih =>
    intro τ
    have e : (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ) - 1) • τ =
        (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ)) • ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ) := by
      rw [zpow_sub_one, mul_smul]
    rw [e, ih, ← step ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ), smul_inv_smul]

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeToward
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem index_comap_toSpanSingleton_ne_zero {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by
  have h1 : (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup =
      A.toAddSubgroup.comap (LinearMap.toSpanSingleton R X y).toAddMonoidHom := rfl
  rw [h1, AddSubgroup.index_comap]
  intro h0
  refine hAB (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨r, rfl⟩
  exact B.smul_mem r hy

theorem exists_mem_maximal_annihilator {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) (hBA : ¬ B ≤ A) :
    ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ ∀ r : R, r • x ∈ A ↔ r ∈ P := by
  have hex : ∃ n, ∃ y ∈ B, y ∉ A ∧
      (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index = n := by
    obtain ⟨y, hyB, hyA⟩ := SetLike.not_le_iff_exists.1 hBA
    exact ⟨_, y, hyB, hyA, rfl⟩
  obtain ⟨x, hxB, hxA, hx⟩ := Nat.find_spec hex
  have hne := index_comap_toSpanSingleton_ne_zero A B hAB hxB
  let P : Ideal R := A.comap (LinearMap.toSpanSingleton R X x)
  have hP : ∀ r : R, r • x ∈ A ↔ r ∈ P := fun r => Iff.rfl
  have hfin : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero hne
  have hprime : P.IsPrime := by
    refine ⟨fun htop => hxA ?_, fun {r s} hrs => ?_⟩
    · have : (1 : R) ∈ P := htop ▸ Submodule.mem_top
      simpa using (hP 1).2 this
    · by_contra hcon
      rw [not_or] at hcon
      have hs : s • x ∉ A := fun h => hcon.2 ((hP s).1 h)
      have hmin := Nat.find_min' hex ⟨s • x, B.smul_mem s hxB, hs, rfl⟩
      have hne' := index_comap_toSpanSingleton_ne_zero A B hAB (B.smul_mem s hxB)
      have hle : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup ≤
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        intro a ha
        have ha' : a • x ∈ A := ha
        show a • s • x ∈ A
        rw [smul_comm]
        exact A.smul_mem s ha'
      have hmul := AddSubgroup.relIndex_mul_index hle
      rw [← hx, ← hmul] at hmin
      have h1 : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup.relIndex
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup = 1 := by
        rw [← hmul] at hne
        have h2 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hne)
        have h3 := Nat.pos_of_ne_zero hne'
        nlinarith
      rw [AddSubgroup.relIndex_eq_one] at h1
      have hr : r ∈ (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        show r • s • x ∈ A
        rw [smul_smul]
        exact (hP _).2 hrs
      exact hcon.1 (h1 hr)
  haveI := hprime
  exact ⟨x, hxB, P, Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain _), hfin, hP⟩

theorem exists_adj_selfDual_step : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hA hB hAB hBA
  obtain ⟨x, hxB, P, hPm, hPf, hP⟩ := exists_mem_maximal_annihilator A B hAB hBA
  let T : Submodule R X := Submodule.span R {x}
  have hTB : T ≤ B := (Submodule.span_singleton_le_iff_mem x B).2 hxB
  have hxT : x ∈ T := Submodule.mem_span_singleton_self x
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]
        exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hS : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSA : S ≤ A := fun a ha => ha.1
  have hidx : A.toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := fun h0 =>
    hAB (AddSubgroup.relIndex_eq_zero_of_le_right (fun t ht => hTB ht) h0)
  obtain ⟨-, hdual, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup (fun a ha => ⟨fun h1 => h1.2, fun h1 => ⟨ha, h1⟩⟩)
    (fun t _ => ⟨fun h1 a ha => h.iso hA ha h1,
      fun h1 => (hA t).2 fun a ha => h.swap_eq_one (h1 a ha)⟩) hidx
  refine ⟨S ⊔ T, fun y => ⟨fun hy z hz => ?_, fun hy => ?_⟩,
    ⟨x, Submodule.mem_sup_right hxT, P, hPm, hPf, hP, ?_⟩, ?_⟩
  · obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, hb, u, hu, rfl⟩ := Submodule.mem_sup.1 hz
    rw [h.add_left, h.add_right, h.add_right, h.iso hA ha.1 hb.1, ha.2 u hu,
      h.swap_eq_one (hb.2 t ht), h.iso hB (hTB ht) (hTB hu)]
    simp
  · obtain ⟨t, ht, hyt⟩ := hdual y fun a _ ha =>
      h.swap_eq_one (hy a (Submodule.mem_sup_left ha))
    have ht' : t ∈ T := ht
    have h1 : y + -t ∈ S := by
      refine ⟨(hA _).2 fun a ha => h.swap_eq_one ?_, fun u hu => ?_⟩
      · rw [h.add_right, h.neg_right, hyt a ha, mul_inv_cancel₀ (h.ne_zero _ _)]
      · rw [h.add_left, hy u (Submodule.mem_sup_right hu),
          h.iso hB (B.neg_mem (hTB ht')) (hTB hu), one_mul]
    exact Submodule.mem_sup.2 ⟨_, h1, t, ht', by abel⟩
  · exact sup_le_sup_right (le_inf hSA le_sup_left) _
  · exact sup_le_sup (le_inf le_sup_left hSA) (le_inf le_sup_right hTB)

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPowStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_On_zeta_pow_mul_q_pow : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
  ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  first | exact @GlobalTheory.K5.OnFree.on_free | exact GlobalTheory.K5.OnFree.on_free | (intros; apply GlobalTheory.K5.OnFree.on_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletedLaurentQuotPrimeEquivLaurentFp
section
open GlobalTheory.K5

namespace GlobalTheory.K5

noncomputable def lauRed (p : ℕ) [Fact p.Prime] : Lau p →+* LaurentSeries (ZMod p) where
  toFun x := HahnSeries.map x (PadicInt.toZMod (p := p))
  map_one' := HahnSeries.map_one (PadicInt.toZMod (p := p)).toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem lauRed_coeff (p : ℕ) [Fact p.Prime] (x : Lau p) (n : ℤ) :
    (lauRed p x).coeff n = PadicInt.toZMod (x.coeff n) := rfl

theorem lauRed_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (lauRed p) := by
  intro y
  refine ⟨HahnSeries.map y (⟨fun a => ((ZMod.val a : ℕ) : ℤ_[p]), by simp⟩ : ZeroHom (ZMod p) ℤ_[p]), ?_⟩
  ext n
  rw [lauRed_coeff]
  show PadicInt.toZMod ((ZMod.val (y.coeff n) : ℕ) : ℤ_[p]) = _
  simp

theorem ker_lauRed (p : ℕ) [Fact p.Prime] : RingHom.ker (lauRed p) = pI p := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h : ∀ n, ∃ c : ℤ_[p], x.coeff n = (p : ℤ_[p]) * c := by
      intro n
      have h1 : x.coeff n ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker, ← lauRed_coeff, hx]; rfl
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
      exact h1
    choose c hc using h
    have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine Ideal.mem_span_singleton.2 ⟨⟨c, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro n hn
      rw [HahnSeries.mem_support, hc n]
      exact mul_ne_zero hp hn
    · ext n
      rw [← nsmul_eq_mul, HahnSeries.coeff_nsmul, hc n]
      simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show lauRed p _ = 0
    rw [map_natCast]
    ext n
    rw [← Nat.smul_one_eq_cast, HahnSeries.coeff_nsmul]
    simp

theorem exists_completedLaurent_quot_prime_equiv_laurentFp (p : ℕ) [Fact p.Prime] : ∃ e : (O0 p ⧸ Ideal.span {(p : O0 p)}) ≃+* LaurentSeries (ZMod p),
    e (Ideal.Quotient.mk _ (qO p)) = HahnSeries.single (1 : ℤ) (1 : ZMod p) := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (pI p)) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap _ _ a, (AdicCompletion.evalOneₐ (pI p)).commutes a⟩
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h1 : Ideal.span {(p : O0 p)} = RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [← hmap]; exact hker.symm
  refine ⟨(Ideal.quotEquivOfEq h1).trans
    ((RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (pI p)).toRingHom) hsurj).trans
      ((Ideal.quotEquivOfEq (ker_lauRed p).symm).trans
        (RingHom.quotientKerEquivOfSurjective (lauRed_surjective p)))), ?_⟩
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hq : (AdicCompletion.evalOneₐ (pI p)).toRingHom (qO p) =
      Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) :=
    (AdicCompletion.evalOneₐ (pI p)).commutes _
  rw [hq, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  ext n
  rw [lauRed_coeff]
  by_cases hn : n = 1
  · subst hn; simp
  · simp [HahnSeries.coeff_single_of_ne hn]

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGammaOneOfNebentypusCuspidal
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_of_chiInv : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N →
    CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  intro N k χ G _ hC hχ
  refine ⟨{ toFun := G
            slash_action_eq' := fun A hA => ?_
            holo' := hC.1
            zero_at_cusps' := fun {c} hc => hC.2 c (hc.mono ?_) }, rfl⟩
  · obtain ⟨A, hA, rfl⟩ := hA
    have hA0 : A ∈ Gamma0 N := Gamma1_in_Gamma0 N hA
    have h11 : ((mat A 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N A).1 hA).2.1
    have := hχ A hA0
    rw [h11, map_one, one_smul, ModularForm.SL_slash] at this
    exact this
  · rintro _ ⟨γ, -, rfl⟩; exact ⟨γ, rfl⟩
end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationExtendPadicLaurentToClosure
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerExt

theorem exists_extend_of_formallySmooth {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r, D' (algebraMap R S r) = algebraMap R S (D r) := by
  let g : R →+* TrivSqZeroExt S S :=
    { toFun := fun r ↦ TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r))
      map_one' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_one,
            map_one, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one,
            Derivation.map_one_eq_zero, map_zero, zero_add]
      map_mul' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_mul,
            map_mul, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul,
            TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, Derivation.leibniz,
            smul_eq_mul, map_add, map_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, zero_add, add_zero]
          ring
      map_zero' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_zero,
            map_zero, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero,
            map_zero, zero_add]
      map_add' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, map_add (f := _), add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add (f := _), zero_add] }
  have hg : ∀ r, (g r).fst = algebraMap R S r ∧ (g r).snd = algebraMap R S (D r) := fun r ↦ by
    constructor
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).fst = _
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).snd = _
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  obtain ⟨l, h1, h2⟩ : ∃ l : S →+* TrivSqZeroExt S S, (∀ s, (l s).fst = s) ∧ ∀ r, l (algebraMap R S r) = g r := by
    letI : Algebra R (TrivSqZeroExt S S) := g.toAlgebra
    let π : TrivSqZeroExt S S →ₐ[R] S :=
      { (TrivSqZeroExt.fstHom S S S).toRingHom with commutes' := fun r ↦ (hg r).1 }
    have hs : Function.Surjective π := fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩
    have hk : IsNilpotent (RingHom.ker (π : TrivSqZeroExt S S →+* S)) := by
      refine ⟨2, ?_⟩
      rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [RingHom.mem_ker] at hx hy
      change x.fst = 0 at hx
      change y.fst = 0 at hy
      rw [Ideal.mem_bot]
      ext
      · simp [hx]
      · simp [TrivSqZeroExt.snd_mul, hx, hy]
    let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) π hs hk
    exact ⟨l, fun s ↦ AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R S) π hs hk) s,
      fun r ↦ l.commutes r⟩
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s ↦ (l s).snd, map_zero' := by simp, map_add' := fun x y ↦ by rw [map_add (f := _)]; rfl }) fun a b ↦ ?_,
    fun r ↦ ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h1, h1]
    simp [mul_comm]
  · change (l _).snd = _
    rw [h2, (hg r).2]

theorem derivation_extend : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ D : Derivation ℤ (O0 p) (O0 p),
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) := by
  intro p _ Ω _ _ h D
  haveI : IsDomain (O0 p) := h.inj.isDomain _
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = IsFractionRing.lift h.inj (algebraMap (O0 p) K x)
    rw [IsFractionRing.lift_algebraMap]
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : Algebra.IsSeparable K Ω := Algebra.IsSeparable.of_integral K Ω
  haveI : Algebra.FormallyEtale K Ω := Algebra.FormallyEtale.of_isSeparable K Ω
  haveI : Algebra.FormallySmooth (O0 p) K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (O0 p))
  haveI : Algebra.FormallySmooth (O0 p) Ω := Algebra.FormallySmooth.comp (O0 p) K Ω
  exact exists_extend_of_formallySmooth D

end GlobalTheory.K5.DerExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatible
section
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem isDerOn_iSup_glue (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B : ℕ → Subalgebra A S) (hB : Monotone B) (D : ℕ → S → M)
    (hDer : ∀ m, IsDerOn (B m) (D m)) (hcomp : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) :
    ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  classical
  have hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro x _; rfl
    | succ k hmk ih =>
      intro x hx
      rw [hcomp k x (hB hmk hx), ih x hx]
  let D' : S → M := fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0
  have hD' : ∀ m, ∀ x ∈ B m, D' x = D m x := by
    intro m x hx
    have h : ∃ m, x ∈ B m := ⟨m, hx⟩
    simp only [D', dif_pos h]
    exact (hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm
  have hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m := fun x hx =>
    by
    have := hx
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion] at this
    exact this
  refine ⟨D', ⟨?_, ?_, ?_⟩, hD'⟩
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']
  · intro a
    rw [hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspFormsStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_oddFrame_cuspForms : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0) → ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧ ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | exact GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | (intros; apply GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCuspsStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps : ∀ (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ), IsMF Γ K H → (∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) → ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  first | exact @GlobalTheory.exists_eq_discriminant_mul | exact GlobalTheory.exists_eq_discriminant_mul | (intros; apply GlobalTheory.exists_eq_discriminant_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixingStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (S : Finset L), (∀ s ∈ S, (MulAction.orbit G s).Finite) → ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧ ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | exact GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | (intros; apply GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing <;> assumption)
end

