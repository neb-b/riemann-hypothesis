module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasis
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl


set_option maxHeartbeats 2000000 in
theorem decompletion_matrix (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL)
    (E : EtSit P AI K s LL h W) (H : Set (GQ l))
    (hH : ∀ g, g ∈ H ↔ ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1)
    (d : ℕ) (Pm : Matrix (Fin d) (Fin d) W.EE) :
    (∀ y : Fin d → RW LL, (∀ i, y i ∈ fixSub AI LL H) → ∃ z : Fin d → RW LL,
      (∀ i, z i ∈ fixSub AI LL H) ∧
        ∀ i, ∃ e, y i - (∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i) = E.tie.ioE e) ∧
    (∀ z : Fin d → RW LL, (∀ i, z i ∈ fixSub AI LL H) →
      (∀ i, ∃ e, ∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i = E.tie.ioE e) →
        ∀ i, ∃ e, z i = E.tie.ioE e) := by
  obtain ⟨c1, c2, c3, c4⟩ := _root_.GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E
  obtain ⟨f1, f2, f3⟩ := _root_.GlobalTheory.Decompl.FixL.fixSub_ladic l P AI LL H
  obtain ⟨p1, p2, -, -⟩ := _root_.GlobalTheory.DecomplFrob.frobenius_and_constants l P AI LL s
  obtain ⟨s1, s2⟩ := _root_.GlobalTheory.Decompl.Sat.ioE_saturated_closed l P AI K s LL h W E
  have hE : ∀ e, E.tie.ioE e ∈ fixSub AI LL H := fun e => mem_fixSub.2 fun g hg => by
    obtain ⟨hg, hg1⟩ := (hH g).1 hg
    exact c2 ⟨g, hg⟩ hg1 e
  have hsub : ∀ y ∈ fixSub AI LL H, y ∈ fixSub AI LL (Hinf K : Set (GQ l)) := fun y hy =>
    mem_fixSub.2 fun g hg => mem_fixSub.1 hy g
      ((hH g).2 ((GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).2 s LL h W g hg))
  have hπ : piR AI LL s ∈ fixSub AI LL H := by rw [← c3]; exact hE _
  have q1 := _root_.GlobalTheory.Decompl.fixSub_nearPi_complete l P AI LL s H hπ
  have q2 := _root_.GlobalTheory.Decompl.ioE_closed l P AI K s LL h W E
  have q3 := fun y hy => GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection l P AI K s LL h W E y (hsub y hy)
  have q4 := _root_.GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective (RW LL) W.EE (RA LL) (E.tie.ioE : W.EE →+* RW LL) (inclR LL : RA LL →+* RW LL)
    (φRW LL : RW LL →+* RW LL) (fixSub AI LL H) l (piR AI LL s)
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
  simp only [RingHom.coe_coe] at q4
  have q5 := q4 hE f2 (fun e => ⟨W.φE e, (c1 e).symm⟩) p1 p2 c4 f1 s1
  have q6 := q5 q1 q2 q3
  exact q6 f3 s2 d Pm

theorem decompletion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; DecW S E := by
  intro D HW F l _ K s LL h S E
  refine GlobalTheory.T.decW_of_matrix_criterion S E fun d Pm => ?_
  have hm := decompletion_matrix l (D.loc l) (D.locA l) K s LL h ((HW l).W K s LL h)
    ((F l).E K s LL h) {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1}
    (fun _ => Iff.rfl) d Pm
  have hf : ∀ x : RW LL, x ∈ fixSub (D.locA l) LL
      {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1} ↔
      ∀ g ∈ Hker S, S.gR g x = x := fun x =>
    mem_fixSub.trans ⟨fun hx g hg => hx g.1 ⟨g.2, hg⟩, fun hx g ⟨hg, hg1⟩ => hx ⟨g, hg⟩ hg1⟩
  refine ⟨fun y hy => ?_, fun z hz => hm.2 z fun i => (hf _).2 (hz i)⟩
  obtain ⟨z, hz, hz'⟩ := hm.1 y fun i => (hf _).2 (hy i)
  exact ⟨z, fun i => (hf _).1 (hz i), hz'⟩

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EnvLevel

theorem mem_smul_top_of_mem_map_C {R : Type} [CommRing R] (I : Ideal R) (p : MvPolynomial ℕ R)
    (hp : p ∈ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ℕ R) I) :
    p ∈ I • (⊤ : Submodule R (MvPolynomial ℕ R)) := by
  rw [MvPolynomial.mem_map_C_iff] at hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ fun s _ => ?_
  have : MvPolynomial.monomial s (p.coeff s) = p.coeff s • MvPolynomial.monomial s (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hp s) Submodule.mem_top

theorem tri_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (l i : ℕ) (v : Aˣ)
    (a b : MvPolynomial ℕ A)
    (ha : a ∈ MvPolynomial.supported A (Set.Iio i)) (hb : b ∈ MvPolynomial.supported A (Set.Iio i)) :
    ∃ (v' : Rˣ) (a' b' : MvPolynomial ℕ R), a' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      b' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      MvPolynomial.map f (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) =
        MvPolynomial.C (v' : R) * MvPolynomial.X i ^ l + a' * MvPolynomial.X i + b' := by
  refine ⟨Units.map f.toMonoidHom v, MvPolynomial.map f a, MvPolynomial.map f b, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported] at ha ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map a f)).trans ha
  · rw [MvPolynomial.mem_supported] at hb ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map b f)).trans hb
  · simp [map_add (f := _), map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]

end GlobalTheory.EnvLevel

theorem GlobalTheory.digitMonomials_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  intro l _ A _ J r hr n
  classical
  let π : MvPolynomial ℕ A →+* MvPolynomial ℕ (A ⧸ J ^ n) := MvPolynomial.map (Ideal.Quotient.mk (J ^ n))
  have hπs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    simp only [π]; rw [MvPolynomial.ker_map, Ideal.mk_ker]
  let I : Ideal (A ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n))
  have hIn : I ^ n = ⊥ := by
    simp only [I]; rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  choose v a b ha hb hrab using hr
  let t : ℕ → MvPolynomial ℕ (A ⧸ J ^ n) := fun i =>
    π (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)
  have ht := fun i => GlobalTheory.EnvLevel.tri_map (Ideal.Quotient.mk (J ^ n)) l i (v i) (a i) (b i) (ha i) (hb i)
  obtain ⟨htli, htsp⟩ := _root_.GlobalTheory.TriBasis.tri_basis l (A ⧸ J ^ n) t ht
  let B : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ (A ⧸ J ^ n) := fun x =>
    MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => π (r i) ^ m
  have hK : ∀ i, π (r i) - t i ∈ Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I := by
    intro i
    have h1 : π (r i) - t i = π (r i - (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)) := by
      simp only [t, map_sub]
    have h2 : Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I =
        Ideal.map π (J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) := by
      simp only [I, π]
      rw [Ideal.map_map, Ideal.map_map, MvPolynomial.map_comp_C]
    rw [h1, h2]
    exact Ideal.mem_map_of_mem _ (hrab i)
  have hBK : ∀ x, B x - (MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => t i ^ m) ∈
      I • (⊤ : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n))) := by
    intro x
    apply GlobalTheory.EnvLevel.mem_smul_top_of_mem_map_C
    rw [← Ideal.Quotient.eq]
    simp only [B, map_mul, Finsupp.prod, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq.mpr (hK i)]
  obtain ⟨hBli, hBsp⟩ := _root_.GlobalTheory.BSP.family_congr_basis_mod_nilpotent (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) (Digits l × (ℕ →₀ ℕ))
    _ B I n hIn htli htsp hBK
  have hBmem : ∀ k : Digits l × (ℕ →₀ ℕ), k.2 ≠ 0 → B k ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
    intro k hk
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hk
    apply Ideal.mul_mem_left
    have hd : π (r i) ^ k.2 i ∣ k.2.prod fun i m => π (r i) ^ m :=
      Finset.dvd_prod_of_mem (fun i => π (r i) ^ k.2 i) hi
    obtain ⟨d, hd⟩ := hd
    rw [hd]
    apply Ideal.mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self (f := ⇑π ∘ r) i)) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  let S : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) :=
    Submodule.span (A ⧸ J ^ n) (B '' {x | x.2 ≠ 0})
  have hmulS : ∀ i (p : MvPolynomial ℕ (A ⧸ J ^ n)), p * π (r i) ∈ S := by
    intro i p
    have hp : p ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : B k * π (r i) = B (k.1, k.2 + Finsupp.single i 1) := by
        simp only [B]
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp)]
        simp only [pow_one, mul_assoc]
      rw [this]
      refine Submodule.subset_span ⟨(k.1, k.2 + Finsupp.single i 1), ?_, rfl⟩
      intro h
      have := DFunLike.congr_fun h i
      simp at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hspanS : ∀ x ∈ Ideal.span (Set.range (⇑π ∘ r)), ∀ p, p * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact fun p => hmulS i p
    | zero => intro p; simp
    | add y z _ _ hy hz => intro p; rw [mul_add]; exact S.add_mem (hy p) (hz p)
    | smul c y _ hy => intro p; rw [smul_eq_mul, ← mul_assoc]; exact hy (p * c)
  refine ⟨?_, ?_⟩
  · intro x
    have hx : π x ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    let f0 := f.filter fun k => k.2 = 0
    let f1 := f.filter fun k => ¬ k.2 = 0
    let g : Digits l →₀ (A ⧸ J ^ n) := f0.mapDomain Prod.fst
    have hsplit : π x = (f0.sum fun k a => a • B k) + (f1.sum fun k a => a • B k) := by
      rw [← hf, ← Finsupp.sum_add_index' (h := fun k a => a • B k) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _)]
      simp only [f0, f1]
      rw [Finsupp.filter_add_filter_not]
    have h0sum : (f0.sum fun k a => a • B k) = g.sum fun α a => MvPolynomial.monomial α.1 a := by
      simp only [g]
      rw [Finsupp.sum_mapDomain_index (h := fun (α : Digits l) (a : A ⧸ J ^ n) => MvPolynomial.monomial α.1 a)
        (fun (α : Digits l) => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_zero)
        (fun (α : Digits l) _ _ => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_add _ _)]
      refine Finsupp.sum_congr fun k hk => ?_
      have hk2 : k.2 = 0 := by
        simp only [f0] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      simp only [B, hk2, Finsupp.prod_zero_index, mul_one, MvPolynomial.smul_monomial, smul_eq_mul]
    have h1mem : (f1.sum fun k a => a • B k) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      unfold Finsupp.sum
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk2 : k.2 ≠ 0 := by
        simp only [f1] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      show f1 k • B k ∈ _
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (hBmem k hk2)
    let sec : (A ⧸ J ^ n) → A := fun y =>
      if y = 0 then 0 else Function.surjInv (Ideal.Quotient.mk_surjective (I := J ^ n)) y
    have hsec0 : sec 0 = 0 := by simp [sec]
    have hsec : ∀ y, Ideal.Quotient.mk (J ^ n) (sec y) = y := by
      intro y
      by_cases h : y = 0
      · simp [sec, h]
      · simp only [sec, h, if_false]; exact Function.surjInv_eq _ y
    refine ⟨g.mapRange sec hsec0, ?_⟩
    have hmap : π ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) =
        g.sum fun α a => MvPolynomial.monomial α.1 a := by
      rw [map_finsuppSum, Finsupp.sum_mapRange_index (h := fun (α : Digits l) (a : A) => π (MvPolynomial.monomial α.1 a))
        (fun _ => by simp)]
      simp only [π, MvPolynomial.map_monomial, hsec]
    have hmem : x - ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) ∈
        Ideal.comap π (Ideal.map π (Ideal.span (Set.range r))) := by
      rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, map_sub, hmap, hsplit, ← h0sum,
        add_sub_cancel_left]
      exact h1mem
    rwa [Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot, hker] at hmem
  · intro c hc α
    have h1 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      have := Ideal.mem_map_of_mem π hc
      rwa [Ideal.map_sup, ← hker, (Ideal.map_eq_bot_iff_le_ker π).mpr le_rfl, sup_bot_eq, Ideal.map_span,
        ← Set.range_comp] at this
    have h2 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ S := by
      simpa using hspanS _ h1 1
    have hinj : Function.Injective (fun α : Digits l => (α, (0 : ℕ →₀ ℕ))) :=
      fun _ _ h => congrArg Prod.fst h
    let g' : Digits l × (ℕ →₀ ℕ) →₀ (A ⧸ J ^ n) :=
      Finsupp.mapDomain (fun α => (α, (0 : ℕ →₀ ℕ))) (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _))
    have hg' : Finsupp.linearCombination (A ⧸ J ^ n) B g' = π (c.sum fun α a => MvPolynomial.monomial α.1 a) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a => a • (B ∘ fun α => (α, (0 : ℕ →₀ ℕ))) i)
          (fun _ => zero_smul _ _), map_finsuppSum]
      refine Finsupp.sum_congr fun β _ => ?_
      simp [B, π, MvPolynomial.smul_monomial]
    obtain ⟨l', hl', hl'eq⟩ := (Finsupp.mem_span_image_iff_linearCombination (A ⧸ J ^ n)).mp h2
    have hl : l' = g' := hBli (hl'eq.trans hg'.symm)
    have h3 : g' (α, 0) = 0 := by
      rw [← hl]; exact (Finsupp.mem_supported' (A ⧸ J ^ n) l').mp hl' _ (by simp)
    have h4 : g' (α, 0) = Ideal.Quotient.mk (J ^ n) (c α) :=
      Finsupp.mapDomain_apply_of_injective hinj (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _)) α
    rw [h4] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormula
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem exists_inv_pow_one_add {l : ℕ} [Fact l.Prime] {s : ℕ} (hs : 1 ≤ s) (e : ℕ) (u : ℚ_[l]ˣ)
    (hu : (u : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l])) :
    ∃ U : ℤ_[l], (U : ℚ_[l]) = ((u ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) ∧ (l : ℤ_[l]) ^ s ∣ U - 1 := by
  have hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l] := by
    rw [PadicInt.mem_nonunits, norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
  obtain ⟨V, hV⟩ := hunit.exists_left_inv
  refine ⟨V ^ e, ?_, ?_⟩
  · have h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1 := by
      have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV
      rw [hu]
      push_cast at this ⊢
      linear_combination this
    have h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹ := eq_inv_of_mul_eq_one_left h1
    simp [h2]
  · have h1 : (l : ℤ_[l]) ^ s ∣ V - 1 := ⟨-V, by linear_combination hV⟩
    have h2 := sub_dvd_pow_sub_pow V 1 e
    rw [one_pow] at h2
    exact h1.trans h2

theorem zetaQ_pow_level {l : ℕ} [Fact l.Prime] (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem levSum_mem_Ks {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type}
    (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ↥(K0 K)) :
    levSum P K s j T c m d ∈ Ks K s := by
  have h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s := fun x => (le_sup_left : K0 K ≤ Ks K s) x.2
  have hζ : P.ζQ s ∈ Ks K s := by
    refine (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)
    exact zetaQ_pow_level P s
  unfold levSum
  refine add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ =>
    mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _)))
    (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))

theorem expStar_levSum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  intro LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd
  classical
  obtain ⟨U, hU, hU1⟩ := exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ
  have hgen : IsGen (LT l).χQ K s g := by
    refine ⟨hg, ?_⟩
    rw [hχ]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨w, hw⟩ := _root_.GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l (LT l) AI hT K (c i) (hc i hi).1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨y, hy, hexp⟩ := _root_.GlobalTheory.ExpImage.Expand.expand l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw
    (fun j hj => hd j (by omega))
  have hsolv : Solv AI K s g U (y - WittVector.frobenius y) := by
    rw [hy]
    refine Solv.sum T _ fun i hi => ?_
    exact (_root_.GlobalTheory.ExpImage.EpsSolve.main l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul
      ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))
  obtain ⟨b, hb0, hbH, z₀, hz₀⟩ := _root_.GlobalTheory.ExpImage.Sum.main l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv
  obtain ⟨z, hz, hE⟩ := _root_.GlobalTheory.ExpImage.LowTerms.expStar_of_sum LT l AI hT K s hs e g hgen
    (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
      levSum (LT l) K s j T c m (d j))
    (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _))
    b hb0 hbH ⟨z₀, by
      have := add_mem hz₀ hexp
      rw [hU] at this
      convert this using 1
      ring⟩
  refine ⟨z, hz, ?_⟩
  rw [hχ, ← mul_assoc, ← map_mul, ← mul_inv] at hE
  exact hE

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowDvdOfBdRPlusDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DivTransfer

theorem div_transfer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), aDp l (bk.ev bk.E) ≠ 0 ∧
    ∀ (m : ℕ) (s : bk.S), aDp l (bk.ev bk.E) ^ m ∣ aDp l (bk.ev s) → bk.E ^ m ∣ s := by
  intro l _ K bk

  have hF := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1
  have hS := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.1
  refine ⟨fun h0 => ?_, fun m s hd => ?_⟩
  · have h2 : bk.ev bk.E ^ 2 ∣ bk.ev bk.E := (hF 2 (bk.ev bk.E)).1 (by rw [h0]; exact Ideal.zero_mem _)
    obtain ⟨c, hc⟩ := hS 2 bk.E h2
    have h1 : bk.E * 1 = bk.E * (bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have hu : bk.E * c = 1 := (mul_left_cancel₀ bk.E_ne_zero h1).symm
    have hmem : (1 : Ainf l) ∈ RingHom.ker (Per.θ l) := by
      rw [← bk.span_ev, ← map_one bk.ev, ← hu, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [RingHom.mem_ker, map_one] at hmem
    exact one_ne_zero hmem
  · apply hS m s
    apply (hF m _).1
    obtain ⟨c, hc⟩ := hd
    rw [hc, ← map_pow, ← map_pow]
    exact Ideal.mul_mem_right _ _ ((hF m _).2 (by rw [map_pow]))

end GlobalTheory.BSP.DivTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBasesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases : ∀ (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι), m k₀ = 1 → IsAdicComplete J A → IsCompl i (J.map s) → (∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s) → (∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) → ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_levels | exact GlobalTheory.BSP.exists_topBasis_of_levels | (intros; apply GlobalTheory.BSP.exists_topBasis_of_levels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AinfRetraction

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  refine ⟨TB.c TB.i₀, TB.c_mul TB.i₀, ?_⟩
  rw [← TB.b_i₀]
  exact TB.c_self TB.i₀

end GlobalTheory.BKLim.AinfRetraction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_integral_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  first | exact @GlobalTheory.CycIntegral.cyc_lattice | exact GlobalTheory.CycIntegral.cyc_lattice | (intros; apply GlobalTheory.CycIntegral.cyc_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalizationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_localization : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (M : Submonoid A), (∀ x ∈ M, D.φ x ∈ M) → ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  first | exact @GlobalTheory.BSP.delta_localization | exact GlobalTheory.BSP.delta_localization | (intros; apply GlobalTheory.BSP.delta_localization <;> assumption)
end

