module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHom
section
namespace GlobalTheory.ValExt

theorem ker_isMaximal (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) : (RingHom.ker h).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp, fun J a hJ ha haJ => ?_⟩
  have ha' : h a ≠ 0 := fun e => ha (RingHom.mem_ker.2 e)
  have hinv := hloc a ha'
  have ha0 : (a : Ω) ≠ 0 := fun e => ha' (by rw [show a = 0 from Subtype.ext e, map_zero])
  have : (1 : A) = ⟨(a : Ω)⁻¹, hinv⟩ * a := Subtype.ext (by simp [inv_mul_cancel₀ ha0])
  rw [this]
  exact J.mul_mem_left _ haJ

theorem exists_ext_local (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k) :
    ∃ (B : Subring Ω) (hAB : A ≤ B) (h' : B →+* k), (∀ b : B, h' b ≠ 0 → (b : Ω)⁻¹ ∈ B) ∧
      ∀ a : A, h' (Subring.inclusion hAB a) = h a := by
  let p := RingHom.ker h
  haveI : p.IsPrime := RingHom.ker_isPrime h
  let L := Localization.AtPrime p
  have hs : ∀ s : p.primeCompl, h s ≠ 0 := fun s e => s.2 (RingHom.mem_ker.2 e)
  have hs' : ∀ s : p.primeCompl, ((s : A) : Ω) ≠ 0 := fun s e =>
    hs s (by rw [show (s : A) = 0 from Subtype.ext e, map_zero])
  let ι : L →+* Ω := IsLocalization.lift (M := p.primeCompl) (g := A.subtype) (fun s => (hs' s).isUnit)
  let hL : L →+* k := IsLocalization.lift (M := p.primeCompl) (g := h) (fun s => (hs s).isUnit)
  have hι : ∀ a : A, ι (algebraMap A L a) = a := fun a => IsLocalization.lift_eq _ _
  have hhL : ∀ a : A, hL (algebraMap A L a) = h a := fun a => IsLocalization.lift_eq _ _
  have hmk : ∀ (a : A) (s : p.primeCompl), ι (IsLocalization.mk' L a s) * ((s : A) : Ω) = a := by
    intro a s
    rw [← hι, ← map_mul, IsLocalization.mk'_spec, hι]
  have hmkL : ∀ (a : A) (s : p.primeCompl), hL (IsLocalization.mk' L a s) * h s = h a := by
    intro a s
    rw [← hhL, ← map_mul, IsLocalization.mk'_spec, hhL]
  have hinj : Function.Injective ι := by
    intro z z' e
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨⟨a', s'⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z'
    rw [IsLocalization.mk'_eq_iff_eq]
    congr 1
    apply Subtype.ext
    have h1 := hmk a s
    have h2 := hmk a' s'
    simp only [Subring.coe_mul]
    rw [← h1, ← h2, e]
    ring
  let B : Subring Ω := ι.range
  let e : L ≃+* B := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b e' => hinj (congrArg Subtype.val e'), ι.rangeRestrict_surjective⟩
  have hAB : A ≤ B := fun a ha => ⟨algebraMap A L ⟨a, ha⟩, hι _⟩
  refine ⟨B, hAB, hL.comp e.symm.toRingHom, fun b hb => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z, e z = b := e.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at hb
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have ha : h a ≠ 0 := fun e0 => hb (by
      have := hmkL a s
      rw [e0] at this
      exact (mul_eq_zero.1 this).resolve_right (hs s))
    let t : p.primeCompl := ⟨a, fun e0 => ha (RingHom.mem_ker.1 e0)⟩
    refine ⟨IsLocalization.mk' L (s : A) t, ?_⟩
    show ι _ = (ι (IsLocalization.mk' L a s))⁻¹
    have h1 := hmk a s
    have h2 := hmk (s : A) t
    have ha0 : ((a : A) : Ω) ≠ 0 := hs' t
    apply eq_inv_of_mul_eq_one_left
    have : ι (IsLocalization.mk' L (s : A) t) * ι (IsLocalization.mk' L a s) * (((a : A) : Ω) * ((s : A) : Ω)) =
        1 * (((a : A) : Ω) * ((s : A) : Ω)) := by
      calc _ = (ι (IsLocalization.mk' L (s : A) t) * ((t : A) : Ω)) * (ι (IsLocalization.mk' L a s) * ((s : A) : Ω)) := by
              simp only [t]; ring
        _ = _ := by rw [h1, h2]; ring
    exact mul_right_cancel₀ (mul_ne_zero ha0 (hs' s)) this
  · have : e.symm (Subring.inclusion hAB a) = algebraMap A L a := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      exact Subtype.ext (hι a).symm
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this, hhL]

theorem exists_ext_adjoin (Ω k : Type) [Field Ω] [Field k] [IsAlgClosed k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) (y : Ω) (M : Ideal (Algebra.adjoin A {y})) [M.IsMaximal]
    (hM : RingHom.ker h ≤ M.comap (algebraMap A (Algebra.adjoin A {y}))) :
    ∃ h' : Algebra.adjoin A {y} →+* k, ∀ a : A, h' (algebraMap A _ a) = h a := by
  haveI := ker_isMaximal Ω k A h hloc
  let K₀ := A ⧸ RingHom.ker h
  let K₁ := (Algebra.adjoin A {y}) ⧸ M
  letI : Field K₁ := Ideal.Quotient.field M
  letI : Field K₀ := Ideal.Quotient.field _
  let f₀ : K₀ →+* K₁ := Ideal.quotientMap M (algebraMap A (Algebra.adjoin A {y})) hM
  letI : Algebra K₀ K₁ := f₀.toAlgebra
  let hb : K₀ →+* k := Ideal.Quotient.lift (RingHom.ker h) h (fun a ha => ha)
  letI : Algebra K₀ k := hb.toAlgebra
  haveI : IsScalarTower A K₀ K₁ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (Algebra.adjoin A {y}) := .adjoin_of_finite (Set.finite_singleton y)
  haveI : Algebra.FiniteType A K₁ :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType K₀ K₁ := Algebra.FiniteType.of_restrictScalars_finiteType A K₀ K₁
  haveI : Module.Finite K₀ K₁ := finite_of_finite_type_of_isJacobsonRing K₀ K₁
  haveI : Algebra.IsIntegral K₀ K₁ := Algebra.IsIntegral.of_finite K₀ K₁
  haveI : Module.IsTorsionFree K₀ K₁ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree K₀ k := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic K₀ K₁ := Algebra.IsIntegral.isAlgebraic
  let L : K₁ →ₐ[K₀] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  have e1 : Ideal.Quotient.mk M (algebraMap A (Algebra.adjoin A {y}) a) = algebraMap K₀ K₁ (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, L.commutes]
  rfl

theorem dichotomy (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) (x : Ω) (hx : x ≠ 0) :
    ∃ y : Ω, (y = x ∨ y = x⁻¹) ∧ ∃ M : Ideal (Algebra.adjoin A {y}), M.IsMaximal ∧
      RingHom.ker h ≤ M.comap (algebraMap A (Algebra.adjoin A {y})) := by
  have hmax : (RingHom.ker h).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp, fun J a hJ ha haJ => ?_⟩
    have ha' : h a ≠ 0 := fun e => ha (RingHom.mem_ker.2 e)
    have hinv := hloc a ha'
    have ha0 : (a : Ω) ≠ 0 := fun e => ha' (by rw [show a = 0 from Subtype.ext e, map_zero])
    have : (1 : A) = ⟨(a : Ω)⁻¹, hinv⟩ * a := Subtype.ext (by simp [inv_mul_cancel₀ ha0])
    rw [this]
    exact J.mul_mem_left _ haJ
  by_cases hT : (RingHom.ker h).map (algebraMap A (Algebra.adjoin A {x})) = ⊤
  · letI := invertibleOfNonzero hx
    have htop : (RingHom.ker h).map (algebraMap A (Algebra.adjoin A {x})) ⊔
        Ideal.span {⟨x, Algebra.subset_adjoin rfl⟩} = ⊤ := by rw [hT]; exact top_sup_eq _
    obtain ⟨p, hp, hpx⟩ :=
      Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _ hmax.ne_top htop
    have hlc : h p.leadingCoeff ≠ 0 := by
      intro e
      have h1 := sub_mem (RingHom.mem_ker.2 e) hp
      simp only [sub_sub_cancel] at h1
      exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hu : IsUnit p.leadingCoeff := by
      have hinv := hloc _ hlc
      have h0 : (p.leadingCoeff : Ω) ≠ 0 := fun e => hlc (by
        rw [show p.leadingCoeff = 0 from Subtype.ext e, map_zero])
      exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : A) (Subtype.ext (by simp [mul_inv_cancel₀ h0]))
    have hint : IsIntegral A x⁻¹ := by
      refine ⟨Polynomial.C (hu.unit⁻¹ : Aˣ).1 * p, ?_, ?_⟩
      · exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by simp)
      · rw [← Polynomial.aeval_def, map_mul]
        rw [invOf_eq_inv] at hpx
        rw [hpx, mul_zero]
    haveI : Algebra.IsIntegral A (Algebra.adjoin A {x⁻¹}) := Algebra.IsIntegral.adjoin (by simpa using hint)
    have hker : RingHom.ker (algebraMap A (Algebra.adjoin A {x⁻¹})) ≤ RingHom.ker h := by
      intro a ha
      have e := congrArg Subtype.val (RingHom.mem_ker.1 ha)
      have : a = 0 := Subtype.ext (by simpa using e)
      rw [this]; exact zero_mem _
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker h) hker
    exact ⟨x⁻¹, Or.inr rfl, Q, hQ, hQc.ge⟩
  · obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hT
    exact ⟨x, Or.inl rfl, M, hM, Ideal.map_le_iff_le_comap.1 hle⟩

theorem exists_valuationSubring_ext : ∀ (W Ω k : Type) [CommRing W] [Field Ω] [Field k] [IsAlgClosed k]
    (j : W →+* Ω), Function.Injective j → ∀ g : W →+* k, ∃ (U : ValuationSubring Ω) (hU : ∀ w, j w ∈ U)
      (h : U →+* k), ∀ w, h ⟨j w, hU w⟩ = g w := by
  intro W Ω k _ _ _ _ j hj g
  let S : Set (Subring (Ω × k)) :=
    {G | (∀ a ∈ G, ∀ b ∈ G, a.1 = b.1 → a.2 = b.2) ∧ ∀ w, (j w, g w) ∈ G}
  have G0 : (RingHom.prod j g).range ∈ S := by
    refine ⟨?_, fun w => ⟨w, rfl⟩⟩
    rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ e
    have : w = w' := hj e
    subst this; rfl
  obtain ⟨G, -, hG⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, fun w => le_sSup hy ((hcS hy).2 w)⟩, fun z hz => le_sSup hz⟩
    intro a ha b hb e
    obtain ⟨s₁, hs₁, ha₁⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 ha
    obtain ⟨s₂, hs₂, hb₂⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 hb
    obtain ⟨s₃, hs₃, h13, h23⟩ := hd s₁ hs₁ s₂ hs₂
    exact (hcS hs₃).1 a (h13 ha₁) b (h23 hb₂) e) _ G0
  obtain ⟨⟨hGf, hGb⟩, hGm⟩ := hG
  let π : G →+* Ω := (RingHom.fst Ω k).comp G.subtype
  have hπ : Function.Injective π := fun p q e =>
    Subtype.ext (Prod.ext e (hGf p.1 p.2 q.1 q.2 e))
  let A : Subring Ω := π.range
  let e : G ≃+* A := RingEquiv.ofBijective π.rangeRestrict
    ⟨fun a b e' => hπ (congrArg Subtype.val e'), π.rangeRestrict_surjective⟩
  let h : A →+* k := ((RingHom.snd Ω k).comp G.subtype).comp e.symm.toRingHom
  have hA : ∀ a : A, ((a : Ω), h a) ∈ G := fun a => by
    have e1 : π (e.symm a) = a := congrArg Subtype.val (e.apply_symm_apply a)
    have : ((a : Ω), h a) = ((e.symm a : G) : Ω × k) := Prod.ext e1.symm rfl
    rw [this]; exact (e.symm a).2
  have hG2 : ∀ p ∈ G, ∃ a : A, (a : Ω) = p.1 ∧ h a = p.2 := fun p hp =>
    ⟨π.rangeRestrict ⟨p, hp⟩, rfl, by
      show ((e.symm (e ⟨p, hp⟩) : G) : Ω × k).2 = p.2
      rw [e.symm_apply_apply]⟩
  have ext_le : ∀ (B : Subring Ω) (hAB : A ≤ B) (h' : B →+* k),
      (∀ a : A, h' (Subring.inclusion hAB a) = h a) → B ≤ A := by
    intro B hAB h' hh' b hb
    let G' : Subring (Ω × k) := (RingHom.prod B.subtype h').range
    have hG' : G' ∈ S := by
      refine ⟨?_, fun w => ?_⟩
      · rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩ e'
        have : b₁ = b₂ := Subtype.ext e'
        subst this; rfl
      · obtain ⟨a, ha1, ha2⟩ := hG2 _ (hGb w)
        refine ⟨Subring.inclusion hAB a, ?_⟩
        exact Prod.ext ha1 ((hh' a).trans ha2)
    have hle : G ≤ G' := fun p hp => by
      obtain ⟨a, ha1, ha2⟩ := hG2 p hp
      exact ⟨Subring.inclusion hAB a, Prod.ext ha1 ((hh' a).trans ha2)⟩
    have hmem : ((b : Ω), h' ⟨b, hb⟩) ∈ G := hGm hG' hle ⟨⟨b, hb⟩, rfl⟩
    exact ⟨⟨_, hmem⟩, rfl⟩
  have hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A := by
    intro a ha
    obtain ⟨B, hAB, h', hB, hh'⟩ := exists_ext_local Ω k A h
    have := hB (Subring.inclusion hAB a) (by rw [hh']; exact ha)
    exact ext_le B hAB h' hh' this
  have hval : ∀ x : Ω, x ∈ A ∨ x⁻¹ ∈ A := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ zero_mem A)
    obtain ⟨y, hy, M, hM, hMc⟩ := dichotomy Ω k A h hloc x hx
    obtain ⟨h', hh'⟩ := exists_ext_adjoin Ω k A h hloc y M hMc
    let B : Subring Ω := (Algebra.adjoin A {y}).toSubring
    have hAB : A ≤ B := fun a ha => (Algebra.adjoin A {y}).algebraMap_mem (⟨a, ha⟩ : A)
    have hyA : y ∈ A := ext_le B hAB h' hh' (Algebra.subset_adjoin rfl)
    rcases hy with rfl | rfl
    · exact Or.inl hyA
    · exact Or.inr hyA
  let U : ValuationSubring Ω := { A with mem_or_inv_mem' := hval }
  have hU : ∀ w, j w ∈ U := fun w => by
    obtain ⟨a, ha1, -⟩ := hG2 _ (hGb w)
    show j w ∈ A
    rw [← show (a : Ω) = j w from ha1]; exact a.2
  refine ⟨U, hU, h.comp (Subring.inclusion (le_refl A)), fun w => ?_⟩
  have m1 := hA ⟨j w, hU w⟩
  exact hGf _ m1 _ (hGb w) rfl

end GlobalTheory.ValExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedHomogenisation
section
open MvPolynomial

namespace GlobalTheory

theorem exists_weightedHomogenisation {L : Type} [Field L] (Q : Subring L) (r : ℕ)
    (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ) (hwt : wt 0 = 1) (hz : (z 0 : L) ≠ 0)
    (P : MvPolynomial (Fin r) Q) :
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  classical
  let d : (Fin r →₀ ℕ) → ℕ := fun α => ∑ i, α i * wt i.succ
  let N : ℕ := P.support.sup d
  let e : (Fin r →₀ ℕ) → (Fin (r + 1) →₀ ℕ) := fun α => Finsupp.cons (N - d α) α
  have he : Function.Injective e := fun a b h => by
    have := congrArg Finsupp.tail h
    simpa [e] using this
  have hd : ∀ α ∈ P.support, d α ≤ N := fun α h => Finset.le_sup (f := d) h
  refine ⟨N, ∑ α ∈ P.support, monomial (e α) (P.coeff α), ?_, ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun α hα => ?_
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ]
    have := hd α hα
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ, hwt, smul_eq_mul, mul_one]
    change N - d α + d α = N
    omega
  · rw [eval₂_eq', Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
    have h1 : (z 0 : L) ^ N = (z 0 : L) ^ (N - d α) * (z 0 : L) ^ d α := by
      rw [← pow_add, Nat.sub_add_cancel (hd α hα)]
    have h2 : (z 0 : L) ^ d α * ∏ i, ((z i.succ : L) / (z 0 : L) ^ wt i.succ) ^ α i
        = ∏ i, (z i.succ : L) ^ α i := by
      simp only [d]
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_comm (α i), pow_mul, ← mul_pow, mul_div_cancel₀ _ (pow_ne_zero _ hz)]
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ]
    push_cast
    rw [h1, ← h2, Subring.coe_subtype]
    ring
  · intro α
    refine ⟨e α, ?_⟩
    rw [coeff_sum]
    simp only [coeff_monomial, he.eq_iff]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.mp h).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjEntriesHasFDerivAtZero
section
namespace GlobalTheory

theorem exp_conj_entries_hasFDerivAt_zero : ∀ (n : ℕ) (ι : Type) [Fintype ι] (A : (ι → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (p : ι → Fin n × Fin n), (∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = A w (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0) ∧ ∀ s : Matrix (Fin n) (Fin n) ℂ, ∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = (s * A w - A w * s) (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (-A w) * s * NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0 := by
  intro n ι _ A p
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ι → ℂ) :=
    { toFun := fun M x => M (p x).1 (p x).2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Ec := LinearMap.toContinuousLinearMap E
  let Ac := LinearMap.toContinuousLinearMap A
  have hA0 : Ac 0 = 0 := map_zero _
  have hnA0 : (-Ac) 0 = 0 := map_zero _
  have h1 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Ac 0) := by
    rw [hA0]; exact hasFDerivAt_exp_zero
  have h1' : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) ((-Ac) 0) := by
    rw [hnA0]; exact hasFDerivAt_exp_zero
  have hexpA : HasFDerivAt (fun w => NormedSpace.exp (Ac w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp Ac) 0 :=
    h1.comp (0 : ι → ℂ) Ac.hasFDerivAt
  have hexpN : HasFDerivAt (fun w => NormedSpace.exp ((-Ac) w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp (-Ac)) 0 :=
    h1'.comp (0 : ι → ℂ) (-Ac).hasFDerivAt
  refine ⟨⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hexpA⟩, fun s => ?_⟩
  · intro w x; rfl
  · have hprod := (hexpN.mul' (hasFDerivAt_const s (0 : ι → ℂ))).mul' hexpA
    refine ⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hprod⟩
    intro w x
    have hA0' : A 0 = 0 := map_zero A
    simp only [Ec, E, Ac, hA0', NormedSpace.exp_zero, Pi.mul_apply, map_zero, neg_zero]
    change ((1 * s) * A w + (1 * 0 + (-(A w)) * s) * 1 : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2 = (s * A w - A w * s) (p x).1 (p x).2
    rw [one_mul, mul_zero, zero_add, mul_one, neg_mul, ← sub_eq_add_neg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpNegLeNormTprodOneSubInv
section
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

theorem exp_neg_le_norm_tprod_one_sub_inv {ι : Type} (x : ι → ℂ) (B : ℝ)
    (h : ∀ a, ‖x a‖ ≤ 1 / 2) (hs : Summable (fun a => ‖x a‖)) (hB : ∑' a, ‖x a‖ ≤ B) :
    Real.exp (-B) ≤ ‖∏' a, (1 - x a)⁻¹‖ := by
  have hlow : ∀ a, 1 / 2 ≤ ‖1 - x a‖ := by
    intro a
    have h1 := norm_sub_norm_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [h a]
  have hne : ∀ a, 1 - x a ≠ 0 := by
    intro a h0
    have := hlow a
    rw [h0, norm_zero] at this
    linarith
  have heq : ∀ a, (1 - x a)⁻¹ = 1 + x a * (1 - x a)⁻¹ := by
    intro a
    have := hne a
    field_simp
    ring
  have hsum : Summable (fun a => ‖x a * (1 - x a)⁻¹‖) := by
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) (hs.mul_right 2)
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_le_comm₀ (by linarith [hlow a]) (by norm_num)]
    linarith [hlow a]
  have hm : Multipliable (fun a => (1 - x a)⁻¹) := by
    have := multipliable_one_add_of_summable hsum
    simpa only [← heq] using this
  have hfac : ∀ a, Real.exp (-‖x a‖) ≤ ‖(1 - x a)⁻¹‖ := by
    intro a
    rw [norm_inv, Real.exp_neg]
    refine inv_anti₀ (by linarith [hlow a]) ?_
    have h1 := norm_sub_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [Real.add_one_le_exp ‖x a‖]
  have ht := (continuous_norm.tendsto _).comp hm.hasProd
  refine ge_of_tendsto' ht (fun s => ?_)
  have hsle : ∑ a ∈ s, ‖x a‖ ≤ B :=
    (hs.sum_le_tsum s (fun a _ => norm_nonneg _)).trans hB
  calc Real.exp (-B) ≤ Real.exp (∑ a ∈ s, -‖x a‖) := by
        rw [Finset.sum_neg_distrib]
        exact Real.exp_le_exp.2 (neg_le_neg hsle)
    _ = ∏ a ∈ s, Real.exp (-‖x a‖) := Real.exp_sum _ _
    _ ≤ ∏ a ∈ s, ‖(1 - x a)⁻¹‖ :=
        Finset.prod_le_prod₀ (fun a _ => (Real.exp_pos _).le) (fun a _ => hfac a)
    _ = _ := by simp only [Function.comp, norm_prod]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAlgHomAdjoinIntegralRoot
section
namespace GlobalTheory

open Polynomial

theorem extend_alg_hom_adjoin_integral_root :
    ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ →
    ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 →
    ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω,
      ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))),
        ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  intro k F Ω _ _ _ _ _ R _ θ hθ ev r hr
  let S : Subalgebra R F := Algebra.adjoin R {θ}
  let e : AdjoinRoot (minpoly R θ) ≃ₐ[R] S := minpoly.equivAdjoin hθ
  let φ : S →+* Ω := (AdjoinRoot.lift (ev : R →+* Ω) r hr).comp (e.symm : S →+* AdjoinRoot (minpoly R θ))
  have hφ : ∀ (x : F) (hx : x ∈ R) (hxS : x ∈ S), φ ⟨x, hxS⟩ = ev ⟨x, hx⟩ := by
    intro x hx hxS
    have h1 : (⟨x, hxS⟩ : S) = algebraMap R S ⟨x, hx⟩ := rfl
    simp only [φ, RingHom.comp_apply, h1]
    rw [show (e.symm : S →+* AdjoinRoot (minpoly R θ)) (algebraMap R S ⟨x, hx⟩)
        = AdjoinRoot.of (minpoly R θ) ⟨x, hx⟩ from e.symm.commutes _]
    exact AdjoinRoot.lift_of hr
  have hle : Algebra.adjoin k (insert θ (R : Set F)) ≤ S.restrictScalars k := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨?_, ?_⟩
    · show θ ∈ S
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro y hy
      show y ∈ S
      exact S.algebraMap_mem (⟨y, hy⟩ : R)
  have hmem : ∀ z : Algebra.adjoin k (insert θ (R : Set F)), (z : F) ∈ S := fun z => hle z.2
  let ψ₀ : Algebra.adjoin k (insert θ (R : Set F)) →+* Ω :=
    { toFun := fun z => φ ⟨z.1, hmem z⟩
      map_one' := φ.map_one
      map_mul' := fun a b => φ.map_mul ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩
      map_zero' := φ.map_zero
      map_add' := fun a b => φ.map_add ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ }
  refine ⟨{ ψ₀ with commutes' := fun c => ?_ }, fun x hx hx' => hφ x hx (hle hx')⟩
  exact (hφ (algebraMap k F c) (R.algebraMap_mem c) _).trans (ev.commutes c)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaloisFractionRingOfIsFractionRing
section
namespace GlobalTheory

theorem _root_.GlobalTheory.finiteGalois_fractionRing_of_isFractionRing :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  intro A K L _ _ _ _ _ _ _ _ _ _ h
  let e : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  letI alg : Algebra (FractionRing A) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hmap : ∀ y : FractionRing A, algebraMap (FractionRing A) L y = algebraMap K L (e y) :=
    fun _ => rfl
  have hcomp : (algebraMap (FractionRing A) L).comp (e.symm.toRingEquiv : K →+* FractionRing A) =
      ((RingEquiv.refl L : L ≃+* L) : L →+* L).comp (algebraMap K L) := by
    ext x; simp [hmap]
  refine ⟨alg, IsScalarTower.of_algebraMap_eq fun a => ?_, ?_, ?_, ?_⟩
  · rw [hmap, AlgEquiv.commutes, h]
  · exact Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp
  · exact IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv) (g := RingEquiv.refl L) hcomp
  · intro σ x
    have := σ.commutes (e.symm x)
    simpa [hmap] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerTail
section
namespace GlobalTheory.AbelianSumIdentityFirst

theorem main : ∀ {ι : Type} {z : ℂ}, z ≠ (0 : ℂ) → ∀ (s : Finset ι) (a : ι → ℤ),
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  intro ι z hz s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hz, ih]

end GlobalTheory.AbelianSumIdentityFirst
end

