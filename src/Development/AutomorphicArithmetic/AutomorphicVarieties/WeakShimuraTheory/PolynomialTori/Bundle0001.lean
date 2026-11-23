module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinPow

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.DimOne
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem pow_le_of_primes {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (I : Ideal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = maximalIdeal B) : ∃ n, maximalIdeal B ^ n ≤ I := by
  have hle : maximalIdeal B ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hIQ, hQ⟩
    rw [h Q hQ hIQ]
  exact Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian _)

theorem UpperTheory.V.Ws.Po.dimOne :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B], ¬ Module.Finite O B →
      ∃ (P : Ideal B) (t : B) (n : ℕ), P.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ P ∧ t ∈ maximalIdeal B ∧ t ∉ P ∧
        maximalIdeal B ^ n ≤ P ⊔ Ideal.span {t} := by
  intro O _ _ _ B _ _ _ hnf
  haveI : IsLocalHom (algebraMap O B) := IsCO.isLocalHom
  have hIm : (maximalIdeal O).map (algebraMap O B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (algebraMap O B) x hx
  have hex : ∃ Q : Ideal B, Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧
      Q ≠ maximalIdeal B := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := pow_le_of_primes _ (fun Q hQ hIQ => hcon Q hQ hIQ)
    exact hnf (UpperTheory.V.Ws.Po.finPow hIm IsCO.res_surj n hn)
  obtain ⟨P, ⟨hP, hIP, hPm⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian B B)
      {Q : Ideal B | Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧ Q ≠ maximalIdeal B} hex
  have hPle : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top
  obtain ⟨t, htm, htP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPle hPm)
  obtain ⟨n, hn⟩ := pow_le_of_primes (P ⊔ Ideal.span {t}) (by
    intro Q hQ hPQ
    by_contra hQm
    have hPQ' : P ≤ Q := le_trans le_sup_left hPQ
    have htQ : t ∈ Q := hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
    exact hmax Q ⟨hQ, hIP.trans hPQ', hQm⟩
      (lt_of_le_of_ne hPQ' (fun e => htP (by rw [e]; exact htQ))))
  exact ⟨P, t, n, hP, hIP, htm, htP, hn⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinExt
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.finExt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (V : ValuationSubring K) (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
      (φ : A →+* B) (f : A →+* V), Function.Injective φ → φ.Finite → Function.Injective f →
      ∃ (y : B →+* V) (s : Finset K), y.comp φ = f ∧ ∀ b, (y b : K) ∈ Subfield.closure (Set.range (V.subtype.comp f) ∪ s) := by
  intro K _ _ V A B _ _ _ _ φ f hφ hfin hf
  classical
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A K := (V.subtype.comp f).toAlgebra
  letI : Algebra A V := f.toAlgebra
  haveI : Module.Finite A B := hfin
  have hfK : Function.Injective (V.subtype.comp f) := Subtype.val_injective.comp hf
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hfK
  haveI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  let y₀ : B →ₐ[A] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hmem : ∀ b, y₀ b ∈ V := by
    intro b
    have h1 : IsIntegral A (y₀ b) := (Algebra.IsIntegral.isIntegral b).map y₀
    have h2 : IsIntegral V (y₀ b) := h1.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    rw [← hz]
    exact z.2
  let y : B →+* V := y₀.toRingHom.codRestrict V hmem
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
  refine ⟨y, Finset.univ.image (fun i => y₀ (g i)), ?_, ?_⟩
  · ext a
    exact y₀.commutes a
  · intro b
    show y₀ b ∈ _
    have hb : b ∈ Submodule.span A (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Subfield.subset_closure
      right
      simp
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x z _ _ hx hz =>
      rw [map_add (f := _)]
      exact add_mem hx hz
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem (Subfield.subset_closure ?_) hx
      left
      exact ⟨a, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.NonAlg
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem fix_mul {V : Type} [Monoid V] {l n : ℕ} {x : V} (h : x ^ l ^ n = x) (m : ℕ) : x ^ l ^ (n * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private theorem fix_both {V : Type} [Monoid V] {l : ℕ} {x z : V} (hx : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x)
    (hz : ∃ n : ℕ, 0 < n ∧ z ^ l ^ n = z) : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x ∧ z ^ l ^ n = z := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hzb⟩ := hz
  refine ⟨a * b, Nat.mul_pos ha hb, fix_mul hxa b, ?_⟩
  rw [Nat.mul_comm]
  exact fix_mul hzb a

theorem UpperTheory.V.Ws.Po.nonAlg :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R]
      (ρ : Γ →* M4 R) (V : Type) [CommRing V] [IsLocalRing V] [CharP V l] (y : R →+* V), (∀ a ∈ maximalIdeal O, y (algebraMap O R a) = 0) →
      ∀ u ∈ Algebra.adjoin O (mono ρ 0), y u ∈ maximalIdeal V → y u ≠ 0 →
      ∃ x ∈ mono (mapRep y ρ) 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro l _ O _ _ _ Γ _ R _ _ ρ V _ _ _ y hy u hu hum hu0
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ Algebra.adjoin O (mono ρ 0), ∃ n : ℕ, 0 < n ∧ (y v) ^ l ^ n = y v := by
    intro v hv
    induction hv using Algebra.adjoin_induction with
    | mem x hx =>
      apply hcon
      obtain ⟨L, hL, rfl⟩ := hx
      refine ⟨L, hL, ?_⟩
      rw [map_list_prod, List.map_map]
      rfl
    | algebraMap r =>
      let g : O →+* V := y.comp (algebraMap O R)
      have hg : ∀ a ∈ maximalIdeal O, g a = 0 := hy
      let f : ResidueField O →+* V := Ideal.Quotient.lift (maximalIdeal O) g hg
      have hf : Function.Injective f := f.injective
      haveI : CharP (ResidueField O) l := f.charP hf l
      letI : Fintype (ResidueField O) := Fintype.ofFinite _
      obtain ⟨m, -, hm⟩ := FiniteField.card (ResidueField O) l
      refine ⟨m, m.pos, ?_⟩
      have h1 : y (algebraMap O R r) = f (IsLocalRing.residue O r) :=
        (Ideal.Quotient.lift_mk (maximalIdeal O) g hg).symm
      rw [h1, ← map_pow, ← hm, FiniteField.pow_card]
    | add x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_add (f := _), add_pow_char_pow, hxn, hzn]⟩
    | mul x z _ _ hx hz =>
      obtain ⟨n, hn, hxn, hzn⟩ := fix_both hx hz
      exact ⟨n, hn, by rw [map_mul, mul_pow, hxn, hzn]⟩
  obtain ⟨n, hn, hun⟩ := key u hu
  obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 + 1 :=
    ⟨l ^ n - 2, by
      have := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
      omega⟩
  apply hu0
  have hmem : y u ^ (k + 1) ∈ maximalIdeal V := Ideal.pow_mem_of_mem _ hum _ (Nat.succ_pos k)
  have hunit : IsUnit (1 - y u ^ (k + 1)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hmem)
  have h0 : y u * (1 - y u ^ (k + 1)) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ', ← hk, hun, sub_self]
  exact hunit.mul_left_eq_zero.mp h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PsFinEv
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.psFin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsDomain B], (∀ a ∈ maximalIdeal O, algebraMap O B a = 0) →
      ∀ t ∈ maximalIdeal B, t ≠ 0 → ∀ n : ℕ, maximalIdeal B ^ n ≤ Ideal.span {t} →
      ∃ φ : PowerSeries (ResidueField O) →+* B, Function.Injective φ ∧ φ.Finite ∧ φ PowerSeries.X = t ∧
        ∀ a : O, φ (PowerSeries.C (residue O a)) = algebraMap O B a := by
  intro O _ _ B _ _ _ _ h0 t ht ht0 n hn
  classical
  let ι : ResidueField O →+* B := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O B) h0
  letI : UniformSpace (ResidueField O) := ⊥
  letI : WithIdeal B := ⟨maximalIdeal B⟩
  have hadic : IsAdic (maximalIdeal B) := rfl
  have hc : CompleteSpace B ∧ T2Space B := hadic.isAdicComplete_iff.mp (IsCO.complete (O := O))
  haveI := hc.1
  haveI := hc.2
  have hcont : Continuous ι := continuous_of_discreteTopology
  have hte : PowerSeries.HasEval t := by
    show Filter.Tendsto (fun m => t ^ m) Filter.atTop (nhds 0)
    rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i] with m hm
    exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ht m)
  let φ := PowerSeries.eval₂Hom hcont hte
  have hφX : φ PowerSeries.X = t := by simp [φ, PowerSeries.coe_eval₂Hom]
  have hφC : ∀ r, φ (PowerSeries.C r) = ι r := by
    intro r
    simp [φ, PowerSeries.coe_eval₂Hom]
  refine ⟨φ, ?_, ?_, hφX, fun a => by rw [hφC]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      exact Ne.isUnit (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)
    have h1 := congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
    rw [map_mul, map_pow, hφX, hf] at h1
    exact mul_ne_zero (pow_ne_zero _ ht0) (hu.map φ).ne_zero h1
  · letI : Algebra (PowerSeries (ResidueField O)) B := φ.toAlgebra
    haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField O))) (PowerSeries (ResidueField O)) := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    have hmap : Ideal.map (algebraMap (PowerSeries (ResidueField O)) B)
        (maximalIdeal (PowerSeries (ResidueField O))) = Ideal.span {t} := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
        RingHom.algebraMap_toAlgebra, hφX]
    show Module.Finite _ _
    refine UpperTheory.V.Ws.Po.finPow ?_ ?_ n ?_
    · rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
      exact ht
    · intro x
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
      exact ⟨PowerSeries.C (residue O a), by rw [RingHom.algebraMap_toAlgebra, hφC]; exact ha⟩
    · rw [hmap]
      exact hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ZmPow
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

section

variable {O : Type} [CommRing O] {Γ : Type} [Group Γ] {R : Type} [CommRing R] [Algebra O R] (ρ : Γ →* M4 R)

private lemma zm_one : (1 : R) ∈ Submodule.span O (mono ρ 0) :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

private lemma zm_mul {v w : ℤ × ℤ} {x y : R} (hx : x ∈ Submodule.span O (mono ρ v))
    (hy : y ∈ Submodule.span O (mono ρ w)) : x * y ∈ Submodule.span O (mono ρ (v + w)) := by
  open scoped Pointwise in
  have hsub : mono ρ v * mono ρ w ⊆ mono ρ (v + w) := by
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨M, hM, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp [hL, hM], by simp⟩
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hsub h

private lemma zm_pow {v : ℤ × ℤ} {x : R} (hx : x ∈ Submodule.span O (mono ρ v)) (k : ℕ) :
    x ^ k ∈ Submodule.span O (mono ρ (k • v)) := by
  induction k with
  | zero => simpa using zm_one (O := O) ρ
  | succ k ih => rw [pow_succ, succ_nsmul]; exact zm_mul ρ ih hx

end

theorem UpperTheory.V.Ws.Po.zMono :
    ∀ (O : Type) [CommRing O] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R] (ρ : Γ →* M4 R) (W : WPres O (ℤ × ℤ) R)
      (c : Γ → Fin 4 → Fin 4 → O), (∀ g a b, a ≠ b → c g a b = 0) →
      (∀ i, ∃ g a b, W.z i = ρ g a b - algebraMap O R (c g a b) ∧ W.wt i = wt a b) →
      ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ Algebra.adjoin O (mono ρ 0) := by
  intro O _ Γ _ R _ _ ρ W c hc hz n hn
  have hmem : ∀ i, W.z i ∈ Submodule.span O (mono ρ (W.wt i)) := by
    intro i
    obtain ⟨g, a, b, hzi, hwi⟩ := hz i
    rw [hzi, hwi]
    by_cases hab : a = b
    · subst hab
      have h0 : wt a a = 0 := (wt_eq_zero a a).mpr rfl
      rw [h0, Algebra.algebraMap_eq_smul_one]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨[(g, a, a)], by simp [h0], by simp⟩) ?_
      exact Submodule.smul_mem _ _ (zm_one ρ)
    · rw [hc g a b hab, map_zero, sub_zero]
      exact Submodule.subset_span ⟨[(g, a, b)], by simp, by simp⟩
  classical
  have hall : ∀ t : Finset W.σ,
      (∏ s ∈ t, W.z s ^ n s) ∈ Submodule.span O (mono ρ (∑ s ∈ t, n s • W.wt s)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using zm_one (O := O) ρ
    | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact zm_mul ρ (zm_pow ρ (hmem a) _) ih
  have h := hall n.support
  rw [Finsupp.weight_apply, Finsupp.sum] at hn
  rw [hn] at h
  exact Algebra.span_le_adjoin O _ h
end

