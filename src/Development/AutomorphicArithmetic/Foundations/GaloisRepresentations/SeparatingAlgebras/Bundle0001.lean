module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.AlgPf
section
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.alg_pf :
    UpperTheory.Gal.Gen.HB → UpperTheory.Gal.Gen.GroupDet → UpperTheory.Gal.Gen.Alg := by
  intro hHB hGD k _ _ l _ H _ _ hH P hP hN
  classical
  have hl0 : 0 ≤ ‖(l : k)‖ := norm_nonneg _
  have hl1 : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hdN : Module.finrank k P ≤ Fintype.card H := by
    have h := Submodule.finrank_le P
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have key : ∀ a : H → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) →
      ‖∑ i, a i * (fun _ => (1 : k)) i‖ ≤ Real.sqrt ‖(l : k)‖ := by
    intro a ha hperp
    have hker : P ≤ LinearMap.ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin := by
      intro c hc
      rw [LinearMap.mem_ker]
      funext g
      have h0 := hperp (fun h => c (h * g)) (hP c hc g)
      have h1 : ∑ h, a (h * g⁻¹) * c h = ∑ i, a i * c (i * g) :=
        Fintype.sum_equiv (Equiv.mulRight g⁻¹) _ _ (fun x => by simp)
      change ∑ h, a (h * g⁻¹) * c h = 0
      rw [h1]
      exact h0
    have hrank : (Matrix.of fun h g : H => a (h * g⁻¹)).rank ≤
        Fintype.card H - Module.finrank k P := by
      have h2 := LinearMap.finrank_range_add_finrank_ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h2
      have h3 := Submodule.finrank_mono hker
      rw [← Matrix.rank_transpose]
      have h4 : (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.rank =
          Module.finrank k (LinearMap.range
            (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin) := rfl
      omega
    have h1 := hGD k l H hH a _ ha hrank
    rw [Nat.sub_sub_self hdN] at h1
    simp only [mul_one]
    rw [Real.le_sqrt (norm_nonneg _) hl0]
    have hne : Fintype.card H ≠ 0 := Fintype.card_ne_zero
    refine (pow_le_pow_iff_left₀ (by positivity) hl0 hne).mp ?_
    calc (‖∑ i, a i‖ ^ 2) ^ Fintype.card H
        = (‖∑ i, a i‖ ^ Fintype.card H) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (‖(l : k)‖ ^ Module.finrank k P) ^ 2 := by gcongr
      _ = ‖(l : k)‖ ^ (2 * Module.finrank k P) := by rw [← pow_mul, mul_comm]
      _ ≤ ‖(l : k)‖ ^ Fintype.card H := pow_le_pow_of_le_one hl0 hl1 hN
  obtain ⟨c, hc, hcv⟩ := hHB k H P (fun _ => 1) (Real.sqrt ‖(l : k)‖) key
  refine ⟨c, hc, fun h => ?_⟩
  have h5 : ‖(1 : k) - c h‖ ≤ Real.sqrt ‖(l : k)‖ := hcv h
  exact (Real.le_sqrt (norm_nonneg _) hl0).mp h5
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CodimPf
section
namespace UpperTheory.Gal.Gen

theorem codim_pf : Codim := by
  intro k V M _ _ _ _ _ _ Ψ A B _ h
  let f : V →ₗ[k] M ⧸ A := A.mkQ ∘ₗ Ψ
  have hker : LinearMap.ker f = A.comap Ψ := by
    ext v
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hrange : LinearMap.range f ≤ B.map A.mkQ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h v)
    refine ⟨b, hb, ?_⟩
    have hz : A.mkQ a = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ha
    simp only [f, LinearMap.comp_apply, ← hab, map_add (f := _), hz, zero_add]
  haveI : FiniteDimensional k (B.map A.mkQ) :=
    Module.Finite.map B A.mkQ
  have h1 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (B.map A.mkQ) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank k (B.map A.mkQ) ≤ Module.finrank k B :=
    Submodule.finrank_map_le A.mkQ B
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at h3
  omega

end UpperTheory.Gal.Gen
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetLow
section
noncomputable section

namespace UpperTheory.Gal.Gen

private lemma det_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) k) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  classical
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)

private lemma det_zero_of_card {k : Type} [Field k] {N ρ : ℕ}
    (A M : Matrix (Fin N) (Fin N) k) (s : Finset (Fin N)) (hr : A.rank ≤ ρ) (hs : ρ < s.card)
    (hM : ∀ i ∈ s, M i = A i) : M.det = 0 := by
  classical
  by_contra hne
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hne
  have heq : (fun i : s => A i) = (fun i => M i) ∘ (fun i : s => (i : Fin N)) := by
    funext i
    exact (hM i i.2).symm
  have hli' : LinearIndependent k (fun i : s => A i) := by
    rw [heq]
    exact hli.comp _ Subtype.val_injective
  have hle : Module.finrank k (Submodule.span k (Set.range (fun i : s => A i))) ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  rw [finrank_span_eq_card hli', Fintype.card_coe] at hle
  omega

private theorem det_add_smul_eq_sum_powerset_pow_card_mul_det {k : Type} [Field k] {N : ℕ} (A B : Matrix (Fin N) (Fin N) k)
    (c : k) :
    (A + c • B).det = ∑ t ∈ (Finset.univ : Finset (Fin N)).powerset,
      c ^ t.card * (Matrix.of fun r j => if r ∈ t then B r j else A r j).det := by
  classical
  rw [← Matrix.det_transpose]
  simp_rw [← Matrix.det_transpose (Matrix.of _)]
  simp only [Matrix.det_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [add_comm (A _ _)]
  rw [Finset.prod_add, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter,
    Finset.prod_mul_distrib, Finset.prod_const, mul_assoc, mul_smul_comm]

theorem detLow_pf : DetLow := by
  intro k _ _ N A B c ρ hA hB hc hr
  classical
  rw [det_add_smul_eq_sum_powerset_pow_card_mul_det]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t _ => ?_
  rw [norm_mul, norm_pow]
  by_cases ht : N - ρ ≤ t.card
  · have h1 := det_norm_le_one (Matrix.of fun r j => if r ∈ t then B r j else A r j) (by
      intro i j
      simp only [Matrix.of_apply]
      split_ifs
      · exact hB i j
      · exact hA i j)
    calc ‖c‖ ^ t.card * ‖(Matrix.of fun r j => if r ∈ t then B r j else A r j).det‖
        ≤ ‖c‖ ^ t.card * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ‖c‖ ^ (N - ρ) := by
        rw [mul_one]
        exact pow_le_pow_of_le_one (norm_nonneg _) hc ht
  · have h0 : (Matrix.of fun r j => if r ∈ t then B r j else A r j).det = 0 := by
      refine det_zero_of_card A _ tᶜ hr ?_ ?_
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
      · intro i hi
        funext j
        simp only [Matrix.of_apply, if_neg (Finset.mem_compl.mp hi)]
    rw [h0, norm_zero, mul_zero]
    positivity

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ExistsCloseVectorUltrametric
section
noncomputable section

namespace UpperTheory.Gal.Gen

private theorem exists_close_vector_ultrametric (k : Type) [NormedField k] [IsUltrametricDist k] (X : Type) [Fintype X] (r : ℝ) :
    ∀ (n : ℕ) (P : Submodule k (X → k)) (v : X → k), Module.finrank k P = n →
      (∀ a : X → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) → ‖∑ i, a i * v i‖ ≤ r) →
      ∃ c ∈ P, ∀ i, ‖v i - c i‖ ≤ r := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P v hn h
  by_cases hP : P = ⊥
  · subst hP
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    have key := h (Pi.single i 1) ?_ ?_
    · simpa [Pi.single_apply] using key
    · intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · intro c hc
      have hc0 : c = 0 := by simpa using hc
      simp [hc0]
  · obtain ⟨p0, hp0, hp0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ i, p0 i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hp0ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty X := ⟨j⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖p0 i‖)
    have hne : p0 i0 ≠ 0 := by
      intro h0
      have h1 := hi0 j
      rw [h0, norm_zero] at h1
      exact hj (norm_le_zero_iff.mp h1)
    obtain ⟨p, hp⟩ : ∃ p, p = (p0 i0)⁻¹ • p0 := ⟨_, rfl⟩
    have hpP : p ∈ P := hp ▸ P.smul_mem _ hp0
    have hpi0 : p i0 = 1 := by simp [hp, hne]
    have hple : ∀ i, ‖p i‖ ≤ 1 := by
      intro i
      simp only [hp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
      simpa using hi0 i
    obtain ⟨P', hP'⟩ : ∃ P', P' = P ⊓ LinearMap.ker (LinearMap.proj i0 : (X → k) →ₗ[k] k) := ⟨_, rfl⟩
    have hmem : ∀ c, c ∈ P' ↔ c ∈ P ∧ c i0 = 0 := by
      intro c
      simp [hP', Submodule.mem_inf, LinearMap.mem_ker]
    have hlt : P' < P := by
      refine lt_of_le_of_ne (fun c hc => ((hmem c).1 hc).1) ?_
      intro heq
      have h1 : p ∈ P' := heq ▸ hpP
      have h2 := ((hmem p).1 h1).2
      rw [hpi0] at h2
      exact one_ne_zero h2
    have hfr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨c', hc', hb⟩ := ih _ (hn ▸ hfr) P' (v - v i0 • p) rfl (by
      intro a ha hperp
      obtain ⟨s, hs⟩ : ∃ s, s = ∑ i, a i * p i := ⟨_, rfl⟩
      have hsn : ‖s‖ ≤ 1 := by
        rw [hs]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_one₀ (ha i) (norm_nonneg _) (hple i)
      have hsingle : ∀ w : X → k, ∑ i, (Pi.single i0 s : X → k) i * w i = s * w i0 := by
        intro w
        simp [Pi.single_apply, ite_mul]
      have key := h (a - Pi.single i0 s : X → k) ?_ ?_
      · have e : ∑ i, (a - Pi.single i0 s : X → k) i * v i = ∑ i, a i * (v - v i0 • p) i := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub,
            Finset.sum_sub_distrib, hsingle]
          congr 1
          rw [hs, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rwa [e] at key
      · intro i
        by_cases hi : i = i0
        · subst hi
          simp only [Pi.sub_apply, Pi.single_eq_same]
          rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha _) ?_)
          rwa [norm_neg]
        · simpa [Pi.single_apply, hi] using ha i
      · intro c hc
        have hd : c - c i0 • p ∈ P' := by
          refine (hmem _).2 ⟨P.sub_mem hc (P.smul_mem _ hpP), ?_⟩
          simp [hpi0]
        have h0 := hperp _ hd
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at h0
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hsingle]
        have h1 : ∑ i, a i * (c i0 * p i) = c i0 * s := by
          rw [hs, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [h1] at h0
        rw [mul_comm s]
        exact h0)
    refine ⟨v i0 • p + c', P.add_mem (P.smul_mem _ hpP) ((hmem _).1 hc').1, fun i => ?_⟩
    have e : v i - (v i0 • p + c') i = (v - v i0 • p) i - c' i := by
      simp [sub_sub]
    rw [e]
    exact hb i

theorem hB_pf : HB := by
  intro k _ _ X _ P v r h
  exact exists_close_vector_ultrametric k X r _ P v rfl h

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ExistsInvariantFlagModL
section
open Module

namespace UpperTheory.Gal.Gen

private theorem exists_invariant_flag_mod_l (hF : FixVec) (l : ℕ) [Fact l.Prime] (H : Type) [Group H] (hH : IsPGroup l H)
    (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V] (ρ : Representation (ZMod l) H V)
    (m : ℕ) (hm : m ≤ finrank (ZMod l) V) :
    ∃ v : Fin m → V, LinearIndependent (ZMod l) v ∧
      ∀ h j, ρ h (v j) - v j ∈ Submodule.span (ZMod l) (v '' {i | i < j}) := by
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  induction m with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hs⟩ := ih (Nat.le_of_succ_le hm)
    set U := Submodule.span (ZMod l) (Set.range v) with hU
    have hmono : ∀ j, Submodule.span (ZMod l) (v '' {i | i < j}) ≤ U := fun j =>
      Submodule.span_mono (Set.image_subset_range _ _)
    have hvU : ∀ j, v j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
    have hst : ∀ h, ∀ u ∈ U, ρ h u ∈ U := by
      intro h u hu
      have hle : U ≤ U.comap (ρ h) := by
        rw [hU, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have h1 := hmono j (hs h j)
        have h2 := U.add_mem h1 (hvU j)
        simpa using h2
      exact hle hu
    have hne : U ≠ ⊤ := by
      intro htop
      have h1 : finrank (ZMod l) U = m := by
        rw [hU, finrank_span_eq_card hv]; simp
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨x, hx, hxs⟩ := hF l H hH V ρ U hst hne
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · exact (linearIndependent_finSnoc).2 ⟨hv, hx⟩
    · intro h j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · have himg : (Fin.snoc v x : Fin (m+1) → V) '' {i | i < Fin.last m} = Set.range v := by
          ext y
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hi' : i ≠ Fin.last m := ne_of_lt hi
            obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi'
            exact ⟨i', by simp⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
        simp only [Fin.snoc_last]
        rw [himg]
        exact hxs h
      · have himg : v '' {i | i < j} ⊆ (Fin.snoc v x : Fin (m+1) → V) '' {i | i < j.castSucc} := by
          rintro _ ⟨i, hi, rfl⟩
          exact ⟨i.castSucc, by simpa using hi, by simp⟩
        simp only [Fin.snoc_castSucc]
        exact Submodule.span_mono himg (hs h j)

theorem flag_pf : FixVec → Flag := by
  intro hF l _ H _ hH V _ _ _ ρ
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  obtain ⟨v, hv, hs⟩ := exists_invariant_flag_mod_l hF l H hH V ρ _ le_rfl
  have hsp : ⊤ ≤ Submodule.span (ZMod l) (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (by simp)).ge
  let b : Basis (Fin (finrank (ZMod l) V)) (ZMod l) V := Basis.mk hv hsp
  refine ⟨b, ?_⟩
  intro h i j hji
  have hb : ∀ j, b j = v j := fun j => Basis.mk_apply hv hsp j
  have hmem : ρ h (b j) - b j ∈ Submodule.span (ZMod l) (b '' {i | i < j}) := by
    have : (b : _ → V) '' {i | i < j} = v '' {i | i < j} := by
      ext y; simp [hb]
    rw [this, hb]
    exact hs h j
  have hsupp := (Basis.mem_span_image b).1 hmem
  by_contra hne
  have hi : i ∈ ((b.repr (ρ h (b j) - b j)).support : Set _) := by
    simpa using hne
  have := hsupp hi
  exact absurd this (not_lt.2 hji)

end UpperTheory.Gal.Gen
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FixVec
section
namespace UpperTheory.Gal.Gen

theorem fixVec_pf : FixVec := by
  intro l _ H _ hH V _ _ _ ρ U hU hne
  classical
  let act : H → (V ⧸ U) →ₗ[ZMod l] (V ⧸ U) :=
    fun h => U.mapQ U (ρ h) (fun u hu => hU h u hu)
  have act_mk : ∀ (h : H) (v : V), act h (U.mkQ v) = U.mkQ (ρ h v) := fun h v => rfl
  letI : MulAction H (V ⧸ U) :=
    { smul := fun h x => act h x
      one_smul := by
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act 1 (U.mkQ v) = U.mkQ v
        rw [act_mk]
        simp
      mul_smul := by
        intro g h x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act (g * h) (U.mkQ v) = act g (act h (U.mkQ v))
        rw [act_mk, act_mk, act_mk]
        simp }
  have smul_def : ∀ (h : H) (x : V ⧸ U), h • x = act h x := fun h x => rfl
  haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hne
  haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  have hcard : l ∣ Nat.card (V ⧸ U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]
    exact dvd_pow_self l Module.finrank_pos.ne'
  have h0 : (0 : V ⧸ U) ∈ MulAction.fixedPoints H (V ⧸ U) := by
    intro h
    rw [smul_def, map_zero]
  obtain ⟨x, hx, hx0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ U) hcard h0
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hx0
    rw [eq_comm]
    simpa using hv
  · intro h
    have hfix := hx h
    rw [smul_def, act_mk] at hfix
    exact (Submodule.Quotient.eq U).1 hfix

end UpperTheory.Gal.Gen
end

