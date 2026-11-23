module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CliffordSS
section
open Polynomial Matrix

theorem UpperTheory.V.Pr.T.cliffordSS :
    ∀ {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ρ : Representation K G V) (N : Subgroup G) [N.Normal],
      (∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∀ W : Submodule K V, (∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) →
        ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  intro K G V _ _ _ _ _ ρ N hN hirr W hW
  have hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v; rw [map_mul]; rfl
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  by_cases htriv : (⊤ : Submodule K V) = ⊥
  · exact top_le_iff.mp (htriv ▸ bot_le)
  obtain ⟨S, ⟨hSs, hS0⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥)
    ⟨⊤, fun _ _ _ _ => Submodule.mem_top, htriv⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  have hU := hirr (⨅ g : G, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  rcases hU with hU | hU
  · exfalso
    apply hS0
    rw [eq_bot_iff, ← hU]
    intro s hs
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => key g s hs
  · rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    simpa using hv 1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.IwasawaVal
section
open Polynomial Matrix

namespace UpperTheory.V.Pr.T

private def IwReach {K : Type} [Field K] (V : ValuationSubring K) {n : ℕ} (Y Z : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ k : GL (Fin n) V, ((k : Matrix (Fin n) (Fin n) V).map V.subtype) * Y = Z

section
variable {K : Type} [Field K] (V : ValuationSubring K) {n : ℕ}

private theorem iw_refl (Y : Matrix (Fin n) (Fin n) K) : IwReach V Y Y := by
  refine ⟨1, ?_⟩
  simp

private theorem iw_trans {X Y Z : Matrix (Fin n) (Fin n) K} (h1 : IwReach V X Y) (h2 : IwReach V Y Z) :
    IwReach V X Z := by
  obtain ⟨k1, rfl⟩ := h1
  obtain ⟨k2, rfl⟩ := h2
  exact ⟨k2 * k1, by rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]⟩

private theorem iw_perm (Y : Matrix (Fin n) (Fin n) K) (σ : Equiv.Perm (Fin n)) :
    IwReach V Y (Y.submatrix σ id) := by
  classical
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · show (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) V).map V.subtype * Y = _
    rw [PEquiv.map_toMatrix, PEquiv.toMatrix_toPEquiv_mul]

private theorem iw_clear (Y : Matrix (Fin n) (Fin n) K) (c : Fin n) (a : Fin n → V) (ha : a c = 0) :
    IwReach V Y (Matrix.of fun i j => Y i j - (a i : K) * Y c j) := by
  classical
  let A : Matrix (Fin n) (Fin n) V := Matrix.of fun i j => if j = c then a i else 0
  have hA2 : A * A = 0 := by
    ext i j
    simp [A, Matrix.mul_apply, ha]
  refine ⟨⟨1 - A, 1 + A, by simp [sub_mul, mul_add, hA2], by simp [add_mul, mul_sub, hA2]⟩, ?_⟩
  ext i j
  simp [A, Matrix.mul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
  simp only [apply_ite (fun x : V => (x : K)), ZeroMemClass.coe_zero, OneMemClass.coe_one, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem iw_step (Y : Matrix (Fin n) (Fin n) K) (c : Fin n)
    (hY : ∀ i j : Fin n, j < c → j < i → Y i j = 0) :
    ∃ Z, IwReach V Y Z ∧ ∀ i j : Fin n, j ≤ c → j < i → Z i j = 0 := by
  classical
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => c ≤ i)
    (fun i => V.valuation (Y i c)) ⟨c, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpmax
  set Y1 := Y.submatrix (Equiv.swap c p) id with hY1
  have r1 : IwReach V Y Y1 := iw_perm V Y _
  have hY1c : ∀ i j : Fin n, j < c → j < i → Y1 i j = 0 := by
    intro i j hjc hji
    simp only [hY1, Matrix.submatrix_apply, id]
    apply hY _ _ hjc
    rcases eq_or_ne i c with rfl | hic
    · rw [Equiv.swap_apply_left]
      exact lt_of_lt_of_le hjc hp
    rcases eq_or_ne i p with rfl | hip
    · rw [Equiv.swap_apply_right]
      exact hjc
    · rw [Equiv.swap_apply_of_ne_of_ne hic hip]
      exact hji
  have hmax1 : ∀ i, c ≤ i → V.valuation (Y1 i c) ≤ V.valuation (Y1 c c) := by
    intro i hi
    simp only [hY1, Matrix.submatrix_apply, id, Equiv.swap_apply_left]
    apply hpmax
    rcases eq_or_ne i c with rfl | hic
    · rw [Equiv.swap_apply_left]
      exact hp
    rcases eq_or_ne i p with rfl | hip
    · rw [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hic hip]
      exact hi
  by_cases h0 : Y1 c c = 0
  · refine ⟨Y1, r1, fun i j hjc hji => ?_⟩
    rcases lt_or_eq_of_le hjc with hlt | heq
    · exact hY1c i j hlt hji
    · rw [heq] at hji ⊢
      have h1 := hmax1 i hji.le
      rw [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
  · have hmem : ∀ i, c ≤ i → Y1 i c / Y1 c c ∈ V := by
      intro i hi
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 h0)]
      exact hmax1 i hi
    let a : Fin n → V := fun i => if h : c < i then ⟨Y1 i c / Y1 c c, hmem i h.le⟩ else 0
    have ha : a c = 0 := by simp [a]
    refine ⟨_, iw_trans V r1 (iw_clear V Y1 c a ha), fun i j hjc hji => ?_⟩
    simp only [Matrix.of_apply]
    rcases lt_or_eq_of_le hjc with hlt | heq
    · rw [hY1c i j hlt hji, hY1c c j hlt hlt, mul_zero, sub_zero]
    · rw [heq] at hji ⊢
      simp only [a, dif_pos hji]
      show Y1 i c - Y1 i c / Y1 c c * Y1 c c = 0
      rw [div_mul_cancel₀ _ h0, sub_self]

private theorem iw_ind (Y : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    ∃ Z, IwReach V Y Z ∧ ∀ i j : Fin n, (j : ℕ) < m → j < i → Z i j = 0 := by
  induction m with
  | zero => exact ⟨Y, iw_refl V Y, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨Z, hZ, h⟩ := ih
    by_cases hm : m < n
    · obtain ⟨Z', hZ', h'⟩ := iw_step V Z ⟨m, hm⟩ (fun i j hj hi => h i j hj hi)
      exact ⟨Z', iw_trans V hZ hZ', fun i j hj hi => h' i j (Nat.lt_succ_iff.1 hj) hi⟩
    · exact ⟨Z, hZ, fun i j _ hi => h i j (by have := j.2; omega) hi⟩

end

end UpperTheory.V.Pr.T

theorem UpperTheory.V.Pr.T.iwasawaVal :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (Y : Matrix (Fin n) (Fin n) K),
      ∃ k : GL (Fin n) V, (((k : Matrix (Fin n) (Fin n) V).map V.subtype) * Y).BlockTriangular id := by
  intro K _ V n Y
  obtain ⟨Z, ⟨k, hk⟩, hZ⟩ := iw_ind V Y n
  refine ⟨k, ?_⟩
  rw [hk]
  intro i j hij
  exact hZ i j j.isLt hij
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.OneUnitTF
section
open Polynomial Matrix

theorem UpperTheory.V.Pr.T.oneUnitTF :
    ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (x : R) (n : ℕ),
      n ≠ 0 → x - 1 ∈ IsLocalRing.maximalIdeal R → x ^ n = 1 → x = 1 := by
  intro R _ _ _ p _ _ x n hn hx hxn
  have hp : p.Prime := Fact.out
  obtain ⟨k, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hy1 : x ^ p ^ k - 1 = (x - 1) ^ p ^ k := by rw [sub_pow_char_pow, one_pow]
  have hym : (x ^ p ^ k) ^ m = 1 := by rw [← pow_mul]; exact hxn
  have hyM : x ^ p ^ k - 1 ∈ IsLocalRing.maximalIdeal R := by
    rw [hy1]; exact Ideal.pow_mem_of_mem _ hx _ (pow_pos hp.pos _)
  have hmu : IsUnit (m : R) := by
    have h0 : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h := (Ne.isUnit h0).map (ZMod.castHom (dvd_refl p) R)
    simpa using h
  have hs : (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) - m ∈ IsLocalRing.maximalIdeal R := by
    have h : (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) - m
        = ∑ i ∈ Finset.range m, ((x ^ p ^ k) ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [h]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (x ^ p ^ k) 1 i
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ hyM
  have hsu : IsUnit (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) := by
    by_contra h
    have h' := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 := Ideal.sub_mem _ h' hs
    rw [sub_sub_cancel] at h2
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 hmu
  have hy0 : x ^ p ^ k - 1 = 0 := by
    have h := geom_sum_mul (x ^ p ^ k) m
    rw [hym, sub_self] at h
    exact hsu.mul_right_eq_zero.1 h
  rw [hy1] at hy0
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero)).1 hy0)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
section
open Polynomial Matrix

private theorem UpperTheory.V.Pr.T.unipTorsion_unit {A : Type} [CommRing A] [IsLocalRing A] (χ : A[X]) (n m : ℕ)
    (hχ : χ.Monic) (hr : χ.map (IsLocalRing.residue A) = (X - 1) ^ n) (hm : IsUnit (m : A)) :
    IsUnit (AdjoinRoot.mk χ (∑ i ∈ Finset.range m, X ^ i)) := by
  haveI : Module.Finite A (AdjoinRoot χ) := (AdjoinRoot.powerBasis' hχ).finite
  haveI : Algebra.IsIntegral A (AdjoinRoot χ) := Algebra.IsIntegral.of_finite A _
  by_contra hnu
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (mt Ideal.span_singleton_eq_top.mp hnu)
  have hmem : AdjoinRoot.mk χ (∑ i ∈ Finset.range m, X ^ i) ∈ M := hle (Ideal.mem_span_singleton_self _)
  letI : Field (AdjoinRoot χ ⧸ M) := Ideal.Quotient.field M
  set π : AdjoinRoot χ →+* AdjoinRoot χ ⧸ M := Ideal.Quotient.mk M with hπdef
  set φ : A →+* AdjoinRoot χ ⧸ M := π.comp (algebraMap A (AdjoinRoot χ)) with hφdef
  have hcomap : Ideal.comap (algebraMap A (AdjoinRoot χ)) M = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) M)
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := by
    intro a ha
    rw [← hcomap, Ideal.mem_comap] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  set ψ : IsLocalRing.ResidueField A →+* AdjoinRoot χ ⧸ M := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ hker with hψdef
  have hψ : ψ.comp (IsLocalRing.residue A) = φ := by
    ext a
    exact Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ hker
  have key : ∀ p : A[X], π (AdjoinRoot.mk χ p) = eval₂ φ (π (AdjoinRoot.root χ)) p := by
    intro p
    rw [← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂]
  have hroot : π (AdjoinRoot.root χ) = 1 := by
    have h0 := key χ
    rw [AdjoinRoot.mk_self, map_zero, ← hψ, ← eval₂_map, hr] at h0
    simp only [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one] at h0
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0.symm)
  have hs := key (∑ i ∈ Finset.range m, X ^ i)
  have hz : π (AdjoinRoot.mk χ (∑ i ∈ Finset.range m, X ^ i)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hz, hroot] at hs
  simp only [eval₂_finsetSum, eval₂_X_pow, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hs
  have hu := hm.map φ
  rw [map_natCast] at hu
  exact hu.ne_zero hs.symm

theorem UpperTheory.V.Pr.T.unipTorsion :
    ∀ {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (γ : E) (χ : A[X]) (n m : ℕ),
      χ.Monic → aeval γ χ = 0 → χ.map (IsLocalRing.residue A) = (X - 1) ^ n → IsUnit (m : A) → γ ^ m = 1 → γ = 1 := by
  intro A E _ _ _ _ γ χ n m hχ hγ hr hm hγm
  have hu := UpperTheory.V.Pr.T.unipTorsion_unit χ n m hχ hr hm
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [← map_mul, ← map_one (AdjoinRoot.mk χ), AdjoinRoot.mk_eq_mk] at hb
  obtain ⟨q, hq⟩ := hb
  have h1 : aeval γ (∑ i ∈ Finset.range m, (X : A[X]) ^ i) * aeval γ p = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (aeval (R := A) γ), ← map_sub, hq, map_mul, hγ, zero_mul]
  have h2 : (1 - γ) * aeval γ (∑ i ∈ Finset.range m, (X : A[X]) ^ i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_pow, aeval_X]
    rw [mul_neg_geom_sum, hγm, sub_self]
  have h3 : 1 - γ = 0 := by
    calc 1 - γ = (1 - γ) * (aeval γ (∑ i ∈ Finset.range m, (X : A[X]) ^ i) * aeval γ p) := by
          rw [h1, mul_one]
      _ = 0 := by rw [← mul_assoc, h2, zero_mul]
  exact (sub_eq_zero.mp h3).symm
end

