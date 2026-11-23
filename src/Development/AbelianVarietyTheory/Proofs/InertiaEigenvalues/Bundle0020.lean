module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueAnnihilatorOfNotStandardColumnFormA
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem exists_residue_annihilator_of_not_standard_column_form (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) O)
    (hx : ¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) :
    ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  classical
  set V := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hV
  let A : Set (Fin r → IsLocalRing.ResidueField O) :=
    {v | ∃ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ V ∧
      (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) ∧ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = v}
  have hA0 : (0 : Fin r → IsLocalRing.ResidueField O) ∈ A :=
    ⟨0, by convert V.zero_mem using 1; ext; simp, by simp, by ext; simp⟩
  have hAadd : ∀ v w, v ∈ A → w ∈ A → v + w ∈ A := by
    rintro v w ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩
    refine ⟨u + u', ?_, ?_, ?_⟩
    · have := V.add_mem hu hu'
      convert this using 1
      ext i; simp
    · intro i; simp [hu0 i, hu0' i]
    · ext i; simp
  have hAsmul : ∀ (c : IsLocalRing.ResidueField O) v, v ∈ A → c • v ∈ A := by
    rintro c v ⟨u, hu, hu0, rfl⟩
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨c' • u, ?_, ?_, ?_⟩
    · have := V.smul_mem (algebraMap O K c') hu
      convert this using 1
      ext i; simp
    · intro i; simp [hu0 i]
    · ext i; simp
  have hspan : ∀ v ∈ Submodule.span (IsLocalRing.ResidueField O) A, v ∈ A := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact hA0
    | add y w _ _ hy hw => exact hAadd y w hy hw
    | smul c y _ hy => exact hAsmul c y hy
  by_cases htop : Submodule.span (IsLocalRing.ResidueField O) A = ⊤
  · exfalso
    apply hx
    have hmem : ∀ i : Fin r, (Pi.single i 1 : Fin r → IsLocalRing.ResidueField O) ∈ A :=
      fun i => hspan _ (htop ▸ Submodule.mem_top)
    choose u hu hu0 hu1 using hmem
    let B : Matrix (Fin r ⊕ Fin t) (Fin r) O := fun p j => u j p
    let T : Matrix (Fin r) (Fin r) O := fun i j => u j (Sum.inl i)
    have hT : IsUnit T.det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      have : (IsLocalRing.residue O).mapMatrix T = 1 := by
        ext i j
        have := congrFun (hu1 j) i
        show IsLocalRing.residue O (u j (Sum.inl i)) = _
        rw [this]; simp [Pi.single_apply, Matrix.one_apply]
      rw [this, Matrix.det_one]; exact one_ne_zero
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hdiv : ∀ (i : Fin t) (j : Fin r), ∃ c, u j (Sum.inr i) = ϖ * c := by
      intro i j
      have : u j (Sum.inr i) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.residue_eq_zero_iff _).1 (hu0 j i)
      rw [hmax, Ideal.mem_span_singleton] at this
      exact this
    choose C hC using hdiv
    have hcol : ∀ j, ∃ c : Fin r → K, ∑ l, c l • (fun i => algebraMap O K (x i l)) = fun i => algebraMap O K (u j i) :=
      fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu j)
    choose d hd using hcol
    let D : Matrix (Fin r) (Fin r) K := fun l j => d j l
    have hBD : x.map (algebraMap O K) * D = B.map (algebraMap O K) := by
      ext p j
      have := congrFun (hd j) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_apply, Matrix.map_apply]
      show _ = algebraMap O K (u j p)
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hTD : (x.submatrix Sum.inl id).map (algebraMap O K) * D = T.map (algebraMap O K) := by
      ext i j
      have := congrFun₂ hBD (Sum.inl i) j
      simpa [Matrix.mul_apply] using this
    have hdetT : (T.map (algebraMap O K)).det = algebraMap O K T.det := by
      rw [RingHom.map_det]; rfl
    have hTK : IsUnit (T.map (algebraMap O K)).det := by
      rw [hdetT]; exact hT.map _
    have hDu : IsUnit D.det := by
      rw [← hTD, Matrix.det_mul] at hTK
      exact isUnit_of_mul_isUnit_right hTK
    have hdetTi : ((T⁻¹).map (algebraMap O K)).det = algebraMap O K (T⁻¹).det := by
      rw [RingHom.map_det]; rfl
    have hg : IsUnit (D * (T⁻¹).map (algebraMap O K)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hdetTi]
      exact hDu.mul ((Matrix.isUnit_nonsing_inv_det T hT).map _)
    refine ⟨hg.unit, Matrix.fromRows 0 (Matrix.of fun i j => ∑ l, C i l * T⁻¹ l j), ?_⟩
    rw [IsUnit.unit_spec, ← Matrix.mul_assoc, hBD, ← Matrix.map_mul]
    congr 1
    ext p j
    rcases p with i | i
    · rw [Matrix.mul_apply]
      have := congrFun₂ (Matrix.mul_nonsing_inv T hT) i j
      rw [Matrix.mul_apply] at this
      simpa [B, T] using this
    · rw [Matrix.mul_apply]
      simp [B, hC, Finset.mul_sum, mul_assoc]
  · obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 htop)
    have hf : ∀ v, f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]; congr 2; ext j; simp [Pi.single_apply, eq_comm]
    refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
    · intro h0
      apply hf0
      apply LinearMap.ext
      intro v
      rw [LinearMap.zero_apply, hf v, h0, zero_dotProduct]
    · intro u hu hu0
      rw [← hf]
      exact hle (Submodule.subset_span ⟨u, hu, hu0, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingSqZeroNilpotentAugmented
section
open Polynomial

namespace GlobalTheory.SqZeroPow

theorem dual_decomp {R : Type} [CommRing R] (b : DualNumber R) (r s : R) (h : r * s = b.fst) :
    TrivSqZeroExt.inl b.snd * (DualNumber.eps : DualNumber R)
      + TrivSqZeroExt.inl s * TrivSqZeroExt.inl r = b := by
  ext <;> simp [← h, mul_comm]

theorem dual_fst_of_eps_mul {R : Type} [CommRing R] (f : DualNumber R) (r : R) (n : ℕ)
    (h : (DualNumber.eps : DualNumber R) * (TrivSqZeroExt.inl r) ^ n * f = 0) :
    r ^ n * f.fst = 0 := by
  have hs := congrArg TrivSqZeroExt.snd h
  simpa [mul_comm] using hs

theorem dual_inl_pow {R : Type} [CommRing R] (r : R) (n : ℕ) (h : r ^ n = 0) :
    (TrivSqZeroExt.inl r : DualNumber R) ^ n = 0 := by
  rw [TrivSqZeroExt.inl_pow, h, TrivSqZeroExt.inl_zero]

theorem exists_ring (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ) (hm : 0 < m) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B),
      (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧
      x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  classical
  have h0 : (X ^ m : A[X]).eval₂ (AlgHom.id O A : A →+* A) 0 = 0 := by
    simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
  obtain ⟨g, hg⟩ : ∃ g : AdjoinRoot (X ^ m : A[X]) →ₐ[O] A,
      ∀ p : A[X], g (AdjoinRoot.mk _ p) = p.coeff 0 :=
    ⟨AdjoinRoot.liftAlgHom _ (AlgHom.id O A) 0 h0, fun p => by
      rw [AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_at_zero]
      rfl⟩
  have hroot : (AdjoinRoot.root (X ^ m : A[X])) ^ m = 0 := by
    have hself : AdjoinRoot.mk (X ^ m : A[X]) (X ^ m) = 0 := AdjoinRoot.mk_self
    rwa [map_pow, AdjoinRoot.mk_X] at hself
  refine ⟨DualNumber (AdjoinRoot (X ^ m : A[X])), inferInstance, inferInstance,
    (TrivSqZeroExt.inlAlgHom O _ _).comp (IsScalarTower.toAlgHom O A _),
    g.comp (TrivSqZeroExt.fstHom O _ _),
    DualNumber.eps, TrivSqZeroExt.inl (AdjoinRoot.root _), ?_, ?_, ?_, ?_,
    DualNumber.eps_mul_eps, dual_inl_pow _ _ hroot, ?_⟩
  · intro a
    simp only [AlgHom.comp_apply, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.fstHom_apply,
      TrivSqZeroExt.fst_inl, IsScalarTower.toAlgHom_apply]
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hg, Polynomial.coeff_C_zero]
  · intro b hb
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply] at hb
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective b.fst
    rw [← hp, hg] at hb
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hb
    have hq : AdjoinRoot.root (X ^ m : A[X]) * AdjoinRoot.mk _ q = b.fst := by
      rw [← hp, map_mul, AdjoinRoot.mk_X]
    have e := dual_decomp b _ _ hq
    rw [← e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)) <;> simp
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero]
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_inl]
    rw [← AdjoinRoot.mk_X, hg, Polynomial.coeff_X_zero]
  · intro f hf
    have h1 := dual_fst_of_eps_mul f _ (m - 1) hf
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply]
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective f.fst
    have e : AdjoinRoot.root (X ^ m : A[X]) ^ (m - 1) * AdjoinRoot.mk _ p
        = AdjoinRoot.mk _ (X ^ (m - 1) * p) := by
      rw [map_mul, map_pow, AdjoinRoot.mk_X]
    rw [← hp, e, AdjoinRoot.mk_eq_zero, Polynomial.X_pow_dvd_iff] at h1
    have h2 := h1 (m - 1) (Nat.sub_lt hm Nat.one_pos)
    rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at h2
    rw [← hp, hg]
    exact h2

end GlobalTheory.SqZeroPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootMulPowApprox
section
open PowerSeries

namespace GlobalTheory.PadicUnitGen

theorem dvd_iff_toZMod {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem one_add_pow_eq {R : Type*} [CommRing R] (t : R) (j : ℕ) :
    ∃ z, (1 + t) ^ j = 1 + j * t + t ^ 2 * z := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨j + z + t * z, by rw [pow_succ, hz]; push_cast; ring⟩

theorem exists_pow_approx {l : ℕ} [hl : Fact l.Prime] (u : ℤ_[l]) (h2 : l ≠ 2)
    (hu : Associated (u - 1) (l : ℤ_[l])) (x : ℤ_[l]) (hx : (l : ℤ_[l]) ∣ x - 1) (k : ℕ) :
    ∃ m : ℕ, (l : ℤ_[l]) ^ (k + 1) ∣ x - u ^ m := by
  obtain ⟨w, hw⟩ := hu.symm
  have hu' : u = 1 + l * (w : ℤ_[l]) := by rw [hw]; ring
  have h3 : 3 ≤ l := by
    have := hl.out.two_le
    omega
  have hl0 : PadicInt.toZMod (l : ℤ_[l]) = 0 := by simp
  have hw0 : PadicInt.toZMod (w : ℤ_[l]) ≠ 0 :=
    (w.isUnit.map (PadicInt.toZMod (p := l))).ne_zero
  have hu1 : PadicInt.toZMod u = 1 := by rw [hu']; simp
  induction k with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨m, c, hc⟩ := ih
    obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[l]) (u := l) (v := l)
      hl.out dvd_rfl (by rw [← pow_two, ← pow_succ]; exact pow_dvd_pow _ h3) (w : ℤ_[l]) k
    rw [← hu'] at hy
    set j : ℕ := (PadicInt.toZMod c / PadicInt.toZMod (w : ℤ_[l])).val with hj
    obtain ⟨z, hz⟩ := one_add_pow_eq ((l : ℤ_[l]) ^ k * l * (w + l * y)) j
    refine ⟨m + l ^ k * j, ?_⟩
    have hd : (l : ℤ_[l]) ∣ c - u ^ m * (j * (w + l * y)
        + (l : ℤ_[l]) ^ k * l * (w + l * y) ^ 2 * z) := by
      rw [dvd_iff_toZMod]
      simp only [map_sub, map_mul, map_add (f := _), map_pow, hl0, hu1, map_natCast, hj,
        ZMod.natCast_zmod_val, ZMod.natCast_self]
      field_simp
      ring
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    rw [pow_add, pow_mul, hy, hz]
    linear_combination hc + (l : ℤ_[l]) ^ (k + 1) * hd

theorem exists_lift {l : ℕ} [hl : Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (hΔ : Nat.card Δ = l - 1) (x : (ZMod l)ˣ) :
    ∃ δ ∈ Δ, PadicInt.toZMod (δ : ℤ_[l]) = x := by
  let f : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →* ZMod l)).comp Δ.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have h1 : PadicInt.toZMod ((δ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := congrArg Units.val hδ
    have h2 : ((δ : ℤ_[l]ˣ) : ℤ_[l]) ^ (l - 1) = 1 := by
      have : δ ^ (l - 1) = 1 := by rw [← hΔ]; exact pow_card_eq_one'
      have := congrArg (fun t : Δ => ((t : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa using this
    have h3 := geom_sum_mul ((δ : ℤ_[l]ˣ) : ℤ_[l]) (l - 1)
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h | h
    · exfalso
      have := congrArg (PadicInt.toZMod (p := l)) h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, map_zero] at this
      rw [Nat.cast_pred hl.out.pos] at this
      simp at this
    · apply Subtype.ext
      apply Units.ext
      exact sub_eq_zero.1 h
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hΔ, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨δ, hδ⟩ := hbij.2 x
  exact ⟨δ, δ.2, congrArg Units.val hδ⟩

theorem exists_root_mul_pow_approx :
    ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (u : ℤ_[l]), l ≠ 2 →
      Nat.card Δ = l - 1 → Associated (u - 1) (l : ℤ_[l]) → ∀ k a : ℕ, ¬ l ∣ a →
      ∃ δ ∈ Δ, ∃ m : ℕ, (l : ℤ_[l]) ^ k ∣ (a : ℤ_[l]) - (δ : ℤ_[l]) * u ^ m := by
  intro l hl Δ _ u h2 hΔ hu k a ha
  have ha0 : (a : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨δ, hδ, hδa⟩ := exists_lift Δ hΔ (Units.mk0 _ ha0)
  have hx : (l : ℤ_[l]) ∣ (a : ℤ_[l]) * (δ⁻¹ : ℤ_[l]ˣ) - 1 := by
    have : (l : ℤ_[l]) ∣ (a : ℤ_[l]) - δ := by
      rw [dvd_iff_toZMod, map_sub, hδa]; simp
    have h := this.mul_right ((δ⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    rwa [sub_mul, Units.mul_inv] at h
  obtain ⟨m, hm⟩ := exists_pow_approx u h2 hu _ hx k
  refine ⟨δ, hδ, m, (pow_dvd_pow _ (Nat.le_succ k)).trans ?_⟩
  have h := hm.mul_left (δ : ℤ_[l])
  rwa [mul_sub, mul_comm (a : ℤ_[l]), Units.mul_inv_cancel_left] at h

end GlobalTheory.PadicUnitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplex
section
namespace GlobalTheory

theorem adjoin_roots_of_unity_embeds_complex {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K)
    (t : L0 →+* ℂ) (Z : Set K) (hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧
      ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  letI : Algebra L0 K := s.toAlgebra
  letI : Algebra L0 ℂ := t.toAlgebra
  have hint : ∀ z ∈ Z, IsIntegral L0 z := by
    intro z hz
    obtain ⟨n, hn, hzn⟩ := hZ z hz
    exact ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hzn]⟩
  haveI : Algebra.IsAlgebraic L0 (IntermediateField.adjoin L0 Z) :=
    IntermediateField.isAlgebraic_adjoin hint
  let φ : IntermediateField.adjoin L0 Z →ₐ[L0] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(IntermediateField.adjoin L0 Z).toSubfield, φ.toRingHom,
    fun x => (IntermediateField.adjoin L0 Z).algebraMap_mem x,
    fun z hz => IntermediateField.subset_adjoin L0 Z hz, ?_⟩
  intro x hx
  have h : (⟨s x, hx⟩ : IntermediateField.adjoin L0 Z) = algebraMap L0 _ x := rfl
  change φ ⟨s x, hx⟩ = t x
  rw [h, φ.commutes]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTensorIdempotentOfAlgHomToBase
section
open NumberField IsDedekindDomain TensorProduct Polynomial

namespace GlobalTheory

theorem exists_tensor_idem_of_algHom (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E']
    [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K) :
    ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  classical
  set A := K ⊗[E] E'
  let pb := Field.powerBasisOfFiniteOfSeparable E E'
  set θ := pb.gen
  let T : A := Algebra.TensorProduct.includeRight θ
  set α : K := ψ T
  let f : E[X] := minpoly E θ
  let fK : K[X] := f.map (algebraMap E K)
  have hfT : aeval T fK = 0 := by
    rw [aeval_map_algebraMap]
    have : aeval T f = Algebra.TensorProduct.includeRight (aeval θ f) := by
      rw [aeval_algHom_apply]
    rw [this, minpoly.aeval, map_zero]
  have hroot : IsRoot fK α := by
    have h1 : aeval α fK = ψ (aeval T fK) := by
      rw [aeval_algHom_apply]
    rw [hfT, map_zero] at h1
    simpa [IsRoot, aeval_def, eval₂_eq_eval_map] using h1
  have hsep : fK.Separable := Polynomial.Separable.map (p := f) (Algebra.IsSeparable.isSeparable E θ)
  set g : K[X] := fK /ₘ (X - C α)
  have hfac : (X - C α) * g = fK := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hgα : g.eval α ≠ 0 := by
    have hd := hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := α) (by simpa [eval₂_id] using hroot)
    rw [eval₂_id, ← hfac] at hd
    simpa [derivative_mul] using hd
  let e : A := algebraMap K A (g.eval α)⁻¹ * aeval T g
  have hψg : ψ (aeval T g) = g.eval α := by
    rw [← aeval_algHom_apply]; rfl
  have hψe : ψ e = 1 := by
    have hc : ψ (algebraMap K A (g.eval α)⁻¹) = (g.eval α)⁻¹ := ψ.commutes _
    simp only [e, map_mul, hc, hψg]
    exact inv_mul_cancel₀ hgα
  have hTe : e * T = algebraMap K A (ψ T) * e := by
    have h0 : (T - algebraMap K A α) * aeval T g = 0 := by
      have : aeval T ((X - C α) * g) = (T - algebraMap K A α) * aeval T g := by
        simp [map_mul, map_sub]
      rw [← this, hfac, hfT]
    have h1 : T * aeval T g = algebraMap K A α * aeval T g := by
      rw [sub_mul] at h0; exact sub_eq_zero.1 h0
    simp only [e]
    calc algebraMap K A (g.eval α)⁻¹ * aeval T g * T
        = algebraMap K A (g.eval α)⁻¹ * (T * aeval T g) := by ring
      _ = algebraMap K A α * (algebraMap K A (g.eval α)⁻¹ * aeval T g) := by rw [h1]; ring

  let Q : A → Prop := fun a => e * a = algebraMap K A (ψ a) * e
  have Qmul : ∀ a b, Q a → Q b → Q (a * b) := by
    intro a b ha hb
    show e * (a * b) = algebraMap K A (ψ (a * b)) * e
    rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb]; ring
  have Qadd : ∀ a b, Q a → Q b → Q (a + b) := by
    intro a b ha hb
    show e * (a + b) = algebraMap K A (ψ (a + b)) * e
    rw [map_add (f := _), map_add (f := _), mul_add, ha, hb, add_mul]
  have Qalg : ∀ k : K, Q (algebraMap K A k) := by
    intro k
    show e * algebraMap K A k = algebraMap K A (ψ (algebraMap K A k)) * e
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  have Qright : ∀ x : E', Q (Algebra.TensorProduct.includeRight x) := by
    intro x
    have hx : x ∈ Algebra.adjoin E ({θ} : Set E') := by rw [pb.adjoin_gen_eq_top]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]; exact hTe
    | algebraMap r =>
      have : (Algebra.TensorProduct.includeRight (algebraMap E E' r) : A)
          = algebraMap K A (algebraMap E K r) := by
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E K A]
      rw [this]; exact Qalg _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Qadd _ _ hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact Qmul _ _ hy hz
  refine ⟨e, hψe, fun a => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    have : (k ⊗ₜ[E] x : A) = algebraMap K A k * Algebra.TensorProduct.includeRight x := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, one_mul]
    rw [this]; exact Qmul _ _ (Qalg k) (Qright x)
  | add a b ha hb => exact Qadd _ _ ha hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationSubringAlgClosedNotIsUnit
section
open scoped NNReal

namespace GlobalTheory

theorem exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero :
    ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V),
        ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  intro S _ u hu
  obtain ⟨m, hm, hum⟩ := Ideal.exists_le_maximal (Ideal.span {u})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hum' : u ∈ m := hum (Ideal.mem_span_singleton_self u)
  haveI := hm.isPrime
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := m) bot_le
  haveI hqp : q.IsPrime := hq.1.1
  let L := AlgebraicClosure (FractionRing (S ⧸ q))
  let g : S →+* L := ((algebraMap (FractionRing (S ⧸ q)) L).comp
    (algebraMap (S ⧸ q) (FractionRing (S ⧸ q)))).comp (Ideal.Quotient.mk q)
  have hg : ∀ s, g s = 0 ↔ s ∈ q := by
    intro s
    simp only [g, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (algebraMap (FractionRing (S ⧸ q)) L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) (FractionRing (S ⧸ q))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hne : m.map g.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : g.range) ∈ m.map g.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ :=
      (Ideal.mem_map_iff_of_surjective _ g.rangeRestrict_surjective).1 h1
    have h2 : g (x - 1) = 0 := by
      have := congrArg Subtype.val hx1
      simp only [RingHom.coe_rangeRestrict, OneMemClass.coe_one] at this
      rw [map_sub, this, map_one, sub_self]
    have h3 : x - 1 ∈ m := hqm ((hg _).1 h2)
    have h4 : (1 : S) ∈ m := by simpa using m.sub_mem hx h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h4)
  obtain ⟨V, hV, hV'⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hmem : ∀ s, g s ∈ V := fun s => hV (show g s ∈ g.range from ⟨s, rfl⟩)
  refine ⟨L, inferInstance, inferInstance, V, g.codRestrict V hmem, ?_, ?_⟩
  · have h1 : g u ∈ V.nonunits :=
      hV' ⟨g.rangeRestrict u, Ideal.mem_map_of_mem _ hum', rfl⟩
    have h2 := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨g u, hmem u⟩)).1 h1
    exact h2
  · intro s hs h0
    have h1 : g s = 0 := congrArg Subtype.val h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq)
      ((hg s).1 h1) hs

end GlobalTheory
end

