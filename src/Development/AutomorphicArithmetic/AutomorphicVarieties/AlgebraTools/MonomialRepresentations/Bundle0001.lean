module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CharpolyPowInt
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.charpolyPowInt :
    ∀ (R ι : Type) [CommRing R] [Fintype ι] [DecidableEq ι] (S : Subring R) (M : Matrix ι ι R) (N : ℕ), 0 < N →
      (∀ i, (M ^ N).charpoly.coeff i ∈ S) → ∀ i, IsIntegral S (M.charpoly.coeff i) := by
  intro R ι _ _ _ S M N hN h i
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, Polynomial.monic_one, Subsingleton.elim _ _⟩
  haveI : Nontrivial S := ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  have hdvd : M.charpoly ∣ (M ^ N).charpoly.comp (X ^ N) := by
    set A : Matrix ι ι R[X] := Matrix.scalar ι (X : R[X]) with hAdef
    set B : Matrix ι ι R[X] := (C : R →+* R[X]).mapMatrix M with hBdef
    have hAB : Commute A B := Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    have e1 : (M ^ N).charpoly.comp (X ^ N) = (A ^ N - B ^ N).det := by
      have hA : A ^ N = Matrix.scalar ι ((X : R[X]) ^ N) := (map_pow (Matrix.scalar ι) X N).symm
      have hB : B ^ N = (C : R →+* R[X]).mapMatrix (M ^ N) := (map_pow _ M N).symm
      rw [hA, hB, Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
      congr 1
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.charmatrix_apply_eq]
      · simp [Matrix.charmatrix_apply_ne _ _ _ hab, hab]
    rw [e1, ← hAB.geom_sum₂_mul N, Matrix.det_mul]
    exact Dvd.intro_left _ rfl
  have hl : (M ^ N).charpoly ∈ Polynomial.lifts (algebraMap S R) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨p₀, hp₀, -, hmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hl (Matrix.charpoly_monic _)
  refine Polynomial.isIntegral_coeff_of_dvd (p₀.comp (X ^ N)) M.charpoly
    (hmon.comp (Polynomial.monic_X_pow N) (by rw [Polynomial.natDegree_X_pow]; omega))
    (Matrix.charpoly_monic M) ?_ i
  rw [Polynomial.map_comp, hp₀, Polynomial.map_pow, Polynomial.map_X]
  exact hdvd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Clifford
section
open Polynomial Matrix

namespace UpperTheory.V.AlgebraTools

section

variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V) (N : Subgroup G) [hN : N.Normal]

private def cliffTr (g : G) (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) where
  toSubmodule := W.toSubmodule.comap (ρ g)
  apply_mem_toSubmodule n v hv := by
    have h := W.apply_mem_toSubmodule ⟨g * n * g⁻¹, hN.conj_mem _ n.2 g⟩ hv
    have e : ρ (g * n * g⁻¹) (ρ g v) = ρ g (ρ n v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    change ρ g (ρ n v) ∈ W.toSubmodule
    rw [← e]
    exact h

private theorem cliffTr_mul (g h : G) (hgh : g * h = 1)
    (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    cliffTr ρ N h (cliffTr ρ N g W) = W := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change ρ g (ρ h v) ∈ W.toSubmodule ↔ _
  rw [← Module.End.mul_apply, ← map_mul, hgh, map_one]
  rfl

private def cliffIso (g : G) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) ≃o
      Subrepresentation (ρ.comp N.subtype : Representation K N V) :=
  Equiv.toOrderIso
    { toFun := cliffTr ρ N g
      invFun := cliffTr ρ N g⁻¹
      left_inv := cliffTr_mul ρ N g g⁻¹ (by simp)
      right_inv := cliffTr_mul ρ N g⁻¹ g (by simp) }
    (fun _ _ h _ hv => h hv) (fun _ _ h _ hv => h hv)

end

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.clifford :
    ∀ (K G V : Type) [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V)
      (N : Subgroup G) [N.Normal], ρ.IsIrreducible → Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  intro K G V _ _ _ _ _ ρ N _ hirr
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)
  let A := {m : Submodule (MonoidAlgebra K N) (Representation.asModule (ρ.comp N.subtype)) |
    IsSimpleModule (MonoidAlgebra K N) m}
  have hA : ∀ m, m ∈ A ↔ IsAtom m := fun m => isSimpleModule_iff_isAtom
  change sSup A = ⊤
  have inv : ∀ g : G, ∀ v : V, v ∈ e.symm (sSup A) → ρ g v ∈ e.symm (sSup A) := by
    intro g v hv
    let φ := e.symm.trans ((UpperTheory.V.AlgebraTools.cliffIso ρ N g).trans e)
    have hφ : φ (sSup A) = sSup A := by
      rw [OrderIso.map_sSup]
      apply le_antisymm
      · refine iSup₂_le fun a ha => le_sSup ?_
        exact (hA _).2 ((φ.isAtom_iff a).2 ((hA a).1 ha))
      · refine sSup_le fun b hb => ?_
        have hb' : φ.symm b ∈ A := (hA _).2 ((φ.symm.isAtom_iff b).2 ((hA b).1 hb))
        have h := le_iSup₂ (f := fun a (_ : a ∈ A) => φ a) (φ.symm b) hb'
        simpa using h
    have h : v ∈ e.symm (φ (sSup A)) := by rw [hφ]; exact hv
    exact h
  let T : Subrepresentation ρ := ⟨(e.symm (sSup A)).toSubmodule, fun g v hv => inv g v hv⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · exfalso
    have hmono : StrictMono (Subrepresentation.toSubmodule :
        Subrepresentation (ρ.comp N.subtype) → Submodule K V) :=
      fun x y h => h
    haveI := hmono.wellFoundedLT
    haveI : IsAtomic (Subrepresentation (ρ.comp N.subtype)) :=
      isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    have hne : (⊤ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊥ := by
      intro h
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.ext
      exact (congrArg Subrepresentation.toSubmodule h).symm
    obtain ⟨a, ha, -⟩ :=
      (eq_bot_or_exists_atom_le (⊤ : Subrepresentation (ρ.comp N.subtype))).resolve_left hne
    have h1 : a ≤ e.symm (sSup A) := by
      have h0 : e a ≤ sSup A := le_sSup ((hA _).2 ((e.isAtom_iff a).2 ha))
      simpa using e.symm.monotone h0
    have h2 : (e.symm (sSup A)).toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hT
    apply ha.1
    apply Subrepresentation.ext
    apply le_antisymm _ bot_le
    intro v hv
    have h3 : v ∈ (e.symm (sSup A)).toSubmodule := h1 hv
    rw [h2] at h3
    exact h3
  · refine eq_top_iff.2 fun v _ => ?_
    have h3 : (show V from v) ∈ T.toSubmodule := by rw [hT]; exact Submodule.mem_top
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CoordSub
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.coordSub :
    ∀ (C ι : Type) [CommRing C] [Fintype ι] [DecidableEq ι] (d : ι → C), (∀ i j, i ≠ j → IsUnit (d i - d j)) →
      ∀ W : Submodule C (ι → C), (∀ w ∈ W, diagonal d *ᵥ w ∈ W) → ∀ w ∈ W, ∀ i, Pi.single i (w i) ∈ W := by
  intro C ι _ _ _ d hd W hD w hw i
  have key : ∀ S : Finset ι, (fun k => (∏ j ∈ S, (d k - d j)) * w k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using hw
    · intro j S hj ih
      have h2 := W.sub_mem (hD _ ih) (W.smul_mem (d j) ih)
      convert h2 using 1
      funext k
      simp only [Finset.prod_insert hj, Pi.sub_apply, Matrix.mulVec_diagonal,
        Pi.smul_apply, smul_eq_mul, mul_assoc, sub_mul]
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (d i - d j)) :=
    IsUnit.prod_iff.mpr fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm
  have h3 := W.smul_mem (↑hu.unit⁻¹ : C) (key (Finset.univ.erase i))
  convert h3 using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · have hz : ∏ j ∈ Finset.univ.erase i, (d k - d j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp [Pi.single_eq_of_ne hk, hz]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.DiscSwap
section
open Polynomial Matrix

private theorem charpoly_fromBlocks_antidiagonal_fin_two {F : Type} [Field F] (P Q : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks 0 P Q 0).charpoly = X ^ 4 - C ((Q * P) 0 0 + (Q * P) 1 1) * X ^ 2
      + C ((Q * P) 0 0 * (Q * P) 1 1 - (Q * P) 0 1 * (Q * P) 1 0) := by
  unfold Matrix.charpoly
  rw [charmatrix_fromBlocks]
  have hcz : charmatrix (0 : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ : Fin 2 => (X : F[X])) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [charmatrix_apply]
    · simp [charmatrix_apply, diagonal_apply_ne _ h]
  rw [hcz]
  generalize hS : (diagonal (fun _ : Fin 2 => (X : F[X])) : Matrix (Fin 2) (Fin 2) F[X]) = S
  generalize hP' : P.map C = P'
  generalize hQ' : Q.map C = Q'
  have hcomm : S * P' = P' * S := by
    subst hS
    ext i j
    simp [mul_comm]
  have hprod : fromBlocks S (-P') (-Q') S * fromBlocks S P' 0 S
      = fromBlocks (S * S) 0 (-(Q' * S)) (S * S - Q' * P') := by
    rw [fromBlocks_multiply, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [hcomm, neg_mul, add_neg_cancel]
    · simp
    · rw [neg_mul, add_comm, sub_eq_add_neg]
  have hdet := congrArg det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  have hSd : det S = X ^ 2 := by
    subst hS
    simp [det_diagonal, Fin.prod_univ_two, sq]
  rw [det_mul, hSd] at hdet
  have hX : (X ^ 2 * X ^ 2 : F[X]) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)
  have hG : det (fromBlocks S (-P') (-Q') S) = det (S * S - Q' * P') := by
    apply mul_right_cancel₀ hX
    rw [hdet]
    ring
  rw [hG, det_fin_two]
  subst hS hP' hQ'
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem separable_biquadratic_of_ne_zero_of_discrim_ne_zero {F : Type} [Field F] (a d : F) (h2 : (2 : F) ≠ 0) (hd : d ≠ 0)
    (he : a ^ 2 - 4 * d ≠ 0) : (X ^ 4 - C a * X ^ 2 + C d : F[X]).Separable := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hk : 4 * d * (8 * d - 2 * a ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero h4 hd) ?_
    rw [show 8 * d - 2 * a ^ 2 = -2 * (a ^ 2 - 4 * d) by ring]
    exact mul_ne_zero (neg_ne_zero.2 h2) he
  have hder : derivative (X ^ 4 - C a * X ^ 2 + C d : F[X]) = 4 * X ^ 3 - 2 * C a * X := by
    rw [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X_pow, derivative_C]
    norm_num
    simp only [map_ofNat]
    ring
  have hCe : (C (8 * d - 2 * a ^ 2) : F[X]) = 8 * C d - 2 * C a ^ 2 := by
    simp only [map_mul, map_sub, map_pow, map_ofNat]
  have key : (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)) * (X ^ 4 - C a * X ^ 2 + C d)
      + (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X) * (4 * X ^ 3 - 2 * C a * X)
      = C (4 * d * (8 * d - 2 * a ^ 2)) := by
    rw [map_mul, map_mul, hCe]
    simp only [map_ofNat]
    ring
  unfold Polynomial.Separable IsCoprime
  refine ⟨C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)),
    C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X), ?_⟩
  rw [hder]
  calc _ = C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * C (4 * d * (8 * d - 2 * a ^ 2)) := by rw [← key]; ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hk, C_1]

private theorem discSwap_lemma_3 {K : Type} [Field K] (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ)
    (hw₁ : StrictAnti w₁) (hw₂ : StrictAnti w₂) (hb : b 0 0 ≠ 0) (hc : c 0 0 ≠ 0)
    (hbd : b.det ≠ 0) (hcd : c.det ≠ 0) :
    let N := (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) *
      (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i));
    N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 ∧
      (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) ≠ 0 := by
  intro N
  have h01 : (0 : Fin 2) < 1 := by decide
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, w₁ 0 = w₁ 1 + n ∧ 0 < n :=
    ⟨(w₁ 0 - w₁ 1).toNat, by have := hw₁ h01; omega, by have := hw₁ h01; omega⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m : ℕ, w₂ 0 = w₂ 1 + m ∧ 0 < m :=
    ⟨(w₂ 0 - w₂ 1).toNat, by have := hw₂ h01; omega, by have := hw₂ h01; omega⟩
  set f := algebraMap K (RatFunc K) with hf
  set Y : RatFunc K := RatFunc.X with hY
  have hY0 : Y ≠ 0 := RatFunc.X_ne_zero
  have hA : Y ^ w₁ 0 = Y ^ w₁ 1 * Y ^ n := by rw [hn, zpow_add₀ hY0, zpow_natCast]
  have hB : Y ^ w₂ 0 = Y ^ w₂ 1 * Y ^ m := by rw [hm, zpow_add₀ hY0, zpow_natCast]
  have hu : Y ^ w₁ 1 ≠ 0 := zpow_ne_zero _ hY0
  have hv : Y ^ w₂ 1 ≠ 0 := zpow_ne_zero _ hY0
  have e00 : N 0 0 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e01 : N 0 1 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e10 : N 1 0 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e11 : N 1 1 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0
      = f (c.det * b.det) * (Y ^ w₁ 1) ^ 2 * (Y ^ w₂ 1) ^ 2 * Y ^ (n + m) := by
    rw [e00, e01, e10, e11, hA, hB, det_fin_two, det_fin_two]
    simp only [map_mul, map_sub]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdet]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hu)) (pow_ne_zero _ hv)) (pow_ne_zero _ hY0)
    exact (map_ne_zero f).2 (mul_ne_zero hcd hbd)
  · set q : K[X] := C (c 0 0 * b 0 0) * X ^ (n + m)
      + (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1)) with hq
    set Pol : K[X] := q ^ 2 - C (4 * (c.det * b.det)) * X ^ (n + m) with hPol
    have hkey : (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0)
        = (Y ^ w₁ 1 * Y ^ w₂ 1) ^ 2 * algebraMap K[X] (RatFunc K) Pol := by
      rw [hdet, e00, e11, hA, hB, hPol, hq]
      simp only [map_mul, map_sub, map_add (f := _), map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        map_ofNat, hf, RatFunc.algebraMap_eq_C, hY]
      ring
    have hrest : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
        < n + m := by
      have h1 : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
          ≤ max n m := by
        refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_right _ _)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_left _ _)
        · rw [natDegree_C]; exact Nat.zero_le _
      omega
    have hqd : q.natDegree = n + m := by
      rw [hq, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ (mul_ne_zero hc hb)]
      exact hrest
    have hPol0 : Pol ≠ 0 := by
      intro h0
      have hsq : q ^ 2 = C (4 * (c.det * b.det)) * X ^ (n + m) := sub_eq_zero.1 (hPol ▸ h0)
      have := congrArg natDegree hsq
      rw [natDegree_pow, hqd] at this
      have hle := natDegree_C_mul_X_pow_le (4 * (c.det * b.det)) (n + m)
      omega
    rw [hkey]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu hv)) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hPol0

theorem UpperTheory.V.AlgebraTools.discSwap :
    ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ), StrictAnti w₁ → StrictAnti w₂ →
      b 0 0 ≠ 0 → c 0 0 ≠ 0 → b.det ≠ 0 → c.det ≠ 0 →
      ((fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
        diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))).charpoly.Separable := by
  intro K _ h2 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  have hblk : (fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
      diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
      = fromBlocks 0 (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
          (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.mul_diagonal]
  have h2' : (2 : RatFunc K) ≠ 0 := by
    rw [show (2 : RatFunc K) = algebraMap K (RatFunc K) 2 from (map_ofNat _ 2).symm]
    exact (_root_.map_ne_zero _).2 h2
  obtain ⟨hd, he⟩ := discSwap_lemma_3 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  rw [hblk, charpoly_fromBlocks_antidiagonal_fin_two]
  exact separable_biquadratic_of_ne_zero_of_discrim_ne_zero _ _ h2' hd he
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdComp
section
open Polynomial Matrix

private theorem comp_image {G : Type} [TopologicalSpace G] (e : G ≃ₜ G) {Z : Set G}
    (hZ : Z ∈ irreducibleComponents G) : e '' Z ∈ irreducibleComponents G := by
  refine ⟨hZ.1.image e e.continuous.continuousOn, fun y hy hsub => ?_⟩
  have h1 : Z ⊆ e.symm '' y := by
    intro z hz
    exact ⟨e z, hsub ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩
  have h2 := hZ.2 (hy.image e.symm e.symm.continuous.continuousOn) h1
  intro w hw
  exact ⟨e.symm w, h2 ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩

private theorem exists_unique_pt {G : Type} [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G]
    (a : G) : ∃ x : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      x ∈ Z → x ∈ W → Z = W := by
  classical
  obtain ⟨Z, hZ, haZ⟩ : ∃ Z ∈ irreducibleComponents G, a ∈ Z :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents a, mem_irreducibleComponent⟩
  have hfin : (irreducibleComponents G \ {Z}).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff
  have hnot : ¬ Z ⊆ ⋃₀ (irreducibleComponents G \ {Z}) := by
    intro hsub
    obtain ⟨W, hW, hZW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ.1) hfin.toFinset
      (fun W hW => isClosed_of_mem_irreducibleComponents W (hfin.mem_toFinset.1 hW).1)
      (by simpa using hsub)
    rw [hfin.mem_toFinset] at hW
    exact hW.2 (Set.mem_singleton_iff.2 (le_antisymm (hZ.2 hW.1.1 hZW) hZW))
  obtain ⟨x, hxZ, hxn⟩ := Set.not_subset.1 hnot
  have key : ∀ Y ∈ irreducibleComponents G, x ∈ Y → Y = Z := by
    intro Y hY hxY
    by_contra hne
    exact hxn ⟨Y, ⟨hY, hne⟩, hxY⟩
  refine ⟨x, fun Z' hZ' W' hW' hx1 hx2 => ?_⟩
  rw [key Z' hZ' hx1, key W' hW' hx2]

theorem UpperTheory.V.AlgebraTools.idComp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G],
      (∀ g : G, Continuous (fun x => g * x)) → (∀ g : G, Continuous (fun x => x * g)) →
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ IsClosed (N : Set G) ∧ IsIrreducible (N : Set G) ∧
        ∀ U : Subgroup G, U.FiniteIndex → (N : Set G) ⊆ closure ((U ⊓ N : Subgroup G) : Set G) := by
  intro G _ _ _ hL hR
  classical
  let hl : G → G ≃ₜ G := fun g =>
    { toFun := fun x => g * x, invFun := fun x => g⁻¹ * x,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hL g, continuous_invFun := hL g⁻¹ }
  let hr : G → G ≃ₜ G := fun g =>
    { toFun := fun x => x * g, invFun := fun x => x * g⁻¹,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hR g, continuous_invFun := hR g⁻¹ }
  obtain ⟨x, hx⟩ := exists_unique_pt (1 : G)
  have uniq : ∀ y : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      y ∈ Z → y ∈ W → Z = W := by
    intro y Z hZ W hW hyZ hyW
    have hxy : (hl (x * y⁻¹)) y = x := by
      show x * y⁻¹ * y = x
      simp
    have h := hx _ (comp_image (hl (x * y⁻¹)) hZ) _ (comp_image (hl (x * y⁻¹)) hW)
      ⟨y, hyZ, hxy⟩ ⟨y, hyW, hxy⟩
    exact Set.image_injective.2 (hl (x * y⁻¹)).injective h
  obtain ⟨C, hC, h1C⟩ : ∃ C ∈ irreducibleComponents G, (1 : G) ∈ C :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents 1, mem_irreducibleComponent⟩
  let N : Subgroup G :=
    { carrier := C
      one_mem' := h1C
      mul_mem' := fun {a b} ha hb => by
        have e1 : (hl a) '' C = C := uniq a _ (comp_image (hl a) hC) _ hC
          ⟨1, h1C, by show a * 1 = a; simp⟩ ha
        have h2 : a * b ∈ (hl a) '' C := ⟨b, hb, rfl⟩
        rwa [e1] at h2
      inv_mem' := fun {a} ha => by
        have e1 : (hl a⁻¹) '' C = C := uniq 1 _ (comp_image (hl a⁻¹) hC) _ hC
          ⟨a, ha, by show a⁻¹ * a = 1; simp⟩ h1C
        have h2 : a⁻¹ ∈ (hl a⁻¹) '' C := ⟨1, h1C, by show a⁻¹ * 1 = a⁻¹; simp⟩
        rwa [e1] at h2 }
  have hNC : ∀ y, y ∈ N ↔ y ∈ C := fun y => Iff.rfl
  have hfinQ : Finite (G ⧸ N) := by
    let F : G ⧸ N → irreducibleComponents G :=
      Quotient.lift (fun g => (⟨(hl g) '' C, comp_image (hl g) hC⟩ : irreducibleComponents G))
        (by
          intro a b hab
          have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
          apply Subtype.ext
          exact uniq b _ (comp_image (hl a) hC) _ (comp_image (hl b) hC)
            ⟨a⁻¹ * b, hab', by show a * (a⁻¹ * b) = b; simp⟩ ⟨1, h1C, by show b * 1 = b; simp⟩)
    have hFinj : Function.Injective F := by
      intro p q hpq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have h := congrArg Subtype.val hpq
      change (hl a) '' C = (hl b) '' C at h
      have hb : b ∈ (hl a) '' C := by
        rw [h]
        exact ⟨1, h1C, by show b * 1 = b; simp⟩
      obtain ⟨c, hc, hcb⟩ := hb
      change a * c = b at hcb
      apply QuotientGroup.eq.2
      rw [← hcb, inv_mul_cancel_left]
      exact hc
    haveI : Finite (irreducibleComponents G) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Finite.of_injective F hFinj
  refine ⟨N, ⟨fun n hn g => ?_⟩, Subgroup.finiteIndex_of_finite_quotient,
    isClosed_of_mem_irreducibleComponents C hC, hC.1, fun U hU => ?_⟩
  · have e1 : ((hl g).trans (hr g⁻¹)) '' C = C := uniq 1 _ (comp_image _ hC) _ hC
      ⟨1, h1C, by show g * 1 * g⁻¹ = 1; simp⟩ h1C
    have h2 : g * n * g⁻¹ ∈ ((hl g).trans (hr g⁻¹)) '' C := ⟨n, hn, rfl⟩
    rw [e1] at h2
    exact h2
  · haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    haveI := Fintype.ofFinite (G ⧸ U)
    let S : G ⧸ U → Set G := fun q => {y | y ∈ C ∧ (y : G ⧸ U) = q}
    obtain ⟨z, hz, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hC.1)
      (Finset.univ.image fun q => closure (S q)) (by simp [isClosed_closure]) (by
        intro y hy
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.sUnion_range,
          Set.mem_iUnion]
        exact ⟨(y : G ⧸ U), subset_closure ⟨hy, rfl⟩⟩)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨n, hnC, hnq⟩ : (S q).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, closure_empty] at hCz
      exact hCz h1C
    have hSsub : S q ⊆ (hl n) '' ((U ⊓ N : Subgroup G) : Set G) := by
      rintro y ⟨hyC, hyq⟩
      refine ⟨n⁻¹ * y, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by show n * (n⁻¹ * y) = y; simp⟩
      · exact QuotientGroup.eq.1 (hnq.trans hyq.symm)
      · exact N.mul_mem (N.inv_mem hnC) hyC
    intro y hy
    have h3 : n * y ∈ closure ((hl n) '' ((U ⊓ N : Subgroup G) : Set G)) :=
      closure_mono hSsub (hCz (N.mul_mem hnC hy))
    rw [← Homeomorph.image_closure] at h3
    obtain ⟨k, hk, hky⟩ := h3
    change n * k = n * y at hky
    rwa [mul_left_cancel hky] at hk
end

