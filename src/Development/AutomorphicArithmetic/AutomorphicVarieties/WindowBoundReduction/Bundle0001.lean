module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.ExistsAlgRepQdetEqSmulOneOfIsReg
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

theorem UpperTheory.exists_algRep_qdet_eq_smul_one_of_isReg :
    ∀ (E : Type) [Field E] [NumberField E] (a D : ℕ), 0 < D → ∀ (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ), IsReg ρ → ∀ s : (E →+* ℂ) → ℂ → ℂ, (∀ τ u, Formalism.REAL.qdet (eOf ρ τ) u = s τ u • 1) → ∃ Ξ : AlgRep E a, ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = s τ u • 1 := by
  intro E _ _ a D hD ρ hreg s hs
  obtain ⟨d, A, B, σ, hd, -, hBA, hσ, hint, hirr⟩ := UpperTheory.V.Weyl.irrSub _ D ρ hD
  have hσreg : IsReg σ := by simpa only [← hσ] using isReg_conj hreg B A
  refine ⟨⟨d, σ, hσreg, hd, hirr⟩, fun τ u => ?_⟩
  have hlie : ∀ i j, eOf ρ τ i j * A = A * eOf σ τ i j := by
    intro i j
    have l := eOf_conj hreg (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have r := eOf_conj hσreg A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, hint] at l r
    exact l.symm.trans r
  have hq := UpperTheory.V.Weyl.qdetRect a D d _ _ A hlie u
  calc Formalism.REAL.qdet (eOf σ τ) u = B * (A * Formalism.REAL.qdet (eOf σ τ) u) := by
        rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
    _ = s τ u • 1 := by
        rw [← hq, hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hBA]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.WindowIntegerGapBound
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

private theorem lift_int (c : ℂ) (m : Multiset ℂ) (h : ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + c) :
    ∃ m' : Multiset ℤ, m = m'.map (fun n : ℤ => (n : ℂ) + c) := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons z m ih =>
    obtain ⟨m', rfl⟩ := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    obtain ⟨n, rfl⟩ := h z (Multiset.mem_cons_self _ _)
    exact ⟨n ::ₘ m', by simp⟩

private theorem gap {a : ℕ} (e : Fin a → ℤ) (he : StrictMono e) (i : Fin a) :
    ∀ (d : ℕ) (j : Fin a), (j : ℕ) = i + d → e i + d ≤ e j := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have : j = i := Fin.ext (by simpa using hj)
    subst this; simp
  | succ d ih =>
    intro j hj
    have hlt : (i : ℕ) + d < a := by have := j.2; omega
    have h1 := ih ⟨i + d, hlt⟩ rfl
    have h2 : e ⟨i + d, hlt⟩ < e j := he (by rw [Fin.lt_def]; simp only; omega)
    push_cast; omega

theorem UpperTheory.window_integer_gap_bound :
    ∀ (a : ℕ) (m : Multiset ℂ), IsRegInt a m → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ ν : Fin a → ℕ, Antitone ν ∧ ∀ u : ℂ, ∏ k : Fin a, (u + ((a : ℂ) - 1) / 2 - (N : ℂ) - (k : ℂ) + (ν k : ℂ)) = ((m.map Neg.neg).map (u + ·)).prod := by
  rintro a m ⟨hc, hn, hz⟩
  obtain ⟨m', rfl⟩ := lift_int _ m hz
  have hn' : m'.Nodup := Multiset.Nodup.of_map _ hn
  let s : Finset ℤ := ⟨m', hn'⟩
  have hs : s.card = a := by simpa [s, Finset.card] using hc
  let e := s.orderEmbOfFin hs
  have hm : m' = (Finset.univ : Finset (Fin a)).val.map e := by
    have := congrArg Finset.val (Finset.map_orderEmbOfFin_univ s hs)
    rw [Finset.map_val] at this
    exact this.symm
  refine ⟨a + ∑ k : Fin a, (e k).toNat, fun N hN => ?_⟩
  have hpos : ∀ k : Fin a, 0 ≤ (N : ℤ) + k + 1 - a - e k := by
    intro k
    have := Finset.single_le_sum (f := fun k : Fin a => (e k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  refine ⟨fun k => ((N : ℤ) + k + 1 - a - e k).toNat, ?_, fun u => ?_⟩
  · intro i j hij
    have h1 := gap e e.strictMono i (j - i) j (by have : (i : ℕ) ≤ j := hij; omega)
    have : (i : ℕ) ≤ j := hij
    simp only
    omega
  · rw [hm, Multiset.map_map, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun k _ => ?_
    have h : ((((N : ℤ) + k + 1 - a - e k).toNat : ℕ) : ℂ) = (N : ℂ) + (k : ℕ) + 1 - a - (e k : ℤ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hpos k)]
      push_cast; ring
    simp only [Function.comp, h]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.WindowLinearEntryEstimate
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

private theorem lin_entry {d D : ℕ} (φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin D) :
    φ A i j = ∑ k, ∑ l, φ (Matrix.single k l 1) i j * A k l := by
  have e : A = ∑ k, ∑ l, A k l • Matrix.single k l (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem UpperTheory.window_linear_entry_estimate :
    ∀ (E : Type) [Field E] [NumberField E] (a d D : ℕ) (φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (M : GL (Fin a) (Cinf E) → Matrix (Fin d) (Fin d) ℂ), IsReg M → IsReg (fun y => φ (M y)) ∧ ∀ τ i j, eOf (fun y => φ (M y)) τ i j = φ (eOf M τ i j) := by
  intro E _ _ a d D φ M h
  refine ⟨fun i j => ?_, ?_⟩
  · have e : (fun y => φ (M y) i j) = ∑ k, ∑ l, (φ (Matrix.single k l 1) i j) • fun y => M y k l := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact lin_entry φ (M y) i j
    rw [e]
    exact Subalgebra.sum_mem _ fun l _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (h l k) _
  · have hd : ∀ X, dOf (fun y => φ (M y)) X = φ (dOf M X) := by
      intro X
      ext i j
      have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
        HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => (h.diff k l).const_mul (φ (Matrix.single k l 1) i j)
      have h2 := h1.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => φ (M y) i j)
        (fun y => by simp only [extGL_val]; exact lin_entry φ (M y) i j) (x := oneL E a) isUnit_one)
      rw [lin_entry φ (dOf M X), dOf, Matrix.of_apply, h2.fderiv]
      simp [dOf]
    intro τ i j
    simp only [eOf, hd, map_smul, map_sub]
end

