module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.StabilizerStdSeqIsoGLOfComplement
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.StabSeq

open scoped Matrix

variable (R : Type) [CommRing R]

theorem padMat_castLE {m n : ℕ} (h : m ≤ n) (A : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (padMat R A : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [padMat, Fin.coe_castLE, i.2, j.2]

theorem stab_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (stab R m n h) := by
  intro g g' e
  ext i j
  have := congrArg (fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j)) e
  simpa [stab, padHom, padMat_castLE] using this

def IsPad (m : ℕ) {n : ℕ} (g : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i k : Fin n, m ≤ (k : ℕ) → g i k = (if i = k then 1 else 0) ∧ g k i = (if k = i then 1 else 0)

theorem padMat_of_isPad {m n : ℕ} (h : m ≤ n) (g : Matrix (Fin n) (Fin n) R) (hg : IsPad R m g) :
    padMat R (Matrix.of fun i j : Fin m => g (Fin.castLE h i) (Fin.castLE h j)) = g := by
  ext i j
  simp only [padMat, Matrix.of_apply]
  split_ifs with h1 h2
  · rfl
  · subst h2
    have : m ≤ (i : ℕ) := by omega
    simpa using ((hg i i this).1).symm
  · by_cases hj : m ≤ (j : ℕ)
    · rw [(hg i j hj).1, if_neg h2]
    · have hi : m ≤ (i : ℕ) := by omega
      rw [(hg j i hi).2, if_neg h2]

theorem mem_range_of_isPad {m n : ℕ} (h : m ≤ n) (g : GL (Fin n) R)
    (hg : IsPad R m (g : Matrix (Fin n) (Fin n) R)) (hg' : IsPad R m ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) :
    g ∈ (stab R m n h).range := by
  set A : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => (g : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j)
  set B : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun i j => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Fin.castLE h i) (Fin.castLE h j)
  have hA : padHom R h A = g := padMat_of_isPad R h _ hg
  have hB : padHom R h B = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := padMat_of_isPad R h _ hg'
  have inj : ∀ X Y : Matrix (Fin m) (Fin m) R, padHom R h X = padHom R h Y → X = Y := by
    intro X Y e
    ext i j
    have := congrArg (fun x : Matrix (Fin n) (Fin n) R => x (Fin.castLE h i) (Fin.castLE h j)) e
    simpa [padHom, padMat_castLE] using this
  have hAB : A * B = 1 := inj _ _ (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hBA : B * A = 1 := inj _ _ (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨A, B, hAB, hBA⟩, Units.ext ?_⟩
  exact hA

theorem isPad_stab {m n : ℕ} (h : m ≤ n) (A : GL (Fin m) R) :
    IsPad R m (stab R m n h A : Matrix (Fin n) (Fin n) R) := by
  intro i k hk
  have : ¬ (k : ℕ) < m := by omega
  constructor
  · rw [stab_apply, dite_eq_right (by tauto)]
  · rw [stab_apply, dite_eq_right (by tauto)]

theorem stdSeq_fixed_iff (n p : ℕ) (h : p ≤ n) (g : GL (Fin n) R) :
    g ∈ MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) ↔
      ∀ j : Fin p, (g : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 =
          Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 ∧
        Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
          Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 := by
  have e : ∀ j : Fin p, (fun k : Fin n => if (k : ℕ) = n - p + j then (1 : R) else 0) =
      Pi.single (⟨n - p + j, by omega⟩ : Fin n) 1 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]
  have key : g • stdSeq R n p h = stdSeq R n p h ↔ (g • stdSeq R n p h).1 = (stdSeq R n p h).1 :=
    ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  rw [MulAction.mem_stabilizer_iff, key, smul_val]
  simp only [stdSeq, stdList, List.map_ofFn, List.ofFn_inj, funext_iff, Function.comp_apply, pairAct,
    Prod.ext_iff, e]

theorem isPad_of_mem (n p : ℕ) (h : p ≤ n) (g : GL (Fin n) R)
    (hg : g ∈ MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h)) :
    IsPad R (n - p) (g : Matrix (Fin n) (Fin n) R) := by
  intro i k hk
  have hf := (stdSeq_fixed_iff R n p h g).1 hg ⟨(k : ℕ) - (n - p), by omega⟩
  have hk' : (⟨n - p + ((k : ℕ) - (n - p)), by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
  simp only [hk'] at hf
  obtain ⟨h1, h2⟩ := hf
  have h3 : Pi.single k 1 ᵥ* (g : Matrix (Fin n) (Fin n) R) = Pi.single k 1 := by
    conv_lhs => rw [← h2]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  constructor
  · have := congrFun h1 i
    rw [Matrix.mulVec_single] at this
    simpa [Pi.single_apply] using this
  · have := congrFun h3 i
    rw [Matrix.single_vecMul] at this
    simpa [Pi.single_apply, eq_comm] using this

theorem range_eq (n p : ℕ) (h : p ≤ n) :
    (stab R (n - p) n (Nat.sub_le n p)).range = MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    rw [stdSeq_fixed_iff]
    intro j
    have hk : n - p ≤ ((⟨n - p + j, by omega⟩ : Fin n) : ℕ) := by simp
    have P := isPad_stab R (Nat.sub_le n p) A
    have Q := isPad_stab R (Nat.sub_le n p) A⁻¹
    rw [map_inv] at Q
    constructor
    · funext i
      rw [Matrix.mulVec_single]
      simp [(P i _ hk).1, Pi.single_apply]
    · rw [Matrix.single_vecMul]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, one_mul, Matrix.row_apply]
      rw [(Q i _ hk).2]
      simp [Pi.single_apply, eq_comm]
  · intro hg
    exact mem_range_of_isPad R _ g (isPad_of_mem R n p h g hg)
      (isPad_of_mem R n p h g⁻¹ (inv_mem hg))

end GlobalTheory.StabSeq

namespace GlobalTheory.StabSeq

theorem stab_injective_range_eq : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p ≤ n), Function.Injective (stab R (n - p) n (Nat.sub_le n p)) ∧ (stab R (n - p) n (Nat.sub_le n p)).range = MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) :=
  fun R _ n p h => ⟨stab_injective R _, range_eq R n p h⟩

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.stabilizer_stdSeq_iso_GL_of_complement : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p ≤ n), Function.Injective (stab R (n - p) n (Nat.sub_le n p)) ∧ (stab R (n - p) n (Nat.sub_le n p)).range = MulAction.stabilizer (GL (Fin n) R) (stdSeq R n p h) := by
  first
  | exact @GlobalTheory.StabSeq.stab_injective_range_eq
  | exact @GlobalTheory.StabSeq.range_eq
  | exact @GlobalTheory.StabSeq.isPad_of_mem
  | exact @GlobalTheory.StabSeq.stdSeq_fixed_iff
  | exact @GlobalTheory.StabSeq.isPad_stab
  | exact @GlobalTheory.StabSeq.mem_range_of_isPad
  | exact @GlobalTheory.StabSeq.padMat_of_isPad
  | exact @GlobalTheory.StabSeq.stab_injective
  | exact @GlobalTheory.StabSeq.padMat_castLE
end
end GlobalTheory.StabSeq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniSeqBasic

theorem perm_lift {α β : Type} (f : α → β) {l l' : List β} (h : l.Perm l') :
    ∀ γ : List α, γ.map f = l → ∃ γ' : List α, γ.Perm γ' ∧ γ'.map f = l' := by
  induction h with
  | nil => intro γ hγ; exact ⟨γ, List.Perm.refl _, hγ⟩
  | cons x _ ih =>
    intro γ hγ
    rcases γ with _ | ⟨a, γ⟩
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      obtain ⟨γ', h1, h2⟩ := ih γ hγ.2
      exact ⟨a :: γ', h1.cons a, by simp [h2, hγ.1]⟩
  | swap x y l =>
    intro γ hγ
    rcases γ with _ | ⟨a, _ | ⟨b, γ⟩⟩
    · simp at hγ
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      exact ⟨b :: a :: γ, List.Perm.swap _ _ _, by simp [hγ.1, hγ.2.1, hγ.2.2]⟩
  | trans _ _ ih1 ih2 =>
    intro γ hγ
    obtain ⟨γ1, p1, e1⟩ := ih1 γ hγ
    obtain ⟨γ2, p2, e2⟩ := ih2 γ1 e1
    exact ⟨γ2, p1.trans p2, e2⟩

def Orth (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a b : M × (M →ₗ[R] R)) : Prop := a.2 b.1 = 0 ∧ b.2 a.1 = 0

theorem orth_symm (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    Symmetric (Orth R M) := fun _ _ h => ⟨h.2, h.1⟩

theorem mem_uniM_iff (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ γ : List (M × (M →ₗ[R] R)), γ.map Prod.fst = l ∧
      (∀ p ∈ γ, p.2 p.1 = 1) ∧ γ.Pairwise (Orth R M) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(List.finRange l.length).map (fun i => (l.get i, f i)), ?_, ?_, ?_⟩
    · apply List.ext_getElem <;> simp
    · intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      simpa using hf i i
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_finRange l.length).imp fun {i j} hij => ?_
      have hne : i ≠ j := ne_of_lt hij
      exact ⟨by simpa [hne] using hf i j, by simpa [hne.symm] using hf j i⟩
  · rintro ⟨γ, rfl, hone, hpw⟩
    refine ⟨fun i => (γ[i.1]'(by simpa using i.2)).2, fun i j => ?_⟩
    have hi : i.1 < γ.length := by simpa using i.2
    have hj : j.1 < γ.length := by simpa using j.2
    rw [List.pairwise_iff_getElem] at hpw
    simp only [List.get_eq_getElem, List.getElem_map]
    split_ifs with hij
    · subst hij
      exact hone _ (List.getElem_mem _)
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact (hpw _ _ hi hj h).1
      · exact (hpw _ _ hj hi h).2

theorem main : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  intro R M _ _ _
  have key : ∀ (ψ : M ≃ₗ[R] M) (l : List M), l ∈ uniM R M → l.map ψ ∈ uniM R M := by
    intro ψ l hl
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    refine (mem_uniM_iff R M _).mpr
      ⟨γ.map (fun p => (ψ p.1, p.2 ∘ₗ (ψ.symm : M →ₗ[R] M))), ?_, ?_, ?_⟩
    · simp [List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa using hone q hq
    · rw [List.pairwise_map]
      refine hpw.imp fun {a b} h => ?_
      simpa [Orth] using h
  refine ⟨?_, ?_, ?_⟩
  · intro l hl l' hsub
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hγ', rfl⟩ := List.sublist_map_iff.mp hsub
    exact (mem_uniM_iff R M _).mpr ⟨γ', rfl, fun p hp => hone p (hγ'.subset hp), hpw.sublist hγ'⟩
  · intro l l' hperm hl
    obtain ⟨γ, hγ, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hp, hm⟩ := perm_lift Prod.fst hperm γ hγ
    exact (mem_uniM_iff R M _).mpr
      ⟨γ', hm, fun p hq => hone p (hp.symm.subset hq), hpw.perm hp (fun {_ _} h => orth_symm R M h)⟩
  · intro ψ l
    constructor
    · intro h
      have := key ψ.symm _ h
      simpa [List.map_map, Function.comp_def] using this
    · exact key ψ l

end GlobalTheory.UniSeqBasic

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniSeqBasic.main
  | exact @GlobalTheory.UniSeqBasic.mem_uniM_iff
  | exact @GlobalTheory.UniSeqBasic.orth_symm
  | exact @GlobalTheory.UniSeqBasic.perm_lift
end
end

