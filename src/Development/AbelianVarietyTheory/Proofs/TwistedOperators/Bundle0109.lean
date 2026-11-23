module

public import Mathlib
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonotoneTwoBlockIndicator
section
noncomputable section

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors GlobalTheory.Parabolic GlobalTheory.FiniteGL

namespace GlobalTheory.GoodNoFixed

theorem mem_radical_iff {k : Type} [Field k] {r a : ℕ} {u : GL (Fin r) k} :
    u ∈ radical k r a ↔ u ∈ unipRadical k (blk2 a) := by
  rw [GlobalTheory.FiniteGL.mem_unipRadical]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
  constructor
  · intro h i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_contra hne
    obtain ⟨h1, h2⟩ := h i j hne
    simp only [Formalism.L2.DIV.blk2] at hij
    split_ifs at hij <;> omega
  · intro h i j hne
    by_contra hc
    apply hne
    rw [← sub_eq_zero, ← Matrix.sub_apply]
    apply h
    simp only [Formalism.L2.DIV.blk2]
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := by
        by_contra hj
        exact hc ⟨hi, by omega⟩
      split_ifs <;> omega
    · split_ifs <;> omega

theorem monotone_twoBlockIndicator {r : ℕ} (a : ℕ) : Monotone (blk2 (n := r) a) := by
  intro i j hij
  rw [Fin.le_iff_val_le_val] at hij
  simp only [Formalism.L2.DIV.blk2]
  split_ifs <;> omega

private theorem mem_map_castLEEmb_trans_perm_iff {r a : ℕ} (ha : a ≤ r) (w : Equiv.Perm (Fin r)) (i : Fin r) :
    i ∈ Finset.univ.map ((Fin.castLEEmb ha).trans w.toEmbedding) ↔ (w.symm i : ℕ) < a := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
    Fin.castLEEmb_apply, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [show Fin.castLE ha ⟨(w.symm i : ℕ), h⟩ = w.symm i from Fin.ext rfl]
    simp

theorem exists_union_of_blocks {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ} (hb : Monotone b) {Y : Type} [Zero Y]
    (ρ : blockTri (κ := k) b → Y → Y) (hρ : ∀ q, ρ q 0 = 0)
    (cusp : ∀ S : Finset (Fin r), (∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : Y,
      (∀ u : blockTri (κ := k) b, (∀ i j, ((u : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) i j ≠
        (1 : Matrix (Fin r) (Fin r) k) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → ρ u y = y) → y = 0)
    {a : ℕ} (ha : a ≤ r) (φ : GL (Fin r) k → Y)
    (hl : ∀ (q : blockTri (κ := k) b) (x : GL (Fin r) k), φ (q * x) = ρ q (φ x))
    (hr : ∀ x, ∀ n ∈ radical k r a, φ (x * n) = φ x) (x : GL (Fin r) k) (hx : φ x ≠ 0) :
    ∃ S : Finset (Fin r), S.card = a ∧ ∀ i j, b i = b j → i ∈ S → j ∈ S := by
  obtain ⟨w, p', p, hxe⟩ := GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri k r (blk2 a) b (monotone_twoBlockIndicator a) hb x
  have hy : φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) ≠ 0 := by
    intro h0
    apply hx
    rw [hxe, mul_assoc, hl p', h0, hρ]
  have hS := mem_map_castLEEmb_trans_perm_iff ha w
  refine ⟨Finset.univ.map ((Fin.castLEEmb ha).trans w.toEmbedding), by simp, fun i j hij hi => ?_⟩
  by_contra hj
  apply hy
  refine cusp _ ⟨i, j, hij, hi, hj⟩ _ fun u hu => ?_
  have hm : (GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) * GlobalTheory.Parabolic.permGL k w ∈ radical k r a := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq]
    intro i' j' hne
    have he := GlobalTheory.Parabolic.conj_permGL_apply (k := k) w⁻¹ (u : GL (Fin r) k) (w i') (w j')
    rw [map_inv, inv_inv] at he
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at he
    rw [he] at hne
    have h1 : (1 : Matrix (Fin r) (Fin r) k) (w i') (w j') = (1 : Matrix (Fin r) (Fin r) k) i' j' := by
      by_cases h : i' = j'
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun e => h (w.injective e))]
    rw [← h1] at hne
    obtain ⟨-, hi', hj'⟩ := hu _ _ hne
    rw [hS] at hi' hj'
    simp only [Equiv.symm_apply_apply] at hi' hj'
    exact ⟨hi', not_lt.1 hj'⟩
  have hm' : (p : GL (Fin r) k)⁻¹ * ((GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) *
      GlobalTheory.Parabolic.permGL k w) * (p : GL (Fin r) k) ∈ radical k r a := by
    rw [mem_radical_iff] at hm ⊢
    have hn := GlobalTheory.Parabolic.blockTri_le_normalizer (k := k) (blk2 (n := r) a) (Subgroup.inv_mem _ p.2)
    have := (Subgroup.mem_normalizer_iff.1 hn _).1 hm
    simpa only [inv_inv, SetLike.mem_coe] using this
  calc ρ u (φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)))
      = φ ((u : GL (Fin r) k) * (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k))) := (hl u _).symm
    _ = φ ((GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) * ((p : GL (Fin r) k)⁻¹ *
        ((GlobalTheory.Parabolic.permGL k w)⁻¹ * (u : GL (Fin r) k) * GlobalTheory.Parabolic.permGL k w) *
        (p : GL (Fin r) k))) := by congr 1; group
    _ = φ (GlobalTheory.Parabolic.permGL k w * (p : GL (Fin r) k)) := hr _ _ hm'

theorem card_eq_sum_blocks {r : ℕ} {ι : Type} [DecidableEq ι] (b : Fin r → ι) (S : Finset (Fin r))
    (hS : ∀ i j, b i = b j → i ∈ S → j ∈ S) :
    S.card = ∑ c ∈ S.image b, (Finset.univ.filter fun i => b i = c).card := by
  rw [Finset.card_eq_sum_card_image b S]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro hj
  exact hS i j hj.symm hi

theorem fixedVectorBlocks : FixedVectorBlocks := by
  intro k _ _ r b W _ _ ρ hc V _ _ τ hsub a ha0 har hnf
  obtain ⟨T, hTi, hT⟩ := hsub
  unfold NoFixed at hnf
  push Not at hnf
  obtain ⟨v, hv, hv0⟩ := hnf
  have hTv : T v ≠ 0 := fun h => hv0 (hTi (h.trans (map_zero T).symm))
  obtain ⟨y, hy⟩ : ∃ y, ((T v : _) : GL (Fin r) k → W) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hTv (Subtype.ext (funext hcon))
  have hl : ∀ (q : blockTri (κ := k) b) (z : GL (Fin r) k),
      ((T v : _) : GL (Fin r) k → W) (q * z) = ρ q (((T v : _) : GL (Fin r) k → W) z) :=
    fun q z => (T v).2 q z
  have hr : ∀ z, ∀ n ∈ radical k r a, ((T v : _) : GL (Fin r) k → W) (z * n) = ((T v : _) : GL (Fin r) k → W) z := by
    intro z n hn
    have h1 := LinearMap.congr_fun (hT n) v
    simp only [LinearMap.comp_apply] at h1
    rw [hv n hn] at h1
    have h2 := congrFun (congrArg Subtype.val h1) z
    exact h2.symm
  obtain ⟨S, hS, hU⟩ := exists_union_of_blocks (k := k) hc.mono (Y := W) (fun q w => ρ q w)
    (fun q => map_zero _) hc.cusp (le_of_lt har) _ hl hr y hy
  refine ⟨S.image b, Finset.image_subset_image (Finset.subset_univ _), ?_⟩
  rw [← hS, card_eq_sum_blocks b S hU]
  simp only [Fintype.card_subtype]

theorem map_mem_radical {k k' : Type} [CommRing k] [CommRing k'] (e : k →+* k') {r a : ℕ} {u : GL (Fin r) k}
    (hu : u ∈ radical k r a) : Matrix.GeneralLinearGroup.map e u ∈ radical k' r a := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical, Set.mem_ofPred_eq] at hu ⊢
  intro i j hij
  apply hu i j
  intro heq
  apply hij
  rw [Matrix.GeneralLinearGroup.map_apply]
  rw [heq]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem sum_character_eq_zero_iff {H V : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ H V) : ∑ h, τ.character h = 0 ↔ ∀ x : V, (∀ h, τ h x = x) → x = 0 := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard
  have h := τ.card_inv_mul_sum_char_eq_finrank
  constructor
  · intro hs x hx
    rw [hs, mul_zero] at h
    have h0 : Module.finrank ℂ τ.invariants = 0 := by exact_mod_cast h.symm
    have hb : τ.invariants = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hxm : x ∈ τ.invariants := (τ.mem_invariants x).2 hx
    rw [hb] at hxm
    exact (Submodule.mem_bot ℂ).1 hxm
  · intro hx
    have hb : τ.invariants = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun x hxm => hx x ((τ.mem_invariants x).1 hxm)
    rw [hb, finrank_bot, Nat.cast_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hcard)

theorem noFixed_iff_sum {k : Type} [Field k] {r a : ℕ} [Fintype (unipRadical k (blk2 (n := r) a))] {G V : Type} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ G V) (ι : GL (Fin r) k →* G) :
    NoFixed τ (ι '' radical k r a) ↔ ∑ u : unipRadical k (blk2 (n := r) a), τ.character (ι u) = 0 := by
  refine Iff.trans ?_ (sum_character_eq_zero_iff (τ.comp (ι.comp (unipRadical k (blk2 (n := r) a)).subtype))).symm
  unfold NoFixed
  refine forall_congr' fun x => imp_congr_left ⟨fun hx h => hx _ ⟨h, mem_radical_iff.2 h.2, rfl⟩, ?_⟩
  rintro hx _ ⟨u, hu, rfl⟩
  exact hx ⟨u, mem_radical_iff.1 hu⟩

end GlobalTheory.GoodNoFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

noncomputable def topVec (r : ℕ) (lam : DomWeight r) : nablaSq ℂ r lam :=
  ⟨extremal ℂ r lam, hwMem ℂ r r le_rfl _ (factNatW r lam).1⟩

theorem sqRep_topVec_of_unitriangular (r : ℕ) (lam : DomWeight r) (g : GL (Fin r) ℂ)
    (h1 : (g : Matrix (Fin r) (Fin r) ℂ).BlockTriangular id) (h2 : ∀ a, (g : Matrix (Fin r) (Fin r) ℂ) a a = 1) :
    sqRep ℂ r lam g (topVec r lam) = topVec r lam :=
  Subtype.ext ((factSqHighestWeight ℂ r lam).2 g h1 h2)

theorem sqRep_topVec_diag {m : ℕ} (r : ℕ) (a : Part m) (t : Fin r → ℂˣ) :
    sqRep ℂ r (pad r a) (diagGL ℂ r t) (topVec r (pad r a)) =
      (∏ i, (t i : ℂ) ^ rowNu (r := r) a.1 i) • topVec r (pad r a) := by
  apply Subtype.ext
  have h := (factSqHighestWeight ℂ r (pad r a)).1 t
  have e : ((∏ i, t i ^ (pad r a).w i : ℂˣ) : ℂ) = ∏ i, (t i : ℂ) ^ rowNu (r := r) a.1 i := by
    simp [pad]
  rw [e] at h
  exact h

theorem exists_intertwining_piece (n n' : ℕ) (a : Part (min n n')) :
    ∃ φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
      (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))),
      φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a)) ≠ 0 := by
  obtain ⟨T, hT⟩ := GlobalTheory.Proof.GenericSubmoduleMonomials.exists_pairing n n' (min n n')
  obtain ⟨hE, hN⟩ := GlobalTheory.GLDuality.pairing_equivariant_and_ne_zero n n' (min n n') T hT
  obtain ⟨j, hj, hj0⟩ := GlobalTheory.GLDuality.exists_map_nablaSq_pad n (min n n') (min_le_left _ _) a
  obtain ⟨j', hj', hj0'⟩ := GlobalTheory.GLDuality.exists_map_nablaSq_pad n' (min n n') (min_le_right _ _) a
  refine ⟨⟨TensorProduct.lift (T.compl₁₂ j j'), fun p => ?_⟩, ?_⟩
  · apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, pieceRep_tmul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change T (j (sqRep ℂ n _ p.1 v)) (j' (sqRep ℂ n' _ p.2 w)) = matRep n n' (p.1, p.2) (T (j v) (j' w))
    rw [hj, hj', hE]
  · change T (j _) (j' _) ≠ 0
    rw [hj0 _ rfl, hj0' _ rfl]
    exact hN _ _ _

theorem map_topVec_highest (n n' : ℕ) (a : Part (min n n'))
    (φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
      (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)))) :
    φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a)) ∈ dualWeyl ℂ n' n (rowNu (r := n) a.1) ∧
      ∀ i j : Fin n', i < j → ∀ k : ℕ, 1 ≤ k →
        rowDiv ℂ i j k (φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a))) = 0 := by
  have hφ : ∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) v w, matRep n n' (g, h) (φ (v ⊗ₜ w)) =
      φ (sqRep ℂ n _ g v ⊗ₜ sqRep ℂ n' _ h w) := fun g h v w => by
    have := Representation.IntertwiningMap.isIntertwining _ _ φ (g, h) (v ⊗ₜ w)
    rw [pieceRep_tmul] at this
    exact this.symm
  refine ⟨GlobalTheory.GLDuality.mem_dualWeyl_of_unitriangular_fixed n n' _ _ (fun g h1 h2 => ?_) (fun t => ?_), GlobalTheory.GLDuality.rowDiv_eq_zero_of_matRep_unipotent_fixed n n' _ fun g h1 h2 => ?_⟩
  · rw [hφ, sqRep_topVec_of_unitriangular _ _ g h1 h2, map_one, Module.End.one_apply]
  · rw [hφ, sqRep_topVec_diag, map_one, Module.End.one_apply, ← TensorProduct.smul_tmul', map_smul]
  · rw [hφ, sqRep_topVec_of_unitriangular _ _ g h1 h2, map_one, Module.End.one_apply]

theorem colAdd_matRep_diag {n n' : ℕ} (t : Fin n → ℂˣ) (l j : Fin n) (c : ℂ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    colAdd ℂ l j c (matRep n n' (diagGL ℂ n t, 1) v) =
      matRep n n' (diagGL ℂ n t, 1) (colAdd ℂ l j (c * t j * (t l)⁻¹) v) := by
  have hX : ∀ (a : Fin n') (s : Fin n),
      sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ
        (X (a, s)) = C (t s : ℂ) * X (a, s) := by
    intro a s
    rw [← matRep_apply, matRep_X]
    simp [diagGL, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  have e : (colAdd ℂ (r := n') l j c).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ).comp
        (colAdd ℂ l j (c * t j * (t l)⁻¹)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hX]
    by_cases hs : s = j
    · subst hs
      simp only [colAdd, map_mul, algHom_C, aeval_X, if_true, map_add (f := _), hX, algebraMap_eq]
      have : (C ((t l)⁻¹ : ℂ) : MvPolynomial (Fin n' × Fin n) ℂ) * C (t l : ℂ) = 1 := by
        rw [← map_mul]; simp
      simp only [Units.val_inv_eq_inv_val] at this ⊢
      linear_combination (-(C c * C (t s : ℂ) * X (a, l))) * this
    · simp only [colAdd, map_mul, algHom_C, aeval_X, if_neg hs, hX, algebraMap_eq]
  exact DFunLike.congr_fun e v

theorem exists_mem_dualWeyl_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), v ∈ N ∧ v ≠ 0 ∧ v ∈ dualWeyl ℂ n' n ν := by
  classical
  obtain ⟨v, hv, hv0, hf⟩ := GlobalTheory.GLDuality.exists_colAdd_fixed_of_stable n n' N hN hst
  let M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ) :=
    { carrier := {w | w ∈ N ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c w = w}
      add_mem' := fun ha hb => ⟨N.add_mem ha.1 hb.1, fun l j h c => by rw [map_add (f := _), ha.2 l j h, hb.2 l j h]⟩
      zero_mem' := ⟨N.zero_mem, fun l j h c => map_zero _⟩
      smul_mem' := fun a _ ha => ⟨N.smul_mem a ha.1, fun l j h c => by rw [map_smul, ha.2 l j h]⟩ }
  have hM : ∀ t : Fin n → ℂˣ, ∀ w ∈ M, matRep n n' (diagGL ℂ n t, 1) w ∈ M := fun t w hw =>
    ⟨hst _ w hw.1, fun l j h c => by rw [colAdd_matRep_diag, hw.2 l j h]⟩
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hv0
  have hw := GlobalTheory.GLDuality.weightedHomogeneousComponent_colW_mem n n' M hM (Finsupp.weight (colW n' n) d) v ⟨hv, hf⟩
  refine ⟨_, _, hw.1, ne_zero_iff.2 ⟨d, ?_⟩, (dualWeylPoint ℂ n' n _ _).2
    ⟨weightedHomogeneousComponent_isWeightedHomogeneous _ _, hw.2⟩⟩
  rwa [coeff_weightedHomogeneousComponent, if_pos rfl]

theorem exists_highest_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ N, matRep n n' p v ∈ N) :
    ∃ (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), v ∈ N ∧ v ≠ 0 ∧ v ∈ dualWeyl ℂ n' n ν ∧
      ∀ i j : Fin n', i < j → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ i j k v = 0 := by
  obtain ⟨ν, v, hv, hv0, hvd⟩ := exists_mem_dualWeyl_of_stable n n' N hN fun g => hst (g, 1)
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n') ℂ, ∀ f ∈ N ⊓ dualWeyl ℂ n' n ν,
      rowAct ℂ u f ∈ N ⊓ dualWeyl ℂ n' n ν := by
    intro u hu f hf
    refine ⟨?_, dualWeylRowStable ℂ n' n ν u f hf.2⟩
    have h1 := hst (1, unitaryIncl n' (Matrix.UnitaryGroup.transpose ⟨u, hu⟩)) f hf.1
    rw [matRep_one_left] at h1
    exact h1
  obtain ⟨w, hw, hw0, hk⟩ := exists_killed_of_rowDivClosed _
    (rowDivClosed_of_rowAct_stable _ (rowAct_mem_of_unitary_stable _ hU))
    (fun e => hv0 ((Submodule.eq_bot_iff _).1 e v ⟨hv, hvd⟩))
  exact ⟨ν, w, hw.1, hw0, hw.2, hk⟩

theorem nonempty_equiv_polyRep (n n' : ℕ) :
    Nonempty ((Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).Equiv
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)))) := by
  classical
  have h1 := irreducibleDistinct_gl (min_le_left n n')
  have h2 := irreducibleDistinct_gl (min_le_right n n')
  have hirr : ∀ a : Part (min n n'),
      (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IsIrreducible :=
    fun a => GlobalTheory.OuterTensor.isIrreducible_outer_tprod _ _ _ _ _ _ (h1.1 a) (h2.1 a)
  have hdis : ∀ a b : Part (min n n'), a ≠ b →
      ∀ φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
        (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) b), φ = 0 := by
    intro a b hab
    refine GlobalTheory.outerTensor_intertwining_eq_zero_of_left _ _ _ _ _ _ _ _ _ _ fun ψ => ?_
    have := h1.1 a
    have := h1.1 b
    refine (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_left fun hb => hab (h1.2 a b ?_)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ.toLinearMap hb) ψ.isIntertwining'⟩
  choose φ hφ using exists_intertwining_piece n n'
  let Φ : (Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))) :=
    ⟨DirectSum.toModule ℂ _ _ (fun i => (φ i).toLinearMap), fun g => by
      refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun v => ?_
      simp [(φ i).isIntertwining]⟩
  have hΦ : ∀ i v, Φ (DirectSum.lof ℂ _ _ i v) = φ i v := fun i v =>
    DirectSum.toModule_lof ℂ (φ := fun i => (φ i).toLinearMap) i v
  have hinj : Function.Injective Φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine GlobalTheory.directSum_eq_zero_of_toModule_eq_zero _ _ hirr hdis Φ ?_ (DFinsupp.support x) x
      (fun j hj => DFinsupp.notMem_support_iff.1 hj) hx
    intro i v hv
    have := hirr i
    have hi := (Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right
      (fun e => hφ i (by rw [e]; rfl))
    apply hi
    rw [← hΦ, hv, map_zero]
  have hsurj : Function.Surjective Φ.toLinearMap := by
    rw [← LinearMap.range_eq_top]
    by_contra hM
    obtain ⟨N, hN, hNM, hst⟩ := GlobalTheory.GLDuality.Compl.exists_stable_disjoint n n' _ hM (by
      rintro p _ ⟨x, rfl⟩
      exact ⟨_, Representation.IntertwiningMap.isIntertwining _ _ Φ p x⟩)
    obtain ⟨ν, v, hv, hv0, hvd, hk⟩ := exists_highest_of_stable n n' N hN hst
    obtain ⟨a, rfl⟩ := (GlobalTheory.GLDuality.HighestLine.highest_line n' n ν v hvd hk hv0).1
    obtain ⟨ht1, ht2⟩ := map_topVec_highest n n' a (φ a)
    obtain ⟨c, hc⟩ := (GlobalTheory.GLDuality.HighestLine.highest_line n' n _ _ ht1 ht2 (hφ a)).2 v hvd hk
    refine hv0 ((Submodule.eq_bot_iff _).1 hNM v ⟨hv, ?_⟩)
    rw [hc]
    exact Submodule.smul_mem _ _ ⟨_, hΦ a _⟩
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩) Φ.isIntertwining'⟩

end GlobalTheory.GLDuality

theorem GlobalTheory.Published.glHoweDuality_holds : GlobalTheory.Published.GLHoweDuality :=
  GlobalTheory.Published.glHoweDuality_of_equiv fun n n' _ _ => GlobalTheory.GLDuality.nonempty_equiv_polyRep n n'
end

