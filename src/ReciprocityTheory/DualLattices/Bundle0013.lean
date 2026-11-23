module

public import ReciprocityTheory.DualLattices.UpSmith
public import ReciprocityTheory.DualLattices.Bundle0009
public import ReciprocityTheory.DualLattices.Bundle0011
public import ReciprocityTheory.DualLattices.Bundle0010
public import ReciprocityTheory.DualLattices.MemDualLat
public import ReciprocityTheory.DualLattices.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.Smith

section general

variable {R : Type} [CommRing R]

def Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))

theorem det_Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : (Vm j0 s).det = 1 := by
  rw [Matrix.det_succ_column (Vm j0 s) j0, Finset.sum_eq_single j0]
  · have hsub : (Vm j0 s).submatrix j0.succAbove j0.succAbove = 1 := by
      ext k l
      simp only [Matrix.submatrix_apply, Vm, Matrix.of_apply, Fin.succAbove_ne, ite_false,
        sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
    rw [hsub, Matrix.det_one]
    simp [Vm, ← two_mul, pow_mul]
  · intro k _ hk
    simp [Vm, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_Vm {m N : ℕ} (X : Matrix (Fin m) (Fin (N + 1)) R) (j0 : Fin (N + 1))
    (s : Fin (N + 1) → R) (i : Fin m) (l : Fin (N + 1)) :
    (X * Vm j0 s) i l = if l = j0 then X i j0 else X i l - s l * X i j0 := by
  classical
  simp only [Matrix.mul_apply, Vm, Matrix.of_apply]
  by_cases hl : l = j0
  · simp [hl]
  · simp only [hl, ite_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

theorem VmT_mul {N n : ℕ} (j0 : Fin (N + 1)) (u : Fin (N + 1) → R) (Y : Matrix (Fin (N + 1)) (Fin n) R)
    (k : Fin (N + 1)) (l : Fin n) :
    ((Vm j0 u)ᵀ * Y) k l = if k = j0 then Y j0 l else Y k l - u k * Y j0 l := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Vm, Matrix.of_apply]
  by_cases hk : k = j0
  · simp [hk]
  · simp only [hk, ite_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']

def piv {N : ℕ} (i0 : Fin (N + 1)) : Equiv.Perm (Fin (N + 1)) :=
  (finSuccEquiv N).trans (finSuccEquiv' i0).symm

theorem piv_zero {N : ℕ} (i0 : Fin (N + 1)) : piv i0 0 = i0 := by
  simp [piv, finSuccEquiv_zero]

theorem piv_succ {N : ℕ} (i0 : Fin (N + 1)) (l : Fin N) : piv i0 l.succ = i0.succAbove l := by
  simp [piv, finSuccEquiv_succ]

def bd1 {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : Matrix (Fin (N + 1)) (Fin (M + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun l => Fin.cases 0 (fun k => P l k) j) i

@[simp] theorem blockOne_zero_zero_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : bd1 P 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (k : Fin M) :
    bd1 P 0 k.succ = 0 := rfl
@[simp] theorem blockOne_succ_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (l : Fin N) (k : Fin M) :
    bd1 P l.succ k.succ = P l k := rfl

theorem det_blockOne_alt {N : ℕ} (P : Matrix (Fin N) (Fin N) R) : (bd1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockOne_zero_zero_alt, blockOne_zero_succ_alt, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one,
    Fin.val_zero, pow_zero, one_mul]
  congr 1

theorem blockOne_mul_mul_blockOne {d n : ℕ} (P : Matrix (Fin d) (Fin d) R) (Cm : Matrix (Fin (d + 1)) (Fin (n + 1)) R)
    (Q : Matrix (Fin n) (Fin n) R) (h0 : ∀ k : Fin n, Cm 0 k.succ = 0)
    (h1 : ∀ l : Fin d, Cm l.succ 0 = 0) :
    (bd1 P * Cm * bd1 Q) 0 0 = Cm 0 0 ∧ (∀ k : Fin n, (bd1 P * Cm * bd1 Q) 0 k.succ = 0) ∧
      (∀ l : Fin d, (bd1 P * Cm * bd1 Q) l.succ 0 = 0) ∧
      ∀ (l : Fin d) (k : Fin n), (bd1 P * Cm * bd1 Q) l.succ k.succ =
        (P * (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) * Q) l k := by
  have bd1_succ_zero {N M : ℕ} (X : Matrix (Fin N) (Fin M) R) (l : Fin N) :
      bd1 X l.succ 0 = 0 := rfl
  have hPC0 : ∀ j : Fin (n + 1), (bd1 P * Cm) 0 j = Cm 0 j := by
    intro j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPCs : ∀ (l : Fin d) (j : Fin (n + 1)), (bd1 P * Cm) l.succ j = ∑ m, P l m * Cm m.succ j := by
    intro l j; simp [Matrix.mul_apply, Fin.sum_univ_succ, bd1_succ_zero]
  refine ⟨?_, fun k => ?_, fun l => ?_, fun l k => ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hPCs, h1, bd1_succ_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [hPCs, blockOne_zero_succ_alt, mul_zero, zero_add, blockOne_succ_succ_alt, Matrix.mul_apply, Matrix.of_apply]

theorem isUnit_det_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) R).det := by
  have h := Matrix.det_permutation (R := R) σ
  simp only [Equiv.Perm.permMatrix] at h
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smith_mat (hv : v.Integers R) : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
    ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
  intro d
  induction d with
  | zero =>
    intro n A
    exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
  | succ d ih =>
    intro n A
    cases n with
    | zero =>
      exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
    | succ n =>
      classical
      set g : Fin (n + 1) → Fin (d + 1) → R := fun j i => A i j with hg
      have hp := exists_pivot (v := v) (b := d) (ι := Fin (n + 1)) hv g
      obtain ⟨i0, a, u, s, hu, -, hs, hz, hnz⟩ := hp
      by_cases ha : a = 0
      · have hA : A = 0 := by
          ext i j
          have := congrFun (hz ha j) i
          simpa [hg] using this
        exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hA]⟩
      · obtain ⟨j0, hj0, hs0⟩ := hnz ha
        have hAj0 : ∀ i, A i j0 = a * u i := fun i => by
          have := congrFun hj0 i
          simpa [hg] using this
        have hAi0 : ∀ l, A i0 l = a * s l := fun l => by
          have := hs l
          simpa [hg] using this
        set B := (Vm i0 u)ᵀ * A * Vm j0 s with hBdef
        have hB : ∀ k l, B k l = if k = i0 then (if l = j0 then a else 0) else
            (if l = j0 then 0 else A k l - s l * (a * u k)) := by
          intro k l
          rw [hBdef, Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hk : k = i0 <;> by_cases hl : l = j0
          · subst hk; subst hl; simp [hAj0, hu]
          · subst hk; simp [hl, hAi0, hs0]; ring
          · subst hl; simp [hk, hAj0, hu]; ring
          · simp [hk, hl, hAj0, hAi0, hu]; ring
        set A'' : Matrix (Fin d) (Fin n) R := Matrix.of fun l k => B (i0.succAbove l) (j0.succAbove k)
        obtain ⟨P'', Q'', a'', hP'', hQ'', hD''⟩ := ih n A''
        set Cm := B.submatrix (piv i0) (piv j0) with hCm
        have hCeq : ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * B * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Cm := by
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have h0 : ∀ k : Fin n, Cm 0 k.succ = 0 := by
          intro k
          simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, ite_true,
            Fin.succAbove_ne, ite_false]
        have h1 : ∀ l : Fin d, Cm l.succ 0 = 0 := by
          intro l
          simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, Fin.succAbove_ne, ite_false,
            ite_true]
        have hsub : (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) = A'' := by
          ext l k
          simp only [hCm, Matrix.of_apply, Matrix.submatrix_apply, piv_succ]
          rfl
        obtain ⟨e00, e0s, es0, ess⟩ := blockOne_mul_mul_blockOne P'' Cm Q'' h0 h1
        refine ⟨bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ,
          Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'', Fin.cons a a'', ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP''.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ''
        · have hfull : bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ * A *
              (Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'') = bd1 P'' * Cm * bd1 Q'' := by
            rw [← hCeq, hBdef]
            simp only [Matrix.mul_assoc]
          intro j k
          rw [hfull]
          refine Fin.cases ?_ (fun l => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
          · rw [e00]
            simp [hCm, piv_zero, hB]
          · rw [e0s]
            simp
          · rw [es0]
            simp
          · rw [ess, hsub, hD'']
            simp [Fin.val_succ]

end ReciprocityTheory.PGsh.Up.Smith
end
end

-- bundled from ReciprocityTheory.DualLattices.ColengthCotangentBoundStatementOfClaim
section
noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def ColengthCotangentValuation (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ AA : HopfOrder (C := C) R N,
    ∃ (n : ℕ) (g : Fin n → N → C) (δ : Fin n → R),
      (∀ i, g i ∈ augIdeal AA.carrier) ∧
      (∀ f ∈ augIdeal AA.carrier, ∃ r : Fin n → R,
        f - ∑ j, r j • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      (∀ i, ∃ a : Fin n → R,
        δ i • g i - ∑ j, (if j < i then a j else 0) • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      ∀ c, HasColen R v AA.carrier c →
        c ^ 2 = (∏ i, v (algebraMap R C (δ i))) ^ Fintype.card N

theorem colengthCotangentBound_of_claim (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) (hcl : ColengthCotangentValuation p C v R)
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (hN : ∀ x : N, p • x = 0)
    (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal)
    (hlen : HasColen R v AA.carrier lenN) (hom : HasLen v R (OmAA AA.carrier) lenOm) :
    lenN ^ 2 ≤ lenOm ^ Fintype.card N := by
  obtain ⟨n, g, δ, hg, hgen, htri, hcol⟩ := hcl N hN AA
  let q := ((sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype).mkQ
  have key : ∀ x z : augIdeal AA.carrier,
      ((x : N → C) - z) ∈ sqIdeal (augIdeal AA.carrier) → q x = q z := by
    intro x z h
    exact (Submodule.Quotient.eq _).mpr (by simpa [Submodule.mem_comap] using h)
  let y : Fin n → OmAA AA.carrier := fun i => q ⟨g i, hg i⟩
  have hy : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨r, hr⟩ := hgen f hf
    have e : q ⟨f, hf⟩ = ∑ j, r j • y j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, ← map_smul, ← map_sum]
      apply key
      simpa using hr
    show q ⟨f, hf⟩ ∈ _
    rw [e]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j := by
    intro i
    obtain ⟨a, ha⟩ := htri i
    refine ⟨a, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, ← map_smul, ← map_sum]
    apply key
    have e2 : (((∑ j, (if j < i then a j else 0) • (⟨g j, hg j⟩ : augIdeal AA.carrier) :
        augIdeal AA.carrier)) : N → C) = ∑ j, (if j < i then a j else 0) • g j := by
      rw [Submodule.coe_sum]
      rfl
    rw [e2]
    exact ha
  have hle := prod_le_of_gen hv hom y hy δ hrel
  rw [hcol lenN hlen]
  first
    | exact pow_le_pow_left₀ zero_le hle _
    | exact pow_le_pow_left zero_le hle _
    | gcongr

theorem colengthCotangentBoundStatement_of_claim (hcl : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 → ColengthCotangentValuation p C v R) : ColengthCotangentBoundStatement := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA lenN lenOm hlen hom
  exact colengthCotangentBound_of_claim p C v R hv (hcl p C v R hv hp) N hN AA lenN lenOm hlen hom

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def sumLat {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) :=
  ⟨Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B), by
    rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Mτ τ).det_ne⟩

lemma sumLat_apply {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (x y : Fin n × Fin s) :
    (sumLat Mτ).B x y = if x.1 = y.1 then (Mτ x.1).B x.2 y.2 else 0 := by
  simp only [sumLat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply]

lemma sumLat_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (c : Fin n × Fin s → C) (τ : Fin n)
    (i : Fin s) : ((sumLat Mτ).B *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
  simp only [Matrix.mulVec, dotProduct, sumLat_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun j _ => if_neg (Ne.symm hb)
  · intro h; exact absurd (Finset.mem_univ τ) h

lemma sumLat_pts {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : (sumLat Mτ).pts = sumPts Mτ := by
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
    funext i
    exact sumLat_mulVec Mτ c τ i
  · intro hw
    choose c hc hwc using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext ⟨τ, i⟩
    rw [sumLat_mulVec]
    exact congrFun (hwc τ) i

lemma freeMat_eq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [freeMat, Matrix.of_apply, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]

lemma det_freeMat {n : ℕ} (a : Fin n → C) (s : ℕ) :
    (freeMat a s).det = (Matrix.vandermonde a).det ^ s := by
  rw [freeMat_eq, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma v_det_vandermonde_sq {n : ℕ} (a : Fin n → C) :
    v (Matrix.vandermonde a).det ^ 2 = v (discr a) := by
  have hsplit : ∀ τ : Fin n, Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
    intro τ
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  have hdisj : ∀ τ : Fin n, Disjoint (Finset.Ioi τ) (Finset.Iio τ) := by
    intro τ
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Finset.mem_Ioi.1 h1) (Finset.mem_Iio.1 h2)
  rw [Matrix.det_vandermonde, discr]
  simp only [map_prod]
  have h1 : ∏ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
      (∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ')) *
        ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => by rw [hsplit τ, Finset.prod_union (hdisj τ)]
  have h2 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') =
      ∏ τ' : Fin n, ∏ τ ∈ Finset.Ioi τ', v (a τ - a τ') :=
    Finset.prod_comm' (by intro x y; simp [Finset.mem_Iio, Finset.mem_Ioi])
  have h3 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ') =
      ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ) :=
    Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => Valuation.map_sub_swap v _ _
  rw [h1, h2, h3, sq]

lemma v_det_freeMat_sq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    v (freeMat a s).det ^ 2 = v (discr a) ^ s := by
  rw [det_freeMat, map_pow, pow_right_comm, v_det_vandermonde_sq]

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsMatOfEquiv
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder

open ReciprocityTheory.PGsh.L2

section Hopf

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def pullHopf {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup X]
    [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) : HopfOrder (C := C) R X where
  carrier := AA.carrier.map (LinearMap.funLeft R C ψ)
  lat := hlat
  le_int := by
    rintro _ ⟨f, hf, rfl⟩ x
    exact AA.le_int hf (ψ x)
  one_mem := ⟨1, AA.one_mem, rfl⟩
  mul_mem := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, AA.mul_mem f g hf hg, rfl⟩
  comul := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← SecondCohomologyLattice.map_tensorSpan (⇑ψ) AA.carrier]
    refine ⟨addPull R N f, AA.comul f hf, ?_⟩
    funext x
    simp [addPull, LinearMap.funLeft_apply, map_add (f := _)]
  antipode := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x => f (-x), AA.antipode f hf, funext fun x => by simp [LinearMap.funLeft_apply]⟩

theorem pullHopf_carrier {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    [AddCommGroup X] [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) :
    (pullHopf ψ AA hlat).carrier = AA.carrier.map (LinearMap.funLeft R C ψ) := rfl

theorem isLat_map_equiv {X K : Type} [Fintype X] [DecidableEq X] {_ : Fintype K} {_ : DecidableEq K}
    (e : X ≃ K) {M : Submodule R (K → C)} (hM : IsLat R M) :
    IsLat R (M.map (LinearMap.funLeft R C e)) := by
  obtain ⟨B, hB, rfl⟩ := hM
  refine ⟨B.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Submodule.map_span, ← Set.range_comp]
  have h1 : (fun j x => (B.submatrix e e) x j) =
      (⇑(LinearMap.funLeft R C e) ∘ fun j x => B x j) ∘ e := by
    funext j x
    rfl
  rw [h1, e.surjective.range_comp]

theorem hopfLat {K : Type} {_ : AddCommGroup K} {_ : Fintype K} {_ : DecidableEq K}
    (A : HopfOrder (C := C) R K) : IsLat R A.carrier := A.lat

theorem isLat_pull (v : Valuation C NNReal) (hv : v.Integers R) {N X : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] [AddCommGroup X] [Fintype X] [DecidableEq X]
    (ψ : X →+ N) (hψ : Function.Injective ψ) (AA : HopfOrder (C := C) R N) :
    IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ)) := by
  classical
  obtain ⟨⟨AK, hAK⟩, -⟩ := h2 C R v hv N ψ.range AA
  let e := AddMonoidHom.ofInjective hψ
  have hmap : (AA.carrier.map (resK ψ.range)).map (LinearMap.funLeft R C e.toEquiv) =
      AA.carrier.map (LinearMap.funLeft R C ψ) := by
    rw [← Submodule.map_comp]
    congr 1
  rw [← hmap, ← hAK]
  exact isLat_map_equiv e.toEquiv (hopfLat AK)

end Hopf

section Split

variable {S : Type} [CommRing S] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

theorem exists_split (e : Matrix n n S) (he : e * e = e) (B : Matrix n k S)
    (hr : LinearMap.range B.mulVecLin = LinearMap.range e.mulVecLin)
    (hk : LinearMap.ker B.mulVecLin = ⊥) : ∃ L : Matrix k n S, L * B = 1 ∧ B * L = e := by
  have hcol : ∀ j : n, ∃ c : k → S, B *ᵥ c = e *ᵥ Pi.single j 1 := by
    intro j
    have hmem : e *ᵥ Pi.single j 1 ∈ LinearMap.range B.mulVecLin := by
      rw [hr]
      exact ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc⟩
  choose c hc using hcol
  let L : Matrix k n S := Matrix.of fun i j => c j i
  have hBL : B * L = e := by
    ext i j
    have h1 := congrFun (hc j) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [← h1]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, L]
  have heB : e * B = B := by
    ext i j
    have hmem : B *ᵥ Pi.single j 1 ∈ LinearMap.range e.mulVecLin := by
      rw [← hr]
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    have h2 : e *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
      rw [← hw]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
    simpa [Matrix.col_apply] using congrFun h2 i
  have hinj : Function.Injective B.mulVecLin := LinearMap.ker_eq_bot.1 hk
  refine ⟨L, ?_, hBL⟩
  ext i j
  have h3 : B *ᵥ ((L * B) *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hBL, heB]
  have h4 : (L * B) *ᵥ Pi.single j 1 = Pi.single j 1 := hinj h3
  rw [Matrix.mulVec_single_one] at h4
  have h5 := congrFun h4 i
  simp only [Matrix.col_apply] at h5
  rw [h5, Matrix.one_apply, Pi.single_apply]

end Split

end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
end
end

