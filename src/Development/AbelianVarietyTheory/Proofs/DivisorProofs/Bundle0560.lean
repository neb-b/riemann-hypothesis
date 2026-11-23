module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPointedEtaleNeighbourhoodEqMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspace
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem exists_eigenvector_of_stable {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : (ι → F) → V →ₗ[ℂ] V) (h0 : T 0 = LinearMap.id) (hT : ∀ x x' v, T x (T x' v) = T (x + x') v)
    (W : Submodule ℂ V) (hW : ∀ x, ∀ v ∈ W, T x v ∈ W) (hne : W ≠ ⊥) :
    ∃ l : ι → F, ∃ w ∈ W, w ≠ 0 ∧ ∀ x, T x w = ψ (∑ i, l i * x i) • w := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
  let w : (ι → F) → V := fun l => ∑ x : ι → F, ψ (-∑ i, l i * x i) • T x v
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have hs : ∀ x : ι → F, x ≠ 0 → ∑ l : ι → F, ψ (-∑ i, l i * x i) = 0 := by
    intro x hx
    have e : ∀ l : ι → F, ψ (-∑ i, l i * x i) = ∏ i, ψ (l i * (-x i)) := by
      intro l
      rw [← Finset.sum_neg_distrib]
      simp only [mul_neg]
      induction (Finset.univ : Finset ι) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    simp only [e]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun i t => ψ (t * (-x i)))]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := AddChar.sum_mulShift (ψ := ψ) (-x i) hprim
    rw [if_neg (by simpa using hi)] at this
    simpa using this
  have hsum : ∑ l, w l = (Fintype.card (ι → F) : ℂ) • v := by
    simp only [w]
    rw [Finset.sum_comm, Finset.sum_eq_single (0 : ι → F)]
    · simp [h0, Nat.cast_smul_eq_nsmul, -Fintype.card_pi]
    · intro x _ hx
      rw [← Finset.sum_smul, hs x hx, zero_smul]
    · simp
  have hex : ∃ l, w l ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero fun l _ => hc l] at hsum
    rcases smul_eq_zero.1 hsum.symm with h | h
    · exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h
    · exact hv0 h
  obtain ⟨l, hl⟩ := hex
  refine ⟨l, w l, W.sum_mem fun x _ => W.smul_mem _ (hW x v hv), hl, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [w, map_sum, map_smul, hT, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun z => ?_
  simp only [Equiv.coe_addLeft, ← AddChar.map_add_eq_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 2
  ring

variable {F : Type} [Field F] {r : ℕ}

def colMat (k : Fin r) (x : Fin r → F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if i < k ∧ j = k then x i else 0

theorem colMat_mul_apply (k : Fin r) (x : Fin r → F) (M : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    (colMat k x * M) i j = if i < k then x i * M k j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · by_cases h : i < k <;> simp [colMat, h]
  · intro m _ hm
    simp [colMat, hm]
  · simp

theorem one_add_colMat_mul (k : Fin r) (x x' : Fin r → F) :
    (1 + colMat k x) * (1 + colMat k x') = 1 + colMat k (x + x') := by
  have : colMat k x * colMat k x' = 0 := by
    ext i j
    rw [colMat_mul_apply]
    simp [colMat]
  have h2 : colMat k (x + x') = colMat k x + colMat k x' := by
    ext i j
    simp only [colMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h2, add_mul, mul_add, mul_add, this]
  simp only [one_mul, mul_one]
  abel

theorem colMat_zero (k : Fin r) : colMat k (0 : Fin r → F) = 0 := by
  ext i j
  simp [colMat]

def colGL (k : Fin r) (x : Fin r → F) : GL (Fin r) F where
  val := 1 + colMat k x
  inv := 1 + colMat k (-x)
  val_inv := by rw [one_add_colMat_mul]; simp [colMat_zero]
  inv_val := by rw [one_add_colMat_mul]; simp [colMat_zero]

theorem colGL_mem_unip (k : Fin r) (x : Fin r → F) : colGL k x ∈ unip F r := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    have : ¬ (i < k ∧ j = k) := fun h => by
      obtain ⟨h1, rfl⟩ := h
      exact lt_asymm h1 hij'
    simp [colGL, colMat, this, Matrix.one_apply_ne hij'.ne']
  · have : ¬ (i < k ∧ i = k) := fun h => h.1.ne h.2
    simp [colGL, colMat, this]

def colEl {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) : blockTri (κ := F) b :=
  ⟨colGL k x, fun i j hij => (colGL_mem_unip k x).1 (show j < i from hb.reflect_lt hij)⟩

theorem colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) :
    ((colEl hb k x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + colMat k x := rfl

theorem colEl_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x x' : Fin r → F) :
    colEl hb k x * colEl hb k x' = colEl hb k (x + x') :=
  Subtype.ext (Units.ext (one_add_colMat_mul k x x'))

theorem colEl_zero {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) : colEl hb k (0 : Fin r → F) = 1 :=
  Subtype.ext (Units.ext (by rw [colEl_val, colMat_zero]; simp))

theorem colEl_neg_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b k.val)
    (hx : ∀ i, i < k → x i = ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k) :
    colEl hb k (-x) * u ∈ colSet F b (k.val + 1) ∧
      edgeSum (blkEdge b) ((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) =
        edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
  have e : ∀ i j, (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j +
        if i < k then -x i * ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k j else 0 := by
    intro i j
    rw [Subgroup.coe_mul, Units.val_mul, colEl_val, add_mul, one_mul, Matrix.add_apply, colMat_mul_apply]
    rfl
  have hc : ∀ i j : Fin r, j.val < k.val + 1 →
      (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
        (1 : Matrix (Fin r) (Fin r) F) i j := by
    intro i j hj
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [hu.2 i j h, hu.2 k j h, Matrix.one_apply_ne (i := k) (j := j) (fun h' => by simp [h'] at h)]
      simp
    · obtain rfl : j = k := Fin.ext h
      rw [hu.1.2 j]
      rcases lt_trichotomy i j with h' | h' | h'
      · rw [if_pos h', hx i h', Matrix.one_apply_ne h'.ne]; ring
      · subst h'; simp [hu.1.2 i]
      · rw [if_neg (lt_asymm h'), hu.1.1 (show j.val < i.val from h'), Matrix.one_apply_ne h'.ne']; simp
  refine ⟨⟨(unip F r).mul_mem (colGL_mem_unip k (-x)) hu.1, hc⟩, ?_⟩
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : blkEdge b i j
  · have h1 := hij.1
    by_cases hk : k < j
    · have : ¬ i < k := by rw [Fin.lt_def] at hk ⊢; omega
      rw [if_pos hij, if_pos ⟨hij, hk⟩, e, if_neg this, add_zero]
    · rw [if_pos hij, if_neg (fun h => hk h.2), hc i j (by rw [Fin.lt_def] at hk; omega),
        Matrix.one_apply_ne (fun h' => by simp [h'] at h1)]
  · rw [if_neg hij, if_neg (fun h => hij h.1)]

theorem mul_colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b (k.val + 1)) (i j : Fin r) :
    (((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j + if i < k ∧ j = k then x i else 0 := by
  rw [Subgroup.coe_mul, Units.val_mul, colEl_val, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  have : ∀ m, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i m * colMat k x m j =
      (1 : Matrix (Fin r) (Fin r) F) i m * colMat k x m j := by
    intro m
    by_cases hm : m < k
    · rw [hu.2 i m (by rw [Fin.lt_def] at hm; omega)]
    · simp [colMat, hm]
  simp only [this]
  rw [← Matrix.mul_apply, one_mul]
  rfl

theorem colEl_stable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar F ℂ) {b : Fin r → ℕ} (hb : Monotone b)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (x : Fin r → F) (v : V)
    (hv : v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F)))) :
    σ (colEl hb k x) v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  rw [mem_eig] at hv ⊢
  intro u hu
  have hu' : u ∈ colSet F b k.val := ⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩
  have hm : u * colEl hb k x ∈ colSet F b k.val := by
    refine ⟨(unip F r).mul_mem hu.1 (colGL_mem_unip k x), fun i j hj => ?_⟩
    rw [mul_colEl_val hb k x hu, hu.2 i j (by omega), if_neg (fun h => by simp [h.2] at hj), add_zero]
  obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hm (fun i hi => by
    rw [mul_colEl_val hb k x hu, hu.2 i k (by omega), if_pos ⟨hi, rfl⟩, Matrix.one_apply_ne hi.ne, zero_add])
  obtain ⟨-, h3⟩ := colEl_neg_mul hb k 0 hu' (fun i hi => by
    rw [hu.2 i k (by omega), Matrix.one_apply_ne hi.ne]; rfl)
  rw [neg_zero, colEl_zero, one_mul] at h3
  have h4 : edgeSum (fun i j => blkEdge b i j ∧ k < j) ((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) =
      edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
    unfold edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [mul_colEl_val hb k x hu, if_neg (fun h' => h.2.ne' h'.2), add_zero]
    · rfl
  have h5 := hv _ h1
  rw [h2, h4, ← h3] at h5
  have h6 : u * colEl hb k x = colEl hb k x * (colEl hb k (-x) * (u * colEl hb k x)) := by
    rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
  rw [← Module.End.mul_apply, ← map_mul, h6, map_mul, Module.End.mul_apply, h5, map_smul]

theorem exists_colChar_eig_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  intro F _ _ ψ hψ r V _ _ b σ hb hinf k hne
  obtain ⟨l, w, hw, hw0, hl⟩ := exists_eigenvector_of_stable ψ hψ (fun x => σ (colEl hb k x))
    (by rw [colEl_zero, map_one]; rfl)
    (fun x x' v => by rw [← Module.End.mul_apply, ← map_mul, colEl_mul]) _
    (fun x v hv => colEl_stable ψ hb σ k x v hv) hne
  refine ⟨l, fun i hi => ?_, (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩⟩
  · by_contra hc
    refine AddChar.IsPrimitive.of_ne_one hψ hi (AddChar.ext _ _ fun t => ?_)
    have h1 : σ (colEl hb k (Pi.single i t)) = 1 := by
      refine hinf _ fun a c hac => ?_
      rw [colEl_val, Matrix.add_apply, add_eq_left]
      simp only [colMat, Matrix.of_apply]
      split_ifs with h
      · refine Pi.single_eq_of_ne (fun h' => hc ?_) _
        rw [← h', hac, h.2]
        exact ⟨h.2 ▸ h.1, rfl⟩
      · rfl
    have h2 := hl (Pi.single i t)
    rw [h1, Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), Pi.single_eq_same] at h2
    have h3 : (ψ (l i * t) - 1) • w = 0 := by rw [sub_smul, ← h2]; simp
    have h4 := (smul_eq_zero.1 h3).resolve_right hw0
    simpa [sub_eq_zero] using h4
  · rw [mem_eig] at hw ⊢
    intro u hu
    set x : Fin r → F := fun i => ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k with hx
    obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hu (fun i _ => rfl)
    have h5 := hw _ h1
    rw [h2] at h5
    have h6 : u = colEl hb k x * (colEl hb k (-x) * u) := by
      rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
    calc σ u w = σ (colEl hb k x) (σ (colEl hb k (-x) * u) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← h6]
      _ = _ := by
          rw [h5, map_smul, hl x, smul_smul, colChar, AddChar.map_add_eq_mul, mul_comm]

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHenselisation
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem exists_henselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := _root_.GlobalTheory.Henselisation.etNbhd_isDirected R
  obtain ⟨hloc, hofloc⟩ := _root_.GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of R
  haveI : HenselianLocalRing (Hens R) := _root_.GlobalTheory.Henselisation.henselianLocalRing_hens R
  let ofA : ∀ i : EtNbhd R, i.B →ₐ[R] Hens R := fun i =>
    { toRingHom := Hens.of i, commutes' := _root_.GlobalTheory.Henselisation.Hens.of_algebraMap R i }
  have hof_trans : ∀ {i j : EtNbhd R} (h : i ≤ j) (x : i.B),
      Hens.of j (EtNbhd.trans h x) = Hens.of i x := fun h x => Ring.DirectLimit.of_f h x
  have hexists : ∀ s : Hens R, ∃ i b, Hens.of i b = s := fun s => Ring.DirectLimit.exists_of s
  have hlocB : ∀ i : EtNbhd R, IsLocalHom (algebraMap R i.B) := fun i => ⟨fun r hr => by
    by_contra hn
    have hm : algebraMap R i.B r ∈ maximalIdeal i.B := by
      rw [_root_.GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map R i]; exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).2 hn)
    exact (mem_maximalIdeal _).1 hm hr⟩
  haveI : IsLocalHom (algebraMap R (Hens R)) := by
    have e : algebraMap R (Hens R) =
        (Hens.of EtNbhd.base).comp (algebraMap R (EtNbhd.base (R := R)).B) := rfl
    rw [e]
    haveI := hlocB EtNbhd.base
    haveI := hofloc EtNbhd.base
    infer_instance
  have hmax : (maximalIdeal R).map (algebraMap R (Hens R)) = maximalIdeal (Hens R) := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (algebraMap R (Hens R)) r hr
    · intro s hs
      obtain ⟨i, b, rfl⟩ := hexists s
      have hb : b ∈ maximalIdeal i.B := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (mem_maximalIdeal _).1 hs (hu.map (Hens.of i))
      rw [_root_.GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map R i] at hb
      have hm := Ideal.mem_map_of_mem (Hens.of i) hb
      rwa [Ideal.map_map, show (Hens.of i).comp (algebraMap R i.B) = algebraMap R (Hens R) from
        RingHom.ext (_root_.GlobalTheory.Henselisation.Hens.of_algebraMap R i)] at hm
  have hres : Function.Bijective (ResidueField.map (algebraMap R (Hens R))) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨s, rfl⟩ := residue_surjective y
    obtain ⟨i, b, rfl⟩ := hexists s
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal R i b
    refine ⟨residue R r, ?_⟩
    rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero,
      ← (residue (Hens R)).map_sub, residue_eq_zero_iff,
      ← _root_.GlobalTheory.Henselisation.Hens.of_algebraMap R i r, ← (Hens.of i).map_sub]
    exact map_nonunit (Hens.of i) _ hr
  refine ⟨Hens R, inferInstance, inferInstance, inferInstance, inferInstance, _root_.GlobalTheory.Henselisation.flat_hens R, hmax, hres,
    EtNbhd R, inferInstance, inferInstance, inferInstance, fun i => (ofA i).range, ?_, ?_, ?_⟩
  · intro i j h y hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).1 hy
    exact (AlgHom.mem_range _).2 ⟨EtNbhd.trans h x, hof_trans h x⟩
  · intro s
    obtain ⟨i, b, rfl⟩ := hexists s
    exact ⟨i, (AlgHom.mem_range _).2 ⟨b, rfl⟩⟩
  · intro i
    exact ⟨i.A, inferInstance, inferInstance, inferInstance, i.q, inferInstance,
      ⟨AlgEquiv.ofInjective (ofA i) (_root_.GlobalTheory.Henselisation.Hens.of_injective_of_nbhd R i)⟩⟩

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomain
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.OrthoFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_approx_cmType (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : Ψ → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : E, ∀ τ : Ψ, dist (w τ) (τ.1 x) < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  choose z hz using fun τ : Ψ => Metric.denseRange_iff.1
    (GlobalTheory.ShortVec.denseRange_emb τ.1 (IsTotallyComplex.complexEmbedding_not_isReal τ.1)) (w τ) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (v := fun τ : Ψ => (InfinitePlace.mk τ.1).1) (fun τ => InfinitePlace.isNontrivial _)
    (by
      intro σ τ hne h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.eq_iff_isEquiv.2 h) with h1 | h1
      · exact hne (Subtype.ext h1)
      · exact (hΨ σ.1).1 σ.2 (h1 ▸ τ.2)) z hε2
  refine ⟨x, fun τ => ?_⟩
  have h1 : ‖τ.1 (z τ - x)‖ < ε / 2 := by
    rw [← InfinitePlace.apply]; exact hx τ
  rw [map_sub, ← dist_eq_norm] at h1
  have h2 := dist_triangle (w τ) (τ.1 (z τ)) (τ.1 x)
  have h3 := hz τ
  linarith

theorem dom_nonempty {r : ℕ} (X : Data E r) : X.dom.Nonempty := by
  choose P hP using X.signature
  refine ⟨fun τ k a => P τ k a, fun τ => ⟨(hP τ).1, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ k a => P τ k a) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    change lminor (gram τ.1 X.Gm (P τ)) i = _
    rw [(hP τ).2, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  unfold sgn
  split_ifs <;> norm_num

theorem exists_frm_mem_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r),
    ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  intro E _ _ _ r X
  obtain ⟨P, hP⟩ := dom_nonempty X
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (FourierCoefficientDomain.isOpen_dom X) P hP
  choose u hu using fun a k : Fin r =>
    exists_approx_cmType X.Ψ X.cmType (fun τ => P τ k a) hε
  refine ⟨u, hb ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_pi_lt_iff hε]
  intro τ
  rw [dist_pi_lt_iff hε]
  intro k
  rw [dist_pi_lt_iff hε]
  intro a
  exact hu a k τ

end GlobalTheory.OrthoFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimpleLabelOfSeriesIdempotentPair
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.SeriesIdem

theorem zIdem_pair_ne_zero {G : Type} [Group G] [Fintype G] (τ W : FDRep ℂ G) [Simple τ] [Simple W]
    (h : ∑ x, (zIdem τ).coeff x * W.character x ≠ 0) : Nonempty (W ≅ τ) := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI := invertibleOfNonzero hcard
  have ho := FDRep.char_orthonormal W τ
  by_contra hn
  rw [if_neg hn] at ho
  apply h
  have hs : ∑ g, W.character g * τ.character g⁻¹ = 0 := by
    rcases mul_eq_zero.mp ho with h0 | h0
    · exact absurd h0 (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    · exact h0
  calc ∑ x, (zIdem τ).coeff x * W.character x
      = (Module.finrank ℂ τ : ℂ) / Fintype.card G * ∑ g, W.character g * τ.character g⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [zIdem_coeff]
        simp only [FDRep.character]
        ring
    _ = 0 := by rw [hs, mul_zero]

end GlobalTheory.SeriesIdem

open GlobalTheory.SeriesIdem in
theorem GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair : ∀ (g : ℕ) [Fact g.Prime] (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X]) (ψ : GL (Fin r) (ZMod g) → ℂ), Formalism.L2.NT.IsIrrChar ψ → ∑ x, (Formalism.L2.NT.eSerO O r f).coeff x * ψ x = ψ 1 → ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ HasLabelO O τ f ∧ ∀ x, τ.character x = ψ x := by
  intro g _ C O r f ψ hψ hsum
  classical
  obtain ⟨W, hWs, rfl⟩ := (PI.SerBridgeGLW.irrCharIff_of PI.SerBridgeGLW.conjugate_character_formula _ ψ).1 hψ
  haveI := hWs
  by_contra hno
  push_neg at hno
  have hnt : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h0 : ∀ x, W.character x = 0 := fun x => by
      rw [FDRep.character, Subsingleton.elim (W.ρ x) 0, map_zero]
    have hn1 := (FDRep.simple_iff_char_is_norm_one W).mp hWs
    simp only [h0, zero_mul, Finset.sum_const_zero] at hn1
    exact absurd hn1.symm (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h1 : W.character 1 ≠ 0 := by
    rw [FDRep.char_one]
    exact_mod_cast Module.finrank_pos.ne'
  apply h1
  rw [← hsum]

  have hz : ∀ z : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)),
      (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) →
      ∑ x, z.coeff x * W.character x = 0 := by
    rintro z ⟨τ, hτs, rfl, hτl⟩
    haveI := hτs
    by_contra hne
    obtain ⟨i⟩ := zIdem_pair_ne_zero τ W hne
    obtain ⟨x, hx⟩ := hno τ hτs hτl
    exact hx (by rw [FDRep.char_iso i])
  unfold Formalism.L2.NT.eSerO
  set F : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) := fun z =>
    ∑ᶠ (_ : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f), z with hF
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_sum F hfin]
    have hsplit : ∑ x, (∑ z ∈ hfin.toFinset, F z).coeff x * W.character x =
        ∑ z ∈ hfin.toFinset, ∑ x, (F z).coeff x * W.character x := by
      simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_mul]
      exact Finset.sum_comm
    rw [hsplit]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hP : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f
    · simp only [hF, finsum_eq_if, if_pos hP]
      exact hz z hP
    · simp only [hF, finsum_eq_if, if_neg hP]
      simp
  · rw [finsum_of_infinite_support hfin]
    simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspaceStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mirabolic_whittaker_eigenspace : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (k : ℕ) (P : Subgroup (GL (Fin (k + 1)) F)), (∀ g, g ∈ P ↔ ∀ j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Representation ℂ P V), finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unipSym F (k + 1) 0 k} fun p => ψ (edgeSum (symEdge 0 k) (p : GL (Fin (k + 1)) F))) = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unip F (k + 1)} fun p => ψ (edgeSum (cutEdge (j)) (p : GL (Fin (k + 1)) F))) := by
  first | exact @GlobalTheory.FinGL.Mir.mirabolic_whittaker | exact GlobalTheory.FinGL.Mir.mirabolic_whittaker | (intros; apply GlobalTheory.FinGL.Mir.mirabolic_whittaker <;> assumption)
end

