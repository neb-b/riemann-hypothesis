module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem levi_mul_rad_apply {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n}
    (hm : ∀ i j, β i ≠ β j → mat m i j = 0)
    (hu : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j) {i l : Fin n} (h : β l ≤ β i) :
    mat (m * u) i l = mat m i l := by
  rw [mat_mul, Matrix.mul_apply]
  have key : ∀ k, mat m i k * mat u k l = mat m i k * (1 : Matrix (Fin n) (Fin n) L) k l := by
    intro k
    by_cases hk : β i = β k
    · rw [hu k l (by rw [← hk]; exact h)]
    · rw [hm i k hk, zero_mul, zero_mul]
  simp_rw [key]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem leviRad : LeviRad := by
  intro L _ _ σ n β hσ m hm u hu
  refine ⟨?_, fun hmu => ?_⟩
  · show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
    intro i l h
    have hmi : m⁻¹ ∈ leviU σ β := inv_mem hm
    rw [mat_mul, Matrix.mul_apply]
    have key : ∀ k, mat (m * u) i k * mat m⁻¹ k l = mat m i k * mat m⁻¹ k l := by
      intro k
      by_cases hk : β k = β l
      · rw [levi_mul_rad_apply hm hu (by rw [hk]; exact h)]
      · rw [hmi k l hk, mul_zero, mul_zero]
    simp_rw [key]
    rw [← Matrix.mul_apply, ← mat_mul, mul_inv_cancel, mat_one]
  · rw [mem_KU_iff hσ] at hmu ⊢
    intro i l
    by_cases hk : β i = β l
    · rw [← levi_mul_rad_apply hm hu (le_of_eq hk.symm)]
      exact hmu i l
    · rw [hm i l hk]
      exact zero_mem _

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCard
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem indexTwo_unitary (y : L) (hy : σ y + y = 0) :
    cT σ !![1, y; 0, 1] * antiJ L 2 * !![1, y; 0, 1] = antiJ L 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [add_comm]; exact hy

theorem indexTwo_exists_hom (σ : L →+* L) (T : AddSubgroup L) (hT : ∀ y, y ∈ T ↔ σ y + y = 0) :
    ∃ ψ : Multiplicative T →* GU σ 2,
      ∀ y, mat (ψ y) = !![1, (y.toAdd : L); 0, 1] := by
  have h : ∀ y : Multiplicative T,
      ∃ g : GU σ 2, mat g = !![1, (y.toAdd : L); 0, 1] := fun y =>
    exists_mat _ (indexTwo_unitary _ ((hT _).1 y.toAdd.2))
  choose f hf using h
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, hf⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, AddSubgroup.coe_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem indexTwo_mem_root (g : GU σ 2) :
    g ∈ rootU σ ![0, 0] ↔ mat g = !![1, mat g 0 1; 0, 1] := by
  constructor
  · intro h
    have h1 : ∀ i j : Fin 2, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 2) (Fin 2) L) i j := h.1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1 0 0 (by simp)
    · simp
    · simpa using h1 1 0 (by simp)
    · simpa using h1 1 1 (by simp)
  · intro h
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [h]
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · fin_cases i <;> fin_cases j <;> simp at hij

theorem indexTwo_trace (g : GU σ 2) (y : L) (h : mat g = !![1, y; 0, 1]) : σ y + y = 0 := by
  have h1 : cT σ (mat g) * antiJ L 2 * mat g = antiJ L 2 := g.2
  rw [h] at h1
  have := congrFun (congrFun h1 1) 1
  simpa [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using this

theorem indexTwo_conj {ϖ : L} (h0 : ϖ ≠ 0) (s g : GU σ 2)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i)) (y : L)
    (h : mat g = !![1, y; 0, 1]) : mat (s * g * s⁻¹) = !![1, ϖ * (ϖ * y); 0, 1] := by
  have e : mat s * mat g = !![1, ϖ * (ϖ * y); 0, 1] * mat s := by
    rw [hs, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rw [mat_mul, mat_mul, e, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]

end

theorem indexTwo_of_traceZeroIndex (H : TraceZeroIndex) : IndexTwo := by
  intro L _ _ ϖ σ q hU s hs
  have hq := H L ϖ σ q hU
  have h0 : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  have memT : ∀ y, y ∈ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔ σ y + y = 0 := fun y => Iff.rfl
  generalize (σ.toAddMonoidHom + AddMonoidHom.id L).ker = T at hq memT
  obtain ⟨ψ, hψ⟩ := indexTwo_exists_hom σ T memT
  set U := (intL L).toAddSubgroup ⊓ T with hUdef
  set m : L →+ L := AddMonoidHom.mulLeft ϖ with hm
  have hmT : ∀ y, y ∈ T → ϖ * y ∈ T := fun y hy => by
    rw [memT] at hy ⊢
    rw [map_mul, hU.2.2.1, ← mul_add, hy, mul_zero]
  have hminj : Function.Injective m := mul_right_injective₀ h0
  have hle : U.map m ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(intL L).mul_mem hϖ hy.1, hmT y hy.2⟩
  have h2 : ((U.map m).map m).relIndex U = q ^ 2 := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ (U.map m) _ (AddSubgroup.map_mono hle) hle,
      AddSubgroup.relIndex_map_map_of_injective _ _ hminj, hq, sq]
  have hinj : Function.Injective ψ := by
    intro a b hab
    have := congrFun (congrFun ((hψ a).symm.trans ((congrArg mat hab).trans (hψ b))) 0) 1
    exact Multiplicative.toAdd.injective (Subtype.ext (by simpa using this))
  have e1 : KU σ 2 ⊓ rootU σ ![0, 0] = (AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨hK, hr⟩
      have hr' := (indexTwo_mem_root g).1 hr
      have ht := (memT _).2 (indexTwo_trace g _ hr')
      refine ⟨Multiplicative.ofAdd ⟨mat g 0 1, ht⟩, ⟨(mem_KU_iff hU.2.1 g).1 hK 0 1, ht⟩, mat_injective ?_⟩
      rw [hψ]; exact hr'.symm
    · rintro ⟨y, hy, rfl⟩
      have hy1 : (y.toAdd : L) ∈ intL L := hy.1
      refine ⟨(mem_KU_iff hU.2.1 _).2 fun i j => ?_, (indexTwo_mem_root _).2 ?_⟩
      · rw [hψ]
        fin_cases i <;> fin_cases j
        · exact one_mem _
        · exact hy1
        · exact zero_mem _
        · exact one_mem _
      · rw [hψ]; rfl
  have e2 : ((AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ).map (MulAut.conj s).toMonoidHom =
      (AddSubgroup.toSubgroup (((U.map m).map m).addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ⟨ϖ * (ϖ * (y.toAdd : L)), hmT _ (hmT _ y.toAdd.2)⟩,
        ⟨_, ⟨_, hy, rfl⟩, rfl⟩, mat_injective ?_⟩
      rw [hψ]
      exact (indexTwo_conj h0 s _ hs _ (hψ y)).symm
    · rintro ⟨z, ⟨_, ⟨y, hy, rfl⟩, hz⟩, rfl⟩
      refine ⟨ψ (Multiplicative.ofAdd ⟨y, hy.2⟩), ⟨Multiplicative.ofAdd ⟨y, hy.2⟩, hy, rfl⟩, mat_injective ?_⟩
      refine (indexTwo_conj h0 s _ hs _ (hψ _)).trans ?_
      rw [hψ]
      exact congrArg (fun w => !![1, w; 0, 1]) hz
  rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup,
    AddSubgroup.relIndex_addSubgroupOf inf_le_right, h2]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReduction
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Swap

def ex (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

theorem tMat_eq {L : Type} [Field L] (ϖ : L) (n m : ℕ) (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun i => ϖ ^ ex n m a i := by
  unfold tMat ex
  congr 1
  funext i
  split_ifs <;> simp

theorem ex_low {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val = k.val) : ex n m a c = a k := by
  unfold ex
  rw [dite_eq_left (h ▸ k.2)]
  exact congrArg a (Fin.ext h)

theorem ex_high {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val + k.val + 1 = n) :
    ex n m a c = -a k := by
  have := k.2
  unfold ex
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg (fun x => -a x) (Fin.ext (by simp only; omega))

theorem ex_mid {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (h : m ≤ c.val) (h' : c.val + m < n) :
    ex n m a c = 0 := by
  unfold ex
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]

theorem ex_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) : ex n m a c.rev = -ex n m a c := by
  have h1 := c.2
  have h2 := Fin.val_rev c
  by_cases h : c.val < m
  · rw [ex_low a c ⟨c.val, h⟩ rfl, ex_high hm a c.rev ⟨c.val, h⟩ (by simp only; omega)]
  · by_cases h' : c.val + m < n
    · rw [ex_mid a c (by omega) h', ex_mid a c.rev (by omega) (by omega), neg_zero]
    · rw [ex_high hm a c ⟨c.rev.val, by omega⟩ (by simp only; omega), ex_low a c.rev ⟨c.rev.val, by omega⟩ rfl,
        neg_neg]

def emb (n i : ℕ) (h : 2 * i + 4 ≤ n) : Fin 4 → Fin n :=
  ![⟨i, by omega⟩, ⟨i + 1, by omega⟩, ⟨n - 2 - i, by omega⟩, ⟨n - 1 - i, by omega⟩]

def blk (n i : ℕ) (a : Fin n) : ℕ :=
  if a.val = i + 1 then i else if a.val = n - 1 - i then n - 2 - i else a.val

theorem blk_eq_iff {n i : ℕ} (h : 2 * i + 4 ≤ n) (a b : Fin n) :
    blk n i a = blk n i b ↔ a.val = b.val ∨ (a.val = i ∧ b.val = i + 1) ∨ (a.val = i + 1 ∧ b.val = i) ∨
      (a.val + i + 2 = n ∧ b.val + i + 1 = n) ∨ (a.val + i + 1 = n ∧ b.val + i + 2 = n) := by
  unfold blk
  split_ifs <;> omega

theorem mem_range_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) (a : Fin n) :
    a ∈ Set.range (emb n i h) ↔ a.val = i ∨ a.val = i + 1 ∨ a.val = n - 2 - i ∨ a.val = n - 1 - i := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [emb]
  · rintro (h1 | h1 | h1 | h1)
    exacts [⟨0, Fin.ext h1.symm⟩, ⟨1, Fin.ext h1.symm⟩, ⟨2, Fin.ext h1.symm⟩, ⟨3, Fin.ext h1.symm⟩]

theorem isBlockDatum_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) : IsBlockDatum (emb n i h) (blk n i) ![0, 0, 1, 1] := by
  have v0 : (emb n i h 0).val = i := rfl
  have v1 : (emb n i h 1).val = i + 1 := rfl
  have v2 : (emb n i h 2).val = n - 2 - i := rfl
  have v3 : (emb n i h 3).val = n - 1 - i := rfl
  have b0 : blk n i (emb n i h 0) = i := by unfold blk; rw [v0]; split_ifs <;> omega
  have b1 : blk n i (emb n i h 1) = i := by unfold blk; rw [v1]; split_ifs <;> omega
  have b2 : blk n i (emb n i h 2) = n - 2 - i := by unfold blk; rw [v2]; split_ifs <;> omega
  have b3 : blk n i (emb n i h 3) = n - 2 - i := by unfold blk; rw [v3]; split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro k
    fin_cases k
    · show i < i + 1
      omega
    · show i + 1 < n - 2 - i
      omega
    · show n - 2 - i < n - 1 - i
      omega
  · intro k
    apply Fin.ext
    rw [Fin.val_rev]
    fin_cases k
    · show n - 1 - i = n - (i + 1)
      omega
    · show n - 2 - i = n - (i + 1 + 1)
      omega
    · show i + 1 = n - (n - 2 - i + 1)
      omega
    · show i = n - (n - 1 - i + 1)
      omega
  · intro a b hab
    have : a.val ≤ b.val := hab
    unfold blk
    split_ifs <;> omega
  · intro a b
    have := a.2
    have := b.2
    rw [blk_eq_iff h, blk_eq_iff h, Fin.val_rev, Fin.val_rev]
    clear v0 v1 v2 v3 b0 b1 b2 b3
    rintro (h1 | h1 | h1 | h1 | h1) <;> omega
  · intro a b
    rw [mem_range_emb, mem_range_emb, Fin.ext_iff, blk_eq_iff h]
    rintro (h1 | h1 | h1 | h1 | h1)
    · exact Or.inl h1
    all_goals exact Or.inr ⟨by omega, by omega⟩
  · have hne : i ≠ n - 2 - i := by omega
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    simp [b0, b1, b2, b3, hne, hne.symm, show (Fin.succ 2 : Fin 4) = 3 from rfl]

theorem coeffSwap (H : LeviStep) (HI : IndexFour) (HC : CartanFour) : CoeffSwap := by
  intro L _ _ _ ϖ σ q n m hU hm hn h hh a i j hij t t' ht ht'
  have hj := j.2
  have h4 : 2 * i.val + 4 ≤ n := by omega
  have hq : q ≠ 0 := by
    have := hU.2.2.2.2.2.1
    omega
  have key : ∀ (c : Fin m → ℤ) (k : Fin 4),
      ex n m c (emb n i h4 k) = (![c i, c j, -c j, -c i] : Fin 4 → ℤ) k := by
    intro c k
    fin_cases k
    · exact ex_low c _ i rfl
    · exact ex_low c _ j hij.symm
    · exact ex_high hm c _ j (by show n - 2 - i.val + j.val + 1 = n; omega)
    · exact ex_high hm c _ i (by show n - 1 - i.val + i.val + 1 = n; omega)
  have key' : ∀ k : Fin 4, ex n m (a ∘ Equiv.swap i j) (emb n i h4 k) =
      (![a j, a i, -a i, -a j] : Fin 4 → ℤ) k := by
    intro k
    rw [key]
    simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have main := H L ϖ σ q n 4 (emb n i h4) (blk n i) ![0, 0, 1, 1] ![1, 0, 0, -1] (ex n m a)
    (ex n m (a ∘ Equiv.swap i j)) (q ^ 2) (a j - a i) t t' h hU (isBlockDatum_emb h4)
    (by decide) (by decide) (ex_rev hm _) (ex_rev hm _) ?_ ?_ (ht.trans (tMat_eq _ _ _ _))
    (ht'.trans (tMat_eq _ _ _ _)) (pow_ne_zero _ hq) (HI L ϖ σ q hU) ?_ hh
  · rw [main, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 2
    push_cast
    ring
  · intro c hc
    rw [mem_range_emb] at hc
    have := c.2
    unfold ex
    split_ifs with h1 h2
    · rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega
    · rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega
    · rfl
  · intro k l
    rw [key', key']
    fin_cases k <;> fin_cases l <;> simp <;> ring
  · intro s s' hs hs'
    simp only [key a] at hs
    simp only [key'] at hs'
    exact HC L ϖ σ q hU (a i) (a j) s s' hs hs'

end GlobalTheory.SatakeWeyl.Swap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPart
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem antiJ_eq_one_rev {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i.rev = j then 1 else 0 := by
  have := antiJ_mul_apply (1 : Matrix (Fin n) (Fin n) L) i j
  rw [Matrix.mul_one] at this
  rw [this, Matrix.one_apply]

theorem exists_mat_submatrix {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    (e : Fin r → Fin n) (he : Function.Injective e) (hrev : ∀ i, e i.rev = (e i).rev) (m : GU σ n)
    (hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b) :
    ∃ a : GU σ r, mat a = (mat m).submatrix e e := by
  apply exists_mat
  ext i j
  have h1 : cT σ (mat m) * antiJ L n * mat m = antiJ L n := m.2
  have h2 := congrFun (congrFun h1 (e i)) (e j)
  rw [Matrix.mul_apply] at h2 ⊢
  simp only [P.fSatake_cTJ] at h2 ⊢
  rw [antiJ_eq_one_rev] at h2 ⊢
  rw [← hrev] at h2
  simp only [he.eq_iff] at h2
  rw [← h2]
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · intro l hl
    rw [hm l (e j) (Or.inl hl), Matrix.one_apply_ne (fun h => hl ⟨j, h.symm⟩), mul_zero]
  · intro l
    simp only [Matrix.submatrix_apply, hrev]

theorem unipSplit_of_leviPart (hL : LeviPart) : UnipSplit := by
  intro L _ _ σ n r e β γ ι hB hι u hu
  obtain ⟨hmono, hrev, hβ, hβrev, hβe, hγ⟩ := hB
  have hu' : ∀ i j : Fin n, j.val ≤ i.val → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  have htri : (mat u).BlockTriangular β := by
    intro a b hab
    have hba : b < a := hβ.reflect_lt hab
    rw [hu' a b hba.le, Matrix.one_apply_ne hba.ne']
  obtain ⟨m, hmL, hmu, hrad⟩ := hL L σ n β hβrev u htri
  have hmL' : ∀ i j, β i ≠ β j → mat m i j = 0 := hmL
  have hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b := by
    intro a b hab
    by_cases h : β a = β b
    · rcases hβe a b h with rfl | ⟨h1, h2⟩
      · rw [hmu a a rfl, hu' a a le_rfl]
      · rcases hab with h' | h'
        · exact absurd h1 h'
        · exact absurd h2 h'
    · rw [hmL' a b h, Matrix.one_apply_ne (fun e' : a = b => h (congrArg β e'))]
  obtain ⟨a, ha⟩ := exists_mat_submatrix e hmono.injective hrev m hm
  have hιa : ι a = m := by
    apply mat_injective
    ext x y
    by_cases hxy : x ∉ Set.range e ∨ y ∉ Set.range e
    · rw [(hι a).2 x y hxy, hm x y hxy]
    · push Not at hxy
      obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hxy
      rw [(hι a).1 i j, ha, Matrix.submatrix_apply]
  refine ⟨a, ⟨?_, ?_⟩, m⁻¹ * u, hrad, by rw [hιa, mul_inv_cancel_left]⟩
  · intro i j hij
    have hij' : j ≤ i := hij
    rw [ha, Matrix.submatrix_apply]
    by_cases h : β (e i) = β (e j)
    · rw [hmu _ _ h, hu' _ _ (hmono.monotone hij'), Matrix.one_apply, Matrix.one_apply]
      simp only [hmono.injective.eq_iff]
    · rw [hmL' _ _ h, Matrix.one_apply_ne (fun e' : i = j => h (by rw [e']))]
  · intro i j hij
    rw [ha, Matrix.submatrix_apply]
    exact hmL' _ _ fun h => hij ((hγ i j).1 h)

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTwoDerivativeEisensteinTermUniformBound
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum.Bound

theorem eTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  intro E _ _ _ I _ φ hφ m σ r hσ hr
  have hr' : 0 < 1 - r := by linarith
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹) ^ (2 + m i) *
    (1 - r) ^ (-2 * σ.re)), fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) = ∏ i, (‖φ i x‖ ^ 2) ^ (-(1 + σ.re)) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  rw [hN, ← Finset.prod_mul_distrib, eTerm, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  have hp : 0 < ‖φ i x‖ := norm_pos_iff.2 ((map_ne_zero (φ i)).2 hx)
  have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ z x i (hz i)
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hd]
  set a := ‖φ i x‖ with ha
  set d := ‖defCoord φ z x i‖ with hdd
  have h1 : a ^ m i * d⁻¹ ^ (2 + m i) ≤ (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by
    have hinv : d⁻¹ ≤ (1 - r)⁻¹ * a⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
    calc a ^ m i * d⁻¹ ^ (2 + m i) ≤ a ^ m i * ((1 - r)⁻¹ * a⁻¹) ^ (2 + m i) := by gcongr
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 * (a ^ m i * a⁻¹ ^ m i) := by rw [mul_pow, pow_add a⁻¹]; ring
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow, mul_one]
  have h2 : d ^ ((-2 * σ).re) ≤ (1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re) := by
    rw [show (-2 * σ).re = -2 * σ.re by simp, ← Real.mul_rpow hr'.le hp.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hr' hp) hl (by linarith)
  have h3 : (a ^ 2) ^ (-(1 + σ.re)) = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by
    calc (a ^ 2) ^ (-(1 + σ.re)) = a ^ ((2 : ℝ) * (-(1 + σ.re))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
      _ = a ^ (-(2 : ℝ)) * a ^ (-2 * σ.re) := by rw [← Real.rpow_add hp]; ring_nf
      _ = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by rw [Real.rpow_neg hp.le, inv_pow]; norm_num
  rw [h3]
  calc ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * a ^ m i * d⁻¹ ^ (2 + m i) * d ^ ((-2 * σ).re)
      = ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * (a ^ m i * d⁻¹ ^ (2 + m i)) * d ^ ((-2 * σ).re) := by
        ring
    _ ≤ ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2) *
        ((1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (by positivity) (by positivity)
    _ = _ := by ring

end GlobalTheory.WeightTwoSum.Bound
end
end

