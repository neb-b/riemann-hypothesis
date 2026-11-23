module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlipSimilar
section
noncomputable section

namespace GlobalTheory.HCComm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def flip {n : ℕ} (M : Mt g n) : Mt g n := (M.submatrix Fin.revPerm Fin.revPerm).transpose

theorem flip_apply {n : ℕ} (M : Mt g n) (i j : Fin n) : flip M i j = M j.rev i.rev := rfl

theorem flip_mul {n : ℕ} (M N : Mt g n) : flip (M * N) = flip N * flip M := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv M N Fin.revPerm Fin.revPerm Fin.revPerm, Matrix.transpose_mul]

theorem flip_one {n : ℕ} : flip (1 : Mt g n) = 1 := by
  unfold flip
  rw [Matrix.submatrix_one_equiv, Matrix.transpose_one]

theorem flip_flip {n : ℕ} (M : Mt g n) : flip (flip M) = M := by
  ext i j
  simp only [flip_apply, Fin.rev_rev]

private lemma one_submatrix_rev_mul_apply {n : ℕ} (A : Mt g n) (i j : Fin n) :
    ((1 : Mt g n).submatrix Fin.rev id * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, Matrix.one_apply]

private lemma mul_one_submatrix_rev_apply {n : ℕ} (A : Mt g n) (i j : Fin n) :
    (A * (1 : Mt g n).submatrix Fin.rev id) i j = A i j.rev := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp Fin.revPerm]
  simp [Matrix.one_apply]

theorem flip_similar {n : ℕ} (M : Mt g n) : ∃ P : Mt g n, IsUnit P ∧ P * M = flip M * P := by

  obtain ⟨Q, hQ, hQM⟩ := GlobalTheory.SimilarTranspose.main (ZMod g) (Fin n) M
  have hJJ : (1 : Mt g n).submatrix Fin.rev id * (1 : Mt g n).submatrix Fin.rev id = 1 := by
    ext i j
    rw [one_submatrix_rev_mul_apply]
    simp [Matrix.one_apply]
  have hflip : flip M = (1 : Mt g n).submatrix Fin.rev id * M.transpose *
      (1 : Mt g n).submatrix Fin.rev id := by
    ext i j
    rw [mul_one_submatrix_rev_apply, one_submatrix_rev_mul_apply, flip_apply, Matrix.transpose_apply]
  generalize (1 : Mt g n).submatrix Fin.rev id = J at hJJ hflip
  refine ⟨J * Q, IsUnit.mul ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩ hQ, ?_⟩
  have hJJQ : J * (J * Q) = Q := by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [hflip]
  simp only [Matrix.mul_assoc, hJJQ, hQM]

def flipG {n : ℕ} (x : Gn g n) : Gn g n where
  val := flip (x : Mt g n)
  inv := flip ((x⁻¹ : Gn g n) : Mt g n)
  val_inv := by rw [← flip_mul, Units.inv_mul, flip_one]
  inv_val := by rw [← flip_mul, Units.mul_inv, flip_one]

theorem flipG_coe {n : ℕ} (x : Gn g n) : ((flipG x : Gn g n) : Mt g n) = flip (x : Mt g n) := rfl

theorem flipG_mul {n : ℕ} (x y : Gn g n) : flipG (x * y) = flipG y * flipG x := by
  apply Units.ext
  simp only [flipG_coe, Units.val_mul, flip_mul]

theorem flipG_inv {n : ℕ} (x : Gn g n) : flipG x⁻¹ = (flipG x)⁻¹ := by
  apply Units.ext
  rfl

theorem flipG_flipG {n : ℕ} (x : Gn g n) : flipG (flipG x) = x := by
  apply Units.ext
  simp only [flipG_coe, flip_flip]

theorem flipG_conj {n : ℕ} (x : Gn g n) : ∃ p : Gn g n, flipG x = p * x * p⁻¹ := by
  obtain ⟨P, hP, hPx⟩ := flip_similar (x : Mt g n)
  refine ⟨hP.unit, Units.ext ?_⟩
  have h1 : ((hP.unit : Gn g n) : Mt g n) = P := hP.unit_spec
  have h2 : ((hP.unit : Gn g n) : Mt g n) * ((hP.unit⁻¹ : Gn g n) : Mt g n) = 1 := hP.unit.mul_inv
  rw [h1] at h2
  rw [flipG_coe, Units.val_mul, Units.val_mul, h1, hPx, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dite_eq_left (Units.isUnit x)]
  exact Units.ext rfl

theorem class_flip {n : ℕ} {α : Gn g n → ℂ} (hα : IsClass α) (M : Mt g n) :
    α (toG (flip M)) = α (toG M) := by
  by_cases hM : IsUnit M
  · have e1 : toG M = hM.unit := by
      unfold toG
      rw [dite_eq_left hM]
    have e2 : toG (flip M) = flipG hM.unit := by
      rw [← toG_coe (flipG hM.unit), flipG_coe, IsUnit.unit_spec]
    obtain ⟨p, hp⟩ := flipG_conj hM.unit
    rw [e1, e2, hp]
    exact hα _ _
  · have hF : ¬ IsUnit (flip M) := by
      intro h
      apply hM
      have e : flip (flip M) = ((flipG h.unit : Gn g n) : Mt g n) := by
        rw [flipG_coe, IsUnit.unit_spec]
      rw [flip_flip] at e
      rw [e]
      exact Units.isUnit _
    unfold toG
    rw [dite_eq_right hM, dite_eq_right hF]

theorem inPar_flip {a b : ℕ} (M : Mt g (a + b)) : InPar b (flip M) ↔ InPar a M := by
  constructor
  · intro h i j hj hi
    have hi' := i.isLt
    have hj' := j.isLt
    have := h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega)
    rwa [flip_apply, Fin.rev_rev, Fin.rev_rev] at this
  · intro h i j hj hi
    have hi' := i.isLt
    have hj' := j.isLt
    rw [flip_apply]
    exact h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega)

private lemma entN_of_lt {n : ℕ} (M : Mt g n) (x y : ℕ) (hx : x < n) (hy : y < n) :
    entN M x y = M ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold entN
  rw [dite_eq_left ⟨hx, hy⟩]

theorem tl_flip {a b : ℕ} (M : Mt g (a + b)) : tl b (flip M) = flip (br a b M) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [flip_apply]
  simp only [tl, br]
  rw [entN_of_lt (flip M) i j (by omega) (by omega),
    entN_of_lt M (a + j.rev) (a + i.rev) (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega), flip_apply]
  congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega

private lemma entN_eq_apply_of_lt_of_lt {n : ℕ} (M : Mt g n) (x y : ℕ) (hx : x < n) (hy : y < n) :
    entN M x y = M ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold entN
  rw [dite_eq_left ⟨hx, hy⟩]

theorem br_flip {a b : ℕ} (M : Mt g (a + b)) : br b a (flip M) = flip (tl a M) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [flip_apply]
  simp only [tl, br]
  rw [entN_eq_apply_of_lt_of_lt (flip M) (b + i) (b + j) (by omega) (by omega),
    entN_eq_apply_of_lt_of_lt M j.rev i.rev (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega), flip_apply]
  congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega

private lemma sum_flipG_conj_eq_sum_conj_flipG {n : ℕ} (F : Gn g n → ℂ) (w : Gn g n) :
    ∑ y : Gn g n, F (flipG (y⁻¹ * w * y)) = ∑ y : Gn g n, F (y⁻¹ * flipG w * y) := by
  refine Fintype.sum_bijective (fun y => (flipG y)⁻¹) ?_ _ _ ?_
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun v => flipG v⁻¹, ?_, ?_⟩
    · intro y
      simp only [inv_inv, flipG_flipG]
    · intro v
      simp only [flipG_flipG, inv_inv]
  · intro y
    simp only [flipG_mul, flipG_inv, inv_inv, mul_assoc]

private lemma sum_conj_conj_eq_sum_conj {n : ℕ} (F : Gn g n → ℂ) (w p : Gn g n) :
    ∑ y : Gn g n, F (y⁻¹ * (p * w * p⁻¹) * y) = ∑ y : Gn g n, F (y⁻¹ * w * y) := by
  refine Fintype.sum_bijective (fun y => p⁻¹ * y) (Group.mulLeft_bijective p⁻¹) _ _ ?_
  intro y
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem main : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ),
    IsClass α → IsClass β → n = a + b → hc a b α β n = hc b a β α n := by
  intro g _ a b n α β hα hβ hn
  subst hn
  funext x

  have key : ∀ z : Gn g (a + b),
      (if InPar b ((flipG z : Gn g (a + b)) : Mt g (a + b)) then
        β (toG (tl b ((flipG z : Gn g (a + b)) : Mt g (a + b)))) *
          α (toG (br b a ((flipG z : Gn g (a + b)) : Mt g (a + b)))) else 0) =
      (if InPar a (z : Mt g (a + b)) then
        α (toG (tl a (z : Mt g (a + b)))) * β (toG (br a b (z : Mt g (a + b)))) else 0) := by
    intro z
    simp only [flipG_coe, inPar_flip, tl_flip, br_flip, class_flip hβ, class_flip hα]
    rw [mul_comm]
  have hcard : (Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card =
      (Finset.univ.filter fun p : Gn g (a + b) => InPar b (p : Mt g (a + b))).card := by
    refine Finset.card_nbij' flipG flipG ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [flipG_coe, inPar_flip]
      exact hq
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [flipG_coe]
      apply (inPar_flip (a := a) (b := b) (flip (q : Mt g (a + b)))).mp
      rwa [flip_flip]
    · intro q _
      exact flipG_flipG q
    · intro q _
      exact flipG_flipG q
  obtain ⟨p, hp⟩ := flipG_conj x
  let Fba : Gn g (a + b) → ℂ := fun z =>
    if InPar b (z : Mt g (a + b)) then
      β (toG (tl b (z : Mt g (a + b)))) * α (toG (br b a (z : Mt g (a + b)))) else 0
  have e1 : (∑ y : Gn g (a + b), if InPar a ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)) then
      α (toG (tl a ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)))) *
        β (toG (br a b ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)))) else 0) =
      ∑ y : Gn g (a + b), Fba (y⁻¹ * x * y) := by
    calc _ = ∑ y : Gn g (a + b), Fba (flipG (y⁻¹ * x * y)) :=
          Finset.sum_congr rfl fun y _ => (key _).symm
      _ = ∑ y : Gn g (a + b), Fba (y⁻¹ * flipG x * y) := sum_flipG_conj_eq_sum_conj_flipG Fba x
      _ = ∑ y : Gn g (a + b), Fba (y⁻¹ * x * y) := by
          rw [hp]
          exact sum_conj_conj_eq_sum_conj Fba x p
  simp only [hc, hcT]
  rw [hcard]
  congr 1

end GlobalTheory.HCComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GgOneAndIsClass
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.GGDeg

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {n : ℕ} {M : Mt g n} (h : IsUniUp M) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun a b hab => (h a b).1 hab),
    Finset.prod_eq_one fun a _ => (h a a).2 rfl]
  exact isUnit_one

theorem card_uniUp_mat (n : ℕ) :
    (Finset.univ.filter fun M : Mt g n => IsUniUp M).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  have h : (Finset.univ.filter fun M : Mt g n => IsUniUp M) =
      (Fintype.piFinset fun a : Fin n => Fintype.piFinset fun b : Fin n =>
        (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)) :
          Finset (Fin n → Fin n → ZMod g)) := by
    ext M
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
    refine Iff.trans ?_ Fintype.mem_piFinset.symm
    refine forall_congr' fun a => Iff.trans (forall_congr' fun b => ?_) Fintype.mem_piFinset.symm
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne, hab.not_gt]
    · subst hab; simp
    · simp [hab, hab.ne', hab.not_gt]
  rw [h]
  erw [Fintype.card_piFinset]
  simp only [Fintype.card_piFinset]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h2 : ∀ a : Fin n, (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)).card =
      if a < b then g else 1 := by
    intro a
    split_ifs <;> simp [ZMod.card]
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [show (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b by ext; simp]
  simp

theorem card_uniUp (n : ℕ) :
    (Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  rw [← card_uniUp_mat]
  refine Finset.card_bij (fun u _ => (u : Mt g n)) ?_ ?_ ?_
  · intro u hu
    simpa using hu
  · intro u _ v _ h
    exact Units.ext h
  · intro M hM
    have hM' : IsUniUp M := by simpa using hM
    exact ⟨(isUnit_of_isUniUp hM').unit, by simpa using hM', rfl⟩

theorem card_Gn (n : ℕ) : (Fintype.card (Gn g n) : ℂ) =
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) * ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) := by
  have hg : 0 < g := (Fact.out : g.Prime).pos
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have h1 : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) = ∏ i : Fin n, ((g : ℂ) ^ (n - i) - 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((g : ℂ) ^ (n - i) - 1)) n]
    refine Finset.prod_bij' (fun i _ => n - i) (fun i _ => n - i) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [Finset.mem_Icc, Finset.mem_range] <;> intro i hi
    · omega
    · omega
    · omega
    · omega
    · rw [show n - (n - i) = i by omega]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hg i.2.le), mul_sub, ← pow_add,
    show (i : ℕ) + (n - i) = n by have := i.2; omega]
  push_cast
  ring

theorem gg_one_and_isClass : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ),
    gg ψ n 1 = ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) ∧ IsClass (gg ψ n) := by
  intro g _ ψ n
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  constructor
  · have h1 : IsUniUp (1 : Mt g n) := fun a b =>
      ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq a⟩
    have h2 : ∀ i, entN (1 : Mt g n) i (i + 1) = 0 := by
      intro i
      unfold entN
      split_ifs with h
      · exact Matrix.one_apply_ne (by simp)
      · rfl
    unfold gg
    simp only [mul_one, inv_mul_cancel, Units.val_one, h1, if_true, h2, Finset.sum_const_zero,
      AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [card_uniUp, card_Gn]
    push_cast
    rw [inv_mul_cancel_left₀ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hg)]
  · intro x z
    unfold gg
    congr 1
    refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_).symm
    have : (Equiv.mulLeft z y)⁻¹ * (z * x * z⁻¹) * (Equiv.mulLeft z y) = y⁻¹ * x * y := by
      simp [mul_assoc]
    rw [this]

end GlobalTheory.GLq.GGDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.WtSkew

theorem invVol_le_relIndex {G : Type} [Group G] (A B : Subgroup G) :
    GlobalTheory.HL.invVol A B ≤ (B.relIndex A : ℝ) := by
  unfold GlobalTheory.HL.invVol
  rcases Nat.eq_zero_or_pos (A.relIndex B) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [StarRing K] in
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (h : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t h

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_X (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem normalForm_baseLattice_le_dualSpan_sup_line (N : NF H r) : N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_))
    (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem ref_inf_Pi (N : NF H r) (L : Submodule (𝓞 K) V) (hc : IsCompl N.Wt N.Pi)
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hp : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (hz : ∀ t : K, t • N.F.z ∈ L → t ∈ (1 : Submodule (𝓞 K) K)) :
    N.Ref L ⊓ rs (𝓞 K) N.Pi = N.P0 := by
  have h0 : N.P0 ≤ rs (𝓞 K) N.Pi := hp ▸ normalForm_baseLattice_le_dualSpan_sup_line N
  have hzP : N.F.z ∈ N.Pi := hp ▸ Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  refine le_antisymm ?_ (le_inf le_sup_left h0)
  rintro x ⟨hx, hxP⟩
  obtain ⟨p, hpP, l, ⟨hlL, hlW⟩, rfl⟩ := Submodule.mem_sup.1 hx
  have hlW' : l ∈ N.Wt ⊔ Submodule.span K {N.F.z} := hn ▸ hlW
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hlW'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hxP' : p + (w + t • N.F.z) ∈ N.Pi := hxP
  have hpP' : p ∈ N.Pi := h0 hpP
  have hwP : w ∈ N.Pi := by
    have := N.Pi.sub_mem (N.Pi.sub_mem hxP' hpP') (N.Pi.smul_mem t hzP)
    simpa using this
  have hw0 : w = 0 := (Submodule.disjoint_def.1 hc.disjoint) w hw hwP
  subst hw0
  rw [zero_add] at hlL ⊢
  refine N.P0.add_mem hpP ?_
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨t, hz t hlL, rfl⟩)

theorem invVol_skew_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  obtain ⟨-, -, hc, hdim, hn, -, -, -, -, -, -, hp⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hR, -⟩ := _root_.GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  obtain ⟨-, -, hz, -, hlat, -⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT
  have hstab := _root_.GlobalTheory.DegCnt.stab_of_deep_congruence K V H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  have hP := ref_inf_Pi N (latL N.F N.F' Λ) hc hn hp (fun t ht => (hz t).1 ht)
  have hfg : N.P0.FG := by
    refine Submodule.FG.of_le hlat.fg ?_
    rw [← hP]; exact inf_le_left
  have hmap : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, ∀ x ∈ N.P0, s x ∈ N.P0 := by
    rintro s ⟨⟨hsR, hsS⟩, -, hsW⟩ x hx
    rw [← hP] at hx ⊢
    have hsS' : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := hsS
    refine ⟨?_, ?_⟩
    · rw [← hsS']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx.1
    · have hx2 : x ∈ perp H N.Wt := hx.2
      change s x ∈ perp H N.Wt
      rw [mem_perp_iff] at hx2 ⊢
      intro w hw
      have hw' : s w = w := (mem_fixingSubgroup_iff _).1 hsW w hw
      have := ((hR s).1 hsR).1.1 x w
      simp only [LinearEquiv.coe_coe, hw'] at this
      rw [this]; exact hx2 w hw
  have hfix : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, s • N.P0 = N.P0 := by
    intro s hs
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hmap s hs x hx
    · intro y hy
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ y, hmap _ (inv_mem hs) y hy, ?_⟩
      exact s.apply_symm_apply y
  have hm : 𝔠 ^ (3 * e + 10) ≠ ⊥ := pow_ne_zero _ h0
  obtain ⟨-, hle⟩ := _root_.GlobalTheory.CongIndex.relIndex_le K V (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) N.P0 (𝔠 ^ (3 * e + 10))
    (N.Gam Λ ⊓ N.ZI) hfg hm hfix (fun s hs hx =>
      ⟨⟨hs.1.1, hstab s ⟨hs.1.1, hs.2.2⟩ hx⟩, hs.2⟩)
  have hrk : Module.finrank K (Submodule.span K (N.P0 : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (N.P0 : Set V) ≤ N.Pi := by
      rw [Submodule.span_le, ← hP]
      exact fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hpos : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  refine (invVol_le_relIndex _ _).trans ?_
  have : (N.Gam Λ ⊓ N.ZI).relIndex (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hle.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hrk 2))
  exact_mod_cast this

end GlobalTheory.DegCnt.WtSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIntegersIffSplitAtTypePrime
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem intV_iff_sp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp), (∀ i, (gp i).Prime) → (∀ i, SplitsIn E (gp i)) → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) (x : E ⊗[F] v.adicCompletion F), x ∈ intV E v ↔ (G.sp i v hv x).1 ∈ v.adicCompletionIntegers F ∧ (G.sp i v hv x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm gp G _ _ i v hv x
  exact split_integral_local F E v (G.sp i v hv) (G.sp_alg i v hv) x

end GlobalTheory.St.G
end

