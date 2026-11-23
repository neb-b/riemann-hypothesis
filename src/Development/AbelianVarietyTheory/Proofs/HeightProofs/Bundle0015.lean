module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Matrix

namespace GlobalTheory.RealPar

variable {p q n : ℕ}

def BlockOrd (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) ∧ ∀ a b, posC a b → e a < e b

def Factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)) : Prop :=
  ∀ x, U.π x = σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))

theorem BlockOrd.sameBlock_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    sameBlock a b ↔ ε (e a) = ε (e b) := by
  obtain ⟨h1, h2, -⟩ := h
  cases a <;> cases b <;> simp [sameBlock, h1, h2]

theorem BlockOrd.posC_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    posC a b ↔ e a < e b ∧ ε (e a) = ε (e b) := by
  constructor
  · intro hab
    refine ⟨h.2.2 a b hab, ?_⟩
    rw [← h.sameBlock_iff]
    cases a <;> cases b <;> simp_all [posC, sameBlock]
  · rintro ⟨hlt, heq⟩
    rw [← h.sameBlock_iff] at heq
    have hne : a ≠ b := fun hab => by subst hab; exact lt_irrefl _ hlt
    have hnot : ¬ posC b a := fun hba => lt_asymm hlt (h.2.2 b a hba)
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inl hij) hne
        · exact absurd hij hnot
      | inr j => simp [sameBlock] at heq
    | inr i =>
      cases b with
      | inl j => simp [sameBlock] at heq
      | inr j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inr hij) hne
        · exact absurd hij hnot

theorem exists_blockOrd (ε : Fin n → Bool) (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : ∃ e : Ix p q ≃ Fin n, BlockOrd e ε := by
  classical
  set S := Finset.univ.filter fun a => ε a = true with hS
  set T := Finset.univ.filter fun a => ε a = false with hT
  have hcard : p + q = n := by
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun a => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h0
    rw [← hp, ← hq]
    exact h0
  let f : Ix p q → Fin n := fun x =>
    match x with
    | Sum.inl i => S.orderEmbOfFin hp i
    | Sum.inr j => T.orderEmbOfFin hq j
  have fS : ∀ i, ε (f (Sum.inl i)) = true := fun i =>
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem hp i)).2
  have fT : ∀ j, ε (f (Sum.inr j)) = false := fun j =>
    (Finset.mem_filter.mp (T.orderEmbOfFin_mem hq j)).2
  have hinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl ((S.orderEmbOfFin hp).injective hxy)
      | inr j =>
        have h1 := fS i
        rw [hxy, fT j] at h1
        exact absurd h1 (by simp)
    | inr i =>
      cases y with
      | inl j =>
        have h1 := fT i
        rw [hxy, fS j] at h1
        exact absurd h1 (by simp)
      | inr j => exact congrArg Sum.inr ((T.orderEmbOfFin hq).injective hxy)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [hcard]
  refine ⟨Equiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro i
    exact fS i
  · intro j
    exact fT j
  · intro a b hab
    simp only [Equiv.ofBijective_apply]
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (S.orderEmbOfFin hp).strictMono hab
      | inr j => exact absurd hab (by simp [posC])
    | inr i =>
      cases b with
      | inl j => exact absurd hab (by simp [posC])
      | inr j => exact (T.orderEmbOfFin hq).strictMono hab

theorem BlockOrd.reindex_Jm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    Matrix.reindex e e (Jm p q) = Formalism.REAL.Jm ε := by
  obtain ⟨h1, h2, -⟩ := h
  ext a b
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Jm, Formalism.UG.Jpq]
  cases a' <;> cases b' <;> simp [h1, h2, Matrix.one_apply] <;> split_ifs <;> simp

theorem BlockOrd.inUJ_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (g : Mat p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e g) ↔ gᴴ * Jm p q * g = Jm p q := by
  have key : ∀ M N : Mat p q, Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.inUJ
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex, key, key]
  exact (Matrix.reindex e e).injective.eq_iff

theorem mem_Upq (g : GL (Ix p q) ℂ) : g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Jm p q * g = Jm p q := by
  unfold Formalism.UG.Upq Formalism.UG.UJ
  rw [Subgroup.mem_mk]
  show Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q ↔ _
  have hc : Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) = (g : Mat p q)ᴴ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hc]
  rfl

theorem BlockOrd.cov_mem {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  exact (h.inUJ_iff _).mpr ((mem_Upq _).mp (T.cov_mem x))

theorem BlockOrd.cov_surj {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ x : T.G, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g := by
  have hg' : Formalism.REAL.inUJ ε g := hg
  set g' : Mat p q := (Matrix.reindex e e).symm g
  have hre : Matrix.reindex e e g' = g := (Matrix.reindex e e).apply_symm_apply g
  have hU : g'ᴴ * Jm p q * g' = Jm p q := by
    rw [← h.inUJ_iff, hre]
    exact hg'
  have hJJ : Jm p q * Jm p q = 1 := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hleft : (Jm p q * g'ᴴ * Jm p q) * g' = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hU, hJJ]
  have hright : g' * (Jm p q * g'ᴴ * Jm p q) = 1 := mul_eq_one_comm.mp hleft
  let u : GL (Ix p q) ℂ := ⟨g', Jm p q * g'ᴴ * Jm p q, hright, hleft⟩
  have hu : u ∈ Formalism.UG.Upq p q := (mem_Upq u).mpr hU
  have hdet : (u : Mat p q).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (u : Mat p q)).mp u.isUnit
    exact this.ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : Mat p q).det (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hz]; simp)
  obtain ⟨x, ⟨hx, -⟩, -⟩ := T.bij u hu (Units.mk0 z hz0) (by simpa using hz)
  refine ⟨x, ?_⟩
  rw [hx]
  exact hre

theorem exists_factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (h : ∀ x, T.cov x = 1 → U.π x = 1) : ∃ σ, Factors U e σ := by
  classical
  refine ⟨fun M => if hM : ∃ x, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = M
    then U.π hM.choose else 0, ?_⟩
  intro x
  have hM : ∃ y, Matrix.reindex e e ((T.cov y : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := ⟨x, rfl⟩
  simp only [dif_pos hM]
  set y := hM.choose with hy
  have hyx : T.cov y = T.cov x := Units.ext ((Matrix.reindex e e).injective hM.choose_spec)
  have h1 : T.cov (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 : U.π y⁻¹ * U.π x = 1 := by
    rw [← map_mul]
    exact h _ h1
  calc U.π x = U.π (y * y⁻¹) * U.π x := by simp
    _ = U.π y * (U.π y⁻¹ * U.π x) := by rw [map_mul, mul_assoc]
    _ = U.π y := by rw [h2, mul_one]

end GlobalTheory.RealPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsWeierstrassPMulOde
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

theorem relIndex_mul_periodLattice (L : PeriodPair) {α : ℂ} (h0 : α ≠ 0)
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) :
    (((AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup).relIndex
      L.lattice.toAddSubgroup : ℕ) : ℝ) = ‖α‖ ^ 2 := by
  classical
  let f : L.lattice →ₗ[ℤ] L.lattice := (LinearMap.mulLeft ℤ α).restrict (fun l hl => hα l hl)
  have hf : ∀ x : L.lattice, (f x : ℂ) = α * x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun t : L.lattice => (t : ℂ)) hxy
    simp only [hf] at this
    exact Subtype.ext (mul_left_cancel₀ h0 this)
  have hsub : (AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup).addSubgroupOf
      L.lattice.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  have hidx := AddSubgroup.index_eq_natAbs_det L.latticeBasis (LinearMap.range f).toAddSubgroup
    (L.latticeBasis.map (LinearEquiv.ofInjective f hinj))
  have hdet : (L.latticeBasis.det fun i =>
      ((L.latticeBasis.map (LinearEquiv.ofInjective f hinj)) i : L.lattice)) =
      L.latticeBasis.repr (f (L.latticeBasis 0)) 0 * L.latticeBasis.repr (f (L.latticeBasis 1)) 1 -
      L.latticeBasis.repr (f (L.latticeBasis 1)) 0 * L.latticeBasis.repr (f (L.latticeBasis 0)) 1 := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    rfl
  have hrep : ∀ x : L.lattice, α * x = (L.latticeBasis.repr (f x) 0 : ℤ) * L.ω₁ +
      (L.latticeBasis.repr (f x) 1 : ℤ) * L.ω₂ := by
    intro x
    have := congrArg (fun t : L.lattice => (t : ℂ)) (L.latticeBasis.sum_repr (f x))
    simp only [Fin.sum_univ_two, hf] at this
    rw [← this]
    simp
  have h1 := hrep (L.latticeBasis 0)
  have h2 := hrep (L.latticeBasis 1)
  rw [AddSubgroup.relIndex, hsub]
  refine (congrArg Nat.cast (hidx.trans (congrArg Int.natAbs hdet))).trans ?_
  generalize L.latticeBasis.repr (f (L.latticeBasis 0)) 0 = a at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 0)) 1 = c at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 1)) 0 = b at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 1)) 1 = d at h1 h2 ⊢
  simp only [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one] at h1 h2
  have hD : L.ω₁.re * L.ω₂.im - L.ω₂.re * L.ω₁.im ≠ 0 := by
    intro hD
    have hind := LinearIndependent.pair_iff.mp L.indep
    have e1 := hind L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp <;> linarith)
    have e2 := hind L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp <;> linarith)
    have e3 : L.ω₂ = 0 := Complex.ext e2.1 e1.1
    have := hind 0 1 (by simp [e3])
    exact one_ne_zero this.2
  have r1 := congrArg Complex.re h1
  have i1 := congrArg Complex.im h1
  have r2 := congrArg Complex.re h2
  have i2 := congrArg Complex.im h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, sub_zero, add_zero] at r1 i1 r2 i2
  have key : ((a * d - b * c : ℤ) : ℝ) = ‖α‖ ^ 2 := by
    apply mul_right_cancel₀ hD
    rw [Complex.sq_norm, Complex.normSq_apply]
    push_cast
    have : (α.re * L.ω₁.re - α.im * L.ω₁.im) * (α.re * L.ω₂.im + α.im * L.ω₂.re) -
        (α.re * L.ω₂.re - α.im * L.ω₂.im) * (α.re * L.ω₁.im + α.im * L.ω₁.re) =
        (a * L.ω₁.re + c * L.ω₂.re) * (b * L.ω₁.im + d * L.ω₂.im) -
        (b * L.ω₁.re + d * L.ω₂.re) * (a * L.ω₁.im + c * L.ω₂.im) := by
      rw [r1, i1, r2, i2]
    linear_combination -this
  rw [Nat.cast_natAbs, Int.cast_abs, key]
  exact abs_of_nonneg (by positivity)

theorem exists_weierstrassP_mul_ode : ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), α ≠ 0 → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = N → ∃ A D : ℂ[X], D ≠ 0 ∧ A.natDegree = N ∧ D.natDegree + 1 = N ∧ (∀ z, α * z ∉ L.lattice → D.eval (L.weierstrassP z) ≠ 0 ∧ L.weierstrassP (α * z) = A.eval (L.weierstrassP z) / D.eval (L.weierstrassP z)) ∧ C (α ^ 2) * D * (4 * A ^ 3 - C L.g₂ * A * D ^ 2 - C L.g₃ * D ^ 3) = (derivative A * D - A * derivative D) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
  intro L α N h0 hα hN
  obtain ⟨A, D, -, -, hmon, -, -, hA, hD, hz, hdiv⟩ :=
    exists_weierstrassP_mul_eq_div h0 hα ⊤ trivial trivial trivial (fun _ _ _ => trivial)
  have hAN : A.natDegree = N := by
    have := relIndex_mul_periodLattice L h0 hα
    rw [← hA, hN] at this
    exact_mod_cast this
  refine ⟨A, D, hmon.ne_zero, hAN, hD.trans hAN, fun z hz' => ⟨?_, hdiv z hz'⟩, ?_⟩
  · intro h
    exact hz' ((hz z (fun hl => hz' (hα z hl))).mp h)
  · apply Polynomial.eq_of_infinite_eval_eq
    have hfin : {x : ℂ | D.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hmon.ne_zero
    refine hfin.infinite_compl.mono ?_
    intro x hx
    obtain ⟨z, hzL, rfl⟩ := exists_weierstrassP_eq L x
    have hx' : D.eval (L.weierstrassP z) ≠ 0 := hx
    have hαz : α * z ∉ L.lattice := fun h => hx' ((hz z hzL).mpr h)
    have e1 := derivWeierstrassP_mul_eq hα hdiv hαz hx'
    have e2 := L.derivWeierstrassP_sq z hzL
    have e3 := L.derivWeierstrassP_sq _ hαz
    rw [hdiv z hαz] at e3
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_ofNat] at e1 ⊢
    rw [← e2]
    have e4 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e4
    rw [e3] at e4
    field_simp at e4
    linear_combination e4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
private lemma natAbs_discr_pow_finrank_le_natAbs_discr (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    (discr K).natAbs ^ Module.finrank K L ≤ (discr L).natAbs := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) ?_
  rw [h]
  exact Dvd.intro_left _ rfl


set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
theorem _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    Real.log (Module.finrank ℚ K) ≤ Real.log (Module.finrank ℚ L) ∧
      Real.log |((NumberField.discr K : ℤ) : ℝ)| / Module.finrank ℚ K ≤
        Real.log |((NumberField.discr L : ℤ) : ℝ)| / Module.finrank ℚ L := by
  have hmul := Module.finrank_mul_finrank ℚ K L
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hm : 0 < Module.finrank K L := Module.finrank_pos
  have hnR : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast hn
  have hmR : (0 : ℝ) < Module.finrank K L := by exact_mod_cast hm
  have hNR : ((Module.finrank ℚ L : ℕ) : ℝ) = Module.finrank ℚ K * Module.finrank K L := by
    rw [← hmul]; push_cast; ring
  constructor
  · apply Real.log_le_log hnR
    rw [hNR]
    have : (1 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hm
    nlinarith
  · have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
      have := discr_ne_zero K
      positivity
    have hle : |((discr K : ℤ) : ℝ)| ^ Module.finrank K L ≤ |((discr L : ℤ) : ℝ)| := by
      have h := natAbs_discr_pow_finrank_le_natAbs_discr K L
      have h' : (((discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) ≤ ((discr L).natAbs : ℝ) := by
        exact_mod_cast h
      simpa [Nat.cast_natAbs, Int.cast_abs] using h'
    have hlog : (Module.finrank K L : ℝ) * Real.log |((discr K : ℤ) : ℝ)| ≤
        Real.log |((discr L : ℤ) : ℝ)| := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hK _) hle
    rw [hNR, div_le_div_iff₀ hnR (mul_pos hnR hmR)]
    nlinarith


set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
theorem _root_.GlobalTheory.FieldSize.sz_mono_and_of_le :
    (∀ (F : IntermediateField ℚ ℂ) (a b a' b' : ℝ), _root_.GlobalTheory.FieldSize.Sz F a b →
        a ≤ a' → b ≤ b' → _root_.GlobalTheory.FieldSize.Sz F a' b') ∧
      ∀ (F F' : IntermediateField ℚ ℂ) (a b : ℝ), F ≤ F' →
        _root_.GlobalTheory.FieldSize.Sz F' a b → _root_.GlobalTheory.FieldSize.Sz F a b := by
  constructor
  · rintro F a b a' b' ⟨hF, h1, h2⟩ ha hb
    exact ⟨hF, h1.trans ha, h2.trans hb⟩
  · rintro F F' a b hFF' ⟨hF', h1, h2⟩
    haveI : FiniteDimensional ℚ F' := hF'
    haveI hF : FiniteDimensional ℚ F :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hFF').toLinearMap
        (IntermediateField.inclusion hFF').injective
    haveI : NumberField F := ⟨⟩
    haveI : NumberField F' := ⟨⟩
    letI : Algebra F F' := (IntermediateField.inclusion hFF').toRingHom.toAlgebra
    obtain ⟨g1, g2⟩ := _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower F F'
    exact ⟨hF, g1.trans h1, g2.trans h2⟩

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory

theorem log_rootDiscr_le_of_natCast_mem_differentIdeal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (N : ℕ), 0 < N → (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) → Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤ Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K + Real.log N := by
  intro K L _ _ _ _ _ N hN hmem
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have h3 : Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) = N ^ Module.finrank ℚ L := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  rw [h3] at h2
  have h4 := Nat.le_of_dvd (pow_pos hN _) h2
  have h5 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L := by
    rw [h1]; exact Nat.mul_le_mul_right _ h4
  have hL : (0 : ℝ) < |((discr L : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero L)
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h6 : |((discr L : ℤ) : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ L * |((discr K : ℤ) : ℝ)| ^ Module.finrank K L := by
    have : (((discr L).natAbs : ℕ) : ℝ) ≤ ((N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) := by
      exact_mod_cast h5
    simpa [Nat.cast_natAbs] using this
  have h7 := Real.log_le_log hL h6
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h7
  have h8 : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ K L
  have hk : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hl : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have h9 : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by exact_mod_cast h8
  rw [div_le_iff₀ hl]
  refine h7.trans (le_of_eq ?_)
  rw [← h9]
  field_simp
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
section
set_option autoImplicit false

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem sz_adjoin_rootOfUnity :
    ∀ n : ℕ, 0 < n → Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set F := ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ with hF
  haveI hc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [hF, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hn).tower_top (A := ℚ)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hfd : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {n} ℚ F
  refine ⟨hfd, ?_⟩
  letI : NumberField F := NumberField.mk
  have hrk : Module.finrank ℚ F = Nat.totient n :=
    IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hn)
  have ht : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have htR : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast ht
  have hd : (NumberField.discr F).natAbs ≤ n ^ Nat.totient n := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr n F]
    exact Nat.div_le_self _ _
  refine ⟨?_, ?_⟩
  · rw [hrk]
    exact Real.log_le_log htR (by exact_mod_cast Nat.totient_le n)
  · rw [hrk, div_le_iff₀ htR, mul_comm, ← Real.log_pow]
    have h0 : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
    refine Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hd

end GlobalTheory.FieldSize
end

