module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLe
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_psi_le (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2)
      = s (LinearMap.charpoly (g.restrict hg)) := by
  rw [_root_.GlobalTheory.CuspGL.charpoly_eq_finsum_psi F A s (g.restrict hg)]
  let e : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W} ≃
      {W' : Submodule F A // ∀ x ∈ W', g.restrict hg x ∈ W'} :=
    { toFun := fun W => ⟨W.1.comap A.subtype, fun x hx => by
        simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply] at hx ⊢
        exact W.2.2 _ hx⟩
      invFun := fun W' => ⟨W'.1.map A.subtype, Submodule.map_subtype_le _ _, fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        exact Submodule.mem_map.2 ⟨_, W'.2 y hy, rfl⟩⟩
      left_inv := fun W => Subtype.ext (by
        change (W.1.comap A.subtype).map A.subtype = W.1
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.2 W.2.1)
      right_inv := fun W' => Subtype.ext (Submodule.comap_map_eq_of_injective A.injective_subtype _) }
  rw [← finsum_comp_equiv e]
  congr 1
  funext W
  have hc : (Submodule.comapSubtypeEquivOfLe W.2.1).conj
      ((g.restrict hg).restrict (e W).2) = g.restrict W.2.2 := by
    ext x
    simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe]
  rw [← hc, _root_.GlobalTheory.CuspGL.psi_conj]
  rfl

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIcoStatement
section
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), (∀ j : ℕ, s ((X - C 1) ^ j) = j) → 0 < Module.finrank F V → psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.psi_one | exact GlobalTheory.CuspGL.psi_one | (intros; apply GlobalTheory.CuspGL.psi_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSum
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem ipGL_rootSum_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ l : ℕ, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1}, ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) * mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ V _ _ _ θ φ hcl hprim hpos l
  rw [ipGL_charpoly_eq_finsum_mass F V φ (rootSum θ l)]
  refine sum_poly_eq_sum_torus F θ (Module.finrank F V) hpos (mass φ) l ?_

  intro P _ _ hP
  unfold mass
  rw [finsum_mem_def]
  refine finsum_eq_zero_of_forall_eq_zero fun g => ?_
  by_cases hg : LinearMap.charpoly g = P
  · rw [Set.indicator_of_mem (show g ∈ {g : Module.End F V | LinearMap.charpoly g = P} from hg)]
    exact _root_.GlobalTheory.CuspGL.eq_zero_of_not_primary F V φ hcl hprim hpos g (hg ▸ hP)
  · exact Set.indicator_of_notMem (show g ∉ {g : Module.End F V | LinearMap.charpoly g = P} from hg) _

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterEsymmRootsCharpoly
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def compoundRep {G : Type} [Group G] {n : ℕ} (j : ℕ) (ρ : G →* GL (Fin n) ℂ) :
    Representation ℂ G (Set.powersetCard (Fin n) j → ℂ) where
  toFun g := Matrix.toLin' (GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, GlobalTheory.compoundMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, GlobalTheory.compoundMatrix_mul, Matrix.toLin'_mul]; rfl

open Polynomial in
private lemma det_submatrix_subsetEnum_eq_det_submatrix_val {n j : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Set.powersetCard (Fin n) j) :
    (A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S)).det =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).det := by
  have hmem : ∀ i, _root_.GlobalTheory.subsetEnum S i ∈ S.1 := fun i => by
    have : _root_.GlobalTheory.subsetEnum S i ∈ Set.range (_root_.GlobalTheory.subsetEnum S) :=
      ⟨i, rfl⟩
    rw [_root_.GlobalTheory.range_subsetEnum] at this
    exact_mod_cast this
  let σ : Fin j ≃ {x // x ∈ S.1} := Equiv.ofBijective
    (fun i => ⟨_root_.GlobalTheory.subsetEnum S i, hmem i⟩)
    ⟨fun a b hab => _root_.GlobalTheory.subsetEnum_injective S (congrArg Subtype.val hab),
      fun x => by
        have hx : x.1 ∈ ((S.1 : Finset (Fin n)) : Set (Fin n)) := x.2
        rw [← _root_.GlobalTheory.range_subsetEnum] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩
  have hsub : A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S) =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).submatrix σ σ := rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

open Polynomial in
private lemma trace_compoundMatrix_eq_sum_principal_minors {n : ℕ} (j : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.compoundMatrix j A).trace = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) => s ∈ Set.powersetCard (Fin n) j) _
    (fun s => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  unfold _root_.GlobalTheory.compoundMatrix
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact Finset.sum_congr rfl fun S _ => det_submatrix_subsetEnum_eq_det_submatrix_val A S

open Polynomial in
private lemma esymm_roots_charpoly_eq_sum_principal_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  rcases le_or_gt j n with hj | hj
  · have h1 := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have h2 := M.charpoly_coeff_eq_sum_minors j (by simp [hj])
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at h1
    rw [Fintype.card_fin, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2
  · rw [Finset.powersetCard_eq_empty.mpr (by simp [hj]), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp


open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_esymm_roots_charpoly :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by
  intro G _ n j ρ
  have h := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (_root_.GlobalTheory.BI.compoundRep j ρ)).1
  have heq : (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) =
      fun g => algebraMap ℂ ℂ ((_root_.GlobalTheory.BI.compoundRep j ρ).character g) := by
    funext g
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = LinearMap.trace ℂ _
      (Matrix.toLin' (_root_.GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ)))
    rw [Matrix.trace_toLin'_eq, trace_compoundMatrix_eq_sum_principal_minors, esymm_roots_charpoly_eq_sum_principal_minors]
  rw [heq]
  exact h

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_ind : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L),
    IsChar K L ψ → IsChar K L (ind H ψ) := by
  intro K L _ _ _ _ _ G _ _ H ψ h
  have hcl : ∀ a x : H, ψ (x⁻¹ * a * x) = ψ a := (_root_.GlobalTheory.isChar_restrict_conj_one K L H ψ h).2.1
  have e : ind H ψ = fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) :=
    funext (_root_.GlobalTheory.BI.ind_eq_finsum_cosets L G H ψ hcl)
  rw [e]
  exact _root_.GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar K L G H ψ h
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL

theorem exists_linearEquiv_mem_iff_of_finrank_eq {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B : Submodule F V) (h : Module.finrank F A = Module.finrank F B) :
    ∃ e : V ≃ₗ[F] V, ∀ x, e x ∈ B ↔ x ∈ A := by
  obtain ⟨A', hA⟩ := A.exists_isCompl
  obtain ⟨B', hB⟩ := B.exists_isCompl
  have h' : Module.finrank F A' = Module.finrank F B' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hA
    have h2 := Submodule.finrank_add_eq_of_isCompl hB
    omega
  let e1 := LinearEquiv.ofFinrankEq A B h
  let e2 := LinearEquiv.ofFinrankEq A' B' h'
  refine ⟨(Submodule.prodEquivOfIsCompl A A' hA).symm ≪≫ₗ (e1.prodCongr e2) ≪≫ₗ
    Submodule.prodEquivOfIsCompl B B' hB, fun x => ?_⟩
  obtain ⟨⟨a, a'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A A' hA).surjective x
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
  rw [B.add_mem_iff_right (e1 a).2, A.add_mem_iff_right a.2,
    Submodule.mem_left_iff_eq_zero_of_disjoint hB.disjoint,
    Submodule.mem_left_iff_eq_zero_of_disjoint hA.disjoint]
  simp

theorem finsum_nilRad_extZero_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hχ : IsChar ℂ ℂ χ) (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F))
    (hb : Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1)
      (H : Set (GL (Fin d) F)) (nilRad A))
    (h0 : ∑ᶠ u ∈ (H : Set (GL (Fin d) F)), χ u = 0)
    (g : Module.End F (Fin d → F)) (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ h ∈ nilRad A, extZero χ (g + h) = 0 := by
  obtain ⟨e1, e2, -, -⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ
  by_cases hu : IsUnit g
  · have hm : IsUnit (LinearMap.toMatrix' g) := by
      have := hu.map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin d))
      exact this
    obtain ⟨x, hx⟩ := hm
    have hgx : Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
      rw [hx, Matrix.toLin'_toMatrix']
    have : Finite (Module.End F (Fin d → F)) := Module.finite_of_finite F
    have hb2 : Set.BijOn (fun h : Module.End F (Fin d → F) => g * h) (nilRad A) (nilRad A) := by
      refine ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo ?_).1 ?_
      · intro h hh
        exact ⟨fun y => hg _ (hh.1 y), fun y hy => by simp [hh.2 y hy]⟩
      · intro a _ b _ hab
        exact hu.mul_left_cancel hab
    have h1 := _root_.GlobalTheory.BI.char_coset_sum_eq_zero _ χ hχ H
      ((finsum_set_coe_eq_finsum_mem (f := χ) (H : Set (GL (Fin d) F))).trans h0) x
    have h2 := (finsum_set_coe_eq_finsum_mem (f := fun u => χ (x * u)) (H : Set (GL (Fin d) F))).symm.trans h1
    rw [← h2]
    symm
    refine finsum_mem_eq_of_bijOn _ (hb2.comp hb) fun u _ => ?_
    rw [← e1]
    congr 1
    simp only [Function.comp, Units.val_mul, Matrix.toLin'_mul, hgx, mul_sub, mul_one]
    rw [add_sub_cancel]
    rfl
  · refine finsum_mem_of_eqOn_zero fun h hh => ?_
    refine e2 _ fun hu' => hu ?_
    have hc := (_root_.GlobalTheory.CuspGL.charpoly_block F _ A g hg).2 h hh
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff] at hu' ⊢
    rwa [hc] at hu'

theorem isPrimitive_extZero_of_sum_unipotent : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  intro F _ _ d χ hχ hs A hA0 hA1 g hg
  have ha0 : 0 < Module.finrank F A := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hA0 (Submodule.finrank_eq_zero.1 h)
  have ha1 : Module.finrank F A < d := by
    have := Submodule.finrank_lt hA1
    simpa using this
  obtain ⟨B, H, hB, hH, hb⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d _ ha1.le
  have h0 := hs _ ha0 ha1
  rw [← hH] at h0
  obtain ⟨e, he⟩ := exists_linearEquiv_mem_iff_of_finrank_eq A B hB.symm
  have hcl := (_root_.GlobalTheory.CuspGL.extZero_spec F d χ).2.2.2 (GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ hχ).2.1
  have key := finsum_nilRad_extZero_eq_zero F d χ hχ B H hb h0 (e.conj g) (fun x hx => by
    rw [LinearEquiv.conj_apply_apply, he]
    apply hg
    rw [← he]
    simpa using hx)
  rw [← key]
  refine finsum_mem_eq_of_bijOn (fun h => e.conj h) ⟨fun h hh => ⟨fun y => ?_, fun y hy => ?_⟩,
    e.conj.injective.injOn, fun h hh => ⟨e.symm.conj h, ⟨fun y => ?_, fun y hy => ?_⟩, by ext y; simp [LinearEquiv.conj_apply_apply]⟩⟩ fun h _ => ?_
  · rw [LinearEquiv.conj_apply_apply, he]
    exact hh.1 _
  · rw [LinearEquiv.conj_apply_apply, hh.2 _ (by rw [← he]; simpa using hy), map_zero]
  · rw [← he, LinearEquiv.conj_apply_apply]
    simpa using hh.1 _
  · rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, hh.2 _ ((he y).2 hy), map_zero]
  · rw [← map_add (f := _), hcl]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OrthogonalIntVectorsNotAgreeOnRegular
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private lemma abs_sum_le_sum_sq_int (s : Finset ℕ) (a : ℕ → ℤ) :
    |∑ k ∈ s, a k| ≤ ∑ k ∈ s, a k ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rcases eq_or_ne (a k) 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |a k| := Int.one_le_abs h
    nlinarith [sq_abs (a k)]

theorem orthogonal_int_vectors_not_agree_on_regular :
    ∀ (q n : ℕ) (ω : ℂ) (a b : ℕ → ℤ), 2 ≤ q → 0 < n → IsPrimitiveRoot ω (q ^ n - 1) → ∑ k ∈ Finset.range (q ^ n - 1), a k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), b k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), a k * b k = 0 → 0 < (∑ k ∈ Finset.range (q ^ n - 1), a k) * (∑ k ∈ Finset.range (q ^ n - 1), b k) → (∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) → ∑ k ∈ Finset.range (q ^ n - 1), (a k : ℂ) * ω ^ (j * k) = ∑ k ∈ Finset.range (q ^ n - 1), (b k : ℂ) * ω ^ (j * k)) → False := by
  intro q n ω a b hq hn hω ha2 hb2 hab hpos hreg
  have hN : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hc2 : ∑ k ∈ Finset.range (q ^ n - 1), (a k - b k) ^ 2 = 2 * (n : ℤ) := by
    have e : ∀ k, (a k - b k) ^ 2 = a k ^ 2 + b k ^ 2 - 2 * (a k * b k) := fun k => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha2, hb2, hab]
    ring
  have hcoef : ∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) →
      ∑ k ∈ Finset.range (q ^ n - 1), (((a k - b k : ℤ)) : ℂ) * ω ^ (j * k) = 0 := by
    intro j hj
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hreg j hj, sub_self]
  by_cases hexc : q = 2 ∧ (n = 4 ∨ n = 6)
  · obtain ⟨rfl, rfl | rfl⟩ := hexc
    · refine _root_.GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h5 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h5
            interval_cases j <;> interval_cases e <;> decide))
    · refine _root_.GlobalTheory.no_norm_twelve_order_sixtythree ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h21 h9 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h21 h9
            interval_cases j <;> interval_cases e <;> decide))
  · have hsum : |∑ k ∈ Finset.range (q ^ n - 1), (a k - b k)| ≤ (n : ℤ) - 1 := by
      rw [Finset.sum_sub_distrib]
      have hA := abs_le.mp ((abs_sum_le_sum_sq_int _ a).trans ha2.le)
      have hB := abs_le.mp ((abs_sum_le_sum_sq_int _ b).trans hb2.le)
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.mpr ⟨by omega, by omega⟩
    have h1 := _root_.GlobalTheory.parsevalSep_bound n (q ^ n - 1) ω (fun k => a k - b k)
      ((Finset.Ioo 0 (q ^ n - 1)).filter
        (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1]))
      hn hN hω hc2 hsum (fun j hj0 hjN hjS => by
        refine hcoef j (fun e he1 he2 he => hjS ?_)
        simp only [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨hj0, hjN⟩, e, ⟨he1, he2⟩, he⟩)
    have h2 := GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le q n hq hn
    have h3 := _root_.GlobalTheory.CuspGL.sep_numerical_ineq q n hq hn hexc
    exact absurd (lt_of_le_of_lt (h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _)) h3)
      (lt_irrefl _)

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionEqZeroOfPrimary
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem primitive_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr f m hf h0
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  have key : ∀ n : ℕ, ∀ g : Module.End F V,
      Module.finrank F V - Module.finrank F (LinearMap.ker (aeval g f)) = n →
      LinearMap.charpoly g = f ^ m → φ g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hn hg
    by_cases htop : LinearMap.ker (aeval g f) = ⊤
    · exact h0 g hg (LinearMap.ker_eq_top.mp htop)
    have hCH : ∀ g' : Module.End F V, LinearMap.charpoly g' = f ^ m → aeval g' (f ^ m) = 0 := by
      intro g' hg'
      rw [← hg']
      exact LinearMap.aeval_self_charpoly g'
    have hbot : LinearMap.ker (aeval g f) ≠ ⊥ := by
      intro hb
      have hinj : Function.Injective (aeval g f : Module.End F V) := LinearMap.ker_eq_bot.mp hb
      have hinj' : Function.Injective ((aeval g f) ^ m : Module.End F V) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate m
      rw [← map_pow, hCH g hg] at hinj'
      apply htop
      rw [hb, eq_comm, eq_bot_iff]
      intro x _
      exact (Submodule.mem_bot F).mpr (hinj' (by simp))
    have hinv : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc : aeval g f * g = g * aeval g f := by
        have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
        simpa using this
      have := congrArg (fun k : Module.End F V => k x) hc
      simpa [hx] using this
    have hsum := hpr _ hbot htop g hinv
    have hfin : (nilRad (LinearMap.ker (aeval g f))).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hterm : ∀ h ∈ hfin.toFinset, φ (g + h) =
        if LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) then φ g else 0 := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      have hcp : LinearMap.charpoly (g + h) = f ^ m := by
        rw [(_root_.GlobalTheory.CuspGL.charpoly_block F V _ g hinv).2 h hh, hg]
      obtain ⟨hle, heq⟩ := _root_.GlobalTheory.CuspGL.ker_aeval_add_nilRad F V g h f hh
      split_ifs with hc
      · obtain ⟨e, he⟩ := _root_.GlobalTheory.CuspGL.primary_conj_of_finrank_ker_eq F V g (g + h) f m hf (hCH g hg) (hCH _ hcp) (heq hc)
        rw [← he, hcl e g]
      · have hlt : LinearMap.ker (aeval g f) < LinearMap.ker (aeval (g + h) f) :=
          lt_of_le_of_ne hle (Ne.symm hc)
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt
        have h2 := Submodule.finrank_le (LinearMap.ker (aeval (g + h) f))
        exact ih _ (by omega) (g + h) rfl hcp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    refine (mul_eq_zero.mp hsum).resolve_left ?_
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨0, ?_⟩
    simp [nilRad]
  intro g hg
  exact key _ g rfl hg

end GlobalTheory.CuspGL
end

