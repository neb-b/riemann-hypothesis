module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfAffineHyperplaneLineSums
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.FiniteRadon


open Classical in
theorem card_annihilator_mul (k W : Type) [Field k] [Fintype k] [AddCommGroup W] [Module k W]
    [Fintype (Module.Dual k W)] (y : W) (hy : y ≠ 0) :
    Fintype.card k * (Finset.univ.filter (fun g : Module.Dual k W => g y = 0)).card
      = Fintype.card (Module.Dual k W) := by
  let ev : Module.Dual k W →ₗ[k] k := Module.Dual.eval k W y
  have hev : ∀ g, ev g = g y := fun g => rfl
  have hs : Function.Surjective ev := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hy
    intro t
    exact ⟨t • f, by simp [hev, hf]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ev)
  have h2 : Nat.card (Module.Dual k W ⧸ LinearMap.ker ev) = Nat.card k :=
    Nat.card_congr (ev.quotKerEquivOfSurjective hs).toEquiv
  have h3 : Nat.card (LinearMap.ker ev)
      = (Finset.univ.filter (fun g : Module.Dual k W => g y = 0)).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => by simp [LinearMap.mem_ker, hev]))
  rw [← h3, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h1, h2, mul_comm]

theorem eq_zero_of_hyperplane_sums (k W M : Type) [Field k] [Fintype k] [DecidableEq k]
    [AddCommGroup W] [Module k W] [Finite W] [AddCommGroup M] [Module ℂ M] (ψ : W → M)
    (_h0 : ψ 0 = 0)
    (h1 : ∀ g : Module.Dual k W, g ≠ 0 → ∑ᶠ x ∈ {x | g x = 1}, ψ x = 0)
    (h2 : ∀ x, ∑ a : kˣ, ψ ((a : k) • x) = 0) (x0 : W) : ψ x0 = 0 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (Module.Dual k W) :=
    Finite.of_injective (fun g : Module.Dual k W => (g : W → k)) DFunLike.coe_injective
  haveI : Fintype (Module.Dual k W) := Fintype.ofFinite _
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hcancel : ∀ (n : ℕ) (m : M), n ≠ 0 → n • m = 0 → m = 0 := by
    intro n m hn h
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h
    rw [← one_smul ℂ m, ← inv_mul_cancel₀ hn', mul_smul, h, smul_zero]
  have A : ∀ (g : Module.Dual k W) (t : k), ∑ x, (if g x = t then ψ x else 0) = 0 := by
    intro g t
    by_cases ht : t = 0
    · subst ht
      apply hcancel (Fintype.card kˣ) _ Fintype.card_ne_zero
      have e : ∀ a : kˣ, ∑ x, (if g x = 0 then ψ x else 0)
          = ∑ x, (if g x = 0 then ψ ((a : k) • x) else 0) := by
        intro a
        rw [← Equiv.sum_comp (MulAction.toPerm a)]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [MulAction.toPerm, Units.smul_def]
      rw [← Finset.card_univ, ← Finset.sum_const, Finset.sum_congr rfl (fun a _ => e a),
        Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : g x = 0
      · simp only [hx, if_true]; exact h2 x
      · simp [hx]
    · by_cases hg : g = 0
      · subst hg
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [Ne.symm ht]
      · have h := h1 (t⁻¹ • g) (smul_ne_zero (inv_ne_zero ht) hg)
        rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
        refine Eq.trans ?_ h
        refine Finset.sum_congr rfl fun x _ => ?_
        have : (t⁻¹ • g) x = 1 ↔ g x = t := by
          simp only [LinearMap.smul_apply, smul_eq_mul]
          rw [inv_mul_eq_one₀ ht, eq_comm]
        simp only [Set.indicator_apply, Set.mem_setOf_eq, this]
  have T : ∑ x, ψ x = 0 := by simpa using A 0 0
  have B : ∑ x, (Finset.univ.filter (fun g : Module.Dual k W => g (x - x0) = 0)).card • ψ x
      = 0 := by
    have : ∑ g : Module.Dual k W, ∑ x, (if g x = g x0 then ψ x else 0) = 0 :=
      Finset.sum_eq_zero fun g _ => A g _
    rw [Finset.sum_comm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const]
    simp only [map_sub, sub_eq_zero]
  set N := Fintype.card (Module.Dual k W) with hN
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
  have C : ∀ x, Fintype.card k •
      ((Finset.univ.filter (fun g : Module.Dual k W => g (x - x0) = 0)).card • ψ x)
      = N • ψ x + (if x = x0 then (r * N) • ψ x0 else 0) := by
    intro x
    rw [← mul_smul]
    by_cases hx : x = x0
    · subst hx
      simp only [sub_self, map_zero, Finset.filter_true, Finset.card_univ, if_true, hr]
      rw [← add_smul]; congr 1; ring
    · have := card_annihilator_mul k W (x - x0) (sub_ne_zero.mpr hx)
      rw [if_neg hx, add_zero, hN, ← this]
      congr!
  have D := congrArg (fun m => Fintype.card k • m) B
  simp only [Finset.smul_sum, C] at D
  simp only [smul_zero, Finset.sum_add_distrib, ← Finset.smul_sum, T,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at D
  exact hcancel _ _ (Nat.mul_ne_zero (show r ≠ 0 by omega) Fintype.card_ne_zero) D

end GlobalTheory.FiniteRadon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef.RealMove

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  let L := Matrix.toLin' P
  let b := Module.finBasis ℂ (LinearMap.range L)
  let e := Pi.basisFun ℂ (Fin m)
  refine ⟨_, LinearMap.toMatrix b e (LinearMap.range L).subtype, LinearMap.toMatrix e b L.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_codRestrict, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' P
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b]
    congr 1
    ext ⟨_, y, rfl⟩ : 1
    apply Subtype.ext
    show L (L y) = L y
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP]

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := by
  obtain ⟨p, U, V, h1, h2⟩ := exists_factor P hP
  refine ⟨p, by rw [← h1, Matrix.trace_mul_comm, h2]; simp, fun a => ?_⟩
  have e : P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      1 + (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (V ⊗ₖ (a - 1)) := by
    rw [← Matrix.mul_kronecker_mul, h1, Matrix.one_mul, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  have e2 : 1 + (V ⊗ₖ (a - 1)) * (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ a := by
    rw [← Matrix.mul_kronecker_mul, h2, Matrix.mul_one, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  rw [e, Matrix.det_one_add_mul_comm, e2, Matrix.det_kronecker]
  simp

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := by
  obtain ⟨P, hPd⟩ : ∃ P, P = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have hQ : (1 / 2 : ℂ) • (1 - s) = 1 - P := by rw [hPd]; module
  have hP : P * P = P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, mul_add, hs, one_mul, mul_one, one_mul]; module
  obtain ⟨p, hp, hd⟩ := det_idem_kron (n := n) P hP
  refine ⟨p, ?_, fun a b hb => ?_⟩
  · rw [hPd, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hp
    linear_combination 2 * hp
  have hc : P * b = b * P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hb, one_mul, mul_one]
  have hc2 : P * b * P = P * b := by rw [mul_assoc, ← hc, ← mul_assoc, hP]
  rw [← hPd, hQ]
  constructor
  · have e1 : (1 / 2 : ℂ) • ((1 + s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) * (b ⊗ₖ aᵀ)) +
        (1 / 2 : ℂ) • (1 - s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
        (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hQ, hPd, Matrix.transpose_one, add_mul, ← Matrix.mul_kronecker_mul, Matrix.smul_mul, add_mul, one_mul, one_mul,
        one_mul, ← Matrix.one_kronecker_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((P * b + (1 - P)) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
          (P ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      have f1 : (P * b + (1 - P)) * P = P * b := by rw [add_mul, hc2, sub_mul, one_mul, hP, sub_self, add_zero]
      have f2 : (P * b + (1 - P)) * (1 - P) = 1 - P := by rw [mul_sub, f1, mul_one]; abel
      rw [mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, f1, f2, one_mul, one_mul]
    unfold GlobalTheory.WeilParts.detPlus
    rw [e1, e2, Matrix.det_mul, hd, Matrix.det_kronecker]
    simp
  · rw [← Matrix.det_mul]
    congr 1
    have f3 : P * b * ((1 - P) * b) = 0 := by
      rw [← mul_assoc, mul_sub, mul_one, hc2, sub_self, zero_mul]
    have f4 : (1 - P) * ((1 - P) * b) = (1 - P) * b := by
      rw [← mul_assoc, sub_mul, mul_sub, mul_sub, hP]; simp
    have f5 : (1 - P) * P = 0 := by rw [sub_mul, hP, one_mul, sub_self]
    rw [add_mul, mul_add, mul_add, f3, f4, f5, hc2, sub_mul]; simp

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := by
  obtain ⟨n, hn, h0, h⟩ := hχ
  obtain ⟨n', hn', -, h'⟩ := hη
  have e : n' = 1 := by
    have : (n' : ℚ) = 1 := by rw [hn']; norm_num
    exact_mod_cast this
  subst e
  refine ⟨n - k, by push_cast; rw [hn]; ring, h0, fun θ hθ x h1 h2 => ?_⟩
  have hne : θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
    have := h' θ hθ x h1 h2
    rw [zpow_one] at this
    rw [← this]; exact Circle.coe_ne_zero _
  rw [zpow_sub₀ hne, ← h θ hθ x h1 h2, zpow_natCast]
  have := h' θ hθ x h1 h2
  rw [zpow_one] at this
  rw [← this]
  simp [div_eq_mul_inv]

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  rw [← sub_eq_zero]
  exact hσ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
    rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]


open Classical in
theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1, by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := adele_ext hθ (by rw [RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul]) fun τ' => by
    rw [RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) :=
  (RingHom.map_det ((θ τ).comp (infPart D)) M).symm

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  have key : ∀ z : AE D, finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a x => rfl
  rw [key, hz, map_one]

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  choose x hx1 hx2 using fun τ => exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν c hc => ?_⟩
  · refine adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine Finset.prod_congr rfl fun τ _ => ?_
    obtain ⟨n, hn, -, h⟩ := hc τ
    have e : n = 2 * c τ := by exact_mod_cast hn
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2, e, ← hw1, _root_.zpow_mul]
    simp

end GlobalTheory.OneMapRef.RealMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

theorem exists_haar_prod {G H I : Type} [Fintype I] {U : I → Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [Group H] [TopologicalSpace H] [∀ i, Group (U i)] [∀ i, TopologicalSpace (U i)]
    [∀ i, IsTopologicalGroup (U i)] [∀ i, MeasurableSpace (U i)] [∀ i, BorelSpace (U i)]
    [∀ i, SecondCountableTopology (U i)] [∀ i, LocallyCompactSpace (U i)]
    (ν : ∀ i, Measure (U i)) [∀ i, (ν i).IsHaarMeasure] (e : G ≃ₜ* (∀ i, U i) × H) (K : Subgroup H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ B : ∀ i, Set (U i), (∀ i, MeasurableSet (B i)) →
      μ {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = ∏ i, ν i (B i) := by
  let j : H →* G := (e.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Topology.IsEmbedding j :=
    e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : ∀ i, U i))
  haveI : IsTopologicalGroup H := hj.isInducing.topologicalGroup j
  haveI : SecondCountableTopology H := hj.secondCountableTopology
  haveI : T2Space H := hj.t2Space
  haveI : LocallyCompactSpace H :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let K0 : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by
      show (interior (K : Set H)).Nonempty
      rw [hKo.interior_eq]; exact ⟨1, K.one_mem⟩⟩
  let m : Measure ((∀ i, U i) × H) := (Measure.pi ν).prod (Measure.haarMeasure K0)
  haveI : m.IsHaarMeasure := inferInstanceAs (((Measure.pi ν).prod (Measure.haarMeasure K0)).IsHaarMeasure)
  refine ⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB => ?_⟩
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  rw [hme.map_apply]
  have : e.symm ⁻¹' {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = (Set.univ.pi B) ×ˢ (K : Set H) := by
    ext x
    simp [and_comm]
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have h1 : Measure.haarMeasure K0 (K : Set H) = 1 := Measure.haarMeasure_self
  rw [h1, mul_one]

theorem mat_mul {P Q : ℕ} (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem exists_upq_mul {P Q M : ℕ} (A A' : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (B B' : Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ) (h1 : A * B = 1) (h2 : B * A = 1) (h3 : A' * B' = 1)
    (h4 : B' * A' = 1) (h : Aᴴ * Formalism.UG.Jpq P Q * A = A'ᴴ * Formalism.UG.Jpq P Q * A') :
    ∃ u : UpqT P Q, UpqT.mat u * A = A' := by
  let g : GL (Fin P ⊕ Fin Q) ℂ := ⟨A' * B, A * B',
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, h3],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h4, Matrix.one_mul, h1]⟩
  have hg : g ∈ Formalism.UG.Upq P Q := by
    show (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Formalism.UG.Jpq P Q
    calc (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Bᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (A * B)ᴴ * Formalism.UG.Jpq P Q * (A * B) := by
          rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq P Q := by rw [h1]; simp
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P Q), ?_⟩
  show A' * B * A = A'
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem exists_isVolMeasF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (τ i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (τ i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := _root_.GlobalTheory.Mem.InfGroup.real_points F E cm.sig W.rank W.gram I τ θ (fun ρ => (W.sig (τ ρ)).1)
    (fun ρ => (W.sig (τ ρ)).2) A hcm hτ hθ1 (fun i => hW (τ i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E cm.sig W.rank W.gram
  obtain ⟨L, hL, hLfg, hLsp⟩ := GlobalTheory.Mem.Vol.latC_full_lattice E W
  obtain ⟨K, hK, hKo, hKc⟩ := _root_.GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E cm.sig W.rank W.gram L hLfg hLsp
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := cd.haar
  let e : HA (AF F) cm.sig W.gram ≃ₜ*
      (∀ i, UpqT (W.sig (τ i)).1 (W.sig (τ i)).2) × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) cm.sig W.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod (fun i => cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2) e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' B hB => ?_⟩
  have hu : ∀ i, ∃ u : UpqT (W.sig (τ i)).1 (W.sig (τ i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2
      ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) =
      cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (cd.haar (W.sig (τ i)).1 (W.sig (τ i)).2)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK, (he0 h).1, hL]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat cm.sig W.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat cm.sig W.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.Mem.VolExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity : ∀ (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (M' : Matrix (Fin n) (Fin n) ℂ), M 0 = 1 → (∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) → HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧ ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  first | exact @GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv | exact GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv | (intros; apply GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv <;> assumption)
end

