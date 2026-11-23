module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
section
noncomputable section

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5 Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

theorem IsNTr.isPrimitiveRoot_zt (ε : Ω →+* ℂ) (l n : ℕ) [NeZero l] : IsPrimitiveRoot (zt ε l n) (l ^ n) := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ ε.injective
  have he : ε (zt ε l n) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ)) := by
    rw [zt, (eOm_props ε ε.injective).1]
    congr 1; push_cast; ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ (NeZero.ne l))

theorem IsNTr.zt_pow (ε : Ω →+* ℂ) (l m k : ℕ) [NeZero l] : zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  apply ε.injective
  rw [map_pow, zt, zt, (eOm_props ε ε.injective).1, (eOm_props ε ε.injective).1, ← Complex.exp_nat_mul]
  congr 1; push_cast; field_simp; ring


open Classical in
theorem IsNTr.card_filter (l n m : ℕ) [hl : Fact l.Prime] (hm : 1 ≤ m) (hmn : m ≤ n) :
    (Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m])).card = l ^ (n - m) := by
  have hd : l ^ m ∣ l ^ n := pow_dvd_pow l hmn
  have hk : (Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m])).card =
      Nat.card (ZMod.unitsMap hd).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    refine Finset.filter_congr fun a _ => ?_
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Nat.cast_one,
      Units.val_one]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZMod.unitsMap hd).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hd)).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := (ZMod (l ^ m))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hl.out (by omega), Nat.totient_prime_pow hl.out (by omega), ← hk] at h1
  have hpos : 0 < l ^ (m - 1) * (l - 1) := Nat.mul_pos (pow_pos hl.out.pos _) (by have := hl.out.two_le; omega)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← h1, mul_right_comm, ← pow_add]
  congr 2; omega

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
section
noncomputable section

namespace GlobalTheory.Cyc.Model

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

variable {l : ℕ} [Fact l.Prime]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isom_gal (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Isometry (g : _root_.Formalism.BasicNotions.Loc.Om l →+* _root_.Formalism.BasicNotions.Loc.Om l) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x => ?_
  change spectralNorm ℚ_[l] (PadicAlgCl l) (g x) = spectralNorm ℚ_[l] (PadicAlgCl l) x
  exact (spectralNorm_eq_of_equiv g x).symm

def extHom (g : GQ l) : PadicComplex l →+* PadicComplex l :=
  UniformSpace.Completion.mapRingHom (g : Om l →+* Om l) (isom_gal g).continuous

theorem extHom_coe (g : GQ l) (x : Om l) : extHom g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem extHom_cont (g : GQ l) : Continuous (extHom g) := UniformSpace.Completion.continuous_map

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem continuous_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Continuous (_root_.GlobalTheory.Cyc.Model.extHom g) :=
  UniformSpace.Completion.continuous_extension

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem cyc_extHom_coe (g : _root_.Formalism.BasicNotions.Loc.GQ l) (x : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Cyc.Model.extHom g (x : PadicComplex l) = ((g x : _root_.Formalism.BasicNotions.Loc.Om l) : PadicComplex l) := by
  simp only [_root_.GlobalTheory.Cyc.Model.extHom, UniformSpace.Completion.mapRingHom]
  rw [UniformSpace.Completion.extensionHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_mul (g h : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (g * h) y =
      _root_.GlobalTheory.Cyc.Model.extHom g (_root_.GlobalTheory.Cyc.Model.extHom h y) := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (continuous_cyc_extHom _)
    ((continuous_cyc_extHom g).comp (continuous_cyc_extHom h))) fun x => ?_
  rw [cyc_extHom_coe, cyc_extHom_coe, cyc_extHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_one (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (1 : _root_.Formalism.BasicNotions.Loc.GQ l) y = y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_cyc_extHom _) continuous_id) fun x => ?_
  rw [cyc_extHom_coe]; rfl

def actC : GQ l →* (PadicComplex l ≃+* PadicComplex l) where
  toFun g := { extHom g with
    invFun := extHom g⁻¹
    left_inv := fun y => by
      change extHom g⁻¹ (extHom g y) = y
      rw [← extHom_mul, inv_mul_cancel, extHom_one]
    right_inv := fun y => by
      change extHom g (extHom g⁻¹ y) = y
      rw [← extHom_mul, mul_inv_cancel, extHom_one] }
  map_one' := by ext y; exact extHom_one y
  map_mul' g h := by ext y; exact extHom_mul g h y

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem norm_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    ‖_root_.GlobalTheory.Cyc.Model.extHom g y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_norm.comp (continuous_cyc_extHom g)) continuous_norm) fun x => ?_
  rw [cyc_extHom_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact (_root_.GlobalTheory.Cyc.Model.isom_gal g).norm_map_of_map_zero (map_zero _) x

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isActC_actC :
    _root_.GlobalTheory.Cyc.IsActC (_root_.GlobalTheory.Cyc.Model.actC (l := l)) :=
  ⟨fun g x => cyc_extHom_coe g x, fun g y => norm_cyc_extHom g y⟩

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.cyc_irred (n : ℕ) :
    Irreducible (cyclotomic (l ^ (n + 1)) ℚ_[l]) := by
  have hP : (Ideal.span {(l : ℤ_[l])}).IsPrime :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  have hnu : ¬ IsUnit (l : ℤ_[l]) := fun h => hP.ne_top (Ideal.span_singleton_eq_top.2 h)
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l n
  have hmap : taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l]) =
      ((cyclotomic (l ^ (n + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[l]) := by
    rw [taylor_apply, Polynomial.map_comp, map_cyclotomic]; simp
  have hmon : (taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l])).Monic := by
    rw [taylor_apply]; exact (cyclotomic.monic _ _).comp_X_add_C 1
  have hdeg : (taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l])).natDegree =
      ((cyclotomic (l ^ (n + 1)) ℤ).comp (X + 1)).natDegree := by
    rw [natDegree_taylor, natDegree_comp, natDegree_cyclotomic, natDegree_cyclotomic,
      show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
  have hZ : Irreducible (cyclotomic (l ^ (n + 1)) ℤ_[l]) := by
    rw [← MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ_[l]))]
    change Irreducible (taylor (1 : ℤ_[l]) _)
    refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro k hk
      rw [degree_eq_natDegree hmon.ne_zero, Nat.cast_lt, hdeg] at hk
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hE.mem hk)
      rw [hmap, coeff_map, Ideal.mem_span_singleton, hd]
      exact ⟨d, by simp⟩
    · rw [degree_eq_natDegree hmon.ne_zero, natDegree_taylor, natDegree_cyclotomic, Nat.cast_pos]
      exact Nat.totient_pos.2 (pow_pos (Fact.out : l.Prime).pos _)
    · rw [taylor_coeff_zero, eval_one_cyclotomic_prime_pow, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hnu
      have hl : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
      refine isUnit_iff_exists_inv.2 ⟨c, mul_left_cancel₀ hl ?_⟩
      rw [mul_one, ← mul_assoc, ← pow_two]; exact hc.symm
  have h := (cyclotomic.monic (l ^ (n + 1)) ℤ_[l]).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[l]) |>.1 hZ
  rwa [map_cyclotomic] at h

end GlobalTheory.Cyc.Model
end
end

