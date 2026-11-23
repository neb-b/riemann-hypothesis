module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaOneGammaZeroHomogeneousCocyclesFinite
section
open scoped MatrixGroups TensorProduct Pointwise
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gam_fg (N l : ℕ) [Fact l.Prime] (hN : 0 < N) : Group.FG (Gam N l) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  exact Subgroup.fg_of_index_ne_zero _

theorem module_finite_z1_padicInt : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  intro N l w _ hN
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.1 (gam_fg N l hN)
  let t : Set (Gam N l) := insert 1 (s ∪ s⁻¹)
  have ht : t.Finite := (hfin.union hfin.inv).insert 1
  haveI : Finite t := ht.to_subtype
  haveI : Module.Finite ℤ_[l] (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  let L : Z1 N l w →ₗ[ℤ_[l]] (t → MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    { toFun := fun c i => ⟨c.1 i.1, c.2.1 i.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun c hc => ?_)
  have h0 : ∀ γ ∈ t, c.1 γ = 0 := fun γ hγ => congrArg Subtype.val (congrFun hc ⟨γ, hγ⟩)
  apply Subtype.ext
  funext γ
  have hγ : γ ∈ Submonoid.closure (s ∪ s⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hs]; trivial
  show c.1 γ = 0
  induction hγ using Submonoid.closure_induction with
  | mem x hx => exact h0 x (Set.mem_insert_of_mem _ hx)
  | one => exact h0 1 (Set.mem_insert _ _)
  | mul x y _ _ hx hy => rw [c.2.2 x y, hx, hy, map_zero, add_zero]

end GlobalTheory.KZ.BettiB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGauss
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique_of_gauss : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.exists_finset_primes_forall_mem_valuationSubring s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have key : ∀ W : ValuationSubring L, Gauss t V W →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.gaussExtension_coeff_mem_nonunits t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ h₁ h₂ (key W₁ h₁))
    (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ h₂ h₁ (key W₂ h₂))

end GlobalTheory.BertiniNoether
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruence
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

open Matrix CongruenceSubgroup


set_option backward.isDefEq.respectTransparency false in
theorem conj_Gamma_den_mul (g : GL (Fin 2) ℚ) (M : ℕ) (y : SL(2, ℤ))
    (hy' : y ∈ Gamma ((g.1.den * (g⁻¹).1.den) * M)) :
    ∃ z ∈ Gamma M, ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      g.1 * ((y : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) * (g⁻¹).1 := by
  obtain ⟨y, hy⟩ := y
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← mul_smul, ← mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, hz_coe⟩
  rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  change z.map (Int.cast : ℤ → ZMod M) = 1
  ext i j
  change (↑((1 : Matrix (Fin 2) (Fin 2) ℤ) i j +
    M • (A₁.num * k * A₂.num) i j) : ZMod M) = (1 : Matrix (Fin 2) (Fin 2) (ZMod M)) i j
  simp [nsmul_eq_mul, Matrix.one_apply]

theorem exists_conj_principal_congruence :
    ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n),
      ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  intro g
  let G : GL (Fin 2) ℚ := g
  refine ⟨G.1.den * (G⁻¹).1.den, Nat.mul_pos (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)) (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)), fun N δ hδ => ?_⟩
  rw [mul_comm] at hδ
  obtain ⟨z, hz, hzc⟩ := conj_Gamma_den_mul G N δ hδ
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have h21 : (G⁻¹).1 * G.1 = 1 := by
    simp only [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  show G.1 * ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
    ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) * G.1
  have e1 : ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  have e2 : ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  rw [e1, e2, hzc, Matrix.mul_assoc, h21, Matrix.mul_one]

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobius
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HermFN

lemma lin_ne_zero (c e : ℤ) (z : ℂ) (hz : 0 < z.im) (h : c ≠ 0 ∨ e ≠ 0) : (c : ℂ) * z + e ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hc
  · subst hc; simp at hre; rcases h with h | h <;> simp_all
  · linarith

lemma common_den (g : GQ) : ∃ N : ℕ, 0 < N ∧ ∀ i j, ∃ z : ℤ, (N : ℚ) * ent g i j = z := by
  refine ⟨∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (ent g i j).den_pos))
  · intro i j
    have hdv : (ent g i j).den ∣ ∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (ent g i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin 2, (ent g i j).den) (Finset.mem_univ i))
    obtain ⟨k, hk⟩ := hdv
    refine ⟨k * (ent g i j).num, ?_⟩
    rw [hk]
    have := Rat.mul_den_eq_num (ent g i j)
    push_cast
    rw [← this]; ring

lemma upper_step (p p' x b dd q : ℤ) (a : ℕ) (τ : ℂ) (hd0 : (dd : ℂ) ≠ 0) (hpC : (p : ℂ) = a * p')
    (hq'C : (p' : ℂ) * b + x * dd = q) :
    ((p' : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((x : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
  rw [hpC, ← hq'C]; field_simp; ring

lemma left_step (m0 m1 A B C D : ℤ) (N : ℕ) (τ : ℂ) (hN : (N : ℂ) ≠ 0) (hD : (C : ℂ) * τ + D ≠ 0) :
    (m0 : ℂ) / N * (((A : ℂ) * τ + B) / ((C : ℂ) * τ + D)) + (m1 : ℂ) / N =
      (((m0 * A + m1 * C : ℤ) : ℂ) * τ + ((m0 * B + m1 * D : ℤ) : ℂ)) / (N * ((C : ℂ) * τ + D)) := by
  have hD' : τ * (C : ℂ) + D ≠ 0 := by rwa [mul_comm]
  rw [eq_div_iff (mul_ne_zero hN hD)]
  push_cast
  field_simp
  ring

end GlobalTheory.HermFN

namespace GlobalTheory.HermFN

theorem hermite (g : GQ) : ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧
    ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  obtain ⟨N, hN, hm⟩ := common_den g
  choose m hm using hm
  have hdetg : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
    have h := g.2
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  set nI : ℤ := m 0 0 * m 1 1 - m 0 1 * m 1 0 with hnI
  have hn : 0 < nI := by
    have hq : (nI : ℚ) = (N : ℚ) ^ 2 * (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0) := by
      rw [hnI]; push_cast; rw [← hm 0 0, ← hm 0 1, ← hm 1 0, ← hm 1 1]; ring
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (0 : ℚ) < nI := by rw [hq]; positivity
    exact_mod_cast this
  refine ⟨nI.toNat, by omega, ?_⟩
  intro γ₀
  have hdet0 : γ₀ 0 0 * γ₀ 1 1 - γ₀ 0 1 * γ₀ 1 0 = 1 := by
    have := γ₀.2; rwa [Matrix.det_fin_two] at this
  set p : ℤ := m 0 0 * γ₀ 0 0 + m 0 1 * γ₀ 1 0 with hp_def
  set r : ℤ := m 1 0 * γ₀ 0 0 + m 1 1 * γ₀ 1 0 with hr_def
  set q : ℤ := m 0 0 * γ₀ 0 1 + m 0 1 * γ₀ 1 1 with hq_def
  set s : ℤ := m 1 0 * γ₀ 0 1 + m 1 1 * γ₀ 1 1 with hs_def
  have hps : p * s - q * r = nI := by
    rw [hp_def, hr_def, hq_def, hs_def, hnI]; linear_combination (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hdet0
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  set a : ℕ := Int.gcd p r with ha_def
  have ha : 0 < a := Int.gcd_pos_iff.mpr hpr
  set p' : ℤ := p / a
  set r' : ℤ := r / a
  have hp : p = a * p' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)).symm
  have hr : r = a * r' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)).symm
  have cop : IsCoprime p' r' := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd ha)
  obtain ⟨γ, h0, h1⟩ := cop.exists_SL2_col 0
  have hγ : p' * γ 1 1 - γ 0 1 * r' = 1 := by
    have := γ.2; rw [Matrix.det_fin_two, h0, h1] at this; linear_combination this
  set b : ℤ := γ 1 1 * q - γ 0 1 * s with hb_def
  set dd : ℤ := p' * s - r' * q with hdd_def
  have had : (a : ℤ) * dd = nI := by
    rw [hdd_def, ← hps]; linear_combination (-s) * hp + q * hr
  have hd : 0 < dd := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith
  have hq' : p' * b + γ 0 1 * dd = q := by rw [hb_def, hdd_def]; linear_combination q * hγ
  have hs' : r' * b + γ 1 1 * dd = s := by rw [hb_def, hdd_def]; linear_combination s * hγ
  refine ⟨γ, a, dd.toNat, b, ?_, ?_⟩
  · zify; rw [Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hn.le]; exact had
  · intro τ
    have hz : 0 < (τ : ℂ).im := τ.im_pos
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hdC : ((dd.toNat : ℕ) : ℂ) = (dd : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hd.le]
    have hd0 : (dd : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hc : ∀ i j, ((ent g i j : ℚ) : ℂ) = (m i j : ℂ) / N := by
      intro i j
      have : ent g i j = (m i j : ℚ) / N := by
        rw [← hm i j]; field_simp
      rw [this]; push_cast; rfl
    have hD0 : ((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ) ≠ 0 := by
      apply lin_ne_zero _ _ _ hz
      by_contra h; push_neg at h; rw [h.1, h.2] at hdet0; simp at hdet0
    have hRS : (r : ℂ) * τ + s ≠ 0 := lin_ne_zero r s _ hz hrs
    have hpC : (p : ℂ) = a * p' := by exact_mod_cast hp
    have hrC : (r : ℂ) = a * r' := by exact_mod_cast hr
    have hq'C : (p' : ℂ) * b + γ 0 1 * dd = q := by exact_mod_cast hq'
    have hs'C : (r' : ℂ) * b + γ 1 1 * dd = s := by exact_mod_cast hs'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, hdC]
    simp only [mob, hc, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    have eL : ((m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N) /
        ((m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N)
        = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
      have e1 : (m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N
          = ((p : ℂ) * τ + q) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 0 0) (m 0 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      have e2 : (m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N
          = ((r : ℂ) * τ + s) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 1 0) (m 1 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hNC hD0)]
    have eR : ((γ 0 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 0 1 : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
      rw [h0]; exact upper_step p p' (γ 0 1) b dd q a τ hd0 hpC hq'C
    have eR2 : ((γ 1 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 1 1 : ℤ) : ℂ) = ((r : ℂ) * τ + s) / dd := by
      rw [h1]; exact upper_step r r' (γ 1 1) b dd s a τ hd0 hrC hs'C
    have hofSL : ∀ i j, ((ent (ofSL γ) i j : ℚ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
      intro i j; show (((γ i j : ℤ) : ℚ) : ℂ) = _; push_cast; rfl
    simp only [hofSL]
    rw [eL, eR, eR2, div_div_div_cancel_right₀ hd0]

end GlobalTheory.HermFN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlaneProperties
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNMob

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := (Matrix.mem_glpos (g : GL (Fin 2) ℚ)).1 g.2
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
  simpa [ent] using h

theorem im_frac (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im = (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem denom_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp at hi hr
  have hz' : 0 < z.im := hz
  have hc : ent g 1 0 = 0 := by
    rcases hi with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hr
  have hd : ent g 1 1 = 0 := by simpa using hr
  have := det_pos g
  rw [hc, hd] at this
  simp at this

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hne := denom_ne g hz
  have e : mob g z = ((((ent g 0 0 : ℝ)) : ℂ) * z + ((ent g 0 1 : ℝ) : ℂ)) /
      ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    simp [mob]
  show 0 < (mob g z).im
  rw [e, im_frac]
  have hn : 0 < Complex.normSq ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    rw [Complex.normSq_pos]; simpa using hne
  have hd : (0 : ℝ) < (ent g 0 0 : ℝ) * (ent g 1 1 : ℝ) - (ent g 0 1 : ℝ) * (ent g 1 0 : ℝ) := by
    exact_mod_cast det_pos g
  have hz' : 0 < z.im := hz
  positivity

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem frac_comp (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  rw [show a * (N / D) + b = (a * N + b * D) / D by field_simp,
    show c * (N / D) + d = (c * N + d * D) / D by field_simp, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have hne := denom_ne h hz
  simp only [mob, ent_mul]
  push_cast
  rw [frac_comp _ _ _ _ _ _ hne]
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by simp [mob, ent]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  have hne := denom_ne g hz
  show DifferentiableWithinAt ℂ (fun z : ℂ => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) /
    ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) Hs z
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) z := by fun_prop
  exact (h1.div h2 hne).differentiableWithinAt

theorem mob_upper (g : GQ) (hc : ent g 1 0 = 0) : 0 < ent g 0 0 / ent g 1 1 ∧
    ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) := by
  have hdet := det_pos g
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : ent g 1 1 ≠ 0 := by rintro h; rw [h, mul_zero] at hdet; exact lt_irrefl _ hdet
  refine ⟨?_, fun z => ?_⟩
  · have : ent g 0 0 / ent g 1 1 = ent g 0 0 * ent g 1 1 / (ent g 1 1 * ent g 1 1) := by
      field_simp
    rw [this]; exact div_pos hdet (mul_self_pos.2 hd)
  · have hd' : (ent g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [mob, hc]
    push_cast
    simp only [zero_mul, zero_add]
    rw [add_div, mul_div_right_comm]

end GlobalTheory.FNMob

theorem GlobalTheory.FN.mob_props : (∀ (g : GQ) (z : ℂ), z ∈ Hs → mob g z ∈ Hs) ∧ (∀ (g h : GQ) (z : ℂ), z ∈ Hs → mob (g * h) z = mob g (mob h z)) ∧ (∀ z : ℂ, mob 1 z = z) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ)) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ ∀ g : GQ, ent g 1 0 = 0 → 0 < ent g 0 0 / ent g 1 1 ∧ ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) :=
  ⟨fun g _ hz => GlobalTheory.FNMob.mob_mem g hz, fun g h _ hz => GlobalTheory.FNMob.mob_mul g h hz, GlobalTheory.FNMob.mob_one,
    GlobalTheory.FNMob.mob_ofSL, GlobalTheory.FNMob.mob_diff, GlobalTheory.FNMob.mob_upper⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSer
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fnShape : ∀ (Ω : Type) [Field Ω] (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → ∃ (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω), 0 < N ∧ a 0 ≠ 0 ∧ (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0 := by
  intro Ω _ h hD h0
  obtain ⟨N, hN, hd⟩ := hD
  have hc : h.coeff h.order ≠ 0 := fun e => h0 (HahnSeries.coeff_order_eq_zero.mp e)
  obtain ⟨n₀, hn₀⟩ := hd _ hc
  refine ⟨N, n₀, fun k => h.coeff (((n₀ + k : ℤ) : ℚ) / N), hN, ?_, fun k => rfl, ?_⟩
  · simpa [← hn₀] using hc
  · intro r hr
    by_contra hne
    obtain ⟨n, rfl⟩ := hd r hne
    have hle : h.order ≤ (n : ℚ) / N := HahnSeries.order_le_of_coeff_ne_zero hne
    rw [hn₀] at hle
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (n₀ : ℚ) ≤ n := by
      have := (div_le_div_iff_of_pos_right hNq).mp hle
      exact this
    have hnn : n₀ ≤ n := by exact_mod_cast this
    apply hr (n - n₀).toNat
    congr 2
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring

end GlobalTheory
end

