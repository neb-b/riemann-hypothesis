module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamily
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma mem_tauPair_lattice_iff (τ : ℍ) (z : ℂ) :
    z ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) * τ + n = z := by
  rw [PeriodPair.mem_lattice]
  simp [_root_.GlobalTheory.QFam.tauPair]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma modularGroup_denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ =
      ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma modularGroup_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← modularGroup_denom_eq]
  exact UpperHalfPlane.denom_ne_zero _ τ

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma coe_modularGroup_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma exists_tors_vact_eq_denom_mul_tors_smul_add (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    ∃ l ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice,
      _root_.GlobalTheory.WpFam.tors N τ (_root_.GlobalTheory.WpFam.vact N x γ) =
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l := by
  have hv0 : _root_.GlobalTheory.WpFam.vact N x γ 0 =
      x 0 * ((γ 0 0 : ℤ) : ZMod N) + x 1 * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  have hv1 : _root_.GlobalTheory.WpFam.vact N x γ 1 =
      x 0 * ((γ 0 1 : ℤ) : ZMod N) + x 1 * ((γ 1 1 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  set y := _root_.GlobalTheory.WpFam.vact N x γ
  have h0 : (N : ℤ) ∣ ((y 0).val : ℤ) - ((x 0).val * γ 0 0 + (x 1).val * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv0]
  have h1 : (N : ℤ) ∣ ((y 1).val : ℤ) - ((x 0).val * γ 0 1 + (x 1).val * γ 1 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv1]
  obtain ⟨k, hk⟩ := h0
  obtain ⟨k', hk'⟩ := h1
  refine ⟨(k : ℂ) * τ + k', (mem_tauPair_lattice_iff τ _).2 ⟨k, k', rfl⟩, ?_⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hD := modularGroup_denom_ne_zero γ τ
  have e0 := congrArg (fun t : ℤ => (t : ℂ)) hk
  have e1 := congrArg (fun t : ℤ => (t : ℂ)) hk'
  push_cast at e0 e1
  have hw : (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * ((γ • τ : ℍ) : ℂ) =
      ((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ) := by
    rw [coe_modularGroup_smul, mul_div_assoc', mul_div_cancel_left₀ _ hD]
  unfold _root_.GlobalTheory.WpFam.tors
  rw [mul_div_assoc', div_add' _ _ _ hN, div_left_inj' hN]
  linear_combination (τ : ℂ) * e0 + e1 - ((x 0).val : ℂ) * hw

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isTauOf_tauPair_denom_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf (_root_.GlobalTheory.QFam.tauPair τ) (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ))
      (γ • τ) := by
  have hD := modularGroup_denom_ne_zero γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have key : ∀ u v : ℤ, (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) *
      ((u : ℂ) * ((γ • τ : ℍ) : ℂ) + v) =
      ((u * γ 0 0 + v * γ 1 0 : ℤ) : ℂ) * τ + ((u * γ 0 1 + v * γ 1 1 : ℤ) : ℂ) := by
    intro u v
    rw [coe_modularGroup_smul]
    field_simp
    push_cast
    ring
  unfold _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf
  refine ⟨hD, fun z => ?_⟩
  rw [mem_tauPair_lattice_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * γ 1 1 - n * γ 1 0, -(m * γ 0 1) + n * γ 0 0, ?_⟩
    have h1 : (m * γ 1 1 - n * γ 1 0) * γ 0 0 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 0 = m := by
      linear_combination m * hdet
    have h2 : (m * γ 1 1 - n * γ 1 0) * γ 0 1 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 1 = n := by
      linear_combination n * hdet
    rw [key, h1, h2]
  · rintro ⟨u, v, rfl⟩
    exact ⟨_, _, (key u v).symm⟩


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.isFam_wp_wpd : ∀ (N : ℕ) [NeZero N],
    _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 2
        (_root_.GlobalTheory.WpFam.wp N) ∧
      _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 3
        (_root_.GlobalTheory.WpFam.wpd N) := by
  intro N _
  constructor
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wp
    rw [hP, hper, hom.2.1, zpow_neg, zpow_ofNat]
    ring
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wpd
    rw [hP, hper, hom.2.2.1, zpow_neg, zpow_ofNat]
    ring

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDualReduction
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem wittDual_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [Module.Free (WittVector p k) M] [Module.Finite (WittVector p k) M] [AddCommGroup V] [Module k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = p • n) → ∃ r' : Module.Dual (WittVector p k) M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] Module.Dual k V, (∀ l m, r' l (r m) = WittVector.constantCoeff (l m)) ∧ Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  intro p _ k _ _ _ M V _ _ _ _ _ _ r hr hker
  have hσs : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) :=
    WittVector.constantCoeff_surjective p
  have hpk : ∀ y : k, (p • y) = 0 := fun y => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hσker : ∀ x : WittVector p k, WittVector.constantCoeff x = 0 → ∃ y, x = p • y := by
    intro x hx
    have hx' : x ∈ Ideal.span {(p : WittVector p k)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 (by simpa [WittVector.constantCoeff_apply] using hx)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    exact ⟨y, by rw [nsmul_eq_mul, ← hy, mul_comm]⟩
  have hwd : ∀ (l : Module.Dual (WittVector p k) M) (m m' : M), r m = r m' →
      WittVector.constantCoeff (l m) = WittVector.constantCoeff (l m') := by
    intro l m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h1 : l m - l m' = p • l n := by rw [← map_sub, hn, map_nsmul]
    rw [← sub_eq_zero, ← map_sub, h1, map_nsmul, hpk]
  have hg0 : ∀ (l : Module.Dual (WittVector p k) M) (m : M),
      WittVector.constantCoeff (l (Function.surjInv hr (r m))) = WittVector.constantCoeff (l m) :=
    fun l m => hwd l _ _ (Function.surjInv_eq hr _)
  let g : Module.Dual (WittVector p k) M → Module.Dual k V := fun l =>
    { toFun := fun v => WittVector.constantCoeff (l (Function.surjInv hr v))
      map_add' := fun v w => by
        obtain ⟨m, rfl⟩ := hr v
        obtain ⟨m', rfl⟩ := hr w
        rw [← map_add r, hg0, hg0, hg0, map_add (f := _), map_add (f := _)]
      map_smul' := fun c v => by
        obtain ⟨a, rfl⟩ := hσs c
        obtain ⟨m, rfl⟩ := hr v
        rw [← LinearMap.map_smulₛₗ, hg0, hg0, map_smul, smul_eq_mul, map_mul, RingHom.id_apply,
          smul_eq_mul] }
  have hg : ∀ l m, g l (r m) = WittVector.constantCoeff (l m) := fun l m => hg0 l m
  let r' : Module.Dual (WittVector p k) M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k V :=
    { toFun := g
      map_add' := fun l l' => by
        ext v
        obtain ⟨m, rfl⟩ := hr v
        rw [LinearMap.add_apply, hg, hg, hg, LinearMap.add_apply, map_add (f := _)]
      map_smul' := fun a l => by
        ext v
        obtain ⟨m, rfl⟩ := hr v
        rw [LinearMap.smul_apply, hg, hg, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul] }
  have hr' : ∀ l m, r' l (r m) = WittVector.constantCoeff (l m) := hg
  let b := Module.Free.chooseBasis (WittVector p k) M
  refine ⟨r', hr', ?_, ?_⟩
  · intro f
    let a : Module.Free.ChooseBasisIndex (WittVector p k) M → WittVector p k :=
      fun i => Function.surjInv hσs (f (r (b i)))
    let l : Module.Dual (WittVector p k) M := b.constr (WittVector p k) a
    let F1 : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] k :=
      { toFun := fun m => WittVector.constantCoeff (l m)
        map_add' := fun m m' => by rw [map_add (f := _), map_add (f := _)]
        map_smul' := fun c m => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
    have hF : F1 = f.comp r := by
      refine b.ext fun i => ?_
      show WittVector.constantCoeff (l (b i)) = f (r (b i))
      rw [show l (b i) = a i from b.constr_basis _ _ _]
      exact Function.surjInv_eq hσs _
    refine ⟨l, ?_⟩
    ext v
    obtain ⟨m, rfl⟩ := hr v
    rw [hr']
    exact LinearMap.congr_fun hF m
  · intro l
    constructor
    · intro h0
      have hz : ∀ m, WittVector.constantCoeff (l m) = 0 := fun m => by
        rw [← hr', h0, LinearMap.zero_apply]
      choose w hw using fun i => hσker _ (hz (b i))
      refine ⟨b.constr (WittVector p k) w, b.ext fun i => ?_⟩
      rw [LinearMap.smul_apply, b.constr_basis, hw]
    · rintro ⟨l', rfl⟩
      rw [map_nsmul]
      ext v
      rw [LinearMap.smul_apply, hpk, LinearMap.zero_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleFreeFiniteOfReduction
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem wittModule_free_finite_of_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [AddCommGroup V] [Module k V] [Module.Finite k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), IsHausdorff (Ideal.span {(p : WittVector p k)}) M → (∀ m : M, (p : WittVector p k) • m = 0 → m = 0) → Function.Surjective r → (∀ m, r m = 0 → ∃ n, m = p • n) → Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M := by
  intro p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker
  classical
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0 := by
    intro j
    induction j with
    | zero => intro m h; simpa using h
    | succ j ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact htf m (ih _ h)
  haveI : Module.IsTorsionFree (WittVector p k) M :=
    Module.IsTorsionFree.of_smul_eq_zero fun a m h => by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨j, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
      rw [mul_smul] at h
      have h1 := hpow j _ h
      rw [← Units.smul_def] at h1
      exact (smul_eq_zero_iff_eq u).mp h1
  haveI : IsHausdorff I M := hH
  let b := Module.finBasis k V
  choose m hm using fun i => hr (b i)
  let F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M :=
    Fintype.linearCombination (WittVector p k) m
  haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) :=
    GlobalTheory.isPrecomplete_pi I _
  have hs : Function.Surjective F := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, Fintype.linearCombination_apply, map_sum]
      simp only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      exact b.sum_repr (r x)
    obtain ⟨y, hy⟩ := hker _ h0
    rw [hy]
    have : ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    simpa [Nat.cast_smul_eq_nsmul] using this
  haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

end GlobalTheory
end

