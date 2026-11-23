module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjEisensteinPolynomialLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem exists_eisensteinCombination_of_isModularForm {w : ℕ} {F : ℍ → ℂ}
    (hF : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (w : ℤ) F) :
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  obtain ⟨f, hf⟩ := hF
  have hmem := _root_.ReciprocityTheory.PGsh.coe_mem_monoSpanF w f
  unfold _root_.ReciprocityTheory.PGsh.monoSpanF at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  classical
  refine ⟨(_root_.ReciprocityTheory.PGsh.monoIdx w).image fun a => (a, _root_.ReciprocityTheory.PGsh.monoB w a),
    fun p => if hp : p.1 ∈ _root_.ReciprocityTheory.PGsh.monoIdx w then c ⟨p.1, hp⟩ else 0, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    exact _root_.ReciprocityTheory.PGsh.monoIdx_wt ha
  · intro τ
    rw [Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h), ← hf τ, ← hc]
    rw [Finset.sum_apply, ← Finset.sum_attach (_root_.ReciprocityTheory.PGsh.monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, a.2, dif_pos]
    rw [_root_.ReciprocityTheory.PGsh.coe_monoW a.2]
    rfl

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem qConj_eisensteinCombination (g : ℂ ≃+* ℂ) {N : ℕ}
    (hN : 0 < N) {ι : Type} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ) :
    _root_.GlobalTheory.QFam.QConj g N (fun τ => ∑ i ∈ s, c i * (E₄ τ ^ u i * E₆ τ ^ v i))
      (fun τ => ∑ i ∈ s, g (c i) * (E₄ τ ^ u i * E₆ τ ^ v i)) := by
  refine _root_.GlobalTheory.QFam.QConj.sum s fun i _ => ?_
  have h₄ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inl rfl) g
  have h₆ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
  exact (_root_.GlobalTheory.QFam.QConj.const g N (c i)).mul hN
    ((h₄.pow hN (u i)).mul hN (h₆.pow hN (v i)))


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.QFam.levelPoly_conj : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ),
    0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → _root_.GlobalTheory.QFam.QConj g N F F' →
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧
      ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro g w N F F' hN hinv hconj
  obtain ⟨a, ha, ha'⟩ := hconj
  obtain ⟨s, c, hw, hF⟩ := exists_eisensteinCombination_of_isModularForm
    (_root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha)
  refine ⟨s, c, hw, hF, ?_⟩
  obtain ⟨b, hb, hb'⟩ :=
    qConj_eisensteinCombination g hN s c Prod.fst Prod.snd
  have hFeq : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
  rw [← hFeq] at hb
  have hab : a = b := ha.coeff_unique hN hb
  subst hab
  intro τ
  exact congrFun (ha'.fun_unique hb') τ

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLift
section
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

section Coeff

variable {R : Type} [CommRing R]

private lemma coeff_eq_of_X_pow_dvd_sub {n i : ℕ} {a b : PowerSeries R}
    (h : (X : PowerSeries R) ^ n ∣ a - b) (hi : i < n) : coeff i a = coeff i b := by
  rw [X_pow_dvd_iff] at h
  have := h i hi
  rwa [map_sub, sub_eq_zero] at this

private lemma coeff_mul_of_X_pow_dvd' {n : ℕ} {u : PowerSeries R} (hu : (X : PowerSeries R) ^ n ∣ u)
    (h : PowerSeries R) : coeff n (u * h) = coeff n u * coeff 0 h := by
  obtain ⟨k, rfl⟩ := hu
  rw [mul_assoc, coeff_X_pow_mul', coeff_X_pow_mul', if_pos le_rfl, if_pos le_rfl, Nat.sub_self]
  simp only [coeff_zero_eq_constantCoeff_apply, map_mul]

private lemma X_pow_dvd_rescale' {k : ℕ} {p : PowerSeries R} (a : R)
    (h : (X : PowerSeries R) ^ k ∣ p) : (X : PowerSeries R) ^ k ∣ rescale a p := by
  rw [X_pow_dvd_iff] at h ⊢
  intro i hi
  rw [coeff_rescale, h i hi, mul_zero]

end Coeff

theorem exists_jet_succ_of_lift (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R]
    (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π) (hεm : ε.comp m = ε)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (_hδ : ∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) (_hδπ : ∀ a, δ (π a) = 0)
    (n : ℕ) (hn : 2 ≤ n) (φ ψ : A → PowerSeries R) (hφ : IsJet π ε m β δ n φ)
    (hψ : IsRingHomMod π β (n + 1) ψ) (hψφ : ∀ f, (X : PowerSeries R) ^ n ∣ ψ f - φ f) :
    ∃ ψ' : A → PowerSeries R, IsJet π ε m β δ (n + 1) ψ' ∧
      ∀ f, (X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  obtain ⟨-, hφm, hφ0, hφ1⟩ := hφ
  obtain ⟨hψmul, hψadd, hψone, hψπ⟩ := hψ
  have hεmf : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hmπf : ∀ b, m (π b) = π b := fun b => by rw [← RingHom.comp_apply, hmπ]
  have hψ0 : ∀ f, coeff 0 (ψ f) = β (ε f) := fun f => by
    rw [coeff_eq_of_X_pow_dvd_sub (hψφ f) (by omega), coeff_zero_eq_constantCoeff_apply, hφ0]

  obtain ⟨u, hu_def⟩ : ∃ u : A → PowerSeries R, ∀ f, u f = ψ (m f) - rescale 2 (ψ f) :=
    ⟨_, fun _ => rfl⟩
  have hu : ∀ f, (X : PowerSeries R) ^ n ∣ u f := fun f => by
    have e : u f = (ψ (m f) - φ (m f)) + (φ (m f) - rescale 2 (φ f)) - rescale 2 (ψ f - φ f) := by
      rw [hu_def, map_sub]; ring
    rw [e]
    exact dvd_sub (dvd_add (hψφ _) (hφm f)) (X_pow_dvd_rescale' _ (hψφ f))
  obtain ⟨D, hD_def⟩ : ∃ D : A → R, ∀ f, D f = coeff n (u f) := ⟨_, fun _ => rfl⟩
  have hDadd : ∀ f g, D (f + g) = D f + D g := fun f g => by
    simp only [hD_def]
    rw [← map_add (f := _)]
    apply coeff_eq_of_X_pow_dvd_sub _ (Nat.lt_succ_self n)
    have e : u (f + g) - (u f + u g) =
        (ψ (m f + m g) - (ψ (m f) + ψ (m g))) - rescale 2 (ψ (f + g) - (ψ f + ψ g)) := by
      simp only [hu_def, map_add (f := _), map_sub]; ring
    rw [e]
    exact dvd_sub (hψadd _ _) (X_pow_dvd_rescale' _ (hψadd _ _))
  have hDmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := fun f g => by
    have e1 : (X : PowerSeries R) ^ (n + 1) ∣
        u (f * g) - (u f * ψ (m g) + rescale 2 (ψ f) * u g) := by
      have e : u (f * g) - (u f * ψ (m g) + rescale 2 (ψ f) * u g) =
          (ψ (m f * m g) - ψ (m f) * ψ (m g)) - rescale 2 (ψ (f * g) - ψ f * ψ g) := by
        simp only [hu_def, map_mul, map_sub]; ring
      rw [e]
      exact dvd_sub (hψmul _ _) (X_pow_dvd_rescale' _ (hψmul _ _))
    simp only [hD_def]
    rw [coeff_eq_of_X_pow_dvd_sub e1 (Nat.lt_succ_self n), map_add (f := _),
      coeff_mul_of_X_pow_dvd' (hu f), mul_comm (rescale 2 (ψ f)), coeff_mul_of_X_pow_dvd' (hu g)]
    rw [coeff_rescale, pow_zero, one_mul, hψ0, hψ0, hεmf]
    ring
  have hDπ : ∀ b, D (π b) = 0 := fun b => by
    rw [hD_def, hu_def, hmπf, map_sub, coeff_rescale,
      coeff_eq_of_X_pow_dvd_sub (hψπ b) (Nat.lt_succ_self n), coeff_C, if_neg (by omega)]
    ring
  obtain ⟨c, hc⟩ : ∃ c : R, c * ((2 : R) ^ n - 2) = 1 := by
    have h4 : (4 : ℚ) ≤ 2 ^ n := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hne : (2 : ℚ) ^ n - 2 ≠ 0 := by intro h; linarith
    refine ⟨algebraMap ℚ R ((2 : ℚ) ^ n - 2)⁻¹, ?_⟩
    have e : ((2 : R) ^ n - 2) = algebraMap ℚ R ((2 : ℚ) ^ n - 2) := by
      rw [map_sub, map_pow, map_ofNat]
    rw [e, ← map_mul, inv_mul_cancel₀ hne, map_one]
  obtain ⟨E, hE⟩ : ∃ E : A →+ R, ∀ f, E f = c * D f :=
    ⟨AddMonoidHom.mk' (fun f => c * D f) (fun f g => by rw [hDadd]; ring), fun _ => rfl⟩
  have hEmul : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f := fun f g => by
    rw [hE, hE, hE, hDmul]; ring
  have hEπ : ∀ b, E (π b) = 0 := fun b => by rw [hE, hDπ, mul_zero]
  have hEm : ∀ f, E (m f) = 2 * E f := deriv_comp_m π ε m β E hεπ hmπ hm2 hEmul hEπ
  refine ⟨fun f => ψ f + C (E f) * X ^ n, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro f g
    have e : ψ (f * g) + C (E (f * g)) * X ^ n - (ψ f + C (E f) * X ^ n) * (ψ g + C (E g) * X ^ n) =
        (ψ (f * g) - ψ f * ψ g) + X ^ n * (C (E (f * g)) - C (E f) * ψ g - C (E g) * ψ f) -
          C (E f) * C (E g) * (X ^ n * X ^ n) := by ring
    rw [e]
    refine dvd_sub (dvd_add (hψmul f g) ?_) ?_
    · rw [pow_succ]
      apply mul_dvd_mul_left
      rw [X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
      simp only [map_sub, coeff_zero_C, coeff_C_mul, hψ0, hEmul]
      ring
    · apply dvd_mul_of_dvd_right
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
  · intro f g
    convert hψadd f g using 1
    simp only [map_add (f := _)]
    ring
  · convert hψone using 1
    dsimp only
    rw [show E 1 = 0 by rw [← map_one π, hEπ]]
    simp
  · intro b
    convert hψπ b using 1
    dsimp only
    rw [hEπ]
    simp
  · intro f
    rw [X_pow_dvd_iff]
    intro i hi
    simp only [map_sub, map_add (f := _), coeff_rescale, coeff_C_mul_X_pow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [if_neg h.ne, if_neg h.ne]
      have := (X_pow_dvd_iff.mp (hu f)) i h
      rw [hu_def, map_sub, coeff_rescale] at this
      linear_combination this
    · rw [h, if_pos rfl, if_pos rfl, hEm, hE, hD_def, hu_def, map_sub, coeff_rescale]
      linear_combination (-(coeff n (ψ (m f)) - 2 ^ n * coeff n (ψ f))) * hc
  · intro f
    rw [← coeff_zero_eq_constantCoeff_apply, map_add (f := _), coeff_C_mul_X_pow, if_neg (by omega),
      add_zero, hψ0]
  · intro f
    rw [map_add (f := _), coeff_C_mul_X_pow, if_neg (by omega), add_zero,
      coeff_eq_of_X_pow_dvd_sub (hψφ f) (by omega), hφ1]
  · intro f
    have e : ψ f + C (E f) * X ^ n - φ f = (ψ f - φ f) + C (E f) * X ^ n := by ring
    rw [e]
    exact dvd_add (hψφ f) (dvd_mul_left _ _)

end GlobalTheory.Nef.PathJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrime
section
open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtFactorLoc

def constColim (R : Type) [CommRing R] :
    IsColimit (Cocone.mk (CommRingCat.of R)
      (𝟙 ((Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)))) where
  desc c := c.ι.app ⟨⟨⟩⟩
  fac c j := by rcases j with ⟨⟨⟩⟩; simp
  uniq c m hm := by simpa using hm ⟨⟨⟩⟩

theorem exists_etale_factor_of_indEt_atPrime : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  intro R O _ _ _ P _ φ hφ hind Z _ _ _ g
  let L := Localization.AtPrime P
  letI : Algebra L O := φ.toAlgebra
  haveI : IsScalarTower R L O :=
    IsScalarTower.of_algebraMap_eq (fun r => (congrArg (fun f => f r) hφ).symm)
  let g1 : L ⊗[R] Z →ₐ[L] O :=
    Algebra.TensorProduct.lift (Algebra.ofId L O) g (fun _ _ => Commute.all _ _)
  obtain ⟨C, _, _, _, ψ, χ, hψχ⟩ := GlobalTheory.EtC.exists_etale_factor_of_indEt L O hind (L ⊗[R] Z) g1
  let M := P.primeCompl
  let D0 := (Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)
  let s0 : D0 ⟶ (Functor.const _).obj (CommRingCat.of R) := 𝟙 _
  have hs0 : IsColimit (Cocone.mk _ s0) := constColim R
  obtain ⟨j, Aj, _, instA, hAj, ⟨e⟩⟩ := GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit
    (GlobalTheory.IndEtaleLoc.Idx D0 s0 M) (GlobalTheory.IndEtaleLoc.diag D0 s0 M)
    (Cocone.mk _ (GlobalTheory.IndEtaleLoc.toLoc (s := s0) (M := M) L))
    (GlobalTheory.IndEtaleLoc.isColimitToLoc L hs0) C

  let Re : Type := Localization.Away j.e
  letI : Algebra R Re := (inferInstance : Algebra (D0.obj j.j) (Localization.Away j.e))
  letI : Algebra Re L := (GlobalTheory.IndEtaleLoc.leg L j).toAlgebra
  letI : Algebra Re Aj := instA
  haveI : Algebra.Etale Re Aj := hAj
  let e0 : R := j.e
  have he0 : e0 ∈ M := j.mem
  haveI : IsLocalization (Submonoid.powers e0) Re :=
    (inferInstance : IsLocalization (Submonoid.powers j.e) (Localization.Away j.e))
  haveI : IsScalarTower R Re L := IsScalarTower.of_algebraMap_eq (fun r =>
    (GlobalTheory.IndEtaleLoc.leg_algebraMap (s := s0) (M := M) L j r).symm)
  haveI hLoc : IsLocalization (M.map (algebraMap R Re)) L :=
    IsLocalization.isLocalization_of_submonoid_le Re L (Submonoid.powers e0) M
      (Submonoid.powers_le.2 he0)
  let e' : L ⊗[Re] Aj ≃ₐ[L] C := e
  letI rA : Algebra Aj (L ⊗[Re] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI hT : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re)))
      (L ⊗[Re] Aj) := IsLocalization.tensorRight _ _
  letI : Algebra Aj C := (e'.toRingHom.comp (algebraMap Aj (L ⊗[Re] Aj))).toAlgebra
  let eA : L ⊗[Re] Aj ≃ₐ[Aj] C := AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun _ => rfl)
  haveI hCloc : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) C :=
    IsLocalization.isLocalization_of_algEquiv _ eA
  letI : Algebra R Aj := ((algebraMap Re Aj).comp (algebraMap R Re)).toAlgebra
  haveI : IsScalarTower R Re Aj := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale R Re :=
    (Algebra.Etale.of_isLocalizationAway j.e : Algebra.Etale (D0.obj j.j) (Localization.Away j.e))
  haveI : Algebra.Etale R Aj := Algebra.Etale.comp R Re Aj
  letI : Algebra R C := ((algebraMap L C).comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R Aj C := IsScalarTower.of_algebraMap_eq (fun r => by
    have key : ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r)) =
        algebraMap L (L ⊗[Re] Aj) (algebraMap R L r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R Re L]
      generalize algebraMap R Re r = c
      rw [Algebra.algebraMap_eq_smul_one (A := Aj) c, Algebra.algebraMap_eq_smul_one (A := L) c,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    show algebraMap L C (algebraMap R L r) = e' ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r))
    rw [key, AlgEquiv.commutes])
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R C) :=
    GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization R Aj C
      (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) (GlobalTheory.EtC.indEt_of_etale R Aj)
  let ψ' : Z →ₐ[R] C := (ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨W, _, _, _, u, v', huv⟩ := GlobalTheory.EtC.exists_etale_factor_of_indEt R C hC Z ψ'
  refine ⟨W, inferInstance, inferInstance, inferInstance, u, (χ.restrictScalars R).comp v', ?_⟩
  ext z
  have h1 := DFunLike.congr_fun huv z
  have h2 := DFunLike.congr_fun hψχ ((1 : L) ⊗ₜ[R] z)
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', ψ',
    Algebra.TensorProduct.includeRight_apply] at h1 h2 ⊢
  rw [h1, h2]
  simp [g1]

end GlobalTheory.IndEtFactorLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatPicMapAlgebraEqOneStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_faithfullyFlat_picMapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  first | (exact @GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one) | (exact GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one) | (intros; apply GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection : ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f → ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  first | (exact @GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective) | (exact GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective) | (intros; apply GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLocalRootOfUnitOfKummerStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleLocal_root_of_unit_of_kummer : ∀ (q : ℕ) [NeZero q],
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
      Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  first | (exact @GlobalTheory.EtC.KumRoots.roots) | (exact GlobalTheory.EtC.KumRoots.roots) | (intros; apply GlobalTheory.EtC.KumRoots.roots  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmod
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

theorem intCast_surj (Q : ℕ) : Function.Surjective (Int.cast : ℤ → ULift.{1} (ZMod Q)) := by
  intro r
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective r.down
  exact ⟨z, ULift.ext (by simp [hz])⟩

theorem map_smul_of_add {A B M N : Type*} [Ring A] [Ring B] (f : A →+* B)
    (hA : Function.Surjective (Int.cast : ℤ → A)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (g : M →+ N) (r : A) (m : M) : g (r • m) = f r • g m := by
  obtain ⟨z, rfl⟩ := hA r
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]

variable {R S : Type} [CommRing R] [CommRing S]

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {G : Shv S} (f g : (extSh φ).obj F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map f (extSh.sec φ F U a) = Sec.map g (extSh.sec φ F U a)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    f.hom g.hom G.property ?_
  ext U : 2
  apply (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext a
  exact h (unop U) a

end FactorExt

end GlobalTheory.EtC

end

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
  (hR : Function.Surjective (Int.cast : ℤ → ULift.{1} R)) {I : Cx R} {K : Cx S} (ρ : SemiMap I K)
include hR

def lin (s : ℤ) (U : Scheme.{0}) :
    (I.X s).obj.obj (op U) ⟶ (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)) :=
  ModuleCat.ofHom (X := (I.X s).obj.obj (op U))
    (Y := (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)))
    { toFun := ρ.app U s
      map_add' := map_add _
      map_smul' := fun r a => by
        exact map_smul_of_add (uliftHom φ) hR (ρ.app U s) r a }

def pre (s : ℤ) : (I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ) ⟶ (K.X s).obj where
  app U := ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).symm (lin φ hR ρ s (unop U))
  naturality {U V} g := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    ext a
    exact (ρ.nat g.unop s a).symm

def term (s : ℤ) : (extCx φ I).X s ⟶ K.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S))).homEquiv _ _).symm (pre φ hR ρ s)

theorem term_sec (s : ℤ) (U : Scheme.{0}) (a : Sec (I.X s) U) :
    Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a) = ρ.app U s a := by
  have h1 : toSheafify Scheme.etaleTopology.{0} ((I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ≫
      (term φ hR ρ s).hom = pre φ hR ρ s := by
    have := Adjunction.homEquiv_unit (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S)))
      _ _ (term φ hR ρ s)
    rw [sheafificationAdjunction_unit_app] at this
    exact this.symm.trans (Equiv.apply_symm_apply _ _)
  have h2 := Adjunction.homEquiv_unit (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)) _ _
    ((pre φ hR ρ s).app (op U))
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (NatTrans.congr_app h1 (op U)))
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app ((I.X s).obj.obj (op U))).hom a)
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h2) a
  simp only [pre, Equiv.apply_symm_apply] at e2
  exact e1.trans e2.symm

def hom : extCx φ I ⟶ K where
  f s := term φ hR ρ s
  comm' s t _ := by
    apply FactorExt.extSh_hom_ext φ
    intro U a
    show Sec.map (K.d s t) (Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a)) =
      Sec.map (term φ hR ρ t) (Sec.map ((extSh φ).map (I.d s t)) (extSh.sec φ (I.X s) U a))
    rw [term_sec, extSh.sec_map, term_sec, ρ.comm]

end FactorExt

theorem SemiMap.factor_extCx : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K),
    ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) :=
  fun Q _ hq _ _ ρ => ⟨FactorExt.hom _ (FactorExt.intCast_surj Q) ρ,
    fun U s a => (FactorExt.term_sec (ZMod.castHom hq _) (FactorExt.intCast_surj Q) ρ s U a).symm⟩

end GlobalTheory.EtC

end
end

