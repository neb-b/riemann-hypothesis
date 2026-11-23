module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.QuotientMetricDivisors.FinalW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerLeOfBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem perCol_base_smul_form (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ)
    (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

theorem perCol_eq_pairing_of_kills (D : D7) (h : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (u : D.what₂.Word)
    (φ : D.what₂.Mu u)
    (hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 φ F = 0)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F) := by
  set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
  have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
    have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
    rw [map_sub, this, sub_zero]
  have hF' : F = (F - n) + n := by abel
  rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
  conv_lhs => rw [hF']
  rw [D.perCol_add, hK n hnU, add_zero]

theorem span_range_inf_ker_le_of_basis {K : Type} [Field K] (σ : K →+* ℂ) {W E A I : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module K A]
    [Finite I] {n : ℕ} (b : Module.Basis I K A)
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : A →ₛₗ[σ] E) (f : W →ₗ[ℂ] E) (g : (Fin n → K) →ₗ[K] A)
    (hli : LinearIndependent ℂ (fun i => j' (b i))) (hf : ∀ x, f (j x) = j' (g x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f = Submodule.span ℂ (j '' {x | g x = 0}) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let b' := b.reindex e
  let M := LinearMap.toMatrix' (b'.equivFun.toLinearMap ∘ₗ g)
  have hM : ∀ x, M.mulVec x = b'.equivFun (g x) := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have key := span_range_inf_ker_eq_span_rational_ker σ j
    (j'.comp b'.equivFun.symm.toLinearMap) f M ?_ ?_
  · rw [key]
    congr 2
    ext x
    simp only [Set.mem_setOf_eq, hM, EmbeddingLike.map_eq_zero_iff]
  · have h1 : (fun l => (j'.comp b'.equivFun.symm.toLinearMap) (Pi.single l 1))
        = (fun i => j' (b i)) ∘ e.symm := by
      funext l
      simp [b', Pi.single_apply]
    rw [h1]
    exact hli.comp _ e.symm.injective
  · intro x
    rw [hf, hM]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHom
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomial
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens {A B : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal B).comap f = maximalIdeal A := by
  ext x
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private lemma locPiecesEtale_localization_atPrime {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] :
    _root_.GlobalTheory.LocAcyc.LocPiecesEtale R (Localization.AtPrime q) := by
  unfold _root_.GlobalTheory.LocAcyc.LocPiecesEtale
  exact ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
    fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨A, inferInstance, inferInstance, inferInstance, q,
      inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.strictHenselisation_etale_over_polynomial : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S)
      (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T E _ _ _ _ _ _ _ _ y _
  obtain ⟨S, _, _, _, _, hsep, hflat, -, -, hpieces⟩ := _root_.GlobalTheory.exists_strictHenselisation
    (Localization.AtPrime y) (SeparableClosure (ResidueField (Localization.AtPrime y)))
  haveI := hsep
  have hP : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Localization.AtPrime y) S := hpieces
  letI : Algebra E S :=
    ((algebraMap (Localization.AtPrime y) S).comp (algebraMap E (Localization.AtPrime y))).toAlgebra
  letI : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  letI : Algebra (Polynomial T) S := ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  haveI : IsScalarTower E (Localization.AtPrime y) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    exact congrArg _ (IsScalarTower.algebraMap_apply T (Polynomial T) E x)
  haveI : IsScalarTower (Polynomial T) (Localization.AtPrime y) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap (Localization.AtPrime y) S (algebraMap E (Localization.AtPrime y)
          (algebraMap (Polynomial T) E x)) =
        algebraMap (Localization.AtPrime y) S (algebraMap (Polynomial T) (Localization.AtPrime y) x)
      exact congrArg _ (IsScalarTower.algebraMap_apply (Polynomial T) E (Localization.AtPrime y) x).symm
  have hcomap : (maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E (Localization.AtPrime y) S, ← Ideal.comap_comap,
      _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
    exact Localization.AtPrime.under_maximalIdeal ..
  haveI : Module.Flat E (Localization.AtPrime y) := IsLocalization.flat _ y.primeCompl
  haveI := hflat
  have hflatE : Module.Flat E S := Module.Flat.trans E (Localization.AtPrime y) S
  have hpiecesE : _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S :=
    _root_.GlobalTheory.indEtale_localPieces_trans E (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := E) (A := E) y) hP
  have hpiecesT : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Polynomial T) S :=
    _root_.GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := Polynomial T) (A := E) y) hP
  obtain ⟨P, _, φ, hφc, hφs⟩ := _root_.GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S hpiecesT
  have hPy : P = y.comap (algebraMap (Polynomial T) E) := by
    haveI : IsLocalHom φ := hφs.2.2.1
    calc P = ((maximalIdeal S).comap φ).comap (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
          rw [_root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
          exact (Localization.AtPrime.under_maximalIdeal ..).symm
      _ = (maximalIdeal S).comap (algebraMap (Polynomial T) S) := by
          rw [Ideal.comap_comap, hφc]
      _ = y.comap (algebraMap (Polynomial T) E) := by
          rw [IsScalarTower.algebraMap_eq (Polynomial T) E S, ← Ideal.comap_comap, hcomap]
  subst hPy
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcomap, hflatE, hpiecesE, φ, hφc, hφs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySumStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (g : MvPowerSeries (Fin d) R) (n : ℕ), subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g + ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  first | exact @GlobalTheory.QLog.subst_nmul_eq | exact GlobalTheory.QLog.subst_nmul_eq | (intros; apply GlobalTheory.QLog.subst_nmul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def coeffIdeal (τ : Type) (J : Ideal B) : Ideal (MvPowerSeries τ B) where
  carrier := {w | ∀ α, coeff α w ∈ J}
  add_mem' ha hb α := by rw [map_add (f := _)]; exact J.add_mem (ha α) (hb α)
  zero_mem' α := by rw [map_zero]; exact J.zero_mem
  smul_mem' c x hx α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun _ _ => J.mul_mem_left _ (hx _)

def scaledIdeal (τ : Type) (K : Ideal B) (c : Q) : Ideal (MvPowerSeries τ B) where
  carrier := {x | ∀ γ, ∃ b ∈ K, c * algebraMap B Q (coeff γ x) = algebraMap B Q b}
  add_mem' {x y} hx hy γ := by
    obtain ⟨a, ha, ea⟩ := hx γ
    obtain ⟨b, hb, eb⟩ := hy γ
    exact ⟨a + b, K.add_mem ha hb, by rw [map_add (f := _), map_add (f := _), mul_add, ea, eb, map_add (f := _)]⟩
  zero_mem' γ := ⟨0, K.zero_mem, by simp⟩
  smul_mem' r x hx γ := by
    classical
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, coeff_mul, map_sum, Finset.mul_sum]
    have key : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal γ, ∃ b ∈ K,
        c * algebraMap B Q (coeff q.1 r * coeff q.2 x) = algebraMap B Q b := by
      intro q _
      obtain ⟨b, hb, eb⟩ := hx q.2
      exact ⟨coeff q.1 r * b, K.mul_mem_left _ hb, by rw [map_mul, map_mul, ← eb]; ring⟩
    choose! g hg eg using key
    exact ⟨∑ q ∈ Finset.HasAntidiagonal.antidiagonal γ, g q, K.sum_mem hg, by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_congr rfl eg⟩

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {τ : Type} {J : Ideal B}

theorem pow_add_sub_pow
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (v w : MvPowerSeries τ B) (hw : w ∈ coeffIdeal τ J) (n : ℕ) :
    ∃ z ∈ coeffIdeal τ J, (v + w) ^ n - v ^ n = (n : MvPowerSeries τ B) * z := by
  cases n with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ m =>
    choose! y hy ey using fun k (hk : 0 < k) => hdp w hw k hk
    refine ⟨∑ k ∈ Finset.range (m + 1), (m.descFactorial k : MvPowerSeries τ B) * y (k + 1) * v ^ (m - k),
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hy _ (Nat.succ_pos k))), ?_⟩
    rw [add_comm v w, add_pow, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h : (((k + 1).factorial * (m + 1).choose (k + 1) : ℕ) : MvPowerSeries τ B) =
        ((m + 1 : ℕ) : MvPowerSeries τ B) * (m.descFactorial k : ℕ) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ, Nat.cast_mul]
    rw [ey (k + 1) (Nat.succ_pos k), Nat.add_sub_add_right]
    push_cast at h ⊢
    linear_combination (y (k + 1) * v ^ (m - k)) * h

theorem prod_sub_mem {σ : Type} (K : Ideal B) (c : Q) (α : σ →₀ ℕ) (u v : σ → MvPowerSeries τ B)
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (huv : ∀ i, u i - v i ∈ coeffIdeal τ J)
    (hsc : ∀ i, ∀ z ∈ coeffIdeal τ J, (α i : MvPowerSeries τ B) * z ∈ scaledIdeal τ K c)
    (s : Finset σ) : ∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i ∈ scaledIdeal τ K c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨z, hz, ez⟩ := pow_add_sub_pow hdp (v a) (u a - v a) (huv a) (α a)
    rw [add_sub_cancel] at ez
    have e : u a ^ α a * ∏ i ∈ s, u i ^ α i - v a ^ α a * ∏ i ∈ s, v i ^ α i =
        u a ^ α a * (∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i) +
          (u a ^ α a - v a ^ α a) * ∏ i ∈ s, v i ^ α i := by ring
    rw [e, ez]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ (hsc a z hz))

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

theorem subst_sub_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) →
    In (J * N) (MvPowerSeries.subst (σ := σ) (τ := τ) (R := Q) (S := Q) (up Q u) f -
      MvPowerSeries.subst (σ := σ) (τ := τ) (R := Q) (S := Q) (up Q v) f) := by
  intro p _ B O Q _ _ _ _ θ hF J hJ σ τ _ N f u v hf hu hv huv
  classical
  have hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n →
      ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y := fun w hw n hn => by
    obtain ⟨y, hy, e⟩ := _root_.GlobalTheory.DPSeries.pow_eq_factorial_mul p B O Q θ hF J hJ τ w hw n hn
    exact ⟨y, hy, e⟩
  have hsU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hu i]
  have hsV : HasSubst (up Q v) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hv i]
  intro γ
  rw [map_sub, coeff_subst hsU, coeff_subst hsV,
    ← finsum_sub_distrib (coeff_subst_finite hsU f γ) (coeff_subst_finite hsV f γ)]
  refine finsum_induction (fun q => ∃ b ∈ J * N, q = algebraMap B Q b) ⟨0, Submodule.zero_mem _, by simp⟩
    (fun x y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a + b, Submodule.add_mem _ ha hb, by rw [ea, eb, map_add (f := _)]⟩)
    (fun d => ?_)
  have hprod : ∀ w : σ → MvPowerSeries τ B,
      (d.prod fun s e => up Q w s ^ e) = map (algebraMap B Q) (∏ i, w i ^ d i) := by
    intro w
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp [up, map_pow]
  have hsc : ∀ i, ∀ z ∈ coeffIdeal τ J,
      (d i : MvPowerSeries τ B) * z ∈ scaledIdeal τ (J * N) (coeff d f) := by
    intro i z hz γ'
    obtain ⟨b, hb, eb⟩ := hf d i
    refine ⟨coeff γ' z * b, Ideal.mul_mem_mul (hz γ') hb, ?_⟩
    rw [show ((d i : ℕ) : MvPowerSeries τ B) = C (d i : B) from (map_natCast C _).symm, coeff_C_mul,
      map_mul, map_mul, ← eb, map_natCast]
    ring
  have hmem := prod_sub_mem (J := J) (J * N) (coeff d f) d u v hdp (fun i α => huv i α) hsc Finset.univ
  obtain ⟨b, hb, eb⟩ := hmem γ
  refine ⟨b, hb, ?_⟩
  rw [hprod, hprod, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub (coeff γ), ← map_sub, coeff_map, ← eb]

end GlobalTheory.KatzCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleAdditiveEqCoboundaryAddStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), IsCoc (addLaw R d) c → constantCoeff c = 0 → ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b + ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m))) := by
  first | exact @GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt | exact GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt | (intros; apply GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticSimilitudeInvertibleModN
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SympModN

theorem omegaStd_nsmul_left {h : ℕ} (N : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (N • a) b = N * omegaStd a b := by
  unfold omegaStd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_add_nsmul_modEq {h : ℕ} (N : ℕ) (x y b c : Fin h ⊕ Fin h → ℤ) :
    omegaStd (x + N • b) (y + N • c) ≡ omegaStd x y [ZMOD N] := by
  rw [Int.modEq_iff_dvd]
  unfold omegaStd
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  exact ⟨-(b (.inl i) * y (.inr i) + x (.inl i) * c (.inr i) + N * b (.inl i) * c (.inr i)) +
    (b (.inr i) * y (.inl i) + x (.inr i) * c (.inl i) + N * b (.inr i) * c (.inl i)), by ring⟩

theorem exists_eq_nsmul_iff {ι : Type*} (N : ℕ) (hN : N ≠ 0) (a : ι → ℤ) :
    (∃ b, a = N • b) ↔ ∀ j, (N : ℤ) ∣ a j := by
  constructor
  · rintro ⟨b, rfl⟩ j
    simp [nsmul_eq_mul]
  · intro hd
    refine ⟨fun j => a j / N, funext fun j => ?_⟩
    simp [nsmul_eq_mul, Int.mul_ediv_cancel' (hd j)]

theorem symplecticSimilitude_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 →
    m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) →
    (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧
    ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧
      ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  intro h N m T hN hm hT
  have h1 : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hd : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have e := hT a y
      rw [hb, omegaStd_nsmul_left] at e
      have hdm : (N : ℤ) ∣ (m : ℤ) * omegaStd a y := by
        have h3 := Int.modEq_iff_dvd.1 e
        have h2 : (N : ℤ) ∣ (N : ℤ) * omegaStd b (T y) := dvd_mul_right _ _
        simpa using dvd_add h3 h2
      exact (Nat.isCoprime_iff_coprime.2 hm.symm).dvd_of_dvd_mul_left hdm
    refine (exists_eq_nsmul_iff N hN a).2 fun j => ?_
    rcases j with i | i
    · simpa [omegaStd_single_inr] using hd (Pi.single (.inr i) 1)
    · simpa [omegaStd_single_inl] using hd (Pi.single (.inl i) 1)
  haveI : NeZero N := ⟨hN⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a j => (a j : ZMod N)
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v j => ((v j).val : ℤ)
  have hred0 : ∀ a, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    rw [exists_eq_nsmul_iff N hN a, funext_iff]
    exact forall_congr' fun j => ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hredlift : ∀ v, red (lift v) = v := by
    intro v; funext j; simp [red, lift]
  have hred_sub : ∀ a a', red (a - a') = red a - red a' := by
    intro a a'; funext j; simp [red]
  have finj : Function.Injective fun v => red (T (lift v)) := by
    intro v w hvw
    have e : red (T (lift v - lift w)) = 0 := by
      rw [map_sub, hred_sub]; exact sub_eq_zero.2 hvw
    obtain ⟨b', hb'⟩ := h1 _ ((hred0 _).1 e)
    have e2 : red (lift v - lift w) = 0 := (hred0 _).2 ⟨b', hb'⟩
    rw [hred_sub, hredlift, hredlift] at e2
    exact sub_eq_zero.1 e2
  have fsurj := Finite.injective_iff_surjective.1 finj
  have h2 : ∀ a, ∃ a' b, T a' = a + N • b := by
    intro a
    obtain ⟨v, hv⟩ := fsurj (red a)
    have e : red (T (lift v) - a) = 0 := by
      rw [hred_sub]; exact sub_eq_zero.2 hv
    obtain ⟨b, hb⟩ := (hred0 _).1 e
    exact ⟨lift v, b, by rw [← hb]; abel⟩
  choose v b hvb using fun i : Fin h ⊕ Fin h => h2 (Pi.single i 1)
  let T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) :=
    ∑ i, (LinearMap.proj i : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hT' : ∀ x, T' x = ∑ i, x i • v i := by
    intro x; simp [T']
  have h3 : ∀ x, T (T' x) = x + N • ∑ i, x i • b i := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT', map_sum]
    simp only [map_zsmul, hvb, smul_add, Finset.sum_add_distrib]
    congr 1
    · funext j
      simp [Finset.sum_apply, Pi.single_apply]
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨h1, h2, T', fun x => ⟨_, h3 x⟩, ?_⟩
  intro m' hmm' x y
  have e1 := hT (T' x) (T' y)
  rw [h3, h3] at e1
  have e2 := omegaStd_add_nsmul_modEq N x y (∑ i, x i • b i) (∑ i, y i • b i)
  have e3 : (m : ℤ) * omegaStd (T' x) (T' y) ≡ omegaStd x y [ZMOD N] := e1.symm.trans e2
  have hmm'' : (m : ℤ) * m' ≡ 1 [ZMOD N] := by
    unfold Nat.ModEq at hmm'
    unfold Int.ModEq
    exact_mod_cast hmm'
  calc omegaStd (T' x) (T' y) = 1 * omegaStd (T' x) (T' y) := by ring
    _ ≡ ((m : ℤ) * m') * omegaStd (T' x) (T' y) [ZMOD N] := Int.ModEq.mul_right _ hmm''.symm
    _ = m' * ((m : ℤ) * omegaStd (T' x) (T' y)) := by ring
    _ ≡ m' * omegaStd x y [ZMOD N] := Int.ModEq.mul_left _ e3

end GlobalTheory.SympModN
end

