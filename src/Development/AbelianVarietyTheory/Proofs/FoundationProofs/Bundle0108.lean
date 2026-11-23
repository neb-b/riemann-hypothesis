module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Polynomial

namespace GlobalTheory.QFam

theorem vieta_root {ι : Type} [Fintype ι] (y : ι → ℂ) (i : ι) :
    y i ^ Fintype.card ι + ∑ j : Fin (Fintype.card ι),
      ((-1) ^ (Fintype.card ι - (j : ℕ)) *
        ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, y l) *
        y i ^ (j : ℕ) = 0 := by
  classical
  set n := Fintype.card ι with hn
  set P : ℂ[X] := ∏ l, (X + C (-y l)) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_add_C _
  have hdeg : P.natDegree = n := by
    rw [hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]
  have hroot : P.eval (y i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcoeff : ∀ j ≤ n, P.coeff j =
      (-1) ^ (n - j) * ∑ t ∈ Finset.powersetCard (n - j) Finset.univ, ∏ l ∈ t, y l := by
    intro j hj
    rw [hP, Finset.prod_X_add_C_coeff _ _ (by simpa [hn] using hj), Finset.card_univ, ← hn,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]
  have h1 : P.coeff n = 1 := hdeg ▸ hmon.coeff_natDegree
  rw [eval_eq_sum_range, hdeg, Finset.sum_range_succ, h1, one_mul] at hroot
  rw [← hroot, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * y i ^ m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff j j.2.le]

end GlobalTheory.QFam

theorem GlobalTheory.QFam.minpoly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  intro ι _ act k N F R _ hb hF hQ
  refine ⟨fun j τ => (-1) ^ (Fintype.card ι - (j : ℕ)) *
      ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, F l τ,
    fun j => ⟨fun γ => ?_, ?_⟩, fun i τ => vieta_root (fun l => F l τ) i⟩
  · have hE := IsFam.esymm_slash hb hF γ (Fintype.card ι - (j : ℕ))
    have hw : (((k * (Fintype.card ι - (j : ℕ)) : ℕ) : ℤ)) =
        (((Fintype.card ι - (j : ℕ) : ℕ) : ℤ) * (k : ℤ)) := by
      rw [Nat.cast_mul, mul_comm]
    funext τ
    have hEτ := congrFun hE τ
    rw [ModularForm.SL_slash_apply] at hEτ
    rw [hw, ModularForm.SL_slash_apply, mul_assoc, hEτ]
  · exact QAllSubring.mul (QAllSubring.const (R.pow_mem (R.neg_mem R.one_mem) _))
      (QAllSubring.sum _ fun t _ => QAllSubring.prod _ fun l _ => hQ l)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansions
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.mul_powerSeries {N : ℕ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
    (hf : HasQ N f (fun n => PowerSeries.coeff n φ)) (hg : HasQ N g (fun n => PowerSeries.coeff n ψ)) :
    HasQ N (fun τ => f τ * g τ) (fun n => PowerSeries.coeff n (φ * ψ)) := by
  have h := hf.mul_conv hg
  have e : conv (fun n => PowerSeries.coeff n φ) (fun n => PowerSeries.coeff n ψ) =
      fun n => PowerSeries.coeff n (φ * ψ) := by
    funext n; rw [conv, PowerSeries.coeff_mul]
  rwa [e] at h

theorem HasQ.pow_powerSeries {N : ℕ} {f : ℍ → ℂ} {b : ℕ → ℂ} (hf : HasQ N f b) (i : ℕ) :
    HasQ N (fun τ => f τ ^ i) (fun n => PowerSeries.coeff n (PowerSeries.mk b ^ i)) := by
  induction i with
  | zero =>
    have h := HasQ.const N (1 : ℂ)
    convert h using 2 <;> simp [PowerSeries.coeff_one]
  | succ i ih =>
    have hb : HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk b)) := by
      simpa only [PowerSeries.coeff_mk] using hf
    have h := ih.mul_powerSeries hb
    simpa only [pow_succ] using h

theorem polyRel_qSeries : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  intro N n f b p c hN hf hp hrel
  have hterm : ∀ i ∈ Finset.range (n + 1), HasQ N (fun τ => p i τ * f τ ^ i)
      (fun m => PowerSeries.coeff m (PowerSeries.mk (c i) * PowerSeries.mk b ^ i)) := by
    intro i _
    have hpi : HasQ N (p i) (fun m => PowerSeries.coeff m (PowerSeries.mk (c i))) := by
      simpa only [PowerSeries.coeff_mk] using hp i
    exact hpi.mul_powerSeries (hf.pow_powerSeries i)
  have hsum := HasQ.sum (Finset.range (n + 1)) hterm
  have hzero : HasQ N (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) (fun _ => 0) := by
    have h0 := HasQ.const N (0 : ℂ)
    have e : (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) = fun _ => (0 : ℂ) :=
      funext hrel
    rw [e]
    simpa using h0
  have hc := HasQ.coeff_unique hN hsum hzero
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  ext m
  have := congrFun hc m
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using this

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQ
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem powerSeries_to_hahnSeries_rat :
    ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  intro Ω _ N hN
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  let f : ℕ →+ ℚ := (AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Nat.castAddMonoidHom ℚ)
  have hf : ∀ k : ℕ, f k = (k : ℚ) / N := fun k => by
    simp [f, div_eq_mul_inv]
  have hfle : ∀ g g' : ℕ, f g ≤ f g' ↔ g ≤ g' := fun g g' => by
    rw [hf, hf, div_le_div_iff_of_pos_right hN', Nat.cast_le]
  have hfi : Function.Injective f := fun g g' h =>
    le_antisymm ((hfle g g').1 h.le) ((hfle g' g).1 h.ge)
  refine ⟨(HahnSeries.embDomainRingHom f hfi hfle).comp
    (HahnSeries.toPowerSeries (R := Ω)).symm.toRingHom, ?_, ?_⟩
  · intro p k
    rw [← hf]
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    rw [HahnSeries.embDomain_mk_coeff]
    rfl
  · intro p r hr
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨k, -, hk⟩
    exact hr k (by rw [← hf]; exact hk.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharacterEntrySumEisensteinProductStatement
section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product : ∀ (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K], 1 ≤ m → 0 < N → ¬ p ∣ N → 3 ≤ k → ∀ (ψ : DirichletCharacter K (p ^ m)), ψ.IsPrimitive → ∀ (ζ : K), IsPrimitiveRoot ζ (N * p ^ m) → ∀ (a₀ b₀ t : ℤ), (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ (i j : ℕ), ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) * (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i * coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) = if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  first | exact @GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum | exact GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum | (intros; apply GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveConstMulOfBoundedExpansion
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.PrimConst

open NumberField

theorem exists_dividing {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    {ι : Type} (c : ι → Ω) (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] (D : ℕ) (hD : 0 < D)
    (hc : ∀ i, c i ∈ E ∧ IsIntegral ℤ ((D : Ω) * c i))
    (hne : ∃ i, c i ≠ 0) : ∃ i0, c i0 ≠ 0 ∧ ∀ i, c i * (c i0)⁻¹ ∈ A := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NumberField E := by
    refine { to_charZero := inferInstance, to_finiteDimensional := ?_ }
    convert ‹FiniteDimensional ℚ E›
    exact Subsingleton.elim _ _
  have hmem : ∀ i, (D : Ω) * c i ∈ E := fun i => E.mul_mem (E.natCast_mem D) (hc i).1
  let f : ι → 𝓞 E := fun i => ⟨⟨(D : Ω) * c i, hmem i⟩, by
      rw [mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) E.val.injective).1 (hc i).2⟩
  have hf : ∀ i, algebraMap (𝓞 E) Ω (f i) = (D : Ω) * c i := fun i => rfl
  obtain ⟨s0, hs0⟩ : ∃ s0 : Finset ι, ∀ i, f i ∈ Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) := by
    have hN : IsNoetherian ℤ (𝓞 E) := inferInstance
    obtain ⟨M, ⟨s0, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 hN
      (Set.range fun s : Finset ι => Submodule.span ℤ ((s.image f : Finset (𝓞 E)) : Set (𝓞 E))) (Set.range_nonempty _)
    refine ⟨s0, fun i => ?_⟩
    have hle : Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) ≤
        Submodule.span ℤ (((insert i s0).image f : Finset (𝓞 E)) : Set (𝓞 E)) :=
      Submodule.span_mono (by intro y hy; simp only [Finset.coe_image, Finset.coe_insert] at hy ⊢; exact Set.image_mono (Set.subset_insert _ _) hy)
    have heq := eq_of_le_of_not_lt hle (hmax _ ⟨insert i s0, rfl⟩)
    rw [heq]; exact Submodule.subset_span (by simp)
  set v := A.valuation
  have hDv : v (D : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.2 hD.ne'
  have hint : ∀ z : ℤ, v (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  obtain ⟨i1, hi1⟩ := hne
  have ht : (s0.filter (fun i => c i ≠ 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hz : ∀ y ∈ s0.image f, y = 0 := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have := hcon hj; push_neg at this
      ext; simp [f, this]
    have h1 := hs0 i1
    rw [Submodule.mem_span_finset] at h1
    obtain ⟨g, -, hg⟩ := h1
    rw [Finset.sum_eq_zero (fun y hy => by rw [hz y hy, smul_zero])] at hg
    have := congrArg (algebraMap (𝓞 E) Ω) hg
    rw [hf, map_zero] at this
    exact hi1 ((mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hD.ne'))
  obtain ⟨i0, hi0t, hmax⟩ := (s0.filter (fun i => c i ≠ 0)).exists_max_image (fun i => v (c i)) ht
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0t).2
  have hmax' : ∀ j ∈ s0, v (c j) ≤ v (c i0) := by
    intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, map_zero]; exact zero_le'
    · exact hmax j (Finset.mem_filter.2 ⟨hj, hcj⟩)
  refine ⟨i0, hi0, fun i => ?_⟩
  have h1 := hs0 i
  rw [Submodule.mem_span_finset] at h1
  obtain ⟨g, -, hg⟩ := h1
  have h2 := congrArg (algebraMap (𝓞 E) Ω) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum] at h2
  have hle : v ((D : Ω) * c i) ≤ v (D : Ω) * v (c i0) := by
    rw [← h2]
    refine Valuation.map_sum_le _ (fun y hy => ?_)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [map_zsmul, hf, zsmul_eq_mul, map_mul, map_mul]
    calc v (g (f j) : Ω) * (v (D : Ω) * v (c j)) ≤ 1 * (v (D : Ω) * v (c j)) := by
          gcongr; exact hint _
      _ ≤ v (D : Ω) * v (c i0) := by rw [one_mul]; gcongr; exact hmax' j hj
  rw [map_mul] at hle
  have hle' : v (c i) ≤ v (c i0) := by
    calc v (c i) = (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i)) := (inv_mul_cancel_left₀ hDv _).symm
      _ ≤ (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i0)) := by gcongr
      _ = v (c i0) := inv_mul_cancel_left₀ hDv _
  have hv0 : v (c i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hi0
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc v (c i) * (v (c i0))⁻¹ ≤ v (c i0) * (v (c i0))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hv0

theorem prim_of_bounded : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ a : X.K, a ≠ 0 → (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp a).coeff r)) → ∃ κ : Ω, κ ≠ 0 ∧ Prim A (X.exp (algebraMap Ω X.K κ * a)) ∧ ∃ S : Finset Ω, ∀ r, (X.exp (algebraMap Ω X.K κ * a)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X _ l _ A _ a ha hb
  obtain ⟨S, D, hD, hc⟩ := hb
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hne : ∃ r, (X.exp a).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : X.exp a = 0 := HahnSeries.ext (funext h)
    exact ha ((map_eq_zero_iff X.exp (RingHom.injective X.exp.toRingHom)).1 h0)
  obtain ⟨r0, h0, hA⟩ := exists_dividing A (fun r => (X.exp a).coeff r) _ D hD hc hne
  have hcoef : ∀ (κ : Ω) r, (X.exp (algebraMap Ω X.K κ * a)).coeff r = κ * (X.exp a).coeff r := by
    intro κ r
    rw [map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  refine ⟨((X.exp a).coeff r0)⁻¹, inv_ne_zero h0, ⟨fun r => ?_, r0, ?_⟩, S, fun r => ?_⟩
  · rw [hcoef, mul_comm]; exact hA r
  · rw [hcoef, inv_mul_cancel₀ h0, inv_one]
    exact ⟨one_ne_zero, one_mem A⟩
  · rw [hcoef]
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (hc r0).1) (hc r).1

end GlobalTheory.PrimConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMem
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def congrAlg (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) :
    Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {M | ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) ((M i j : 𝒪[k]) : k)}
  mul_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
      (triv_zero _) ?_
    intro l _
    have hAv : valuation k ((A i l : 𝒪[k]) : k) ≤ 1 := (A i l).2
    have hBv : valuation k ((B l j : 𝒪[k]) : k) ≤ 1 := (B l j).2
    have h1 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((B l j : 𝒪[k]) : k) := mul_le_of_le_one_left' hAv
    have h2 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((A i l : 𝒪[k]) : k) := mul_le_of_le_one_right' hBv
    rcases le_or_gt l i with hli | hil
    · refine triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) ?_
      exact hψ l i j j hli hij.le le_rfl _ (hB l j (lt_of_le_of_lt hli hij))
    rcases le_or_gt j l with hjl | hlj
    · refine triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) ?_
      exact hψ i i j l le_rfl hij.le hjl _ (hA i l hil)
    · have e : ψ i / ψ l * (ψ l / ψ j) = ψ i / ψ j := div_mul_div_cancel _ _ _
      rw [← e]
      exact triv_mul _ _ _ (triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) (hA i l hil))
        (triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) (hB l j hlj))
  one_mem' := by
    intro i j hij
    simp [Matrix.one_apply_ne hij.ne, triv_zero]
  add_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    simpa using triv_add _ _ _ (hA i j hij) (hB i j hij)
  zero_mem' := by
    intro i j hij
    simp [triv_zero]
  algebraMap_mem' := by
    intro c i j hij
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_ne _ hij.ne, triv_zero]

theorem inv_val_mem_adjoin {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) :
    ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) ∈ Algebra.adjoin R {(g : Matrix (Fin m) (Fin m) R)} := by
  set A : Matrix (Fin m) (Fin m) R := (g : Matrix (Fin m) (Fin m) R)
  set p := A.charpoly
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  have hdec : p.divX * Polynomial.X + Polynomial.C (p.coeff 0) = p := Polynomial.divX_mul_X_add p
  have hdet : A.det = (-1) ^ Fintype.card (Fin m) * p.coeff 0 := Matrix.det_eq_sign_charpoly_coeff A
  have hu : IsUnit (p.coeff 0) := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp (Units.isUnit g)
    rw [hdet] at h
    exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hu
  have h1 : Polynomial.aeval A p.divX * A = -algebraMap R _ (p.coeff 0) := by
    rw [← hdec] at hCH
    simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
    exact eq_neg_of_add_eq_zero_left hCH
  have key : ((-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX) * A = 1 := by
    rw [smul_mul_assoc, h1, Algebra.algebraMap_eq_smul_one, ← hu, neg_smul_neg, smul_smul,
      Units.inv_mul, one_smul]
  have e : ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = (-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX :=
    Units.inv_eq_of_mul_eq_one_left key
  rw [e]
  exact Subalgebra.smul_mem _ (Polynomial.aeval_mem_adjoin_singleton R A) _

end GlobalTheory.PsType


open GlobalTheory.PsType in
theorem GlobalTheory.PsType.grp_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  intro k _ _ _ _ n ψ hψ a ha
  obtain ⟨haK, hat⟩ := ha
  obtain ⟨g, rfl⟩ := haK
  have hg : (g : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ := fun i j hij => hat i j hij
  have hinv : ((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hg) (inv_val_mem_adjoin g)
  refine ⟨inv_mem ⟨g, rfl⟩, ?_⟩
  intro i j hij
  rw [← map_inv]
  exact hinv i j hij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompact
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  intro k _ _ _ _ n ψ hψ
  have hT := (triv_ev_props k).2.2.2.2.2.1
  have hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x} := fun i j => by
    refine hT _ ?_
    rw [div_eq_mul_inv]
    exact (hψ i).mul (hψ j).inv
  have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j := fun i j =>
    by
    have h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  have hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x} := by
    ext g; simp [grp]
  rw [hE]
  refine ⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangular
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNQ

theorem qAll_affine : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  intro E N a d b f hE hN ha hd hf
  obtain ⟨c, hc, hcE⟩ := hf
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let e : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * (((k : ℚ) * b / (N * d) : ℚ) : ℂ))
  refine ⟨fun m => if a ∣ m then c (m / a) * e (m / a) else 0, ?_, ?_⟩
  · intro τ
    have hz : 0 < (((a : ℂ) * τ + b) / d).im := by
      have : (((a : ℂ) * τ + b) / d).im = a * τ.im / d := by
        simp [Complex.div_ofReal_im]
      rw [this]; have := τ.im_pos; positivity
    have hτ := hc (UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hτ
    have hinj : Function.Injective (fun k : ℕ => a * k) := fun x y h => by
      simpa [ha.ne'] using h
    rw [← hinj.hasSum_iff]
    · show HasSum (fun k => _) (f _)
      convert hτ using 1
      funext k
      simp only [Function.comp_apply, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ ha, e]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
      exact congrArg f (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
    · intro m hm
      have : ¬ a ∣ m := by
        rintro ⟨k, rfl⟩; exact hm ⟨k, rfl⟩
      simp [this]
  · intro m
    by_cases h : a ∣ m
    · simp only [h, if_true]
      exact E.mul_mem (hcE _) (hE _)
    · simp only [h, if_false]; exact E.zero_mem

end GlobalTheory.FNQ
end

