module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import GroundTheory.LocalFields.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormApproximationFirstLevel
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLattice
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormEq

open GlobalTheory.UTr GroundTheory.LocalField

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem sigO_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : sigO σ h.2.1 (piO h) = piO h :=
  Subtype.ext h.2.2.1

theorem conj_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {a : Alg P} (ha : a ∈ piPow h P m) : conj P a ∈ piPow h P m := by
  set_option backward.isDefEq.respectTransparency false in
    unfold piPow at *
    simp only [Ideal.mem_span_singleton] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    have hp : conj P (algebraMap (intL L) (Alg P) (piO h)) = algebraMap (intL L) (Alg P) (piO h) :=
      (GlobalTheory.UTr.conj_algebraMap P _).trans (congrArg _ (sigO_piO h))
    exact ⟨conj P b, by
      rw [map_mul, map_pow]
      exact congrArg (fun x : Alg P => x ^ m * conj P b) hp⟩

theorem normU_mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {g : (Alg P)ˣ} (hg : g ∈ filt h P m) : normU P g ∈ filt h P m := by
  set_option backward.isDefEq.respectTransparency false in
    change (g : Alg P) - 1 ∈ piPow h P m at hg
    change ((normU P g : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P m
    have hc : conj P (g : Alg P) - 1 ∈ piPow h P m := by
      have := conj_mem_piPow h P m hg
      rwa [map_sub, map_one] at this
    have e : ((normU P g : (Alg P)ˣ) : Alg P) - 1 = ((g : Alg P) - 1) * conj P (g : Alg P) + (conj P (g : Alg P) - 1) := by
      rw [val_normU]; ring
    rw [e]
    exact (piPow h P m).add_mem ((piPow h P m).mul_mem_right _ hg) hc

theorem div_mem_of_sub_mem {R : Type} [CommRing R] {I : Ideal R} {x u : Rˣ} (hx : (x : R) - u ∈ I) :
    ((x / u : Rˣ) : R) - 1 ∈ I := by
  have e : ((x / u : Rˣ) : R) - 1 = ((x : R) - u) * ((u⁻¹ : Rˣ) : R) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [e]; exact I.mul_mem_right _ hx

theorem normU_surj (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (hP : P.1.Separable)
    (x : (Alg P)ˣ) (hx : x ∈ plus P) : ∃ u : (Alg P)ˣ, normU P u = x := by
  have hs : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  let f : (Alg P)ˣ →* plus P := (normU P).codRestrict (plus P) (normU_mem_plus P hs)
  let E : ℕ → Subgroup (plus P) := fun m => (filt h P m).comap (plus P).subtype
  have hE : Antitone E := fun a b hab => Subgroup.comap_mono (filt_antitone h P hab)
  have hsepE : FiltrationSeparated E := by
    intro g hg
    have h0 : ((g : (Alg P)ˣ) : Alg P) - 1 = 0 := GlobalTheory.T.eq_zero_of_mem_all_powers L σ ϖ q h P _ fun m => hg m
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h0))
  have hE0 : E (id 0) = ⊤ := by
    ext g; change ((g : (Alg P)ˣ) ∈ filt h P 0) ↔ True
    rw [filt_zero]; exact ⟨fun _ => trivial, fun _ => Subgroup.mem_top _⟩
  have hmap : ∀ n, ∀ g ∈ filt h P n, f g ∈ E (id n) := fun n g hg => normU_mem_filt h P n hg
  have hgr : ∀ n, ∀ z ∈ E (id n), ∃ g ∈ filt h P n, z / f g ∈ E (id (n + 1)) := by
    intro n z hz
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨u, hu⟩ := _root_.GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one L σ ϖ q h P hP z.1 z.2
      refine ⟨u, by rw [filt_zero]; exact Subgroup.mem_top u, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (0 + 1)
      exact div_mem_of_sub_mem hu
    · obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.norm_approximation_filtration L σ ϖ q h P n hn z.1 z.2 hz
      refine ⟨u, hu, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (n + 1)
      exact div_mem_of_sub_mem hu'
  obtain ⟨u, hu⟩ := surjective_of_graded_surjective (F := filt h P) (E := E) (filt_antitone h P) hE
    (_root_.GlobalTheory.NormEq.filtrationComplete_filt L σ ϖ q h P) hsepE f tendsto_id (filt_zero h P) hE0 hmap hgr ⟨x, hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq
open GlobalTheory.UTr

theorem hermUnit_eq_norm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (y : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X]), (∀ i j, y i j ∈ intL L) → cT σ y * y = 1 → y.charpoly = Q₀.map (intL L).subtype → Q₀.Separable → ∀ t : GL (Fin n) L, (∀ i j, t.val i j ∈ intL L) → (∀ i j, (t⁻¹ : GL (Fin n) L).val i j ∈ intL L) → cT σ t.val = t.val → (∃ p : (intL L)[X], t.val = aeval y (p.map (intL L).subtype)) → ∃ s : GL (Fin n) L, s.val * y = y * s.val ∧ s.val * cT σ s.val = t.val := by
  intro L _ _ _ σ ϖ q h n y Q₀ hy hyu hch hsep t ht hti htc ⟨p, hp⟩
  let sO := sigO σ h.2.1
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  let yO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨y i j, hy i j⟩
  have hyO : Φ yO = y := rfl
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  have hchO : yO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← hyO]
    exact (Matrix.charpoly_map yO (intL L).subtype).symm
  have hyuO : cT sO yO * yO = 1 := hΦinj (by rw [map_mul, hΦcT, hyO, hyu, map_one])
  have hcsr : IsCsr sO Q₀ := hchO ▸ GlobalTheory.T.conjugate_self_reciprocal_charpoly _ sO n yO hyuO
  let P : Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval yO P.1 = 0 := by
    show aeval yO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly yO
  let ev := evalMat P yO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (root P) r) = aeval yO r := fun r => by
    rw [← aeval_algHom_apply, evalMat_root]
  have hevinj : ∀ z, ev z = 0 → z = 0 := by
    intro z hz
    obtain ⟨r, rfl⟩ := exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n yO r (hchO ▸ hsep) hz
    rw [hchO] at hd
    exact (aeval_root_eq_zero_iff P).2 hd
  have hevinj' : Function.Injective ev := (injective_iff_map_eq_zero ev).2 hevinj
  have hcomp : Φ.comp (algebraMap (intL L) (Matrix (Fin n) (Fin n) (intL L))) =
      (algebraMap L (Matrix (Fin n) (Fin n) L)).comp (intL L).subtype := by
    ext a i j
    simp only [RingHom.coe_comp, Function.comp_apply, Φ, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have hΦaeval : ∀ r : (intL L)[X], Φ (aeval yO r) = aeval y (r.map (intL L).subtype) := by
    intro r
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, eval₂_map, hcomp, hyO]

  let tz : Alg P := aeval (root P) p
  let tO := ev tz
  have htO : Φ tO = t.val := by rw [show tO = aeval yO p from hev p, hΦaeval, hp]
  let tiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨(t⁻¹ : GL (Fin n) L).val i j, hti i j⟩
  have htiO : tO * tiO = 1 := hΦinj (by
    rw [map_mul, htO, map_one]; exact t.mul_inv)
  have hdet : IsUnit tO.det := isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz tO.charpoly = 0 := hevinj _ (by
      rw [← aeval_algHom_apply]; exact Matrix.aeval_self_charpoly tO)
    have hc0 : IsUnit (tO.charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff tO
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add tO.charpoly)
    rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz tO.charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (Alg P)ˣ := hunit.unit

  have hyuO' : yO * cT sO yO = 1 := mul_eq_one_comm.1 hyuO
  let gU : UJ sO (1 : Matrix (Fin n) (Fin n) (intL L)) :=
    ⟨⟨yO, cT sO yO, hyuO', hyuO⟩, by
      show cT sO yO * 1 * yO = 1
      rw [Matrix.mul_one, hyuO]⟩
  have hcT : ∀ z, cT sO (ev z) = ev (conj P z) := fun z => by
    have := cT_evalMat P gU hg z
    rwa [Matrix.mul_one, Matrix.one_mul] at this
  have htz : conj P tz = tz := hevinj' (by
    rw [← hcT]
    exact hΦinj (by rw [hΦcT, htO, htc]))
  have hT : T ∈ plus P := (GlobalTheory.UTr.mem_plus (P := P)).2 htz
  obtain ⟨u, hu⟩ := normU_surj L σ ϖ q h P hsep T hT
  let Ψ : Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * y = y * Φ (ev u)
    rw [← hyO, ← map_mul, ← map_mul]
    congr 1
    rw [← evalMat_root P yO hg, ← map_mul, ← map_mul, mul_comm]
  · show Φ (ev u) * cT σ (Φ (ev u)) = t.val
    rw [← hΦcT, hcT, ← map_mul, ← map_mul, ← val_normU, hu, ← htO]
    rfl

end GlobalTheory.NormEq
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalPointsIntegralAlmostAll
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dite_eq_left (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.CocycleMultiplicative.norm_eq_one_of_root γ τ z hz

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.MonicDivisorSignSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem monic_of_mem_normalizedFactors {P q : k[X]} (hq : q ∈ normalizedFactors P) : q.Monic := by
  have h0 : q ≠ 0 := (irreducible_of_normalized_factor q hq).ne_zero
  rw [← normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize h0

theorem monic_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    (∏ q ∈ t, q).Monic := by
  exact Polynomial.monic_prod_of_monic t id fun q hq => monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 (ht hq))

theorem normalizedFactors_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    normalizedFactors (∏ q ∈ t, q) = t.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id',
    normalizedFactors_prod_eq _ fun q hq => irreducible_of_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))]
  conv_rhs => rw [← Multiset.map_id t.val]
  exact Multiset.map_congr rfl fun q hq => normalize_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))

theorem prod_sub_dvd {P : k[X]} (hP : P ≠ 0) (t : Finset k[X])
    (ht : t ⊆ (normalizedFactors P).toFinset) : (∏ q ∈ t, q) ∣ P := by
  have h0 : (∏ q ∈ t, q) ≠ 0 := (monic_prod_sub t ht).ne_zero
  rw [dvd_iff_normalizedFactors_le_normalizedFactors h0 hP, normalizedFactors_prod_sub t ht]
  exact (Multiset.le_iff_subset t.nodup).2 fun q hq => Multiset.mem_toFinset.1 (ht hq)

theorem eq_prod_sub {P Q : k[X]} (hP : P ≠ 0) (hsq : Squarefree P) (hQ : Q.Monic) (hQP : Q ∣ P) :
    (normalizedFactors Q).toFinset ⊆ (normalizedFactors P).toFinset ∧
      Q = ∏ q ∈ (normalizedFactors Q).toFinset, q := by
  have hQ0 := hQ.ne_zero
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hQ0 hP).1 hQP
  refine ⟨fun a ha => Multiset.mem_toFinset.2 (Multiset.mem_of_le hle (Multiset.mem_toFinset.1 ha)), ?_⟩
  have hnd : (normalizedFactors Q).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hQ0).1 (hsq.squarefree_of_dvd hQP)
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
    prod_normalizedFactors_eq hQ0]
  exact ((Polynomial.normalize_eq_self_iff_monic hQ0).2 hQ).symm

end GlobalTheory.DivSum

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem isCoprime_of_sub {P q : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset)
    (hq : q ∈ (normalizedFactors P).toFinset) (hqt : q ∉ t) : IsCoprime q (∏ r ∈ t, r) := by
  refine IsCoprime.prod_right fun r hr => ?_
  have hqP := Multiset.mem_toFinset.1 hq
  have hrP := Multiset.mem_toFinset.1 (ht hr)
  rw [(irreducible_of_normalized_factor q hqP).coprime_iff_not_dvd]
  intro hd
  exact hqt (normalizedFactors_eq_of_dvd P q hqP r hrP hd ▸ hr)

theorem s_prod_sub {P : k[X]} (hP : P ≠ 0) (s : k[X] → ℂ)
    (hmul : ∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂)
    (h1 : s 1 = 1) (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    s (∏ q ∈ t, q) = ∏ q ∈ t, s q := by
  induction t using Finset.induction_on with
  | empty => simp [h1]
  | insert a t ha ih =>
    have ht' : t ⊆ (normalizedFactors P).toFinset := fun x hx => ht (Finset.mem_insert_of_mem hx)
    have haP : a ∈ (normalizedFactors P).toFinset := ht (Finset.mem_insert_self a t)
    have hma : a.Monic := monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 haP)
    have hd : a * ∏ q ∈ t, q ∣ P := by
      have h := prod_sub_dvd hP _ ht
      rwa [Finset.prod_insert ha] at h
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      hmul _ _ hma (monic_prod_sub t ht') hd (isCoprime_of_sub t ht' haP ha), ih ht']

theorem finsum_monic_divisors_sign : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ,
    (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) →
    (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) →
    {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧
      ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 =
        if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  intro k _ P hPm hPs s hmul hsgn
  have hP : P ≠ 0 := hPm.ne_zero
  have hsq : Squarefree P := hPs.squarefree
  set F := (normalizedFactors P).toFinset with hF
  have memF : ∀ q ∈ F, q.Monic ∧ q ∣ P := fun q hq =>
    ⟨monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq)⟩
  have h1 : s 1 = 1 := by
    have hm := hmul 1 1 monic_one monic_one (by rw [one_mul]; exact one_dvd P) isCoprime_one_left
    rw [one_mul] at hm
    rcases hsgn 1 monic_one (one_dvd P) with h | h
    · exact h
    · rw [h] at hm
      norm_num at hm
  let φ : {t // t ∈ F.powerset} → {Q : k[X] // Q.Monic ∧ Q ∣ P} := fun t =>
    ⟨∏ q ∈ t.1, q, monic_prod_sub t.1 (Finset.mem_powerset.1 t.2),
      prod_sub_dvd hP t.1 (Finset.mem_powerset.1 t.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg (fun Q : {Q : k[X] // Q.Monic ∧ Q ∣ P} => normalizedFactors Q.1) hab
    simp only [φ] at h
    rw [normalizedFactors_prod_sub a.1 (Finset.mem_powerset.1 a.2),
      normalizedFactors_prod_sub b.1 (Finset.mem_powerset.1 b.2)] at h
    exact Subtype.ext (Finset.val_injective h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨Q, hQm, hQd⟩
    obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
    exact ⟨⟨_, Finset.mem_powerset.2 hsub⟩, Subtype.ext heq.symm⟩
  have hs1 : ∀ q ∈ F, s q = 1 ∨ s q = -1 := fun q hq => hsgn q (memF q hq).1 (memF q hq).2
  refine ⟨?_, ?_⟩
  · have hsub : {Q : k[X] | Q.Monic ∧ Q ∣ P} ⊆ ((F.powerset.image fun t => ∏ q ∈ t, q : Finset k[X]) : Set k[X]) := by
      intro Q hQ
      obtain ⟨⟨t, ht⟩, htQ⟩ := hsurj ⟨Q, hQ⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, ht, congrArg Subtype.val htQ⟩)
    exact (Finset.finite_toSet _).subset hsub
  · rw [← finsum_comp_equiv (Equiv.ofBijective φ ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
    have hsum : ∑ t : {t // t ∈ F.powerset}, s (Equiv.ofBijective φ ⟨hinj, hsurj⟩ t).1 = ∏ q ∈ F, (1 + s q) := by
      rw [Finset.prod_one_add, ← Finset.sum_coe_sort F.powerset]
      refine Finset.sum_congr rfl fun t _ => ?_
      exact s_prod_sub hP s hmul h1 t.1 (Finset.mem_powerset.1 t.2)
    rw [hsum]
    split_ifs with hall
    · rw [Finset.prod_congr rfl fun q hq => show 1 + s q = 2 by
        rw [hall q (memF q hq).1 (memF q hq).2]
        norm_num, Finset.prod_const]
      have hnd : (normalizedFactors P).Nodup := (squarefree_iff_nodup_normalizedFactors hP).1 hsq
      rw [hF, Multiset.card_toFinset, hnd.dedup]
      rfl
    · push_neg at hall
      obtain ⟨Q, hQm, hQd, hQs⟩ := hall
      obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
      have hsQ := s_prod_sub hP s hmul h1 _ hsub
      rw [← heq] at hsQ
      by_contra hne
      apply hQs
      rw [hsQ]
      refine Finset.prod_eq_one fun q hq => ?_
      rcases hs1 q (hsub hq) with h | h
      · exact h
      · exact absurd (Finset.prod_eq_zero (hsub hq) (by rw [h]; norm_num)) hne

end GlobalTheory.DivSum
end

