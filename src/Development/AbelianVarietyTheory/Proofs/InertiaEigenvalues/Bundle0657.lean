module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocks
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerParahoric

open GlobalTheory.LevelProduct

theorem exists_cut {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : GA D V) (hS : Lev.finE V h ∈ St β)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ k : GA D V, Lev.finE V k ∈ St β ∧ ∀ PP : Pl D.host.E,
      ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S → redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h)) ∧
      ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ S → redFn β PP (Lev.finE V k) = 1) := by
  induction S using Finset.cons_induction_on with
  | empty =>
    refine ⟨1, ?_, fun PP => ⟨fun hh => absurd hh (Finset.notMem_empty _), fun _ => ?_⟩⟩
    · rw [MonoidHom.map_one]; exact Subgroup.one_mem _
    · rw [MonoidHom.map_one]; exact redFn_one PP
  | cons v S hv ih =>
    obtain ⟨k, hk, hr⟩ := ih
    have hc : Lev.finE V (cmp V v h) ∈ St β := by
      rw [finE_cmp]; exact piece_mem_St (phi_idem v) (phi_idem' v) hS
    have hpos : ∀ PP : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = redFn β PP (Lev.finE V h) := fun PP e => by
      rw [finE_cmp]; exact redFn_piece (phi_idem v) (phi_idem' v) hS PP (resS_phi_pos e)
    have hneg : ∀ PP : Pl D.host.E, ¬ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = 1 := fun PP e => by
      rw [finE_cmp] at hc ⊢; exact redFn_piece_eq_one (phi_idem' v) hc PP (resS_phi_neg e)
    refine ⟨cmp V v h * k, ?_, fun PP => ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hc hk
    · rw [MonoidHom.map_mul, redFn_mul hc hk, Finset.mem_cons]
      by_cases e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
      · refine ⟨fun _ => ?_, fun hn => absurd (Or.inl e) hn⟩
        rw [hpos PP e, (hr PP).2 (e ▸ hv), mul_one]
      · rw [hneg PP e, one_mul]
        exact ⟨fun hh => (hr PP).1 (hh.resolve_left e), fun hh => (hr PP).2 fun h' => hh (Or.inr h')⟩


set_option maxHeartbeats 1600000 in
theorem exists_mem_smaller : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  classical
  intro D V β Λ _ L Q' xq hQ hoff g hg
  obtain ⟨_, h, rfl⟩ := g
  have hh : Lev.finE V h ∈ lev D.sp.cm V.gram β (Lev.flagL L) := hg
  obtain ⟨-, hS, hP, hq⟩ := mem_parLev.1 (lev_le_parLev hh)
  obtain ⟨k, hk, hr⟩ := exists_cut V β h hS (L.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have h1 : ∀ PP ∈ L.Pg, redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h) := fun PP hPP =>
    (hr PP).1 (Finset.mem_image_of_mem _ hPP)
  have h2 : ∀ PP ∈ Q', redFn β PP (Lev.finE V k) = 1 := fun PP' hPP' => (hr PP').2 fun hm => by
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨a, b, -⟩ := hoff PP hPP PP' hPP'
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact a e'.symm
    · refine b ?_
      rw [e']
      exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩
  have hS' : Lev.finE V h⁻¹ ∈ St β := by rw [MonoidHom.map_inv]; exact Subgroup.inv_mem _ hS
  have h3 : ∀ PP, redFn β PP (Lev.finE V (h⁻¹ * k)) = (redFn β PP (Lev.finE V h))⁻¹ * redFn β PP (Lev.finE V k) :=
    fun PP => by rw [MonoidHom.map_mul, redFn_mul hS' hk, MonoidHom.map_inv, redFn_inv hS]
  have A : Lev.finE V k ∈ lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V k, hk, fun PP hPP => ?_, fun PP hPP => ?_⟩,
      Subgroup.mem_top _⟩
    · rw [h1 PP hPP]; exact hP PP hPP
    · rw [h2 PP hPP]; exact Subgroup.one_mem _
  have B : Lev.finE V (h⁻¹ * k) ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, ?_, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hS' hk
    · rw [h3, h1 PP hPP, inv_mul_cancel]; exact Subgroup.one_mem _
    · rw [h3, h2 PP (hQ hPP), mul_one]; exact Subgroup.inv_mem _ (hq PP hPP)
    · have e : rTup β (Lev.flag1L L) (Lev.finE V (h⁻¹ * k)) = 1 := by
        funext PP
        show upperLeftBlock L.hr (redFn β PP.1 (Lev.finE V (h⁻¹ * k))) = 1
        rw [h3, h1 PP.1 PP.2, inv_mul_cancel]; exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [e]; exact Subgroup.one_mem _
  refine ⟨(finHom V).rangeRestrict k, A, ?_⟩
  have e : (⟨finHom V h, h, rfl⟩ : Bridge.Gf V)⁻¹ * (finHom V).rangeRestrict k = (finHom V).rangeRestrict (h⁻¹ * k) := by
    apply Subtype.ext
    exact ((MonoidHom.map_mul (finHom V) _ _).trans (congrArg (· * finHom V k) (MonoidHom.map_inv (finHom V) h))).symm
  rw [e]
  exact B

end GlobalTheory.SmallerParahoric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRegularCharacterLabelRootProduct
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.RegLabelChar

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

theorem pow_congr (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ^ (g ^ n - 1) = 1) {a b : ℕ}
    (h : L.gen n ^ a = L.gen n ^ b) : t ^ a = t ^ b := by
  have hN := L.gen_order n hn
  have hq1 : 0 < g ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
    omega
  have hpos : 0 < orderOf (L.gen n) := hN ▸ hq1
  have h2 : L.gen n ^ (a % orderOf (L.gen n)) = L.gen n ^ (b % orderOf (L.gen n)) := by
    rw [pow_mod_orderOf, pow_mod_orderOf, h]
  have h3 := pow_injOn_Iio_orderOf (Set.mem_Iio.2 (Nat.mod_lt a hpos)) (Set.mem_Iio.2 (Nat.mod_lt b hpos)) h2
  rw [hN] at h3
  rw [← Nat.mod_add_div a (g ^ n - 1), ← Nat.mod_add_div b (g ^ n - 1), pow_add, pow_add, pow_mul, pow_mul, ht,
    one_pow, one_pow, h3]

theorem thetaOf_eq (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : L.teich x ^ (g ^ n - 1) = 1) {z : Formalism.CyclotomicNorms.Fbar g} {k : ℕ} (hz : z = L.gen n ^ k) :
    thetaOf L n x z = L.teich x ^ k := by
  have he : ∃ m : ℕ, z = L.gen n ^ m := ⟨k, hz⟩
  unfold thetaOf
  rw [dite_eq_left he]
  exact pow_congr L hn hx ((Exists.choose_spec he).symm.trans hz)

theorem exists_regularChar :
    ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (hn : 0 < n) (P : (ZMod g)[X])
    (hP : IsPrimeLab n P) (K : Type) [Field K] [Finite K] (hK : Nat.card K = g ^ n) (ι : K →+* Formalism.CyclotomicNorms.Fbar g),
    ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧
      (∃ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = thetaOf L n x (ι u)) ∧
      ∀ u : Kˣ, ι u = L.gen n →
        ∏ j ∈ Finset.range n, (X - C ((θ (u ^ g ^ j) : ℂˣ) : ℂ)) = GlobalTheory.SerSys.TameGen.liftPoly L.teich P := by
  intro g _ L n hn P hP K _ _ hK ι
  classical
  haveI := Fintype.ofFinite K
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' hg1
  have hq1 : 0 < g ^ n - 1 := by omega
  haveI : NeZero (g ^ n - 1) := ⟨hq1.ne'⟩
  have hdegP : P.natDegree = n := hP.2.2.2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Formalism.CyclotomicNorms.Fbar g) P (degree_pos_of_irreducible hP.2.1).ne'
  have hxmem : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
    simpa [Formalism.CyclotomicNorms.rootsBar, hP.2.1.ne_zero, aeval_def, eval_map] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero'] at hx
    exact hP.2.2.1 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective).1 hx)
  have hxq : x ^ (g ^ n - 1) = 1 := by
    have h1 : x ^ g ^ n = x := (GlobalTheory.GreenExists.pow_eq_self_iff hP.2.1 hx n).2 (hdegP ▸ dvd_refl _)
    have h2 : x ^ (g ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, h1, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have ht1 : L.teich x ^ (g ^ n - 1) = 1 := by rw [← map_pow, hxq, map_one]
  have hgo : orderOf (L.gen n) = g ^ n - 1 := L.gen_order n hn
  have hprim : IsPrimitiveRoot (L.gen n) (g ^ n - 1) := hgo ▸ IsPrimitiveRoot.orderOf _
  have hcardK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : ∀ u : Kˣ, ∃ k : ℕ, ι u = L.gen n ^ k := fun u => by
    have h1 : (ι u) ^ (g ^ n - 1) = 1 := by
      rw [← map_pow, ← hcardK, FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  let f : Kˣ →* ℂ :=
    { toFun := fun u => thetaOf L n x (ι u)
      map_one' := by
        rw [thetaOf_eq L hn ht1 (k := 0) (by rw [Units.val_one, map_one, pow_zero]), pow_zero]
      map_mul' := fun u v => by
        obtain ⟨a, ha⟩ := hpow u
        obtain ⟨b, hb⟩ := hpow v
        rw [thetaOf_eq L hn ht1 ha, thetaOf_eq L hn ht1 hb,
          thetaOf_eq L hn ht1 (k := a + b) (by rw [Units.val_mul, map_mul, ha, hb, pow_add]), pow_add] }
  have hf : ∀ u : Kˣ, ((f.toHomUnits u : ℂˣ) : ℂ) = thetaOf L n x (ι u) := fun u => rfl
  have hfpow : ∀ (u : Kˣ) (m : ℕ), ι u = L.gen n → ((f.toHomUnits (u ^ m) : ℂˣ) : ℂ) = L.teich x ^ m :=
    fun u m hu => by
      rw [hf]
      exact thetaOf_eq L hn ht1 (by rw [Units.val_pow_eq_pow_val, map_pow, hu])

  have hroots := GlobalTheory.GreenExists.rootsBar_eq hP.2.1 hx
  rw [hdegP] at hroots
  have hnd : (Formalism.CyclotomicNorms.rootsBar P).Nodup := by
    unfold Formalism.CyclotomicNorms.rootsBar
    exact nodup_roots ((PerfectField.separable_of_irreducible hP.2.1).map)
  rw [hroots] at hnd
  refine ⟨f.toHomUnits, ?_, ⟨x, hxmem, hf⟩, ?_⟩
  ·
    intro i j hi hj h
    obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hwo : orderOf w = g ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
    have hιw : orderOf (ι (w : K)) = g ^ n - 1 := by
      have h := orderOf_injective ι.toMonoidHom ι.injective (w : K)
      rw [orderOf_units, hwo] at h
      exact h
    have hwp : IsPrimitiveRoot (ι (w : K)) (g ^ n - 1) := hιw ▸ IsPrimitiveRoot.orderOf _
    obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one (hgo ▸ pow_orderOf_eq_one (L.gen n))
    have hu0 : ι ((w ^ k : Kˣ) : K) = L.gen n := by rw [Units.val_pow_eq_pow_val, map_pow, hk]
    have h1 := congrArg (fun φ : Kˣ →* ℂˣ => ((φ (w ^ k) : ℂˣ) : ℂ)) h
    simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h1
    have hθ0 : ((f.toHomUnits (w ^ k) : ℂˣ) : ℂ) = L.teich x := by
      rw [hf]
      exact (thetaOf_eq L hn ht1 (k := 1) (by rw [hu0, pow_one])).trans (pow_one _)
    rw [hθ0, ← map_pow, ← map_pow] at h1
    have h2 := L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0) h1
    exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_range.2 hi) j
      (Finset.mem_range.2 hj) h2
  · intro u hu
    rw [GlobalTheory.SerSys.TameGen.liftPoly, hroots, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    rw [Function.comp_apply, hfpow u _ hu, map_pow L.teich]

end GlobalTheory.RegLabelChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueFieldEmbeddingPlaceOver
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem GlobalTheory.residue_ringOfIntegers_to_place : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g),
    ∃ ι : 𝓞 E' ⧸ w'.asIdeal →+* Formalism.CyclotomicNorms.Fbar g,
      ∀ x : 𝓞 E', ι (Ideal.Quotient.mk _ x) = redThrough A κ (algebraMap E' Ω (x : E')) := by
  intro E' Ω _ _ _ _ g _ A w' h' κ
  classical
  have hmem : ∀ x : 𝓞 E', algebraMap E' Ω (x : E') ∈ A := by
    intro x
    have hi : IsIntegral ℤ (algebraMap E' Ω (x : E')) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E' Ω)
    have h2 : IsIntegral A.valuation.integer (algebraMap E' Ω (x : E')) := hi.tower_top
    have h3 := (Valuation.integer.integers A.valuation).mem_of_integral h2
    obtain ⟨y, hy⟩ := h3
    rw [← hy]
    exact (A.valuation_le_one_iff _).1 (by simpa [Algebra.smul_def] using y.2)
  let φ : 𝓞 E' →+* A :=
    { toFun := fun x => ⟨algebraMap E' Ω (x : E'), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let ψ : 𝓞 E' →+* Formalism.CyclotomicNorms.Fbar g := κ.toRingHom.comp ((IsLocalRing.residue A).comp φ)
  have hker : ∀ x ∈ w'.asIdeal, ψ x = 0 := by
    intro x hx
    have hlt : A.valuation (algebraMap E' Ω (x : E')) < 1 := (h' x).2 hx
    have hm : φ x ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff (φ x)).2 hlt
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [(IsLocalRing.residue_eq_zero_iff (φ x)).2 hm, map_zero]
  refine ⟨Ideal.Quotient.lift _ ψ hker, fun x => ?_⟩
  rw [Ideal.Quotient.lift_mk]
  unfold redThrough
  rw [dite_eq_left (hmem x)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedAlgebraicOfLimitOfFixedElements
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixApprox

theorem val_lt_map {K : Type} [Field K] (B : ValuationSubring K) (τ : K ≃+* K)
    (hB : ∀ z, τ z ∈ B ↔ z ∈ B) (a b : K) (h : B.valuation a < B.valuation b) :
    B.valuation (τ a) < B.valuation (τ b) := by
  have hb : b ≠ 0 := by
    rintro rfl; simp at h
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero]
    exact (Valuation.pos_iff _).2 (by simpa using hb)
  · have hta : τ a ≠ 0 := by simpa using ha
    rw [← not_le] at h ⊢
    intro h'
    apply h
    have h1 : B.valuation (τ b / τ a) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hta)]; exact h'
    rw [ValuationSubring.valuation_le_one_iff, ← map_div₀, hB] at h1
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 ha)] at h1
    exact h1

theorem fix_of_approx : ∀ (K : Type) [Field K] [CharZero K] (B : ValuationSubring K) (τ : K ≃+* K), (∀ z, τ z ∈ B ↔ z ∈ B) → ∀ y : K, IsAlgebraic ℚ y → (∀ δ : K, δ ≠ 0 → ∃ u : K, τ u = u ∧ B.valuation (y - u) < B.valuation δ) → τ y = y := by
  intro K _ _ B τ hB y _ happ
  by_contra hne
  set m := τ y with hm
  set s := τ.symm y with hs
  have hym : y - m ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hys : y - s ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg τ (sub_eq_zero.1 h)
    rw [hs, RingEquiv.apply_symm_apply] at h'
    exact h'
  obtain ⟨u, hu, hlt⟩ := happ (if B.valuation (y - m) ≤ B.valuation (y - s) then y - m else y - s)
    (by split_ifs <;> assumption)
  have h1 : B.valuation (y - u) < B.valuation (y - m) := by
    split_ifs at hlt with hc
    · exact hlt
    · exact lt_of_lt_of_le hlt (le_of_lt (not_le.1 hc))
  have h2 : B.valuation (y - u) < B.valuation (y - s) := by
    split_ifs at hlt with hc
    · exact lt_of_lt_of_le hlt hc
    · exact hlt
  have h3 := val_lt_map B τ hB _ _ h2
  have e1 : τ (y - u) = m - u := by rw [map_sub, hu]
  have e2 : τ (y - s) = m - y := by rw [map_sub, hs, RingEquiv.apply_symm_apply]
  rw [e1, e2] at h3
  have h4 : B.valuation (m - y) = B.valuation (y - m) := Valuation.map_sub_swap _ _ _
  have h5 : m - y = (m - u) - (y - u) := by ring
  have h6 : B.valuation (m - y) < B.valuation (m - y) := by
    calc B.valuation (m - y) = B.valuation ((m - u) - (y - u)) := by rw [← h5]
      _ < B.valuation (m - y) := Valuation.map_sub_lt _ h3 (h4 ▸ h1)
  exact lt_irrefl _ h6

end GlobalTheory.FixApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOne
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_pow_sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1) (hab : A.valuation (a - b) < 1) (k : ℕ) :
    A.valuation (a ^ k - b ^ k) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b), map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hab

theorem frob_pow_apply_sub_lt_one :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  intro F Ω _ _ _ _ A q σ hσ n
  obtain ⟨hD, hF⟩ := hσ
  have hD' : σ ∈ ReciprocityTheory.Gal.Dec (F := F) A := hD
  have hle : ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (σ y) ≤ 1 := by
    intro y hy
    rw [A.valuation_le_one_iff] at hy ⊢
    exact (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hD' y).mpr hy
  induction n with
  | zero =>
    intro x _
    simp
  | succ n ih =>
    intro x hx
    have e : (σ ^ (n + 1)) x - x ^ (q ^ (n + 1)) =
        σ ((σ ^ n) x - x ^ (q ^ n)) + ((σ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ' σ n, AlgEquiv.mul_apply, map_sub, map_pow, ← pow_mul, ← pow_succ']
      ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · exact (ReciprocityTheory.Gal.valuation_apply_lt_one_iff hD' _).mpr (ih x hx)
    · refine valuation_pow_sub_pow_lt_one A (hle x hx) ?_ (hF x hx) _
      rw [map_pow]; exact pow_le_one' hx _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenFinite

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S)
    (g : GA D T) (c : ℂ) (f : WO S T → ℂ) : thetaKO om h g (c • f) = c * thetaKO om h g f := by
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem integrableOn_downIntegrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ)
      (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f l g hf
  have hm := hG.core.models
  have hom := (hP i t).datum
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hom.std (Vc D i) (Wc D i) _ _ (R.ωP i t) hom hpos ℂ
    (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f) (fun x => theta_smul x hf) (fun h => l (R.extV i t y h)) hcont hinv
    (R.νV i t) (R.fdV i t) (hm.νV i t).1.1 (hm.νV i t).2 g
  have e : (fun h => thetaKO (R.ωP i t) h g (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f (l (R.extV i t y h)))) =
      fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h) := by
    funext h
    exact (thetaKO_smul (R.ωP i t) h g _ f).trans (mul_comm _ _)
  rw [e] at key
  exact key

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianStabilizerNormalizesFrameUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  first | exact @GlobalTheory.RallisCusp.conj_mem_NI | exact GlobalTheory.RallisCusp.conj_mem_NI | (intros; apply GlobalTheory.RallisCusp.conj_mem_NI <;> assumption)
end

