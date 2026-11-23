module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductive
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilBrauer

theorem eq_of_induced : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  intro hB E Ω _ _ _ _ _ A w h ε ε' hε hε' hcp hchar hind
  classical
  set f : WD h → ℂˣ := fun x => ε x / ε' x with hf
  have fmul : ∀ x y, f (x.lpSum y) = f x * f y := by
    intro x y
    simp only [hf, hε, hε']
    exact mul_div_mul_comm _ _ _ _
  have fcp : ∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hcp x y hxy
    simp only [hf, h1, h2]
  have key : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → f (WD.mk (a.twist μ hμ)) = 1 := by
    intro n a μ hμ hfin
    let u : Weil h →* (Module.End ℂ (Fin n → ℂ))ˣ := a.ρ.toHomUnits
    let G : Subgroup (Module.End ℂ (Fin n → ℂ))ˣ := u.range
    have hGfin : Finite G := by
      have hr : (Set.range u).Finite := by
        refine Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
        refine hfin.subset ?_
        rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      have : ((G : Set (Module.End ℂ (Fin n → ℂ))ˣ)) = Set.range u := MonoidHom.coe_range u
      exact Set.finite_coe_iff.mpr (this ▸ hr)
    letI : Fintype G := Fintype.ofFinite G
    let π : Weil h →* G := u.rangeRestrict
    have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective u
    let ρG : Representation ℂ G (Fin n → ℂ) := (Units.coeHom _).comp G.subtype
    have hρG : ∀ σ, ρG (π σ) = a.ρ σ := fun σ => rfl
    have hπ1 : ∀ σ, π σ = 1 ↔ a.ρ σ = 1 := by
      intro σ
      constructor
      · intro h1
        rw [← hρG, h1, map_one]
      · intro h1
        apply Subtype.ext
        apply Units.ext
        exact h1
    have hopen : IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} := by
      have : {σ : Ine (F := E) A | π (ineIncl h σ) = 1} = {σ | a.ρ (ineIncl h σ) = 1} :=
        Set.ext fun σ => hπ1 _
      rw [this]
      exact a.smooth
    obtain ⟨r, H, χ, c, hbr⟩ := hB G (Fin n → ℂ) ρG
    have hi1 := fun i => _root_.GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace G (H i) (χ i)
    have hi2 := fun i => _root_.GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace G (H i) 1
    choose Rχ vχ hRχ using hi1
    choose R1 v1 hR1 using hi2
    have hp1 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (Rχ i) μ hμ
    have hp2 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (R1 i) μ hμ
    choose bχ hbχ using hp1
    choose b1 hb1 using hp2
    have span_of : ∀ (i : Fin r) (R : Representation ℂ G (Fin (H i).index → ℂ))
        (b : WDRep h (Fin (H i).index → ℂ)) (v : Fin (H i).index → ℂ),
        (∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ)) → Submodule.span ℂ (Set.range fun g => R g v) = ⊤ →
        Submodule.span ℂ (Set.range fun σ => b.ρ σ v) = ⊤ := by
      intro i R b v hb hs
      rw [eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨σ, rfl⟩ := hπs g
      show R (π σ) v ∈ _
      have e : R (π σ) v = (((μ σ)⁻¹ : ℂˣ) : ℂ) • b.ρ σ v := by
        rw [hb, LinearMap.smul_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
    have hpair : ∀ i, f (WD.mk (bχ i)) = f (WD.mk (b1 i)) := by
      intro i
      let H' := (H i).comap π
      have hidx : (H i).index = H'.index := (Subgroup.index_comap_of_surjective _ hπs).symm
      haveI : H'.FiniteIndex := ⟨by rw [← hidx]; exact Subgroup.index_ne_zero_of_finite⟩
      have hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H'} := by
        have hle : (π.comp (ineIncl h)).ker ≤ H'.comap (ineIncl h) := by
          intro σ hσ
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ
          show π (ineIncl h σ) ∈ H i
          rw [hσ]
          exact one_mem _
        exact Subgroup.isOpen_mono hle hopen
      let χ₁ : H' →* ℂˣ := μ.comp H'.subtype * (χ i).comp (π.subgroupComap (H i))
      let χ₂ : H' →* ℂˣ := μ.comp H'.subtype * (1 : H i →* ℂˣ).comp (π.subgroupComap (H i))
      have e1 : ∀ σ : H', (bχ i).ρ σ (vχ i) = (χ₁ σ : ℂ) • vχ i := by
        intro σ
        rw [hbχ, LinearMap.smul_apply, (hRχ i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have e2 : ∀ σ : H', (b1 i).ρ σ (v1 i) = (χ₂ σ : ℂ) • v1 i := by
        intro σ
        rw [hb1, LinearMap.smul_apply, (hR1 i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have hh := hind H' inferInstance hop χ₁ χ₂ _ (bχ i) (b1 i) (vχ i) (v1 i) hidx e1 e2
        (span_of i _ _ _ (hbχ i) (hRχ i).2.1) (span_of i _ _ _ (hb1 i) (hR1 i).2.1)
      simp only [hf]
      exact div_eq_div_iff_mul_eq_mul.mpr hh
    have hμ1 : f (WD.mk (WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ)) = 1 := by
      have := hchar μ hμ
      simp only [hf]
      exact div_eq_one.mpr this
    let F : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → Σ m, WDRep h (Fin m → ℂ) :=
      Sum.elim (Sum.elim (fun _ => ⟨n, a.twist μ hμ⟩)
          (fun _ => ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ⟩))
        (Sum.elim (fun i => ⟨_, bχ i⟩) (fun i => ⟨_, b1 i⟩))
    let cc : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → ℤ :=
      Sum.elim (Sum.elim (fun _ => 1) (fun _ => -(n : ℤ))) (Sum.elim (fun i => -c i) (fun i => c i))
    have htr : ∀ σ, ∑ j, (cc j : ℂ) * LinearMap.trace ℂ (Fin (F j).1 → ℂ) ((F j).2.ρ σ) = 0 := by
      intro σ
      have hb := hbr (π σ)
      rw [Module.finrank_fin_fun] at hb
      have t0 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inl (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inl (default : Unit)))).2.ρ σ) =
          (μ σ : ℂ) * LinearMap.trace ℂ (Fin n → ℂ) (ρG (π σ)) := by
        show LinearMap.trace ℂ (Fin n → ℂ) ((a.twist μ hμ).ρ σ) = _
        rw [WDRep.twist_ρ, map_smul, smul_eq_mul, hρG]
      have t1 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inr (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inr (default : Unit)))).2.ρ σ) = (μ σ : ℂ) := by
        show LinearMap.trace ℂ (Fin 1 → ℂ)
          ((WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ).ρ σ) = _
        rw [WDRep.ofChars_ρ]
        have e : (diagEnd fun _ : Fin 1 => (μ σ : ℂ)) = (μ σ : ℂ) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
          ext v i
          simp
        rw [e, map_smul, LinearMap.trace_one, smul_eq_mul, Module.finrank_fin_fun, Nat.cast_one,
          mul_one]
      have tχ : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inl i))).1 → ℂ)
          ((F (Sum.inr (Sum.inl i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((bχ i).ρ σ) = _
        rw [hbχ, map_smul, smul_eq_mul, (hRχ i).2.2]
      have t1' : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inr i))).1 → ℂ)
          ((F (Sum.inr (Sum.inr i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((b1 i).ρ σ) = _
        rw [hb1, map_smul, smul_eq_mul, (hR1 i).2.2]
        simp
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, t0, t1, tχ, t1']
      simp only [cc, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg, Int.cast_natCast,
        one_mul]
      have hs : ∑ i, -(c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)) +
          ∑ i, (c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)) =
          -(μ σ : ℂ) * ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) (π σ) -
            indFun (H i) (fun _ => 1) (π σ)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hs]
      linear_combination (μ σ : ℂ) * hb
    have hv := _root_.GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero E Ω A w h f fmul fcp _ (fun j => (F j).1) (fun j => (F j).2) cc htr
    have hμ1' : f (WD.mk (F (Sum.inl (Sum.inr (default : Unit)))).2) = 1 := hμ1
    have hp' : ∀ i, f (WD.mk (F (Sum.inr (Sum.inl i))).2) = f (WD.mk (F (Sum.inr (Sum.inr i))).2) :=
      hpair
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, hμ1', hp'] at hv
    simp only [cc, Sum.elim_inl, Sum.elim_inr, zpow_one, _root_.zpow_neg, _root_.one_zpow, inv_one,
      mul_one, ← Finset.prod_mul_distrib, _root_.inv_mul_cancel, Finset.prod_const_one] at hv
    exact hv
  intro x
  have hx := _root_.GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite E Ω A w h (fun x => f x = 1)
    (fun x y hx hy => by rw [fmul, hx, hy, one_mul])
    (fun x y hxy hx => by rw [← fcp x y hxy, hx]) key x
  simp only [hf] at hx
  exact div_eq_one.mp hx

end GlobalTheory.WeilBrauer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfApproxByCongruentGlobalUnits
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unit_pow_dvd_sub_one_of_finite {R : Type} [CommRing R] (g : R)
    [Finite (R ⧸ Ideal.span {g})] :
    ∃ m : ℕ, 0 < m ∧ ∀ ε : Rˣ, g ∣ (ε : R) ^ m - 1 := by
  haveI : Finite (R ⧸ Ideal.span {g})ˣ := Finite.of_injective (fun u => (u : R ⧸ Ideal.span {g})) (fun _ _ h => Units.ext h)
  refine ⟨Nat.card (R ⧸ Ideal.span {g})ˣ, Nat.card_pos, fun ε => ?_⟩
  have h := pow_card_eq_one' (G := (R ⧸ Ideal.span {g})ˣ) (x := Units.map (Ideal.Quotient.mk _).toMonoidHom ε)
  have h2 : Ideal.Quotient.mk (Ideal.span {g}) ((ε : R) ^ Nat.card (R ⧸ Ideal.span {g})ˣ - 1) = 0 := by
    have := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one] at this
    rw [map_sub, map_pow, this, map_one, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
  exact h2

end GlobalTheory

namespace GlobalTheory


open IsDedekindDomain.HeightOneSpectrum in
theorem eq_one_of_approx_by_congruent_units : ChevalleyUnits → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E), Valued.v x = 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → x = 1 := by
  intro hCh E _ _ w x hx hap
  have hE : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    fun k => valuedAdicCompletion_eq_valuation' w k
  set q : ℕ := Ideal.absNorm w.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  set γ := w.intValuation (q : 𝓞 E) with hγdef
  have hγ : γ < 1 := (w.intValuation_lt_one_iff_mem _).2 hqmem
  have key : ∀ n : ℕ, Valued.v (x - 1) ≤ γ ^ (n + 1) := by
    intro n
    set g : 𝓞 E := (q : 𝓞 E) ^ (n + 1) with hgdef
    have hg0 : g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hq0)
    haveI : Finite (𝓞 E ⧸ Ideal.span {g}) := by
      refine (Ideal.absNorm_ne_zero_iff _).1 ?_
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hg0
    obtain ⟨m, hm, hmg⟩ := unit_pow_dvd_sub_one_of_finite g
    obtain ⟨a, ha0, hacop, hch⟩ := hCh E m q hm (Nat.pos_of_ne_zero hq0)

    have hanot : (a : 𝓞 E) ∉ w.asIdeal := by
      intro ha
      obtain ⟨s, t, hst⟩ := (Nat.isCoprime_iff_coprime.2 hacop).map (Int.castRingHom (𝓞 E))
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hst]
      simp only [eq_intCast, Int.cast_natCast]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hqmem)
    have hva : w.intValuation (a : 𝓞 E) = 1 := intValuation_eq_one_iff.2 hanot
    have haE : (a : E) = algebraMap (𝓞 E) E (a : 𝓞 E) := (map_natCast _ _).symm
    have ha0E : (a : E) ≠ 0 := Nat.cast_ne_zero.2 ha0.ne'
    have hvaE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (a : E) ≤ 1 := fun v => by
      rw [haE, valuation_of_algebraMap]; exact v.intValuation_le_one _
    have hwaE : w.valuation E (a : E) = 1 := by rw [haE, valuation_of_algebraMap]; exact hva
    set t : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 E) E g) with htdef
    have hvt : Valued.v t = γ ^ (n + 1) := by
      rw [htdef, hE, valuation_of_algebraMap, hgdef, map_pow]
    have ht0 : t ≠ 0 := by
      intro h; have := hvt; rw [h, map_zero] at this
      exact (pow_ne_zero _ (by have hq0' : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq0; rw [hγdef]; exact w.intValuation_ne_zero _ hq0')) this.symm
    obtain ⟨k, hkv, hkw⟩ := hap a ha0 t ht0
    rw [hvt] at hkw
    have hγn : γ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' hγ (Nat.succ_ne_zero n)

    have hwk : w.valuation E (k : E) = 1 := by
      rw [← hE, ← hx]
      exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hkw (hx ▸ hγn))
    have hk1 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E) - 1) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv
        exact Valuation.map_sub_le _ hwk.le (by rw [map_one])
      · have h1 := (hkv v hv).1
        have : (k : E) - 1 = ((k : E) - 1) / (a : E) * (a : E) := by field_simp
        rw [this, map_mul]
        exact mul_le_one' h1 (hvaE v)
    have hkle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) ≤ 1 := by
      intro v
      have : (k : E) = ((k : E) - 1) + 1 := by ring
      rw [this]; exact Valuation.map_add_le _ (hk1 v) (by rw [map_one])
    have hkile : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E)⁻¹) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [map_inv₀, hwk, inv_one]
      · exact (hkv v hv).2
    obtain ⟨κ, hκ⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkle
    obtain ⟨κ', hκ'⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkile
    have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
    have hkk : κ * κ' = 1 := hinj (by rw [map_mul, hκ, hκ', map_one, mul_inv_cancel₀ k.ne_zero])
    let u : (𝓞 E)ˣ := ⟨κ, κ', hkk, by rw [mul_comm]; exact hkk⟩
    have hdivE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [map_div₀, hwaE, div_one]; exact hk1 _
      · exact (hkv v hv).1
    obtain ⟨y, hy⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hdivE
    have hdvd : (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 := by
      refine ⟨y, hinj ?_⟩
      show algebraMap (𝓞 E) E (κ - 1) = algebraMap (𝓞 E) E ((a : 𝓞 E) * y)
      rw [map_sub, map_one, hκ, map_mul, hy, ← haE]
      field_simp
    obtain ⟨ε, hε⟩ := hch u hdvd
    have hgk : g ∣ κ - 1 := by
      have := hmg ε
      rw [← Units.val_pow_eq_pow_val, ← hε] at this
      exact this
    have hwk1 : w.valuation E ((k : E) - 1) ≤ γ ^ (n + 1) := by
      obtain ⟨c, hc⟩ := hgk
      rw [← hκ, ← map_one (algebraMap (𝓞 E) E), ← map_sub, valuation_of_algebraMap, hc, map_mul]
      have : w.intValuation g = γ ^ (n + 1) := by rw [hgdef, map_pow]
      rw [this]
      exact mul_le_of_le_one_right' (w.intValuation_le_one c)
    have hsplit : x - 1 = -(algebraMap E (w.adicCompletion E) (k : E) - x)
        + algebraMap E (w.adicCompletion E) ((k : E) - 1) := by
      rw [map_sub, map_one]; ring
    rw [hsplit]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Valuation.map_neg]; exact hkw
    · rw [hE]; exact hwk1
  by_contra hne
  have hne' : Valued.v (x - 1) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hγ (Units.mk0 _ hne')
  have h1 := key n
  have h2 : γ ^ (n + 1) ≤ γ ^ n := by rw [pow_succ]; exact mul_le_of_le_one_right' hγ.le
  exact absurd (lt_of_le_of_lt (h1.trans h2) hn) (lt_irrefl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalApproxOfArtinTrivial
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ArtinApprox

open Neutral.B1 GlobalTheory.HeckeGal

theorem isOpen_integers_away {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen {f : FiniteAdeleRing (𝓞 E) E | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ≠ w)

theorem mem_integers_iff {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (z : E) :
    algebraMap E (v.adicCompletion E) z ∈ v.adicCompletionIntegers E ↔ v.valuation E z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  show Valued.v ((z : v.adicCompletion E)) ≤ 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem le_of_mul_inv_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y t : w.adicCompletion E) (ht : t ≠ 0) (h : y * t⁻¹ ∈ w.adicCompletionIntegers E) : Valued.v y ≤ Valued.v t := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀] at h
  have hp : 0 < Valued.v t := by
    rw [pos_iff_ne_zero]; exact (_root_.map_ne_zero _).mpr ht
  simpa using (mul_inv_le_iff₀ hp).mp h

theorem snd_mul_infConn {E : Type} [Field E] [NumberField E] (d c : Ideles E) (hc : c ∈ infConn E) :
    ((d * c : Ideles E) : AdeleRing (𝓞 E) E).2 = (d : AdeleRing (𝓞 E) E).2 := by
  obtain ⟨c', _, rfl⟩ := hc
  rw [Units.val_mul]
  show (d : AdeleRing (𝓞 E) E).2 * 1 = _
  rw [mul_one]

theorem snd_diagUnits {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    ((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).2 = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E) := rfl

theorem localIdele_snd_ne' {E : Type} [Field E] [NumberField E] (w v : HeightOneSpectrum (𝓞 E)) (hv : v ≠ w)
    (x : (w.adicCompletion E)ˣ) : ((localIdele E w x : Ideles E) : AdeleRing (𝓞 E) E).2 v = 1 :=
  (localIdele_isSupportedAt E w x).2 v hv

theorem exists_global_approx : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ), art (Neutral.B1.localIdele E w x) = 1 →
    (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - (x : w.adicCompletion E)) ≤ Valued.v t) := by
  intro E Ω _ _ _ _ _ art ha w x hx a _ t ht
  classical
  have hmem : localIdele E w x ∈ closure (((diagUnits E).range ⊔ infConn E : Subgroup (Ideles E)) : Set (Ideles E)) := by
    rw [← Subgroup.topologicalClosure_coe, ← ha.ker]
    exact hx
  let g1 : Ideles E → FiniteAdeleRing (𝓞 E) E := fun y => (y : AdeleRing (𝓞 E) E).2
  let g2 : Ideles E → FiniteAdeleRing (𝓞 E) E := fun y => ((y⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2
  have hg1 : Continuous g1 := continuous_snd.comp Units.continuous_val
  have hg2 : Continuous g2 := continuous_snd.comp Units.continuous_coe_inv
  let c : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((a : E)⁻¹)
  let U : Set (FiniteAdeleRing (𝓞 E) E) := {f | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E}
  have hU : IsOpen U := isOpen_integers_away w
  let N : Set (Ideles E) := (fun y => (g1 y - 1) * c) ⁻¹' U ∩ g2 ⁻¹' U ∩
    (fun y => (g1 y w - (x : w.adicCompletion E)) * t⁻¹) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  have hN : IsOpen N := by
    refine ((hU.preimage ((hg1.sub continuous_const).mul continuous_const)).inter (hU.preimage hg2)).inter ?_
    exact (Valued.isOpen_valuationSubring _).preimage
      ((((RestrictedProduct.continuous_eval w).comp hg1).sub continuous_const).mul continuous_const)
  have hxN : localIdele E w x ∈ N := by
    refine ⟨⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩
    · show ((g1 (localIdele E w x) - 1) * c) v ∈ v.adicCompletionIntegers E
      have e : ((g1 (localIdele E w x) - 1) * c) v = 0 := by
        show (((localIdele E w x : Ideles E) : AdeleRing (𝓞 E) E).2 v - 1) * c v = 0
        rw [localIdele_snd_ne' w v hv, sub_self, zero_mul]
      rw [e]; exact zero_mem _
    · show g2 (localIdele E w x) v ∈ v.adicCompletionIntegers E
      have e : g2 (localIdele E w x) v = 1 := by
        show (((localIdele E w x)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 v = 1
        rw [← map_inv]
        exact localIdele_snd_ne' w v hv _
      rw [e]; exact one_mem _
    · show (g1 (localIdele E w x) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E
      have e : g1 (localIdele E w x) w = (x : w.adicCompletion E) := localIdele_snd_self E w x
      rw [e, sub_self, zero_mul]; exact zero_mem _
  obtain ⟨h, hhN, hhH⟩ := mem_closure_iff.mp hmem N hN hxN
  obtain ⟨_, ⟨k, rfl⟩, d, hd, rfl⟩ := Subgroup.mem_sup.1 hhH
  have e1 : g1 (diagUnits E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E) := by
    show ((diagUnits E k * d : Ideles E) : AdeleRing (𝓞 E) E).2 = _
    rw [snd_mul_infConn _ _ hd, snd_diagUnits]
  have e2 : g2 (diagUnits E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) ((k⁻¹ : Eˣ) : E) := by
    show (((diagUnits E k * d)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 = _
    rw [mul_inv, ← map_inv, snd_mul_infConn _ _ (inv_mem hd), snd_diagUnits]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hhN
  refine ⟨k, fun v hv => ⟨?_, ?_⟩, ?_⟩
  · have this : ((g1 (diagUnits E k * d) - 1) * c) v ∈ v.adicCompletionIntegers E := h1 v hv
    have e : ((g1 (diagUnits E k * d) - 1) * c) v = algebraMap E (v.adicCompletion E) (((k : E) - 1) / (a : E)) := by
      rw [e1, div_eq_mul_inv, map_mul, map_sub, map_one]
      rfl
    rw [e] at this
    exact (mem_integers_iff v _).mp this
  · have this : g2 (diagUnits E k * d) v ∈ v.adicCompletionIntegers E := h2 v hv
    rw [e2] at this
    rw [← Units.val_inv_eq_inv_val]
    exact (mem_integers_iff v _).mp this
  · have e : g1 (diagUnits E k * d) w = algebraMap E (w.adicCompletion E) (k : E) := by
      rw [e1]; rfl
    have h3' : (g1 (diagUnits E k * d) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E := h3
    rw [e] at h3'
    exact le_of_mul_inv_mem w _ t ht h3'

end GlobalTheory.ArtinApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegmentStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsClassification_twist_multisegment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  first | exact @GlobalTheory.LocGL.isL_map_tw_of_isL | exact GlobalTheory.LocGL.isL_map_tw_of_isL | (intros; apply GlobalTheory.LocGL.isL_map_tw_of_isL <;> assumption)
end

