module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIterated
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.PeriodicIteratedIntegral

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem integral_fundamentalDomain_eq_iterated (Γ₁ : AddSubgroup V) [Countable Γ₁]
    (Γ : AddSubgroup (V × V)) (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (mW : MeasurableSpace (V × V)) (hmW : mW = Prod.instMeasurableSpace)
    (ν : @Measure (V × V) mW) (hν : @Measure.IsAddHaarMeasure _ _ _ mW ν)
    (𝓕 : Set (V × V)) (h𝓕 : @IsAddFundamentalDomain Γ _ _ _ mW 𝓕 ν)
    (𝓕₁ : Set V) (h𝓕₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) (hfin : μ 𝓕₁ ≠ ⊤) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : V × V → ℂ, @Measurable _ _ mW _ G →
      (∀ γ ∈ Γ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓕, G w ∂ν = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  subst hmW
  haveI := hν
  haveI : Countable Γ := by
    have hinj : Function.Injective (fun k : Γ =>
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁), (⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁))) := by
      intro k k' hk
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk
      exact Subtype.ext (Prod.ext hk.1 hk.2)
    exact hinj.countable
  have hmeq := Measure.isAddLeftInvariant_eq_smul ν (μ.prod μ)
  set c : NNReal := Measure.addHaarScalarFactor ν (μ.prod μ)
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (μ.prod μ)
  have hν' : ν = (c : ENNReal) • μ.prod μ := by
    rw [← ENNReal.smul_def]; exact hmeq
  refine ⟨(c : ℝ), by exact_mod_cast hcpos, fun G hG hper hB => ?_⟩
  obtain ⟨B, hB⟩ := hB
  open scoped Pointwise in
  have hprod : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) (μ.prod μ) := by
    refine ⟨h𝓕₁.nullMeasurableSet.prod h𝓕₁.nullMeasurableSet, ?_, ?_⟩
    · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h𝓕₁.ae_covers
      have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h𝓕₁.ae_covers
      filter_upwards [h1, h2] with p ha hb
      obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      exact ⟨⟨((a : V), (b : V)), (hΓ _).2 ⟨a.2, b.2⟩⟩, ha, hb⟩
    · intro g g' hne
      have hset : ∀ k : Γ, k +ᵥ (𝓕₁ ×ˢ 𝓕₁) =
          ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁) +ᵥ 𝓕₁) ×ˢ
            ((⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁) +ᵥ 𝓕₁) := by
        intro k
        ext ⟨x, y⟩
        simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod, AddSubgroup.vadd_def,
          AddSubgroup.coe_neg, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      show μ.prod μ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₁))) = 0
      rw [hset g, hset g', Set.prod_inter_prod, Measure.prod_prod]
      by_cases h1 : (g : V × V).1 = (g' : V × V).1
      · have h2 : (g : V × V).2 ≠ (g' : V × V).2 := by
          intro h2
          exact hne (Subtype.ext (Prod.ext h1 h2))
        have := h𝓕₁.aedisjoint (i := ⟨(g : V × V).2, ((hΓ _).1 g.2).2⟩)
          (j := ⟨(g' : V × V).2, ((hΓ _).1 g'.2).2⟩) (fun h' => h2 (congrArg Subtype.val h'))
        rw [show μ _ = 0 from this, mul_zero]
      · have := h𝓕₁.aedisjoint (i := ⟨(g : V × V).1, ((hΓ _).1 g.2).1⟩)
          (j := ⟨(g' : V × V).1, ((hΓ _).1 g'.2).1⟩) (fun h' => h1 (congrArg Subtype.val h'))
        rw [show μ _ = 0 from this, zero_mul]
  have hD : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) ν :=
    hprod.mono (by rw [hν']; exact Measure.smul_absolutelyContinuous)
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  have hint : Integrable G ((μ.restrict 𝓕₁).prod (μ.restrict 𝓕₁)) :=
    Integrable.of_bound hG.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  rw [h𝓕.setIntegral_eq hD (fun g x => hper g g.2 x), hν', Measure.restrict_smul,
    integral_smul_measure, ← Measure.prod_restrict, integral_prod _ hint, ENNReal.coe_toReal,
    Complex.real_smul]

end General

end GlobalTheory.PeriodicIteratedIntegral

namespace GlobalTheory.PeriodicIteratedIntegral

theorem integral_ratPair_fundamentalDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ (lam : MeasureTheory.Measure ((κ → AF F) × (κ → AF F))), lam.IsAddHaarMeasure →
    ∀ 𝓖 : Set ((κ → AF F) × (κ → AF F)),
      MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) 𝓖 lam →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ℂ, Measurable G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓖, G w ∂lam = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  intro F _ _ κ _ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ hfin
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.PeriodicIterated.countable_ratVec F κ
  haveI := hμ
  exact integral_fundamentalDomain_eq_iterated (GlobalTheory.ThetaParseval.ratVec F κ)
    (GlobalTheory.WeilUnitaryTransport.ratPair F κ) (GlobalTheory.PeriodicIterated.mem_ratPair_iff_ratVec F κ) μ (borel _)
    (Prod.borelSpace (α := κ → AF F) (β := κ → AF F)).measurable_eq.symm lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ hfin

end GlobalTheory.PeriodicIteratedIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.OmegaRank

theorem mem_pow_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
    x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem dual_dvd_iff {O : Type} [CommRing O] (p n : ℕ) (x : DualNumber O) :
    (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
  have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
    rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
  rw [e]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩

theorem isAdicComplete_dualNumber {O : Type} [CommRing O] (p : ℕ)
    [h : IsAdicComplete (Ideal.span {(p : O)}) O] :
    IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := {
  toIsHausdorff := ⟨fun x hx => by
    simp only [SModEq.zero, mem_pow_iff, dual_dvd_iff] at hx
    refine TrivSqZeroExt.ext (h.toIsHausdorff.haus x.fst fun n => ?_)
      (h.toIsHausdorff.haus x.snd fun n => ?_)
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).1
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).2⟩,
  toIsPrecomplete := ⟨fun f hf => by
    simp only [SModEq.sub_mem, mem_pow_iff, dual_dvd_iff] at hf ⊢
    obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec (f := fun n => (f n).fst) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).1
    obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec (f := fun n => (f n).snd) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).2
    simp only [SModEq.sub_mem, mem_pow_iff] at ha hb
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩⟩ }

theorem exists_param {O : Type} [CommRing O] [IsLocalRing O] (H : Over (Sp O)) [GrpObj H] {n : ℕ}
    (hH : SmoothOfRelativeDimension n H.hom) :
    ∃ e : (Fin n → O) ≃ LieG H, (∀ c d, (e (c + d)).1 = (e c).1 * (e d).1) ∧
      ∀ (a : O) c, (e (a • c)).1 = ptMap (dualScale a) ≫ (e c).1 := by
  obtain ⟨x, hx⟩ := KeyPow.exists_isUnivChart H hH
  refine ⟨⟨fun c => ⟨Chart.tvec (x := x) c, Chart.isTan_tvec hx c⟩, fun w => Chart.tcoord hx w.1 w.2,
    fun c => Chart.tcoord_tvec hx c, fun w => Subtype.ext (Chart.tcoord_spec hx w.1 w.2).symm⟩,
    fun c d => Chart.tvec_add hx c d, fun a c => Chart.tvec_smul hx a c⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem smoothDim_model : SmoothOfRelativeDimension P.A.g P.G.hom := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : ConnectedSpace P.G.left := GeometricallyConnected.connectedSpace P.G.hom P.G.hom.isOpenMap
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected P.G.hom (Classical.arbitrary _)
  have h₁ : SmoothOfRelativeDimension n P.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback P.gen_pull.1 hn
  rwa [← H1.dim_unique _ h₁ P.A.smoothDim (η[P.A.A].left (IsLocalRing.closedPoint C))]

section Lim

variable {R : Type} [CommRing R] [Algebra O R]


variable (p O R) in
abbrev redR (m : ℕ) : R →ₐ[O] R ⧸ Ideal.span {(p : R) ^ m} := Ideal.Quotient.mkₐ O _

omit [Fact p.Prime] in
theorem nilpR (m : ℕ) : IsNilpotent (p : R ⧸ Ideal.span {(p : R) ^ m}) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

omit [Fact p.Prime] in
theorem factor_redR (m : ℕ) : ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (p : R) (Nat.le_succ m)))) ≫ ptMap (redR p O R (m + 1)) = ptMap (redR p O R m) := by
  rw [TangentPow.ptMap_comp_ptMap]
  rfl

def Corr (x : specO O R ⟶ P.Gt) (y : specO O R ⟶ P.G) : Prop :=
  ∀ m, ptMap (redR p O R m) ≫ y = P.cmp _ (nilpR m) (ptMap (redR p O R m) ≫ x)

variable {P}

theorem Corr.mul {x x' : specO O R ⟶ P.Gt} {y y' : specO O R ⟶ P.G} (h : Corr P x y) (h' : Corr P x' y') :
    Corr P (x * x') (y * y') := fun m => by
  rw [MonObj.comp_mul, MonObj.comp_mul, map_mul, h, h']

theorem Corr.one : Corr P (1 : specO O R ⟶ P.Gt) 1 := fun m => by
  rw [MonObj.comp_one, MonObj.comp_one, map_one]

theorem Corr.comp {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') {x : specO O R ⟶ P.Gt}
    {y : specO O R ⟶ P.G} (h : Corr P x y) : Corr P (ptMap φ ≫ x) (ptMap φ ≫ y) := fun m => by
  let ψ : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' ⧸ Ideal.span {(p : R') ^ m} :=
    Ideal.quotientMapₐ _ φ (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have e : ptMap (redR p O R' m) ≫ ptMap φ = ptMap ψ ≫ ptMap (redR p O R m) := by
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap]
    rfl
  rw [← Category.assoc, ← Category.assoc, e, Category.assoc, Category.assoc, h,
    P.cmp_nat _ _ (nilpR m) (nilpR m)]

variable [IsLocalRing R] (hp : ¬ IsUnit (p : R)) (hc : IsAdicComplete (Ideal.span {(p : R)}) R)
include hp hc

theorem existsUnique_right (x : specO O R ⟶ P.Gt) : ∃! y, Corr P x y :=
  AdicPt.existsUnique_lim O R (p : R) hp hc P.G _
    fun m => by rw [← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), ← Category.assoc, factor_redR]

theorem existsUnique_left (y : specO O R ⟶ P.G) : ∃! x, Corr P x y := by
  have h := AdicPt.existsUnique_lim O R (p : R) hp hc P.Gt
    (fun m => (P.cmp _ (nilpR m)).symm (ptMap (redR p O R m) ≫ y)) fun m =>
      (P.cmp _ (nilpR m)).injective (by
        rw [P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, ← Category.assoc, factor_redR])
  obtain ⟨x, hx, hu⟩ := h
  refine ⟨x, fun m => by rw [hx, MulEquiv.apply_symm_apply], fun x' hx' => hu x' fun m => ?_⟩
  rw [hx' m, MulEquiv.symm_apply_apply]

end Lim

theorem exists_lieEquiv [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃ e : LieG P.G ≃ LieG P.Gt, (∀ x y z : LieG P.G, z.1 = x.1 * y.1 → (e z).1 = (e x).1 * (e y).1) ∧
      ∀ (a : O) (x z : LieG P.G), z.1 = ptMap (dualScale a) ≫ x.1 →
        (e z).1 = ptMap (dualScale a) ≫ (e x).1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hc := isAdicComplete_dualNumber (O := O) p
  have hl := existsUnique_left (P := P) hp hc
  have hr := existsUnique_right (P := P) hp hc
  let f : LieG P.G → LieG P.Gt := fun y => ⟨(hl y.1).choose,
    (existsUnique_left (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hl y.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [y.2] at h
        exact h) Corr.one⟩
  let g : LieG P.Gt → LieG P.G := fun x => ⟨(hr x.1).choose,
    (existsUnique_right (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hr x.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [x.2] at h
        exact h) Corr.one⟩
  have hf : ∀ y, Corr P (f y).1 y.1 := fun y => (hl y.1).choose_spec.1
  have hg : ∀ x, Corr P x.1 (g x).1 := fun x => (hr x.1).choose_spec.1
  refine ⟨⟨f, g, fun y => Subtype.ext ((hr _).unique (hg _) (hf y)),
    fun x => Subtype.ext ((hl _).unique (hf _) (hg x))⟩, fun x y z h => ?_, fun a x z h => ?_⟩
  · exact (hl _).unique (hf z) (h ▸ (hf x).mul (hf y))
  · exact (hl _).unique (hf z) (h ▸ (hf x).comp (dualScale a))

end GlobalTheory.HTLat.OmegaRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsogFiniteFlat

open GlobalTheory.UnramifiedEndFlat GlobalTheory.FiniteEndFlat

theorem apply_genericPoint_of_comp {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (g : Y ⟶ X) [LocallyQuasiFinite g]
    (h : g (f (genericPoint X)) = genericPoint X) : f (genericPoint X) = genericPoint Y := by
  have hs := strictMono_of_locallyQuasiFinite g
  have h1 : genericPoint Y ⤳ f (genericPoint X) := genericPoint_specializes _
  have h2 : g (genericPoint Y) ⤳ genericPoint X := by
    rw [← h]; exact h1.map g.continuous
  have h3 : g (genericPoint Y) = genericPoint X :=
    (h2.antisymm (genericPoint_specializes _)).eq
  by_contra hne
  have hlt : f (genericPoint X) < genericPoint Y := lt_of_le_not_ge h1 fun h' =>
    hne (h1.antisymm (show f (genericPoint X) ⤳ genericPoint Y from h')).eq.symm
  have := hs hlt
  rw [h3, h] at this
  exact lt_irrefl _ this

theorem flat_of_isFinite_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj G'] [IsIntegral G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') (φ' : G' ⟶ G)
    [IsMonHom φ] [IsMonHom φ'] [IsFinite φ.left] [IsFinite φ'.left] :
    Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : (φ.left ≫ φ'.left) o = o := by
    have : η[G] ≫ (φ ≫ φ') = η[G] := IsMonHom.one_hom (φ ≫ φ')
    rw [← Over.comp_left]
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ0 := apply_genericPoint (φ.left ≫ φ'.left) hfo
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left :=
    apply_genericPoint_of_comp φ.left φ'.left (by simpa using hξ0)
  obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

end GlobalTheory.IsogFiniteFlat

namespace GlobalTheory.IsogFiniteFlat

theorem isFinite_and_flat_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A]
    [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c →
      ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  intro S _ A A' _ _ _ _ hA hA' ψ ψ' c hc _ _ h1 h2
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hc
  obtain ⟨hfA, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA c hc1
  obtain ⟨hfA', -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A' hA' c hc1
  have := hA.proper
  have := hA.smooth
  have := hA'.proper
  have := hA'.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp _ A.hom
  haveI : IsSeparated (ψ.left ≫ A'.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ.left := IsSeparated.of_comp _ A'.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact hfA
  haveI : IsFinite (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hfA'
  have hf : IsFinite ψ.left := IsFinite.of_comp _ ψ'.left
  have hf' : IsFinite ψ'.left := IsFinite.of_comp _ ψ.left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A' ψ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hB' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A' hA'
  have := hB.smooth
  have := hB'.smooth
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A).hom hB.smooth hB.geomConnected
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A').hom hB'.smooth hB'.geomConnected
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj A').left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A').hom
  haveI : IsFinite ((Over.pullback t).map ψ).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ) hf
  haveI : IsFinite ((Over.pullback t).map ψ').left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ') hf'
  exact flat_of_isFinite_grpHom K _ _ ((Over.pullback t).map ψ) ((Over.pullback t).map ψ')

end GlobalTheory.IsogFiniteFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyDegreeKilledByPrimeToPHarrisTaylor
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel.PrimeToP

theorem isIsogDeg_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), (∀ c : 𝓞 D.F, c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n))) → ∀ (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (K : Over S) (i : K ⟶ o.A), Mono i → (∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o _hdeg 𝔟 h𝔟 K i hi hK
  obtain ⟨K', i', hi', hfin, het, hK'⟩ := GlobalTheory.T.killed_by_ideal_finite_etale p D R b N S s o 𝔟 h𝔟
  have hne : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [bot_sup_eq] at h𝔟
    have h1 := congrArg Ideal.absNorm h𝔟
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have h2 : Algebra.norm ℤ ((p : ℤ) : 𝓞 D.F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 D.F) := by
      rw [← Algebra.norm_algebraMap]; rfl
    rw [Int.cast_natCast] at h2
    rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hp := (Fact.out : p.Prime).one_lt
    have hr : 0 < Module.finrank ℤ (𝓞 D.F) := Module.finrank_pos
    have := Nat.one_lt_pow hr.ne' hp
    omega
  have hd : 1 ≤ Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)))
  obtain ⟨u, hu⟩ : GlobalTheory.IwLevel.InSub i' i := (hK' K i).2 ((hK K i).1 ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨v, hv⟩ : GlobalTheory.IwLevel.InSub i i' := (hK K' i').2 ((hK' K' i').1 ⟨𝟙 _, Category.id_comp _⟩)
  have : IsIso u := ⟨⟨v, by rw [← cancel_mono i, Category.assoc, hv, hu, Category.id_comp],
    by rw [← cancel_mono i', Category.assoc, hu, hv, Category.id_comp]⟩⟩
  have h3 := GlobalTheory.T.isogeny_degree_of_point_count o.A K' i' hi' hfin het _ hd fun k _ _ t => by
    rw [← GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow p D R b N S s o 𝔟 h𝔟 k t]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => hK' _ y)
  have h4 := (GlobalTheory.IwLevel.IsIsogDeg.of_isIso u).comp h3
  rwa [_root_.one_mul, toUnit_unique (u ≫ toUnit K') (toUnit K)] at h4

end GlobalTheory.IwLevel.PrimeToP
end

