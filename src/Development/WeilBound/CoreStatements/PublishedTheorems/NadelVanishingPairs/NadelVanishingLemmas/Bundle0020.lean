module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLiftStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

private theorem unitAt_of_ord_eq_zero_coheight_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {v : X}
    (hv : Order.coheight v = 1) {h : X.functionField} (h0 : h ≠ 0)
    (hord : Scheme.ord h v = 0) : UnitAt v h := by
  haveI := hufd v
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk v) := krullDimLE_of_coheight_le hv.le
  by_cases hF : IsField (X.presheaf.stalk v)
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk v) h
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨b', hbb'⟩ := hF.mul_inv_cancel hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply h0
      rw [← hab, map_zero, zero_div]
    obtain ⟨a', haa'⟩ := hF.mul_inv_cancel ha0
    refine ⟨a * b', ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨a' * b, ?_⟩
      calc a * b' * (a' * b) = (a * a') * (b * b') := by ring
        _ = 1 := by rw [haa', hbb', one_mul]
    · rw [← hab, map_mul]
      have : algebraMap (X.presheaf.stalk v) X.functionField b *
          algebraMap (X.presheaf.stalk v) X.functionField b' = 1 := by
        rw [← map_mul, hbb', map_one]
      rw [eq_div_iff (fun h' => hb0 (IsFractionRing.injective (X.presheaf.stalk v) X.functionField
        (by rw [h', map_zero]))), mul_assoc, mul_comm _ (algebraMap _ _ b), this, mul_one]
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk v) := by
      have hmax : ∀ I : Ideal (X.presheaf.stalk v), I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
        Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance
      have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk v) ≠ ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hF
      have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk v) hF).out 4 1
      exact key.mp ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨hne, inferInstance⟩,
        fun P hP => IsLocalRing.eq_maximalIdeal (hmax P hP.1 hP.2)⟩⟩
    have h1 : Scheme.ordHom v hv h = 1 := by
      have := (Scheme.ord_eq_iff hv h0 (n := 0)).mp hord
      simpa using this
    have hmem : h ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk v) (K := X.functionField)) :=
      MonoidHom.mem_mker.mpr h1
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    exact ⟨a, ha, rfl⟩
private theorem Scheme_ord_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (v : X) :
    Scheme.ord (1 : X.functionField) v = 0 := by
  have h := Scheme.ord_mul (x := v) (one_ne_zero : (1 : X.functionField) ≠ 0) one_ne_zero
  rw [mul_one] at h
  omega

private theorem Scheme_ord_units_zpow {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (n : ℤ) (v : X) :
    Scheme.ord ((g ^ n : (X.functionField)ˣ) : X.functionField) v =
      n * Scheme.ord (g : X.functionField) v := by
  let φ : (X.functionField)ˣ →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd (Scheme.ord (a : X.functionField) v)
      map_one' := by simp [Scheme_ord_one]
      map_mul' := fun a b => by
        rw [Units.val_mul, Scheme.ord_mul a.ne_zero b.ne_zero, ofAdd_add] }
  have h := map_zpow φ g n
  have h2 := congrArg Multiplicative.toAdd h
  simpa [φ, toAdd_zpow, smul_eq_mul] using h2

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_open {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X} (U : X.Opens)
    (hy : y ∈ U) (h : (X.functionField)ˣ)
    (hord : ∀ v ∈ U, Scheme.ord (h : X.functionField) v = 0) : UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ, (∀ v ∈ U, Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z (hz.mem_open U.isOpen hy))).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv => by rw [Scheme_ord_units_inv, hord v hv, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩

private theorem exists_local_unit_ord_eq_finite_sum {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [DecidableEq X] (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (c : X → ℤ)
    (S : Finset X) (hS : ∀ z ∈ S, Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : (X.functionField)ˣ, ∀ v ∈ U,
      Scheme.ord (f : X.functionField) v = ∑ z ∈ S, if v = z then c z else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, 1, fun v _ => by simp [Scheme_ord_one]⟩
  | insert z S hzS ih =>
    obtain ⟨U1, hx1, f1, hf1⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
    obtain ⟨U2, hx2, π, hπ⟩ := PrimeDivCartier.exists_local_eqn X hufd z
      (hS z (Finset.mem_insert_self z S)) x
    refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, f1 * π ^ (c z), fun v hv => ?_⟩
    rw [Finset.sum_insert hzS, Units.val_mul, Scheme.ord_mul f1.ne_zero (π ^ c z).ne_zero,
      Scheme_ord_units_zpow, hf1 v hv.1, hπ v hv.2]
    split_ifs <;> simp [add_comm]

theorem _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ,
        (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) →
          ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  intro X _ _ hufd c hfin hc
  classical
  have hS : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 :=
    fun z hz => hc z (hfin.mem_toFinset.mp hz)
  have hsum : ∀ v, (∑ z ∈ hfin.toFinset, if v = z then c z else 0) = c v := by
    intro v
    rw [Finset.sum_ite_eq]
    split_ifs with hv
    · rfl
    · have : c v = 0 := by
        by_contra h'
        exact hv (hfin.mem_toFinset.mpr h')
      exact this.symm
  choose U hxU f hf using fun x => exists_local_unit_ord_eq_finite_sum hufd c hfin.toFinset hS x
  have hmem : (fun x => germOf x (f x)) ∈ cartierGroup X := by
    intro x
    refine ⟨U x, hxU x, f x, fun y hy => ?_⟩
    rw [germOf_eq_iff]
    have hu := unitAt_of_ord_eq_zero_on_open hufd (U x ⊓ U y) ⟨hy, hxU y⟩ (f x * (f y)⁻¹)
      (fun v hv => by
        rw [Units.val_mul, Scheme.ord_mul (f x).ne_zero ((f y)⁻¹).ne_zero, Scheme_ord_units_inv,
          hf x v hv.1, hf y v hv.2, add_neg_cancel])
    simpa [div_eq_mul_inv] using hu
  let D : CartierDiv X := (⟨fun x => germOf x (f x), hmem⟩ : cartierGroup X)
  refine ⟨D, fun z => ?_⟩
  have he : D.IsEqn z (f z) := rfl
  rw [he.mult_eq, hf z z (hxU z), hsum]
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionAtlasModP
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.LogAtlas

theorem fnOf_coord_ne_zero {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {U : X.Opens} (h : genericPoint X ∈ U) {n : ℕ} {t : Fin n → Γ(X, U)}
    (ht : IsEtCoord f U t) (j : Fin n) : fnOf U h (t j) ≠ 0 := by
  intro h0
  have h1 : t j = 0 := fnOf_injective U h (h0.trans (map_zero _).symm)
  letI := (MvPolynomial.eval₂Hom (cstOn f U) t).toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, U) := ht
  have : Nonempty U := ⟨⟨_, h⟩⟩
  have h2 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := R) j))
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin n) R) • (1 : Γ(X, U)) =
      (MvPolynomial.X j : MvPolynomial (Fin n) R) • (0 : Γ(X, U)) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact (MvPolynomial.eval₂Hom_X' _ _ j).trans h1
  exact one_ne_zero (h2 h3)

theorem exists_div_of_sec {X : Scheme.{0}} [IsIntegral X] {M : LB X} (hM : M.IsLB) (τ : M.Sec) (c₀ : M.ι)
    (h₀ : genericPoint X ∈ M.U c₀) (hτ : fnOf _ h₀ (τ.f c₀) ≠ 0) :
    ∃ E : CartierDiv X, toPic E = cls M hM ∧ ∀ (c : M.ι) (y : X) (hy : y ∈ M.U c)
      (g : X.functionFieldˣ), (g : X.functionField) = fnOf _ (gen_mem hy) (τ.f c) → E.IsEqn y g := by
  have P := presents_ofLB hM c₀ h₀
  have hr : P.rat τ ≠ 0 := fun e => hτ (by rw [← P.rat_mul τ c₀ h₀, e, zero_mul])
  have Q := P.add_principal (Units.mk0 _ hr)
  refine ⟨_, Q.toPic_eq, fun c y hy g hg => ?_⟩
  have e : g = frameRat M c₀ h₀ c * Units.mk0 _ hr := Units.ext (by
    rw [hg, ← P.rat_mul τ c (gen_mem hy), Units.val_mul, Units.val_mk0, mul_comm])
  exact e ▸ Q.isEqn c y hy

theorem exists_div_of_chart {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {d s : ℕ} {M : Fin s → LB X} (hM : ∀ i, (M i).IsLB) {τ : ∀ i, (M i).Sec}
    (C₀ : SncChart f d M τ) (h₀ : genericPoint X ∈ C₀.U) :
    ∃ E : Fin s → CartierDiv X, (∀ i, toPic (E i) = cls (M i) (hM i)) ∧
      ∀ (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (x : Fin d → X.functionFieldˣ),
        (∀ j, (x j : X.functionField) = fnOf C.U h (C.t j)) →
        ∀ i, ∀ y ∈ C.U, (E i).IsEqn y ((C.e i).elim 1 x) := by
  have key (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (i : Fin s) :
      fnOf _ (C.le i h) ((τ i).f (C.c i)) = fnOf C.U h (C.u i) * fnOf C.U h ((C.e i).elim 1 C.t) := by
    rw [← fnOf_resG (C.le i) h, C.eq i, map_mul]
  have H (i : Fin s) := exists_div_of_sec (hM i) (τ i) (C₀.c i) (C₀.le i h₀) (by
    rw [key C₀ h₀ i]
    refine mul_ne_zero (unitAt_fnOf h₀ h₀ _).ne_zero ?_
    rcases C₀.e i with _ | a
    · simp
    · exact fnOf_coord_ne_zero h₀ C₀.etale a)
  choose E hE hE' using H
  refine ⟨E, hE, fun C h x hx i y hy => ?_⟩
  have hu := unitAt_fnOf hy h (C.u i)
  have e : (((C.e i).elim 1 x : X.functionFieldˣ) : X.functionField) =
      fnOf C.U h ((C.e i).elim 1 C.t) := by
    rcases C.e i with _ | a
    · simp
    · exact hx a
  have h1 := hE' i (C.c i) y (C.le i hy) (Units.mk0 _ hu.ne_zero * (C.e i).elim 1 x) (by
    rw [Units.val_mul, Units.val_mk0, e]; exact (key C h i).symm)
  rw [h1.iff_unitAt, Units.val_mul, Units.val_mk0, div_mul_eq_div_div_swap, div_self (Units.ne_zero _),
    one_div]
  exact hu.inv

noncomputable def pullChart {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {X X' : Scheme.{0}}
    {f : X ⟶ Sp R} {f' : X' ⟶ Sp R'} {π : X' ⟶ X} (hP : IsPullback π f' f (spMap φ)) {d s : ℕ}
    {L : Fin s → LB X} {σ : ∀ i, (L i).Sec} (C : SncChart f d L σ) :
    SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) where
  U := π ⁻¹ᵁ C.U
  affine := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).1
  t := fun a => (π.app C.U).hom (C.t a)
  etale := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).2
  c := fun i => fun _ => C.c i
  le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
  e := C.e
  inj := C.inj
  u := fun i => Units.map (π.app C.U).hom (C.u i)
  eq := fun i => by
    show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
    rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
    rcases h : C.e i with _ | a
    · simp
    · simp

theorem exists_atlas_decomp : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∃ (m : ℕ) (E : Fin s → CartierDiv X) (𝒜 : SncAtlas E d (Fin m)), Decomp p 𝒜 ∧ ∀ i, toPic (E i) = CechPic.pull π (cls (L i) (h.isLB i)) := by
  classical
  intro p _ Y X _ g f π d _ hP hf hd s L σ h
  choose D hD using fun x : X => h.chart (π x)
  have hpr := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((π ⁻¹ᵁ (D x).U : X.Opens) : Set X))
    (fun x => (π ⁻¹ᵁ (D x).U).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hD x⟩)
  let ε := T.equivFin.symm
  let C : Fin T.card → SncChart g d L σ := fun k => D (ε k)
  have hgen (k) : genericPoint X ∈ (pullChart hP (C k)).U := gen_mem (x := ε k) (hD _)
  have hcov (y : X) : ∃ k, y ∈ (pullChart hP (C k)).U := by
    obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    obtain ⟨k, hk⟩ := ε.surjective ⟨z, hz⟩
    obtain rfl : (ε k : X) = z := congrArg Subtype.val hk
    exact ⟨k, hy⟩
  obtain ⟨k₀, -⟩ := hcov (genericPoint X)
  have : Nonempty (Fin T.card) := ⟨k₀⟩
  obtain ⟨E, hE, hE'⟩ := exists_div_of_chart (fun i => pull_isLB (h.isLB i) π) (pullChart hP (C k₀)) (hgen k₀)
  let x : Fin T.card → Fin d → X.functionFieldˣ := fun k j =>
    Units.mk0 _ (fnOf_coord_ne_zero (hgen k) (pullChart hP (C k)).etale j)
  let J : Fin T.card → Finset (Fin d) := fun k => Finset.univ.filter fun j => ∃ c, (C k).e c = some j
  have hJ (k j) : j ∈ J k ↔ ∃ c, (C k).e c = some j := by simp [J]
  have heq (k) := hE' (pullChart hP (C k)) (hgen k) (x k) (fun _ => rfl)
  have hlog (k) : IsLogChart (suppAll E) (pullChart hP (C k)).U (x k) (J k) := by
    refine GlobalTheory.T.etale_coordinates_log_chart p X f _ (hgen k) (pullChart hP (C k)).t (x k) (J k) _ (pullChart hP (C k)).affine
      (pullChart hP (C k)).etale (fun _ => rfl) fun y hy => ?_
    constructor
    · intro hy'
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hy'
      have h1 := (heq k c y hy).mem_supp_iff.1 hc
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField) at h1
      rcases he : (C k).e c with _ | a
      · rw [he] at h1
        exact (h1 (unitAt_one y)).elim
      · rw [he] at h1
        exact ⟨a, (hJ k a).2 ⟨c, he⟩, h1⟩
    · rintro ⟨j, hj, hu⟩
      obtain ⟨c, hc⟩ := (hJ k j).1 hj
      refine Set.mem_iUnion.2 ⟨c, (heq k c y hy).mem_supp_iff.2 ?_⟩
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField)
      rw [hc]
      exact hu
  let 𝒜 : SncAtlas E d (Fin T.card) :=
    { U := fun k => (pullChart hP (C k)).U
      x := x
      J := J
      affine := fun k => (pullChart hP (C k)).affine
      gen := hgen
      cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (hcov y)
      chart := hlog
      snc := fun k => ⟨(C k).e, (C k).inj, hJ k, heq k⟩ }
  have : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  refine ⟨T.card, E, 𝒜, GlobalTheory.T.frobenius_decomposition_of_lift p 𝒜 hd ?_, fun i => (hE i).trans (CechPic.cls_pull (h.isLB i) π _)⟩
  refine DI.isLifted_of_sncCharts p Y X g f π hP L σ h.isLB C _ _ (fun _ => le_rfl) hgen x J
    (fun k l => ?_) (fun k l => (hJ k l).1) hlog
  exact congrArg (fun ψ : Γ(Y, (C k).U) ⟶ Γ(X, π ⁻¹ᵁ (C k).U) => fnOf _ (hgen k) (ψ.hom ((C k).t l)))
    (π.app_eq_appLE)

end GlobalTheory.LogAtlas
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

noncomputable def DivOver.ordHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : X.functionFieldˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (E.ord f)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul]

theorem DivOver.ord_prod_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ) (e : ι → ℤ) :
    E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  have h := congrArg Multiplicative.toAdd (map_prod E.ordHom (fun j => f j ^ e j) s)
  rw [toAdd_prod] at h
  calc E.ord (∏ j ∈ s, f j ^ e j) = Multiplicative.toAdd (E.ordHom (∏ j ∈ s, f j ^ e j)) := rfl
    _ = ∑ j ∈ s, Multiplicative.toAdd (E.ordHom (f j ^ e j)) := h
    _ = ∑ j ∈ s, e j * E.ord (f j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

theorem DivOver.ord_eq_zero_of_unitAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {E : DivOver p} {x : X} (hE : E.Through x) (v : X.functionFieldˣ)
    (hv : UnitAt x (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, hav⟩ := hv
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, hav⟩
  have hinv : algebraMap (X.presheaf.stalk x) X.functionField (↑(ha.unit⁻¹)) =
      ((v⁻¹ : X.functionFieldˣ) : X.functionField) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hav, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := hE _ ⟨_, hinv⟩
  have e1 := (E.ord_nonneg_iff v).mpr h1
  have e2 := (E.ord_nonneg_iff v⁻¹).mpr h2
  rw [E.ord_inv] at e2
  omega

theorem coeff_criterion_snc : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  intro k _ _ Y _ _ q n _ η hη K G m B hm hK hsnc hsupp y g hG E hE
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hdim : topologicalKrullDim Y = n :=
    HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n inferInstance
  obtain ⟨U, hy, z, J, w, u, hc⟩ := exists_isSncChart k Y q n B hsnc y
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hfg := isFreeGen_formOf hgen hc.frame
  have hω0 : formOf U hgen (dOn q z) ≠ 0 := by
    intro h0
    have := hfg.1 (a₁ := 0) (a₂ := 1) (by simp only [h0, smul_zero])
    exact zero_ne_one this
  have hr : hfg.repr η ≠ 0 := by
    intro h0
    apply hη
    rw [← hfg.repr_smul η, h0, zero_smul]
  have hηh : η = ((Units.mk0 _ hr : Y.functionFieldˣ) : Y.functionField) • formOf U hgen (dOn q z) :=
    (hfg.repr_smul η).symm
  set h : Y.functionFieldˣ := Units.mk0 _ hr with hdef
  have hKy : K.IsEqn y h := hK U (dOn q z) hc.frame y hy h hηh
  have hD1 : (G - m • K).IsEqn y (g / h ^ m) := hG.sub (hKy.nsmul m)
  have hD2 := IsSncChart.isEqn_monomial k Y q n B y U hy z J w u hc (G - m • K) hsupp
  have hunit := (hD1.iff_unitAt).mp hD2
  have hzero := DivOver.ord_eq_zero_of_unitAt hE
    ((∏ j ∈ J, u j ^ (G - m • K).mult (w j)) / (g / h ^ m)) (by simpa using hunit)
  rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv,
    DivOver.ord_prod_zpow, E.ord_pow] at hzero
  have hform : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z)) := by
    rw [hηh]
    exact E.formOrd_smul hdim hω0 h
  have hF0 : 0 ≤ E.formOrd (formOf U hgen (dOn q z)) :=
    E.formOrd_formOf_nonneg hdim hy hE (dOn q z) hω0
  have hF1 := E.sum_ord_sub_one_le_formOrd_dOn hdim hy hE z hω0 (J := ↥J) (fun j => j.1)
    Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hF1
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).mpr (hE _ (by rw [hc.val j hj]; exact regAt_fnOf hy _ _))
  set F := E.formOrd (formOf U hgen (dOn q z)) with hFdef
  set S := ∑ j ∈ J, E.ord (u j) with hSdef
  change S - 1 ≤ F at hF1
  set T := ∑ j ∈ J, (G - m • K).mult (w j) * E.ord (u j) with hTdef
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hdisc : discrep E η m g = ((m * F - T : ℤ) : ℚ) / m := by
    have hg' : E.ord g = m * E.ord h + T := by linarith
    unfold discrep
    rw [hform, hg']
    push_cast
    field_simp
    ring
  rw [hdisc]
  constructor
  · intro hlt
    have hT : T ≤ (m - 1) * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have := hlt (w j) (hc.spec j hj)
      exact mul_le_mul_of_nonneg_right (by omega) (hnn j hj)
    have hS0 : 0 ≤ S := Finset.sum_nonneg hnn
    have key : -(m : ℤ) < m * F - T := by
      rcases eq_or_lt_of_le hS0 with hS | hS
      · rw [← hS] at hT
        have : (m : ℤ) * F ≥ 0 := mul_nonneg (by exact_mod_cast hm.le) hF0
        have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
        linarith
      · have : (m : ℤ) * (S - 1) ≤ m * F :=
          mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
        nlinarith
    rw [lt_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) < ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith
  · intro hle
    have hT : T ≤ m * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (hle (w j) (hc.spec j hj)) (hnn j hj)
    have key : -(m : ℤ) ≤ m * F - T := by
      have : (m : ℤ) * (S - 1) ≤ m * F :=
        mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
      nlinarith
    rw [le_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) ≤ ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundaryStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_effective_boundary : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  first | exact @_root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown | exact _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown | (intros; apply _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceStalkSncStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.regular_sequence_stalk_snc : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → (∀ x : X, IsClosed ({x} : Set X) → ∃ (n : ℕ) (t : Fin n → X.presheaf.stalk x) (c : ∀ i, (L i).ι) (hc : ∀ i, x ∈ (L i).U (c i)) (e : Fin s → Option (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧ ∀ i, Associated ((X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t)) → RelSnc f d L σ := by
  first | exact @_root_.GlobalTheory.RegParams.relSnc_of_regular_params | exact _root_.GlobalTheory.RegParams.relSnc_of_regular_params | (intros; apply _root_.GlobalTheory.RegParams.relSnc_of_regular_params <;> assumption)
end

