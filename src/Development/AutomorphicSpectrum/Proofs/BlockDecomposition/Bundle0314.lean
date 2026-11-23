module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralProdSubgroup
section
noncomputable section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotProduct

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂]
  [MeasurableMul₂ G₁] [MeasurableMul₂ G₂] {T₁ : Subgroup G₁} {T₂ : Subgroup G₂}
  {ν₁ : Measure T₁} [SFinite ν₁] {ν₂ : Measure T₂} [SFinite ν₂] {ν : Measure (T₁.prod T₂)}

def split (t : T₁.prod T₂) : T₁ × T₂ :=
  (⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩)

theorem measurable_split : Measurable (split : T₁.prod T₂ → T₁ × T₂) :=
  ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)

theorem lintegral_prod_subgroup (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : Measurable ρ) (g : G₁ × G₂) :
    ∫⁻ h : T₁.prod T₂, ρ ((h : G₁ × G₂) * g) ∂ν =
      ∫⁻ t₁ : T₁, ∫⁻ t₂ : T₂, ρ ((t₁ : G₁) * g.1, (t₂ : G₂) * g.2) ∂ν₂ ∂ν₁ := by
  have hm : Measurable fun p : T₁ × T₂ => ρ ((p.1 : G₁) * g.1, (p.2 : G₂) * g.2) :=
    hρ.comp ((((measurable_subtype_coe.comp measurable_fst).mul_const g.1)).prodMk
      ((measurable_subtype_coe.comp measurable_snd).mul_const g.2))
  rw [← lintegral_prod _ hm.aemeasurable, ← hν, lintegral_map hm measurable_split]
  rfl

theorem normaliser_fst (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₁ ν₁ fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₁ × T₂ => ρ (p.1, (p.2 : G₂)))
    (hρ.1.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))), fun g => ?_⟩
  have h := hρ.2 (g, 1)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  simpa using h

theorem normaliser_snd (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₂ ν₂ fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₂ × T₁ => ρ ((p.2 : G₁), p.1))
    (hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk measurable_fst)), fun g => ?_⟩
  have h := hρ.2 (1, g)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  rw [lintegral_lintegral_swap]
  · simpa using h
  · have hm : Measurable fun p : T₂ × T₁ => ρ ((p.2 : G₁), (p.1 : G₂) * g) :=
      hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk
        ((measurable_subtype_coe.comp measurable_fst).mul_const g))
    exact hm.aemeasurable

theorem normaliser_mul (hν : ν.map split = ν₁.prod ν₂) {ρ₁ : G₁ → ℝ≥0∞} {ρ₂ : G₂ → ℝ≥0∞}
    (h₁ : IsQuotNormaliser T₁ ν₁ ρ₁) (h₂ : IsQuotNormaliser T₂ ν₂ ρ₂) :
    IsQuotNormaliser (T₁.prod T₂) ν fun x => ρ₁ x.1 * ρ₂ x.2 := by
  have hm : Measurable fun x : G₁ × G₂ => ρ₁ x.1 * ρ₂ x.2 :=
    (h₁.1.comp measurable_fst).mul (h₂.1.comp measurable_snd)
  refine ⟨hm, fun g => ?_⟩
  rw [lintegral_prod_subgroup hν hm]
  have hc : ∀ t₁ : T₁, ∫⁻ t₂ : T₂, ρ₁ ((t₁ : G₁) * g.1) * ρ₂ ((t₂ : G₂) * g.2) ∂ν₂ =
      ρ₁ ((t₁ : G₁) * g.1) := fun t₁ => by
    have hm₂ : Measurable fun t₂ : T₂ => ρ₂ ((t₂ : G₂) * g.2) :=
      h₂.1.comp (measurable_subtype_coe.mul_const g.2)
    rw [lintegral_const_mul _ hm₂, h₂.2, mul_one]
  simp only [hc]
  exact h₁.2 g.1

end GlobalTheory.CompanionTheory.QuotProduct

namespace GlobalTheory.CompanionTheory.QuotProduct

theorem quotProd_holds : PositivityTheory.Rg.BcB.D4.QuotProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν₁ _ _ ν₂ _ _ ν _ _ F hF hν hinv hfib
  by_cases hex : ∃ ρ, IsQuotNormaliser (T₁.prod T₂) ν ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hν' : ν.map split = ν₁.prod ν₂ := hν
    have n₁ := normaliser_fst hν' hρ
    have n₂ := normaliser_snd hν' hρ
    have n := normaliser_mul hν' n₁ n₂
    set ρ₁ : G₁ → ℝ≥0∞ := fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂
    set ρ₂ : G₂ → ℝ≥0∞ := fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁
    rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hinv n]
    by_cases hi : Integrable (fun x : G₁ × G₂ => F x * (((ρ₁ x.1 * ρ₂ x.2).toReal : ℝ) : ℂ)) (μ₁.prod μ₂)
    · rw [integral_prod_symm _ hi]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      have hFx : Measurable fun x₁ => F (x₁, x₂) := hF.comp (measurable_id.prodMk measurable_const)
      have hinvx : ∀ h ∈ T₁, ∀ g, F (h * g, x₂) = F (g, x₂) := fun h hh g => by
        simpa using hinv (h, 1) (Subgroup.mem_prod.2 ⟨hh, T₂.one_mem⟩) (g, x₂)
      have hq := hfib x₂
      rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hFx hinvx n₁] at hq
      have : ∀ x₁, F (x₁, x₂) * (((ρ₁ x₁ * ρ₂ x₂).toReal : ℝ) : ℂ) =
          (F (x₁, x₂) * (((ρ₁ x₁).toReal : ℝ) : ℂ)) * (((ρ₂ x₂).toReal : ℝ) : ℂ) := fun x₁ => by
        rw [ENNReal.toReal_mul]; push_cast; ring
      simp only [this, Pi.zero_apply]
      rw [integral_mul_const, hq, zero_mul]
    · exact integral_undef hi
  · simp only [quotIntegral, dif_neg hex]

theorem quotProd_of_normEq : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.D4.QuotProd :=
  fun _ => quotProd_holds

end GlobalTheory.CompanionTheory.QuotProduct

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompatStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_derivation_compat : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan | exact GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfBadSetClosedFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.PSupp

lemma fromSpec_appTop_eq {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
  have h := hV.fromSpec_app_of_le ⊤ le_top
  have e : ∀ i : (⊤ : (Spec Γ(X, V)).Opens) ⟶ ⊤, (Spec Γ(X, V)).presheaf.map i.op = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]
    simp
  refine h.trans ?_
  erw [e, Category.comp_id]
  rfl

lemma fromSpec_comp_base {A : Type} [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {V : X.Opens}
    (hV : IsAffineOpen V) :
    hV.fromSpec ≫ (X ↘ Spec (.of A)) = Spec.map (CommRingCat.ofHom (toFunctions (A := A) V)) := by
  have key : (Scheme.ΓSpecIso (.of A)).inv ≫ (X ↘ Spec (.of A)).appTop ≫
      X.presheaf.map (homOfLE le_top).op = CommRingCat.ofHom (toFunctions (A := A) V) := by
    ext r
    rfl
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, fromSpec_appTop_eq,
    ← cancel_epi (Scheme.ΓSpecIso (.of A)).inv, ← Scheme.ΓSpecIso_inv_naturality, ← key]
  simp only [Category.assoc]
  rfl

lemma basicOpen_of_sub_one_mem {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V)
    (hI : I ≤ ((X ↘ Spec (.of A)).base x).asIdeal) {r : Γ(X, V)}
    (hr : r - 1 ∈ Ideal.map (toFunctions (A := A) V) I) : x ∈ X.basicOpen r := by
  set p := hV.primeIdealOf ⟨x, hxV⟩ with hp
  have hpx : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hcomp : (X ↘ Spec (.of A)).base x =
      (Spec.map (CommRingCat.ofHom (toFunctions (A := A) V))).base p := by
    rw [← fromSpec_comp_base hV, ← hpx]
    rfl
  have hle : Ideal.map (toFunctions (A := A) V) I ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have := hI ha
    rw [hcomp] at this
    exact this
  have hrp : r ∉ p.asIdeal := fun h => p.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.sub_mem h (hle hr)))
  rw [← hV.fromSpec_image_basicOpen r]
  exact ⟨p, hrp, hpx⟩

theorem mem_of_badSet_closedFibre : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, IsCoherent P → ∀ (Bb : Subobject P), (Bb : X.Modules).IsQuasicoherent → ∀ (K : Set X), IsClosed K → (∀ V : X.Opens, Disjoint (V : Set X) K → secs (Bb ⊔ powSub I P 1) V = Set.univ) → ∀ x ∈ GlobalTheory.CompanionTheory.GE.PSupp.badSet Bb, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ K := by
  intro A _ _ I X _ P hP Bb hBq K hK h x hx hI
  by_contra hxK
  obtain ⟨W, ⟨V, hV, rfl⟩, hxV, hVK⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ Kᶜ from hxK) hK.isOpen_compl
  have hV' : IsAffineOpen V := hV
  have hdisj : Disjoint (V : Set X) K := Set.disjoint_left.2 fun y hy hyK => hVK hy hyK
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  let N : Submodule Γ(X, V) Γ(P, V) :=
    { carrier := secs Bb V
      add_mem' := fun hx hy => GlobalTheory.CompanionTheory.GE.Comb.secs_add hx hy
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := fun r _ hx => GlobalTheory.CompanionTheory.GE.Comb.secs_smul r hx }
  have hsum : ∀ m : Γ(P, V), ∃ s ∈ N, ∃ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)), m = s + t := by
    intro m
    have hm : m ∈ secs (Bb ⊔ powSub I P 1) V := by rw [h V hdisj]; trivial
    rw [(GlobalTheory.T.quasicoherent_sup_sections hP.1 Bb (powSub I P 1) hBq (GlobalTheory.CompanionTheory.GE.Comb.qc_pow I hP.1 1)).2 V hV',
      GlobalTheory.T.ideal_power_subobject_sections I P hP.1 1 V hV', pow_one] at hm
    obtain ⟨s, hs, t, ht, rfl⟩ := hm
    exact ⟨s, hs, t, ht, rfl⟩
  haveI : Module.Finite Γ(X, V) Γ(P, V) := hP.2 V hV'
  have hfg : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)) ≤ J • ⊤ := by
    intro z _
    obtain ⟨m, rfl⟩ := N.mkQ_surjective z
    obtain ⟨s, hs, t, ht, rfl⟩ := hsum m
    have h1 : N.mkQ (s + t) = N.mkQ t := by
      have h0 : N.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero N).2 hs
      rw [map_add (f := _), h0, zero_add]
    rw [h1]
    have h2 : N.mkQ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)).map N.mkQ := ⟨t, ht, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
    exact h2
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤ hfg hle
  have hrN : ∀ m : Γ(P, V), r • m ∈ N := fun m => by
    have := hr (N.mkQ m) trivial
    rw [← map_smul] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this
  have hxD : x ∈ X.basicOpen r := basicOpen_of_sub_one_mem I hV' hxV hI hr1
  have hD : IsAffineOpen (X.basicOpen r) := hV'.basicOpen r
  refine hx ⟨X.basicOpen r, hD⟩ ?_ hxD
  refine Set.eq_univ_of_forall fun m => ?_
  haveI : P.IsQuasicoherent := hP.1
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq P hV' r m
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le r) r) := X.toRingedSpace.isUnit_res_basicOpen r
  obtain ⟨b, hb⟩ := hrN m'
  have h3 : resF P (X.basicOpen_le r) (r • m') ∈ secs Bb (X.basicOpen r) := by
    rw [← hb]
    exact ⟨resF _ (X.basicOpen_le r) b, (resF_app Bb.arrow (X.basicOpen_le r) b).symm⟩
  rw [resF_smul, hm', ← hu, smul_smul, ← pow_succ'] at h3
  have h4 := GlobalTheory.CompanionTheory.GE.Comb.secs_smul (((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) : Γ(X, X.basicOpen r)) ^ (e + 1)) h3
  rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h4

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.TorusCh

def IsPol {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop := ∃ f : K[X], e = aeval γ f

structure IsPrim {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop where
  pol : IsPol γ e
  idem : e * e = e
  ne : e ≠ 0
  inv : ∀ h : K[X], aeval γ h * e ≠ 0 → ∃ h' : K[X], aeval γ h' * (aeval γ h * e) = e

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  d.val * (X.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val

def rm (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (Ad E) := X.map (algebraMap E (Ad E))

def chi (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : Ad E := (1 + rm e * (t.val - 1)).det

def lam (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : ℝ := logAbs (chi e t)

section Pol

variable {K : Type} [Field K] {n : ℕ}

theorem pol_comm (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b) : a * b = b * a := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  rw [← map_mul, mul_comm, map_mul]

theorem isPol_iff (γ e : Matrix (Fin n) (Fin n) K) : IsPol γ e ↔ e ∈ Algebra.adjoin K {γ} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨fun ⟨f, h⟩ => ⟨f, h.symm⟩, fun ⟨f, h⟩ => ⟨f, h.symm⟩⟩

theorem img_of_pol (γ : GL (Fin n) K) (p : Matrix (Fin n) (Fin n) K) (hp : IsPol γ.val p) :
    img γ (LinearMap.range (Matrix.toLin' p)) = LinearMap.range (Matrix.toLin' p) := by
  have hc : γ.val * p = p * γ.val := pol_comm γ.val _ _ ⟨X, (aeval_X _).symm⟩ hp
  have hs : LinearMap.range (Matrix.toLin' γ.val) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨(γ⁻¹ : GL (Fin n) K).val *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  unfold img
  rw [← LinearMap.range_comp, ← Matrix.toLin'_mul, hc, Matrix.toLin'_mul, LinearMap.range_comp, hs, Submodule.map_top]

theorem mem_range_idem {a : Matrix (Fin n) (Fin n) K} (ha : a * a = a) (w : Fin n → K) :
    w ∈ LinearMap.range (Matrix.toLin' a) ↔ a *ᵥ w = w := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ha]
  · intro h
    exact ⟨w, by rw [Matrix.toLin'_apply, h]⟩

theorem mul_eq_of_range_le {a b : Matrix (Fin n) (Fin n) K} (hb : b * b = b)
    (h : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b)) : b * a = a := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  have h1 : a *ᵥ y ∈ LinearMap.range (Matrix.toLin' b) := h ⟨y, by rw [Matrix.toLin'_apply]⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact (mem_range_idem hb _).1 h1

theorem idem_facts (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b)
    (ha2 : a * a = a) (hb2 : b * b = b) :
    (LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) → a * b = a) ∧
    (LinearMap.range (Matrix.toLin' a) = LinearMap.range (Matrix.toLin' b) → a = b) ∧
    LinearMap.range (Matrix.toLin' (a * b)) =
      LinearMap.range (Matrix.toLin' a) ⊓ LinearMap.range (Matrix.toLin' b) := by
  have hc := pol_comm γ a b ha hb
  refine ⟨fun h => by rw [hc]; exact mul_eq_of_range_le hb2 h, fun h => ?_, ?_⟩
  · have h1 := mul_eq_of_range_le hb2 h.le
    have h2 := mul_eq_of_range_le ha2 h.ge
    rw [← h1, ← hc, h2]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      refine ⟨⟨b *ᵥ y, ?_⟩, ⟨a *ᵥ y, ?_⟩⟩
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc]
    · rintro w ⟨h1, h2⟩
      have h1' := (mem_range_idem ha2 w).1 h1
      have h2' := (mem_range_idem hb2 w).1 h2
      refine ⟨w, ?_⟩
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h2', h1']

end Pol

section Chi

theorem uu_mul {R : Type} [Ring R] (A t t' : R) (hA : A * A = A) (ht : t * A = A * t) :
    (1 + A * (t - 1)) * (1 + A * (t' - 1)) = 1 + A * (t * t' - 1) := by
  have h1 : (t - 1) * A = A * (t - 1) := by rw [sub_mul, mul_sub, ht, one_mul, mul_one]
  have h2 : A * (t - 1) * (A * (t' - 1)) = A * (t - 1) * (t' - 1) := by
    calc A * (t - 1) * (A * (t' - 1)) = A * ((t - 1) * A) * (t' - 1) := by simp only [mul_assoc]
      _ = (A * A) * (t - 1) * (t' - 1) := by rw [h1]; simp only [mul_assoc]
      _ = _ := by rw [hA]
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

theorem uu_add {R : Type} [Ring R] (A B x : R) (hAB : A * B = 0) (hx : x * B = B * x) :
    (1 + A * x) * (1 + B * x) = 1 + (A + B) * x := by
  have h2 : A * x * (B * x) = 0 := by
    calc A * x * (B * x) = A * (x * B) * x := by simp only [mul_assoc]
      _ = (A * B) * x * x := by rw [hx]; simp only [mul_assoc]
      _ = 0 := by rw [hAB]; simp
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_mul (a b : Matrix (Fin n) (Fin n) E) : rm (a * b) = rm a * rm b := Matrix.map_mul

theorem rm_add (a b : Matrix (Fin n) (Fin n) E) : rm (a + b) = rm a + rm b := by
  ext i j; simp [rm]

theorem rm_zero : rm (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j; simp [rm]

theorem comm_inv {e : Matrix (Fin n) (Fin n) E} {t : GA E n} (ht : t.val * rm e = rm e * t.val) :
    (t⁻¹ : GA E n).val * rm e = rm e * (t⁻¹ : GA E n).val := by
  calc (t⁻¹ : GA E n).val * rm e = (t⁻¹ : GA E n).val * (rm e * (t.val * (t⁻¹ : GA E n).val)) := by
        rw [Units.mul_inv, mul_one]
    _ = (t⁻¹ : GA E n).val * (t.val * rm e) * (t⁻¹ : GA E n).val := by
        rw [ht]; simp only [mul_assoc]
    _ = rm e * (t⁻¹ : GA E n).val := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem chi_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n)
    (ht : t.val * rm e = rm e * t.val) : chi e (t * t') = chi e t * chi e t' := by
  unfold chi
  rw [← Matrix.det_mul, uu_mul (rm e) t.val t'.val (by rw [← rm_mul, he]) ht, Units.val_mul]

theorem chi_one (e : Matrix (Fin n) (Fin n) E) : chi e (1 : GA E n) = 1 := by
  simp [chi]

theorem chi_isUnit (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n)
    (ht : t.val * rm e = rm e * t.val) : IsUnit (chi e t) :=
  IsUnit.of_mul_eq_one (chi e t⁻¹) (by rw [← chi_mul e he t _ ht, mul_inv_cancel, chi_one])

theorem lam_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n) (ht : t.val * rm e = rm e * t.val)
    (ht' : t'.val * rm e = rm e * t'.val) : lam e (t * t') = lam e t + lam e t' := by
  unfold lam
  rw [chi_mul e he t t' ht]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit e he t ht) (chi_isUnit e he t' ht')

theorem lam_inv (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t.val * rm e = rm e * t.val) :
    lam e t⁻¹ = - lam e t := by
  have h := lam_mul e he t t⁻¹ ht (comm_inv ht)
  have h0 : lam e (1 : GA E n) = 0 := by
    rw [lam, chi_one, ← map_one (algebraMap E (Ad E))]
    exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero
  rw [mul_inv_cancel, h0] at h
  linarith

theorem lam_zero (t : GA E n) : lam (0 : Matrix (Fin n) (Fin n) E) t = 0 := by
  have h1 : chi (0 : Matrix (Fin n) (Fin n) E) t = algebraMap E (Ad E) 1 := by
    simp [chi, rm_zero]
  rw [lam, h1]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero

theorem chi_add (a b : Matrix (Fin n) (Fin n) E) (hab : a * b = 0) (t : GA E n)
    (hb : t.val * rm b = rm b * t.val) : chi (a + b) t = chi a t * chi b t := by
  unfold chi
  have h1 : (t.val - 1) * rm b = rm b * (t.val - 1) := by rw [sub_mul, mul_sub, hb, one_mul, mul_one]
  rw [← Matrix.det_mul, uu_add (rm a) (rm b) _ (by rw [← rm_mul, hab, rm_zero]) h1, rm_add]

theorem lam_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) E) (hf : ∀ i ∈ s, f i * f i = f i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (t : GA E n) (ht : ∀ i ∈ s, t.val * rm (f i) = rm (f i) * t.val) :
    lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
  classical
  have key : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i ∧
      t.val * rm (∑ i ∈ s, f i) = rm (∑ i ∈ s, f i) * t.val ∧ lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
    induction s using Finset.induction_on with
    | empty => simp [rm_zero, lam_zero]
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (fun i hi => ht i (Finset.mem_insert_of_mem hi))
      have haa := hf a (Finset.mem_insert_self _ _)
      have hta := ht a (Finset.mem_insert_self _ _)
      have hl : f a * ∑ i ∈ s, f i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => ho a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      have hr : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun i hi => ho i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _)
          (fun h => ha (h ▸ hi))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨?_, ?_, ?_⟩
      · rw [add_mul, mul_add, mul_add, hl, hr, haa, h1]; simp
      · rw [rm_add, mul_add, add_mul, hta, h2]
      · unfold lam at h3 ⊢
        rw [chi_add _ _ hl t h2, GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit _ haa t hta) (chi_isUnit _ h1 t h2), h3]
  exact key.2.2

theorem lam_rat (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (r : GL (Fin n) E)
    (hr : (ratGL E n r).val * rm e = rm e * (ratGL E n r).val) : lam e (ratGL E n r) = 0 := by
  have h1 : chi e (ratGL E n r) = algebraMap E (Ad E) (1 + e * (r.val - 1)).det := by
    have : 1 + rm e * ((ratGL E n r).val - 1) = (1 + e * (r.val - 1)).map (algebraMap E (Ad E)) := by
      have h2 : (ratGL E n r).val = r.val.map (algebraMap E (Ad E)) := rfl
      rw [h2]
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [rm, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, apply_ite, map_sum]
    rw [chi, this]
    exact (RingHom.map_det _ _).symm
  have h2 := chi_isUnit e he _ hr
  rw [h1] at h2
  rw [lam, h1]
  refine GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap _ fun h0 => ?_
  rw [h0, map_zero] at h2
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact (h2.map (cV v)).ne_zero (map_zero _)

end Chi

end GlobalTheory.CompanionTheory.TorusCh

end
end

