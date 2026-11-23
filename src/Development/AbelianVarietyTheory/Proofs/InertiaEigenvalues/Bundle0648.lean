module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eig

theorem mem_of_fibres {X Q H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {g : X → H} {a : H}
    (hg : HasSum g a) (π : X → Q) (L : Submodule ℂ H) (hL : IsClosed (L : Set H))
    (h : ∀ x₀, ∃ s : Finset X, (∀ x, π x = π x₀ ↔ x ∈ s) ∧ ∑ x ∈ s, g x ∈ L) : a ∈ L := by
  have h1 := hg.tsum_fiberwise π
  refine hL.mem_of_tendsto h1 (Filter.Eventually.of_forall fun s => L.sum_mem fun c _ => ?_)
  by_cases hc : ∃ x₀, π x₀ = c
  · obtain ⟨x₀, rfl⟩ := hc
    obtain ⟨s, hs, hm⟩ := h x₀
    have e : π ⁻¹' {π x₀} = (s : Set X) := Set.ext fun x => hs x
    rw [e, Finset.tsum_subtype' s g]
    exact hm
  · have e : π ⁻¹' {c} = ((∅ : Finset X) : Set X) := Set.ext fun x => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hc ⟨x, hx⟩
    rw [e, Finset.tsum_subtype' ∅ g, Finset.sum_empty]
    exact L.zero_mem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isFinIdem_fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (Eu.fid D v) := by
  have h : ∃ f, IsFinIdem D v f := by
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
    exact ⟨_, ε, hε, rfl⟩
  unfold Eu.fid
  rw [dite_eq_left h]
  exact h.choose_spec

theorem exists_primeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) :
    ∃ P e, P.under (𝓞 D.host.F) = v ∧ IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hne⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv.over.symm
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨P, e, hP, h⟩

theorem primeIdem_of_under {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P.under (𝓞 D.host.F) = v) : ∃ e, IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨e, h⟩

variable {R : RealDat D A Ks} {i : Fin D.R.m}

theorem bop_spec (hTL : TransLaws R i) {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i)) (x y) :
    trPair R i γ x y = ⟪x, Eu.Bop R i γ y⟫_ℂ := by
  have hex := hTL.2.2.1 γ hγ
  unfold Eu.Bop
  rw [dite_eq_left hex]
  exact hex.choose_spec.2 x y

theorem bop_mul_lev (hLP : LevProd R i) (hTL : TransLaws R i) {γ k : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i))
    (hk : k ∈ levW R i) : Eu.Bop R i (γ * k) = Eu.Bop R i γ := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← bop_spec hTL hγ, ← bop_spec hTL (mul_mem hγ (hLP.1 hk))]
  have := hTL.2.2.2.1 γ hγ 1 (one_mem _) k hk x y
  rwa [one_mul] at this

theorem hecke_sum_good {F : Face D A} (hL : Laws R F) (hTL : TransLaws R i) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    (hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v) {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    ∃ z : ℂ, ∑ δ ∈ C, Eu.Bop R i δ y = z • y := by
  obtain ⟨y', hy', hs⟩ := hTL.2.1 v f hf α hα C hC hCR y
  have e1 : ∑ δ ∈ C, Eu.Bop R i δ y = y' := by
    apply ext_inner_left ℂ
    intro x
    rw [← hTL.2.2.2.2.2 x y', hs 1 (one_mem _) x, inner_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [one_mul, bop_spec hTL (hCR.1 δ hδ).1]
  obtain ⟨P, e, hPv, hP⟩ := exists_primeIdem hf
  obtain ⟨n, hβ⟩ := hL.lev.βW i
  obtain ⟨hJ, hχ, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ).2 P e f hP
    (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
    (by
      intro PP hPP
      have h1 : PP ∈ R.Pg := hPP.resolve_right (Finset.notMem_empty _)
      refine ⟨fun h => hv PP h1 (h ▸ hPv), fun h => hv PP h1 ?_⟩
      rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP] at hPv
      exact hPv)
  obtain ⟨-, ϖ, -, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have he : e * e = e := GlobalTheory.IdemSupport.delta_idem hΦ (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hP).1
  obtain ⟨d, hd, hD⟩ := GlobalTheory.SphLabelOps.exists_divAt (Wc D i) he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP) h1 h2 α
  have hop : Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) ∅ P d C :=
    ⟨e, f, ϖ, α, fun w hw => absurd hw (Finset.notMem_empty w), hP, h1, h2, hd, hJ, hχ, hα, hD, hC, hCR⟩
  have hm := (Submodule.mem_comap.1 hy).2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hm
  have hk := hm P d C hop
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hk
  refine ⟨c P d, e1.trans ((hL.models.HW i (sg0 D A)).1 ?_)⟩
  rw [hy', hk, map_smul]
  rfl

theorem hecke_sum_mem {F : Face D A} (hL : Laws R F) {t : T} (hB : BadSupp R i t) (hLP : LevProd R i)
    (hTL : TransLaws R i) {μ 𝓕} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    coef R i t μ 𝓕 α • ∑ δ ∈ C, Eu.Bop R i δ y ∈ Submodule.span ℂ {y} := by
  by_cases hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v
  · obtain ⟨z, hz⟩ := hecke_sum_good hL hTL hy hf hv hα hC hCR
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  · push_neg at hv
    obtain ⟨P, hP, hPv⟩ := hv
    obtain ⟨e, he⟩ := primeIdem_of_under hf hPv
    by_cases hk : α ∈ levW R i
    · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun δ hδ => ?_)
      obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hCR.1 δ hδ
      have := bop_mul_lev hLP hTL (one_mem _) (mul_mem (mul_mem hk₁.1 hk) hk₂.1)
      rw [one_mul] at this
      rw [this, Eu.bop_one hTL]
      exact Submodule.mem_span_singleton_self y
    · rw [hB μ 𝓕 hμ P (Or.inl hP) e f he α hα hk, zero_smul]
      exact Submodule.zero_mem _

theorem mk_eq_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (g : Eu.locSet R i v) (x : Eu.LX R i v) :
    (Quotient.mk _ g : Eu.LX R i v) = x ↔ g.1⁻¹ * Eu.rep x ∈ levW R i := by
  rw [← QuotientGroup.leftRel_apply]
  exact Quotient.mk_eq_iff_out


set_option maxHeartbeats 800000 in
theorem zop_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hB hLF _ hLP hTL μ 𝓕 hμ hleft c y hy v
  suffices h : Eu.Zop R i t μ 𝓕 v y ∈ Submodule.span ℂ {y} by
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨z, hz.symm⟩
  unfold Eu.Zop
  by_cases hs : Summable fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (Eu.rep x)
  swap
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Submodule.zero_mem _
  have hf := isFinIdem_fid D v
  obtain ⟨P, e, -, hP⟩ := exists_primeIdem hf
  have h0 := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).2.2.1 P e _ hP
  obtain ⟨S, hS⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).1 _ h0.1 h0.2.1).1
  have hloc : ∀ g, g ∈ S → g ∈ Eu.locSet R i v := fun g hg => ⟨h0.2.2.1 g ((hS g).1 hg), (hS g).1 hg⟩
  have hrep : ∀ x : Eu.LX R i v, Eu.rep x ∈ S := fun x => (hS _).2 (Quotient.out x).2.2
  have hsum := (ContinuousLinearMap.apply ℂ _ y).hasSum hs.hasSum
  refine mem_of_fibres hsum (fun x => DoubleCoset.mk (levW R i ⊓ S) (levW R i ⊓ S) (Eu.rep x)) _
    (Submodule.closed_of_finiteDimensional _) fun x₀ => ?_
  have hα : SuppF (Wc D i) (Eu.fid D v) (Eu.rep x₀) := (hS _).1 (hrep x₀)
  obtain ⟨C, hC, hCR⟩ := hTL.1 v _ hf _ hα
  have hK : ∀ k, k ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (Eu.fid D v) k} ↔ k ∈ levW R i ⊓ S := fun k =>
    and_congr_right fun _ => (hS k).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : GA D (Wc D i) → Eu.LX R i v, ∀ δ ∈ C, ∀ x, φ δ = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
    have key : ∀ δ : GA D (Wc D i), ∃ x' : Eu.LX R i v, δ ∈ C → ∀ x, x' = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
      intro δ
      by_cases hδ : δ ∈ C
      · have h1 := (hS δ).2 (hC δ hδ)
        exact ⟨Quotient.mk _ ⟨δ, hloc δ h1⟩, fun _ x =>
          (mk_eq_iff ⟨δ, hloc δ h1⟩ x).trans ⟨fun h => ⟨h, S.mul_mem (S.inv_mem h1) (hrep x)⟩, fun h => h.1⟩⟩
      · exact ⟨Eu.lx0 R i v, fun h => absurd h hδ⟩
    choose φ hφ using key
    exact ⟨φ, hφ⟩
  have hdc : ∀ δ ∈ C, ∃ k₁ ∈ levW R i ⊓ S, ∃ k₂ ∈ levW R i ⊓ S, Eu.rep (φ δ) = k₁ * Eu.rep x₀ * k₂ := fun δ hδ => by
    obtain ⟨-, k₁, hk₁, k₂, hk₂, e1⟩ := hCR.1 δ hδ
    refine ⟨k₁, (hK _).1 hk₁, k₂ * (δ⁻¹ * Eu.rep (φ δ)), mul_mem ((hK _).1 hk₂) ((hφ δ hδ _).1 rfl), ?_⟩
    rw [← mul_assoc, ← e1, mul_inv_cancel_left]
  refine ⟨C.image φ, fun x => ?_, ?_⟩
  · rw [eq_comm, DoubleCoset.eq, Finset.mem_image]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, e1⟩
      obtain ⟨δ, ⟨hδ, h1⟩, -⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact ⟨δ, hδ, (hφ δ hδ x).2 ((hK _).1 h1)⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact hdc δ hδ
  · rw [Finset.sum_image]
    · have := hecke_sum_mem hL hB hLP hTL hμ hy hf hα hC hCR
      rw [Finset.smul_sum] at this
      refine (congrArg (· ∈ Submodule.span ℂ {y}) (Finset.sum_congr rfl fun δ hδ => ?_)).mpr this
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      have e2 : Eu.acoef R i t μ 𝓕 v (φ δ) = coef R i t μ 𝓕 (Eu.rep x₀) := by
        unfold Eu.acoef
        rw [e1, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk₂.1, hleft _ hk₁.1]
      have e3 : Eu.Bop R i (Eu.rep (φ δ)) = Eu.Bop R i δ := by
        rw [← bop_mul_lev hLP hTL (hCR.1 δ hδ).1 ((hφ δ hδ _).1 rfl).1, mul_inv_cancel_left]
      rw [ContinuousLinearMap.apply_apply, e2, e3, ContinuousLinearMap.smul_apply]
    · intro δ hδ δ' hδ' h
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      obtain ⟨δ₀, -, hu⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact (hu δ ⟨hδ, (hK _).2 ((hφ δ hδ _).1 rfl)⟩).trans (hu δ' ⟨hδ', (hK _).2 ((hφ δ' hδ' _).1 h.symm)⟩).symm

end GlobalTheory.RawLift.Eig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletion
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TraceCompl

theorem le_one_iff_of_mul_eq_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (hab : a * b = 1)
    (hb : b ≤ 1) : a ≤ 1 ↔ b = 1 := by
  constructor
  · intro ha
    by_contra hb1
    have hlt : b < 1 := lt_of_le_of_ne hb hb1
    have : (1 : Γ) < 1 := calc
      (1 : Γ) = a * b := hab.symm
      _ ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ < 1 := hlt
    exact lt_irrefl _ this
  · rintro rfl
    rw [mul_one] at hab
    exact hab.le

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

theorem algebraMap_int_mem (A : ValuationSubring Ω) (x : 𝓞 K) : algebraMap K Ω x ∈ A := by
  have h1 : IsIntegral ℤ (algebraMap K Ω x) := x.2.map (algebraMap K Ω).toIntAlgHom
  have h2 : IsIntegral A (algebraMap K Ω x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hy ▸ y.2

theorem algebraMap_mem_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (x : K) : algebraMap K Ω x ∈ A ↔ v.valuation K x ≤ 1 := by
  have key : ∀ n : 𝓞 K, A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 ∧
      v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 ∧
      (A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔
        v.valuation K (algebraMap (𝓞 K) K n) = 1) := by
    intro n
    have h1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (algebraMap_int_mem A n)
    have h2 : v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 := v.valuation_le_one n
    have h3 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) < 1 ↔ n ∈ v.asIdeal := h n
    have h4 : v.valuation K (algebraMap (𝓞 K) K n) < 1 ↔ n ∈ v.asIdeal := v.valuation_lt_one_iff_mem n
    refine ⟨h1, h2, ?_⟩
    have e1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h3, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h1 e⟩
    have e2 : v.valuation K (algebraMap (𝓞 K) K n) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h4, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h2 e⟩
    exact e1.trans e2.symm
  obtain ⟨n, d, hd | hd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1, mul_one] at e1 e2
    rw [← A.valuation_le_one_iff, e1, e2]
    exact iff_of_true (key n).1 (key n).2.1
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1] at e1 e2
    rw [← A.valuation_le_one_iff, le_one_iff_of_mul_eq_one e1 (key n).1,
      le_one_iff_of_mul_eq_one e2 (key n).2.1]
    exact (key n).2.2

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem trace_mem {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (hL : IsLocalExt L h) (z : L) (hz : algebraMap L Ω z ∈ A) :
    algebraMap K Ω (Algebra.trace K L z) ∈ A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  rw [trace_eq_sum_embeddings Ω]
  refine sum_mem fun s _ => ?_
  obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
  have e : s z = (τ : G K Ω) (algebraMap L Ω z) := ((hτ z).trans (s.liftNormal_commutes Ω z)).symm
  rw [e]
  exact (apply_mem_iff_of_mem_Dec (Weil_le_Dec h τ.2) _).2 hz

theorem valuation_trace_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h)
    {c : K} (hc : c ≠ 0) {z : L} (hz : v'.valuation L z ≤ v'.valuation L (algebraMap K L c)) :
    v.valuation K (Algebra.trace K L z) ≤ v.valuation K c := by
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have h1 : v'.valuation L (z * (algebraMap K L c)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ hz zero_le'
  have h2 := trace_mem h hL _ ((algebraMap_mem_iff h' _).2 h1)
  rw [algebraMap_mem_iff h, ← map_inv₀, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
    map_mul, map_inv₀] at h2
  have hv : v.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  calc v.valuation K (Algebra.trace K L z)
      = (v.valuation K c)⁻¹ * v.valuation K (Algebra.trace K L z) * v.valuation K c := by
        rw [mul_comm _ (v.valuation K c), ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    _ ≤ 1 * v.valuation K c := by gcongr
    _ = v.valuation K c := one_mul _

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

open WithZero

variable (K : Type) {L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def traceMap (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) :
    WithVal (v'.valuation L) →+ v.adicCompletion K :=
  ((algebraMap K (v.adicCompletion K)).toAddMonoidHom.comp (Algebra.trace K L).toAddMonoidHom).comp
    (WithVal.equiv (v'.valuation L)).toAddMonoidHom

variable {K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  [IsScalarTower K L Ω]

theorem continuous_traceMap {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h) :
    Continuous (traceMap K v v') := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).2 γ.ne_zero
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt hc0
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0 : algebraMap (𝓞 K) K (π ^ n) ≠ 0 :=
    (_root_.map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (pow_ne_zero n hπ0)
  have hpv : v.valuation K (algebraMap (𝓞 K) K (π ^ n)) ≤ exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.pow_mem_pow hπ n
  have hd : v'.valuation L (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 hp0)
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 ((Valued.v : Valuation (WithVal (v'.valuation L)) ℤᵐ⁰).restrict
    (WithVal.toVal _ (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))))) ?_, fun z hz => hγ ?_⟩
  · simpa using hd
  · rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    have e : traceMap K v v' z = algebraMap K _ (Algebra.trace K L (WithVal.ofVal z)) := rfl
    rw [e, GlobalTheory.Idele.valued_algebraMap]
    exact (valuation_trace_le h h' hL hp0 hz.le).trans_lt (hpv.trans_lt hn)

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

theorem exists_trace_extension : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), IsLocalExt L h → ∃ T : v'.adicCompletion L →+ v.adicCompletion K, Continuous T ∧ ∀ z : L, T (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hL
  refine ⟨(AddMonoidHom.extension (traceMap K v v') (continuous_traceMap h h' hL)).comp
    (HeightOneSpectrum.adicCompletion.equiv L v').toAddMonoidHom, ?_, fun z => ?_⟩
  · exact (AddMonoidHom.continuous_extension _ (continuous_traceMap h h' hL)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v')
  · exact AddMonoidHom.extension_coe _ (continuous_traceMap h h' hL) (WithVal.toVal _ z)

end GlobalTheory.LocLanglands.TraceCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfFixedMemSpanTranslates
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.HeckeAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

theorem mem_conj {g : G} {t : K} :
    t ∈ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K ↔ g⁻¹ * (t : G) * g ∈ K := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, e⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem fix_eq {H : Subgroup K} {v : V} (hv : ∀ h ∈ H, ρ ((h : K) : G) v = v) {a b : K} (hab : (a : K ⧸ H) = b) :
    ρ (a : G) v = ρ (b : G) v := by
  have hm := QuotientGroup.eq.1 hab
  have : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
  rw [this, map_mul, Module.End.mul_apply, hv _ hm]

end GlobalTheory.HeckeAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVZpowDegEq
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem normV_zpow_deg_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (σ' : Weil h') (σ : Weil h) (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v' : ℕ) : ℝ) ^ deg σ' = ((normV v : ℕ) : ℝ) ^ deg σ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, ha⟩ := σ'.2
  obtain ⟨c, d, hc⟩ := σ.2
  rw [deg_eq ha, deg_eq hc]
  set q' := normV v' with hq'
  set q := normV v with hq
  have hq'0 : 0 < q' := (zero_lt_one.trans (one_lt_normV v'))
  have hq0 : 0 < q := (zero_lt_one.trans (one_lt_normV v))
  have key : ∀ x : Ω, A.valuation x ≤ 1 →
      A.valuation (x ^ (q' ^ a * q ^ d) - x ^ (q ^ c * q' ^ b)) < 1 := by
    intro x hx
    have hy : A.valuation ((σ' : G L Ω) x) ≤ 1 := val_apply_le_one ha.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (ha.2 x hx) (q ^ d)
    have h2' := hc.2 x hx
    rw [hσ] at h2'
    have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2' (q' ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h2
    rw [mul_comm (q ^ d) (q' ^ b)] at h2
    exact cong_trans (cong_symm h1) h2
  have hN : q' ^ a * q ^ d = q ^ c * q' ^ b := by
    rcases lt_trichotomy (q' ^ a * q ^ d) (q ^ c * q' ^ b) with hlt | heq | hgt
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq'0 a) (pow_pos hq0 d)) hlt
      exact absurd (cong_symm (key x hx)) hx'
    · exact heq
    · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A)
        (Nat.mul_pos (pow_pos hq0 c) (pow_pos hq'0 b)) hgt
      exact absurd (key x hx) hx'
  have hR : ((q' : ℕ) : ℝ) ^ a * ((q : ℕ) : ℝ) ^ d = ((q : ℕ) : ℝ) ^ c * ((q' : ℕ) : ℝ) ^ b := by
    exact_mod_cast hN
  have h1 : ((q' : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((q : ℕ) : ℝ) ≠ 0 := by positivity
  rw [zpow_sub₀ h1, zpow_sub₀ h2, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h2)]
  linarith

end GlobalTheory.LocLanglands

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands
end

