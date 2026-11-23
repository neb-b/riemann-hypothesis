module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMinpolyUniformizerWittTotallyRamified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TotRam

open IsLocalRing

variable {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O]

theorem isUnit_of_not_dvd_uniformiser {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {ϖ c : S} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ c) : IsUnit c := by
  by_contra hc
  have hm : c ∈ maximalIdeal S := (mem_maximalIdeal c).2 (mem_nonunits_iff.2 hc)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact h hm

theorem not_isUnit_algebraMap [Module.Finite R O] {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ IsUnit (algebraMap R O ϖ) := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hmem : ϖ ∈ maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  have hle : (⊤ : Submodule R O) ≤ maximalIdeal R • ⊤ := by
    intro x _
    have hx : x = ϖ • (v * x) := by rw [Algebra.smul_def, ← mul_assoc, hv, one_mul]
    rw [hx]
    exact Submodule.smul_mem_smul hmem trivial
  exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    (Module.finite_def.mp ‹_›) hle (maximalIdeal_le_jacobson _))

theorem dvd_coeff_of_dvd_sum {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : π ^ e ∣ algebraMap R O ϖ) (c : ℕ → R) {m j : ℕ} (hj : j < e) (hjm : j < m)
    (hlow : ∀ i < j, ϖ ∣ c i) (hs : π ^ (j + 1) ∣ ∑ i ∈ Finset.range m, c i • π ^ i) : ϖ ∣ c j := by
  by_contra hc
  have hu : IsUnit (algebraMap R O (c j)) := (isUnit_of_not_dvd_uniformiser hϖ hc).map _
  have hrest : π ^ (j + 1) ∣ ∑ i ∈ (Finset.range m).erase j, c i • π ^ i := by
    refine Finset.dvd_sum fun i hi => ?_
    rw [Algebra.smul_def]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · obtain ⟨d, hd⟩ := hlow i h
      refine Dvd.dvd.mul_right ((pow_dvd_pow π (by omega : j + 1 ≤ e)).trans (he.trans ?_)) _
      rw [hd, map_mul]; exact dvd_mul_right _ _
    · exact Dvd.dvd.mul_left (pow_dvd_pow π (by omega : j + 1 ≤ i)) _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hjm)] at hs
  have h1 : π ^ j * π ∣ π ^ j * algebraMap R O (c j) := by
    rw [← pow_succ, mul_comm, ← Algebra.smul_def]; exact (dvd_add_left hrest).1 hs
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)).1 h1
  exact hπ.not_isUnit (isUnit_of_dvd_unit h2 hu)

theorem dvd_coeff_all {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : π ^ e ∣ algebraMap R O ϖ) (c : ℕ → R) {m : ℕ}
    (hs : π ^ e ∣ ∑ i ∈ Finset.range m, c i • π ^ i) : ∀ j < e, j < m → ϖ ∣ c j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjm
    exact dvd_coeff_of_dvd_sum hπ hϖ he c hj hjm (fun i hi => ih i hi (by omega) (by omega))
      ((pow_dvd_pow π (by omega)).trans hs)

theorem coeff_eq_zero_of_sum {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (algebraMap R O)) {e : ℕ} (he : π ^ e ∣ algebraMap R O ϖ) :
    ∀ c : ℕ → R, ∑ i ∈ Finset.range e, c i • π ^ i = 0 → ∀ i < e, c i = 0 := by
  have hϖ0 : algebraMap R O ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ n : ℕ, ∀ c : ℕ → R, ∑ i ∈ Finset.range e, c i • π ^ i = 0 → ∀ i < e, ϖ ^ n ∣ c i := by
    intro n
    induction n with
    | zero => intro c _ i _; simp
    | succ n ih =>
      intro c hc i hi
      have hd := dvd_coeff_all hπ hϖ he c (m := e) (by rw [hc]; exact dvd_zero _)
      choose! d hd' using fun k (h : k < e) => hd k h h
      have h0 : algebraMap R O ϖ * ∑ k ∈ Finset.range e, d k • π ^ k = 0 := by
        rw [Finset.mul_sum, ← hc]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hd' k (Finset.mem_range.1 hk), Algebra.smul_def, Algebra.smul_def, map_mul]; ring
      have h1 := (mul_eq_zero.1 h0).resolve_left hϖ0
      rw [hd' i hi, pow_succ']
      exact mul_dvd_mul_left ϖ (ih d h1 i hi)
  intro c hc i hi
  by_contra h0
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  have h1 : ϖ ^ n * ϖ ∣ ϖ ^ n * 1 := by
    rw [← pow_succ, mul_one, ← hu]; exact (key (n + 1) c hc i hi).mul_right _
  exact hϖ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)).1 h1))

theorem exists_degreeLT [Module.Finite R O] {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : Associated (algebraMap R O ϖ) (π ^ e))
    (hres : ∀ x : O, ∃ c : R, ¬ IsUnit (x - algebraMap R O c)) :
    ∀ x : O, ∃ f ∈ Polynomial.degreeLT R e, Polynomial.aeval π f = x := by
  have step : ∀ k (x : O), ∃ f ∈ Polynomial.degreeLT R k, π ^ k ∣ x - Polynomial.aeval π f := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, Submodule.zero_mem _, by rw [pow_zero]; exact one_dvd _⟩
    | succ k ih =>
      intro x
      obtain ⟨f, hf, z, hz⟩ := ih x
      obtain ⟨c, hc⟩ := hres z
      have hm : z - algebraMap R O c ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hc)
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨t, ht⟩ := hm
      refine ⟨f + Polynomial.C c * Polynomial.X ^ k, ?_, t, ?_⟩
      · rw [Polynomial.mem_degreeLT] at hf ⊢
        have hk : ((k : ℕ) : WithBot ℕ) < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast k.lt_succ_self
        exact (Polynomial.degree_add_le _ _).trans_lt
          (max_lt (hf.trans hk) ((Polynomial.degree_C_mul_X_pow_le _ _).trans_lt hk))
      · simp only [map_add (f := _), map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
        rw [pow_succ, mul_assoc, ← ht]
        linear_combination hz
  have hmem : ϖ ∈ maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨v, hv⟩ := he.dvd
  let N : Submodule R O := (Polynomial.degreeLT R e).map (Polynomial.aeval π).toLinearMap
  have hle : (⊤ : Submodule R O) ≤ N ⊔ maximalIdeal R • ⊤ := by
    intro x _
    obtain ⟨f, hf, y, hy⟩ := step e x
    refine Submodule.mem_sup.2 ⟨Polynomial.aeval π f, Submodule.mem_map.2 ⟨f, hf, rfl⟩, ϖ • (v * y),
      Submodule.smul_mem_smul hmem trivial, ?_⟩
    rw [Algebra.smul_def]
    linear_combination -hy - y * hv
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›)
    (maximalIdeal_le_jacobson _) hle
  intro x
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (hN (Submodule.mem_top : x ∈ ⊤))
  exact ⟨f, hf, hfx⟩

theorem eisenstein_of_totallyRamified {ϖ : R} (hϖ : Irreducible ϖ) [Module.Finite R O]
    (hinj : Function.Injective (algebraMap R O))
    (hres : ∀ x : O, ∃ c : R, ¬ IsUnit (x - algebraMap R O c)) {π : O} (hπ : Irreducible π) :
    ∃ Ep : Polynomial R, Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, ϖ ∣ Ep.coeff i) ∧
      (∃ w : Rˣ, Ep.coeff 0 = ϖ * w) ∧ Polynomial.aeval π Ep = 0 ∧
      (∀ x : O, ∃ f : Polynomial R, Polynomial.aeval π f = x) ∧
      ∀ f : Polynomial R, Polynomial.aeval π f = 0 → Ep ∣ f := by
  have hϖ0 : algebraMap R O ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hϖ0 hπ
  have he0 : e ≠ 0 := by
    rintro rfl
    exact not_isUnit_algebraMap hϖ (he.isUnit_iff.2 (by simp))
  have hed : π ^ e ∣ algebraMap R O ϖ := he.symm.dvd
  have hspan := exists_degreeLT hπ hϖ he hres
  obtain ⟨g, hg, hgπ⟩ := hspan (π ^ e)
  have hgdeg : g.degree < e := Polynomial.mem_degreeLT.1 hg
  have hdeg : (Polynomial.X ^ e - g).degree = (e : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]; exact hgdeg
  have hmon : (Polynomial.X ^ e - g).Monic := Polynomial.monic_X_pow_sub hgdeg
  have hnat : (Polynomial.X ^ e - g).natDegree = e := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hroot : Polynomial.aeval π (Polynomial.X ^ e - g) = 0 := by simp [hgπ]
  have hsum : ∑ i ∈ Finset.range (e + 1), (Polynomial.X ^ e - g).coeff i • π ^ i = 0 := by
    have h := Polynomial.aeval_eq_sum_range (p := Polynomial.X ^ e - g) π
    rw [hnat] at h; rw [← h]; exact hroot
  have hdvd : ∀ i < e, ϖ ∣ (Polynomial.X ^ e - g).coeff i := fun i hi =>
    dvd_coeff_all hπ hϖ hed _ (by rw [hsum]; exact dvd_zero _) i hi (by omega)
  have hcoeffe : (Polynomial.X ^ e - g).coeff e = 1 := by
    have := hmon.coeff_natDegree; rwa [hnat] at this
  have hc0 : ∃ w : Rˣ, (Polynomial.X ^ e - g).coeff 0 = ϖ * w := by
    obtain ⟨w, hw⟩ := hdvd 0 (Nat.pos_of_ne_zero he0)
    by_cases hwu : ϖ ∣ w
    · exfalso
      obtain ⟨t, ht⟩ := hwu
      have hrest : π ^ (e + 1) ∣
          ∑ i ∈ (Finset.range (e + 1)).erase e, (Polynomial.X ^ e - g).coeff i • π ^ i := by
        refine Finset.dvd_sum fun i hi => ?_
        have hie : i < e := by
          have := Finset.mem_range.1 (Finset.mem_of_mem_erase hi); have := Finset.ne_of_mem_erase hi; omega
        rw [Algebra.smul_def]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [pow_zero, mul_one, hw, ht, map_mul, map_mul]
          refine (pow_dvd_pow π (by omega : e + 1 ≤ e + e)).trans ?_
          rw [pow_add]; exact mul_dvd_mul hed (hed.mul_right _)
        · obtain ⟨d, hd⟩ := hdvd i hie
          rw [hd, map_mul, pow_succ]
          exact mul_dvd_mul (hed.mul_right _) (dvd_pow_self π hi0.ne')
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.lt_succ_self e)), hcoeffe, one_smul] at hsum
      have h1 : π ^ e * π ∣ π ^ e * 1 := by
        rw [← pow_succ, mul_one]; exact (dvd_add_left hrest).1 (by rw [hsum]; exact dvd_zero _)
      exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero e hπ.ne_zero)).1 h1))
    · exact ⟨(isUnit_of_not_dvd_uniformiser hϖ hwu).unit, hw⟩
  have hmod : ∀ f : Polynomial R, Polynomial.aeval π f = 0 → (Polynomial.X ^ e - g) ∣ f := by
    intro f hf
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmon]
    have hr : Polynomial.aeval π (f %ₘ (Polynomial.X ^ e - g)) = 0 := by
      have h := congrArg (Polynomial.aeval π) (Polynomial.modByMonic_add_div f (Polynomial.X ^ e - g))
      rwa [map_add, map_mul, hroot, zero_mul, add_zero, hf] at h
    have hrdeg : (f %ₘ (Polynomial.X ^ e - g)).natDegree < e := by
      by_cases h0 : f %ₘ (Polynomial.X ^ e - g) = 0
      · rw [h0, Polynomial.natDegree_zero]; omega
      · rw [Polynomial.natDegree_lt_iff_degree_lt h0, ← hdeg]
        exact Polynomial.degree_modByMonic_lt f hmon
    have hs := Polynomial.aeval_eq_sum_range' hrdeg π
    rw [hr] at hs
    have hc := coeff_eq_zero_of_sum hπ hϖ hinj hed _ hs.symm
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < e
    · exact hc i hi
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  exact ⟨Polynomial.X ^ e - g, hmon, by rw [hnat]; omega, fun i hi => hdvd i (by rw [hnat] at hi; exact hi), hc0,
    hroot, fun x => (hspan x).imp fun f hf => hf.2, hmod⟩

theorem eisenstein_minpoly_Wq : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∀ π : O, Irreducible π → ∃ Ep : Polynomial (Wq l a), Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  intro l _ a _ O _ _ _ _ _ hinj hres π hπ
  exact eisenstein_of_totallyRamified (WittVector.irreducible l) hinj hres hπ

end GlobalTheory.TotRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfMemProKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.TameRead

open GlobalTheory.TameQuot

theorem eq_one_of_mem_proKer {I M : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [AddCommGroup M] {l : ℕ} [Fact l.Prime] {k : ℕ}
    (hM : ∀ m : M, (l ^ k) • m = 0) (θ : I →* Multiplicative M)
    (ho : IsOpen (θ.ker : Set I)) {σ : I} (hσ : σ ∈ proKer l I) : θ σ = 1 := by
  refine mem_proKer.1 hσ θ.ker inferInstance ho ?_
  have := Subgroup.quotient_finite_of_isOpen _ ho
  refine IsPGroup.iff_card.1 fun x => ⟨k, ?_⟩
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
  exact hM (θ τ).toAdd

theorem exists_gen_read : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∃ γ ∈ Ine (F := F) A, ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R (G F Ω) M) (k : ℕ), (∀ m : M, (l ^ k) • m = 0) → normV v ≡ 1 [MOD l ^ k] → (∀ σ ∈ Ine (F := F) A, ∀ m, rho σ m = m) → ∀ z : Z1 rho, (z.1 γ = 0 → ∀ σ ∈ Ine (F := F) A, z.1 σ = 0) ∧ ∀ φ : G F Ω, IsFrob A (normV v) φ → rho φ (z.1 γ) = z.1 γ := by
  intro hT F Ω _ _ _ _ _ l _ A v hA hl
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrel⟩ := hT F Ω l A v hA hl
  refine ⟨γ, hγ.1, ?_⟩
  intro R _ M _ _ _ _ rho k hM hq hI z
  have : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  let θ : Ine (F := F) A →* Multiplicative M :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
      have := z.2.2 (g : G F Ω) h
      rw [hI _ g.2] at this
      exact congrArg Multiplicative.ofAdd this
  have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
    (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
  have hJ : ∀ σ ∈ ineKer F A l, z.1 σ = 0 := fun σ hσ =>
    eq_one_of_mem_proKer hM θ ho (σ := ⟨σ, ineKer_le_Ine A l hσ⟩) (coe_mem_ineKer.1 hσ)
  refine ⟨fun h0 σ hσ => ?_, fun φ hφ => ?_⟩
  · have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ.1⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hJ τ hτ, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 hσ)
    exact hτ
  · have hc : φ * γ * φ⁻¹ ∈ Ine (F := F) A := conj_mem_Ine hφ.1 hγ.1
    have h1 := hJ _ (hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec A hγ.1⟩ hφ hγ).2.1
    have h2 : θ (((⟨γ, hγ.1⟩ : Ine (F := F) A) ^ normV v)⁻¹ * ⟨_, hc⟩) = 1 := h1
    rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h2
    have h3 : normV v • z.1 γ = z.1 (φ * γ * φ⁻¹) := congrArg Multiplicative.toAdd h2
    have h4 : normV v • z.1 γ = z.1 γ := by
      rw [← Nat.mod_add_div (normV v) (l ^ k), add_smul, mul_smul, hM, add_zero, hq]
      conv_rhs => rw [← one_smul ℕ (z.1 γ), ← Nat.mod_add_div 1 (l ^ k), add_smul, mul_smul, hM,
        add_zero]
    have h5 := z.2.2 (φ * γ * φ⁻¹) φ
    rw [hI _ hc, inv_mul_cancel_right, z.2.2 φ γ, ← h3, h4, add_comm] at h5
    exact add_right_cancel h5

end GlobalTheory.TameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfFrobeniusPeriodicMemDeRhamFilZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem fil_add_nat_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (a : ℤ) (k : ℕ) {x : P.R.BdR}
    (hx : x ∈ (P.PD (botExt l)).Fil (a + k)) : x ∈ (P.PD (botExt l)).Fil a := by
  induction k generalizing a with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    have h := (P.PD (botExt l)).Fil_anti (a + k)
    apply h
    have : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rwa [← this]

theorem no_fil_zero_neg_slope : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c →
    (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  intro l _ P AI T h d hh hd c hc hfil
  have hF : IsField P.R.BdR := GlobalTheory.RegularRing.isField_of_tied T
  have hι : Function.Injective P.ιB := fun a b hab => (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, hab])
  set PD := P.PD (botExt l) with hPD
  have hdom : ∀ a b : P.R.B, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    have h0 : P.ιB a * P.ιB b = 0 := by rw [← map_mul, hab, map_zero]
    by_cases ha : P.ιB a = 0
    · exact Or.inl (hι (by rw [ha, map_zero]))
    · right
      obtain ⟨y, hy⟩ := hF.mul_inv_cancel ha
      apply hι
      rw [map_zero]
      calc P.ιB b = (y * P.ιB a) * P.ιB b := by rw [mul_comm y, hy, one_mul]
        _ = 0 := by rw [mul_assoc, h0, mul_zero]
  haveI : NoZeroDivisors P.R.B := ⟨fun {a b} hab => hdom a b hab⟩
  haveI : Nontrivial P.R.B := nontrivial_B P
  by_contra hc0
  set N : P.R.B := ∏ j ∈ Finset.range h, P.φB^[j] c with hN
  have hφN : c * P.φB N = N * P.φB^[h] c := by
    have e1 : P.φB N = ∏ j ∈ Finset.range h, P.φB^[j + 1] c := by
      rw [hN, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Function.iterate_succ_apply']
    rw [e1, hN]
    have e2 := Finset.prod_range_succ' (fun j => P.φB^[j] c) h
    have e3 := Finset.prod_range_succ (fun j => P.φB^[j] c) h
    simp only [Function.iterate_zero, id] at e2
    rw [mul_comm c, ← e2, e3]
  have hlN : (l : P.R.B) ^ d * P.φB N = N := by
    have : c * ((l : P.R.B) ^ d * P.φB N - N) = 0 := by
      calc c * ((l : P.R.B) ^ d * P.φB N - N) = (l : P.R.B) ^ d * (c * P.φB N) - N * c := by ring
        _ = N * ((l : P.R.B) ^ d * P.φB^[h] c) - N * c := by rw [hφN]; ring
        _ = 0 := by rw [hc, sub_self]
    rcases hdom _ _ this with h1 | h1
    · exact absurd h1 hc0
    · exact sub_eq_zero.mp h1
  set x : P.R.B := N * P.tB ^ d with hx
  have hφx : PD.φ x = x := by
    rw [P.PD_φ, hx, map_mul, map_pow, localPrime_frobenius_periodT, Algebra.smul_def, map_natCast, mul_pow]
    linear_combination (P.tB ^ d) * hlN
  have hmul : ∀ (a b : ℤ) (u v : P.R.BdR), u ∈ PD.Fil a → v ∈ PD.Fil b → u * v ∈ PD.Fil (a + b) :=
    fun a b u v hu hv => PD.Fil_mul a b u v hu hv
  have hιN : P.ιB N ∈ PD.Fil 0 := by
    rw [hN, map_prod]
    refine Finset.prod_induction _ (fun u => u ∈ PD.Fil 0) (fun u v hu hv => by simpa using hmul 0 0 u v hu hv)
      (by simpa using PD.one_mem) fun j hj => ?_
    exact hfil j (Finset.mem_range.mp hj)
  have hιt : P.ιB P.tB ∈ PD.Fil 1 := by
    have := PD.mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have hιtd : ∀ k : ℕ, P.ιB (P.tB ^ k) ∈ PD.Fil k := by
    intro k
    induction k with
    | zero => simpa using PD.one_mem
    | succ k ih =>
      rw [pow_succ, map_mul]
      have := hmul k 1 _ _ ih hιt
      simpa using this
  have hιx1 : P.ιB x ∈ PD.Fil 1 := by
    have h1 : P.ιB x ∈ PD.Fil (0 + d) := by rw [hx, map_mul]; exact hmul 0 d _ _ hιN (hιtd d)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
    apply fil_add_nat_le P 1 k
    have : (1 : ℤ) + (k : ℤ) = 0 + (d : ℤ) := by rw [hk]; push_cast; ring
    rwa [this]
  have hιx0 : P.ιB x ∈ PD.Fil 0 := fil_add_nat_le P 0 1 (by simpa using hιx1)
  obtain ⟨q, hq⟩ := PD.fund x hφx (by rw [P.PD_ι]; exact hιx0)
  by_cases hq0 : q = 0
  · have hx0 : x = 0 := by rw [← hq, hq0, map_zero]
    have hN0 : N = 0 := by
      rcases hdom _ _ hx0 with h1 | h1
      · exact h1
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp h1) (isUnit_tB P).ne_zero
    rw [hN, Finset.prod_eq_zero_iff] at hN0
    obtain ⟨j, -, hj⟩ := hN0
    apply hc0
    apply (phiB_injective P).iterate j
    rw [hj, iterate_map_zero]
  · have hqx : P.ιB x = algebraMap ℚ_[l] P.R.BdR q := by rw [← hq, AlgHom.commutes]
    have hinv : algebraMap ℚ_[l] P.R.BdR q⁻¹ ∈ PD.Fil 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_of_tower_mem _ _ PD.one_mem
    have hone : algebraMap ℚ_[l] P.R.BdR q⁻¹ * P.ιB x = 1 := by
      rw [hqx, ← map_mul, inv_mul_cancel₀ hq0, map_one]
    have h2 : P.ιB P.tB ∈ PD.Fil 2 := by
      have := hmul 1 (0 + 1) _ _ hιt (hmul 0 1 _ _ hinv hιx1)
      rw [hone, mul_one] at this
      simpa using this
    have := PD.not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq] at this
    exact this h2

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEvalTeichmullerTilt
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal.Roots

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_roots (π : OC l) : ∃ s : ℕ → OC l, s 0 = π ∧ ∀ n, s (n + 1) ^ l = s n := by
  choose r hr using fun x : ℂ_[l] => IsAlgClosed.exists_pow_nat_eq x hl.out.pos
  have hn : ∀ x : ℂ_[l], ‖x‖ ≤ 1 → ‖r x‖ ≤ 1 := fun x hx => by
    have h := congrArg norm (hr x)
    rw [norm_pow] at h
    by_contra h1
    exact absurd (h ▸ one_lt_pow₀ (not_le.1 h1) hl.out.ne_zero) (not_lt.2 hx)
  let t : OC l → OC l := fun x => ⟨r x, (GlobalTheory.RingBasics.mem_OC _).2 (hn _ ((GlobalTheory.RingBasics.mem_OC _).1 x.2))⟩
  exact ⟨fun n => t^[n] π, rfl, fun n => by
    show (t^[n + 1] π) ^ l = t^[n] π
    rw [Function.iterate_succ_apply']
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hr _)⟩


variable {l} in
def flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (s n), fun n => by rw [← map_pow, hs]⟩ :
    Perfection (ModP (OC l) l) l)


variable {l} in
theorem untilt_flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : (flatOf s hs).untilt = s 0 := by
  have hp : ∀ n, s n ^ l ^ n = s 0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hs, ih]
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨s n, rfl, ?_⟩
  rw [hp]

end GlobalTheory.BKReal.Roots

namespace GlobalTheory.BKReal

theorem exists_ev_of_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (π : OC l), ¬ IsUnit π →
    ∃ (fl : OCb l) (ev : (Wq l a)⟦X⟧ →+* Ainf l), Per.θ l (WittVector.teichmuller l fl) = π ∧
      ev X = WittVector.teichmuller l fl ∧ (∀ w, ev (C w) = wA l a w) ∧
      ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x) := by
  intro l hl a _ π hπ
  obtain ⟨s, hs0, hs⟩ := Roots.exists_roots l π
  set fl := Roots.flatOf s hs
  set t : Ainf l := WittVector.teichmuller l fl
  have ht : Per.θ l t = π := (WittVector.fontaineTheta_teichmuller _).trans
    ((Roots.untilt_flatOf s hs).trans hs0)
  have htu : ¬ IsUnit t := fun h => hπ (ht ▸ h.map (Per.θ l))
  have hc : IsAdicComplete (Ideal.span {t}) (Ainf l) := (GlobalTheory.Per.AinfComplete.main l _ htu).2
  have hsep : ∀ x : Ainf l, (∀ n, t ^ n ∣ x) → x = 0 := fun x h =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)
  letI : Algebra (Wq l a) (Ainf l) := (wA l a).toRingHom.toAlgebra
  obtain ⟨f, hfX⟩ := GlobalTheory.Cyc.IoMap.algHom_exists (R := Wq l a) t
    (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) hsep
  have hfC : ∀ w, f.toRingHom (C w) = wA l a w := f.commutes
  have h1 : WittVector.frobenius t = t ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  refine ⟨fl, f.toRingHom, ht, hfX, hfC, fun x => ?_⟩
  refine RingHom.congr_fun (ringHom_ext_of_sep (f.toRingHom.comp (frobS l a))
    (WittVector.frobenius.comp f.toRingHom) (fun w => ?_) ?_ fun y hy => hsep y fun n => ?_) x
  · simp only [RingHom.comp_apply, frobS_C, hfC, wA_sigma]
  · simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX, h1]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX]
    exact pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n

end GlobalTheory.BKReal
end
end

