module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalModularFormCuspForm
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.FinDim

open Asymptotics Filter Topology Function

theorem bigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (hc : ∀ n < m, (qExpansion h f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam h τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := hc i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty hh
  have h2 : (fun τ : ℍ => g (Periodic.qParam h τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam h τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne'] at hτ
  rw [hτ]; simp

theorem coeff_eq_zero_of_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

theorem qParam_pow_bigO {h : ℝ} (hh : 0 < h) {m M : ℕ} (hm : (M : ℝ) * h ≤ m) :
    (fun τ : ℍ => Periodic.qParam h τ ^ m) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ M := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [one_mul, norm_pow, norm_pow, Periodic.norm_qParam, Periodic.norm_qParam, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul, Real.exp_le_exp]
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have key : (M : ℝ) * (τ : ℂ).im ≤ m * (τ : ℂ).im / h := by
    rw [le_div_iff₀ hh]; nlinarith
  have e1 : (m : ℝ) * (-2 * Real.pi * (τ : ℂ).im / h) = -2 * Real.pi * (m * (τ : ℂ).im / h) := by ring
  have e2 : (M : ℝ) * (-2 * Real.pi * (τ : ℂ).im / 1) = -2 * Real.pi * (M * (τ : ℂ).im) := by ring
  rw [e1, e2]
  nlinarith [Real.pi_pos]

theorem norm_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))
  have hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ),
      SlashInvariantForm.quotientFunc (k := k) f q =O[atImInfty] fun _ => (1 : ℂ) := by
    refine Quotient.forall.mpr fun ⟨r, hr⟩ => ?_
    have hc : IsCusp OnePoint.infty 𝒮ℒ := Fact.out
    have := (ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty)
      (by simpa using hc.of_isFiniteRelIndex_conj hr)
    rw [OnePoint.isBoundedAt_infty_iff] at this
    have h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ) := this
    refine IsBigO.trans h2 ?_
    exact IsBigO.of_bound 1 (by simp)
  have h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)),
      SlashInvariantForm.quotientFunc (k := k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by
    have := IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)
    simpa [Finset.prod_fn] using this
  have h2 := (isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1
  simp only [mul_one] at h2
  refine h2.congr_left fun τ => ?_
  have h3 := congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q)
    (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ
  rw [ModularForm.coe_norm]
  have h4 : SlashInvariantForm.quotientFunc (k := k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp
  rw [h4, Pi.mul_apply] at h3
  convert h3

theorem sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion h f).coeff n = 0) → f = 0 := by
  set M := (k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1
  refine ⟨⌈(M : ℝ) * h⌉₊, fun f hf => ?_⟩
  have h1 := coeff_eq_zero_of_bigO one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) M
    ((norm_bigO f).trans ((bigO_qParam_pow hh hΓ f _ hf).trans (qParam_pow_bigO hh (Nat.le_ceil _))))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

def coeffMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)
    (m : ℕ) : ModularForm Γ k →ₗ[ℂ] (Fin m → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    funext n
    simp only [Pi.add_apply]
    rw [ModularForm.coe_add, ModularForm.qExpansion_add hh hΓ f g, map_add (f := _)]
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [ModularForm.coe_smul, ModularForm.qExpansion_smul hh hΓ c f, PowerSeries.coeff_smul, smul_eq_mul]

theorem finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne]
    (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  obtain ⟨m, hm⟩ := sturm Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k
  refine Module.Finite.of_injective (coeffMap Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k m) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  exact hm f fun n hn => congr_fun hf ⟨n, hn⟩

end GlobalTheory.HeckeFamilyMatrices.FinDim


open GlobalTheory.HeckeFamilyMatrices.FinDim in
theorem GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm :
    ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro Γ k hΓ
  have h1 := finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) k
  refine ⟨h1, ?_⟩
  haveI := h1
  exact Module.Finite.equiv (CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAdd
section
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def rightDefect (ρ : G → E →ₗ[ℂ] E) (t : G) : (G → E) →ₗ[ℂ] (G → E) where
  toFun u := fun x => u (x * t) - ρ t (u x)
  map_add' u v := by
    funext x
    simp only [Pi.add_apply, map_add (f := _)]
    abel
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

theorem rightDefect_apply (ρ : G → E →ₗ[ℂ] E) (t : G) (u : G → E) (x : G) :
    rightDefect ρ t u x = u (x * t) - ρ t (u x) := rfl

theorem rightDefect_mem_relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hst : s ^ 2 = t ^ 3) (u : G → E)
    (hu : u ∈ extn Γ ρ s) : rightDefect ρ t u ∈ relThree Γ ρ t := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨ha, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have ha' : ∀ γ ∈ Γ, ∀ x, u (γ * x) = u x + ρ x (u γ - u 1) := by
    intro γ hγ x
    rw [← ha γ hγ x]
    abel
  have hs2 : ∀ x, u (x * t ^ 3) = ρ (t ^ 3) (u x) := by
    intro x
    rw [← hst, pow_two, ← mul_assoc, hb, hb, hρc]
  have p2 : t * t = t ^ 2 := (pow_two t).symm
  have p3 : t ^ 2 * t = t ^ 3 := (pow_succ t 2).symm
  have p3' : t * t ^ 2 = t ^ 3 := (pow_succ' t 2).symm
  simp only [relThree, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, rightDefect_apply]
  refine ⟨?_, ?_⟩
  · show (∀ h ∈ Γ, ∀ g : G, rightDefect ρ t u (h * g) = rightDefect ρ t u g) ∧
      ∀ g : G, rightDefect ρ t u (g * t ^ 3) = ρ (t ^ 3) (rightDefect ρ t u g)
    simp only [rightDefect_apply]
    refine ⟨?_, ?_⟩
    · intro h hh g
      rw [mul_assoc, ha' h hh (g * t), ha' h hh g, map_add (f := _), hρc]
      abel
    · intro g
      have e : g * t ^ 3 * t = g * t * t ^ 3 := by
        rw [mul_assoc, mul_assoc, (Commute.self_pow t 3).eq]
      rw [e, hs2, hs2, map_sub, hρc, hρc, (Commute.self_pow t 3).eq]
  · intro x
    have e1 : x * t * t = x * t ^ 2 := by rw [mul_assoc, p2]
    have e2 : x * t ^ 2 * t = x * t ^ 3 := by rw [mul_assoc, p3]
    rw [e1, e2, hs2, map_sub, map_sub, hρc, hρc, p3', p2]
    abel

theorem eq_zero_of_rightDefect_eq_zero (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (u : G → E)
    (hu : u ∈ extn Γ ρ s) (hΦ : rightDefect ρ t u = 0) (hu1 : u 1 = 0) : u = 0 := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨-, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have hw : ∀ x, u (x * t) = ρ t (u x) := by
    intro x
    have hx := congrFun hΦ x
    rw [rightDefect_apply, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  let H : Subgroup G :=
    { carrier := {g | ∀ x, u (x * g) = ρ g (u x)}
      mul_mem' := by
        intro a b ha hb'
        simp only [Set.mem_ofPred_eq] at ha hb' ⊢
        intro x
        rw [← mul_assoc, hb', ha, hρc]
      one_mem' := by
        simp only [Set.mem_ofPred_eq]
        intro x
        rw [mul_one, h1]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro x
        have hx := ha (x * a⁻¹)
        rw [inv_mul_cancel_right] at hx
        rw [hx, hρc, mul_inv_cancel, h1] }
  have hle : Subgroup.closure ({s, t} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hb
    · exact hw
  rw [hgen] at hle
  funext g
  have hg : g ∈ H := hle (Subgroup.mem_top g)
  have h1g := (show ∀ x, u (x * g) = ρ g (u x) from hg) 1
  rw [one_mul, hu1, map_zero] at h1g
  exact h1g

theorem finrank_extn_le {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v) (hst : s ^ 2 = t ^ 3)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (hE : FiniteDimensional ℂ E)
    (hR : FiniteDimensional ℂ (relThree Γ ρ t)) :
    FiniteDimensional ℂ (extn Γ ρ s) ∧
      Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  have := hE
  have := hR
  have hmem : ∀ u : extn Γ ρ s, ((rightDefect ρ t).comp (extn Γ ρ s).subtype) u ∈ relThree Γ ρ t :=
    fun u => rightDefect_mem_relThree Γ ρ s t hρ hst u.1 u.2
  let Φ : extn Γ ρ s →ₗ[ℂ] relThree Γ ρ t × E :=
    LinearMap.prod (LinearMap.codRestrict (relThree Γ ρ t) ((rightDefect ρ t).comp (extn Γ ρ s).subtype) hmem)
      ((LinearMap.proj (R := ℂ) (φ := fun _ : G => E) (1 : G)).comp (extn Γ ρ s).subtype)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro u hu
    have h1' := congrArg (fun p : relThree Γ ρ t × E => (p.1 : G → E)) hu
    have h2' := congrArg Prod.snd hu
    exact Subtype.ext (eq_zero_of_rightDefect_eq_zero Γ ρ s t hρ h1 hgen u.1 u.2 h1' h2')
  have hfin : FiniteDimensional ℂ (extn Γ ρ s) := FiniteDimensional.of_injective Φ hinj
  refine ⟨hfin, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod] at hle

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtension
section
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

theorem exists_extend_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u : G → E, ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := by
  classical
  let r : G → G := fun x => (Quotient.mk (QuotientGroup.rightRel Γ) x).out
  have hr : ∀ x, x * (r x)⁻¹ ∈ Γ := fun x =>
    QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq
      (Quotient.mk (QuotientGroup.rightRel Γ) x)))
  have hrγ : ∀ (γ : Γ) (x : G), r (γ * x) = r x := fun γ x => by
    have : Quotient.mk (QuotientGroup.rightRel Γ) ((γ : G) * x)
        = Quotient.mk (QuotientGroup.rightRel Γ) x := by
      apply Eq.symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.2
      simp
    simp only [r, this]
  refine ⟨fun x => ρ (r x) (z ⟨x * (r x)⁻¹, hr x⟩), fun γ x => ?_⟩
  have h1 : (⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩ : Γ) = γ * ⟨x * (r x)⁻¹, hr x⟩ := by
    apply Subtype.ext
    simp [hrγ, mul_assoc]
  show ρ (r (γ * x)) (z ⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩) = _
  rw [h1, hz, hrγ, map_add (f := _), ← hmul]
  simp

theorem exists_extn_of_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u ∈ extn Γ ρ s, ∀ γ : Γ, u γ - u 1 = z γ := by
  obtain ⟨u0, hu0⟩ := exists_extend_cocyc Γ ρ hmul z hz
  let u : G → E := fun x => (1 / 4 : ℂ) •
    (u0 x + ρ (s ^ 3) (u0 (x * s)) + ρ (s ^ 2) (u0 (x * s ^ 2)) + ρ s (u0 (x * s ^ 3)))
  have e1 : s * s ^ 3 = 1 := by rw [← hs]; group
  have e2 : s ^ 2 * s ^ 2 = 1 := by rw [← hs]; group
  have e3 : s ^ 3 * s = 1 := by rw [← hs]; group
  have key : ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := fun γ x => by
    simp only [u, mul_assoc, hu0, map_add (f := _), ← hmul, e1, e2, e3, mul_one]
    module
  have key1 : ∀ γ : Γ, u γ - u 1 = z γ := fun γ => by
    have := key γ 1
    rw [mul_one, hone] at this
    rw [this]; abel
  refine ⟨u, ⟨fun γ hγ x => ?_, fun x => ?_⟩, key1⟩
  · have h1 := key ⟨γ, hγ⟩ x
    have h2 := key1 ⟨γ, hγ⟩
    simp only at h1 h2
    rw [h1, h2]; abel
  · have f1 : s * s = s ^ 2 := (pow_two s).symm
    have f2 : s * s ^ 2 = s ^ 3 := by group
    have f3 : s ^ 2 * s = s ^ 3 := by group
    simp only [u, mul_assoc, map_add (f := _), map_smul, ← hmul, e1, e3, f1, f2, f3, mul_one, hone]
    module

def extnToCocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : extn Γ ρ s →ₗ[ℂ] cocyc Γ ρ where
  toFun u := ⟨fun γ => u.1 γ - u.1 1, fun γ δ => by
    have := u.2.1 γ γ.2 δ
    simp only [Subgroup.coe_mul]
    rw [← this]; abel⟩
  map_add' u v := by
    apply Subtype.ext; funext γ
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' c u := by
    apply Subtype.ext; funext γ
    simp [smul_sub]

theorem twInv_le_extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) :
    twInv Γ s (ρ s) ≤ extn Γ ρ s := by
  rintro f ⟨h1, h2⟩
  refine ⟨fun γ hγ x => ?_, h2⟩
  have := h1 γ hγ 1
  rw [mul_one] at this
  rw [h1 γ hγ, this]; simp

theorem finrank_cocyc_add_twInv_le_extn {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (hfd : FiniteDimensional ℂ (extn Γ ρ s)) :
    FiniteDimensional ℂ (cocyc Γ ρ) ∧
      Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s))
        ≤ Module.finrank ℂ (extn Γ ρ s) := by
  have hsurj : Function.Surjective (extnToCocyc Γ ρ s) := by
    rintro ⟨z, hz⟩
    obtain ⟨u, hu, h⟩ := exists_extn_of_cocyc Γ ρ s hmul hone hs z hz
    exact ⟨⟨u, hu⟩, Subtype.ext (funext h)⟩
  refine ⟨Module.Finite.of_surjective _ hsurj, ?_⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (extnToCocyc Γ ρ s)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  let i : twInv Γ s (ρ s) →ₗ[ℂ] LinearMap.ker (extnToCocyc Γ ρ s) :=
    (Submodule.inclusion (twInv_le_extn Γ ρ s)).codRestrict _ (fun f => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext; funext γ
      have := f.2.1 γ γ.2 1
      rw [mul_one] at this
      show f.1 γ - f.1 1 = 0
      rw [this, sub_self])
  have hi : Function.Injective i := by
    intro a b hab
    exact Submodule.inclusion_injective _ (congrArg Subtype.val hab)
  have := LinearMap.finrank_le_finrank_of_injective hi
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLe
section
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem finrank_relThree_add_finrank_twInv_le :
    ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G)
      (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) →
      t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) →
      FiniteDimensional ℂ (relThree Γ ρ t) ∧
        Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤
          Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  intro G _ E _ _ Γ ρ t hmul hone ht hfd
  have h2 : ∀ v, ρ (t ^ 2) v = ρ t (ρ t v) := fun v => by rw [pow_two, hmul]
  have h3 : ∀ v, ρ (t ^ 3) v = ρ t (ρ t (ρ t v)) := fun v => by
    rw [pow_succ t 2, hmul, h2]
  have h6 : ∀ v, ρ t (ρ t (ρ t (ρ t (ρ t (ρ t v))))) = v := fun v => by
    have h : t ^ 3 * t ^ 3 = 1 := by rw [← pow_add]; exact ht
    have h' := hmul (t ^ 3) (t ^ 3) v
    rw [h, hone, h3, h3] at h'
    exact h'.symm
  have e2 : ∀ x : G, x * t * t = x * t ^ 2 := fun x => by rw [pow_two, mul_assoc]
  have e3 : ∀ x : G, x * t * t ^ 2 = x * t ^ 3 := fun x => by
    rw [mul_assoc, ← pow_succ']
  have hle : relThree Γ ρ t ≤ twInv Γ (t ^ 3) (ρ (t ^ 3)) := fun Φ hΦ => hΦ.1
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  let P : twInv Γ (t ^ 3) (ρ (t ^ 3)) →ₗ[ℂ] twInv Γ t (ρ t) :=
    { toFun := fun Φ => ⟨fun x => ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2), by
        obtain ⟨Φ, hΓ, hΦ⟩ := Φ
        refine ⟨fun γ hγ x => ?_, fun x => ?_⟩
        · simp only [mul_assoc, hΓ γ hγ]
        · simp only [e2, e3, hΦ, h2, h3, map_add (f := _)]
          abel⟩
      map_add' := fun Φ Ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        abel
      map_smul' := fun c Φ => by
        ext x
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add] }
  have hP : ∀ Φ x, (P Φ).1 x = ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2) :=
    fun _ _ => rfl
  have hsurj : LinearMap.range P = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨Ψ, hΓ, hΨ⟩
    have hΨ2 : ∀ x, Ψ (x * t ^ 2) = ρ t (ρ t (Ψ x)) := fun x => by rw [← e2, hΨ, hΨ]
    have hΨ3 : ∀ x, Ψ (x * t ^ 3) = ρ t (ρ t (ρ t (Ψ x))) := fun x => by rw [← e3, hΨ2, hΨ]
    refine ⟨⟨fun x => (1 / 3 : ℂ) • ρ t (ρ t (ρ t (ρ t (Ψ x)))), fun γ hγ x => ?_, fun x => ?_⟩, ?_⟩
    · simp only [hΓ γ hγ]
    · simp only [hΨ3, h3, map_smul]
    · ext x
      rw [hP]
      simp only [hΨ, hΨ2, h2, map_smul, h6]
      module
  have hker : Module.finrank ℂ (relThree Γ ρ t) ≤ Module.finrank ℂ (LinearMap.ker P) := by
    let ι : relThree Γ ρ t →ₗ[ℂ] LinearMap.ker P :=
      (Submodule.inclusion hle).codRestrict _ (fun Φ => by
        rw [LinearMap.mem_ker]
        ext x
        rw [hP]
        exact Φ.2.2 x)
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) ?_
    intro a b hab
    exact Submodule.inclusion_injective hle (congrArg Subtype.val hab)
  have hrk := LinearMap.finrank_range_add_finrank_ker P
  rw [hsurj, finrank_top] at hrk
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicitStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeVOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.vOp q f τ) := by
  first | exact @GlobalTheory.Hk.vOp_hasSum | exact GlobalTheory.Hk.vOp_hasSum | (intros; apply GlobalTheory.Hk.vOp_hasSum <;> assumption)
end

