module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIInfOfApply
section
namespace GlobalTheory.IndependentInfimum

open Module

theorem le_of_indep {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : X → Submodule K V) (hW : iSupIndep W) (hUW : ∀ x, U x ≤ W x)
    (hU : ⨆ x, U x = ⊤) (x : X) : W x ≤ U x := by
  classical
  intro w hw
  have htop : w ∈ ⨆ y, U y := by rw [hU]; exact Submodule.mem_top
  have hsplit : (⨆ y, U y) = U x ⊔ ⨆ (y) (_ : y ≠ x), U y := by
    apply le_antisymm
    · refine iSup_le fun y => ?_
      by_cases hy : y = x
      · subst hy
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le y hy le_rfl)
    · exact sup_le (le_iSup U x) (iSup₂_le fun y _ => le_iSup U y)
  rw [hsplit] at htop
  obtain ⟨u, hu, w', hw', hsum⟩ := Submodule.mem_sup.1 htop
  have hw'W : w' ∈ ⨆ (y) (_ : y ≠ x), W y :=
    (iSup₂_mono fun y _ => hUW y) hw'
  have hdiff : w - u ∈ W x := W x |>.sub_mem hw (hUW x hu)
  have heq : w - u = w' := by rw [← hsum]; abel
  have hdis := (hW x).le_bot (Submodule.mem_inf.2 ⟨hdiff, heq ▸ hw'W⟩)
  rw [Submodule.mem_bot, sub_eq_zero] at hdis
  rw [hdis]
  exact hu

theorem mem_iInf_of_apply {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : I → Module.End K V) (x : I → K) (v : V) (hv : ∀ i, A i v = x i • v) :
    v ∈ ⨅ i, (A i).maxGenEigenspace (x i) := Submodule.mem_iInf _ |>.2 fun i =>
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (hv i))

theorem main {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hE : ⨆ (c : C), Ec c = LinearMap.range e)
    (hl : ∀ (c : C), ∀ w ∈ Ec c, ∀ (i : I), (h i : E → E) w = lab c i • w) :
    (Formalism.L2.Col.PairComm fun (i : I) ↦ h i * e) ∧ ∀ (Q : (I → ℂ) → Prop), ¬Q (0 : I → ℂ) →
      Formalism.L2.Col.eigSum (fun (i : I) ↦ h i * e) Q = ⨆ (c : C), ⨆ (_ : Q (lab c)), Ec c := by
  classical
  have hee : ∀ v, e (e v) = e v := fun v => by
    have := congrArg (fun f : Module.End ℂ E => f v) he
    simpa using this
  have hfix : ∀ c, ∀ w ∈ Ec c, e w = w := by
    intro c w hw
    have : w ∈ LinearMap.range e := hE ▸ Submodule.mem_iSup_of_mem c hw
    obtain ⟨u, rfl⟩ := this
    exact hee u
  have hA : ∀ c, ∀ w ∈ Ec c, ∀ i, (h i * e) w = lab c i • w := by
    intro c w hw i
    rw [Module.End.mul_apply, hfix c w hw, hl c w hw]
  have hcomm : ∀ i j, Commute (h i * e) (h j * e) := by
    intro i j
    have key : ∀ w ∈ ⨆ c, Ec c, (h i * e) ((h j * e) w) = (h j * e) ((h i * e) w) := by
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem c w hw =>
        rw [hA c w hw j, hA c w hw i, map_smul, map_smul, hA c w hw j, hA c w hw i, smul_comm]
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add (f := _), ha, hb]
    ext v
    have hv : e v ∈ ⨆ c, Ec c := by rw [hE]; exact ⟨v, rfl⟩
    have := key _ hv
    simpa [Module.End.mul_apply, hee] using this
  refine ⟨hcomm, fun Q hQ => ?_⟩
  have hind : iSupIndep fun x : I → ℂ => ⨅ i, (h i * e).maxGenEigenspace (x i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun i => h i * e)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  let U : (I → ℂ) → Submodule ℂ E := fun x =>
    (⨆ (c : C) (_ : lab c = x), Ec c) ⊔ ⨆ (_ : x = 0), LinearMap.ker e
  have hUW : ∀ x, U x ≤ ⨅ i, (h i * e).maxGenEigenspace (x i) := by
    intro x
    refine sup_le (iSup₂_le fun c hc w hw => ?_) (iSup_le fun hx w hw => ?_)
    · exact mem_iInf_of_apply (fun i => h i * e) x w fun i => hc ▸ hA c w hw i
    · refine mem_iInf_of_apply (fun i => h i * e) x w fun i => ?_
      rw [LinearMap.mem_ker] at hw
      simp [hx, Module.End.mul_apply, hw]
  have hU : ⨆ x, U x = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : LinearMap.range e ≤ ⨆ x, U x := by
      rw [← hE]
      exact iSup_le fun c => le_iSup_of_le (lab c)
        (le_sup_of_le_left (le_iSup₂_of_le (f := fun c' (_ : lab c' = lab c) => Ec c') c rfl le_rfl))
    have h2 : LinearMap.ker e ≤ ⨆ x, U x :=
      le_iSup_of_le 0 (le_sup_of_le_right
        (le_iSup_of_le (f := fun _ : (0 : I → ℂ) = 0 => LinearMap.ker e) rfl le_rfl))
    have h3 : v - e v ∈ LinearMap.ker e := by simp [LinearMap.mem_ker, hee]
    have := Submodule.add_mem _ (h1 ⟨v, rfl⟩) (h2 h3)
    simpa using this
  unfold Formalism.L2.Col.eigSum Formalism.L2.Col.eigAt
  apply le_antisymm
  · refine iSup₂_le fun x hx => (le_of_indep U _ hind hUW hU x).trans ?_
    refine sup_le (iSup₂_le fun c hc => ?_) (iSup_le fun h0 => absurd (h0 ▸ hx) hQ)
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c (hc ▸ hx) le_rfl
  · refine iSup₂_le fun c hc => ?_
    refine le_iSup₂_of_le
      (f := fun (x : I → ℂ) (_ : Q x) => ⨅ i, (h i * e).maxGenEigenspace (x i)) (lab c) hc ?_
    intro w hw
    exact mem_iInf_of_apply (fun i => h i * e) (lab c) w (hA c w hw)

end GlobalTheory.IndependentInfimum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NrmIdNonneg
section
namespace GlobalTheory.KerJ.CharVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dite_eq_left h]

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem chi_pow (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) :
    ((D.chiD t : ℂˣ) : ℂ) ^ h = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := by
  obtain ⟨-, k, hk, e⟩ := hp
  have h1 : D.chiD t ^ h = D.chiD (D.e1Dt z) := by
    rw [← map_pow, e, map_mul, D.chiD_UO k hk, mul_one]
  rw [← Units.val_pow_eq_pow_val, h1]
  exact D.rest_detCharacter_on_unitary_eq z

theorem chi_mem (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) : ((D.chiD t : ℂˣ) : ℂ) ∈ Qbar := by
  have h0 : ((D.chiD t : ℂˣ) : ℂ) ^ h ∈ Qbar := by
    rw [chi_pow D t h z hp]
    exact prod_mem fun τ _ => inv_mem (embT_mem D τ _)
  exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h0).of_pow hp.1)

theorem chiVal_holds (D : D7) : chiVal D := by
  intro p _ lam t h z hp
  refine ⟨chi_pow D t h z hp, ?_⟩
  have hm := chi_mem D t h z hp
  have e : (⟨((D.chiD t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ h = ∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact chi_pow D t h z hp
  rw [lamC_mem' lam hm, ← norm_pow, ← map_pow, e, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_inv₀, norm_inv, lamC_mem' lam (embT_mem D τ _)]

theorem key_norm {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*} [Fintype ι] (y κ : Qbar) (w : ι → Qbar)
    (s : ι → ℤ) (h n : ℕ) (hn : 0 < n) (e : y ^ h = (∏ τ, w τ ^ s τ) * κ) (hκ : κ ^ n = 1) :
    ‖lam y‖ ^ h = ∏ τ, ‖lam (w τ)‖ ^ s τ := by
  have h1 : ‖lam κ‖ = 1 := by
    have : ‖lam κ‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hκ, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  rw [← norm_pow, ← map_pow, e, map_mul, norm_mul, h1, mul_one, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, norm_zpow]

theorem val_of (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (ha : ((ρ t : ℂˣ) : ℂ) ∈ Qbar) (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    ‖lamC lam ((ρ t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (s τ) := by
  obtain ⟨-, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have h1' : ((ρ k : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1]; rfl
  have hkm : ((ρ k : ℂˣ) : ℂ) ∈ Qbar :=
    (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 (h1' ▸ one_mem Qbar)).of_pow hn)
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ h = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) * ((ρ k : ℂˣ) : ℂ) := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, e, map_mul]
  have := key_norm lam (⟨_, ha⟩ : Qbar) ⟨_, hkm⟩ (fun τ => ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩) s h n hn
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_mul, map_prod, map_zpow₀]
      exact e2)
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_one]
      exact h1')
  rw [lamC_mem' lam ha, this]
  exact Finset.prod_congr rfl fun τ _ => by rw [lamC_mem' lam (embT_mem D τ _)]

theorem rhoVal_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (hR : rhoThreeOf D C mt) : rhoValOf D C mt := by
  intro p _ lam t h z hp i hi
  obtain ⟨a, b, c⟩ := hR i hi
  obtain ⟨⟨a1, -⟩, ⟨a2, -⟩⟩ := a t h z hp
  exact ⟨val_of D _ _ lam t h z hp a1 (fun k hk => by obtain ⟨n, hn, x, -⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).1,
    val_of D _ _ lam t h z hp a2 (fun k hk => by obtain ⟨n, hn, -, x⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).2⟩

theorem isUltra (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

theorem norm_le_one_of_int {K : Type} [NormedField K] [IsUltrametricDist K] (x : K)
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := K)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral h1
  have h3 : NormedField.valuation x ≤ 1 := h2
  rw [NormedField.valuation_apply] at h3
  exact_mod_cast h3

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

theorem psi_int (a : 𝓞 E) : ‖ψ (a : E)‖ ≤ 1 :=
  norm_le_one_of_int _ ((RingOfIntegers.isIntegral_coe a).map (ψ : E →+* K).toIntAlgHom)

theorem pow_bound (𝔞 : Submodule (𝓞 E) E) (B : ℝ) (hB : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ B) (hB0 : 0 ≤ B) :
    ∀ (n : ℕ), ∀ y ∈ 𝔞 ^ n, ‖ψ y‖ ≤ B ^ n := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hy
    rw [pow_zero]
    exact psi_int ψ a
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih m hm) (hB k hk) (norm_nonneg _) (pow_nonneg hB0 n)
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem nu_pow (𝔞 : Submodule (𝓞 E) E) (h : ℕ) (h0 : h ≠ 0) (z : E)
    (e : 𝔞 ^ h = Submodule.span (𝓞 E) {z}) :
    sSup ((fun x : E => ‖ψ x‖) '' (𝔞 : Set E)) ^ h = ‖ψ z‖ := by
  set S := (fun x : E => ‖ψ x‖) '' (𝔞 : Set E) with hS
  have hne : S.Nonempty := ⟨_, 0, 𝔞.zero_mem, rfl⟩
  have hpow : ∀ x ∈ 𝔞, ‖ψ x‖ ^ h ≤ ‖ψ z‖ := by
    intro x hx
    have : x ^ h ∈ Submodule.span (𝓞 E) {z} := e ▸ Submodule.pow_mem_pow 𝔞 hx h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← norm_pow, ← map_pow, ← ha, Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (psi_int ψ a)
  set b : ℝ := ‖ψ z‖ ^ ((h : ℝ)⁻¹) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg (norm_nonneg _) _
  have hbh : b ^ h = ‖ψ z‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) h0
  have hle : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ b := fun x hx =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 h0).1 (hbh ▸ hpow x hx)
  have hbd : BddAbove S := ⟨b, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩
  have hs0 : 0 ≤ sSup S := Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)
  apply le_antisymm
  · rw [← hbh]
    exact pow_le_pow_left₀ hs0 (csSup_le hne (by rintro _ ⟨x, hx, rfl⟩; exact hle x hx)) h
  · have hz : z ∈ 𝔞 ^ h := e ▸ Submodule.mem_span_singleton_self z
    exact pow_bound ψ 𝔞 (sSup S) (fun x hx => le_csSup hbd ⟨x, hx, rfl⟩) hs0 h z hz

end Nu

noncomputable def psiT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem lamC_embT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = psiT D lam τ x := lamC_mem' lam (embT_mem D τ x)

theorem nrmId_pow (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) (h : ℕ) (h0 : h ≠ 0)
    (z : D.host.E) (e : 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {z}) :
    nrmId D lam τ 𝔞 ^ h = ‖lamC lam (embT D τ z)‖ := by
  unfold nrmId
  simp only [lamC_embT]
  haveI := isUltra p
  exact nu_pow (psiT D lam τ) 𝔞 h h0 z e

theorem nrmId_nonneg (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) :
    0 ≤ nrmId D lam τ 𝔞 :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)

theorem root_eq {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (ν f : ι → ℝ) (hν : ∀ τ, 0 ≤ ν τ) (s : ι → ℤ) (h : ℕ) (h0 : h ≠ 0)
    (hf : ∀ τ, ν τ ^ h = f τ) (e : a ^ h = ∏ τ, f τ ^ s τ) : a = ∏ τ, ν τ ^ s τ := by
  refine (pow_left_inj₀ ha (Finset.prod_nonneg fun τ _ => zpow_nonneg (hν τ) _) h0).1 ?_
  rw [e, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hf τ, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem brRho_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u))
    (mt : ℕ → D.Dt →* ℂˣ) (hR : rhoThreeOf D C mt) : brRhoOf D C mt := by
  intro idl hpin p _ lam t
  obtain ⟨k, z, hp⟩ := powRatAll_of D idl hpin (GlobalTheory.KernelScalarUnit.normOne_pow D) t
  obtain ⟨-, -, hmul, hz, -⟩ := hpin
  have h0 : k ≠ 0 := Nat.pos_iff_ne_zero.1 hp.1
  have hid : idl (QuotientGroup.mk t) ^ k = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    obtain ⟨-, c, hc, e⟩ := hp
    rw [← idl_pow hmul, ← hz z]
    congr 1
    rw [← QuotientGroup.mk_pow, e]
    exact QuotientGroup.mk_mul_of_mem _ hc
  have hf : ∀ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ k = ‖lamC lam (embT D τ (z : D.host.E))‖ :=
    fun τ => nrmId_pow D lam τ _ k h0 _ hid
  have hν : ∀ τ, 0 ≤ nrmId D lam τ (idl (QuotientGroup.mk t)) := fun τ => nrmId_nonneg D lam τ _
  refine ⟨?_, fun i hi => ?_⟩
  · have e := (chiVal_holds D p lam t k z hp).2
    have := root_eq _ (norm_nonneg _) _ _ hν (fun _ => (-1 : ℤ)) k h0 hf (by simpa only [zpow_neg_one] using e)
    simpa only [zpow_neg_one] using this
  · obtain ⟨x, y⟩ := rhoVal_holds D C mt hR p lam t k z hp i hi
    exact ⟨root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf x, root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf y⟩

end GlobalTheory.KerJ.CharVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormDetLatticeBasisEqDetIdealNorm
section
noncomputable section

namespace GlobalTheory.DetBasisNorm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem norm_det_le_one {p : ℕ} [Fact p.Prime] {N : ℕ} {C : Matrix (Fin N) (Fin N) ℂ_[p]}
    (h : ∀ a b, ‖C a b‖ ≤ 1) : ‖C.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [hs, one_mul]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _

theorem col_mem {E : Type} [Field E] {N : ℕ} {L₀ L : Submodule (𝓞 E) (Fin N → E)}
    (h₀ : ∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) {A : Matrix (Fin N) (Fin N) E}
    (hA : ∀ v ∈ L₀, A.mulVec v ∈ L) (b : Fin N) : (fun i => A i b) ∈ L := by
  have := hA (Pi.single b 1) ((h₀ _).2 fun k => by
    by_cases hk : k = b
    · subst hk; simpa using isIntegral_one
    · simpa [Pi.single_eq_of_ne hk] using isIntegral_zero)
  rwa [Matrix.mulVec_single_one] at this

theorem mulVec_mem {E : Type} [Field E] {N : ℕ} {L₀ L : Submodule (𝓞 E) (Fin N → E)}
    (h₀ : ∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) {A : Matrix (Fin N) (Fin N) E}
    (hA : ∀ b, (fun i => A i b) ∈ L) : ∀ v ∈ L₀, A.mulVec v ∈ L := by
  intro v hv
  have e : A.mulVec v = ∑ b, (⟨v b, (h₀ v).1 hv b⟩ : 𝓞 E) • (fun i => A i b) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    change _ = v b * A i b
    ring
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hA b)

theorem norm_det_eq_nrmId : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (N : ℕ) (L0 L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]), (∀ x, x ∈ L0 ↔ ∀ k, IsIntegral ℤ (x k)) → B.det ≠ 0 → (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) → (∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧ ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)) → ‖B.det‖ = nrmId D lam τ (detId D L0 L) := by
  intro D p _ lam τ N L0 L B h0 hdet hup hlow
  set ψ := GlobalTheory.KernelScalarUnit.lamTau D lam τ with hψdef
  have hψ : ∀ x, tauEmb D lam τ x = ψ x := fun x => congrFun (GlobalTheory.KernelScalarUnit.tauEmb_eq D lam τ) x
  have hn : (fun x : D.host.E => ‖lamC lam (embT D τ x)‖) = fun x => ‖ψ x‖ := funext fun x => by
    rw [← hψ]; rfl

  have hgen : ∀ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L0, A.mulVec v ∈ L) → ‖ψ A.det‖ ≤ ‖B.det‖ := by
    intro A hA
    have hC : ∀ a b, ‖(B⁻¹ * A.map ψ) a b‖ ≤ 1 := fun a b => by
      have := hup _ (col_mem h0 hA b) a
      simp only [hψ] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have e : A.map ψ = B * (B⁻¹ * A.map ψ) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul]
    have e2 : ψ A.det = (A.map ψ).det := ψ.map_det A
    rw [e2, e, Matrix.det_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_det_le_one hC)
  have hall : ∀ x ∈ detId D L0 L, ‖ψ x‖ ≤ ‖B.det‖ := by
    have : detId D L0 L ≤ GlobalTheory.KernelScalarUnit.ball ψ ‖B.det‖ (norm_nonneg _) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨A, hA, rfl⟩
      exact hgen A hA
    exact fun x hx => this hx
  have hbdd : BddAbove ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) := by
    refine ⟨‖B.det‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hall x hx
  have hne : ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)).Nonempty :=
    ⟨_, 0, Submodule.zero_mem _, rfl⟩
  have hS0 : 0 ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) :=
    (norm_nonneg _).trans (le_csSup hbdd ⟨0, Submodule.zero_mem _, rfl⟩)

  choose n r x hr hx hB using hlow
  have hlow : ‖B.det‖ ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) := by
    let f := (Matrix.detRowAlternating : (Fin N → ℂ_[p]) [⋀^Fin N]→ₗ[ℂ_[p]] ℂ_[p]).toMultilinearMap
    have e1 : B.det = f (fun a => ∑ k, r a k • fun i => ψ (x a k i)) := by
      rw [← Matrix.det_transpose]
      change Matrix.detRowAlternating _ = Matrix.detRowAlternating _
      congr 1
      funext a i
      simp only [Matrix.transpose_apply, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, f.map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hS0 fun c _ => ?_
    rw [f.map_smul_univ, smul_eq_mul,
      norm_mul, norm_prod]
    refine (mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => hr a (c a))).trans ?_
    let A : Matrix (Fin N) (Fin N) D.host.E := Matrix.of fun i a => x a (c a) i
    have hA : ∀ v ∈ L0, A.mulVec v ∈ L := mulVec_mem h0 fun b => hx b (c b)
    have e3 : f (fun a i => ψ (x a (c a) i)) = ψ A.det := by
      rw [ψ.map_det A, ← Matrix.det_transpose]
      rfl
    rw [e3]
    exact le_csSup hbdd ⟨A.det, Submodule.subset_span ⟨A, hA, rfl⟩, rfl⟩
  unfold nrmId
  rw [hn]
  exact le_antisymm hlow (csSup_le hne fun _ ⟨y, hy, e⟩ => e ▸ hall y hy)

end GlobalTheory.DetBasisNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrimeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → ∀ f g : W →+* Formalism.L2.G.Pend.WW p, (∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) → f = g := by
  first | exact @GlobalTheory.ringHom_wittKbar_eq_of_modp | exact GlobalTheory.ringHom_wittKbar_eq_of_modp | (intros; apply GlobalTheory.ringHom_wittKbar_eq_of_modp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVectStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsTame χ → IsParahoricVec χ π v → IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  first | exact @GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | exact GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | (intros; apply GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec <;> assumption)
end

