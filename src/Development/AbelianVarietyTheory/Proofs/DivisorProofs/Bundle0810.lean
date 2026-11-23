module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroup
section
open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem exists_mul_lr {F : Type} [NormedField F] [ProperSpace F] {ψ : AddChar F ℂ} (hψ : IsLocallyConstant ψ)
    (hψ1 : ψ ≠ 1) {m : ℕ} {L : Set (Fin (m + 1) → F)} (hL : L ∈ nhds (0 : Fin (m + 1) → F))
    (T' : GL (Fin (m + 1)) F →₀ ℂ) (κ : GL (Fin (m + 1)) F → GL (Fin (m + 1)) F) (Φ : (Fin (m + 1) → F) → ℂ)
    (hΦ : IsLocallyConstant Φ) :
    ∃ M₂ : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act (comp M₂ (T'.sum fun k c => Finsupp.single (cor (κ k)) c)) f (cor h) =
        Φ (lr h) * act (T'.sum fun k c => Finsupp.single (cor (κ k)) c) f (cor h) := by
  classical
  have hK := GlobalTheory.JSW.isCompact_charAnnihilator_of_mem_nhds_zero ψ hψ hψ1 L hL
  set K := {r : Fin (m + 1) → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} with hKdef
  let K' : Set (Fin (m + 1) → F) := ⋃ k ∈ T'.support, (fun r => r ᵥ* ((κ k)⁻¹).val) '' K
  have hK' : IsCompact K' := T'.support.isCompact_biUnion fun k _ =>
    hK.image (continuous_id.matrix_vecMul continuous_const)
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact ψ hψ hψ1 K' hK' Φ hΦ
  set T₂ : GL (Fin (m + 2)) F →₀ ℂ := T'.sum fun k c => Finsupp.single (cor (κ k)) c with hT₂def
  let M₂ : GL (Fin (m + 2)) F →₀ ℂ := M.sum fun v c => Finsupp.single (mir 1 v) c
  refine ⟨M₂, fun f hf hfL h => ?_⟩
  have hT₂ : act T₂ f (cor h) = T'.sum fun k c => c * f (cor (h * κ k)) := by
    simp only [T₂, act_finsupp_sum, act_single, map_mul]
  rw [act_comp]
  simp only [M₂, act_finsupp_sum, act_single, eqv_cor_mul_col (eqv_act hf T₂), ← mul_assoc]
  rw [← Finsupp.sum_mul]
  by_cases h0 : act T₂ f (cor h) = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hM]
    rw [hT₂] at h0
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hk1 := right_ne_zero_of_mul hk0
    refine Set.mem_iUnion₂.2 ⟨k, hk, lr (h * κ k), fun y hy => ?_, ?_⟩
    · have := hfL y hy (cor (h * κ k))
      rw [eqv_cor_mul_col hf] at this
      exact (mul_eq_right₀ hk1).1 this
    · simp only
      rw [← lr_mul, mul_inv_cancel_right]

theorem exists_cut_cor_of_sub : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  intro F _ _ _ ψ hψ hψ1 m H B hBc hBo L hL h₀
  classical
  let U : Subgroup (GL (Fin (m + 1)) F) := B.map (MulAut.conj h₀).toMonoidHom
  have hUe : (U : Set (GL (Fin (m + 1)) F)) = (fun b => h₀ * b * h₀⁻¹) '' B := by
    ext x; simp [U]
  have hUm : ∀ b ∈ B, h₀ * b * h₀⁻¹ ∈ U := fun b hb => ⟨b, hb, rfl⟩
  have hUB : ∀ u ∈ U, h₀⁻¹ * u * h₀ ∈ B := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [mul_assoc] using hb
  have hUc : IsCompact (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact hBc.image (by fun_prop)
  have hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact ((isOpenMap_mul_right h₀⁻¹).comp (isOpenMap_mul_left h₀)) _ hBo
  obtain ⟨U₁, hU₁U, hU₁o, T', hT'⟩ := H U hUc hUo 1
  have hU₁c : IsCompact (U₁ : Set (GL (Fin (m + 1)) F)) :=
    hUc.of_isClosed_subset (U₁.isClosed_of_isOpen hU₁o) hU₁U
  have hOe := _root_.GlobalTheory.JSW.Orbit.isClopen_orbit U₁ hU₁c hU₁o (lr 1) (lr_ne_zero 1)
  let R : GL (Fin (m + 1)) F → Set (Fin (m + 1) → F) := fun a =>
    (fun r => r ᵥ* ((a * h₀)⁻¹).val) ⁻¹' {r | ∃ b ∈ U₁, r = lr 1 ᵥ* (b : Matrix (Fin (m + 1)) (Fin (m + 1)) F)}
  have hR : ∀ a, IsClopen (R a) := fun a => hOe.preimage (continuous_id.matrix_vecMul continuous_const)

  have hC : ∀ a ∈ U, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      ∀ h, lr h ∈ R a → act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro a ha f hf hfB h hRa
    obtain ⟨v, hv, e⟩ := hRa
    have e' : lr (h * h₀⁻¹ * a⁻¹) = lr (1 * v) := by
      rw [show h * h₀⁻¹ * a⁻¹ = h * (a * h₀)⁻¹ by group]
      exact e
    have hmem : h * h₀⁻¹ * a⁻¹ ∈ {g | ∃ p : GL (Fin (m + 1)) F, lr p = lr 1 ∧ ∃ u ∈ U₁, g = p * u} :=
      ⟨h * h₀⁻¹ * a⁻¹ * v⁻¹, by rw [lr_mul_congr e' v⁻¹, one_mul, mul_inv_cancel], v, hv, by group⟩
    have h2 := hT' (fun g => f (cor (g * h₀)))
      (fun u hu g => by simp only [mul_assoc]; exact hf.res u hu _)
      (fun u hu g => by
        rw [show g * u * h₀ = g * h₀ * (h₀⁻¹ * u * h₀) by group, map_mul]
        exact hfB _ (hUB u hu) _)
      (h * h₀⁻¹ * a⁻¹) hmem
    have hT₂ : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        T'.sum fun k c => c * f (cor (h * (h₀⁻¹ * a⁻¹ * k * h₀))) := by
      simp only [act_finsupp_sum, act_single, map_mul]
    have h3 : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        act T' (fun g => f (cor (g * h₀))) (h * h₀⁻¹ * a⁻¹) := by
      rw [hT₂]
      simp only [act, mul_assoc]
    rw [h3, h2]
    have h4 : h * h₀⁻¹ * a⁻¹ ∈ cell 1 (U : Set (GL (Fin (m + 1)) F)) ↔
        h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
      constructor
      · rintro ⟨u, hu, c, hc, e⟩
        refine ⟨u, hu, h₀⁻¹ * (c * a) * h₀, hUB _ (U.mul_mem hc ha), ?_⟩
        rw [show h = h * h₀⁻¹ * a⁻¹ * (a * h₀) by group, e]
        group
      · rintro ⟨u, hu, c, hc, rfl⟩
        exact ⟨u, hu, h₀ * c * h₀⁻¹ * a⁻¹, U.mul_mem (hUm c hc) (U.inv_mem ha), by group⟩
    by_cases h5 : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem h5, Set.indicator_of_mem (h4.2 h5)]
      rw [show h * h₀⁻¹ * a⁻¹ * h₀ = h * (h₀⁻¹ * a⁻¹ * h₀) by group, map_mul]
      exact hfB _ (by simpa using hUB _ (U.inv_mem ha)) _
    · rw [Set.indicator_of_notMem h5, Set.indicator_of_notMem (fun h6 => h5 (h4.1 h6))]

  have key : ∀ A : Finset (GL (Fin (m + 1)) F), (∀ a ∈ A, a ∈ U) → ∃ S : GL (Fin (m + 2)) F →₀ ℂ,
      ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act S f (cor h) = (⋃ a ∈ A, R a).indicator 1 (lr h) *
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; exact ⟨0, fun f _ _ _ h => by simp⟩
    | insert a A haA ih =>
      intro hA
      obtain ⟨S, hS⟩ := ih (fun b hb => hA b (Finset.mem_insert_of_mem hb))
      have ha : a ∈ U := hA a (Finset.mem_insert_self a A)
      have hcl : IsClopen (R a \ ⋃ b ∈ A, R b) := (hR a).diff (isClopen_biUnion_finset fun b _ => hR b)
      obtain ⟨M₂, hM₂⟩ := exists_mul_lr hψ hψ1 hL T' (fun k => h₀⁻¹ * a⁻¹ * k * h₀)
        ((R a \ ⋃ b ∈ A, R b).indicator 1) (LocallyConstant.charFn ℂ hcl).isLocallyConstant
      refine ⟨S + comp M₂ (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c),
        fun f hf hfB hfL h => ?_⟩
      rw [act_add, hS f hf hfB hfL h, hM₂ f hf hfL h]
      by_cases h1 : lr h ∈ ⋃ b ∈ A, R b
      · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
          rw [Finset.set_biUnion_insert]; exact Or.inr h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h3 => h3.2 h1)]
        simp
      · by_cases h3 : lr h ∈ R a
        · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact Or.inl h3
          rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem (s := R a \ ⋃ b ∈ A, R b) ⟨h3, h1⟩,
            hC a ha f hf hfB h h3]
          simp
        · have h2 : lr h ∉ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact fun h4 => h4.elim h3 h1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
            Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h4 => h3 h4.1)]
          simp
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover
    (fun a : U => (fun x => x * (a : GL (Fin (m + 1)) F)⁻¹) ⁻¹' (U₁ : Set (GL (Fin (m + 1)) F)))
    (fun a => hU₁o.preimage (continuous_mul_const _))
    (fun u hu => Set.mem_iUnion.2 ⟨⟨u, hu⟩, by simp [U₁.one_mem]⟩)
  obtain ⟨S, hS⟩ := key (t.image Subtype.val) (fun a ha => by
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ha
    exact b.2)
  refine ⟨S, fun f hf hfB hfL h => ?_⟩
  rw [hS f hf hfB hfL h]
  by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
  · have hmem : lr h ∈ ⋃ a ∈ t.image Subtype.val, R a := by
      obtain ⟨u, hu, c, hc, rfl⟩ := hh
      obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.1 (ht (hUm c hc))
      refine Set.mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹, hw, ?_⟩
      show lr (u * h₀ * c) ᵥ* _ = _
      rw [← lr_mul, show u * h₀ * c * ((i : GL (Fin (m + 1)) F) * h₀)⁻¹ =
        u * (h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹) by group, lr_mul_congr (lr_of_mem hu), one_mul, ← lr_mul, one_mul]
    rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hh, mul_zero]

end GlobalTheory.JSW.Cut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibAdel

open Formalism.HermitianLatticesTheory (localization₂)

section General

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_one_of_vAdd (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (h : vAdd w x = 0) :
    w.valuation K x = 1 := by
  unfold vAdd at h
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, neg_eq_zero.mp h, WithZero.exp_zero]

theorem kron_mul {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R]
    (M M' : ∀ t, Matrix (J t) (J t) R) : kron M * kron M' = kron fun t => M t * M' t := by
  ext I I''
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun I' _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kron_one {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
    {R : Type} [CommRing R] : (kron fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  first
  | exact @_root_.GlobalTheory.KroneckerIdentity.kron_identity
  | exact _root_.GlobalTheory.KroneckerIdentity.kron_identity
  | (apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KroneckerIdentity.kron_identity <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KroneckerIdentity.kron_identity ..)

theorem rhoMat_mul {n : ℕ} (la : Fin n → ℕ) (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la g * rhoMat la h = rhoMat la (h * g) := by
  rw [GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, Matrix.transpose_mul, map_mul, LinearMap.toMatrix_mul]

theorem rhoMat_one {n : ℕ} (la : Fin n → ℕ) : rhoMat la (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [GlobalTheory.DefPt.rhoMat, Matrix.transpose_one, map_one, LinearMap.toMatrix_one]

theorem exists_int_scale (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {M : Matrix ι κ K} (hM : IntAt w M) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix ι κ (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • M := by
  have h1 : ∀ p : ι × κ, ∃ r : 𝓞 K, ∃ d ∈ w.asIdeal.primeCompl,
      M p.1 p.2 * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K r := fun p => by
    obtain ⟨r, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer (M p.1 p.2) (hM p.1 p.2)
    exact ⟨r, d, d.2, h⟩
  choose r d hd h using h1
  refine ⟨∏ p, d p, Submonoid.prod_mem _ fun p _ => hd p,
    Matrix.of fun i j => (∏ p ∈ Finset.univ.erase (i, j), d p) * r (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ← h]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), map_mul]
  ring

theorem valuation_repr_le_one (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} {la : Fin n → ℕ} {f : nabla la K}
    (hf : f ∈ localization₂ w.asIdeal (stdLat la K)) (i : Idx la) : w.valuation K ((basis la K).repr f i) ≤ 1 := by
  obtain ⟨s, hs, hf⟩ := hf
  rw [stdLat_eq_span, Submodule.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  have hc' : ∑ i, (algebraMap (𝓞 K) K (c i)) • basis la K i = (algebraMap (𝓞 K) K s) • f := hc
  have h1 := congrArg (fun x => (basis la K).repr x i) hc'
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  have h2 : w.valuation K (algebraMap (𝓞 K) K s) = 1 := (w.valuation_eq_one_iff_notMem).2 hs
  have h3 : w.valuation K (algebraMap (𝓞 K) K (c i)) ≤ 1 := w.valuation_le_one (c i)
  rw [h1, map_mul, h2, one_mul] at h3
  exact h3

theorem intAt_rhoMat (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (la : Fin n → ℕ) {g : Matrix (Fin n) (Fin n) K}
    (hg : IntAt w g) : IntAt w (rhoMat la g) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int_scale w (M := gᵀ) (fun i j => hg j i)
  intro i j
  have hj : basis la K j ∈ localization₂ w.asIdeal (stdLat la K) :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul, stdLat_eq_span]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  have h := rho_mem_locP w ht hA hj
  rw [GlobalTheory.DefPt.rhoMat, LinearMap.toMatrix_apply]
  exact valuation_repr_le_one w h i

theorem intAt_smul (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] {c : K}
    (hc : w.valuation K c ≤ 1) {M : Matrix ι κ K} (hM : IntAt w M) : IntAt w (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc (hM i j)

theorem intAt_kron (w : HeightOneSpectrum (𝓞 K)) {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {M : ∀ t, Matrix (J t) (J t) K} (hM : ∀ t, IntAt w (M t)) :
    IntAt w (kron M) := fun I I' => by
  rw [kron, Matrix.of_apply, map_prod]
  exact Finset.prod_le_one' fun t _ => hM t (I t) (I' t)

end General

theorem fibA_isAdelic : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ)
    (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K)
    (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) →
    (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) →
    IsAdelic fun w => fibA la (a w) (B w) := by
  intro K _ _ T _ _ N la a B ha hfin hB
  have hinv : ∀ w, (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) * fibA la (a w) (B w) = 1 := by
    intro w
    have e : ∀ t, rhoMat (la t) (B w t)⁻¹ * rhoMat (la t) (B w t) = 1 := fun t => by
      rw [rhoMat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ((hB t).1 w)), rhoMat_one]
    rw [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, smul_smul, inv_mul_cancel₀ (ha w), one_smul]
    simp only [e]
    exact kron_one
  have hinv' : ∀ w, (fibA la (a w) (B w))⁻¹ = (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) :=
    fun w => Matrix.inv_eq_left_inv (hinv w)
  refine ⟨fun w h => ?_, ?_⟩
  · have h1 := congrArg Matrix.det (hinv w)
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  · refine (hfin.union (Set.finite_iUnion fun t => (hB t).2)).subset fun w hw => ?_
    by_contra hw'
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, Function.mem_support, not_or, not_exists,
      not_not] at hw'
    obtain ⟨h0, h1⟩ := hw'
    have hv : w.valuation K (a w) = 1 := valuation_eq_one_of_vAdd w (ha w) h0
    refine hw ⟨intAt_smul w hv.le (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).1), ?_⟩
    rw [hinv' w]
    exact intAt_smul w (by rw [map_inv₀, hv, inv_one]) (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).2)

end GlobalTheory.FibAdel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS

namespace GlobalTheory.KS.PowPB

theorem powMap_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    powMap f φ hφ m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    powMap f φ hφ m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

theorem pow_left_hom_ext {S : Scheme.{0}} {A : Over S} {m : ℕ} {T : Scheme.{0}} (g₁ g₂ : T ⟶ (pow A m).left)
    (hh : g₁ ≫ (pow A m).hom = g₂ ≫ (pow A m).hom) (hi : ∀ i, g₁ ≫ (pr A i).left = g₂ ≫ (pr A i).left) :
    g₁ = g₂ := by
  let u₁ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₁ rfl
  let u₂ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₂ (by simpa using hh.symm)
  have : u₁ = u₂ := Pi.hom_ext _ _ (fun i => by
    ext
    simpa [u₁, u₂] using hi i)
  exact congrArg CommaMorphism.left this

noncomputable def liftPow {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : T ⟶ (pow A' m).left :=
  (Pi.lift (fun i : Fin m => (Over.homMk (H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w))
    (H.lift_snd _ _ _) : Over.mk b ⟶ A')) : Over.mk b ⟶ pow A' m).left

theorem liftPow_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : liftPow H m a b w ≫ (pow A' m).hom = b := by
  unfold liftPow
  exact Over.w _

theorem liftPow_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) (i : Fin m) :
    liftPow H m a b w ≫ (pr A' i).left = H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w) := by
  unfold liftPow
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f →
    ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  intro S S' A A' f φ hφ H m
  refine ⟨⟨powMap_w f φ hφ m⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => liftPow H m s.fst s.snd s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    apply pow_left_hom_ext
    · rw [Category.assoc, powMap_w, ← Category.assoc, liftPow_w, s.condition]
    · intro i
      rw [Category.assoc, powMap_pr, ← Category.assoc, liftPow_pr, H.lift_fst]
  · intro s
    exact liftPow_w H m _ _ _
  · intro s u h₁ h₂
    apply pow_left_hom_ext
    · rw [h₂, liftPow_w]
    · intro i
      rw [liftPow_pr]
      apply H.hom_ext
      · rw [H.lift_fst, Category.assoc, ← powMap_pr f φ hφ, ← Category.assoc, h₁]
      · rw [H.lift_snd, Category.assoc, Over.w, h₂]

end GlobalTheory.KS.PowPB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackFiniteFlatDegreeBounds
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich_flat : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

