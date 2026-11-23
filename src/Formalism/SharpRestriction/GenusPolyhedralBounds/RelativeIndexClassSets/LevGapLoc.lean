module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure SplitCore (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) where
  φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)
  alg : ∀ c : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] c) = (c, c)
  int : ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F

end Core

section SC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sc_exists_emb {K : Type} [Field K] [Algebra F K] (sig : E →ₐ[F] E) (hsig : ∀ x, sig (sig x) = x)
    (hfix : ∀ x, sig x = x → ∃ a, algebraMap F E a = x) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b)
    (D : F) (hb2 : b ^ 2 = algebraMap F E D) (r : K) (hr : r ^ 2 = algebraMap F K D) :
    ∃ ψ : E →ₐ[F] K, ψ b = r := by
  have hd : algebraMap F E D = b ^ 2 := hb2.symm
  have h2E : (2 : E) ≠ 0 := two_ne_zero
  have hα : ∀ x, ∃ a, algebraMap F E a = (x + sig x) / 2 := fun x =>
    hfix _ (by rw [map_div₀, map_add (f := _), hsig, map_ofNat, add_comm])
  have hβ : ∀ x, ∃ a, algebraMap F E a = (x - sig x) / (2 * b) := fun x =>
    hfix _ (by rw [map_div₀, map_sub, hsig, map_mul, map_ofNat, hb]; field_simp; ring)
  choose α hα using hα
  choose β hβ using hβ
  have inj := (algebraMap F E).injective
  have αm : ∀ x y, α (x * y) = α x * α y + D * (β x * β y) := fun x y => inj (by
    simp only [map_add (f := _), map_mul, hα, hβ, hd]; field_simp; ring)
  have βm : ∀ x y, β (x * y) = α x * β y + β x * α y := fun x y => inj (by
    simp only [map_add (f := _), map_mul, hα, hβ]; field_simp; ring)
  have αa : ∀ x y, α (x + y) = α x + α y := fun x y => inj (by
    simp only [map_add (f := _), hα]; ring)
  have βa : ∀ x y, β (x + y) = β x + β y := fun x y => inj (by
    simp only [map_add (f := _), hβ]; ring)
  have αc : ∀ a, α (algebraMap F E a) = a := fun a => inj (by rw [hα, sig.commutes]; ring)
  have βc : ∀ a, β (algebraMap F E a) = 0 := fun a => inj (by rw [hβ, sig.commutes]; simp)
  have αb : α b = 0 := inj (by rw [hα, hb]; simp)
  have βb : β b = 1 := inj (by rw [hβ, hb, map_one]; field_simp; ring)
  have hc : ∀ a, algebraMap F K (α (algebraMap F E a)) + algebraMap F K (β (algebraMap F E a)) * r =
      algebraMap F K a := fun a => by rw [αc, βc]; simp
  refine ⟨{ toFun := fun x => algebraMap F K (α x) + algebraMap F K (β x) * r
            map_one' := by simpa using hc 1
            map_zero' := by simpa using hc 0
            map_mul' := fun x y => by
              rw [αm, βm]
              simp only [map_add (f := _), map_mul]
              linear_combination (-(algebraMap F K (β x) * algebraMap F K (β y))) * hr
            map_add' := fun x y => by rw [αa, βa, map_add (f := _), map_add (f := _)]; ring
            commutes' := hc }, ?_⟩
  show algebraMap F K (α b) + algebraMap F K (β b) * r = r
  rw [αb, βb]; simp

theorem sc_exists_iso {K : Type} [Field K] [Algebra F K] (sig : E →ₐ[F] E)
    (h2 : Module.finrank F E = 2) (ψ : E →ₐ[F] K) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b) :
    ∃ φ : E ⊗[F] K ≃+* K × K, ∀ (x : E) (c : K), φ (x ⊗ₜ[F] c) = (c * ψ x, c * ψ (sig x)) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let e : K ⊗[F] E →ₐ[K] K × K :=
    Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (ψ.prod (ψ.comp sig)) (fun _ _ => Commute.all _ _)
  have he : ∀ (a : K) (x : E), e (a ⊗ₜ x) = (a * ψ x, a * ψ (sig x)) := fun a x =>
    Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) a x
  have hr : ψ b ≠ 0 := (map_ne_zero ψ).mpr hb0
  have hsurj : Function.Surjective e := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * ψ b)) ⊗ₜ b, ?_⟩
    have h2K : (2 : K) ≠ 0 := two_ne_zero
    rw [map_add (f := _), he, he, hb, map_one sig, map_one ψ, map_neg]
    have aux : ∀ r : K, r ≠ 0 → ((x + y) / 2 * 1 + (x - y) / (2 * r) * r = x ∧
        (x + y) / 2 * 1 + (x - y) / (2 * r) * -r = y) := fun r hr => by
      have h1 : (x - y) / (2 * r) * r = (x - y) / 2 := by
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hr]
      have h3 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2K
      rw [mul_neg, h1, div_eq_mul_inv, div_eq_mul_inv]
      constructor
      · linear_combination x * h3
      · linear_combination y * h3
    exact Prod.ext (aux _ hr).1 (aux _ hr).2
  have hdim : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, h2]; simp
  have hinj : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mpr hsurj
  refine ⟨(Algebra.TensorProduct.comm F E K).toRingEquiv.trans
    (AlgEquiv.ofBijective e ⟨hinj, hsurj⟩).toRingEquiv, fun x c => ?_⟩
  show e (Algebra.TensorProduct.comm F E K (x ⊗ₜ[F] c)) = _
  rw [Algebra.TensorProduct.comm_tmul, he]

theorem sc_emb_int (v : HeightOneSpectrum (𝓞 F)) (ψ : E →ₐ[F] v.adicCompletion F) (x : 𝓞 E) :
    ψ (x : E) ∈ v.adicCompletionIntegers F := by
  have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ
  have h2 : IsIntegral (v.adicCompletionIntegers F) (ψ (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]; exact y.2

theorem sc_val_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) = 1 := by
  have h := Formalism.UG.P.csApprox_val_int v x
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at h
  rw [h]
  exact le_antisymm (v.intValuation_le_one x)
    (not_lt.mp fun h' => hx ((HeightOneSpectrum.intValuation_lt_one_iff_mem v x).mp h'))

theorem sc_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ∈ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) < 1 := by
  have h := Formalism.UG.P.csApprox_val_int v x
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at h
  rw [h]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v x).mpr hx

theorem sc_left_mem (v : HeightOneSpectrum (𝓞 F)) (y : 𝓞 E) :
    (y : E) ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v := Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)

theorem sc_right_mem (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (hc : c ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] c ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)


open Polynomial in
theorem sc_core (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → ∃ a, algebraMap F E a = x) (h2 : Module.finrank F E = 2)
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 E) (t N : 𝓞 F)
    (ht : algebraMap F E (t : F) = (a : E) + σ a) (hN : algebraMap F E (N : F) = (a : E) * σ a)
    (hNv : N ∈ v.asIdeal) (htv : t ∉ v.asIdeal) : Nonempty (SplitCore σ v) := by
  let f : Polynomial (v.adicCompletionIntegers F) :=
    X ^ 2 - C (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) * X +
      C (algebraMap (𝓞 F) (v.adicCompletionIntegers F) N)
  have hf : f.Monic := by
    show (X ^ 2 - C _ * X + C _ : Polynomial (v.adicCompletionIntegers F)).Monic
    monicity!
  have h₁ : f.eval 0 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : f.eval 0 = algebraMap (𝓞 F) (v.adicCompletionIntegers F) N := by simp [f]
    rw [this, Examples₂.adicInt_mem_max_iff]
    exact sc_val_lt_one v N hNv
  have h₂ : IsUnit (f.derivative.eval 0) := by
    have : f.derivative.eval 0 = - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t := by
      simp [f, derivative_pow]
    rw [this]
    exact (Examples₂.adicInt_isUnit_of_not_mem v t htv).neg
  obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian f hf 0 h₁ h₂
  have hr0 : r ^ 2 - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) N = 0 := by
    have := hr
    simpa [f, IsRoot.def] using this
  have hr' : (r : v.adicCompletion F) ^ 2 - algebraMap F (v.adicCompletion F) (t : F) * r +
      algebraMap F (v.adicCompletion F) (N : F) = 0 :=
    congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hr0
  have hb : σ ((a : E) - σ a) = -((a : E) - σ a) := by rw [map_sub, hσ]; ring
  have hb2 : ((a : E) - σ a) ^ 2 = algebraMap F E ((t : F) ^ 2 - 4 * (N : F)) := by
    rw [map_sub, map_pow, map_mul, ht, hN, map_ofNat]; ring
  have hρ2 : (2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F)) ^ 2 =
      algebraMap F (v.adicCompletion F) ((t : F) ^ 2 - 4 * (N : F)) := by
    rw [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * hr'
  have hDv : t ^ 2 - 4 * N ∉ v.asIdeal := fun h => by
    have : t ^ 2 ∈ v.asIdeal := by
      have := add_mem h (v.asIdeal.mul_mem_left 4 hNv)
      simpa using this
    exact htv (v.isPrime.mem_of_pow_mem 2 this)
  have hD : Valued.v (algebraMap F (v.adicCompletion F) ((t : F) ^ 2 - 4 * (N : F))) = 1 := by
    have e : (t : F) ^ 2 - 4 * (N : F) = algebraMap (𝓞 F) F (t ^ 2 - 4 * N) := by
      rw [map_sub, map_pow, map_mul, map_ofNat]
    rw [e]; exact sc_val_one v _ hDv
  have hρv : Valued.v (2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F)) = 1 := by
    have : Valued.v (2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F)) ^ 2 = 1 := by
      rw [← map_pow, hρ2, hD]
    exact (pow_eq_one_iff.1 this).resolve_right two_ne_zero
  have hb0 : (a : E) - σ a ≠ 0 := fun h => by
    rw [h] at hb2
    have h0 : ((t : F) ^ 2 - 4 * (N : F)) = 0 := by
      apply (algebraMap F E).injective
      rw [← hb2]; simp
    rw [h0] at hD
    simp at hD
  obtain ⟨ψ, hψb⟩ := sc_exists_emb σ hσ hfix _ hb0 hb _ hb2 _ hρ2
  obtain ⟨φ, hφ⟩ := sc_exists_iso σ h2 ψ _ hb0 hb
  set ρ := 2 * (r : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (t : F) with hρ
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρv; simp at hρv
  refine ⟨⟨φ, fun x => ?_, fun c => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | tmul x c =>
      have : sigR σ (v.adicCompletion F) (x ⊗ₜ[F] c) = σ x ⊗ₜ[F] c := rfl
      rw [this, hφ, hφ, hσ]; rfl
  · rw [hφ]; simp
  · have hle : intV E v ≤ ((v.adicCompletionIntegers F).toSubring.prod
        (v.adicCompletionIntegers F).toSubring).comap φ.toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
      · show φ ((algebraMap (𝓞 E) E y) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Subring.prod _ _
        have hσy : ∃ y' : 𝓞 E, (y' : E) = σ (y : E) :=
          ⟨⟨σ (y : E), (RingOfIntegers.isIntegral_coe y).map σ⟩, rfl⟩
        obtain ⟨y', hy'⟩ := hσy
        rw [hφ]
        refine ⟨?_, ?_⟩
        · simpa using sc_emb_int v ψ y
        · show (1 : v.adicCompletion F) * ψ (σ (algebraMap (𝓞 E) E y)) ∈ _
          rw [one_mul]
          have := sc_emb_int v ψ y'
          rwa [hy'] at this
      · show φ ((1 : E) ⊗ₜ[F] c) ∈ Subring.prod _ _
        rw [hφ]
        refine ⟨?_, ?_⟩ <;> simpa using hc
    exact hle hx
  · obtain ⟨h1, h2'⟩ := hx
    have hσa : ∃ y' : 𝓞 E, (y' : E) = σ (a : E) :=
      ⟨⟨σ (a : E), (RingOfIntegers.isIntegral_coe a).map σ⟩, rfl⟩
    obtain ⟨a', ha'⟩ := hσa
    have hρi : ρ⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hρv, inv_one]
    have he1 : ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F) - (1 : E) ⊗ₜ[F] ψ (σ a)) * ((1 : E) ⊗ₜ[F] ρ⁻¹) ∈ intV E v := by
      refine mul_mem (sub_mem (sc_left_mem v a) (sc_right_mem v _ ?_)) (sc_right_mem v _ hρi)
      rw [← ha']; exact sc_emb_int v ψ a'
    have hφe : φ (((a : E) ⊗ₜ[F] (1 : v.adicCompletion F) - (1 : E) ⊗ₜ[F] ψ (σ a)) * ((1 : E) ⊗ₜ[F] ρ⁻¹)) = (1, 0) := by
      rw [map_mul, map_sub, hφ, hφ, hφ]
      have hd : ψ (a : E) - ψ (σ a) = ρ := by rw [← map_sub, hψb]
      refine Prod.ext ?_ ?_
      · show (1 * ψ (a : E) - ψ (σ a) * ψ 1) * (ρ⁻¹ * ψ 1) = 1
        rw [map_one, one_mul, mul_one, mul_one, hd, mul_inv_cancel₀ hρ0]
      · show (1 * ψ (σ (a : E)) - ψ (σ a) * ψ (σ 1)) * (ρ⁻¹ * ψ (σ 1)) = 0
        rw [map_one, map_one]; ring
    obtain ⟨e₁, he1, hφe⟩ : ∃ e₁, e₁ ∈ intV E v ∧ φ e₁ = (1, 0) := ⟨_, he1, hφe⟩
    have hx : x = (1 : E) ⊗ₜ[F] (φ x).1 * e₁ + (1 : E) ⊗ₜ[F] (φ x).2 * (1 - e₁) := by
      apply φ.injective
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hφe, hφ, hφ]
      refine Prod.ext ?_ ?_
      · show (φ x).1 = (φ x).1 * ψ 1 * 1 + (φ x).2 * ψ 1 * (1 - 1)
        rw [map_one]; ring
      · show (φ x).2 = (φ x).1 * ψ (σ 1) * 0 + (φ x).2 * ψ (σ 1) * (1 - 0)
        rw [map_one, map_one]; ring
    rw [hx]
    exact add_mem (mul_mem (sc_right_mem v _ h1) he1)
      (mul_mem (sc_right_mem v _ h2') (sub_mem (one_mem _) he1))

def SplitCore.swap {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) : SplitCore σ v where
  φ := s.φ.trans RingEquiv.prodComm
  sig x := by
    show ((s.φ (sigR σ _ x)).2, (s.φ (sigR σ _ x)).1) = _
    rw [s.sig]; rfl
  alg c := by
    show ((s.φ _).2, (s.φ _).1) = _
    rw [s.alg]
  int x := by
    rw [s.int x, and_comm]; rfl

theorem sc_sig_fst {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (a : E) :
    (s.φ (σ a ⊗ₜ[F] (1 : v.adicCompletion F))).1 = (s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).2 := by
  have h := congrArg Prod.fst (s.sig (a ⊗ₜ[F] (1 : v.adicCompletion F)))
  simpa [sigR, swapR] using h

theorem sc_norm {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (a : E) (g : F)
    (h : a * σ a = algebraMap F E g) :
    (s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).1 * (s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).2 =
      algebraMap F (v.adicCompletion F) g := by
  have h1 : s.φ (a ⊗ₜ[F] (1 : v.adicCompletion F)) * s.φ (σ a ⊗ₜ[F] (1 : v.adicCompletion F)) =
      (algebraMap F (v.adicCompletion F) g, algebraMap F (v.adicCompletion F) g) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h, ← s.alg]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h2 := congrArg Prod.fst h1
  rw [Prod.fst_mul, sc_sig_fst] at h2
  exact h2

theorem sc_orient {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (a : 𝓞 E) (g : 𝓞 F)
    (hg : g ∈ v.asIdeal) (h : (a : E) * σ a = algebraMap F E (g : F)) :
    Nonempty (SplitAt σ v (σ (a : E))) := by
  have hn := sc_norm s (a : E) (g : F) h
  have hi := (s.int _).1 (sc_left_mem v a)
  have hv := sc_val_lt_one v g hg
  have hv' : Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 *
      Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1 := by
    rw [← map_mul, hn]; exact hv
  by_cases h2 : Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1
  · exact ⟨⟨s.φ, s.sig, s.alg, s.int, by rw [sc_sig_fst]; exact h2⟩⟩
  · have h2' : Valued.v (s.φ ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1 :=
      le_antisymm hi.2 (not_lt.1 h2)
    rw [h2', mul_one] at hv'
    refine ⟨⟨s.swap.φ, s.swap.sig, s.swap.alg, s.swap.int, ?_⟩⟩
    rw [sc_sig_fst]; exact hv'

end SC

section HostSplit

open Formalism.MainNotions.Gaps.LevGap

variable {R : Ranks} (H : Host R)


end HostSplit

section IwGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {k : ℕ} (P : Par F E k)

end IwGen

section IwHost

variable {R : Ranks} (H : Host R)

end IwHost

section FM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fm_card_residue (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  let f : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hs : Function.Surjective f := Examples₂.adicInt_residue_surj (K := F) v
  have hk : RingHom.ker f = v.asIdeal := by
    ext r
    rw [RingHom.mem_ker]
    simp only [f, RingHom.coe_comp, Function.comp_apply, IsLocalRing.residue_eq_zero_iff]
    rw [Examples₂.adicInt_mem_max_iff, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact v.valuation_lt_one_iff_mem r
  rw [← hk]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv).symm

theorem fm_incl_mem (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 E) :
    inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v := sc_left_mem v c

theorem fm_one_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] (c : v.adicCompletion F) ∈ intV E v := sc_right_mem v (c : v.adicCompletion F) c.2

theorem fm_mem_latS {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F)) (a : n → E)
    (y : n → E ⊗[F] v.adicCompletion F) :
    y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (LevGap.diagLat a) ↔
      ∀ i, ∃ c : intV E v, y i = inclE (F := F) (v.adicCompletion F) (a i) * (c : E ⊗[F] v.adicCompletion F) := by
  constructor
  · intro hy
    unfold latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x0, hx0, rfl⟩ := hx
      intro i
      obtain ⟨c, hc⟩ := LevGap.mem_diagLat.1 hx0 i
      exact ⟨⟨_, fm_incl_mem v c⟩, by simp only [hc, map_mul]⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨c, hc⟩ := hx i
      obtain ⟨d, hd⟩ := hy i
      exact ⟨c + d, by simp [hc, hd, mul_add]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨c, hc⟩ := hx i
      exact ⟨r * c, by
        show (r : E ⊗[F] _) * x i = _
        rw [hc]; push_cast; ring⟩
  · intro h
    choose c hc using h
    have : y = ∑ i, c i • (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single i (a i) : n → E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · show y j = (c j : E ⊗[F] v.adicCompletion F) *
          inclE (F := F) (v.adicCompletion F) ((Pi.single j (a j) : n → E) j)
        rw [Pi.single_eq_same, hc j, mul_comm]
      · intro b _ hb
        show (c b : E ⊗[F] v.adicCompletion F) *
          inclE (F := F) (v.adicCompletion F) ((Pi.single b (a b) : n → E) j) = 0
        rw [Pi.single_eq_of_ne hb.symm, map_zero, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, LevGap.single_mem_diagLat a i, rfl⟩)

variable {k : ℕ} (P : Par F E k)

end FM

section Final

variable {R : Ranks} (H : Host R)

end Final

end Formalism.MainNotions.Gaps.LG

end
