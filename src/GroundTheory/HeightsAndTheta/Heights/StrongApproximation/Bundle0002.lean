module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerAtPlace
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

namespace EichlerAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem sigV_inclV (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigV c v (inclV E v x) = inclV E v (c x) := by
  simp [sigV, inclV]

theorem sigA_inclA (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA]

theorem hf_single_incl (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u : Fin N → Kv E v) (y : Fin N → E) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (inclA F E ∘ y) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u (inclV E v ∘ y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_inclA, sigV_inclV, mul_assoc, ← map_mul (inclA F E), mul_assoc, ← map_mul (inclV E v), hsi]

theorem hf_single_single (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hmul : ∀ x y : Kv E v, singleV E v (x * y) = singleV E v x * singleV E v y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u w : Fin N → Kv E v) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (singleV E v ∘ w) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsig, hmul, hsi]

theorem embed_eich (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (e : Fin N → E) (u : Fin N → Kv E v) (c' : Kv E v) :
    embed E v (eich (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) u c') =
      eich (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (singleV E v ∘ u) (singleV E v c') := by
  have hw : ∀ j, ((J.map (inclV E v)) *ᵥ ((sigV c v).toRingHom ∘ (inclV E v ∘ e))) j =
      inclV E v ((J *ᵥ (c ∘ e)) j) := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sigV_inclV, map_mul]
  have hwA : ∀ j, ((J.map (inclA F E)) *ᵥ (sigA c ∘ (inclA F E ∘ e))) j =
      inclA F E ((J *ᵥ (c ∘ e)) j) := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply, sigA_inclA,
      map_mul]
  have hz : ∀ j, ((J.map (inclA F E)) *ᵥ (sigA c ∘ (singleV E v ∘ u))) j =
      singleV E v (((J.map (inclV E v)) *ᵥ ((sigV c v).toRingHom ∘ u)) j) := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsig, mul_comm (inclV E v (J j k)), hsi, mul_comm]
  ext i j
  simp only [embed, eich, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
    vecMulVec_apply, Function.comp_apply, hw, hwA, hz, smul_eq_mul, map_add, map_sub]
  rw [hsi, mul_comm (inclV E v (e i)), hsi, ← map_mul (inclV E v), hsi, map_mul]
  ring

theorem proof (hPM : PlaceMaps.Statement) : EichlerAtPlace.Statement := by
  intro F E _ _ _ _ _ c hF hc v N J
  obtain ⟨-, hv⟩ := hPM F E c hF hc
  obtain ⟨-, -, hmul, -, hsi, hsig, -⟩ := hv v
  have key := fun e u c' => embed_eich c v hsi hsig J e u c'
  refine ⟨key, fun _ e f _ _ _ g hg => ?_⟩
  have along : ∀ a b : Fin N → E,
      g ∈ eichAlong (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ a) (inclV E v ∘ b) →
      embed E v g ∈ eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ a) (inclA F E ∘ b) := by
    rintro a b ⟨u, c', hua, hub, hc', rfl⟩
    refine ⟨singleV E v ∘ u, singleV E v c', ?_, ?_, ?_, key a u c'⟩
    · rw [hf_single_incl c v hsi J, hua, map_zero]
    · rw [hf_single_incl c v hsi J, hub, map_zero]
    · rw [hf_single_single c v hsi hmul hsig J, hsig, ← map_add (f := _), ← map_add (f := _)]
      exact (congrArg (singleV E v) hc').trans (map_zero _)
  rcases hg with hg | hg
  · exact Or.inl (along e f hg)
  · exact Or.inr (along f e hg)

end EichlerAtPlace

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PEichlerDense
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

namespace EichlerDense

section Ring

variable {R : Type*} [CommRing R] {N : ℕ}

def param (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) : Matrix (Fin N) (Fin N) R :=
  eich σ J e (perpProj σ J e f p.1)
    (p.2 - σ p.2 - κ * hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))

theorem hf_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (x y : Fin N → R) :
    hf σ' (J.map φ) (φ ∘ x) (φ ∘ y) = φ (hf σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hf, map_sum, map_mul, hφ]

theorem eich_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e u : Fin N → R) (c : R) :
    (eich σ J e u c).map φ = eich σ' (J.map φ) (φ ∘ e) (φ ∘ u) (φ c) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [eich, vecMulVec_apply, mulVec, dotProduct, map_sum, hφ, Matrix.one_apply, apply_ite φ]

theorem param_map {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) :
    (param σ J e f κ p).map φ = param σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ κ) (φ ∘ p.1, φ p.2) := by
  have hP : φ ∘ perpProj σ J e f p.1 = perpProj σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ ∘ p.1) := by
    funext i
    simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      map_mul, hf_map σ σ' φ hφ]
  rw [param, param, eich_map σ σ' φ hφ, ← hP, map_sub, map_sub, map_mul, hφ, hf_map σ σ' φ hφ]

variable {σ : R →+* R} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin N) (Fin N) R} (hJ : Jᵀ = J.map σ)
  {e f : Fin N → R} {κ : R} (hκ : κ + κ = 1) (hσκ : σ κ = κ)
include hσ hJ hκ hσκ

theorem param_mem
    (hP : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0)
    (p : (Fin N → R) × R) : param σ J e f κ p ∈ eichAlong σ J e f := by
  refine ⟨perpProj σ J e f p.1, _, (hP p.1).1, (hP p.1).2, ?_, rfl⟩
  have hh := hf_symm hσ hJ (perpProj σ J e f p.1) (perpProj σ J e f p.1)
  rw [map_sub, map_sub, map_mul, hσ, hσκ, hh]
  linear_combination (-(hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))) * hκ


omit hσ hJ in
theorem eq_param
    (hfix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u)
    {M : Matrix (Fin N) (Fin N) R} (hM : M ∈ eichAlong σ J e f) : ∃ p, M = param σ J e f κ p := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨(u, κ * c), ?_⟩
  simp only [param, hfix u hue huf]
  congr 1
  rw [map_mul, hσκ]
  linear_combination κ * hc - c * hκ

end Ring

section Top

variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}

theorem continuous_hf (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) {x y : X → Fin N → S}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => hf σ J (x t) (y t) := by
  unfold hf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_apply i).comp hx).mul continuous_const).mul
    (hσ.comp ((continuous_apply j).comp hy))

theorem continuous_eich (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) (e : Fin N → S)
    {g : X → Fin N → S} {k : X → S} (hg : Continuous g) (hk : Continuous k) :
    Continuous fun t => eich σ J e (g t) (k t) := by
  have hσg : Continuous fun t => σ ∘ g t :=
    continuous_pi fun i => hσ.comp ((continuous_apply i).comp hg)
  unfold eich
  fun_prop

end Top

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem c_invol (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair (Ne.symm hc)]
    exact Finset.card_le_univ _
  have hsq : c ^ 2 = 1 := by
    rw [← le_antisymm hle hge]
    exact pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this

omit [NumberField E] in
theorem sigA_inclA' (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

omit [NumberField E] in
theorem sigA_invol' (c : E ≃ₐ[F] E) (hc2 : ∀ x, c (c x) = x) (a : AE F E) :
    sigA c (sigA c a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigA, Algebra.TensorProduct.map_tmul, hc2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem along (hT : AETopologicalRing.Statement) (hD : EDenseInAE.Statement)
    (hO : OrthProjection.Statement) (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (hJ : Jᵀ = J.map c) (e f : Fin N → E)
    (he : hf c.toRingHom J e e = 0) (hff : hf c.toRingHom J f f = 0) (hef : hf c.toRingHom J e f = 1)
    [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)] :
    eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆
      closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
        eichAlong c.toRingHom J e f) := by
  obtain ⟨hring, hσc, -, -⟩ := hT F E c h2 hc
  have hc2 : ∀ x, c.toRingHom (c.toRingHom x) = x := c_invol c h2 hc
  have hσA : ∀ x, sigA c (sigA c x) = x := sigA_invol' c (c_invol c h2 hc)
  have hφ : ∀ x, inclA F E (c.toRingHom x) = sigA c (inclA F E x) := fun x => (sigA_inclA' c x).symm
  have hJA : (J.map (inclA F E))ᵀ = (J.map (inclA F E)).map (sigA c) := by
    ext i j
    have := congrFun (congrFun hJ i) j
    simp only [transpose_apply, map_apply] at this ⊢
    rw [this, sigA_inclA']
  have hκ : (2 : E)⁻¹ + (2 : E)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  have hcκ : c.toRingHom (2 : E)⁻¹ = (2 : E)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hκA : inclA F E (2 : E)⁻¹ + inclA F E (2 : E)⁻¹ = 1 := by rw [← map_add (f := _), hκ, map_one]
  have hσκA : sigA c (inclA F E (2 : E)⁻¹) = inclA F E (2 : E)⁻¹ := by rw [← hφ, hcκ]
  have heA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ e) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, he, map_zero]
  have hffA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ f) (inclA F E ∘ f) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hff, map_zero]
  have hefA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) = 1 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hef, map_one]
  obtain ⟨hP1, hP2⟩ := hO
  obtain ⟨-, -, hPE, -⟩ := hP1 E c.toRingHom hc2 N J hJ e f he hff hef
  obtain ⟨-, -, -, hfixA⟩ := hP1 (AE F E) (sigA c) hσA N (J.map (inclA F E)) hJA _ _ heA hffA hefA
  obtain ⟨hPcont, -⟩ := hP2 F E c h2 hc N J e f
  have hcont : Continuous (param (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f)
      (inclA F E (2 : E)⁻¹)) := by
    have hu : Continuous fun p : (Fin N → AE F E) × AE F E =>
        perpProj (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) p.1 :=
      hPcont.comp continuous_fst
    exact continuous_eich hσc _ _ hu ((continuous_snd.sub (hσc.comp continuous_snd)).sub
      (continuous_const.mul (continuous_hf hσc _ hu hu)))
  have hdense : DenseRange (Prod.map (Pi.map fun _ : Fin N => inclA F E) (inclA F E)) :=
    (DenseRange.piMap fun _ => hD F E c h2 hc).prodMap (hD F E c h2 hc)
  intro M hM
  obtain ⟨p, rfl⟩ := eq_param hκA hσκA hfixA hM
  refine map_mem_closure hcont (hdense p) ?_
  rintro _ ⟨⟨w, t⟩, rfl⟩
  exact ⟨param c.toRingHom J e f (2 : E)⁻¹ (w, t), param_mem hc2 hJ hκ hcκ hPE (w, t),
    param_map c.toRingHom (sigA c) (inclA F E) hφ J e f (2 : E)⁻¹ (w, t)⟩

end Field

end EichlerDense

theorem EichlerDense.proof (h₁ : AETopologicalRing.Statement) (h₂ : EDenseInAE.Statement)
    (h₃ : OrthProjection.Statement) : EichlerDense.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ e f he hff hef _ _
  have hfe : hf c.toRingHom J f e = 1 :=
    hf_fe (fun x => EichlerDense.c_invol c h2 hc x) hJ he hff hef
  exact ⟨EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ e f he hff hef,
    EichlerDense.along h₁ h₂ h₃ c h2 hc N J hJ f e hff he hfe⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalInClosure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

theorem LocalInClosure.proof (hHP : HypPairExists.Statement) (hCl : ClosureIsSubmonoid.Statement)
    (hLR : LocalRingHypotheses.Statement) (hPM : PlaceMaps.Statement)
    (hEA : EichlerAtPlace.Statement) : LocalInClosure.Statement := by
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet ⟨e, he0, hee⟩ _ _ v g hg
  obtain ⟨hinv, hfix, hrank2, hred, h2, hcomm, hform⟩ := hLR F E c hrk hc v

  have hinj : Function.Injective (inclV E v) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (v.adicCompletion F)).injective
  have hcinv : ∀ x, c.toRingHom (c.toRingHom x) = x := fun x =>
    hinj (by
      change inclV E v (c (c x)) = inclV E v x
      rw [← hcomm, ← hcomm, hinv])

  obtain ⟨f, hff, hef⟩ := hHP E c.toRingHom hcinv two_ne_zero N J hJ hdet e he0 hee
  obtain ⟨-, h1, hmul, heich⟩ := hCl F E c hrk hc N J hJ hdet e f hee hff hef

  have hJv : (J.map (inclV E v))ᵀ = (J.map (inclV E v)).map (sigV c v) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [hcomm]
    have h := Matrix.ext_iff.mpr hJ i j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h
    rw [h]
  have hdetv : IsUnit (J.map (inclV E v)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hzero : ∀ x y : Fin N → E, hf c.toRingHom J x y = 0 →
      hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ x) (inclV E v ∘ y) = 0 :=
    fun x y h => by rw [← hform, h, map_zero]
  have hefv : hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) (inclV E v ∘ f) = 1 := by
    rw [← hform, hef, map_one]
  have hg' := hg
  rw [locGen _ _ (sigV c v) hinv hfix hrank2 hred h2 N _ hJv hdetv _ _ (hzero e e hee)
    (hzero f f hff) hefv] at hg'
  clear hg

  obtain ⟨-, hPv⟩ := hPM F E c hrk hc
  obtain ⟨-, -, -, -, -, -, -, -, hPN⟩ := hPv v
  obtain ⟨hemb1, hembmul, -⟩ := hPN N
  induction hg' using Submonoid.closure_induction with
  | mem x hx => exact heich ((hEA F E c hrk hc v N J).2 hJ e f hee hff hef x hx)
  | one => rw [hemb1]; exact h1
  | mul x y _ _ hx hy => rw [hembmul]; exact hmul _ hx _ hy

end StrongApprox

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PLocalRingHypotheses
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

theorem LocalRingHypotheses.proof : LocalRingHypotheses.Statement := by
  intro F E _ _ _ _ _ c h2 hc v
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2

  have hcc : ∀ x, c (c x) = x := by
    have hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
    have hpos := orderOf_pos c
    have hle : orderOf c ≤ Fintype.card (E ≃ₐ[F] E) := orderOf_le_card_univ
    have hne : orderOf c ≠ 1 := fun h => hc (orderOf_eq_one_iff.mp h)
    have ho : orderOf c = 2 := by omega
    intro x
    have h := pow_orderOf_eq_one c
    rw [ho, pow_two] at h
    exact DFunLike.congr_fun h x
  have htmul : ∀ (a : v.adicCompletion F) (b : E), sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := by
    intro a b
    simp [sigV]
  have hsig_incl : ∀ x : E, sigV c v (inclV E v x) = inclV E v (c x) := by
    intro x
    simp [inclV, htmul]

  have hinv : ∀ x, sigV c v (sigV c v x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [htmul, htmul, hcc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

  obtain ⟨α, hα⟩ : ∃ α, c α ≠ α := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  set β : E := α - c α with hβdef
  have hcβ : c β = -β := by simp [hβdef, hcc]
  have hβ0 : β ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h2k : (2 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact fun h => h2F ((algebraMap F (v.adicCompletion F)).injective (h.trans (map_zero _).symm))

  set t : Kv E v := (1 : v.adicCompletion F) ⊗ₜ β with htdef
  have ht : IsUnit t :=
    (isUnit_iff_ne_zero.mpr hβ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] Kv E v)
  have hσt : sigV c v t = -t := by rw [htdef, htmul, hcβ, TensorProduct.tmul_neg]

  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have hsu' : algebraMap F E s + algebraMap F E u * β = 0 := by
      simpa [Algebra.smul_def] using hsu
    have hc' : algebraMap F E s + algebraMap F E u * -β = 0 := by
      have := congrArg c hsu'
      rwa [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcβ, map_zero] at this
    have hs : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hsu' + hc'
    have hs0 : s = 0 := by
      have := (algebraMap F E).injective (hs.trans (map_zero _).symm)
      exact (mul_eq_zero.mp this).resolve_left h2F
    subst hs0
    rw [map_zero, zero_add] at hsu'
    have hu : algebraMap F E u = 0 := (mul_eq_zero.mp hsu').resolve_right hβ0
    exact ⟨rfl, (algebraMap F E).injective (hu.trans (map_zero _).symm)⟩
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ∀ i, B i = ![(1 : E), β] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  let BK : Module.Basis (Fin 2) (v.adicCompletion F) (Kv E v) := Algebra.TensorProduct.basis _ B

  have hdecomp : ∀ x : Kv E v, ∃ a b : v.adicCompletion F,
      x = algebraMap _ _ a + algebraMap _ _ b * t := by
    intro x
    refine ⟨BK.repr x 0, BK.repr x 1, ?_⟩
    conv_lhs => rw [← BK.sum_repr x]
    rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]
    simp [BK, Algebra.TensorProduct.basis_apply, hB, htdef]
  have hinj : Function.Injective (algebraMap (v.adicCompletion F) (Kv E v)) := by
    have : Nontrivial (Kv E v) := ⟨⟨0, t, (ht.ne_zero).symm⟩⟩
    exact (algebraMap (v.adicCompletion F) (Kv E v)).injective

  have hfix : ∀ x, sigV c v x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion F) (Kv E v)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, b, rfl⟩ := hdecomp x
      rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσt] at hx
      have h2b : algebraMap _ (Kv E v) (2 * b) * t = 0 := by
        rw [map_mul, map_ofNat]
        linear_combination -hx
      have hb : b = 0 := by
        have := (ht.mul_left_eq_zero).mp h2b
        rw [← map_zero (algebraMap (v.adicCompletion F) (Kv E v))] at this
        exact (mul_eq_zero.mp (hinj this)).resolve_left h2k
      exact ⟨a, by simp [hb]⟩
    · rintro ⟨a, rfl⟩
      exact AlgHom.commutes _ a

  have hrank : Module.finrank (v.adicCompletion F) (Kv E v) = 2 := by
    rw [Module.finrank_baseChange, h2]

  have hred : IsReduced (Kv E v) := by
    have : Algebra.IsSeparable F E := inferInstance
    have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
    exact Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion F) (Kv E v)
  refine ⟨hinv, hfix, hrank, hred, h2k, hsig_incl, ?_⟩
  intro N J x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hsig_incl]
  rfl

end GroundTheory.Heights₂.Heights.StrongApprox
end
end

