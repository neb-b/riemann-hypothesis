module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibility
section
open Module

namespace GlobalTheory

theorem exists_mem_sub_orth_of_finiteDimensional {E : Type} [AddCommGroup E] [Module ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : Submodule ℂ E) [FiniteDimensional ℂ T]
    (hT : ∀ t ∈ T, b t t = 0 → t = 0) (ψ : E) : ∃ s ∈ T, ∀ t ∈ T, b t (ψ - s) = 0 := by
  let bs := Module.finBasis ℂ T
  let F : E →ₗ[ℂ] (Fin (finrank ℂ T) → ℂ) := LinearMap.pi fun i => b (bs i : E)
  have key : ∀ x, F x = 0 → ∀ t ∈ T, b t x = 0 := by
    intro x hx t ht
    have h1 : (b.flip x) ∘ₛₗ T.subtype = 0 :=
      bs.ext fun i => by simpa [F] using congrFun hx i
    exact LinearMap.congr_fun h1 ⟨t, ht⟩
  have hinj : Function.Injective (F ∘ₗ T.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext (hT z z.2 (key z hz z z.2))
  have hsurj : Function.Surjective (F ∘ₗ T.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨z, hz⟩ := hsurj (F ψ)
  refine ⟨z, z.2, key (ψ - z) ?_⟩
  rw [map_sub, ← hz]
  simp

theorem abstract_complete_reducibility :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  classical
  intro E _ _ P hInf N hN b hpos _hherm hperp e he hidem hsa hfin ψ hψN hψe
  let S := ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A
  show ψ ∈ S
  let V := N.map e
  have hVN : V ≤ N := by rintro _ ⟨x, hx, rfl⟩; exact he N le_rfl hN x hx
  have heV : ∀ v ∈ V, e v = v := by rintro _ ⟨x, hx, rfl⟩; exact hidem x hx
  have hψV : ψ ∈ V := ⟨ψ, hψN, hψe⟩
  have hIrrS : ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → A ≤ S :=
    fun A hA => le_iSup₂_of_le (f := fun A (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) => A) A hA le_rfl
  have hpos0 : ∀ x ∈ N, b x x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have := hpos x hx hne
    rw [h0] at this
    simp at this
  have hGen : ∀ x : E, ∃ G : Submodule ℂ E, x ∈ G ∧ P G ∧ ∀ A, x ∈ A → P A → G ≤ A := fun x =>
    ⟨sInf {A | x ∈ A ∧ P A}, Submodule.mem_sInf.2 fun A hA => hA.1, hInf _ fun A hA => hA.2,
      fun A hx hA => sInf_le ⟨hx, hA⟩⟩
  let C : Submodule ℂ E := sInf (insert N {X | ∃ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) ∧ X = N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)})
  have hCP : P C := by
    apply hInf
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hN
    · exact hperp A hA.1 hA.2.1
  have hCorth : ∀ x ∈ C, ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0 := by
    intro x hx A hA a ha
    have : x ∈ N ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
      Submodule.mem_sInf.1 hx _ (Set.mem_insert_of_mem _ ⟨A, hA, rfl⟩)
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this.2 a ha
  have hCmem : ∀ x ∈ N, (∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0) → x ∈ C := by
    intro x hx h
    refine Submodule.mem_sInf.2 ?_
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hx
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      exact ⟨hx, fun a ha => h A hA a ha⟩
  have hfinT : FiniteDimensional ℂ ↥(S ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hsT, hsorth⟩ := exists_mem_sub_orth_of_finiteDimensional b (S ⊓ V)
    (fun t ht h0 => hpos0 t (hVN ht.2) h0) ψ
  have hcV : ψ - s ∈ V := V.sub_mem hψV hsT.2
  have hcC : ψ - s ∈ C := by
    refine hCmem _ (hVN hcV) fun A hA a ha => ?_
    have haN : a ∈ N := hA.1 ha
    have heaT : e a ∈ S ⊓ V := ⟨hIrrS A hA (he A hA.1 hA.2.1 a ha), ⟨a, haN, rfl⟩⟩
    rw [← heV _ hcV, ← hsa a haN _ (hVN hcV)]
    exact hsorth _ heaT
  suffices hc0 : ψ - s = 0 by
    rw [sub_eq_zero] at hc0
    rw [hc0]
    exact hsT.1
  by_contra hc0
  obtain ⟨D, hcD, hDP, hDmin⟩ := hGen (ψ - s)
  have hDC : D ≤ C := hDmin C hcC hCP
  have hDN : D ≤ N := hDmin N (hVN hcV) hN
  have hex : ∃ n, ∃ B : Submodule ℂ E, B ≤ D ∧ P B ∧ B ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(B ⊓ V) = n :=
    ⟨_, D, le_rfl, hDP, (Submodule.ne_bot_iff _).2 ⟨ψ - s, ⟨hcD, hcV⟩, hc0⟩, rfl⟩
  obtain ⟨B, hBD, hBP, hBV, hBn⟩ := Nat.find_spec hex
  have hmin : ∀ B₁ : Submodule ℂ E, B₁ ≤ D → P B₁ → B₁ ⊓ V ≠ ⊥ →
      Nat.find hex ≤ finrank ℂ ↥(B₁ ⊓ V) :=
    fun B₁ h1 h2 h3 => Nat.find_min' hex ⟨B₁, h1, h2, h3, rfl⟩
  obtain ⟨β, hβBV, hβ0⟩ := (Submodule.ne_bot_iff _).1 hBV
  obtain ⟨G, hβG, hGP, hGmin⟩ := hGen β
  have hGB : G ≤ B := hGmin B hβBV.1 hBP
  have hGN : G ≤ N := hGB.trans (hBD.trans hDN)
  have hβV : β ∈ V := hβBV.2
  have hβe : e β = β := heV β hβV
  have hGirr : G ≤ N ∧ P G ∧ G ≠ ⊥ ∧ ∀ B'' : Submodule ℂ E, B'' ≤ G → P B'' → B'' = ⊥ ∨ B'' = G := by
    refine ⟨hGN, hGP, (Submodule.ne_bot_iff _).2 ⟨β, hβG, hβ0⟩, fun B'' hle hP => ?_⟩
    have hB''N : B'' ≤ N := hle.trans hGN
    by_cases hV'' : B'' ⊓ V = ⊥
    · left
      have hey : ∀ y ∈ B'', e y = 0 := by
        intro y hy
        have : e y ∈ B'' ⊓ V := ⟨he B'' hB''N hP y hy, ⟨y, hB''N hy, rfl⟩⟩
        rw [hV''] at this
        exact (Submodule.mem_bot ℂ).1 this
      have hβperp : β ∈ N ⊓ ⨅ a ∈ B'', LinearMap.ker (b a) := by
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
        refine ⟨hVN hβV, fun y hy => ?_⟩
        rw [← hβe, ← hsa y (hB''N hy) β (hVN hβV), hey y hy, map_zero, LinearMap.zero_apply]
      have hGperp := hGmin _ hβperp (hperp B'' hB''N hP)
      rw [eq_bot_iff]
      intro y hy
      have hyp := hGperp (hle hy)
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyp
      exact (Submodule.mem_bot ℂ).2 (hpos0 y (hB''N hy) (hyp.2 y hy))
    · right
      have hle' : B'' ⊓ V ≤ B ⊓ V := inf_le_inf_right _ (hle.trans hGB)
      have hfinBV : FiniteDimensional ℂ ↥(B ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
      have heq : B'' ⊓ V = B ⊓ V := Submodule.eq_of_le_of_finrank_le hle' (by
        rw [hBn]; exact hmin B'' (hle.trans (hGB.trans hBD)) hP hV'')
      have hβB'' : β ∈ B'' := by
        have h2 := hβBV
        rw [← heq] at h2
        exact h2.1
      exact le_antisymm hle (hGmin B'' hβB'' hP)
  exact hβ0 (hpos0 β (hVN hβV) (hCorth β (hDC (hBD hβBV.1)) G hGirr β hβG))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsField
section
namespace GlobalTheory.Twist

theorem addChar_eq_mulShift_unit_of_isField :
    ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 →
      ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  intro κf _ _ hF ψ φ hψ _
  classical
  let _ : Field κf := hF.toField
  have _ : Fintype κf := Fintype.ofFinite κf

  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)

  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨a, ha⟩ := hbij.2 φ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ‹φ ≠ 1› (by rw [← ha, AddChar.mulShift_zero])
  refine ⟨Units.mk0 a ha0, fun t => ?_⟩
  rw [← ha, AddChar.mulShift_apply, Units.val_mk0]

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AffineChangeFundamentalDomainMeanPeriodic
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.AffineMean

theorem affine_fundamentalDomain_mean :
    ∀ (g : ℕ) (Λ' Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
      (c : Fin g → ℂ) (f : (Fin g → ℂ) → ℝ), Countable Λ' → (∀ z, L z ∈ Λ' ↔ z ∈ Λ₁) →
      IsAddFundamentalDomain Λ' Fd' volume → (∀ a ∈ Λ', ∀ z, f (z + a) = f z) →
      (∫ z in Fd', f z) / (volume Fd').toReal = 1 →
      IsAddFundamentalDomain Λ₁ ((fun z => L z + c) ⁻¹' Fd') volume ∧
        (∫ z in (fun z => L z + c) ⁻¹' Fd', f (L z + c)) / (volume ((fun z => L z + c) ⁻¹' Fd')).toReal = 1 := by
  intro g Λ' Λ₁ Fd' L c f hcount hΛ hF' _ hmean
  let L' : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := L.restrictScalars ℝ
  have hL : ∀ z, L' z = L z := fun z => rfl
  let e : (Fin g → ℂ) ≃ᵐ (Fin g → ℂ) :=
    (L'.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addRight c)).toMeasurableEquiv
  have he : ∀ z, e z = L z + c := fun z => rfl
  have hpre : (fun z => L z + c) ⁻¹' Fd' = e ⁻¹' Fd' := rfl
  have hd : LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ≠ 0 := (LinearEquiv.isUnit_det' L').ne_zero
  have hmapL : Measure.map L' volume =
      ENNReal.ofReal |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hc : 0 < |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| := abs_pos.2 (inv_ne_zero hd)
  generalize |(LinearMap.det (L' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| = k at hmapL hc
  have hmap : Measure.map e volume = ENNReal.ofReal k • volume := by
    have h1 : (e : (Fin g → ℂ) → (Fin g → ℂ)) = (fun z => z + c) ∘ (L' : (Fin g → ℂ) → (Fin g → ℂ)) := rfl
    have hLm : Measurable (L' : (Fin g → ℂ) → (Fin g → ℂ)) :=
      L'.toContinuousLinearEquiv.continuous.measurable
    rw [h1, ← Measure.map_map (measurable_add_const c) hLm, hmapL, Measure.map_smul, map_add_right_eq_self]
    exact (measurable_add_const c).aemeasurable
  have hq : Measure.QuasiMeasurePreserving e volume volume :=
    ⟨e.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let ε : Λ' → Λ₁ := fun a => ⟨L.symm a, (hΛ _).1 (by rw [L.apply_symm_apply]; exact a.2)⟩
  have hε : Function.Bijective ε :=
    ⟨fun a b hab => Subtype.ext (L.symm.injective (congrArg Subtype.val hab)),
      fun a => ⟨⟨L a, (hΛ _).2 a.2⟩, Subtype.ext (L.symm_apply_apply _)⟩⟩
  have hF2 : IsAddFundamentalDomain Λ₁ (e ⁻¹' Fd') volume :=
    hF'.preimage_of_equiv hq hε fun a z => by
      change L (L.symm (a : Fin g → ℂ) + z) + c = (a : Fin g → ℂ) + (L z + c)
      rw [map_add (f := _), L.apply_symm_apply, add_assoc]
  have i2 : ∫ z in e ⁻¹' Fd', f (e z) = k * ∫ z in Fd', f z := by
    have := setIntegral_map_equiv (μ := volume) e f Fd'
    rw [hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at this
    exact this.symm
  have i3 : (volume (e ⁻¹' Fd')).toReal = k * (volume Fd').toReal := by
    rw [← e.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  refine ⟨hpre ▸ hF2, ?_⟩
  rw [hpre]
  have i2' : ∫ z in e ⁻¹' Fd', f (L z + c) = k * ∫ z in Fd', f z := i2
  rw [i2', i3, mul_div_mul_left _ _ hc.ne', hmean]

end GlobalTheory.AffineMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgHomEqEval
section
namespace GlobalTheory.AlgHomEqEval

theorem algHom_eq_eval : ∀ {K : Type} [inst : Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K), ∃ (p : P), ∀ (z : P → K), (θ : (P → K) → K) z = z p := by
  intro K _ P _ _ θ
  have hsum : ∑ p, (Pi.single p (1:K) : P → K) = 1 := by
    ext x; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∑ p, θ (Pi.single p 1) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum, map_one]
  obtain ⟨p, -, hp⟩ : ∃ p ∈ Finset.univ, θ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Finset.sum_eq_zero h] at h1
    exact zero_ne_one h1
  refine ⟨p, fun z => ?_⟩
  have hz : z * Pi.single p 1 = (algebraMap K (P → K) (z p)) * Pi.single p 1 := by
    ext x
    by_cases hx : x = p
    · subst hx; simp
    · simp [Pi.single_apply, hx]
  have h2 := congrArg θ hz
  rw [map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h2
  exact mul_right_cancel₀ hp h2

end GlobalTheory.AlgHomEqEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlot
section
open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem bilinear_bound_of_dense_right : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  intro E _ _ _ _ _ _ p hp X₁ X₂ _ _ _ _ j₁ j₂ hinj hcl D₂ hdense F h₁ h₂ b i
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : PolynormableSpace ℂ E := hp.toPolynormableSpace
  haveI : IsTopologicalAddGroup E := inferInstance
  set Y : Submodule ℂ E := LinearMap.range j₁ with hYdef
  have hYc : IsClosed (Y : Set E) := by simpa [Y, LinearMap.coe_range] using hcl
  haveI : IsUniformAddGroup Y := Y.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace Y := hYc.completeSpace_coe
  haveI : FirstCountableTopology Y := Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : (𝓤 Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BarrelledSpace ℂ Y := inferInstance
  let e : X₁ ≃ₗ[ℂ] Y := LinearEquiv.ofInjective j₁ hinj
  have he : ∀ w, ((e w : Y) : E) = j₁ w := fun w => rfl

  let gl : D₂ → Y →ₗ[ℂ] E := fun a => (F.flip (a : X₂)).comp e.symm.toLinearMap
  have hgl : ∀ a y, gl a y = F (e.symm y) a := fun a y => rfl
  have hgc : ∀ a, Continuous (gl a) := by
    intro a
    refine hp.continuous_of_continuous_comp (gl a) fun k => ?_
    obtain ⟨q, hq, hle⟩ := h₂ a a.2 k
    refine Seminorm.continuous_of_le (q := q.comp Y.subtype) (hq.comp continuous_subtype_val) ?_
    intro y
    have := hle (e.symm y)
    rw [← he, e.apply_symm_apply] at this
    simpa [Seminorm.comp_apply, hgl] using this
  let g : D₂ → Y →L[ℂ] E := fun a => ⟨gl a, hgc a⟩
  let l : Filter D₂ := Filter.comap (fun a : D₂ => j₂ a) (𝓝 (j₂ b))
  haveI : l.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, htx, ⟨a, ha, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense b) t ht
    exact ⟨⟨a, ha⟩, htx⟩
  have hT : Tendsto (fun a y => g a y) l (𝓝 fun y => F (e.symm y) b) := by
    rw [tendsto_pi_nhds]
    intro y
    rw [hp.tendsto_nhds]
    intro k ε hε
    obtain ⟨q, hq, hle⟩ := h₁ (e.symm y) k
    have ht : Tendsto (fun a : D₂ => q (j₂ a - j₂ b)) l (𝓝 0) := by
      have h0 : Tendsto (fun a : D₂ => j₂ a - j₂ b) l (𝓝 (j₂ b - j₂ b)) :=
        tendsto_comap.sub tendsto_const_nhds
      have := (hq.tendsto _).comp h0
      simpa [Function.comp_def] using this
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with a ha
    calc p k (g a y - F (e.symm y) b) = p k (F (e.symm y) ((a : X₂) - b)) := by
          simp [g, hgl, map_sub]
      _ ≤ q (j₂ ((a : X₂) - b)) := hle _
      _ < ε := by simpa [map_sub] using ha
  let G : Y →L[ℂ] E := continuousLinearMapOfTendsto g hT
  have hG : ∀ y, G y = F (e.symm y) b := fun y => rfl
  have hr : Continuous ((p i).comp G.toLinearMap) := (hp.continuous_seminorm i).comp G.continuous
  obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing hr (f := Y.subtype) .subtypeVal
  refine ⟨q, hq, fun w => ?_⟩
  have := hle (e w)
  simpa [Seminorm.comp_apply, hG, he] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardLeOfSeparated
section
open MeasureTheory

namespace GlobalTheory.SeparatedSetCardBound

theorem card_le_of_separated {G E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : G → E) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (T : Finset G)
    (hT : ∀ h ∈ T, ‖φ h‖ ≤ R) (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖) :
    (T.card : ℝ) ≤ ((R + r) / r) ^ Module.finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  haveI := hμ
  set d := Module.finrank ℝ E
  have hdisj : Set.PairwiseDisjoint (T : Set G) (fun h => Metric.ball (φ h) r) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_iff]
    rintro z ⟨hza, hzb⟩
    have hs := hsep a ha b hb hab
    rw [Metric.mem_ball, dist_eq_norm] at hza hzb
    have h3 : ‖φ a - φ b‖ ≤ ‖z - φ b‖ + ‖z - φ a‖ := by
      calc ‖φ a - φ b‖ = ‖(z - φ b) - (z - φ a)‖ := by congr 1; abel
        _ ≤ ‖z - φ b‖ + ‖z - φ a‖ := norm_sub_le _ _
    linarith
  have hsub : (⋃ h ∈ T, Metric.ball (φ h) r) ⊆ Metric.ball (0 : E) (R + r) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨h, hh, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have h4 : ‖z‖ ≤ ‖z - φ h‖ + ‖φ h‖ := by
      calc ‖z‖ = ‖(z - φ h) + φ h‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - φ h‖ + ‖φ h‖ := norm_add_le _ _
    linarith [hT h hh]
  have hle : μ (⋃ h ∈ T, Metric.ball (φ h) r) ≤ μ (Metric.ball (0 : E) (R + r)) := measure_mono hsub
  rw [measure_biUnion_finset hdisj (fun h _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < R + r),
    Finset.sum_const, nsmul_eq_mul] at hle
  have hB0 : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hrd : 0 < r ^ d := pow_pos hr d
  rw [div_pow, le_div_iff₀ hrd]
  exact hle

theorem main : ∀ {G E : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : MeasureTheory.Measure G) [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.SFinite μ] [inst_8 : NormedAddCommGroup E] [inst_9 : NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E), Continuous φ → ∀ (W : Set G) (R r : ℝ), (0 : ℝ) ≤ R → (0 : ℝ) < r → (∀ (g h : G), ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ (2 : ℝ) * r → h⁻¹ * g ∈ W) → (μ : Set G → ENNReal) {g : G | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * (μ : Set G → ENNReal) W := by
  intro G E _ _ _ _ _ _ μ _ _ _ _ _ φ _ W R r hR hr hW
  classical
  let P : Finset G → Prop := fun T =>
    (∀ h ∈ T, ‖φ h‖ ≤ R) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖
  let A : Set ℕ := {n | ∃ T, P T ∧ T.card = n}
  have hA0 : A.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hAb : BddAbove A := by
    refine ⟨⌈((R + r) / r) ^ Module.finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨T, hT, rfl⟩
    have h1 := card_le_of_separated φ R r hR hr T hT.1 hT.2
    have h2 := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨T, hT, hTc⟩ := Nat.sSup_mem hA0 hAb
  have hcover : {g : G | ‖φ g‖ ≤ R} ⊆ ⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W := by
    intro g hg
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hne
    have hg' : ‖φ g‖ ≤ R := hg
    have hgT : g ∉ T := fun hgT => hne g hgT (hW g g hg' (by simp; positivity))
    have far : ∀ h ∈ T, 2 * r < ‖φ g - φ h‖ := by
      intro h hh
      by_contra hle
      push_neg at hle
      exact hne h hh (hW g h (hT.1 h hh) hle)
    have hP : P (insert g T) := by
      refine ⟨?_, ?_⟩
      · intro h hh
        rw [Finset.mem_insert] at hh
        rcases hh with rfl | hh
        · exact hg'
        · exact hT.1 h hh
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact far b hb
        · rw [norm_sub_rev]; exact far a ha
        · exact hT.2 a ha b hb hab
    have hmem : (insert g T).card ∈ A := ⟨_, hP, rfl⟩
    have hle := le_csSup hAb hmem
    rw [Finset.card_insert_of_notMem hgT, ← hTc] at hle
    omega
  calc μ {g : G | ‖φ g‖ ≤ R} ≤ μ (⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W) := measure_mono hcover
    _ ≤ ∑ h ∈ T, μ ((fun x => h⁻¹ * x) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = T.card * μ W := by simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (card_le_of_separated φ R r hR hr T hT.1 hT.2)

end GlobalTheory.SeparatedSetCardBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRightConvolutionBoundedIntegrable
section
open MeasureTheory

namespace GlobalTheory

theorem conv_right_continuous {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (m : Measure H) (α : H → ℂ) (hα : Integrable α m) (φ : G → ℂ) (hφ : Continuous φ)
    (B : ℝ) (hB : ∀ g, ‖φ g‖ ≤ B) :
    Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  refine continuous_of_dominated (bound := fun h => B * ‖α h‖) ?_ ?_ ?_ ?_
  · intro x
    refine hα.aestronglyMeasurable.mul ?_
    exact (hφ.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall (fun h => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · exact hα.norm.const_mul B
  · refine Filter.Eventually.of_forall (fun h => ?_)
    exact continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))

end GlobalTheory
end

