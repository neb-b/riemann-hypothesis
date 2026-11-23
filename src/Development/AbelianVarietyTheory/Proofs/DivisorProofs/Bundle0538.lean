module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapAlgHomAlgebraMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh.CohBaseChange

theorem exists_equiv_of_ker {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A]
    [Module S A] [AddCommGroup B] [Module S B] (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ z, f z = 0 ↔ g z = 0) : ∃ e : A ≃ₗ[S] B, ∀ z, e (f z) = g z := by
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext z; exact h z
  refine ⟨(f.quotKerEquivOfSurjective hf).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    g.quotKerEquivOfSurjective hg, fun z ↦ ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f z) = Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, this]
  rfl

variable {R : Type} [CommRing R]

theorem dB_ext (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R']
    [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i j : ℕ) (y : R' ⊗[R] K.X i) :
    dB K R'' i j (ext α _ y) = ext α _ (dB K R' i j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem spMap_algHom_algebraMap {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R'']
    (α : R' →ₐ[R] R'') : spMap (α : R' →+* R'') ≫ spMap (algebraMap R R') = spMap (algebraMap R R'') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, α.comp_algebraMap]

theorem isPullback_self {X : Scheme.{0}} (s : X ⟶ Sp R) : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
  have : spMap (algebraMap R R) = 𝟙 (Sp R) := Spec.map_id _
  rw [this]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem liftsAt_of (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (i : ℕ) {H H₀ : Type} [AddCommGroup H] [Module R' H]
    [AddCommGroup H₀] [Module k H₀] (θ : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] H)
    (θ₀ : LinearMap.ker (dB K k i (i + 1)) →ₗ[k] H₀) (p : H → H₀) (hθ : Function.Surjective θ)
    (hθ₀ : ∀ z, θ₀ z = 0 ↔ z.1 ∈ LinearMap.range (dB K k (i - 1) i))
    (nat : ∀ z z', z'.1 = ext α _ z.1 → θ₀ z' = p (θ z)) (hp : Function.Surjective p) : LiftsAt K α i := by
  intro z hz
  obtain ⟨x, hx⟩ := hp (θ₀ ⟨z, hz⟩)
  obtain ⟨y, rfl⟩ := hθ x
  have hy' : ext α _ y.1 ∈ LinearMap.ker (dB K k i (i + 1)) := by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 y.2, map_zero]
  have h1 := nat y ⟨_, hy'⟩ rfl
  obtain ⟨b, hb⟩ := (hθ₀ (⟨z, hz⟩ - ⟨_, hy'⟩)).1 (by rw [map_sub, h1, hx, sub_self])
  refine ⟨y.1, b, y.2, ?_⟩
  rw [hb]
  simp

theorem bc_of {R' : Type} [CommRing R'] [Algebra R R'] {Z Z' P H H' : Type} [AddCommGroup Z] [Module R Z]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H]
    [AddCommGroup H'] [Module R' H'] (u : Z →ₗ[R] P) (v : Z' →ₗ[R'] R' ⊗[R] P) (θ : Z →ₗ[R] H)
    (θ' : Z' →ₗ[R'] H') (p : H → H') (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ') (h : ∀ z, θ z = 0 ↔ u z = 0)
    (h' : ∀ z, v z = 0 ↔ θ' z = 0) (nat : ∀ z, ∃ z', v z' = 1 ⊗ₜ u z ∧ θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e, he⟩ := exists_equiv_of_ker θ u hθ hu h
  obtain ⟨e', he'⟩ := exists_equiv_of_ker v θ' hv hθ' h'
  refine ⟨e.baseChange R R' _ _ ≪≫ₗ e', fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hθ c
  obtain ⟨z', h1, h2⟩ := nat z
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, he, ← h1, he', h2]

variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}

theorem liftsAt_zero (M : Model s K) (hU : UConst s) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (hα : Function.Surjective α) : LiftsAt K α 0 := by
  intro z hz
  have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
  have h₀ := IsPullback.of_hasPullback s (spMap (algebraMap R k))
  obtain ⟨e', -⟩ := M.θ0_one h'
  obtain ⟨e₀, he₀⟩ := M.θ0_one h₀
  obtain ⟨r, hr, -⟩ := hU k _ _ _ h₀ (M.θ0 h₀ ⟨z, hz⟩).1 (M.θ0 h₀ ⟨z, hz⟩).2
  have hz' : (⟨z, hz⟩ : LinearMap.ker (dB K k 0 1)) = r • ⟨_, e₀⟩ := by
    apply (M.θ0 h₀).injective
    rw [map_smul]
    refine Subtype.ext (funext fun T ↦ ?_)
    rw [hr T, Algebra.algebraMap_eq_smul_one, ← he₀ T]
    rfl
  obtain ⟨r', rfl⟩ := hα r
  refine ⟨r' • ((1 : R') ⊗ₜ[R] M.one), 0, ?_, ?_⟩
  · rw [map_smul]
    exact (congrArg (r' • ·) (LinearMap.mem_ker.1 e')).trans (smul_zero _)
  · have := congrArg Subtype.val hz'
    simp only [Submodule.coe_smul] at this
    rw [this, map_zero, add_zero, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp

theorem of_parts (hex : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧ Nonempty (Model s K))
    (halg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) → (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) → ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom))
    (hsplit : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z) :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  intro R _ _ X s hp hf hU hl
  obtain ⟨K, hK, hb, ⟨M⟩⟩ := hex R X s hp hf
  have hproj := halg R K hK hb (by
    intro i hi R' _ _ _ _ k _ _ α hα
    have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
    have w := IsPullback.of_hasPullback (pullback.snd s (spMap (algebraMap R R'))) (spMap (α : R' →+* k))
    have h₀ := w.paste_horiz h'
    rw [spMap_algHom_algebraMap] at h₀
    obtain ⟨s1, s2⟩ := hl R' k α hα _ _ _ _ _ _ h' w
    obtain ⟨n1, n2⟩ := M.nat h' h₀ α _ w.w rfl
    obtain ⟨a1, -, a2, -⟩ := M.exact h'
    obtain ⟨-, b1, -, b2⟩ := M.exact h₀
    interval_cases i
    · exact liftsAt_zero M hU α hα
    · exact liftsAt_of K α 1 (M.θ1 h') (M.θ1 h₀) _ a1 b1 n1 s1
    · exact liftsAt_of K α 2 (M.θ2 h') (M.θ2 h₀) _ a2 b2 n2 s2)
  have hid := isPullback_self s
  obtain ⟨a1, b1, a2, b2⟩ := M.exact hid
  have hz : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ℕ) (z : LinearMap.ker (dB K R i (i + 1))),
      ext (Algebra.ofId R R') _ z.1 ∈ LinearMap.ker (dB K R' i (i + 1)) := fun R' _ _ i z ↦ by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 z.2, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ1 hid) hu a1 fun z ↦ (ku z).trans (b1 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ2 hid) hu a2 fun z ↦ (ku z).trans (b2 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R'
    obtain ⟨c1, d1, -, -⟩ := M.exact h
    obtain ⟨n1, -⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ1 hid) (M.θ1 h) _ hu hv a1 c1 (fun z ↦ (b1 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d1 z).symm) fun z ↦ ⟨⟨_, hz R' 1 z⟩, hn _ _ rfl, n1 _ _ rfl⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R'
    obtain ⟨-, -, c2, d2⟩ := M.exact h
    obtain ⟨-, n2⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ2 hid) (M.θ2 h) _ hu hv a2 c2 (fun z ↦ (b2 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d2 z).symm) fun z ↦ ⟨⟨_, hz R' 2 z⟩, hn _ _ rfl, n2 _ _ rfl⟩

end GlobalTheory.AbCoh.CohBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
section
open IsLocalRing

namespace GlobalTheory.DegreeOne

theorem surjective_of_unique_injective_localHom : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  intro B R _ _ _ _ _ _ _ _ _ ψ hB hinj hfin huniq
  haveI := hB
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hfin
  haveI : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  haveI : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).2 hinj
  haveI : CharZero B := ⟨fun m n h => Nat.cast_injective (R := R) (by simpa only [map_natCast] using congrArg ψ h)⟩
  let K := FractionRing B
  let M := FractionRing R
  have hBM : Function.Injective (algebraMap B M) := by
    rw [IsScalarTower.algebraMap_eq B R M]
    exact (IsFractionRing.injective R M).comp hinj
  haveI : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).2 hBM
  letI : Algebra K M := FractionRing.liftAlgebra B M
  haveI : IsScalarTower B K M := FractionRing.isScalarTower_liftAlgebra B M
  haveI : Module.Finite K M := Module.Finite.of_isLocalization B R (Rₚ := K) (Sₚ := M) (nonZeroDivisors B)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing B (K := K)
  let Ω := AlgebraicClosure M
  let L := IntermediateField.normalClosure K M Ω
  haveI : FiniteDimensional K L := normalClosure.is_finiteDimensional K M Ω
  haveI : IsScalarTower B K Ω := inferInstance
  haveI : IsScalarTower B K L := inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let C := integralClosure B L
  haveI : Module.Finite B C := IsIntegralClosure.finite B K L C
  haveI : IsLocalRing C := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := B) C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : CharZero C := ⟨fun m n h => Nat.cast_injective (R := L) (by simpa using congrArg Subtype.val h)⟩
  have hCc : IsAdicComplete (maximalIdeal C) C := CompleteFiniteExtension.isAdicComplete_of_finite_local B C

  have hK : ∀ b : B, algebraMap K L (algebraMap B K b) = algebraMap B L b := fun b =>
    (IsScalarTower.algebraMap_apply B K L b).symm
  have key : ∀ σ : M →ₐ[K] Ω, ∃ f : R →+* C, Function.Injective f ∧ IsLocalHom f ∧ f.comp ψ = algebraMap B C ∧
      ∀ r, ((f r : L) : Ω) = σ (algebraMap R M r) := by
    intro σ
    have hmem : ∀ x, (σ.toRingHom.comp (algebraMap R M)) x ∈ L := fun x =>
      σ.fieldRange_le_normalClosure ⟨_, rfl⟩
    let g₀ : R →+* L := (σ.toRingHom.comp (algebraMap R M)).codRestrict L hmem
    have hg₀ : ∀ b, g₀ (algebraMap B R b) = algebraMap B L b := by
      intro b
      apply Subtype.val_injective
      show σ (algebraMap R M (algebraMap B R b)) = _
      rw [← IsScalarTower.algebraMap_apply B R M, IsScalarTower.algebraMap_apply B K M, σ.commutes,
        ← hK]
      rfl
    let g : R →ₐ[B] L := { g₀ with commutes' := hg₀ }
    have hC : ∀ r, g r ∈ C := fun r => (Algebra.IsIntegral.isIntegral (R := B) r).map g
    let f : R →+* C := (g : R →+* L).codRestrict C hC
    have hcomm : f.comp ψ = algebraMap B C := by
      ext b
      exact congrArg Subtype.val (hg₀ b)
    have hfinj : Function.Injective f := fun x y h =>
      IsFractionRing.injective R M (σ.injective (congrArg (fun c : C => ((c : L) : Ω)) h))
    have hfi : f.IsIntegral := by
      letI : Algebra R C := f.toAlgebra
      haveI : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq' hcomm.symm
      intro c
      exact (integralClosure.isIntegral c).tower_top
    exact ⟨f, hfinj, RingHom.IsIntegral.isLocalHom hfi hfinj, hcomm, fun r => rfl⟩
  choose f hfi hfl hfc hfv using key
  have hemb : ∀ σ τ : M →ₐ[K] Ω, σ = τ := by
    intro σ τ
    have h := huniq C hCc (f σ) (f τ) (hfi σ) (hfi τ) (hfl σ) (hfl τ) ((hfc σ).trans (hfc τ).symm)
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R) (S := M)
    ext r
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
    rw [← hfv σ r, ← hfv τ r, h]
  have hrank : Module.finrank K M = 1 := by
    rw [← Field.finSepDegree_eq_finrank_of_isSeparable K M]
    unfold Field.finSepDegree
    haveI : Subsingleton (Field.Emb K M) := ⟨hemb⟩
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨IsAlgClosed.lift⟩⟩
  have hbot : (⊥ : Subalgebra K M) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hrank
  intro r
  obtain ⟨k, hk⟩ := Algebra.mem_bot.1 (hbot.symm ▸ Algebra.mem_top : algebraMap R M r ∈ (⊥ : Subalgebra K M))
  have hki : IsIntegral B k := by
    have h1 : IsIntegral B (algebraMap K M k) := hk ▸
      (Algebra.IsIntegral.isIntegral (R := B) r).map (IsScalarTower.toAlgHom B R M)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B K M) (algebraMap K M).injective).1 h1
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hki
  refine ⟨b, IsFractionRing.injective R M ?_⟩
  rw [← hk, ← IsScalarTower.algebraMap_apply B K M, IsScalarTower.algebraMap_apply B R M]
  rfl

end GlobalTheory.DegreeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecomposition
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_term_smul_add (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt)
    (y : N.X) (hy : h ^ m = N.io y)
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
        (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S)
    (a b : N.X) : ∃ w : Oˣ, (w : O) ∈ S ∧
      N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH
  set T := S.toSubmonoid.units with hT
  set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ
  have Hc : ∀ a, N.c a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have Hb : h.b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1 := fun x hx x' hx' x'' hx'' =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))
  have σ1 : ∀ a, π (N.σ (N.c a)) = 1 := fun a =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))
  have Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b) := by
    intro a a' b
    have := congrArg π (N.τ_add_left a a' b)
    rwa [map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one] at this
  have Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b') := by
    intro a b b'
    have := congrArg π (N.τ_add_right a b b')
    rwa [map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one] at this
  have fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b) := by
    intro a b
    rw [N.ψ_add, map_mul, map_mul]
  have fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a) := by
    intro a
    have := congrArg π (N.even a)
    rwa [map_mul, σ1, mul_one] at this
  have Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹ := by
    intro a b
    have := Br a b (-b)
    rw [add_neg_cancel, N.τ_zero_right, map_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2 := by
    intro a
    have := fadd a (-a)
    rw [add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one] at this
    rw [sq]
    exact this
  have Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k := by
    intro k a b
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]
  have Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k := by
    intro k a b
    rw [N.τ_symm, Bsmul, N.τ_symm]
  have fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2) := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      ring
  have Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ') := by
    intro χ χ'
    have := congrArg π (h.mult χ χ')
    rwa [map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one] at this
  have Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]
  have Spow : π (h.s a) ^ m = π (N.τ a y) := by
    have := congrArg π (h.pow_s m a)
    rw [map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm] at this
    have hc : π (cubN N.θ m 1 h.b (N.c a)) = 1 := by
      unfold cubN
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)
    rw [hc, mul_one] at this
    exact this.symm
  refine ⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩
  · have e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1 := by
      rw [map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr,
        Ssmul, Spow]
      ac_rfl
    exact ((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1
  · exact (fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by
      rw [mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeOmActKronBlockDiagonalLe
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockBlockDeg

theorem Jm_apply_of_ne {r s : ℕ} {c e : Ix r s} (h : c ≠ e) : Jm r s c e = 0 := by
  rcases c with c | c <;> rcases e with e | e <;>
    simp_all [Jm, Formalism.UG.Jpq]

theorem totalDegree_omAct_kron_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  intro p q r s E hE d P hP
  rw [← mem_restrictTotalDegree] at hP ⊢
  refine GlobalTheory.FockPolGK.omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change E a b * Jm r s c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hE a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Jm_apply_of_ne hc, mul_zero]

end GlobalTheory.FockBlockDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCover
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem twistedDual_omB : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI p q hpq y hy
  obtain ⟨-, hfr, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc I hI
  have hrk : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := hc.exists_basis
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms k F K d x hc).2 τ hτ
  constructor
  · intro h
    refine GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect k K (rB k K x I) d p q hrk hpq y hy fun a ha => ?_
    have haG : a ∈ ⋀[K]^p Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.1
    have hay : a * y ∈ ⋀[K]^d Ω[K⁄k] := hpq ▸ SetLike.mul_mem_graded haG hy
    have hz : ∀ b ∈ rB k K x I, Algebra.trace F K (τ (a * y) * b) ∈ omA k x I := by
      intro b hb
      have hba : b • a ∈ omB k K (rB k K x I) p := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.2 b hb
      have e : τ (a * y) * b = τ ((b • a) * y) := by
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
      rw [e]
      exact h _ hba
    obtain ⟨y', hy', e'⟩ := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).1 hz
    have hy'G : y' ∈ ⋀[K]^d Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) d q).2.1 y' hy').2.2.1
    rw [htop _ hay, ← e', ← htop _ hy'G]
    exact hy'
  · intro h a ha
    have hay : a * y ∈ omB k K (rB k K x I) d := hpq ▸ (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).1 a ha y h
    have := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).2 ⟨a * y, hay, rfl⟩ 1 (Subalgebra.one_mem _)
    rwa [mul_one] at this

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensorsStatement
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K)), (∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) → VV K lam ≤ Submodule.span K {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  first | exact @GlobalTheory.coefSpace_le_span_pure_tensors | exact GlobalTheory.coefSpace_le_span_pure_tensors | (intros; apply GlobalTheory.coefSpace_le_span_pure_tensors <;> assumption)
end
end

