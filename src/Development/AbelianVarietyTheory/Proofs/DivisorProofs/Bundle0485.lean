module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulM
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem appLE_basicOpen_surjective_of_mul_mem_range {X Z : Scheme.{0}} (φ : X ⟶ Z) {V : Z.Opens}
    (haff : IsAffineOpen (φ ⁻¹ᵁ V)) (r : Γ(Z, V))
    (h : ∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b)
    (A : Z.Opens) (B : X.Opens) (e : B ≤ φ ⁻¹ᵁ A) (hA : A = Z.basicOpen r)
    (hB : B = X.basicOpen ((φ.app V).hom r)) : Function.Surjective (φ.appLE A B e) := by
  subst hA hB
  set s := (φ.app V).hom r with hs
  intro y
  let resX : Γ(X, φ ⁻¹ᵁ V) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  let resZ : Γ(Z, V) →+* Γ(Z, Z.basicOpen r) := (Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op).hom
  let g := (φ.appLE (Z.basicOpen r) (X.basicOpen s) e).hom
  haveI := haff.isLocalization_basicOpen s
  obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers s) y
  obtain ⟨b, hb⟩ := h c
  have hu : IsUnit (resZ r) := Z.toRingedSpace.isUnit_res_basicOpen r
  have hv : IsUnit (resX s) := X.toRingedSpace.isUnit_res_basicOpen s
  have hg : ∀ t, g (resZ t) = resX (φ.app V t) := by
    intro t
    simp only [g, resZ, resX]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hc' : y * resX s ^ n = resX c := by rw [← map_pow]; exact hc
  let x := resZ b * ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) ^ (n + 1)
  refine ⟨x, ?_⟩
  have hx : g x * resX s ^ (n + 1) = y * resX s ^ (n + 1) := by
    calc g x * resX s ^ (n + 1) = g (x * resZ r ^ (n + 1)) := by rw [RingHom.map_mul g x (resZ r ^ (n + 1)), map_pow, hg r]
      _ = g (resZ b) := by
          congr 1
          simp only [x, mul_assoc, ← mul_pow]
          rw [show ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) * resZ r = 1 from
            hu.val_inv_mul, one_pow, mul_one]
      _ = resX (φ.app V b) := hg b
      _ = resX (s * c) := by rw [hb]
      _ = y * resX s ^ (n + 1) := by rw [map_mul, ← hc']; ring
  exact (hv.pow (n + 1)).mul_left_inj.1 hx

theorem isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) →
      ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) →
        IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  intro X Z φ V hV haff r h
  have hpre : φ ⁻¹ᵁ Z.basicOpen r = X.basicOpen ((φ.app V).hom r) := Scheme.preimage_basicOpen φ r
  haveI : IsAffine (Z.basicOpen r) := hV.basicOpen r
  haveI : IsAffine (φ ⁻¹ᵁ Z.basicOpen r) := by
    have := haff.basicOpen ((φ.app V).hom r)
    rw [← hpre] at this
    exact this
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  exact appLE_basicOpen_surjective_of_mul_mem_range φ haff r h _ _ _ (by simp) (by simp [hpre])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.RatUnit


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.RatUnit.isUA_ratM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ x) (γ *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) → _root_.GlobalTheory.UCls.IsUA (IsCMField.complexConj E) G (_root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ) := by
  intro E _ _ _ r G γ hdet hinv
  have hmat : ∀ i j, ∑ a, ∑ b, γ a i * G a b * IsCMField.complexConj E (γ b j) = G i j := by
    intro i j
    have h := hinv (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
    simpa [mulVec, dotProduct, Pi.single_apply, apply_ite] using h
  let A := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
  let φ : E →+* _root_.GlobalTheory.AdLat.RA (maximalRealSubfield E) E :=
    (Algebra.TensorProduct.includeRight :
      E →ₐ[maximalRealSubfield E] A ⊗[maximalRealSubfield E] E).toRingHom
  have hφ : ∀ e : E, φ e = (1 : A) ⊗ₜ[maximalRealSubfield E] e := fun _ => rfl
  have hg : _root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ = γ.map φ := rfl
  let τ := _root_.GlobalTheory.AdLat.sg A (IsCMField.complexConj E)
  have hτ : ∀ e : E, τ (φ e) = φ (IsCMField.complexConj E e) := by
    intro e
    simp [τ, hφ, _root_.GlobalTheory.AdLat.sg]
  unfold _root_.GlobalTheory.UCls.IsUA
  rw [hg]
  refine ⟨?_, fun x y => ?_⟩
  · have h := RingHom.map_det φ γ
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (isUnit_iff_ne_zero.mpr hdet).map φ
  · unfold _root_.GlobalTheory.AdLat.hermA
    change ∑ a, ∑ b, (γ.map φ *ᵥ x) a * φ (G a b) * τ ((γ.map φ *ᵥ y) b) =
      ∑ a, ∑ b, x a * φ (G a b) * τ (y b)
    calc _ = ∑ a, ∑ b, ∑ i, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [mulVec, dotProduct, map_apply, map_sum, map_mul, hτ, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ a, ∑ i, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, x i * φ (G i j) * τ (y j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← hmat i j, map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [map_mul]

end GlobalTheory.RatUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isLocallyNoetherian_of_isQProjOver_noeth :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R),
      IsQProjOver f → IsLocallyNoetherian X := by
  intro R _ _ X f h
  obtain ⟨N, i, hi, -, e⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  have : LocallyOfFiniteType f := by
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  exact LocallyOfFiniteType.isLocallyNoetherian f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRegularLocusOfNagata
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularLocalRing_atPrime_of_le {B : Type} [CommRing B] (p q : Ideal B) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have hd : Disjoint (q.primeCompl : Set B) (p : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    exact hx (hpq hxp)
  let P' : Ideal (Localization.AtPrime q) := p.map (algebraMap B _)
  haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hd
  have hc : P'.comap (algebraMap B (Localization.AtPrime q)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl _ ‹p.IsPrime› hd
  have hsub : (P'.comap (algebraMap B (Localization.AtPrime q))).primeCompl = p.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_of_isRegularLocalRing _
  have hreg : IsRegularLocalRing (Localization.AtPrime P') :=
    IsRegularRing.isRegularLocalRing_localization P'
  haveI : IsLocalization p.primeCompl (Localization.AtPrime P') := by
    rw [← hsub]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime q.primeCompl P'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P')
      (Localization.AtPrime p)).toRingEquiv

theorem isOpen_regularLocus_of_nagata : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  intro B _ _ hyp
  apply _root_.GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure B
  · intro p q hpq hq
    exact isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq
  · intro p hp
    obtain ⟨g₁, hg₁p, hg₁⟩ := hyp p.asIdeal
    obtain ⟨g₂, hg₂p, hg₂⟩ := GlobalTheory.T.exists_regular_near_of_regular_quotient_prime B p.asIdeal hp
    refine ⟨g₁ * g₂, fun h => (p.isPrime.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
    intro q hpq hq
    have hq₁ : g₁ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
    have hq₂ : g₂ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
    exact hg₂ q.asIdeal hpq hq₂ (hg₁ q.asIdeal hpq hq₁)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem universallyClosed_of_jointly_surjective {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c₁ := h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)
  have c₂ := h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪
      (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩
  rw [e]
  exact (c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union
    (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))

end GlobalTheory

namespace GlobalTheory

theorem isProper_map_inf_subschemeι : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W),
    IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) →
    IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  intro S W W' f π hsep hlft T' T'' h₁ h₂
  have hle₁ : T'.map π ⊓ T'' ≤ T'.map π := inf_le_left
  have hle₂ : T'.map π ⊓ T'' ≤ T'' := inf_le_right
  let g₁ := Scheme.IdealSheafData.subschemeMap T' (T'.map π ⊓ T'') π hle₁
  let g₂ := Scheme.IdealSheafData.inclusion hle₂
  have e₁ : g₁ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T'.subschemeι ≫ π ≫ f := by simp [g₁]
  have e₂ : g₂ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T''.subschemeι ≫ f := by simp [g₂]
  have huc₀ : UniversallyClosed ((T'.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc]; infer_instance
  have huc : UniversallyClosed (T'.subschemeι ≫ π) :=
    UniversallyClosed.of_comp_of_isSeparated _ f
  have hsupp : ((T'.map π).support : Set W) = Set.range (T'.subschemeι ≫ π) := by
    rw [Scheme.IdealSheafData.map, Scheme.Hom.support_ker]
    exact (T'.subschemeι ≫ π).isClosedMap.isClosed_range.closure_eq
  have hmul : T'.map π * T'' ≤ T'.map π ⊓ T'' := by
    intro U
    exact Ideal.mul_le_inf
  have hcov : ∀ x : (T'.map π ⊓ T'').subscheme, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x := by
    intro x
    have hx : (T'.map π ⊓ T'').subschemeι x ∈ (T'.map π ⊓ T'').support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hx' := Scheme.IdealSheafData.support_antitone hmul hx
    rw [Scheme.IdealSheafData.support_mul] at hx'
    have hinj := (T'.map π ⊓ T'').subschemeι.isClosedEmbedding.injective
    rcases hx' with hx' | hx'
    · rw [hsupp] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inl ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι]
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inr ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
  have huc' : UniversallyClosed ((T'.map π ⊓ T'').subschemeι ≫ f) :=
    universallyClosed_of_jointly_surjective g₁ g₂ _ hcov (e₁ ▸ inferInstance) (e₂ ▸ inferInstance)
  exact { }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
section
noncomputable section

namespace GlobalTheory.TorusFrame

open NumberField Matrix Complex GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem angles_add (φ ψ : Fin (r - 1) → ℝ) (a : Fin r) : angles (φ + ψ) a = angles φ a + angles ψ a := by
  unfold angles; split_ifs <;> simp [Finset.sum_add_distrib]; ring

theorem angles_smul (c : ℝ) (φ : Fin (r - 1) → ℝ) (a : Fin r) : angles (c • φ) a = c * angles φ a := by
  unfold angles; split_ifs <;> simp [Finset.mul_sum]

theorem angles_zero (a : Fin r) : angles (0 : Fin (r - 1) → ℝ) a = 0 := by
  unfold angles; split_ifs <;> simp

def anglesL (r : ℕ) : (Fin (r - 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun φ a := angles φ a
  map_add' φ ψ := funext fun a => angles_add φ ψ a
  map_smul' c φ := funext fun a => angles_smul c φ a

theorem continuous_angles (a : Fin r) : Continuous fun φ : Fin (r - 1) → ℝ => angles φ a :=
  ((continuous_apply a).comp (LinearMap.continuous_of_finiteDimensional (anglesL r)) :)

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isUnit_det_of_isOrth {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    IsUnit (mat x τ).det := by
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq, det_mul, det_mul, det_transpose, det_diagonal] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_mul, zero_mul] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn; split_ifs <;> norm_num

def frameU {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : GL (Fin r) ℂ :=
  nonsingInvUnit (mat x τ) (isUnit_det_of_isOrth hx τ)

def phaseU (φ : Fin (r - 1) → ℝ) : GL (Fin r) ℂ where
  val := diagonal fun a => exp (I * (angles φ a : ℂ))
  inv := diagonal fun a => exp (-(I * (angles φ a : ℂ)))
  val_inv := by rw [diagonal_mul_diagonal]; simp [← exp_add]
  inv_val := by rw [diagonal_mul_diagonal]; simp [← exp_add]

def torusGL {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => frameU hx τ * phaseU (θ τ) * (frameU hx τ)⁻¹

theorem torusGL_val {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) (τ : X.Ψ) :
    ((torusGL hx θ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => exp (I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ := rfl

def torusDerL {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun θ τ a b := (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b
  map_add' θ θ' := by
    funext τ a b
    simp only [Pi.add_apply, angles_add, ofReal_add, mul_add, ← diagonal_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c θ := by
    funext τ a b
    have : (diagonal fun d => I * (angles (c • θ τ) d : ℂ)) = (c : ℂ) • diagonal fun d => I * (angles (θ τ) d : ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, angles_smul]; ring
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

def torusDer {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →L[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
  LinearMap.toContinuousLinearMap (torusDerL x)

theorem torusDer_apply {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (θ : Ψ → Fin (r - 1) → ℝ) (τ : Ψ) (a b : Fin r) :
    torusDer x θ τ a b = (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b := rfl

end GlobalTheory.TorusFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedComplexPartialDerivativeEqWirtingerWord
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.HoloWirt

open Classical in
theorem clm_single_I {I : Type} (f : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    f (Pi.single i Complex.I) = Complex.I * f (Pi.single i 1) := by
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

theorem wirt_false_eq_lineDeriv {I : Type} [Fintype I] [DecidableEq I] (i : I) (h : (I → ℂ) → ℂ) (z : I → ℂ)
    (hd : DifferentiableAt ℂ h z) : wirt i false h z = lineDeriv ℂ h z (Pi.single i 1) := by
  rw [hd.lineDeriv_eq_fderiv]
  unfold wirt
  rw [hd.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', Bool.false_eq_true, if_false]
  rw [clm_single_I]
  have e : ∀ a b : ℂ, a = b → (a + -Complex.I * (Complex.I * a)) / 2 = b := by
    rintro a b rfl
    ring_nf
    rw [Complex.I_sq]
    ring
  apply e
  congr
  exact Subsingleton.elim _ _

end GlobalTheory.HoloWirt

namespace GlobalTheory.HoloWirt

theorem iterD_holo_and_eq {I : Type} [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (l : List I) :
    DifferentiableOn ℂ (iterD l g) U ∧ Set.EqOn (iterD l g) (wirtWord (l.map fun i => (i, false)) g) U := by
  induction l with
  | nil => exact ⟨hg, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨hd, heq⟩ := ih
    have hat : ∀ z ∈ U, DifferentiableAt ℂ (iterD l g) z := fun z hz => hd.differentiableAt (hU.mem_nhds hz)
    have hpart : Set.EqOn (iterD (i :: l) g) (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U := by
      intro z hz
      show lineDeriv ℂ (iterD l g) z (Pi.single i 1) = _
      exact (hat z hz).lineDeriv_eq_fderiv
    refine ⟨?_, ?_⟩
    · have hf : DifferentiableOn ℂ (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U :=
        ((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hd).fderiv.differentiableOn).clm_apply
          (differentiableOn_const _)
      exact hf.congr hpart
    · intro z hz
      have hev : wirtWord (l.map fun i => (i, false)) g =ᶠ[nhds z] iterD l g :=
        Filter.eventually_of_mem (hU.mem_nhds hz) (fun y hy => (heq hy).symm)
      show partialD i (iterD l g) z = wirt i false (wirtWord (l.map fun i => (i, false)) g) z
      have hw : wirt i false (wirtWord (l.map fun i => (i, false)) g) z = wirt i false (iterD l g) z := by
        unfold wirt
        rw [hev.fderiv_eq]
      rw [hw, wirt_false_eq_lineDeriv i _ z (hat z hz)]
      rfl

theorem iterD_eq_wirtWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U,
      iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  intro I _ _ U g hU hg l z hz
  exact (iterD_holo_and_eq U g hU hg l).2 hz

end GlobalTheory.HoloWirt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F), L ≤ stdLat F → (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔ ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  first | exact @GlobalTheory.HilbFam.TwistMem.mem_twist_iff | exact GlobalTheory.HilbFam.TwistMem.mem_twist_iff | (intros; apply GlobalTheory.HilbFam.TwistMem.mem_twist_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := by
  first | (exact @GlobalTheory.EtC.tw_finitary) | (exact GlobalTheory.EtC.tw_finitary) | (intros; apply GlobalTheory.EtC.tw_finitary  <;> assumption)
end

