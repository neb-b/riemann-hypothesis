module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOfFinOrderOfBounded
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_mem_basicOpen_iff_of_isPullback {P X Y Z : Scheme.{0}} {pm : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ Z}
    {f : Y ⟶ Z} (hP : IsPullback pm g' g f) {J : Type} (U : J → X.Opens) (U' : J → P.Opens)
    (hU : ∀ i, U' i = pm ⁻¹ᵁ U i) (s : ∀ i, Γ(X, U i)) (s' : ∀ i, Γ(P, U' i))
    (hs : ∀ i, (pm.appLE _ _ (hU i).le).hom (s i) = s' i) (p' : Y) :
    (∃ (q : P) (i : J), g' q = p' ∧ q ∈ P.basicOpen (s' i)) ↔
      ∃ (q : X) (i : J), g q = f p' ∧ q ∈ X.basicOpen (s i) := by
  have key : ∀ (i : J) (q : P), q ∈ P.basicOpen (s' i) ↔ pm q ∈ X.basicOpen (s i) := by
    intro i q
    have e := Scheme.basicOpen_appLE pm (U' i) (U i) (hU i).le (s i)
    have e' : P.basicOpen (s' i) = U' i ⊓ pm ⁻¹ᵁ (X.basicOpen (s i)) := by
      rw [← hs i]; exact e
    rw [e']
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hU i]
    exact X.basicOpen_le (s i) h
  constructor
  · rintro ⟨q, i, rfl, hq⟩
    refine ⟨pm q, i, ?_, (key i q).1 hq⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hP.w]
  · rintro ⟨q, i, hq, hq'⟩
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback hP q p' hq
    exact ⟨z, i, hz, (key i z).2 hq'⟩

theorem secBC_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x x' hx s s' hbc p'
  obtain ⟨pm, h1, h2, h3⟩ := hbc
  have hA : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left
      Xo.univ.t.G.hom x := (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have hB : IsPullback (snd (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      Xo.univ.t.G.hom x' := (IsPullback.of_hasPullback x' Xo.univ.t.G.hom).flip
  have hP : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) := by
    refine IsPullback.of_right ?_ h2 hA
    rw [h1]
    exact hx ▸ hB
  have hU : ∀ i : Fin 1 → Xo.univ.t.PP.L.ι, (PPx x').U i = pm ⁻¹ᵁ (PPx x).U i := by
    intro i
    ext y
    change y ∈ ⋂ k : Fin 1, (snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) ↔
      pm y ∈ ⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
    rw [← h1]
    simp only [Set.mem_iInter, Set.mem_preimage, Scheme.Hom.comp_apply]
  have h1' : ∀ i, scal x 1 i = 1 := fun i => by
    simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]
  refine exists_mem_basicOpen_iff_of_isPullback hP (PPx x).U (PPx x').U hU s.f s'.f (fun i => ?_) p'
  have := h3 i (hU i).le
  rwa [h1' i, _root_.one_mul] at this

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E) :
    FD.transvMat G ξ α *ᵥ x = x + (α * FD.herm G x ξ) • ξ := by
  funext a
  simp only [FD.transvMat, FD.herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem herm_add_smul_left (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G (x + c • ξ) y = FD.herm G x y + c * FD.herm G ξ y := by
  simp only [FD.herm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_add_smul_right (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G x (y + c • ξ) = FD.herm G x y + FD.cc c * FD.herm G x ξ := by
  simp only [FD.herm, FD.cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_add (f := _),
    map_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem cc_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (x y : Fin r → E) : FD.cc (FD.herm G x y) = FD.herm G y x := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [FD.herm, FD.cc, map_sum, map_mul, hG', IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem transvMat_mul_neg (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : FD.transvMat G ξ α * FD.transvMat G ξ (-α) = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, hξ, mul_zero, add_zero, neg_mul,
    neg_smul, neg_add_cancel_right]

noncomputable def transv (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : GL (Fin r) E where
  val := FD.transvMat G ξ α
  inv := FD.transvMat G ξ (-α)
  val_inv := transvMat_mul_neg G hξ α
  inv_val := by simpa using transvMat_mul_neg G hξ (-α)

theorem herm_transvMat {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0) {α : E} (hα : FD.cc α = -α) (x y : Fin r → E) :
    FD.herm G (FD.transvMat G ξ α *ᵥ x) (FD.transvMat G ξ α *ᵥ y) = FD.herm G x y := by
  have e : FD.cc (α * FD.herm G y ξ) = -α * FD.herm G ξ y := by
    rw [← hα, ← cc_herm hG y ξ]
    exact map_mul (IsCMField.complexConj E) _ _
  rw [transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, herm_add_smul_right,
    herm_add_smul_right, hξ, e]
  ring

omit [NumberField E] [IsCMField E] in
theorem smul_mem_of_isIntegral (Λ : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hv

theorem exists_data : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M m : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (ξ0 κ0 : E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Gm.det ≠ 0 → p0 ≤ r → (∀ τ ∈ Ψ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.cc ξ0 = -ξ0 → ξ0 ≠ 0 → (κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)) → (∀ τ ∈ Ψ, (τ κ0).im < 0) → 0 < m → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) / (M : E) * κ0 * FD.herm Gm x y)) → ∃ X : FD.Data E r, X.Ψ = Ψ ∧ X.Gm = Gm ∧ X.p0 = p0 ∧ X.Λ = Λ ∧ X.ξ0 = ξ0 ∧ X.κ0 = κ0 ∧ X.m = m ∧ (∀ γ, γ ∈ X.Γ ↔ FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∀ la γ, X.χ la γ = 1 := by
  intro hMink E _ _ _ r p0 M m Ψ Gm Λ ξ0 κ0 hΨ hG hdet hp hsig hfg hsp hM hξ hξ0 hκ hκs hm hint
  obtain ⟨Γ, hΓ, hidx⟩ :=
    GlobalTheory.CongruenceIndex.congruence_finiteIndex E r M Gm Λ hfg (by omega)
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hκ0 : κ0 ≠ 0 := by rcases hκ with h | h <;> simp [h, hξ0]
  have hξ' : IsCMField.complexConj E ξ0 = -ξ0 := hξ
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have halg : IsAlgebraic ℤ (((m : E) / (M : E) * κ0)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  refine ⟨{
    Ψ := Ψ, cmType := hΨ, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := p0, p0_le := hp
    signature := fun τ => hsig τ.1 τ.2
    Λ := Λ, Λ_fg := hfg, Λ_span := hsp
    den := (k : 𝓞 E), den_ne := Int.cast_ne_zero.2 hk
    Λ_int := fun x hx y hy => ?_
    Γ := Γ, Γ_stab := fun γ h => ((hΓ γ).1 h).1, Γ_index := hidx
    Γ_free := fun γ h => GlobalTheory.GamFree.gam_free hMink E r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM
      ((hΓ γ).1 h).1 ((hΓ γ).1 h).2
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (mul_one _).symm
    χ_add := fun _ _ _ _ => (mul_one _).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow _⟩
    ξ0 := ξ0, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := κ0, κ0_xi := hκ
    κ0_sign := fun τ => hκs τ.1 τ.2
    m := m, m_pos := hm
    transv := fun ξ hξΛ hiso s hs hsi => ?_ },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hΓ, fun _ _ => rfl⟩
  · have h := hki.mul (hint x hx y hy)
    have e : k • ((m : E) / (M : E) * κ0)⁻¹ * ((m : E) / (M : E) * κ0 * FD.herm Gm x y) =
        (((k : 𝓞 E) : 𝓞 E) : E) * FD.herm Gm x y := by
      rw [zsmul_eq_mul]
      simp only [map_intCast]
      field_simp
    rwa [e] at h
  · have hs' : IsCMField.complexConj E s = s := hs
    have hα : FD.cc ((m : E) * s * κ0) = -((m : E) * s * κ0) := by
      simp [FD.cc, hs', hκc]
    have hMi : IsIntegral ℤ (M : E) := isIntegral_natCast M
    have key : ∀ v ∈ Λ, (s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ ∈ Λ := fun v hv =>
      smul_mem_of_isIntegral Λ (hsi.mul (hint v hv ξ hξΛ)) hξΛ
    have e : ∀ v, ((m : E) * s * κ0 * FD.herm Gm v ξ) • ξ =
        M • ((s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ) := by
      intro v
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1
      field_simp
    refine ⟨transv Gm hiso ((m : E) * s * κ0), (hΓ _).2 ⟨⟨herm_transvMat hG hiso hα, fun x => ?_⟩,
      fun v hv => ⟨_, key v hv, ?_⟩⟩, rfl⟩
    · change x ∈ Λ ↔ FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ x ∈ Λ
      rw [transvMat_mulVec]
      refine ⟨fun hx => Λ.add_mem hx (by rw [e]; exact nsmul_mem (key x hx) M), fun hx => ?_⟩
      have h := nsmul_mem (key _ hx) M
      rw [← e, herm_add_smul_left, hiso, mul_zero, add_zero] at h
      simpa using Λ.sub_mem hx h
    · change FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ v = _
      rw [transvMat_mulVec, e]

end GlobalTheory.FlagData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.VVNonnegIffLeOne
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntegralFrameAllCompare

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Valuations

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_nonneg_iff_le_one (x : K) (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  rw [← WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero, WithZero.log_one, vV]
  omega

theorem mem_range_iff (x : K) : x ∈ Set.range (algebraMap V K) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  rw [vV_nonneg_iff_le_one x hx]
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · exact fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K v) := by
  have h1 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 h0
  have h2 : valV V (algebraMap V K v) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 h2
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

theorem vV_zpow (x : K) (n : ℤ) : vV V (x ^ n) = n * vV V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem vV_of_isUnit {v : V} (h : IsUnit v) : vV V (algebraMap V K v) = 0 := by
  obtain ⟨u, rfl⟩ := h
  have h1 := (mem_range_iff (V := V) (algebraMap V K (u : V))).1 ⟨_, rfl⟩
  have h2 := (mem_range_iff (V := V) (algebraMap V K ((u⁻¹ : Vˣ) : V))).1 ⟨_, rfl⟩
  rw [map_units_inv, ← zpow_neg_one, vV_zpow] at h2
  omega

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem finite_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) : i.Finite := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (mem_range_iff _).2 (by rw [hi]; exact mul_nonneg (by positivity) ((mem_range_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := ((algebraMap W L).comp g).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun a => hg a
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_cases h0 : a = 0
    · simp [h0]
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    have h1 : vV W (algebraMap W L (g a)) = 0 := vV_of_isUnit hu
    have h3 : (0 : ℤ) < r * vV V (algebraMap V K a) := mul_pos (by exact_mod_cast hr) (vV_pos h0 ha)
    rw [← hi, ← hg, h1] at h3
    exact lt_irrefl _ h3
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  have : IsHausdorff ((maximalIdeal V).map (algebraMap V W)) W := IsHausdorff.of_isDomain _ htop
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have : Finite (W ⧸ (maximalIdeal V).map (algebraMap V W)) := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    have : Finite (W ⧸ maximalIdeal W) := h'
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have : Module.Finite V (W ⧸ (maximalIdeal V).map (algebraMap V W)) := Module.Finite.of_finite
  have : Module.Finite V W := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal V)
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

end Valuations

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

end GlobalTheory.IntegralFrameAllCompare
end
end

