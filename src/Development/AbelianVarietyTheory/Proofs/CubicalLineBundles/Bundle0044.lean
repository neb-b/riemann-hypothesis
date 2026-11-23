module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn
open scoped Matrix

namespace GlobalTheory.TransvModel

theorem herm_smul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) {v : Fin r → E} (hv : v ∈ X.L')
    {x : Fin r → E} (hx : x ∈ X.Λ) : FD.herm X.Gm x v • v ∈ X.Λ := by
  rw [hΛ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hx
    rw [GlobalTheory.TransvLevel.herm_smul_left, mul_smul, hΛ]
    exact Submodule.subset_span ⟨a, ha, _, GlobalTheory.FlagData.smul_mem_of_isIntegral _ (X.L'_int u hu v hv) hv, rfl⟩
  | zero => simp [FD.herm]
  | add x y _ _ hx hy =>
    have : FD.herm X.Gm (x + y) v = FD.herm X.Gm x v + FD.herm X.Gm y v := (X.toData.hermL v).map_add x y
    rw [this, add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul E c x, GlobalTheory.TransvLevel.herm_smul_left, mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem transv_mem_of_span {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) (m : ℕ)
    (hmκ : IsIntegral ℤ ((m : E) * X.κ0)) (v : Fin r → E) (hv : v ∈ X.L') (hiso : FD.herm X.Gm v v = 0) (b : E)
    (hb : cc b = b) (hbi : IsIntegral ℤ b) :
    ∃ γ ∈ X.Γ, ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 =
      X.flowMat v τ ((((X.g * m : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  have hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκc : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]
  have hb' : IsCMField.complexConj E b = b := hb
  set α : E := ((X.g * m : ℕ) : E) * b * X.κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hb', hκc]
  have key : ∀ x ∈ X.Λ, (b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v) ∈ X.Λ := fun x hx =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hbi.mul hmκ) (herm_smul_mem X S hΛ hv hx)
  have e : ∀ x, (α * FD.herm X.Gm x v) • v =
      (X.g : E) • ((b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v)) := by
    intro x
    rw [smul_smul, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  have key' : ∀ x ∈ X.Λ, (α * FD.herm X.Gm x v) • v ∈ X.Λ := fun x hx => by
    rw [e]
    exact GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)
  refine ⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _
    ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩
  · change x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩
    have h := key' _ hx
    rw [GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · refine ⟨_, key x hx, ?_⟩
    change transvMat X.Gm v α *ᵥ x - x = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]
  · change (transvMat X.Gm v α).map τ.1 = _
    refine TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_
    rw [hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]
    push_cast
    ring

theorem xiR_eq (D : D7) : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have e1 : D.host.φ₀ D.host.xi0 =
      -1 / ((Ideal.absNorm D.host.ccK : ℂ) * D.host.φ₀ D.host.sqrtMinusD) := by
    unfold Formalism.BasicNotions.Host.xi0; simp [map_div₀, map_mul, map_neg, map_natCast]
  have e2 : ‖D.host.φ₀ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    have h0 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg,
      Complex.norm_natCast]
  unfold xiR; rw [e1, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast, e2]

theorem isIntegral_level_mul_kappa {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r)
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (τ : E →+* ℂ) (hτ : ‖τ X.ξ0‖ = 1 / ((N : ℝ) * Real.sqrt d)) :
    IsIntegral ℤ (((N * d : ℕ) : E) * X.κ0) := by
  have h1 : τ (cc X.ξ0) = (starRingEnd ℂ) (τ X.ξ0) := IsCMField.complexEmbedding_complexConj E τ X.ξ0
  rw [X.ξ0_im, map_neg] at h1
  have h2 := Complex.mul_conj' (τ X.ξ0)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : ‖τ X.ξ0‖ ^ 2 * ((N : ℝ) ^ 2 * d) = 1 := by
    rw [hτ, div_pow, mul_pow, Real.sq_sqrt hd'.le]
    field_simp
  have h4 : ((‖τ X.ξ0‖ : ℝ) : ℂ) ^ 2 * ((N : ℂ) ^ 2 * d) = 1 := by exact_mod_cast h3
  rw [← h1] at h2
  have h5 : X.κ0 ^ 2 = 4 * X.ξ0 ^ 2 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> ring
  have h6 : (((N * d : ℕ) : E) * X.κ0) ^ 2 = ((-(4 * d : ℤ) : ℤ) : E) := by
    apply τ.injective
    rw [mul_pow, h5, map_mul, map_mul, map_pow, map_pow, map_natCast, map_intCast, map_ofNat]
    push_cast
    linear_combination (-4 * (N : ℂ) ^ 2 * (d : ℂ) ^ 2) * h2 - 4 * (d : ℂ) * h4
  refine IsIntegral.of_pow two_pos ?_
  rw [h6]
  exact isIntegral_algebraMap (R := ℤ)

theorem transv_model : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r), Xx.toData = ((T.U j T.σ₀).X k) → Xx.g = T.Q.l.M → Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} → ((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) * Xx.k0 = 2 * (D.host.g 0 * D.host.g 1 : ℕ) * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  intro D T h j hj k Xx hX hg hΛ
  have hM : Xx.g = D.host.g 0 * D.host.g 1 := hg.trans h.pins.2.1.1
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  rw [← hX]
  refine ⟨?_, fun v hv hiso b hb hbi => ?_⟩
  · obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Xx.Ψ := by
      by_cases h0 : D.host.φ₀ ∈ Xx.Ψ
      · exact ⟨_, h0⟩
      · by_contra hc
        exact h0 ((Xx.cmType _).2 fun h1 => hc ⟨_, h1⟩)
    have h1 := Xx.ξ0_abs ⟨τ, hτ⟩
    rw [habs] at h1
    have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    have hs := Real.sqrt_pos.2 hd'
    have hk : Xx.k0 = 2 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
      rw [div_eq_mul_one_div, h1]; ring
    have hss := Real.mul_self_sqrt hd'.le
    rw [hk]
    push_cast
    field_simp
    linear_combination (-((D.host.g 0 : ℝ) * D.host.g 1)) * hss
  · have := transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (isIntegral_level_mul_kappa Xx.toData hN hd D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hM, ← mul_assoc] at this

end GlobalTheory.TransvModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KeyPBIdOfKeyPB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyCancel

theorem keyPB_id_of_keyPB : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x₁ x₂ : KeyIn K), KeyPB x₁ x f → KeyPB x₂ x f → KeyPB x₁ x₂ (RingHom.id K) :=
  fun R K _ _ f x x₁ x₂ h₁ h₂ =>
    keyPB_cancel R K K x x₂ x₁ f (RingHom.id K) h₂ (by rwa [RingHom.id_comp])

end GlobalTheory.KeyCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultOfEigenbasis
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LieType

theorem repr_eq_zero {k O V J : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module O V]
    [SMulCommClass O k V] (b : Module.Basis J k V) (χ : J → (O →+* k)) (hb : ∀ i a, a • b i = χ i a • b i)
    (ψ : O →+* k) (w : V) (hw : ∀ a : O, a • w = ψ a • w) (j : J) (hj : χ j ≠ ψ) : b.repr w j = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, χ j a ≠ ψ a := by
    by_contra h
    push Not at h
    exact hj (RingHom.ext h)
  have e : (b.coord j).comp (DistribSMul.toLinearMap k V a) = χ j a • b.coord j := b.ext fun i => by
    by_cases h : i = j
    · subst h
      simp [hb]
    · simp [hb, Finsupp.single_eq_of_ne' h]
  have e' := LinearMap.congr_fun e w
  simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply] at e'
  exact (mul_eq_mul_right_iff.1 e').resolve_left ha.symm

theorem lieMult_of_eigenbasis {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (a : OAct O G) {n : ℕ} {v : Fin n → (epsR k ⟶ G)} (hv : IsLieBasis v) (χ : Fin n → (O →+* k))
    (hχ : Function.Injective χ) (h : ∀ x i, IsLieComb (Pi.single i (χ i x)) v (v i ≫ a.act x)) :
    (∀ i, LieMult a (𝟙 _) (χ i) 1) ∧ ∀ ψ, (∀ i, χ i ≠ ψ) → LieMult a (𝟙 _) ψ 0 := by
  let b := Serre.Lie.basis a hv
  have hb : ∀ i x, x • b i = χ i x • b i := fun i x => by
    have h1 := h x i
    obtain e : v = fun i => (b i).hom := funext fun i => (Serre.Lie.hom_basis hv i).symm
    rw [e, Serre.Lie.isLieComb_iff] at h1
    refine (Serre.Lie.ext h1 : x • b i = _).trans ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp), Pi.single_eq_same]
  refine ⟨fun i => ?_, fun ψ hψ => ?_⟩
  · have e : Serre.Lie.eig a (χ i) = Submodule.span k {b i} := by
      refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (hb i))
      rw [← b.sum_repr w, Finset.sum_eq_single i (fun j _ hj => by
        rw [repr_eq_zero b χ hb (χ i) w hw j (hχ.ne hj), zero_smul]) (by simp)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_span_singleton (b.ne_zero i))⟩
  · have e : Serre.Lie.eig a ψ = ⊥ := by
      refine eq_bot_iff.2 fun w hw => ?_
      rw [Submodule.mem_bot, ← b.sum_repr w]
      exact Finset.sum_eq_zero fun j _ => by rw [repr_eq_zero b χ hb ψ w hw j (hψ j), zero_smul]
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.Basis.empty _⟩

theorem exists_label {E K k : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field k] [IsAlgClosed k]
    (j : K →+* k) (lab : (E →+* ℂ) → (E →+* K)) (hl : Function.Injective lab) (τ : 𝓞 E →+* k) :
    ∃ t, τ = j.comp ((lab t).comp (algebraMap (𝓞 E) E)) := by
  have : CharZero k := j.charZero_iff j.injective |>.1 inferInstance
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 E)) (RingHom.ker τ) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hi : Function.Injective fun t => j.comp (lab t) := fun t t' e =>
    hl (RingHom.ext fun x => j.injective (RingHom.congr_fun e x))
  have hs := ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hi, (Embeddings.card E ℂ).trans (Embeddings.card E k).symm⟩).2
  obtain ⟨t, ht⟩ := hs (IsFractionRing.lift hτ : E →+* k)
  refine ⟨t, RingHom.ext fun a => ?_⟩
  exact ((RingHom.congr_fun ht _).trans (IsFractionRing.lift_algebraMap hτ a)).symm

theorem hasType_of_isLieType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), act.act = oa.act → Function.Injective lab → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → HasType H act ρ 1 0 := by
  intro E _ _ _ _ H K _ _ A x φ hf oa act S τ lab ρ hact hl hS hT k _ _ β hβ σ
  obtain ⟨act', e⟩ := ellPull_exists_oAct hf.2.1 act
  have := x.P.isAb.comm
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  let res : (E →+* ℂ) → (𝓞 E →+* K) := fun t => (lab t).comp (algebraMap (𝓞 E) E)
  have hres : Function.Injective res := fun t t' h => hl (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h)
  obtain ⟨h1, h0⟩ := lieMult_of_eigenbasis act' x.basis (fun i => res (τ i))
    (hres.comp (Subtype.val_injective.comp τ.injective)) fun a i => by
      obtain ⟨w, hw, ew⟩ := hT a i
      obtain rfl : w = x.v i ≫ act'.act a := by
        refine Over.OverMorphism.ext (hf.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
        rw [← ew, Over.comp_left, Category.assoc, e, hact]
      exact hw
  let j : K →+* k := IsFractionRing.lift hβ
  have hj : ∀ a : 𝓞 K, j a = β a := IsFractionRing.lift_algebraMap hβ
  obtain ⟨t, rfl⟩ := exists_label j lab hl σ
  have key : ∀ n, LieMult act' (𝟙 _) (res t) n → LieMult act (spMap β) (j.comp (res t)) n := fun n h => by
    rw [← LieExt.lieMult_extend_iff j, LiePull.lieMult_pull _ _ _ _ _ _ _ act act' hf.2.1 e,
      spMap_comp_spMap] at h
    convert h using 2
    exact (RingHom.ext hj).symm
  have ht : t ∈ S ↔ j.comp (res t) H.rt = β ρ := by
    rw [hS, ← hj]
    exact j.injective.eq_iff.symm
  refine ⟨fun h => key _ ?_, fun h => key _ (h0 _ fun i hi => h (ht.1 ?_))⟩
  · simpa using h1 (τ.symm ⟨t, ht.2 h⟩)
  · rw [← hres hi]
    exact (τ i).2

end GlobalTheory.LamF.LieType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultTensorOfFinrank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open GlobalTheory.TensorDet GlobalTheory.Serre in
theorem lieMult_tensor_of_finrank {O O' M R k : Type} [CommRing O] [CommRing O'] [Algebra O O'] [AddCommGroup M]
    [Module O M] [Module O' M] [IsScalarTower O O' M] [Module.Finite O M] [Module.Projective O M] [CommRing R]
    [Field k] [Algebra O k] {G A : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
    (hs : Smooth G.hom) (v : epsR R ⟶ G) (hv : IsLieBasis ![v]) (a : OAct O G) (κ : O →+* R) (b₀ : OAct O' A)
    (τ : IsTensor A (comapAct b₀ (algebraMap O O')) G a M)
    (hκ : ∀ c, IsLieComb ![κ c] ![v] (v ≫ a.act c)) (hlin : ∀ (x : O') m, τ.tmul (x • m) = τ.tmul m ≫ b₀.act x)
    (β : R →+* k) (hβ : ∀ c, algebraMap O k c = β (κ c)) (χ : O' →+* k) (n : ℕ)
    (hn : Module.finrank k (EigenSplit.eigenSub (rightAction k O O' M) χ) = n) : LieMult b₀ (spMap β) χ n := by
  have hG := isGrpPullback_pullback G (spMap β)
  have hA := isGrpPullback_pullback A (spMap β)
  obtain ⟨v', hv', hvv⟩ := exists_isLieBasis_baseChange R k β G _ _ hG hs 1 ![v] hv
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv₁ : (v' 0).left ≫ pullback.fst G.hom (spMap β) = spMap (Chart.dualMapR β) ≫ v.left := hvv 0
  have hb : IsLieBasis ![v' 0] := ev.symm ▸ hv'
  generalize v' 0 = v₁ at hv₁ hb
  have hL := isLinearPullback_pullback (comapAct b₀ (algebraMap O O')) (spMap β)
  let b : OAct O ((Over.pullback (spMap β)).obj A) := comapAct (b₀.pullback (spMap β) A) (algebraMap O O')
  let τ₁ : IsTensor _ b _ (a.pullback (spMap β) G) M :=
    τ.baseChange (isLinearPullback_pullback a (spMap β)) ⟨hA, hL.2⟩
  have ht : ∀ m, τ₁.tmul m = (Over.pullback (spMap β)).map (τ.tmul m) := fun m => τ.pullback_tmul (spMap β) m
  obtain ⟨Φ, inj, tan, add, smul, -, eqv⟩ := SerreLie.exists_lie_tensor k _ O M _ _ b τ₁ v₁ hb (fun c => by
    have h := (lieComb_baseChange R k β G _ _ hG 1 ![v] (v ≫ a.act c) ![κ c] ![v₁]
      (v₁ ≫ (a.pullback (spMap β) G).act c) (fun j => by fin_cases j; exact hv₁) (hκ c)).1 (by
        rw [Over.comp_left, Category.assoc, (isLinearPullback_pullback a (spMap β)).2, ← Category.assoc]
        exact (congrArg (· ≫ (a.act c).left) hv₁).trans (Category.assoc _ _ _))
    convert h using 2 with i
    fin_cases i
    exact hβ c)
  have : Module.Finite k (k ⊗[O] M) := inferInstance
  have := lieMult_of_param (b₀.pullback (spMap β) A) (rightAction k O O' M) Φ inj tan add smul
    (fun x y => by
      rw [rightAction_apply, eqv]
      congr 1
      have := (b₀.pullback (spMap β) A).hom x
      refine τ₁.hom_ext fun m => ?_
      rw [IsTensor.tmul_mapLeft, ht, ht]
      exact (congrArg _ (hlin x m)).trans (Functor.map_comp _ _ _)) χ hn
  have h2 := (LiePull.lieMult_pull _ _ _ _ _ _ _ b₀ (b₀.pullback (spMap β) A) hA
    (isLinearPullback_pullback b₀ (spMap β)).2 k (𝟙 _) χ n).1 this
  rwa [Category.id_comp] at h2


open GlobalTheory.TensorDet GlobalTheory.Serre in
theorem hasType_of_isTen : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)), Nonempty (IsTen C D h T) → HasType H T.t.act (2 * ω - 1) (D.p + D.q) 0 := by
  set_option synthInstance.maxHeartbeats 400000 in
    rintro - E _ _ _ H R _ _ ω C D h T ⟨t⟩ k _ _ β hβ χ
    have : CharZero k := β.charZero_iff hβ |>.1 inferInstance
    obtain ⟨κ, hκw, hκ⟩ := LieChar.ell_char E H R ω C
    obtain ⟨-, hgen, -, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
    obtain ⟨_, _, -⟩ := hM D.La D.fin D.proj
    let _ : Algebra (OK H) k := (β.comp κ).toAlgebra
    have := C.P.smoothDim
    have key := lieMult_tensor_of_finrank (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) C.v C.basis C.act κ
      T.t.act t.ten hκ t.lin β (fun _ => rfl) χ
    have hw : algebraMap (OK H) (𝓞 E) (wK H) = H.w0 := rfl
    have hrt : algebraMap (OK H) (𝓞 E) (2 * wK H - 1) = H.rt := by
      rw [map_sub, map_mul, hw, map_ofNat, H.two_weight_eq_one_add_root, map_one, add_sub_cancel_left]
    have hr : β (2 * ω - 1) = algebraMap (OK H) k (2 * wK H - 1) := by
      change _ = β (κ _)
      simp only [map_sub, map_mul, map_ofNat, map_one, hκw]
    rw [hr]
    refine ⟨fun h => key _ ((finrank_eigenSub χ (RingHom.ext fun c => ?_)).trans D.rank), fun h => ?_⟩
    · have hw' : χ (algebraMap (OK H) (𝓞 E) (wK H)) = algebraMap (OK H) k (wK H) := by
        rw [← hrt] at h
        simp only [map_sub, map_mul, map_ofNat, map_one] at h
        linear_combination h / 2
      obtain ⟨m, rfl, -⟩ := hgen c
      simp only [RingHom.comp_apply, map_add (f := _), map_mul, map_intCast, hw']
    · refine key _ (Submodule.finrank_eq_zero.2 ((Submodule.eq_bot_iff _).2 fun y hy => ?_))
      have h1 := EigenSplit.mem_eigenSub.1 hy H.rt
      have h2 : rightAction k (OK H) (𝓞 E) D.La H.rt = algebraMap (OK H) k (2 * wK H - 1) • LinearMap.id := by
        ext m
        simp only [TensorProduct.AlgebraTensorModule.curry_apply,
          TensorProduct.curry_apply, LinearMap.coe_restrictScalars, rightAction_tmul, LinearMap.smul_apply,
          LinearMap.id_apply]
        rw [← hrt, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul k]
      rw [h2] at h1
      have h3 : (χ H.rt - algebraMap (OK H) k (2 * wK H - 1)) • y = 0 := by
        rw [sub_smul, ← h1]; exact sub_self _
      exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormMulDetGram
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.TopDifferential

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {F : DualNumber R →+* DualNumber R'}
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_mul, h₁, h₁, h₂, ← e]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem det_gram {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 * Hm.det.re := by
  have e : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)) =
      (Real.pi : ℂ) • (W * (Hm * W.conjTranspose)).transpose := rfl
  rw [e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Fintype.card_fin, mul_left_comm W.det, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    mul_comm Hm.det, ← _root_.mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

end GlobalTheory.CM.TopDifferential
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem pat_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (T : PAT H (Sp R)), (∃ (T' : PAT H (Sp R')) (_ : SABMap T'.t T.t (spMap f)), T'.g = T.g) ∧ ∀ (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), Nontrivial R' → T'.g = T.g ∧ IsPolFibre f T.pol T'.pol m.φ ∧ ∃ w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ), RigIso m w := by
  intro E _ _ _ H R R' _ _ f T
  refine ⟨?_, fun T' m hR => ?_⟩
  · obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) T.t
    obtain ⟨⟨T', ht, hg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    exact ⟨T', ht ▸ m, hg⟩
  · obtain ⟨-, e⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    have hd : SmoothOfRelativeDimension T.g T'.t.G.hom :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
    have hg : T'.g = T.g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ T'.dim hd (eSec T'.t.G p)
    obtain ⟨w, hw, hr, -⟩ := m.lin
    exact ⟨hg, ⟨hg, m.cart, e⟩, w, hw, hr⟩

end GlobalTheory.LamT
end

