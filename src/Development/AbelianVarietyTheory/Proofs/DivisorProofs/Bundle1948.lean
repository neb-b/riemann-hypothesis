module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberSectionValue_linearCombination : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  first | exact @GlobalTheory.DualLin.sE_comb | exact GlobalTheory.DualLin.sE_comb | (intros; apply GlobalTheory.DualLin.sE_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDetSubOneOfCongModThreeLe
section
open GlobalTheory.Poinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L N : ℕ) (hL : 3 ≤ L)
    (γ : X ≃ₗ[ℤ] X) (hγ : ∀ x, CongMod L (γ x) x) : (N : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
  set b := Module.Free.chooseBasis ℤ X
  have hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det :=
    (LinearMap.det_toMatrix b _).symm
  have hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hγ (b j)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw,
      map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]
    rw [Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1 := by
    rw [hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))
    simp only [eq_intCast] at this
    rw [this, hmap, Matrix.det_one]
  have hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, sub_self]
  rcases Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h
  · rw [h, sub_self]; exact dvd_zero _
  · exfalso
    rw [h] at hdvd
    have h2 : (L : ℤ) ∣ 2 := by
      have : (2 : ℤ) = -(-1 - 1) := by norm_num
      rw [this]; exact (dvd_neg).2 hdvd
    have : L ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

theorem GlobalTheory.dvr_eq_localization_integralClosure : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) → ∀ s ∈ V, ∃ b d : L, (b ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ b = 0) ∧ (d ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ d = 0) ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro K L _ _ _ φ hfin V _ hE s hs
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hfin
  set E : ValuationSubring K := V.comap φ with hEdef
  letI : Algebra E L := (φ.comp E.subtype).toAlgebra
  haveI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsFractionRing E K := inferInstance
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure E L) := integralClosure.isDedekindDomain E K L
  haveI : IsFractionRing (integralClosure E L) L := integralClosure.isFractionRing_of_finite_extension K L

  have hBV : ∀ x : L, IsIntegral E x → x ∈ V := by
    intro x hx
    letI : Algebra E V := ((φ.comp E.subtype).codRestrict V (fun y => y.2)).toAlgebra
    haveI : IsScalarTower E V L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have h2 : IsIntegral V x := IsIntegral.tower_top hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]; exact y.2

  have hpoly : ∀ x : L, IsIntegral E x →
      ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 := by
    rintro x ⟨p, hpm, hp⟩
    refine ⟨p.map E.subtype, hpm.map _, fun i => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff i).2
    · rw [Polynomial.eval₂_map]; exact hp
  set B := integralClosure E L
  let f : B →+* V :=
    { toFun := fun b => ⟨(b : L), hBV _ b.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  haveI hnp : n.IsPrime := Ideal.comap_isPrime _ _

  have hn0 : n ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E
    have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    intro hbot
    have hmem : algebraMap E B ϖ ∈ n := by
      show f (algebraMap E B ϖ) ∈ IsLocalRing.maximalIdeal V
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hϖ.not_isUnit
      have h1 : ((u⁻¹ : Vˣ) : V) * f (algebraMap E B ϖ) = 1 := by rw [← hu]; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V) : L)) * φ ϖ = 1 := congrArg Subtype.val h1
      have h3 : (ϖ : K)⁻¹ ∈ E := by
        show φ ((ϖ : K)⁻¹) ∈ V
        rw [map_inv₀, inv_eq_of_mul_eq_one_left h2]; exact (((u⁻¹ : Vˣ) : V)).2
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h3⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩
    rw [hbot, Ideal.mem_bot] at hmem
    have h4 : φ (ϖ : K) = 0 := congrArg (fun b : B => (b : L)) hmem
    exact hϖ0 ((map_eq_zero φ).1 h4)
  have hunit : ∀ d : B, d ∉ n → (d : L) ≠ 0 ∧ (d : L)⁻¹ ∈ V := by
    intro d hd
    have hu : IsUnit (f d) := by
      by_contra h
      exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu
    have h1 : f d * ((u⁻¹ : Vˣ) : V) = 1 := by rw [← hu]; exact u.mul_inv
    have h2 : (d : L) * ((((u⁻¹ : Vˣ) : V) : L)) = 1 := congrArg Subtype.val h1
    refine ⟨left_ne_zero_of_mul_eq_one h2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h2]; exact (((u⁻¹ : Vˣ) : V)).2
  let O := Localization.AtPrime n
  letI : Algebra O L := IsLocalization.localizationAlgebraOfSubmonoidLe O L n.primeCompl
    (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsScalarTower B O L := IsLocalization.localization_isScalarTower_of_submonoid_le O L
    n.primeCompl (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsFractionRing O L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization n.primeCompl O L
  haveI : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hn0 O
  have hO : ∀ z : O, ∃ b d : B, d ∉ n ∧ algebraMap O L z * (d : L) = (b : L) := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective n.primeCompl z
    refine ⟨a, t, t.2, ?_⟩
    show algebraMap O L (IsLocalization.mk' O a t) * algebraMap B L t = algebraMap B L a
    rw [IsScalarTower.algebraMap_apply B O L (t : B), IsScalarTower.algebraMap_apply B O L a,
      ← map_mul, IsLocalization.mk'_spec]
  by_cases hs0 : s = 0
  · refine ⟨0, 1, ⟨hBV _ isIntegral_zero, hpoly _ isIntegral_zero⟩,
      ⟨hBV _ isIntegral_one, hpoly _ isIntegral_one⟩, one_ne_zero, by rw [inv_one]; exact V.one_mem, ?_⟩
    rw [hs0, zero_div]
  rcases ValuationRing.isInteger_or_isInteger O s with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    refine ⟨b, d, ⟨hBV _ b.2, hpoly _ b.2⟩, ⟨hBV _ d.2, hpoly _ d.2⟩, (hunit d hd).1,
      (hunit d hd).2, ?_⟩
    rw [← hz, ← hbd, mul_div_cancel_right₀ _ (hunit d hd).1]
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    rw [hz] at hbd
    have hsb : s * (b : L) = d := by rw [← hbd, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hb : b ∉ n := by
      intro hb
      have hb' : ¬ IsUnit (f b) := (IsLocalRing.mem_maximalIdeal _).1 hb
      have hfd : IsUnit (f d) := by
        by_contra h
        exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
      have hm : (⟨s, hs⟩ : V) * f b = f d := Subtype.ext hsb
      rw [← hm] at hfd
      exact hb' (isUnit_of_mul_isUnit_right hfd)
    refine ⟨d, b, ⟨hBV _ d.2, hpoly _ d.2⟩, ⟨hBV _ b.2, hpoly _ b.2⟩, (hunit b hb).1,
      (hunit b hb).2, ?_⟩
    rw [eq_div_iff (hunit b hb).1, hsb]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbundleFrameAffineAtlasIsFlagFrameCover
section
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_embK_ne {σ σ' : E →+* ℂ} (h : σ ≠ σ') : ∃ a : 𝓞 E, embK c σ a ≠ embK c σ' a := by
  by_contra hc
  push_neg at hc
  refine h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))
  have := congrArg Subtype.val (hc a)
  simpa [embK, embF] using this

theorem pm_mul_pm {Y : Model Xo c (RingHom.id c.F)} (p : Proj (RingHom.id c.F)) (M : MChart Y) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : LowRank.pm p M σ * LowRank.pm p M σ' = 0 := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c c.F (RingHom.id c.F) Y M
  letI : Algebra c.F Γ(Y.X, M.U) := (str (tau M.hU)).toAlgebra
  have hP : ∀ τ, LowRank.pm p M τ =
      ∑ k, algebraMap c.F Γ(Y.X, M.U) (RingHom.id c.F (p.κ τ k)) • ρ (p.a τ k) :=
    fun τ => by simp only [LowRank.pm, hρ]; rfl
  obtain ⟨a, ha⟩ := exists_embK_ne (c := c) h
  have h1 := (p.spec σ Γ(Y.X, M.U) M.n ρ).1 a
  have h1' := (p.spec σ' Γ(Y.X, M.U) M.n ρ).1 a
  rw [← hP] at h1 h1'
  have hc : ρ a * LowRank.pm p M σ = LowRank.pm p M σ * ρ a := by
    rw [hP, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, mul_comm]
  have e1 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul]
  have e2 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ' a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, h1', Matrix.mul_smul]
  have hd : embK c σ a - embK c σ' a ≠ 0 := sub_ne_zero.2 ha
  have e3 : algebraMap c.F Γ(Y.X, M.U) (embK c σ a - embK c σ' a) •
      (LowRank.pm p M σ * LowRank.pm p M σ') = 0 := by
    rw [map_sub, sub_smul, ← e1, ← e2, sub_self]
  calc LowRank.pm p M σ * LowRank.pm p M σ'
      = algebraMap c.F Γ(Y.X, M.U) ((embK c σ a - embK c σ' a)⁻¹ * (embK c σ a - embK c σ' a)) •
        (LowRank.pm p M σ * LowRank.pm p M σ') := by
        rw [inv_mul_cancel₀ hd, map_one, one_smul]
    _ = 0 := by rw [map_mul, mul_smul, e3, smul_zero]

theorem eCh_w_mul_u {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (k : ECh Y p) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : k.w σ * k.u σ' = 0 := by
  calc k.w σ * k.u σ' = (k.w σ * k.u σ) * k.w σ * (k.u σ' * (k.w σ' * k.u σ')) := by
        rw [k.wu, k.wu, Matrix.one_mul, Matrix.mul_one]
    _ = k.w σ * ((k.u σ * k.w σ) * (k.u σ' * k.w σ')) * k.u σ' := by simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [k.uw, k.uw, ← Matrix.map_mul, pm_mul_pm p _ h, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
          Matrix.zero_mul]

end GlobalTheory.FlagMod.FieldFlag


open GlobalTheory.FlagMod.FieldFlag MonoidalCategory CartesianMonoidalCategory MonObj in
theorem GlobalTheory.FlagMod.FieldFlag.atlas_isCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p), IsCover (RingHom.id c.F) Y.s A.V A.alpha A.cv A.Dv := by
  intro E _ _ _ H Dw l Xo c Y p A
  classical
  refine ⟨fun b => ?_, fun b => ?_, fun k _ b b' φ φ' hx => ?_⟩
  · rw [RingHom.comp_id]
    exact (spMap_ev_top (tau (A.aff b) ≫ Y.s)).symm
  · rintro ⟨σ, i⟩ ⟨σ', j⟩
    have e : ∑ r, A.Dv b ⟨σ, i⟩ r * A.cv b ⟨σ', j⟩ r = ((A.k b).w σ * (A.k b).u σ') i j := by
      have : (A.k b).w σ * (A.k b).u σ' = ((A.k b).w σ * A.C b) * (A.A b * (A.k b).u σ') := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.C b), A.CA, Matrix.one_mul]
      rw [this, Matrix.mul_apply]
      rfl
    rw [e]
    by_cases hs : σ = σ'
    · subst hs
      rw [(A.k b).wu]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.one_apply_ne hij, if_neg]
        intro h'
        exact hij (eq_of_heq (Sigma.mk.inj_iff.1 h').2)
    · rw [eCh_w_mul_u _ hs, Matrix.zero_apply, if_neg]
      intro h'
      exact hs (congrArg Sigma.fst h')
  · have h0 : ⊤ ≤ (spMap φ ≫ (A.V b).2.fromSpec) ⁻¹ᵁ (A.k b).V := le_preimage_comp _ (tau_le (A.aff b) le_rfl)
    have h0' : ⊤ ≤ (spMap φ' ≫ (A.V b').2.fromSpec) ⁻¹ᵁ (A.k b').V :=
      le_preimage_comp _ (tau_le (A.aff b') le_rfl)
    set x := spMap φ ≫ (A.V b).2.fromSpec with hxdef
    have h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V := h0
    have h' : ⊤ ≤ x ⁻¹ᵁ (A.k b').V := hx ▸ h0'
    have hφ : ev x _ h = φ := ev_spMap_tau (A.aff b) φ h
    have hφ' : ev x _ h' = φ' := (ev_congr hx _ h' h0').trans (ev_spMap_tau (A.aff b') φ' h0')
    have hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
    have hM' : ⊤ ≤ x ⁻¹ᵁ (A.k b').M.U := le_preimage_mono (A.k b').le h'
    have hMM : ⊤ ≤ x ⁻¹ᵁ ((A.k b).M.U ⊓ (A.k b').M.U) := le_preimage_inf hM hM'
    obtain ⟨a, ha⟩ := A.tw k x b' b h' h hMM
    rintro ⟨σ, j⟩
    set v : Fin (A.k b').M.n → k := (((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) with hvdef
    set y := ((chg (A.k b).M.toMChart (A.k b').M.toMChart).map (ev x _ hMM)).mulVec v with hydef
    have hv : ((LowRank.pm p (A.k b').M.toMChart σ).map (ev x _ hM')).mulVec v = v :=
      ((A.k b').fix_iff σ x h' hM' v).2 ⟨_, rfl⟩
    have hy : ((LowRank.pm p (A.k b).M.toMChart σ).map (ev x _ hM)).mulVec y = y := by
      have h2 := congrArg (vec (A.k b').M.toMChart x hM') hv
      rw [LowRank.vec_pm, ← vec_chg (A.k b).M.toMChart (A.k b').M.toMChart x hM hM' hMM, ← LowRank.vec_pm] at h2
      exact (vec _ _ _).injective h2
    obtain ⟨t, ht⟩ := ((A.k b).fix_iff σ x h hM y).1 hy
    have key : φ' ∘ A.cv b' ⟨σ, j⟩ = ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t := by
      calc φ' ∘ A.cv b' ⟨σ, j⟩
          = ((A.A b').map (ev x _ h') * ((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) := by
            rw [hφ']
            funext r
            rw [Matrix.mulVec_single_one, ← Matrix.map_mul]
            rfl
        _ = (a : k) • ((A.A b).map (ev x _ h)).mulVec y := by
            rw [← Matrix.mulVec_mulVec, ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        _ = (a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ).mulVec t := by
            rw [← ht, Matrix.mulVec_mulVec, hφ]
        _ = _ := (Matrix.smul_mulVec _ _ _).symm
    have col : ∀ i, φ ∘ A.cv b ⟨σ, i⟩ = fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := fun i => by
      funext r
      rw [← Matrix.map_mul]
      rfl
    have hsum : ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t =
        ∑ i, ((a : k) * t i) • fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := by
      funext r
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    show φ' ∘ A.cv b' ⟨σ, j⟩ ∈ Submodule.span k (Set.range fun i => φ ∘ A.cv b ⟨σ, i⟩)
    rw [key, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, col i⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolar
section
open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem qW_polar_eq_sum_add_transpose {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hβ : ∀ a b, β a b = β b a) (y z : Fin s → X) :
    qW W β (y + z) - qW W β y - qW W β z = ∑ u, ∑ v, (W + W.transpose) u v * β (y u) (z v) := by
  have h : ∑ u, ∑ v, W u v * β (z u) (y v) = ∑ u, ∑ v, W v u * β (y u) (z v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hβ]
  simp only [qW, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.transpose_apply, h]
  ring

theorem eq_adjoint_apply_of_qW_polar (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : PosW W) (X₀ : Type) [AddCommGroup X₀]
    (β : LinearMap.BilinForm ℤ X₀) (hβ : ∀ a b, β a b = β b a) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (E E' : Matrix (Fin 8) (Fin 8) ℤ) (hE : (W + W.transpose) * E' = E.transpose * (W + W.transpose))
    (z z' : Fin 8 → X₀)
    (h : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z =
      qW W β (y + z') - qW W β y - qW W β z') :
    z' = fun a => ∑ b, E' a b • z b := by
  simp only [qW_polar_eq_sum_add_transpose W β hβ] at h
  unfold PosW at hW
  set M := W + W.transpose with hM
  have hdet : M.det ≠ 0 := by
    have h1 := hW.det_pos
    have h2 : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
      rw [Int.cast_det]
    rw [h2] at h1
    intro h0
    simp [h0] at h1
  have key : ∀ x : X₀, (fun v => β x (z' v)) = E' *ᵥ (fun v => β x (z v)) := by
    intro x
    rw [← sub_eq_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hE, sub_eq_zero]
    funext w
    have h1 := h (Pi.single w x)
    have h2 : ∀ a, ∑ b, E a b • (Pi.single w x : Fin 8 → X₀) b = E a w • x := by
      intro a
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    have h3 : ∑ u, ∑ v, M u v * β ((Pi.single w x : Fin 8 → X₀) u) (z' v) = ∑ v, M w v * β x (z' v) := by
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    simp only [h2, h3, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [← h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  funext a
  rw [← sub_eq_zero]
  by_contra hne
  have h1 := hpos _ hne
  generalize hd : z' a - ∑ b, E' a b • z b = d at h1
  have h2 := congrFun (key d) a
  have h3 : β d d = 0 := by
    conv_lhs => rw [show β d d = β d (z' a - ∑ b, E' a b • z b) by rw [hd]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_zsmul, smul_eq_mul, h2, Matrix.mulVec, dotProduct, sub_self]
  omega

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEntireMulEqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FrameAut

theorem eq_zero_of_entire_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hne
  have hc : ContinuousAt D z := hD.continuousAt (hS.mem_nhds hz)
  have he : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hc.eventually_ne hne, hS.mem_nhds hz] with w hw hwS
    exact (mul_eq_zero.1 (h w hwS)).resolve_right hw
  have ha : AnalyticOnNhd ℂ θ Set.univ := SCV.analyticOnNhd_of_differentiable hθ Set.univ
  exact h0 (funext fun w =>
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) he (Set.mem_univ w))

end GlobalTheory.MBLow.Cl.FrameAut

namespace GlobalTheory.MBLow.Cl

theorem frame_eq_autV_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ M N (i : x.P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N) := by
  intro g x hg u τ a b c W hNF M N i z hz
  obtain ⟨hs, hp, ha, hb, hc, hΛ, _, hth, _⟩ := hNF
  obtain ⟨hd, ⟨z₀, hz₀⟩, hlaw⟩ := _root_.GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy g τ a b hs hp ha hb
  have hdc : Differentiable ℂ (fun w => c * thetaChar τ a b w) := (differentiable_const c).mul hd
  have h0 : (fun w => c * thetaChar τ a b w) ≠ 0 := fun h => by
    have := congrFun h z₀
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.elim hc hz₀
  have hl : u.ex (perV τ M N) = 1 := (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩)
  have he : ∀ w, u.ex (w + perV τ M N) = u.ex w := fun w => by rw [u.ex_add, hl, _root_.mul_one]
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} := (u.hol _ 0).1
  have htr : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (u.ex (w + perV τ M N)).left ⁻¹ᵁ x.P.L.U i :=
    fun w hw => by rw [he]; exact hw
  have hcf := (u.fr_hol i).continuousOn
  have haut : Continuous (autV τ a b M N) := by
    unfold autV dotProduct
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - autV τ a b M N w * u.fr i (w + perV τ M N))
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} :=
    hcf.sub (haut.continuousOn.mul (hcf.comp (continuous_add_const _).continuousOn fun w hw => htr w hw))
  refine sub_eq_zero.1 (FrameAut.eq_zero_of_entire_mul_eq_zero hdc h0 hS hD (fun w hw => ?_) hz)
  have h1 := hth i w hw
  have h2 := hth i _ (htr w hw)
  beta_reduce at h1 h2 ⊢
  rw [he, h1, hlaw] at h2
  linear_combination h2

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenNbhdPointMemOpen
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
theorem nbhd_basicOpen_of_mem : ∀ (S : Type) [CommRing S] (X : Scheme.{0}) (x : Sp S ⟶ X) (V : X.Opens) (q : PrimeSpectrum S), x q ∈ V → ∃ f₀ : S, f₀ ∉ q.asIdeal ∧ ⊤ ≤ (spMap (algebraMap S (Localization.Away f₀)) ≫ x) ⁻¹ᵁ V := by
  intro S _ X x V q hq
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (show Set (PrimeSpectrum S) from (x ⁻¹ᵁ V).1)) hq (x ⁻¹ᵁ V).2
  refine ⟨f₀, hqf, ?_⟩
  intro y _
  show x ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f₀)))).base y) ∈ V
  apply hsub
  show f₀ ∉ (PrimeSpectrum.comap (algebraMap S (Localization.Away f₀)) y).asIdeal
  intro h
  exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit f₀))
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieDeterminantLine_ratio_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ) (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q), FrameCover t π s V (HermitianCompactForm.chi c τ) p q → IsSection t π s V (HermitianCompactForm.chi c τ) σ → NowhereZero t π s V (HermitianCompactForm.chi c τ) σ → IsSection t π s V (HermitianCompactForm.chi c τ) σ' → ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  first | exact @GlobalTheory.detLine_exists_ratio | exact GlobalTheory.detLine_exists_ratio | (intros; apply GlobalTheory.detLine_exists_ratio <;> assumption)
end

