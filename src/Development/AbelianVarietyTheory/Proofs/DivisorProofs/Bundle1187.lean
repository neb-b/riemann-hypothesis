module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmFnAndKilledFnOfHolFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLawOfKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem kltAt_add_smul_of_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (δ : ℚ) (x : X), IsQCart D → KltAt p n Δ x → LcAt p n (Δ + D) x → 0 < δ →
      δ ≤ 1 → KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D δ x hD hk hl hδ hδ1
  obtain ⟨η, m, g, hη, hm, hg, hkl⟩ := hk
  obtain ⟨m', f, hm', -, hf⟩ := _root_.GlobalTheory.PairStep.exists_localEqn_of_isQCart X p D hD x
  obtain ⟨m₁, g₁, hm₁, h₁, e₁⟩ := _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n Δ D η x m m' g f 1 hm hm' hg hf
  obtain ⟨m₂, g₂, hm₂, h₂, e₂⟩ := _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n Δ D η x m m' g f (1 - δ) hm hm' hg hf
  rw [one_smul] at h₁
  have hlc := (_root_.GlobalTheory.PairStep.lcAt_iff_of_isLogEqn X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ h₁).1 hl
  refine ⟨η, m₂, g₂, hη, hm₂, h₂, fun E hE => ?_⟩
  have a := hkl E hE
  have b := hlc E hE
  rw [e₁] at b
  rw [e₂]
  set t : ℚ := (E.ord f : ℚ) / m'
  set d := discrep E η m g
  have h1 : -δ < δ * d := by nlinarith
  have h2 : -(1 - δ) ≤ (1 - δ) * (d - 1 * t) := by nlinarith
  nlinarith

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeff
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  intro X _ _ _ p n _ _ Γ B a b x hB hab
  obtain ⟨m', f, hm', hf, hBf⟩ := _root_.GlobalTheory.PairStep.exists_localEqn_of_isQCart X p B hB x
  have key : ∀ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), 0 < m →
      IsLogEqn p (Γ + b • B) η x m g →
      ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + a • B) η x m'' g'' ∧
        ∀ E : DivOver p, E.Through x → discrep E η m g ≤ discrep E η m'' g'' := by
    intro η m g hm hlog
    obtain ⟨m'', g'', hm'', hlog'', hd⟩ :=
      _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n (Γ + b • B) B η x m m' g f (a - b) hm hm' hlog hBf
    have e : Γ + b • B + (a - b) • B = Γ + a • B := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at hlog''
    refine ⟨m'', g'', hm'', hlog'', fun E hE => ?_⟩
    have h0 : (0 : ℚ) ≤ E.ord f := by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)
    have h1 : (0 : ℚ) ≤ (E.ord f : ℚ) / m' := div_nonneg h0 (Nat.cast_nonneg _)
    rw [hd E]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) h1]
  refine ⟨fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_, fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => lt_of_lt_of_le (hk E hE) (hle E hE)⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => le_trans (hk E hE) (hle E hE)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzTermEqDefinitePairOfLocalIsometry
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDefTerm

theorem pointSum_equiv {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ ≃* Γ')
    (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (ι₁' : Γ' →* G₁) (ι₂' : Γ' →* G₂) (h₁ : ∀ y, ι₁' (e y) = ι₁ y)
    (h₂ : ∀ y, ι₂' (e y) = ι₂ y) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f : G₁ → ℂ) (φ : G₂ → ℂ) :
    pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ = pointSum ι₁' ι₂' θ K₁ K₂ γ δ f φ := by
  have e₁ : ι₁ = ι₁'.comp e.toMonoidHom := MonoidHom.ext fun y => (h₁ y).symm
  have e₂ : ι₂ = ι₂'.comp e.toMonoidHom := MonoidHom.ext fun y => (h₂ y).symm
  subst e₁ e₂
  have hr : ((ι₁'.comp e.toMonoidHom).prod (ι₂'.comp e.toMonoidHom)).range = (ι₁'.prod ι₂').range := by
    ext g
    simp only [MonoidHom.mem_range, MonoidHom.prod_apply, MonoidHom.comp_apply]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨e y, hy⟩
    · rintro ⟨y, hy⟩; exact ⟨e.symm y, by simpa using hy⟩
  have hc : ∀ x : G₁ × G₂, Nat.card (stab (ι₁'.comp e.toMonoidHom) (ι₂'.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁' ι₂' K₁ K₂ x) := by
    intro x
    have : stab (ι₁'.comp e.toMonoidHom) (ι₂'.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁' ι₂' K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [this]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv fun a => Iff.rfl)
  unfold pointSum
  simp only [hc]
  rw [hr]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem quot_commute (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) :
    ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (P.γ : G.C) = (P.γ : G.C) * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) := by
  have hP := P.sim
  have hQ := Q.sim
  rw [hγ, hc] at hP
  rw [hγ]
  set γ := Q.γ
  set c := Q.c
  set b₁ := P.β
  set b₂ := Q.β
  set C := algebraMap ℚ G.C (c : ℚ)
  have hs : sh G (γ : G.C) = ((b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (C * b₂) := by
    rw [← hQ]; simp only [← mul_assoc, Units.inv_mul_cancel_left]
    rw [mul_assoc ((b₂⁻¹ : G.Cˣ) : G.C), Units.inv_mul, mul_one, Units.inv_mul, one_mul]
  have hCu : IsUnit C := c.isUnit.map (algebraMap ℚ G.C)
  have h := congrArg (· * ((b₂⁻¹ : G.Cˣ) : G.C)) hP
  rw [hs] at h
  have key : C * ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) =
      C * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) := by
    calc C * ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C))
        = ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * C := Algebra.commutes _ _
      _ = (γ : G.C) * b₁ * (((b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (C * b₂)) *
            ((b₂⁻¹ : G.Cˣ) : G.C) := by
          simp only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = C * b₁ * ((b₂⁻¹ : G.Cˣ) : G.C) := h
      _ = _ := by simp only [Units.val_mul, mul_assoc]
  have k2 := hCu.mul_left_cancel key
  calc ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * (γ : G.C)
      = ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [k2]
    _ = _ := by simp only [mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem commute_quot (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) (y : G.C)
    (hy : y * (P.γ : G.C) = (P.γ : G.C) * y) :
    y * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * y := by
  obtain ⟨w, hw⟩ := (GlobalTheory.LKCentAf.cent_iff_mem P _).1 (quot_commute P Q hγ hc)
  have hb : ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) ∈ Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C) := by
    rw [← hw]; exact w.2
  exact Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hy

theorem cent_eq (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) : P.cent = Q.cent := by
  ext ⟨y, s⟩
  change (y * P.γ = P.γ * y ∧ (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β) ↔
    (y * Q.γ = Q.γ * y ∧ (y : G.C) * Q.β * sh G y = algebraMap ℚ G.C s * Q.β)
  rw [← hγ]
  refine and_congr_right fun h1 => ?_
  have hy : (y : G.C) * (P.γ : G.C) = (P.γ : G.C) * y := by rw [← Units.val_mul, h1, Units.val_mul]
  have hcomm := commute_quot P Q hγ hc y hy
  set b : G.Cˣ := P.β * Q.β⁻¹
  have hβ : (P.β : G.C) = (b : G.C) * Q.β := by simp [b, mul_assoc]
  rw [hβ]
  have e1 : (y : G.C) * (b * Q.β) * sh G y = b * ((y : G.C) * Q.β * sh G y) := by
    rw [← mul_assoc (y : G.C), hcomm]; simp only [mul_assoc]
  have e2 : algebraMap ℚ G.C s * ((b : G.C) * Q.β) = b * (algebraMap ℚ G.C s * Q.β) := by
    rw [← mul_assoc, Algebra.commutes, mul_assoc]
  rw [e1, e2]
  constructor
  · intro h
    have := congrArg (((b⁻¹ : G.Cˣ) : G.C) * ·) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  · intro h; rw [h]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem triv_mul_inv (bP bQ : G.C) (x u : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) bQ x t)
    (hu : (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) bQ * (starT G.star (AfP p) u).unop = inC G (AfP p) bP) :
    Triv G (AfP p) bP (x * u⁻¹) t := by
  unfold Triv at *
  have hs : (starT G.star (AfP p) (((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop =
      (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop *
        (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : (starT G.star (AfP p) (u : AfP p ⊗[ℚ] G.C)).unop *
      (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [hs, ← hu, ← hx]
  calc ((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        ((u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) bQ * (starT G.star (AfP p) u).unop) *
        ((starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop *
          (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop)
      = (x : AfP p ⊗[ℚ] G.C) * (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * u) * inC G (AfP p) bQ *
          ((starT G.star (AfP p) (u : AfP p ⊗[ℚ] G.C)).unop *
            (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop) *
          (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, mul_one, mul_one]

theorem termAt_eq (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) (x u : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) Q.β x t) (hx' : Triv G (AfP p) P.β (x * u⁻¹) t)
    (hu : (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (δ z : Gr G r) :
    P.termAt Kf f r K φ (x * u⁻¹) t hx' δ z = Q.termAt Kf f r K φ x t hx δ z := by
  set e : P.cent ≃* Q.cent := MulEquiv.subgroupCongr (cent_eq P Q hγ hc)
  have h₁ : ∀ y, Q.toAf x t hx (e y) = P.toAf (x * u⁻¹) t hx' y := by
    intro y
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    apply Units.ext
    have hyc : ((y : G.Cˣ × ℚˣ).1 : G.C) * (P.γ : G.C) = (P.γ : G.C) * (y : G.Cˣ × ℚˣ).1 := by
      rw [← Units.val_mul, y.2.1, Units.val_mul]
    have hc1 : ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hyc]
    have hc2 : (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) * u := by rw [hγ]; exact hu
    have hcomm := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _
      (GlobalTheory.LKCentAf.cent_iff_mem P) _ _ hc2 hc1
    show (x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      ((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) *
        (((x * u⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
    have hY : ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * u) = (1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C) := by
      rw [← hcomm, ← mul_assoc, Units.inv_mul, one_mul]
    calc (x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) *
          ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
        = (x : AfP p ⊗[ℚ] G.C) * (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
            (((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * u)) *
            ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by rw [hY]
      _ = _ := by simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]
  have hself : e P.self = Q.self := Subtype.ext (by
    show ((P.γ, P.c) : G.Cˣ × ℚˣ) = (Q.γ, Q.c)
    rw [hγ, hc])
  have hs : P.toAf (x * u⁻¹) t hx' P.self = Q.toAf x t hx Q.self := by rw [← h₁, hself]
  unfold Pair.termAt DPair.termAt
  rw [hs]
  exact pointSum_equiv e _ _ _ _ h₁ (fun y => rfl) _ _ _ _ _ _ _

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

theorem term_eq_of_local_isom : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Q : DPair G), P.γ = Q.γ → P.c = Q.c → (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C)) → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.term Kf f r K φ = Q.term Kf f r K φ := by
  intro p _ G P Q hγ hc hu Kf f r K φ hr hf hφ
  obtain ⟨u, huγ, huβ⟩ := hu
  have hat : P.atP = Q.atP := by
    unfold Pair.atP DPair.atP
    rw [hγ, hc]
  unfold DPair.term
  split_ifs with h
  · have hQ := Q.trivAf.choose_spec.choose_spec
    have hx' := triv_mul_inv (P.β : G.C) (Q.β : G.C) _ u _ hQ huβ
    rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f r K φ hr hf hφ _ _ hx' h.choose.1 h.choose.2 (by rw [hat]; exact h.choose_spec)]
    exact termAt_eq P Q hγ hc _ u _ hQ hx' huγ Kf f r K φ _ _
  · unfold Pair.term
    rw [dite_eq_right]
    rwa [hat]

end GlobalTheory.LKDefTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVec
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.InterpolationCoefficientsInL2

lemma inner_iso_eigen {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : K →L[ℂ] K)
    (hU : ∀ x, ‖U x‖ = ‖x‖) {F : K} {c : ℂ} (hc : ‖c‖ = 1) (hF : U F = c • F) (G : K) :
    ⟪F, U G⟫_ℂ = c * ⟪F, G⟫_ℂ := by
  have h := (LinearIsometry.mk (U : K →ₗ[ℂ] K) hU).inner_map_map F G
  change ⟪U F, U G⟫_ℂ = _ at h
  rw [hF, inner_smul_left] at h
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [← h, ← mul_assoc, h1, one_mul]

lemma rep_mul_apply {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (a b : G) (F : K) : ρ (a * b) F = ρ a (ρ b F) := by
  rw [map_mul]; rfl

lemma inner_rep_one {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (F : K) : ⟪F, ρ 1 F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  simp

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}

lemma holFn_congr {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (h : ∀ u ∈ UG Hm, g u = f u) :
    HolFn Hm q x₀ w g := by
  obtain ⟨P, hP, hf⟩ := hf
  exact ⟨P, hP, fun u hu => (h u hu).trans (hf u hu)⟩

lemma holFn_const_mul {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (c : ℂ) :
    HolFn Hm q x₀ w fun u => c * f u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  refine ⟨fun x => c * P x, ⟨hP1.const_mul c, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu]

lemma holFn_sub {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g) :
    HolFn Hm q x₀ w fun u => f u - g u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  obtain ⟨Q, ⟨hQ1, hQ2⟩, hg⟩ := hg
  refine ⟨fun x => P x - Q x, ⟨hP1.sub hQ1, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb, hQ2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu, hg u hu]

omit [Fintype ι] in
lemma one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := by
  intro τ
  change (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp


lemma norm_prod_exp (w : Fin n → ℤ) (s : Fin n → ℝ) :
    ‖∏ a, Complex.exp ((s a : ℂ) * Complex.I) ^ w a‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [norm_zpow, Complex.norm_exp_ofReal_mul_I, _root_.one_zpow]

lemma norm_torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ‖torCh w s‖ = 1 := by
  unfold torCh
  rw [norm_prod]
  exact Finset.prod_eq_one fun τ _ => norm_prod_exp _ _

lemma eq_const_mul [DecidableEq ι] (hO : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f g : (ι → Mt n) → ℂ} (c : ℂ)
    (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g)
    (hfl : ∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u)
    (hgl : ∀ u ∈ UG Hm, ∀ s, g (torEl x₀ s * u) = torCh w s * g u) (hf1 : f 1 = c) (hg1 : g 1 = 1) :
    ∀ u ∈ UG Hm, f u = c * g u := fun u hu =>
  sub_eq_zero.1 (GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law n ι Hm q x₀ w hO _ (holFn_sub hf (holFn_const_mul hg c))
    (fun u hu s => by beta_reduce; rw [hfl u hu, hgl u hu]; ring)
    (by beta_reduce; rw [hf1, hg1, mul_one, sub_self]) u hu)

end Local

end GlobalTheory.HolDict.InterpolationCoefficientsInL2


open GlobalTheory.HolDict.InterpolationCoefficientsInL2 in
theorem GlobalTheory.HolDict.inner_reg_eq_coef_extremal : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  classical
  intro D θ V S M w v hθ hS hW hv μ 𝓕 ρ hfin hreg J χ φ F hφ hF u₀ hu₀
  refine (GlobalTheory.RealLift.exists_real_lift D θ V hθ).elim fun L hL => ?_
  have hL1 := hL.1
  have hLmul := hL.2.1
  have hUG := hL.2.2.2.1
  have hLinv := hL.2.2.2.2.1
  have hB := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).1
  have hBt := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).2
  have hO : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) :=
    fun τ => ((GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hS).1
  have hU : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  have htm : ∀ s, torEl (x0Mat M) s ∈ UG (gramAt D V) := fun s => by
    simpa using TorusLaw.mul_torEl_mem hO s (one_mem_UG (Hm := gramAt D V))
  have hL0 : L 1 = 1 := by
    have h := hLmul 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    exact mul_left_cancel (a := L 1) (by rw [← h, mul_one])

  have horb : ∀ x, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => φ (x * L u) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := hφ.hol x
    refine holFn_congr hf fun u hu => ?_
    rw [hfx _ (hL1 u hu).1]
    congr 1
    funext τ
    exact (hL1 u hu).2 τ
  have htor : ∀ s x, φ (x * L (torEl (x0Mat M) s)) = torCh w s * φ x := by
    intro s x
    obtain ⟨h1, h2⟩ := GlobalTheory.HolDict.smFn_and_killedFn_of_holFn _ _ _ _ _ _ hO _ (horb x)
    have := GlobalTheory.HolDict.torus_law_of_killed _ _ _ _ _ _ hO _ h1 h2 1 one_mem_UG s
    simpa [hL0] using this
  refine hφ.bdd.elim fun C hC => ?_
  have hR := (GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hfin hreg).2.2
  have hR3 := hR.1
  have hR4 := hR.2.1
  have hR5 := hR.2.2.1
  have hR6 := hR.2.2.2
  have hρt : ∀ s, ρ (L (torEl (x0Mat M) s)) F = torCh w s • F := by
    intro s
    have h1 := hR4 F φ (L (torEl (x0Mat M) s)) hF
    have h2 := hR5 F F φ φ (torCh w s - 1) hF hF
    have e1 : (torCh w s - 1) • F + F = torCh w s • F := by rw [sub_smul, one_smul, sub_add_cancel]
    have e2 : (torCh w s - 1) • φ + φ = rTr V (L (torEl (x0Mat M) s)) φ := by
      funext x
      simp only [rTr, htor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2] at h2
    exact hR3 _ _ _ h1 h2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.fin
  have hA : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => ⟪F, ρ (L u) F⟫_ℂ := by
    have h := GlobalTheory.HolDict.holFn_integral _ _ _ _ _ w hO (GA D V) (μ.restrict 𝓕) (fun x u => star (φ x) * φ (x * L u)) (C * C)
      (fun x => holFn_const_mul (horb x) _)
      (fun x u _ => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))
      (fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).1.aestronglyMeasurable)
    exact holFn_congr h fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).2
  have key := eq_const_mul hO ((‖F‖ ^ 2 : ℝ) : ℂ) hA hB
    (fun u hu s => ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLmul _ (htm s) _ hu)).trans
      (congrArg (fun G => ⟪F, G⟫_ℂ) (rep_mul_apply ρ _ _ F))).trans
      (inner_iso_eigen _ (hreg.iso _) (norm_torCh w s) (hρt s) _))
    (fun u hu s => by
      have a2 : ∀ τ, ⟪(v τ : M.H τ), M.rep τ ((torEl (x0Mat M) s * u) τ) (v τ : M.H τ)⟫_ℂ =
          (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := by
        intro τ
        refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ)
          ((hU τ).1.2 _ (htm s τ) _ (hu τ))).trans ?_
        exact inner_iso_eigen _ ((hU τ).2.1 _ (htm s τ)) (norm_prod_exp _ _) (hBt s τ) _
      exact (Finset.prod_congr rfl fun τ _ => a2 τ).trans Finset.prod_mul_distrib)
    ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) hL0).trans (inner_rep_one ρ F))
    (Finset.prod_eq_one fun τ _ => by
      refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) (hU τ).1.1).trans ?_
      change ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
      simp)
    _ (hUG u₀)
  exact (congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLinv u₀ hu₀)).symm.trans key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (C H : ∀ v, Subgroup (Y v)), (∀ v, (H v).relIndex (C v) ≠ 0) → (∀ᶠ v in cofinite, C v ≤ H v) → (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  first | exact @GlobalTheory.RelIdxRestr.relIndex_iInf_comap | exact GlobalTheory.RelIdxRestr.relIndex_iInf_comap | (intros; apply GlobalTheory.RelIdxRestr.relIndex_iInf_comap <;> assumption)
end

