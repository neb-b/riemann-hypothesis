module

public import Mathlib
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordMapBasisFun
section
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.ProvRowSide

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def stdHLat (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := L

theorem stdHLat_frames (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) :
    IsUnit ((stdHLat K n L).X v).det := by
  show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
  simp

variable {K}

def coordMap (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W) :
    (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

set_option linter.unusedSectionVars false in
theorem coordMap_basisFun (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W)
    (i : Fin n) : coordMap e c (Pi.basisFun K (Fin n) i) = c i := by
  simp [coordMap, Pi.single_apply, apply_ite e, ite_smul]

theorem normAt_one (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (c : OrthonormalBasis (Fin n) ℂ W) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (fun _ => 1) (InfinitePlace.mk e) x = ‖coordMap e c x‖ := by
  have h1 : coordMap e c x = c.repr.symm (WithLp.toLp 2 (fun i => e (x i))) := by
    rw [← c.sum_repr_symm]; rfl
  rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  simp [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

end Std

section WithRRDef

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

end WithRRDef

section Small

variable (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  {n : ℕ} (c : OrthonormalBasis (Fin n) ℂ EE)

end Small

end GlobalTheory.ProvRowSide

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN
  exact GlobalTheory.isThB_coeff_cong Ω ε X A N l hj hl2 hlN (by omega)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassCupProductGeometric
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zcong (n : ℕ) (A B : ℤ) (h : (A : ZMod (p ^ n)) = B) : Cong (p := p) n (A : Ω) (B : Ω) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨((-k : ℤ) : Ω), isInt_intCast _, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hk
  push_cast at this ⊢
  linear_combination -this

theorem isInt_natCast (m : ℕ) : IsInt (p := p) (m : Ω) := by
  have := isInt_intCast (p := p) (Ω := Ω) (m : ℤ)
  simpa using this

theorem isInt_pow_p (c : ℕ) : IsInt (p := p) ((p : Ω) ^ c) := by
  have := isInt_natCast (p := p) (Ω := Ω) (p ^ c)
  simpa using this

theorem conj_invariant {G M : Type*} [Group G] [AddCommGroup M] (H : Subgroup G) (φ : G → M)
    (hφ : ∀ g ∈ H, ∀ h ∈ H, φ (g * h) = φ g + φ h) {σ h : G} (hσ : σ ∈ H) (hh : h ∈ H) :
    φ (σ * h * σ⁻¹) = φ h := by
  have h1 : φ 1 = 0 := by
    have e := hφ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at e
    have e' : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero, ← e]
    exact add_left_cancel e'
  have h2 : φ σ + φ σ⁻¹ = 0 := by
    rw [← hφ σ hσ σ⁻¹ (H.inv_mem hσ), mul_inv_cancel, h1]
  rw [hφ _ (H.mul_mem hσ hh) _ (H.inv_mem hσ), hφ σ hσ h hh, add_right_comm, h2, zero_add]

theorem zeta_eq_pow (T : Tower p Ω) (m k : ℕ) : T.ζ m = T.ζ (m + k) ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    show _ = T.ζ (m + k + 1) ^ p ^ (k + 1)
    rw [ih, ← T.ζpow (m + k), ← pow_mul, ← pow_succ']

theorem gn_fix_zeta (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [zeta_eq_pow T n k, map_pow, ((mem_gn T _ g).1 hg).1]

theorem kum_add (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T L) r a) : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, a (g * h) = a g + a h := by
  intro g hg h hh
  obtain ⟨χ, hχ⟩ := exists_isCyc T n
  have h1 : χ g = 1 := (isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T hn hg)
  rw [isKum_mul hχ hr ha hg hh, h1, one_mul]

theorem isAlgZp_zeta (T : Tower p Ω) (m : ℕ) : IsAlgZp p (T.ζ m) := by
  refine ⟨Polynomial.X ^ (p ^ m) - Polynomial.C 1,
    Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos m) 1, ?_⟩
  simp [(T.prim m).pow_eq_one]

theorem kum_geo_zero (T : Tower p Ω) {n m : ℕ} {H : Subgroup (Gal p Ω)} {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H (T.ζ m) a) {g : Gal p Ω} (hH : g ∈ H) (hg : g ∈ Ggeo p Ω) : a g = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hg' : ∀ x : Ω, IsAlgZp p x → g x = x := hg
  have e := ha g hH
  rw [hg' _ (isAlgZp_zeta T m)] at e
  have hz : T.ζ m ≠ 0 := (T.prim m).ne_zero (pow_ne_zero _ hp.out.ne_zero)
  have e1 : T.ζ n ^ (a g).val = 1 := mul_right_cancel₀ hz (by rw [one_mul]; exact e.symm)
  have e2 : T.ζ n ^ (a g).val = T.ζ n ^ (0 : ℕ) := by rw [pow_zero]; exact e1
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e2
  simpa using e2

theorem conj_mem_ggeo {σ h : Gal p Ω} (hh : h ∈ Ggeo p Ω) : σ * h * σ⁻¹ ∈ Ggeo p Ω := by
  have hh' : ∀ x : Ω, IsAlgZp p x → h x = x := hh
  show ∀ x : Ω, IsAlgZp p x → (σ * h * σ⁻¹) x = x
  rintro x ⟨P, hP, hPx⟩
  have hx' : IsAlgZp p (σ⁻¹ x) := ⟨P, hP, by
    have := Polynomial.aeval_algHom_apply (σ⁻¹ : Gal p Ω).toAlgHom x (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [hPx, map_zero] at this
    exact this⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh' _ hx', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

end GlobalTheory.EdgeAlg

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

theorem edge_class_cup : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt (p := p) f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  classical
  intro p _ hp2 c₁
  obtain ⟨c', hc'⟩ := GlobalTheory.T.geometric_level_h1_coboundary p hp2
  refine ⟨c₁ + c', ?_⟩
  intro Ω _ _ hclo T L n hnL x y lz lq η f hxy hlz hlq hfi hff hη hηlc hcob
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨W, ⟨hWi, hWlc⟩, hW⟩ := hcob
  have hx_add : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h := fun g hg h hh => (hxy g hg h hh).1
  have hlq_add := kum_add T hnL (qq_ne_zero T (L + n)) hlq
  have hlz0 : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), lz g = 0 := fun g hg =>
    kum_geo_zero T hlz (Subgroup.mem_inf.1 hg).2 (Subgroup.mem_inf.1 hg).1
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  let a : Gal p Ω → Ω := fun g => (p : Ω) ^ c₁ * ((η g).val : Ω) - W g
  have haLC : IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a := by
    refine ⟨fun g _ => IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) (isInt_natCast _)) (hWi g), fun g hg => ?_⟩
    obtain ⟨S1, hS1⟩ := hηlc g hg
    obtain ⟨S2, hS2⟩ := hWlc g
    refine ⟨S1 ∪ S2, fun h hh hS => ?_⟩
    have e1 := hS1 h hh (fun z hz => hS z (Finset.mem_union_left _ hz))
    have e2 := hS2 h (fun z hz => hS z (Finset.mem_union_right _ hz))
    simp only [a, e1]
    exact cong_sub (cong_refl _ _) e2
  have haCoc : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L),
      Cong (p := p) n (a (g * h)) (a g + g (a h)) := by
    intro g hg h hh
    have hgG := (Subgroup.mem_inf.1 hg).2
    have hhG := (Subgroup.mem_inf.1 hh).2
    obtain ⟨w, hw, ew⟩ := hW g hgG h hhG
    obtain ⟨u, hu, eu⟩ := zcong (p := p) (Ω := Ω) n (((x g).val : ℤ) * ((y h).val : ℤ))
      (((η h).val : ℤ) - ((η (g * h)).val : ℤ) + ((η g).val : ℤ)) (by
        simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
        exact hη g hg h hh)
    simp only [hlz0 g hg, ZMod.val_zero, Nat.cast_zero] at ew
    refine ⟨(p : Ω) ^ c₁ * u - w, IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) hu) hw, ?_⟩
    simp only [a, map_sub, map_mul, map_pow, map_natCast]
    push_cast at eu
    linear_combination (p : Ω) ^ c₁ * eu - ew
  obtain ⟨o, hoi, hofix, z, hzi, hz⟩ := (hc' Ω hclo T L n hnL lq hlqΔ).1 a haLC haCoc
  refine ⟨o, hoi, hofix, fun σ hσ => ?_⟩
  have hsi : ∀ v : Ω, σ⁻¹ (σ v) = v := fun v => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hfs : σ⁻¹ f = f := hff _ ((Gn T L).inv_mem hσ)
  refine ⟨σ⁻¹ (z - σ z - (p : Ω) ^ c' * W σ),
    isInt_gal _ (IsIntegral.sub (IsIntegral.sub hzi (isInt_gal σ hzi)) (IsIntegral.mul (isInt_pow_p c') (hWi σ))),
    fun h hh => ?_⟩
  have hhG := (Subgroup.mem_inf.1 hh).2
  have hh2 : σ * h * σ⁻¹ ∈ (Ggeo p Ω ⊓ Gn T L) := Subgroup.mem_inf.2
    ⟨conj_mem_ggeo (Subgroup.mem_inf.1 hh).1, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hhG) ((Gn T L).inv_mem hσ)⟩
  have hh2G := (Subgroup.mem_inf.1 hh2).2
  have hcomm : σ * h * σ⁻¹ * σ = σ * h := by group
  have hxh2 : x (σ * h * σ⁻¹) = x h := conj_invariant (Gn T L) x hx_add hσ hhG
  have hlqh2 : lq (σ * h * σ⁻¹) = lq h := conj_invariant (Gn T L) lq hlq_add hσ hhG
  have hlzh2 : lz (σ * h * σ⁻¹) = 0 := hlz0 _ hh2
  have hsh : σ (h z) = (σ * h * σ⁻¹) (σ z) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  have hs2 : ∀ v : Ω, σ⁻¹ ((σ * h * σ⁻¹) v) = h (σ⁻¹ v) := fun v => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  obtain ⟨w1, hw1, e1⟩ := hW _ hh2G σ hσ
  obtain ⟨w2, hw2, e2⟩ := hW σ hσ h hhG
  obtain ⟨w3, hw3, e3⟩ := hz h hh
  obtain ⟨w4, hw4, e4⟩ := hz _ hh2
  obtain ⟨u0, hu0, e0⟩ := zcong (p := p) (Ω := Ω) n
    (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : ℤ)
    (((η (σ * h * σ⁻¹)).val : ℤ) - ((η h).val : ℤ) - ((x h).val : ℤ) * ((y σ).val : ℤ) + ((x σ).val : ℤ) * ((y h).val : ℤ))
    (by simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val])
  push_cast at e0
  simp only [hxh2, hlzh2, hcomm, ZMod.val_zero, Nat.cast_zero] at e1
  simp only [a, hlqh2] at e3 e4
  have e3s := congrArg σ e3
  simp only [map_sub, map_mul, map_pow, map_natCast, hsh] at e3s
  have K : (p : Ω) ^ c₁ * (p : Ω) ^ c' * (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : Ω)
      - (o - σ o - (p : Ω) ^ c₁ * (p : Ω) ^ c' * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)
      - (((σ * h * σ⁻¹) z - (σ * h * σ⁻¹) (σ z) - (p : Ω) ^ c' * (σ * h * σ⁻¹) (W σ)) - (z - σ z - (p : Ω) ^ c' * W σ))
      = (p : Ω) ^ n * ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3) := by
    linear_combination (p : Ω) ^ c₁ * (p : Ω) ^ c' * e0 - (p : Ω) ^ c' * e1 + (p : Ω) ^ c' * e2 + e4 - e3s
  refine ⟨σ⁻¹ ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3), isInt_gal _ ?_, ?_⟩
  · exact IsIntegral.sub (IsIntegral.add (IsIntegral.add (IsIntegral.sub
      (IsIntegral.mul (IsIntegral.mul (isInt_pow_p c₁) (isInt_pow_p c')) hu0)
      (IsIntegral.mul (isInt_pow_p c') hw1)) (IsIntegral.mul (isInt_pow_p c') hw2)) hw4) (isInt_gal σ hw3)
  · have KS := congrArg (⇑(σ⁻¹ : Gal p Ω)) K
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add (f := _), hs2, hsi, hfs] at KS
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add (f := _), hsi, pow_add]
    linear_combination KS

end GlobalTheory.EdgeAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf
section
open Formalism.BasicNotions NumberField

namespace GlobalTheory

def eigIdxFiniteTypes (D : D7) (X : DivX D) : EigIdx D X where
  Pi := D.what₂.FT
  fin := D.what₂.instFT
  dec := D.what₂.instFTd
  cOf := id
  lam_const := by
    intro j _ π π' e _ _ h
    have h' : π = π' := h
    rw [h']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFramesNormAtEqNorm
section
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_frames_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (c : Module.Basis (Fin n) ℂ W) (L : Submodule (𝓞 K) (Fin n → K)), ∃ X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (X v).det) ∧ ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X (InfinitePlace.mk e) x = ‖∑ i, e (x i) • c i‖ := by
  intro K _ _ _ e W _ _ n c _
  have : FiniteDimensional ℂ W := Module.Finite.of_basis c
  have hn : Module.finrank ℂ W = n := by simpa using Module.finrank_eq_card_basis c
  let o : OrthonormalBasis (Fin n) ℂ W := (stdOrthonormalBasis ℂ W).reindex (finCongr hn)
  set A : Matrix (Fin n) (Fin n) ℂ := o.toBasis.toMatrix c with hA
  have hAu : IsUnit A.det :=
    Matrix.isUnit_det_of_right_inverse (o.toBasis.toMatrix_mul_toMatrix_flip c)
  have key : ∀ y : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm (A.mulVec y) = ‖∑ i, y i • c i‖ := by
    intro y
    rw [← o.repr.norm_map, EuclideanSpace.norm_eq]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    simp [hA, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
  rcases InfinitePlace.embedding_mk_eq e with h | h
  · refine ⟨fun _ => A⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det A hAu, fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv A hAu]
    congr 2
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, h]
  · have hBu : IsUnit (A.map (starRingEnd ℂ)).det := by
      have := hAu.map (starRingEnd ℂ)
      rwa [RingHom.map_det] at this
    refine ⟨fun _ => (A.map (starRingEnd ℂ))⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det _ hBu,
      fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv _ hBu]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← RCLike.norm_conj (A.mulVec (fun i => e (x i)) j)]
    congr 1
    simp [Formalism.HermitianLatticesTheory.vecAt, h, Matrix.mulVec, dotProduct]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
section
open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory

def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ) (hj : 1 ≤ j)
    (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  N := N
  j := j
  j_pos := hj
  j_lt := hjN
  lev := lev
  lev_prime := hlev
  Comp := Unit
  vol := 0
  chern := 0
  chern_homog := fun _ _ _ _ => rfl
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl
  CurveHT := fun _ => Empty
  degHT := fun _ _ _ => 0
  CurveDR := fun _ => Empty
  degDR := fun _ _ _ => 0
  FibComp := fun _ => Empty
  fibInBd := fun _ _ => False
  Pt := Unit
  phiDR := fun _ _ _ => 0
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 0
  XC := Unit
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_rfl
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_rfl⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  compOf := fun _ => ()
  normDetInf := fun _ _ => 1
  compPt := fun _ => ()
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  ALB := Unit
  arSelf := fun _ => 0
  arSelfC := fun _ _ => 0
  arSelf_sum := fun _ => by simp
  geo := fun _ => 0
  geoC := fun _ _ => 0
  geo_sum := fun _ => by simp
  arVol := fun _ => 0
  semipos := fun _ => True
  nefFib := fun _ => True
  arNef := fun _ => True
  Mbar := fun _ _ _ => ()

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCongStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cgA_coeff_of_isThB_succ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  first | (exact @GlobalTheory.ThBCompat.isThB_succ_coeff_cong) | (exact GlobalTheory.ThBCompat.isThB_succ_coeff_cong) | (intros; apply GlobalTheory.ThBCompat.isThB_succ_coeff_cong  <;> assumption)
end

