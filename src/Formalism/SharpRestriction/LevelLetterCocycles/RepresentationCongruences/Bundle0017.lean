module

public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SmulEqZeroOfAevalProd
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LeValOneAddPowSub
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.StepOneGG
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DfdPsZero
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DFD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem smul_sub_eq_smul_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Lk' Lk L0 Lκ0 Ls G X Ec Q U' P1 P2 FΛ S Φ Rr C1 C2 f₂ : R) (e1 e2 e3 n2v z : M)
    (hL0 : L0 = Lκ0 * Lk) (hG : G = P1 * P2 * FΛ) (hC1 : C1 = Lk' * Lk * FΛ * U' * P1)
    (hC2 : C2 = X * (P1 * P2 * Rr)) (hz : z = FΛ • e2)
    (h2 : Lk' • (Lk • e1 - Ls • e3) = Φ • e2) (h1 : n2v = S • e1)
    (h4 : P1 * (Lκ0 * f₂ - Ec * X) = Ec * Q * U') (h5 : P1 * S = P2)
    (h6 : Ec • e1 = e1) (h7 : Φ = Q * Rr) :
    (Lk' * G) • (L0 • (f₂ • e1) - Ls • (X • e3)) = Q • (C1 • n2v + C2 • z) := by
  subst hL0 hG hC1 hC2 hz h1 h7
  have h4v := congrArg (fun t : R => t • ((P2 * FΛ * Lk' * Lk) • e1)) h4
  have h5v := congrArg (fun t : R => t • ((FΛ * Lk' * Lk * Ec * Q * U') • e1)) h5
  linear_combination (norm := module) (P1 * P2 * FΛ * X) • h2 +
    (P1 * P2 * FΛ * Lk' * Lk * X + FΛ * Lk' * Lk * Q * U' * P1 * S) • h6 + h4v - h5v

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem dfd_ps_succ (k : ℕ) : ps W (k + 1) = W.φA (ps W k) := by
  unfold ps
  rw [pow_succ', AlgHom.mul_apply]

theorem dfd_ps_zero : ps W 0 = qA W := by
  unfold ps
  rw [pow_zero, AlgHom.one_apply]

theorem dfd_φLam_mem (A : ArcP n) (a : ZMod n) (e : ℕ) :
    W.φA (abelian₂ W A a e) ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} := by
  unfold abelian₂
  rw [map_prod]
  refine Submonoid.prod_mem _ fun s _ => ?_
  rw [map_pow, ← dfd_ps_succ]
  exact Submonoid.pow_mem _ (Submonoid.subset_closure
    (show ps W (s + 1) ∈ {x : LetA O n | ∃ k ≥ 1, x = ps W k} from ⟨s + 1, by omega, rfl⟩)) _

theorem dfd_φD_three (T : LocLat G Qp LL O) (x : W.DD T) :
    ((W.φD T) ^ 3) x = W.φD T (((W.φD T) ^ 2) x) := by
  rw [pow_succ']
  rfl

theorem dfd_φA_lA (k : ℕ) : W.φA (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem dfd_alg_lA (k : ℕ) : algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
  simp only [lA, lE, map_pow, map_natCast]

theorem dfd_closure_AΔ {x : LetA O n}
    (hx : x ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}) : x ∈ W.AΔ := by
  have key : Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} ≤ W.AΔ.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact TypesA.ps_mem W k
  exact key hx

end Local

end Formalism.MainNotions.N.FrobeniusPowerSeries.DFD

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftMapEqPrimePowSmul
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem existsLiftMapEqPrimePowSmul (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (i : ZMod n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ)

    (Ai ri : ℕ) (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))

    (bi S η : ℕ) (hU : Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ i ((Set.Icc (bi : ℤ) (bi + S)) ∪ Set.Icc (-(η : ℤ)) η))
    (hb : 2 * (Ai + ri) + η + 1 ≤ bi)

    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))

    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))

    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))

    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (hgN₂ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧ W.γ T₂ x - x = W.π₀ • y)

    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)

    (hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ (TruncatedCoefficientPoly cc bi S η (Ai + ri)) y))

    (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (lam : W.DD T₂)

    (hH1 : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (s • lam))
    (hH2 : ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ (Ai + ri)) • y) :
    ∃ x₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x₁ ∧
      W.map F x₁ = (((PD.p : ℕ) : LetA O n) ^ EG PD.p (Ai + ri) S η bi) • (s • lam) := by
  classical
  have : Fact (PD.p).Prime := ⟨PD.hp⟩
  have : IsDomain O := Function.Injective.isDomain (algebraMap O LL) hinj
  obtain ⟨hπ, -, -⟩ := lemG_units W hcase hP9 hc₁ hO hOv hinj

  have hdM : imgSub W F i ≤ (imgSub W F i).comap dop₂ := fun z hz =>
    dop_inImg W hπ F i dop₁ hd₁ dop₂ hd₂ hgN₁ hz
  have hpow : ∀ (k : ℕ) (z : W.DD T₂), (((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) ^ k)
      ((imgSub W F i).mkQ z) = (imgSub W F i).mkQ ((dop₂ ^ k) z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        show ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) ((imgSub W F i).mkQ z) =
          (imgSub W F i).mkQ (dop₂ z) from rfl, ih]
  have haev : ∀ (p : O[X]) (z : W.DD T₂),
      aeval ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) p ((imgSub W F i).mkQ z) =
        (imgSub W F i).mkQ (aeval dop₂ p z) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => intro z; rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add (f := _)]
    | monomial k c =>
      intro z
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, hpow,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

  suffices hmain : InImg W F i ((((PD.p : ℕ) : O) ^ EG PD.p (Ai + ri) S η bi) • (s • lam)) by
    obtain ⟨x₁, h1, h2⟩ := hmain
    refine ⟨x₁, h1, ?_⟩
    rw [h2, ← algebraMap_smul (LetA O n), map_pow, map_natCast]
  rcases Nat.eq_zero_or_pos (Ai + ri) with ha0 | ha
  · have h := q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr hH1
    rw [ha0, pow_zero, one_smul] at h
    exact inImg_smulO W F i _ h
  · have h₁ := step_i W hcase hP9 i F hc₁ hO hOv Ai ri hA hr bi (by omega) hgpi0 hA3 hA4 hl0 hinj hgN₁ hgN₂
      dop₁ hd₁ dop₂ hd₂ cc hcc s s' hs' hs lam hH1 hH2
    have h₂ := step_ii W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr dop₁ hd₁ dop₂ hd₂ (TruncatedCoefficientPoly cc bi S η (Ai + ri)) hCONS hH1
    have hu : v (algebraMap O LL ((W.χΓ W.gam : Oˣ) : O) - 1) = 1 := by
      rw [W.gam_gen, hcase.2.1, Nat.cast_one]
    have hcA := cc_assoc v PD.p hcase.2.2 W.v_l hO hOv hinj (W.χΓ W.gam) hu cc hcc
    have hS₂ : TruncationIndexSet bi S η (Ai + ri) ⊆
        Finset.Icc ((bi : ℤ) + 1) ((bi : ℤ) + S + (Ai + ri : ℕ)) ∪
          Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + (Ai + ri : ℕ)) := by
      intro y hy
      simp only [TruncationIndexSet, winU, Finset.mem_image, Finset.mem_product, Finset.mem_union, Finset.mem_Icc] at hy
      obtain ⟨⟨u, j⟩, ⟨hu | hu, hj⟩, rfl⟩ := hy
      · simp only [Finset.mem_union, Finset.mem_Icc]; left; push_cast; omega
      · simp only [Finset.mem_union, Finset.mem_Icc]; right; push_cast; omega
    have hE : ⌊(((3 * (Ai + ri) + S + 2 * η : ℕ) : ℝ) - 2) / ((PD.p : ℝ) - 1) +
        Real.logb PD.p ((bi : ℝ) + η - 1)⌋₊ ≤ EG PD.p (Ai + ri) S η bi := by
      unfold EG; push_cast; exact le_rfl
    have key := lemmaG_lagr PD.p ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) cc hl0 hcA
      (Ai + ri) S η bi (EG PD.p (Ai + ri) S η bi) ha hb (TruncationIndexSet bi S η (Ai + ri)) hS₂
      ((imgSub W F i).mkQ (s • lam))
      (by rw [haev]; exact (Submodule.Quotient.mk_eq_zero _).2 h₁)
      (by rw [haev]; exact (Submodule.Quotient.mk_eq_zero _).2 h₂) hE
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key
    exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPowSmulEqPiPowSmulOfTwistSub
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem sum_split {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (π : R) (f : ℕ → M)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ r ∈ Finset.range N, π ^ r • f r = π • ∑ r ∈ Finset.range (N - 1), π ^ r • f (r + 1) + f 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.smul_sum, pow_zero, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_succ, mul_comm, mul_smul]

section Gen
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem g_step (L π g h a : R) (k k₂ r m : ℕ) (E γE x x' z : M)
    (hkx : L ^ k • (g • E) = π ^ r • x)
    (hzE : L ^ k₂ • (g • (γE - E)) = (π ^ r * π * π ^ m) • z)
    (h1x : L ^ k • ((g * (1 + π * h)) • γE) - π ^ r • x = a • (π ^ r • x) + π ^ (r + 1) • x') :
    π ^ r • (L ^ k₂ • (a • x) - π • (L ^ k₂ • (h • x) + L ^ k • ((1 + π * h) • (π ^ m • z)) -
      L ^ k₂ • x')) = 0 := by
  linear_combination (norm := module) (-(L ^ k₂)) • h1x + (L ^ k * (1 + π * h)) • hzE +
    (L ^ k₂ * (1 + π * h)) • hkx

theorem g_fin (L π g ε a : R) (k k₂ r : ℕ) (E x y : M) (hkx : L ^ k • (g • E) = π ^ r • x)
    (h4 : L ^ k₂ • (a • x) = π • y) :
    (L ^ (k + k₂) * (ε * a)) • (g • E) = π ^ (r + 1) • (ε • y) := by
  linear_combination (norm := module) (L ^ k₂ * ε * a) • hkx + (π ^ r * ε) • h4

theorem g_A (L π q P2 p1 aJ t : R) (κ' b1 κ κ₁ E σ e : ℕ) (FX FX' FD Fn Fz lam φHh y4 : M)
    (E1 : FX = π • FX' + L ^ κ₁ • FD) (E2 : Fn = FD + π • Fz)
    (E3 : q ^ b1 • Fn = L ^ E • (p1 ^ e • lam))
    (E4 : L ^ κ' • (L ^ κ • lam - L ^ σ • φHh) = (π * aJ) • y4)
    (ht : L ^ b1 * p1 ^ e - L ^ e * q ^ b1 = π * t) :
    L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz) +
        (L ^ (κ₁ + E + κ' + σ) * t) • (P2 • φHh)) := by
  have key : L ^ κ' • ((q ^ b1 * P2) • (L ^ (b1 + κ) • FX - L ^ (κ₁ + E + σ + e) • φHh)) =
      π • ((L ^ (κ₁ + E) * L ^ b1 * p1 ^ e * aJ) • (P2 • y4) +
        (L ^ (κ' + b1 + κ) * (q ^ b1 * P2)) • (FX' - L ^ κ₁ • Fz)) +
      (L ^ (κ₁ + E + κ' + σ) * (L ^ b1 * p1 ^ e - L ^ e * q ^ b1)) • (P2 • φHh) := by
    linear_combination (norm := module) (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ)) • E1 -
    (L ^ κ' * (q ^ b1 * P2) * L ^ (b1 + κ + κ₁)) • E2 + (L ^ κ' * P2 * L ^ (b1 + κ + κ₁)) • E3 +
    (P2 * L ^ (b1 + κ₁ + E) * p1 ^ e) • E4
  rw [key, ht]
  module

theorem g_B (L π q P2 u3 Pk : R) (b1 κ c Rr R' M' : ℕ) (FX γFX Fx φHh γφHh φxH : M)
    (B1 : γFX - FX = (π ^ Rr * π ^ R') • Fx)
    (B2 : γφHh - φHh = (u3 * (π ^ Rr * π ^ M') * Pk) • φxH) :
    (q ^ b1 * P2) • (L ^ (b1 + κ) • γFX - L ^ c • γφHh - (L ^ (b1 + κ) • FX - L ^ c • φHh)) =
      π ^ Rr • ((L ^ (b1 + κ) * π ^ R' * (q ^ b1 * P2)) • Fx -
        (L ^ c * u3 * π ^ M' * Pk * q ^ b1) • (P2 • φxH)) := by
  linear_combination (norm := module) (q ^ b1 * P2 * L ^ (b1 + κ)) • B1 - (q ^ b1 * P2 * L ^ c) • B2

theorem g_K (L g π qB : R) (kU κ₁ b1 κ σ₁ E σ e₁ e₂ : ℕ) (Fy FZ φFX φφHh φV : M)
    (hrelF : L ^ κ₁ • Fy + (π * qB) • FZ = L ^ σ₁ • φFX)
    (hφV : φV = L ^ (b1 + κ) • φFX - L ^ (κ₁ + E + σ + (e₁ + e₂)) • φφHh) :
    L ^ (kU + κ₁) • g • (L ^ (b1 + κ) • Fy - L ^ (σ₁ + E + σ + e₁ + e₂) • φφHh) =
      L ^ σ₁ • (L ^ kU • (g • φV)) - (L ^ (kU + b1 + κ) * g * π) • (qB • FZ) := by
  rw [hφV]
  linear_combination (norm := module) (L ^ (kU + b1 + κ) * g) • hrelF

end Gen

variable (W : LocWach PD LL O v n)

theorem γ_mul_form {g g' h h' : LetA O n} (hg : W.γA W.gam g = g * (1 + W.π₀ * h))
    (hg' : W.γA W.gam g' = g' * (1 + W.π₀ * h')) :
    W.γA W.gam (g * g') = g * g' * (1 + W.π₀ * (h + h' + W.π₀ * h * h')) := by
  rw [map_mul, hg, hg']; ring

theorem γ_pow_form {g h : LetA O n} (hh : h ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hg : W.γA W.gam g = g * (1 + W.π₀ * h)) (k : ℕ) :
    ∃ h' ∈ W.AΔ, W.γA W.gam (g ^ k) = g ^ k * (1 + W.π₀ * h') := by
  induction k with
  | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨h', hh', e⟩ := ih
    refine ⟨h' + h + W.π₀ * h' * h, ?_, ?_⟩
    · exact W.AΔ.add_mem (W.AΔ.add_mem hh' hh) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hh') hh)
    · rw [pow_succ, γ_mul_form W e hg]

theorem exists_pow_smul_eq_pi_pow_smul_of_twist_sub (T : LocLat G Qp LL O) (hC : Formalism.MainNotions.UnusedSlot80.Relay2.Ctx W T) (c : ZMod n)
    (g₀ h : LetA O n) (hh : h ∈ W.AΔ)
    (hγg : W.γA W.gam g₀ = g₀ * (1 + W.π₀ * h)) (R : ℕ) (E : W.DD T)
    (hE : ∃ (k : ℕ) (E' : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c E' ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ • E')
    (hγ : ∃ (k : ℕ) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c z ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • (W.γ T E - E)) = W.π₀ ^ R • z) :
    ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ R • x := by
  obtain ⟨k₂, z, hz, hzE⟩ := hγ
  have hπ : W.π₀ ∈ W.AΔ := hC.hπ
  have key : ∀ r, 1 ≤ r → r ≤ R → ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (g₀ • E) = W.π₀ ^ r • x := by
    intro r hr1
    induction r with
    | zero => omega
    | succ r ih =>
      intro hrR
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        obtain ⟨k, E', hE', hk⟩ := hE
        exact ⟨k, E', hE', by rw [hk, zero_add, pow_one]⟩
      obtain ⟨k, x, hx, hkx⟩ := ih hpos (by omega)
      obtain ⟨x', hx', h1x⟩ := hC.H1 c r x hx
      obtain ⟨e, he⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.principal_unit_pow_sub_one_dvd W hC.inj hC.O2 r (hC.H2 r hpos)
      set a : LetA O n := algebraMap O (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) with ha
      rw [← algebraMap_smul (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1), ← ha] at h1x
      have hγx : W.γ T (W.π₀ ^ r • x) =
          Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((g₀ * (1 + W.π₀ * h)) • W.γ T E) := by
        rw [← hkx, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, ← hγg]
        congr 1
        exact Formalism.MainNotions.LiftingTheory.frame_γD_smul W T W.gam g₀ E
      rw [hγx] at h1x
      have hR : W.π₀ ^ R = W.π₀ ^ r * W.π₀ * W.π₀ ^ (R - (r + 1)) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hR] at hzE
      obtain ⟨y, hy⟩ : ∃ y : W.DD T, y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (h • x) +
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((1 + W.π₀ * h) • (W.π₀ ^ (R - (r + 1)) • z)) -
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • x' := ⟨_, rfl⟩
      have h3 : W.π₀ ^ r • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k₂ • (a • x) - W.π₀ • y) = 0 := by
        rw [hy]; exact g_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hkx hzE h1x
      have h4 := Formalism.MainNotions.LiftingTheory.frame_π₀_inj W T hC.hw r _ h3
      rw [sub_eq_zero] at h4
      have h1h : (1 + W.π₀ * h) ∈ W.AΔ := W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hπ hh)
      have hyN : Formalism.MainNotions.LiftingTheory.InNΔi W T c y := by
        rw [hy]
        refine Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W T c (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W T c ?_ ?_)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ hx')
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hh hx)
        · exact Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W T c _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c h1h
            (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ _) hz))
      obtain ⟨ε, hε⟩ : ∃ ε : LetA O n, ε = algebraMap O (LetA O n) e := ⟨_, rfl⟩
      have he' : ε * a = Formalism.MainNotions.ArcLiftingSetup.lA W ^ (1 + padicValNat PD.p r) := by
        rw [hε, ha, ← map_mul, he, map_pow, map_natCast]; rfl
      refine ⟨k + k₂ + (1 + padicValNat PD.p r), ε • y,
        Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (by rw [hε]; exact W.AΔ.algebraMap_mem e) hyN, ?_⟩
      rw [pow_add, ← he']
      exact g_fin _ _ _ _ _ _ _ _ _ _ _ hkx h4
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    obtain ⟨k, E', hE', hk⟩ := hE
    exact ⟨k, W.π₀ • E', Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c hπ hE', by rw [hk, pow_zero, one_smul]⟩
  · exact key R hpos le_rfl

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYCA
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FilVSep
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup
open scoped TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem filV_sep {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hco : ∀ (a : ℤ) (w : V ⊗[Qp] BdR), w ∈ FilV PD (LL := LL) (V := V) a →
      ∀ j, E w j ∈ PD.Fil a := by
    intro a w hw
    obtain ⟨y, rfl⟩ := hw
    induction y using TensorProduct.induction_on with
    | zero => intro j; simp
    | tmul x f =>
      intro j
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        Submodule.coe_subtype, E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul,
        Finsupp.mapRange_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ f.2
    | add x y hx hy =>
      intro j
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact (PD.Fil a).add_mem (hx j) (hy j)
  have h0 : E z = 0 := by
    ext j
    exact PD.Fil_sep _ fun a => hco a z (hz a) j
  simpa using congrArg E.symm h0

theorem filS_top (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (A : ArcP n)
    (T : LocLat G Qp LL O) (hW : Win W A T) (a : ZMod n) (s : ℕ) (u : ℤ)
    (hu : ∀ x ∈ (A.ty (a - (s : ZMod n))).win A.G₀ A.S A.η, x < u) :
    FilS W T a s u = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨hxF, hxL⟩ := Submodule.mem_inf.mp hx
  suffices hx0 : x = 0 by simp [hx0]
  set i : ZMod n := a - (s : ZMod n) with hi
  obtain ⟨hbij, -, -⟩ := hcase
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
  have hez : ∀ z : K₀, e z = algebraMap K₀ K z := fun z => rfl
  have hover : ∀ z : K₀, τ (algebraMap K₀ K z) = W.emb i z := by
    intro z
    have : e.symm (algebraMap K₀ K z) = z := by
      rw [← hez, AlgEquiv.symm_apply_apply]
    show W.emb i (e.symm (algebraMap K₀ K z)) = W.emb i z
    rw [this]
  have hOver : Formalism.MainNotions.LiftingTheory.Over W τ i := by
    ext z
    exact hover z
  have hJ := hW.2 i τ hOver
  have hE : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T i τ hover hbij.2 ⟨x, hxL, rfl⟩
  have hV : ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) u :=
    (Submodule.mem_inf.mp hxF).2
  have hall : ∀ k : ℕ, ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ (u + k) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, add_zero]
      exact Submodule.mem_inf.mpr ⟨hE, hV⟩
    | succ k ih =>
      have heq : FildR PD T.ρ τ (u + k + 1) = FildR PD T.ρ τ (u + k) := by
        by_contra h
        have := hu _ (hJ (u + k) h)
        omega
      rw [Nat.cast_succ, ← add_assoc, heq]
      exact ih
  have hallV : ∀ b : ℤ, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) b := by
    intro b
    by_cases h : b ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti h hV
    · have hk := (Submodule.mem_inf.mp (hall (b - u).toNat)).2
      have : u + ((b - u).toNat : ℤ) = b := by omega
      rwa [this] at hk
  have h0 := filV_sep _ hallV
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (h0.trans (map_zero _).symm)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

