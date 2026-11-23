module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0023
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0022

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeHypFirst
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_hyp_first (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl5 : 5 ≤ PD.p)
    (hArc : ArcCore W) (hFL : ArcFilLowCore W) (A : ArcP n) (hOK : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (hlen : A.len c = 3) (hj : A.j = 1) {b₁ w' : ℕ} (hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up b₁)
    (hty2 : A.ty (c - 2) = Formalism.MainNotions.LocalTheoryWindows.LT.down w')
    {T₂ : LocLat G Qp LL O} (hW₂ : Win W A T₂) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hFil : dv W T₂ (A.len c) bb (Pi.single k₀ 1) ∈ FilS W T₂ c 1 b₁)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 1 lam) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol (A.M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2
      (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ (A.σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) := by
  classical
  have hj2 : A.j ≤ 2 := by rw [hj]; norm_num
  have h2l : 2 ≤ A.len c := by rw [hlen]; norm_num
  obtain ⟨⟨u, hu, hJJ⟩, hT⟩ := hArc hcase hl5 A hOK c hc 2 hj2 h2l
  obtain ⟨-, -, -, hfr⟩ := hT T₂ hW₂
  obtain ⟨-, -, hc3, -, -, -, hcrit⟩ := hfr d bb sol hbb
  have hFL' := hFL hcase hl5 A hOK c hc 2 hj2 h2l T₂ hW₂ d bb sol hbb (Pi.single k₀ 1) 1 (by norm_num)
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a : ZMod n := c' + ((2 : ℕ) : ZMod n) with ha_def
  have ha : a = c - 1 := by rw [ha_def, hc', hlen]; push_cast; ring
  set Λ : LetA O n := abelian₂ W A a 2 with hΛdef
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hHs0 : A.Hs a 2 0 = A.h := by
    unfold ArcP.Hs
    rw [if_neg]
    push Not
    refine ⟨?_, by rw [hj]; norm_num⟩
    rw [Nat.cast_zero, sub_zero, ha, hty1]
    intro h; cases h
  have hHs1 : A.Hs a 2 1 = A.G₀ := by
    unfold ArcP.Hs
    rw [if_pos (Or.inr (by rw [hj]))]
  have hΛ : Λ = qA W ^ A.h * ps W 1 ^ A.G₀ := by
    rw [hΛdef, abelian₂, Finset.prod_range_succ, Finset.prod_range_one, hHs0, hHs1, hps0]
  have hb1h : b₁ + A.S ≤ A.h := by
    have := hOK.2.2.2.2.2.2.2.1 (c - 1) (by rw [hty1]; rfl)
    rwa [hty1] at this
  have hw'η : A.η < w' := by
    have := hOK.2.2.2.2.1 (c - 2)
    rwa [hty2] at this
  have hqmem : qA W ∈ W.AΔ := by rw [← hps0]; exact TypesA.ps_mem W 0
  set R : LetA O n := qA W ^ (A.h - b₁) * ps W 1 ^ (A.G₀ + (w' + A.S)) with hRdef
  have hRmem : R ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)
  have hΛs : (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) R := by
    have hq : qA W ^ A.h = qA W ^ (A.h - b₁) * qA W ^ b₁ := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    calc (algebraMap (LetA O n) W.EE) Λ * s = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s) := by
          rw [hΛ, hq]; simp only [map_mul]; ring
      _ = (algebraMap (LetA O n) W.EE) (qA W ^ (A.h - b₁) * ps W 1 ^ A.G₀) * (algebraMap (LetA O n) W.EE) (ps W 1 ^ (w' + A.S)) := by rw [hs]
      _ = (algebraMap (LetA O n) W.EE) R := by rw [hRdef]; simp only [pow_add, map_mul]; ring
  have hΛx : Λ • (s • lam) = R • lam := by
    rw [← algebraMap_smul W.EE Λ (s • lam), smul_smul, hΛs, algebraMap_smul]
  have hInFP : InFP W T₂ c' 2 1 (Λ • (s • lam)) := by
    rw [hΛx]
    obtain ⟨y, hy, rfl⟩ := hlam
    exact ⟨R • y, TypesA.Pp_smul W hRmem hy, by rw [one_smul, one_smul]⟩
  have hΛmem : Λ ∈ W.AΔ := TypesA.Ps_mem W (TC.lam_mem_Ps W A a 2)
  have hletmem : (letE a : LetA O n) ∈ W.AΔ := TypesD.letE_mem W a

  obtain ⟨-, -, κ₁, κ₁', Hh1, a1, hHh1, -, -⟩ := hc3 (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) else 0) (by
    intro k
    by_cases hk : k = k₀
    · simp only [if_pos hk]
      exact ⟨Λ, hΛmem, by rw [← map_mul]; congr 1; ring⟩
    · simp only [if_neg hk]
      exact ⟨0, W.AΔ.zero_mem, by simp⟩)
  set σ := A.σ PD.p with hσdef
  obtain ⟨κ', y, hy, hyeq⟩ := h4a
  rw [hj] at hJJ
  have hJJ' : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) = W.π₀ * Λ ^ 2 * u := by
    rw [← hJJ]; simp
  have hlet2 : (letE a : LetA O n) • ((W.φD T₂) ^ 2) Hh = ((W.φD T₂) ^ 2) Hh :=
    TypesD.φDpow_letter W (TypesD.horTr_letter W hbb hHh) 2
  have hφl : ((W.φD T₂) ^ 2) (lA W ^ κ₁ • Hh) = lA W ^ κ₁ • ((W.φD T₂) ^ 2) Hh := by
    rw [← TypesA.pO_smul, map_smul, TypesA.pO_smul]
  have hRep : RepVV W T₂ c' 2 (A.M PD.p) Λ bb sol (lA W ^ 0 • (s • lam))
      (fun k => if k = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    refine ⟨κ + κ₁, κ', fun k => if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k,
      fun k => if k = k₀ then letE a * R * lA W ^ σ else 0, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = k₀
      · subst hk; simp only [if_pos rfl]; exact TypesA.IsHorTr_smul W κ₁ hHh
      · simp only [if_neg hk]; rw [add_comm]; exact TypesA.IsHorTr_smul W κ (hHh1 k)
    · intro k
      by_cases hk : k = k₀
      · simp only [if_pos hk]
        refine ⟨W.AΔ.mul_mem (W.AΔ.mul_mem hletmem hRmem) (TypesA.lA_pow_mem W σ), ?_⟩
        rw [TC.lE_eq W σ]
        rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
        simp only [map_mul]; ring
      · simp only [if_neg hk]; exact ⟨W.AΔ.zero_mem, by simp⟩
    · have hsum : ∑ k, (if k = k₀ then letE a * R * lA W ^ σ else 0) •
          ((W.φD T₂) ^ 2) (if k = k₀ then lA W ^ κ₁ • Hh else lA W ^ κ • Hh1 k) =
          (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh := by
        rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp only [if_neg hk, zero_smul]) (by simp)]
        rw [if_pos rfl, if_pos rfl]
        rw [hφl, smul_smul, show letE a * R * lA W ^ σ * lA W ^ κ₁ = (R * lA W ^ σ * lA W ^ κ₁) * letE a by ring,
          mul_smul, hlet2]
      rw [hsum, pow_zero, one_smul, hΛx]
      refine ⟨(u * (R * lA W ^ κ₁)) • y, TypesA.Pp_smul W (W.AΔ.mul_mem hu (W.AΔ.mul_mem hRmem
        (TypesA.lA_pow_mem W κ₁))) hy, ?_⟩
      have e1 : lA W ^ κ' • (lA W ^ (κ + κ₁) • R • lam - (R * lA W ^ σ * lA W ^ κ₁) • ((W.φD T₂) ^ 2) Hh) =
          (R * lA W ^ κ₁) • (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ σ • ((W.φD T₂) ^ 2) Hh)) := by
        simp only [smul_sub, smul_smul]
        congr 2 <;> ring
      rw [e1, hyeq, hJJ', smul_smul, smul_smul]
      congr 1
      ring
  have hfr : ∀ m, InFr W a 1 Λ (if m = k₀ then (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s else 0) := by
    intro m
    by_cases hm : m = k₀
    · simp only [if_pos hm]
      refine ⟨R * lA W ^ σ, W.AΔ.mul_mem hRmem (TypesA.lA_pow_mem W σ), ?_⟩
      rw [TC.lE_eq W σ]
      rw [show (algebraMap (LetA O n) W.EE) Λ * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) Λ * s) by ring, hΛs]
      simp only [map_mul, map_one]; ring
    · simp only [if_neg hm]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
  have hN : InFNc W T₂ a 1 (s • lam) := by
    refine (hcrit (s • lam) 0 _ hInFP hRep hfr).2 ⟨0, 1, fun _ => (algebraMap (LetA O n) W.EE) (letE a) * lE W σ * s,
      fun _ => Pi.single k₀ 1, fun _ t => if t = 0 then -(b₁ : ℤ) else ((w' + A.S : ℕ) : ℤ),
      fun _ => ⟨?_, ?_⟩, fun k => ?_⟩
    · refine ⟨lA W ^ σ, TypesA.lA_pow_mem W σ, ?_⟩
      have e1 : (-(b₁ : ℤ)).toNat = 0 := by omega
      have e2 : (-(-(b₁ : ℤ))).toNat = b₁ := by omega
      have e3 : (((w' + A.S : ℕ) : ℤ)).toNat = w' + A.S := by omega
      have e4 : (-(((w' + A.S : ℕ) : ℤ))).toNat = 0 := by omega
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_ne_zero, ↓reduceIte,
        e1, e2, e3, e4, pow_zero, one_mul, mul_one, hps0]
      rw [TC.lE_eq W σ]
      simp only [map_mul]
      rw [show (algebraMap (LetA O n) W.EE) (qA W ^ b₁) * ((algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * s) = (algebraMap (LetA O n) W.EE) (letE a) * (algebraMap (LetA O n) W.EE) (lA W ^ σ) * ((algebraMap (LetA O n) W.EE) (qA W ^ b₁) * s)
        by ring, hs]
      ring
    · intro t ht
      interval_cases t
      · simp only [↓reduceIte, neg_neg]
        rw [hlen, show (3 : ℕ) = 2 + 1 from rfl, ArcLengthTwo.dv_succ] at hFil
        rw [ArcLengthTwo.dvO_single]
        exact ArcLengthTwo.filS_φ_inv W T₂ (by rw [ha]; push_cast; ring) hFil
      · simp only [one_ne_zero, ↓reduceIte]
        refine hFL'.1 _ fun x hx => ?_
        have e : a - ((1 : ℕ) : ZMod n) = c - 2 := by rw [ha]; push_cast; ring
        rw [e, hty2] at hx
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
        push_cast
        omega
    · simp only [Fin.sum_univ_one, lE, pow_zero, one_mul]
      by_cases hk : k = k₀
      · subst hk; simp
      · simp [if_neg hk, Pi.single_apply, hk]
  obtain ⟨y, hyΔ, hyl, hxy⟩ := hN
  rw [← ha, hxy, one_smul]
  exact ⟨hyΔ, ⟨y, hyΔ.1, by simpa using hyl⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeHypSecond
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_hyp_second (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (A : ArcP n) (c : ZMod n) (hlen : A.len c = 3) {T₂ : LocLat G Qp LL O}
    (hT₂ : IsCrys PD T₂.ρ) (Mi' hi' : ZMod n → ℕ) (hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mi' hi') {b₁ w' A₀ : ℕ}
    (hM1 : Mi' (c - 2) = w' + A.S) (hM2 : Mi' (c - 1) = A.η)
    (hN : b₁ + A₀ + A.η ≤ (PD.p - 1) * A.M PD.p) (hM : 1 ≤ A.M PD.p) (lam : W.DD T₂)
    (hlamγ : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (W.γ T₂ lam - lam))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ A₀) • y := by
  classical
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  have e1 : c - 2 - 1 = c' := by rw [hc', hlen]; push_cast; ring
  have e2 : c - 1 - 1 = c - 2 := by ring
  have e3 : c' + ((2 : ℕ) : ZMod n) = c - 1 := by rw [hc', hlen]; push_cast; ring
  have e4 : c' + ((1 : ℕ) : ZMod n) = c - 2 := by rw [hc', hlen]; push_cast; ring

  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1).finrank_eq, Module.finrank_self]
  have h9 := hP9 T₂ hT₂ hcase.2.1 hcase.2.2
  have hring := (h9.2.2 hK).1
  obtain ⟨wq, hwq⟩ := hring.2.2.2.2.1
  have hq : W.q = (wq : LetA O n) * qA W := by
    rw [hwq]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hQ : W.Q = (wq : LetA O n) * qA W := by
    unfold LocWach.Q
    rw [hcase.2.1]
    simp [hq]
  have h5 := hP5 T₂ Mi' hi' hT₂ hJL
  have hφs : ∀ (a : LetA O n) (y : W.DD T₂), W.φD T₂ (a • y) = W.φA a • W.φD T₂ y := by
    intro a y
    rw [← algebraMap_smul W.EE a y, W.φD_smul, ← algebraMap_smul W.EE (W.φA a)]
    congr 1
    exact W.φE_ext a
  have hps1 : ps W 1 = W.φA (qA W) := by simp [ps]
  have hqmem : qA W ∈ W.AΔ := GS.qA_mem W
  have hp1mem : ps W 1 ∈ W.AΔ := GS.ps_mem W 1

  have hgen : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' x →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) := by
    intro x hx
    obtain ⟨hxΔ, hxl⟩ := hx
    have hxlet := TypesD.nl_letter W hxl
    have h1 := h5.1 (c - 2) x (by rw [e1]; exact hxl)
    rw [hM1] at h1
    have hl1 : (letE (c - 2) : LetA O n) • (W.Q ^ (w' + A.S) • W.φD T₂ x) = W.Q ^ (w' + A.S) • W.φD T₂ x := by
      rw [smul_comm]
      congr 1
      have := TypesD.φD_letter W hxlet
      rwa [show c' + 1 = c - 2 by rw [← e4]; push_cast; ring] at this
    have hletφ : (letE (c - 2) : LetA O n) • W.φD T₂ x = W.φD T₂ x := by
      have := TypesD.φD_letter W hxlet
      rwa [show c' + 1 = c - 2 by rw [← e4]; push_cast; ring] at this
    have hz1 : W.Q ^ (w' + A.S) • W.φD T₂ x ∈ W.Nl T₂ (c - 2) := ⟨_, h1, by simp [hletφ]⟩
    have h2 := h5.1 (c - 1) _ (by rw [e2]; exact hz1)
    rw [hM2, hφs] at h2
    set u : (LetA O n)ˣ := wq ^ A.η * (Units.map (W.φA : LetA O n →* LetA O n) wq) ^ (w' + A.S) with hu
    have hE : ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) =
        ((u⁻¹ : (LetA O n)ˣ) : LetA O n) • (W.Q ^ A.η • (W.φA (W.Q ^ (w' + A.S)) • W.φD T₂ (W.φD T₂ x))) := by
      rw [smul_smul, smul_smul, pow_two, Module.End.mul_apply]
      congr 1
      rw [hQ, map_pow, map_mul, hps1, hu]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, mul_pow]
      have h1' : ((u⁻¹ : (LetA O n)ˣ) : LetA O n) * (u : LetA O n) = 1 := Units.inv_mul u
      rw [hu] at h1'
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at h1'
      linear_combination (-(qA W ^ A.η * W.φA (qA W) ^ (w' + A.S))) * h1'
    have hEN : (qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x ∈ W.N T₂ := by
      rw [hE]; exact (W.N T₂).smul_mem _ h2
    have hlet2 := TypesD.φDpow_letter W hxlet 2
    rw [e3] at hlet2
    have hEl : (letE (c - 1) : LetA O n) • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) =
        (qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x := by
      rw [smul_comm, hlet2]
    have hamem : qA W ^ A.η * ps W 1 ^ (w' + A.S) ∈ W.AΔ :=
      W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem hp1mem _)
    have hΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ (((W.φD T₂) ^ 2) x) = ((W.φD T₂) ^ 2) x := by
      intro δ hδ
      rw [pow_two, Module.End.mul_apply, ← W.φγ_comm, ← W.φγ_comm, hxΔ.2 δ hδ]
    refine ⟨⟨hEN, fun δ hδ => ?_⟩, ⟨_, hEN, by simp [hlet2]⟩⟩
    rw [ArcLengthTwo.γD_smulA W T₂ δ, hΔ δ hδ]
    have ha' : W.γA δ (qA W ^ A.η * ps W 1 ^ (w' + A.S)) = qA W ^ A.η * ps W 1 ^ (w' + A.S) := hamem δ hδ
    rw [ha']

  obtain ⟨z₀, hz₀, hz₀eq⟩ := hlamγ
  have hPall : ∀ z ∈ Pp W T₂ c' 2,
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z) := by
    intro z hz
    unfold Pp at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hz
      rw [smul_comm]
      exact inNΔi_smulA W T₂ (c - 1) hα (hgen x hx)
    | zero => rw [smul_zero]; exact ⟨(W.NΔ T₂).zero_mem, (W.Nl T₂ (c - 1)).zero_mem⟩
    | add z z' _ _ h h' => rw [smul_add]; exact inNΔi_add W T₂ (c - 1) h h'
    | neg z _ h => rw [smul_neg]; exact ⟨(W.NΔ T₂).neg_mem h.1, (W.Nl T₂ (c - 1)).neg_mem h.2⟩
  have hPz := hPall z₀ hz₀

  obtain ⟨r₀, -, r₀', hr₀', hrr₀, hγ₀⟩ := GS.psγ hR 0
  obtain ⟨r₁, hr₁, -, -, -, hγ₁⟩ := GS.psγ hR 1
  have hps0 : ps W 0 = qA W := by simp [ps]
  rw [hps0] at hγ₀
  have hγs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * W.γE W.gam s =
      algebraMap (LetA O n) W.EE (r₀' ^ b₁ * (r₁ * ps W 1) ^ (w' + A.S)) := by
    have h := congrArg (W.γE W.gam) hs
    rw [map_mul, GS.γE_ι, GS.γE_ι, map_pow (W.γA W.gam), map_pow (W.γA W.gam), hγ₀, hγ₁] at h
    have hq' : qA W ^ b₁ = r₀' ^ b₁ * (r₀ * qA W) ^ b₁ := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, mul_comm r₀' r₀, hrr₀, one_pow, one_mul]
    rw [hq', map_mul, mul_assoc, h, ← map_mul]

  obtain ⟨w₁, hw₁⟩ := hR.2.1
  have hJJ : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) =
      (w₁ : LetA O n) ^ A.M PD.p * W.π₀ ^ A.M PD.p * qA W ^ ((PD.p - 1) * A.M PD.p) * ps W 1 ^ (2 * A.G₀) := by
    have hpk : Formalism.MainNotions.LiftingTheory.pk W 0 = qA W := by simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, qA, lA]
    simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, hpk, map_mul, map_pow, hw₁, hps1]
    rw [pow_mul]
    try ring
  have hw₁mem : (w₁ : LetA O n) ∈ W.AΔ := by
    refine GS.quot_mem W (W.AΔ.mul_mem (GS.π₀_mem W) (W.AΔ.pow_mem hqmem _))
      (by rw [map_mul, map_pow]; exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow (PD.p - 1))) ?_
    have : W.π₀ * qA W ^ (PD.p - 1) * (w₁ : LetA O n) = W.φA W.π₀ := by rw [hw₁]; ring
    rw [this]
    exact GS.φpow_mem W 1 (GS.π₀_mem W)
  set N := (PD.p - 1) * A.M PD.p with hNdef
  set M := A.M PD.p with hMdef
  set V : LetA O n := (w₁ : LetA O n) ^ M * r₀' ^ b₁ * r₁ ^ (w' + A.S) with hV
  have hVmem : V ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hw₁mem _)
    (W.AΔ.pow_mem (GS.mem_invariants_of_mem_S1 W hr₀') _)) (W.AΔ.pow_mem (GS.mem_invariants_of_mem_S1 W hr₁) _)
  set C : LetA O n := W.π₀ ^ (M - 1) * qA W ^ (N - b₁ - A₀ - A.η) * ps W 1 ^ (2 * A.G₀) * V with hC
  have hCmem : C ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (GS.π₀_mem W) _)
    (W.AΔ.pow_mem hqmem _)) (W.AΔ.pow_mem hp1mem _)) hVmem
  refine ⟨C • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z₀), inNΔi_smulA W T₂ (c - 1) hCmem hPz, ?_⟩
  have hL : W.γE W.gam s • (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M) • z₀) =
      (W.γE W.gam s * algebraMap (LetA O n) W.EE (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M))) • z₀ := by
    rw [← algebraMap_smul W.EE (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M)) z₀, smul_smul]
  have hRt : (W.π₀ * qA W ^ A₀) • (C • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z₀)) =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ A₀ * (C * (qA W ^ A.η * ps W 1 ^ (w' + A.S)))) • z₀ := by
    rw [smul_smul, smul_smul, algebraMap_smul, mul_assoc]
  rw [hz₀eq, hL, hRt, hJJ]
  congr 1
  have hπ : W.π₀ ^ M = W.π₀ * W.π₀ ^ (M - 1) := by
    rw [← pow_succ']; (try congr 1); (try omega)
  have hqN : qA W ^ N = qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η * qA W ^ b₁ := by
    rw [← pow_add, ← pow_add, ← pow_add]; (try congr 1); (try omega)
  rw [hπ, hqN]
  have : W.γE W.gam s * algebraMap (LetA O n) W.EE ((w₁ : LetA O n) ^ M * (W.π₀ * W.π₀ ^ (M - 1)) *
      (qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η * qA W ^ b₁) * ps W 1 ^ (2 * A.G₀)) =
      algebraMap (LetA O n) W.EE ((w₁ : LetA O n) ^ M * (W.π₀ * W.π₀ ^ (M - 1)) *
      (qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η) * ps W 1 ^ (2 * A.G₀)) *
      (algebraMap (LetA O n) W.EE (qA W ^ b₁) * W.γE W.gam s) := by
    simp only [map_mul]; ring
  rw [this, hγs, ← map_mul]
  congr 1
  rw [hC, hV]
  ring

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SectionInIdealOfLevels
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem section_in_ideal_of_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) (he : 1 ≤ e) {d : ℕ} (b : Fin d → W.DD T)
    (h : Fin d → W.EE)
    (hlev : ∀ s < e, ∃ κ : ℕ, SecIn W a e
      (fun α c₀ => dvO W T e b c₀ ∈ FilS W T a s (-(α s))) (fun k => lE W κ * h k))
    (hlow : ∀ t < e, ∃ U : ℤ, ∀ u ≤ U, ∀ c₀ : Fin d → O, dvO W T e b c₀ ∈ FilS W T a t u) :
    ∃ κ : ℕ, SecIn W a e (condNN W T a e b) (fun k => lE W κ * h k) := by
  have hlev' : ∀ s : ℕ, ∃ κ : ℕ, ∃ I : ℕ, ∃ g : Fin I → W.EE, ∃ c₀ : Fin I → Fin d → O,
      ∃ α : Fin I → ℕ → ℤ, s < e →
        (∀ i, InId W a e (α i) (g i) ∧ dvO W T e b (c₀ i) ∈ FilS W T a s (-(α i s))) ∧
        ∀ k, lE W κ * h k = ∑ i, g i * algebraMap O W.EE (c₀ i k) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨κ, I, g, c₀, α, h1, h2⟩ := hlev s hs
      exact ⟨κ, I, g, c₀, α, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun h' => absurd h' hs⟩
  choose κs I g c₀ α hsec using hlev'
  have hlow' : ∀ t : ℕ, ∃ U : ℤ, t < e → ∀ u ≤ U, ∀ c : Fin d → O, dvO W T e b c ∈ FilS W T a t u := by
    intro t
    by_cases ht : t < e
    · obtain ⟨U, hU⟩ := hlow t ht
      exact ⟨U, fun _ => hU⟩
    · exact ⟨0, fun h' => absurd h' ht⟩
  choose U hU using hlow'
  set N : ℕ := ∑ s ∈ Finset.range e, ∑ i : Fin (I s), ∑ t ∈ Finset.range e,
    ((U t).natAbs + (α s i t).natAbs) with hN
  set κ : ℕ := ∑ s ∈ Finset.range e, κs s with hκ
  obtain ⟨m, ε, -, hεd, hsum⟩ :=
    exists_partition_of_l_pow_levels W hC N (Finset.range e) ⟨0, Finset.mem_range.2 (by omega)⟩
  choose! r hr hεr using hεd
  have hlE : ∀ j, lE W j = algebraMap (LetA O n) W.EE (lA W ^ j) := by
    intro j; simp [lE, lA]
  have hκs : ∀ s < e, κs s ≤ κ := fun s hs =>
    Finset.single_le_sum (f := κs) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  let σ := Σ s : Fin e, Fin (I s)
  let eqv := Fintype.equivFin σ
  let G' : σ → W.EE := fun p => algebraMap (LetA O n) W.EE
    ((∏ t ∈ (Finset.range e).erase (p.1 : ℕ), ps W t ^ N) * (r p.1 * lA W ^ (κ - κs p.1))) * g p.1 p.2
  let C' : σ → Fin d → O := fun p => c₀ p.1 p.2
  let A' : σ → ℕ → ℤ := fun p t => if t = (p.1 : ℕ) then α p.1 p.2 t else α p.1 p.2 t + N
  have hmono : ∀ p : σ, InId W a e (A' p) (G' p) ∧ condNN W T a e b (A' p) (C' p) := by
    rintro ⟨⟨s, hs⟩, i⟩
    have hx : r s * lA W ^ (κ - κs s) ∈ W.AΔ :=
      W.AΔ.mul_mem (hr s (Finset.mem_range.2 hs)) (l_pow_mem_invariants W _)
    refine ⟨inId_shift_levels W hR hs ((hsec s hs).1 i).1 hx, fun t ht => ?_⟩
    by_cases hts : t = s
    · subst hts
      simp only [A', if_true]
      exact ((hsec t hs).1 i).2
    · simp only [A', hts, if_false]
      refine hU t ht _ ?_ _
      have h1 : (U t).natAbs + (α s i t).natAbs ≤
          ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) :=
        Finset.single_le_sum (f := fun t' => (U t').natAbs + (α s i t').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 ht)
      have h2 : ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) ≤
          ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) :=
        Finset.single_le_sum (f := fun i' => ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h3 : ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) ≤ N :=
        Finset.single_le_sum (f := fun s' => ∑ i' : Fin (I s'), ∑ t' ∈ Finset.range e,
          ((U t').natAbs + (α s' i' t').natAbs)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
      have hN' : (((U t).natAbs : ℕ) : ℤ) + (((α s i t).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast h1.trans (h2.trans h3)
      rw [Int.natCast_natAbs, Int.natCast_natAbs] at hN'
      have e1 := neg_abs_le (U t)
      have e2 := neg_abs_le (α s i t)
      linarith
  refine ⟨m + κ, Fintype.card σ, fun j => G' (eqv.symm j), fun j => C' (eqv.symm j),
    fun j => A' (eqv.symm j), fun j => hmono (eqv.symm j), fun k => ?_⟩
  rw [Equiv.sum_comp eqv.symm (fun p => G' p * algebraMap O W.EE (C' p k)), Fintype.sum_sigma]
  calc lE W (m + κ) * h k
      = (∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s)) * (lE W κ * h k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hsum, ← hlE, lE, lE, lE, pow_add]; ring
    _ = ∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : lE W κ = lE W (κ - κs s) * lE W (κs s) := by
          rw [lE, lE, lE, ← pow_add, Nat.sub_add_cancel (hκs s (Finset.mem_range.1 hs))]
        rw [this]; ring
    _ = ∑ s : Fin e, ∑ i : Fin (I s), G' ⟨s, i⟩ * algebraMap O W.EE (C' ⟨s, i⟩ k) := by
        rw [Finset.sum_range (fun s => algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k))]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [(hsec s s.2).2 k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [G', C']
        rw [hεr s (Finset.mem_range.2 s.2), hlE]
        simp only [map_mul]
        ring

end Core

end Formalism.MainNotions.N.Ln17
end
end

