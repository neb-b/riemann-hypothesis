module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitOfResidueConstNeZero

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InFNcOfInFPOfArcSigmaLe
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem inFNc_of_inFP_of_arc_sigma_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  :
    ∀ x : W.DD T₂, InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) x → InFNc W T₂ c 1 x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨qA W ^ (size c + S) • y, ?_, ?_, (one_smul _ _).symm⟩
  · refine DYB.Pp_qpow (W := W) T₂ (c - 1) (size c + S) ?_ hy
    intro z hz
    obtain ⟨-, hs, hp2⟩ := id hcase
    obtain ⟨hcr, hWj⟩ := id hW₂
    obtain ⟨-, -, h9one⟩ := hP9 T₂ hcr hs hp2
    obtain ⟨hring, -⟩ := h9one (NTB.finrank_one W hcase)
    obtain ⟨-, -, -, -, ⟨u, hu⟩, -⟩ := hring
    have hq : W.q = (u : LetA O n) * qA W := by
      rw [hu]
      congr 1
      funext i
      simp [DeltaInvariantLattices.Eat, qA, lA]
    have hQ : W.Q = W.q := by
      simp [LocWach.Q, hs]
    obtain ⟨-, hS, -⟩ := hB
    unfold TruncatedSeriesCountingBounds.HidaSetting at hS
    obtain ⟨-, -, hηs, -⟩ := hS
    have hJ : DeltaInvariantLattices.JumpsLet W T₂ (fun i => size i + S) (fun i => size i + S) := by
      intro τ i hτ a ha
      have h2 := hWj i τ hτ a ha
      have hη := hηs i
      cases hup : up i <;> simp [arcOf, hup, LocalTheoryWindows.LT.win] at h2 <;>
        simp only [Set.mem_Icc, Nat.cast_add] <;> omega
    have h5 : W.Q ^ (size c + S) • W.φD T₂ z ∈ W.N T₂ :=
      (hP5 T₂ (fun i => size i + S) (fun i => size i + S) hcr hJ).1 c z hz.2
    rw [hQ, hq] at h5
    have h6 := Submodule.smul_mem (W.N T₂) ((↑(u⁻¹) : LetA O n) ^ (size c + S)) h5
    rw [smul_smul, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul] at h6
    exact h6
  · have hH := DYB.Pp_le_HLD (W := W) T₂ (c - 1) hy
    obtain ⟨h, -⟩ := hH
    rw [sub_add_cancel] at h
    rw [smul_smul, mul_comm, ← smul_smul, h]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InIOfMemPi0Lattice
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundGal

open Formalism.MainNotions.N.Ln17.PCutBoundRep Formalism.MainNotions.N.Ln17.PCutBoundRho

section Gal

variable {W : LocWach PD LL O v n} {A : ArcP n} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    {c : ZMod n} {d : ℕ} {b : Fin d → W.DD T₂} {sol : Fin d → ℕ → Fin d → LL}

theorem LV_congr {g g' : Fin d → W.EE} {e : ℕ} (h : LV W A F c b sol g e) (hg : ∀ k, g k = g' k) :
    LV W A F c b sol g' e := by
  obtain rfl : g = g' := funext hg
  exact h

theorem LV_galois (hA : A.OK) (hc : c ∈ A.cuts) (hRelay : RelayCore W) (hArc : ArcCore W)
    (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    {g : Fin d → W.EE} {e : ℕ} (he : A.σ PD.p ≤ e) (h : LV W A F c b sol g e)
    (u : W.DD T₂) (hu : InI W T₂ c u)
    (huP : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • u))
    (hrep : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol u
      (fun k => lE W (A.σ PD.p) * g k))
    (x₂ : LatticeCohomology T₂.L) (hx₂ : IsRho W A T₂ c u x₂) :
    ∃ x₁ ∈ latticeFiniteCohomology PD T₁.L, F.H1map x₁ = (((PD.p : ℕ) : O) ^ (e - A.σ PD.p)) • x₂ := by
  obtain ⟨w₁, z, hw, ⟨Λ', hΛ', hΛw⟩, hP, hz, hR⟩ := h
  have hπ := TypesA.pi0_mem_ADelta W
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = PD.p ^ (e - A.σ PD.p) := ⟨_, rfl⟩
  have hjle : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hAc := hArc hcase hl A hA c hc (A.len c) hjle le_rfl
  simp only [sub_add_cancel] at hAc
  obtain ⟨-, hAT⟩ := hAc
  obtain ⟨hPN, hNP, -, hfr⟩ := hAT T₂ hW₂
  obtain ⟨-, -, -, -, -, h0, -⟩ := hfr d b sol hb
  have hRX : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u) 0 := by
    refine TypesA.RepVV_congr W (TypesA.RepVV_add W hR (TypesA.RepVV_neg W (TypesA.RepVV_nat W N hrep)))
      (sub_eq_add_neg _ _).symm fun k => ?_
    rw [Pi.zero_apply]
    unfold lE
    rw [hN, Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel he, add_neg_cancel]
  have hz1 : InFNc W T₂ c 1 z := TypesA.InFNc_one_smul W hπ hz
  have hΛX : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
      (abelian₂ W A c (A.len c) • (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u)) := by
    rw [smul_sub, smul_sub]
    refine TypesA.inMultiple_sub W (TypesA.inMultiple_sub W hP (hNP z hz1)) ?_
    rw [smul_comm]
    exact TypesA.inMultiple_smul W (natCast_mem _ _) huP
  obtain ⟨y, hy, hXy⟩ := h0 _ hΛX hRX
  obtain ⟨y'', hy'', hyc'', hΛy⟩ := hPN y hy
  have hXπ : InFNc W T₂ c W.π₀ (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u) :=
    ⟨y'', hy'', hyc'', by rw [hXy, mul_smul, hΛy, one_smul]⟩
  have hπw : InFNc W T₂ c W.π₀ (W.map F w₁ - ((N : ℕ) : LetA O n) • u) := by
    have hsplit : W.map F w₁ - ((N : ℕ) : LetA O n) • u =
        z + (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u) := by abel
    rw [hsplit]
    exact TypesA.InFNc_add W hz hXπ
  have hIw : InI W T₂ c (W.map F w₁ - ((N : ℕ) : LetA O n) • u) := by
    rw [sub_eq_add_neg]
    exact TypesA.InI_add W (TypesA.InI_map W F hW₁.1 hW₂.1 hw) (TypesA.InI_neg W (TypesA.InI_nat W N hu))
  obtain ⟨hRel, hNat⟩ := hRelay hcase hl A hA c hc
  obtain ⟨-, hR1, -⟩ := hRel T₁ hW₁
  obtain ⟨-, hR2, hAdd⟩ := hRel T₂ hW₂
  obtain ⟨-, -, -, ⟨x₁, hx₁⟩, -, -, hPs⟩ := hR1 w₁ hw
  have hx₁f : x₁ ∈ latticeFiniteCohomology PD T₁.L := hPs Λ' x₁ hΛ' hΛw hx₁
  have hnat := hNat T₁ T₂ F hW₁ hW₂ w₁ x₁ hw hx₁
  have hNu : ∀ k : ℕ, IsRho W A T₂ c (((k : ℕ) : LetA O n) • u) (k • x₂) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_smul, zero_nsmul]
      exact (hR2 0 (TypesA.InI_zero W)).2.2.2.2.2.1 ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, succ_nsmul]
      exact hAdd _ _ _ _ (TypesA.InI_nat W k hu) hu ih hx₂
  have hw0 : IsRho W A T₂ c (W.map F w₁ - ((N : ℕ) : LetA O n) • u) 0 :=
    (hR2 _ hIw).2.2.2.2.2.1 hπw
  have hsum := hAdd _ _ _ _ hIw (TypesA.InI_nat W N hu) hw0 (hNu N)
  rw [sub_add_cancel, zero_add] at hsum
  have huniq := (hR2 (W.map F w₁) (TypesA.InI_map W F hW₁.1 hW₂.1 hw)).2.2.2.2.1 _ _ hnat hsum
  refine ⟨x₁, hx₁f, ?_⟩
  rw [huniq, hN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end Gal

theorem pk_eq (W : LocWach PD LL O v n) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) (κ : ℕ) (P1 : O)
    (hv : v (algebraMap O LL P1) = ((κ : ℕ) : WithTop ℚ)) : ∃ y : O, ((PD.p : ℕ) : O) ^ κ = y * P1 := by
  have hP1 : algebraMap O LL P1 ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact (WithTop.natCast_ne_top κ) hv.symm
  set z : LL := (PD.p : LL) ^ κ * (algebraMap O LL P1)⁻¹ with hz
  have hzP : z * algebraMap O LL P1 = (PD.p : LL) ^ κ := by
    rw [hz, mul_assoc, inv_mul_cancel₀ hP1, mul_one]
  have hvz : 0 ≤ v z := by
    by_cases htop : v z = ⊤
    · rw [htop]; exact le_top
    have h1 := congrArg v hzP
    rw [AddValuation.map_mul, AddValuation.map_pow, W.v_l, hv, nsmul_one] at h1
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hq, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_inj] at h1
    have hq0 : q = 0 := by linarith
    rw [← hq, hq0]
    exact le_refl _
  obtain ⟨y, hy⟩ := hOv z hvz
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, map_pow, map_natCast, hzP]

section Fr

variable (W : LocWach PD LL O v n)

theorem InFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, he⟩ := h
  obtain ⟨u', hu', he'⟩ := h'
  exact ⟨u + u', add_mem hu hu', by rw [mul_add, he, he', ← map_add (f := _), mul_add]⟩

theorem InFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, zero_mem _, by simp⟩

theorem InFr_smulO {a : ZMod n} {num den : LetA O n} (o : O) {f : W.EE} (h : InFr W a num den f) :
    InFr W a num den (o • f) := by
  obtain ⟨u, hu, he⟩ := h
  refine ⟨algebraMap O (LetA O n) o * u, W.AΔ.mul_mem (W.AΔ.algebraMap_mem o) hu, ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, he, ← map_mul]
  congr 1
  ring

theorem InFr_Lam_iff (A : ArcP n) (a : ZMod n) (e : ℕ) (f : W.EE) :
    InFr W a 1 (abelian₂ W A a e) f ↔ InId W a e (fun s => -(A.Hs a e s : ℤ)) f := by
  unfold InId abelian₂
  have h1 : ∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    rw [show (-(A.Hs a e s : ℤ)).toNat = 0 by omega, pow_zero]
  have h2 : ∀ s, (-(-(A.Hs a e s : ℤ))).toNat = A.Hs a e s := fun s => by omega
  simp only [h1, h2]

theorem InFr_γ (hR : GS.RD W) (A : ArcP n) {a : ZMod n} {e : ℕ} {f : W.EE} (h : InFr W a 1 (abelian₂ W A a e) f) :
    InFr W a 1 (abelian₂ W A a e) (W.γE W.gam f) := by
  rw [InFr_Lam_iff] at h ⊢
  exact (GS.gam_frac_core hR a e _ f h).1

theorem InFr_aeval (hR : GS.RD W) (A : ArcP n) {a : ZMod n} {e : ℕ} {f : W.EE}
    (h : InFr W a 1 (abelian₂ W A a e) f) (P : Polynomial O) :
    InFr W a 1 (abelian₂ W A a e) (Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f) := by
  rw [aevalE_eq]
  refine Finset.sum_induction _ _ (fun _ _ => InFr_add W) (InFr_zero W) fun i hi => InFr_smulO W _ ?_
  clear hi
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InFr_γ W hR A ih

end Fr

section Cls

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem inI_of_mem_pi0_lattice (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {z : W.DD T}
    (h : InFNc W T c W.π₀ z) : InI W T c z := by
  obtain ⟨y, hy, hyc, rfl⟩ := h
  obtain ⟨u, hu, hγπ⟩ := hpi0
  have hy' : y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ y = y := hy
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (W.π₀ • y) = W.π₀ • y
    rw [smul_comm, hyc]
  · show ∀ δ ∈ W.DelF, W.γD T δ (W.π₀ • y) = W.π₀ • y
    intro δ hδ
    rw [GS.γD_smulA, TypesA.pi0_mem_ADelta W δ hδ, hy'.2 δ hδ]
  · refine ⟨u • W.γ T y - y, sub_mem (TypesA.NΔ_smul W hu (γ_NΔ W hT hP2 hy)) hy, ?_, ?_⟩
    · rw [smul_sub, hyc, smul_comm, ← GS.γA_letE W W.gam c, ← γ_smul, hyc]
    · rw [γ_smul, hγπ, smul_sub, mul_smul]

variable {c' : ZMod n} {e : ℕ} {Λ : LetA O n}

theorem InFPΛ_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ) {x : W.DD T}
    (h : InFP W T c' e 1 (Λ • x)) : InFP W T c' e 1 (Λ • W.γ T x) := by
  obtain ⟨R, -, R', hR', hRR, hγΛ⟩ := hΛ
  have h2 := γ_InFP W hT hP2 h
  rw [map_one, γ_smul, hγΛ] at h2
  have h3 := TypesA.inMultiple_smul W hR' h2
  rwa [smul_smul, ← mul_assoc, mul_comm R' R, hRR, one_mul] at h3

theorem InFPΛ_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ) {x : W.DD T}
    (h : InFP W T c' e 1 (Λ • x)) (P : Polynomial O) :
    InFP W T c' e 1 (Λ • Polynomial.aeval (W.γ T) P x) := by
  rw [aeval_eq, Finset.smul_sum]
  refine inMultiple_sum W _ _ fun i hi => ?_
  clear hi
  rw [← algebraMap_smul (LetA O n) (P.coeff i), smul_comm]
  refine TypesA.inMultiple_smul W (W.AΔ.algebraMap_mem _) ?_
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InFPΛ_γ W hT hP2 hΛ ih

end Cls

end Formalism.MainNotions.N.Ln17.PCutBoundGal
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
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

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem LiftsAt.liftsAt_mono {f : W.EE} {e e' : ℕ} (he : e ≤ e') (h : LiftsAt W A F c b sol k₀ f e) :
    LiftsAt W A F c b sol k₀ f e' :=
  LiftsAtT.mono W A F c b sol k₀ he h

theorem LiftsAt.add_proof {f f' : W.EE} {e : ℕ} (h : LiftsAt W A F c b sol k₀ f e)
    (h' : LiftsAt W A F c b sol k₀ f' e) : LiftsAt W A F c b sol k₀ (f + f') e :=
  LiftsAtT.add W A F c b sol k₀ h h'

theorem liftsAt_thick_letter_type [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLpp W A T₂ c b k₀)
    (f : W.EE) (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    LiftsAt W A F c b sol k₀ f (rr + A.σ PD.p) :=
  N_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂
    hsur rr hrr hb hk₀ f hf hdown

theorem liftsAt_constants_type (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLpp W A T₂ c b k₀)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1)) (x : O) :
    LiftsAt W A F c b sol k₀ (algebraMap O W.EE x) (rr + A.σ PD.p) :=
  constants_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hArcL
    hW₁ hW₂ hsur rr hrr hb hk₀ b₁ sol₁ hb₁ c₁ hpr x

theorem liftsAt_thin_letter_type (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAt W A F c b sol k₀ f (s₀ + A.σ PD.p) :=
  C_typeT W A F c b sol k₀ hA hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc hW₁ hW₂ hb Si hSi
    b₁ sol₁ hb₁ c₁ s₀ hlt hpr f hf hdown hup

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QPowMemOfGenerator
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem q_pow_mem_of_generator [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i : ZMod n) (Bq : ℕ) (g : LetA O n) (hg : g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k})
    (x : W.DD T) (hx : InFP W T i 1 1 x) (hgx : ∃ k : ℕ, InFP W T i 1 (qA W ^ Bq) (lA W ^ k • g • x)) :
    InFP W T i 1 (qA W ^ Bq) x := by

  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨-, N, a, ha, b, hb, hN⟩ := l_pow_mem_levels_q_pow_ideal Br Bq hg
  obtain ⟨k, z, hz, hkz⟩ := hgx
  have hx1 : x ∈ Pp W T i 1 := by
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy, one_smul]
    exact hy
  have hlx : lA W ^ k • x ∈ Pp W T i 1 := by
    rw [show lA W ^ k = ((PD.p ^ k : ℕ) : LetA O n) by simp [lA], Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx1 _
  have hqPi : qA W ^ Bq ∈ PiPs W := by
    apply Submonoid.pow_mem
    unfold PiPs
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨0, by simp [ps]⟩)
  have h1 : InFP W T i 1 1 ((1 : LetA O n) • x) := by
    rw [one_smul]
    exact hx

  have key : lA W ^ (k + N) • x = qA W ^ Bq • (a • z + b • (lA W ^ k • x)) := by
    calc lA W ^ (k + N) • x = (a * g + b * qA W ^ Bq) • (lA W ^ k • x) := by
          rw [← hN, smul_smul, ← pow_add, Nat.add_comm k N]
      _ = a • (lA W ^ k • g • x) + b • (qA W ^ Bq • (lA W ^ k • x)) := by
          rw [add_smul, mul_smul, mul_smul, smul_comm g (lA W ^ k) x]
      _ = qA W ^ Bq • (a • z + b • (lA W ^ k • x)) := by
          rw [hkz, smul_add, smul_comm a, smul_comm b]
  have hmem : a • z + b • (lA W ^ k • x) ∈ Pp W T i 1 :=
    add_mem (DYB.Pp_smul W T i ha hz) (DYB.Pp_smul W T i hb hlx)
  exact hSatP hcase T i 1 (qA W ^ Bq) 1 hT hqPi (one_mem _) x h1
    ⟨k + N, by unfold InFP; exact ⟨_, hmem, key⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

