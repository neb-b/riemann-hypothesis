module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0030
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CompositeOfChainHolds
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.HorTrUnique
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

theorem lam_unit (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (abelian₂ W A a e)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W
    (Formalism.MainNotions.UnusedSlot80.SatW.UPi.prod _ _ fun s _ => (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s).pow _)

theorem lam_piPs (A : ArcP n) (a : ZMod n) (e : ℕ) : abelian₂ W A a e ∈ PiPs W :=
  Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (Submonoid.subset_closure
    (show ps W s ∈ insert W.π₀ (Set.range (ps W)) from Set.mem_insert_of_mem _ ⟨s, rfl⟩)) _

theorem piLam_piPs (A : ArcP n) (a : ZMod n) (e : ℕ) : W.π₀ * abelian₂ W A a e ∈ PiPs W :=
  Submonoid.mul_mem _ (Submonoid.subset_closure (Set.mem_insert _ _)) (lam_piPs W A a e)

theorem lA_smul_eq (T : LocLat G Qp LL O) (t : ℕ) (z : W.DD T) :
    lA W ^ t • z = (((PD.p : ℕ) : O) ^ t) • z := by
  rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ t) z, map_pow, map_natCast]
  rfl

theorem lA_smul_smul (T : LocLat G Qp LL O) (t s : ℕ) (z : W.DD T) :
    lA W ^ t • lA W ^ s • z = lA W ^ (s + t) • z := by
  rw [smul_smul, ← pow_add, add_comm]

theorem φpow_lA (T : LocLat G Qp LL O) (e t : ℕ) (z : W.DD T) :
    ((W.φD T) ^ e) (lA W ^ t • z) = lA W ^ t • ((W.φD T) ^ e) z := by
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow]
  congr 2
  unfold lA
  rw [map_natCast]

theorem vecB_smul (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (c : O) (y : Fin d → O) :
    Formalism.MainNotions.LiftingTheory.vecB W T b (fun m => c * y m) = c • Formalism.MainNotions.LiftingTheory.vecB W T b y := by
  unfold Formalism.MainNotions.LiftingTheory.vecB
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => mul_smul _ _ _

theorem horTr_scale (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (R κ t : ℕ) (k : Fin d) {H : W.DD T} (h : IsHorTr W T b sol R κ k H) :
    IsHorTr W T b sol R (κ + t) k (lA W ^ t • H) := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨fun r m => ((PD.p : ℕ) : O) ^ t * y r m, fun r hr m => ?_, ?_⟩
  · rw [map_mul, map_pow, map_natCast, hy r hr m, pow_add]; ring
  · rw [lA_smul_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [vecB_smul, smul_comm]

variable [IsDomain O]

theorem horTr_unique (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (R κ : ℕ) (k : Fin d) {H H' : W.DD T}
    (h : IsHorTr W T b sol R κ k H) (h' : IsHorTr W T b sol R κ k H') : H = H' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', rfl⟩ := h'
  refine Finset.sum_congr rfl fun r hr => ?_
  have : y r = y' r := funext fun m => hinj ((hy r (Finset.mem_range.1 hr) m).trans
    (hy' r (Finset.mem_range.1 hr) m).symm)
  rw [this]

def RV (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ : ℕ)
    (Hh : Fin d → W.DD T) (x : W.DD T) (f : Fin d → W.EE) : Prop :=
  ∃ (κ' : ℕ) (a : Fin d → LetA O n),
    (∀ k, a k ∈ W.AΔ ∧ algebraMap (LetA O n) W.EE Λ * f k = algebraMap (LetA O n) W.EE (a k)) ∧
    InFP W T c' e (W.π₀ * Λ ^ 2) (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k)))

theorem repVV_iff (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE) :
    RepVV W T c' e M Λ b sol x f ↔
      ∃ κ Hh, (∀ k, IsHorTr W T b sol M κ k (Hh k)) ∧ RV W T c' e Λ κ Hh x f := by
  constructor
  · rintro ⟨κ, κ', Hh, a, h1, h2, h3⟩
    exact ⟨κ, Hh, h1, κ', a, h2, h3⟩
  · rintro ⟨κ, Hh, h1, κ', a, h2, h3⟩
    exact ⟨κ, κ', Hh, a, h1, h2, h3⟩

theorem rv_up (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ t : ℕ)
    (Hh : Fin d → W.DD T) (x : W.DD T) (f : Fin d → W.EE) (h : RV W T c' e Λ κ Hh x f) :
    RV W T c' e Λ (κ + t) (fun k => lA W ^ t • Hh k) x f := by
  obtain ⟨κ', a, ha, hP⟩ := h
  refine ⟨κ', a, ha, ?_⟩
  have e1 : lA W ^ κ' • (lA W ^ (κ + t) • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (lA W ^ t • Hh k)) =
      lA W ^ t • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
    simp only [φpow_lA, smul_sub, Finset.smul_sum, smul_smul, pow_add]
    congr 1
    · ring_nf
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      ring
  rw [e1]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W t) hP

theorem rv_add (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ : ℕ)
    (Hh : Fin d → W.DD T) (x y : W.DD T) (f g : Fin d → W.EE) (hx : RV W T c' e Λ κ Hh x f)
    (hy : RV W T c' e Λ κ Hh y g) : RV W T c' e Λ κ Hh (x + y) (f + g) := by
  obtain ⟨κ₁, a₁, ha₁, hP₁⟩ := hx
  obtain ⟨κ₂, a₂, ha₂, hP₂⟩ := hy
  refine ⟨κ₁ + κ₂, a₁ + a₂, fun k => ⟨W.AΔ.add_mem (ha₁ k).1 (ha₂ k).1, ?_⟩, ?_⟩
  · rw [Pi.add_apply, mul_add, (ha₁ k).2, (ha₂ k).2, Pi.add_apply, map_add (f := _)]
  · have e1 : lA W ^ (κ₁ + κ₂) • (lA W ^ κ • Λ • (x + y) - ∑ k, (a₁ + a₂) k • ((W.φD T) ^ e) (Hh k)) =
        lA W ^ κ₂ • (lA W ^ κ₁ • (lA W ^ κ • Λ • x - ∑ k, a₁ k • ((W.φD T) ^ e) (Hh k))) +
        lA W ^ κ₁ • (lA W ^ κ₂ • (lA W ^ κ • Λ • y - ∑ k, a₂ k • ((W.φD T) ^ e) (Hh k))) := by
      rw [lA_smul_smul, lA_smul_smul, add_comm κ₂ κ₁, ← smul_add]
      congr 1
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]
      abel
    rw [e1]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hP₁)
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hP₂)

theorem rv_smul (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ : ℕ)
    (Hh : Fin d → W.DD T) (x : W.DD T) (f : Fin d → W.EE) {c : LetA O n} (hc : c ∈ W.AΔ)
    (hx : RV W T c' e Λ κ Hh x f) :
    RV W T c' e Λ κ Hh (c • x) (fun k => algebraMap (LetA O n) W.EE c * f k) := by
  obtain ⟨κ₁, a₁, ha₁, hP₁⟩ := hx
  refine ⟨κ₁, fun k => c * a₁ k, fun k => ⟨W.AΔ.mul_mem hc (ha₁ k).1, ?_⟩, ?_⟩
  · rw [mul_left_comm, (ha₁ k).2, ← map_mul]
  · have e1 : lA W ^ κ₁ • (lA W ^ κ • Λ • (c • x) - ∑ k, (c * a₁ k) • ((W.φD T) ^ e) (Hh k)) =
        c • (lA W ^ κ₁ • (lA W ^ κ • Λ • x - ∑ k, a₁ k • ((W.φD T) ^ e) (Hh k))) := by
      simp only [smul_sub, Finset.smul_sum, mul_smul]
      congr 1
      · rw [smul_comm c (lA W ^ κ₁), smul_comm c (lA W ^ κ), smul_comm c Λ]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_comm c (lA W ^ κ₁)]
    rw [e1]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ hc hP₁

theorem repVV_add (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (c' : ZMod n)
    (e M : ℕ) (Λ : LetA O n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (x y : W.DD T) (f g : Fin d → W.EE) (hx : RepVV W T c' e M Λ b sol x f)
    (hy : RepVV W T c' e M Λ b sol y g) : RepVV W T c' e M Λ b sol (x + y) (f + g) := by
  rw [repVV_iff] at hx hy ⊢
  obtain ⟨κ₁, H₁, hH₁, hR₁⟩ := hx
  obtain ⟨κ₂, H₂, hH₂, hR₂⟩ := hy
  have h1 := rv_up W T c' e Λ κ₁ κ₂ H₁ x f hR₁
  have h2 := rv_up W T c' e Λ κ₂ κ₁ H₂ y g hR₂
  have hH : ∀ k, lA W ^ κ₂ • H₁ k = lA W ^ κ₁ • H₂ k := fun k =>
    horTr_unique W hinj T b sol M _ k (horTr_scale W T b sol M κ₁ κ₂ k (hH₁ k))
      (by rw [add_comm]; exact horTr_scale W T b sol M κ₂ κ₁ k (hH₂ k))
  rw [show (fun k => lA W ^ κ₁ • H₂ k) = fun k => lA W ^ κ₂ • H₁ k from funext fun k => (hH k).symm,
    add_comm κ₂ κ₁] at h2
  exact ⟨κ₁ + κ₂, _, fun k => horTr_scale W T b sol M κ₁ κ₂ k (hH₁ k), rv_add W T c' e Λ _ _ x y f g h1 h2⟩

theorem repVV_smul (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE)
    {c : LetA O n} (hc : c ∈ W.AΔ) (hx : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (c • x) (fun k => algebraMap (LetA O n) W.EE c * f k) := by
  rw [repVV_iff] at hx ⊢
  obtain ⟨κ, H, hH, hR⟩ := hx
  exact ⟨κ, H, hH, rv_smul W T c' e Λ κ H x f hc hR⟩

theorem repVV_sub (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (c' : ZMod n)
    (e M : ℕ) (Λ : LetA O n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (x y : W.DD T) (f g : Fin d → W.EE) (hx : RepVV W T c' e M Λ b sol x f)
    (hy : RepVV W T c' e M Λ b sol y g) : RepVV W T c' e M Λ b sol (x - y) (f - g) := by
  have h := repVV_smul W T c' e M Λ b sol y g (W.AΔ.neg_mem W.AΔ.one_mem) hy
  simp only [map_neg, map_one, neg_one_mul, neg_smul, one_smul] at h
  have := repVV_add W hinj T c' e M Λ b sol x (-y) f (fun k => -g k) hx h
  rwa [← sub_eq_add_neg, show f + (fun k => -g k) = f - g from by funext k; simp [sub_eq_add_neg]] at this

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MapEqOfProdEq
section
noncomputable section

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open Matrix Polynomial Formalism.RepresentationBoundsCohomology.ringDataObjects

section GlobalTheory

variable (r t : ℕ)

def blkG (a : Fin (r + t)) : Fin (t + 1) :=
  if _h : (a : ℕ) < r then 0 else ⟨(a : ℕ) - r + 1, by have := a.2; omega⟩

theorem blkG_castAdd (a : Fin r) : blkG r t (Fin.castAdd t a) = 0 := by
  rw [blkG, dite_eq_left (by simp)]

theorem blkG_natAdd (c : Fin t) : blkG r t (Fin.natAdd r c) = c.succ := by
  rw [blkG, dite_eq_right (by simp only [Fin.coe_natAdd]; omega)]
  ext
  simp

variable (K : Type) [CommRing K]

def eG : (Fin (r + t) → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)) :=
  (LinearEquiv.funCongrLeft K K finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) K K)

theorem eG_apply (u : Fin (r + t) → K) :
    eG r t K u = (fun a => u (Fin.castAdd t a), fun c => u (Fin.natAdd r c)) := rfl

variable {r t K}

theorem eG_mulVec (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (hM : ∀ a b, blkG r t a ≠ blkG r t b → M a b = 0) (u : Fin (r + t) → K) :
    eG r t K (M *ᵥ u) = ((M.submatrix (Fin.castAdd t) (Fin.castAdd t)) *ᵥ (eG r t K u).1,
      fun c => M (Fin.natAdd r c) (Fin.natAdd r c) * (eG r t K u).2 c) := by
  simp only [eG_apply]
  ext a
  · simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [Fin.sum_univ_add]
    have h0 : ∀ c : Fin t, M (Fin.castAdd t a) (Fin.natAdd r c) = 0 := fun c =>
      hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact (Fin.succ_ne_zero c).symm)
    simp [h0]
  · simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add]
    have h1 : ∀ b : Fin r, M (Fin.natAdd r a) (Fin.castAdd t b) = 0 := fun b =>
      hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact Fin.succ_ne_zero a)
    have h2 : ∀ c : Fin t, c ≠ a → M (Fin.natAdd r a) (Fin.natAdd r c) = 0 := fun c hc =>
      hM _ _ (by rw [blkG_natAdd, blkG_natAdd]; exact fun h => hc (Fin.succ_injective _ h).symm)
    simp only [h1, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single a (fun c _ hc => by rw [h2 c hc, zero_mul]) (by simp)]

end GlobalTheory

section Pts

variable {O Y : Type} [CommRing O] [IsDomain O] (t : ℕ) (P : Y → O[X])

end Pts

section EE

variable {A : Type} [CommRing A] {d : Type} [Fintype d] [DecidableEq d]

end EE

section Gen2

variable {r t : ℕ} {A : Type} [CommRing A]

theorem blkG_inj {a b : Fin (r + t)} (h : blkG r t a = blkG r t b) (ha : blkG r t a ≠ 0) : a = b := by
  unfold blkG at h ha
  by_cases h1 : (a : ℕ) < r
  · rw [dite_eq_left h1] at ha
    exact absurd rfl ha
  · by_cases h2 : (b : ℕ) < r
    · rw [dite_eq_left h2, dite_eq_right h1] at h
      exact absurd (congrArg Fin.val h) (by simp)
    · rw [dite_eq_right h1, dite_eq_right h2] at h
      have h3 : (a : ℕ) - r + 1 = (b : ℕ) - r + 1 := congrArg Fin.val h
      exact Fin.ext (by omega)

theorem diag_conj (M : Matrix (Fin (r + t)) (Fin (r + t)) A)
    (hM : ∀ a b, blkG r t a ≠ blkG r t b → M a b = 0) :
    (Matrix.diagonal fun a => if blkG r t a = 0 then (0 : A) else 1) * M *
        (Matrix.diagonal fun a => if blkG r t a = 0 then (0 : A) else 1) =
      Matrix.diagonal fun a => if blkG r t a = 0 then 0 else M a a := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> simp_all
  · rw [if_neg hab]
    by_cases ha : blkG r t a = 0
    · simp [ha]
    · by_cases hb : blkG r t b = 0
      · simp [hb]
      · have hne : blkG r t a ≠ blkG r t b := fun h => hab (blkG_inj h ha)
        simp [hM a b hne]

end Gen2

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses
section
noncomputable section

open Classical

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem truncation_clause_of_lattice_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    Formalism.MainNotions.CrystallineLiftingInputs.adm15 D HW F Cm := by
  refine ⟨Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds, fun l _ K LL hg _ => ?_⟩
  have hP9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := hP9 l K 1 LL hg
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact ⟨tTool1_of _ hinj hO2 hP9W (h8 l K 1 LL hg),
    tTool2_of _ hinj hO2 hlm hP9W (h8 l K 1 LL hg) (h9 l K 1 LL hg)⟩

theorem tTool2Z_DU (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hP9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := hP9 l K 1 LL hg
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact tTool2Z_of _ hinj hO2 hlm hP9W (h8 l K 1 LL hg) (h9 l K 1 LL hg)

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData
end
end

