module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0035

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InNOfPiLam
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

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem φ_Pp (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) :
    ∀ y ∈ Pp W T c' e, W.φD T y ∈ Pp W T c' (e + 1) := by
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' e _ (by simpa using (Pp W T c' (e + 1)).zero_mem)
    (fun x y hx hy => by rw [map_add (f := _)]; exact (Pp W T c' (e + 1)).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Pp W T c' (e + 1)).neg_mem hx) ?_
  intro a ha x hx
  rw [φD_smulA, ← pow_apply_succ]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' (e + 1) (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ ha) hx

theorem φ_InFP (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (F : LetA O n) {y : W.DD T}
    (h : InFP W T c' e F y) : InFP W T c' (e + 1) (W.φA F) (W.φD T y) := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨W.φD T p, φ_Pp W T c' e p hp, by rw [φD_smulA]⟩

theorem φA_lA (t : ℕ) : W.φA (lA W ^ t) = lA W ^ t := by
  rw [map_pow]; unfold lA; rw [map_natCast]

theorem φE_alg (a : LetA O n) : W.φE (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (W.φA a) :=
  W.φE_ext a

theorem φA_π₀ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∃ w ∈ W.AΔ, W.φA W.π₀ = w * W.π₀ * ps W 0 ^ (PD.p - 1) := by
  obtain ⟨-, w, hw⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have hq : (W.π₀ + ((PD.p : ℕ) : LetA O n)) = ps W 0 := by rw [ps_zero]; rfl
  rw [hq] at hw
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  have hc : W.π₀ * ps W 0 ^ (PD.p - 1) ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hp0Δ _)
  have hqP : Formalism.MainNotions.WachCoordinates.qP W = ps W 0 := by rw [ps_zero]; rfl
  have hc0 : ∀ i, (W.π₀ * ps W 0 ^ (PD.p - 1)) i ≠ 0 := by
    intro i
    rw [Pi.mul_apply, Pi.pow_apply, ← hqP]
    exact mul_ne_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) (pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0 i))
  refine ⟨(w : LetA O n), Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hc hc0 ?_, by rw [hw]⟩
  rw [show W.π₀ * ps W 0 ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ by rw [hw]; ring]
  exact Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hR.1

theorem transport (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n) (e M : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE)
    (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hrep : RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x f)
    (hfr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k))
    (N : ℕ) (hN : A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 ≤ N) {vv : LetA O n} (hv : vv ∈ W.AΔ) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T x)) ∧
    RepVV W T c' (e + 1) M (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol
      ((ps W 0 ^ N * vv) • W.φD T x)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ N * vv) * W.φE (f k)) ∧
    ∀ k, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1))
      (algebraMap (LetA O n) W.EE (ps W 0 ^ N * vv) * W.φE (f k)) := by
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  set u : LetA O n := ps W 0 ^ N * vv with hudef
  have hlam : abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) = ps W 0 ^ H * W.φA Λ := lam_succ W A c' e
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  have huΔ : u ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv
  have hupΔ : u * ps W 0 ^ H ∈ W.AΔ := W.AΔ.mul_mem huΔ (W.AΔ.pow_mem hp0Δ H)
  have hmain : ∀ z : W.DD T, abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u • W.φD T z) =
      (u * ps W 0 ^ H) • W.φD T (Λ • z) := by
    intro z
    rw [hlam, φD_smulA, smul_smul, smul_smul]
    congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp, hxp⟩ := hx
    rw [one_smul] at hxp
    refine ⟨(u * ps W 0 ^ H) • W.φD T p, Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) hupΔ _
      (φ_Pp W T c' e p hp), ?_⟩
    rw [one_smul, hmain, hxp]
  · rw [repVV_iff] at hrep ⊢
    obtain ⟨κ, Hh, hHh, κ', aa, haa, hP⟩ := hrep
    refine ⟨κ, Hh, hHh, κ', fun k => u * ps W 0 ^ H * W.φA (aa k), fun k =>
      ⟨W.AΔ.mul_mem hupΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (haa k).1), ?_⟩, ?_⟩
    · have h1 := congrArg W.φE (haa k).2
      rw [map_mul, φE_alg, φE_alg] at h1
      rw [hlam, map_mul (algebraMap (LetA O n) W.EE) (u * ps W 0 ^ H), ← h1, hudef]
      simp only [map_mul]
      ring
    · obtain ⟨w, hw, hφπ⟩ := φA_π₀ W hR hp0
      have hP' := φ_InFP W T c' e _ hP
      obtain ⟨q, hq, hqe⟩ := hP'
      have hE : W.φD T (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, aa k • ((W.φD T) ^ e) (Hh k))) =
          lA W ^ κ' • (lA W ^ κ • W.φA Λ • W.φD T x - ∑ k, W.φA (aa k) • ((W.φD T) ^ (e + 1)) (Hh k)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [φD_smulA, φA_lA, map_sub, φD_smulA, φA_lA, φD_smulA, map_sum]
        congr 2
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [φD_smulA, pow_apply_succ]
      rw [hE] at hqe
      have hkey : lA W ^ κ' • (lA W ^ κ • abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u • W.φD T x) -
          ∑ k, (u * ps W 0 ^ H * W.φA (aa k)) • ((W.φD T) ^ (e + 1)) (Hh k)) =
          (u * ps W 0 ^ H) • (lA W ^ κ' • (lA W ^ κ • W.φA Λ • W.φD T x -
            ∑ k, W.φA (aa k) • ((W.φD T) ^ (e + 1)) (Hh k))) := by
        rw [hlam]
        simp only [smul_sub, Finset.smul_sum, smul_smul]
        congr 1
        · congr 1; ring
        · refine Finset.sum_congr rfl fun k _ => ?_
          congr 1; ring
      rw [hkey, hqe, smul_smul]
      have hexp : H + H ≤ N + H + (PD.p - 1) := by omega
      refine ⟨(vv * w * ps W 0 ^ (N + H + (PD.p - 1) - (H + H))) • q,
        Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem hv hw)
          (W.AΔ.pow_mem hp0Δ _)) q hq, ?_⟩
      rw [smul_smul, hlam, map_mul, map_pow, hφπ]
      congr 1
      have e2 : ps W 0 ^ (N + H + (PD.p - 1)) = ps W 0 ^ (H + H) *
          ps W 0 ^ (N + H + (PD.p - 1) - (H + H)) := by
        rw [← pow_add, Nat.add_sub_cancel' hexp]
      rw [hudef]
      linear_combination (vv * w * W.π₀ * W.φA Λ ^ 2) * e2
  · intro k
    obtain ⟨t, ht, hft⟩ := hfr k
    refine ⟨u * ps W 0 ^ H * W.φA t, W.AΔ.mul_mem hupΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ ht), ?_⟩
    have h1 := congrArg W.φE hft
    rw [map_mul, φE_alg, φE_alg] at h1
    have hl : W.φA (letE (c' + (e : ZMod n)) : LetA O n) = letE (c' + ((e + 1 : ℕ) : ZMod n)) := by
      have := φA_letE W (c' + ((e + 1 : ℕ) : ZMod n))
      rwa [show c' + ((e + 1 : ℕ) : ZMod n) - 1 = c' + (e : ZMod n) by push_cast; ring] at this
    simp only [map_mul, mul_one, hl] at h1
    rw [hlam]
    simp only [map_mul, map_pow, mul_one]
    linear_combination (algebraMap (LetA O n) W.EE (ps W 0) ^ H * algebraMap (LetA O n) W.EE u) * h1

theorem piLam_of_sec (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hsatP : SATPcore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (A : ArcP n) (c' : ZMod n) (e M : ℕ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b)
    (x : W.DD T) (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x)) (h : Fin d → W.EE)
    (hrep : RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x h)
    (hh : ∀ k, InFr W (c' + (e : ZMod n)) (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) 1 (h k)) :
    InFP W T c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) x := by
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  rw [repVV_iff] at hrep
  obtain ⟨κ, Hh, hHh, κ', aa, haa, hP⟩ := hrep
  choose u hu hhu using hh
  have haa' : ∀ k, aa k = W.π₀ * Λ ^ 2 * (letE (c' + (e : ZMod n)) * u k) := by
    intro k
    apply W.EE_inj
    rw [← (haa k).2]
    have := hhu k
    rw [map_one, one_mul] at this
    rw [this, ← map_mul]
    congr 1; ring
  have hS : InFP W T c' e (W.π₀ * Λ ^ 2) (∑ k, aa k • ((W.φD T) ^ e) (Hh k)) := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sum W T c' e _ _ _ fun k _ => ?_
    rw [haa' k, mul_smul]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hu k)) _
      (horTr_mem W T c' b sol hb hR.1 M κ e k (hHh k)))
  have h2 : InFP W T c' e (W.π₀ * Λ ^ 2) (Λ • (lA W ^ (κ + κ') • x)) := by
    have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ hP
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κ') hS)
    rw [smul_sub, sub_add_cancel] at this
    rwa [lA_smul_smul, smul_comm] at this
  obtain ⟨p, hp, hpe⟩ := h2
  have hcan : lA W ^ (κ + κ') • x = (W.π₀ * Λ) • p := by
    refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T (lam_unit W hR A (c' + (e : ZMod n)) e) ?_
    rw [hpe, smul_smul]
    congr 1
    rw [← hΛdef]
    ring
  exact hsatP hCA T c' e (W.π₀ * Λ) Λ hTc (piLam_piPs W A _ e) (lam_piPs W A _ e) x hx
    ⟨κ + κ', p, hp, hcan⟩

theorem inN_of_piLam (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n) (e : ℕ)
    (hup : ∀ y ∈ Pp W T c' e, InFNc W T (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e • y))
    (x : W.DD T) (hx : InFP W T c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) x) :
    InFNc W T (c' + (e : ZMod n)) 1 x := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨y, hy, hyl, hye⟩ := hup p hp
  rw [one_smul] at hye
  refine ⟨W.π₀ • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hπ hy, by rw [smul_comm, hyl], ?_⟩
  rw [one_smul, mul_smul, hye]

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG

def blockZeroEquiv (r t : ℕ) : Fin r ≃ {a : Fin (r + t) // blkG r t a = 0} where
  toFun a := ⟨Fin.castAdd t a, blkG_castAdd r t a⟩
  invFun y := ⟨(y.1 : ℕ), by
    have h := y.2
    unfold blkG at h
    split_ifs at h with h1
    · exact h1
    · exact absurd h (by simp [Fin.ext_iff])⟩
  left_inv a := by
    ext
    rfl
  right_inv y := by
    apply Subtype.ext
    ext
    rfl

theorem absIrr_block {k G : Type} [Field k] {r t : ℕ} (M : G → Matrix (Fin (r + t)) (Fin (r + t)) k)
    (ρb : G → Matrix (Fin r) (Fin r) k)
    (h : ∀ g a b, M g (Fin.castAdd t a) (Fin.castAdd t b) = ρb g a b)
    (hs : Submodule.span k (Set.range ρb) = ⊤) :
    AbsIrr (fun g => (M g).toSquareBlock (blkG r t) 0) := by
  apply absIrr_of_span
  intro a b
  let L := Matrix.reindexLinearEquiv k k (blockZeroEquiv r t) (blockZeroEquiv r t)
  have hL : ∀ g, L (ρb g) = (M g).toSquareBlock (blkG r t) 0 := by
    intro g
    ext x y
    obtain ⟨x', rfl⟩ := (blockZeroEquiv r t).surjective x
    obtain ⟨y', rfl⟩ := (blockZeroEquiv r t).surjective y
    simp only [L, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]
    exact (h g x' y').symm
  have h1 : L.symm (Matrix.single a b (1 : k)) ∈ Submodule.span k (Set.range ρb) := by
    rw [hs]
    exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := L.toLinearMap) h1
  rw [Submodule.map_span] at h2
  have h3 : L.toLinearMap (L.symm (Matrix.single a b (1 : k))) = Matrix.single a b (1 : k) :=
    L.apply_symm_apply _
  rw [h3] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, (hL g).symm⟩

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

theorem one_le_letterBlockLength (R : Ranks) : 1 ≤ R.t := by
  have h := R.rank_add_five_le
  omega

theorem absIrr_of_res (hN : NormAt N r ρ π)
    (hres : Submodule.span (kk N i)
      (Set.range (mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π))) = ⊤) :
    AbsIrr (fun g => ((repX N r g π).toSquareBlock (blk R) 0).map (IsLocalRing.residue (N.O i))) :=
  absIrr_block (r := R.r) (t := R.t) (fun g => (rO N i r π g).map (IsLocalRing.residue (N.O i)))
    (fun g => mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π) g)
    (fun g a b => congrArg (IsLocalRing.residue (N.O i)) (hN.2.2 g a b)) hres

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfInverseLevels
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem universal_general_of_inverse_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG))
    (hUG : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_window D HW F Cm hAdm h9 hH h15 (killWinL_of D HW F Cm hAdm h9 hInv) hUG

end Formalism.MainNotions.UnusedSlot80
end
end

