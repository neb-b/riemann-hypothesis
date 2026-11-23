module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZzPlusSecondProjection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0005
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDensTh
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S.LocalSplitGroups

theorem densTh_of_ga {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : Formalism.L2.SG.CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' :=
  densTh_of Formalism.L2.SG.Pf.density_congruence_holds hG

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhase
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def PhaseAtRep : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)).Finite ∧
    PairVal.phasePair (gS D) L U = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

def PhaseLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U → ∀ p : PlF D,
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E))))

end Steps


variable (D : Formalism.BasicNotions.D7) in
def PsiProdE : Prop :=
  ∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem trace_neg_div (E : Type) [Field E] [NumberField E] (s : E) (g : ℕ) :
    Algebra.trace ℚ E (-(s / (g : E))) = -(Algebra.trace ℚ E s / (g : ℚ)) := by
  have hg : ((g : ℕ) : E) = algebraMap ℚ E (g : ℚ) := by simp
  rw [hg, div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_neg, LinearMap.map_smul, smul_eq_mul]
  ring

theorem phaseAtRep_of (hL : PhaseLoc M δ u u' F0 what₂) (hP : PsiProdE D) : PhaseAtRep M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN
  have hfun : (fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)) = fun p =>
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))) :=
    funext (hL γ w F' L U hrel hgen hN)
  rw [hfun]
  obtain ⟨hf, hp⟩ := hP (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))
  refine ⟨hf, ?_⟩
  rw [hp, trace_neg_div, map_add (f := _)]
  unfold PairVal.phasePair PairVal.psiInf
  rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseProd_of (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hW : PairVal.PhaseWellDef D u u' F0 what₂) (hR : PhaseAtRep M δ u u' F0 what₂) : PhaseProd M δ u u' F0 what₂ := by
  intro γ w hγ
  have hrel := PCount.eligRel_holds γ w hγ
  have hex := normRepElig_of hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  have hpt : ptT γ = hex.choose.1 := by
    unfold ptT nrep
    rw [dite_eq_left hex]
  have hw : hex.choose.1 = w := hpt.symm.trans (FCount.ptT_eq hN hrows hγ hrel)
  have h0 : PairVal.NormRep γ w hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 := by
    have := hex.choose_spec
    rw [hw] at this
    exact this
  obtain ⟨hf, hp⟩ := hR γ w _ _ _ hrel hγ.1.1 h0
  have hyT : ∀ p, yT M δ u u' F0 what₂ γ p =
      CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) hex.choose.2.1) * sgnP p := fun p => by
    unfold yT; rw [hz]
  simp only [hyT]
  refine ⟨hf, ?_⟩
  refine Eq.trans ?_ hp
  have hex1 : ∃ x : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) × PairVal.MatR D × PairVal.MatR D,
      PairVal.NormRep γ w x.1 x.2.1 x.2.2 := ⟨(hex.choose.2.1, hex.choose.2.2.1, hex.choose.2.2.2), h0⟩
  unfold PairVal.phaseAt
  rw [dite_eq_left hex1]
  exact hW γ w hrel _ _ _ _ _ _ hex1.choose_spec h0

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefXiTyped
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section QMul

variable {K : Type} [Field K] [ValuativeRel K] (q : K)

def QM (x : K) : Prop := ∃ t ∈ 𝒪[K], x = q * t

theorem qm_zero : QM q 0 := ⟨0, zero_mem _, by ring⟩

theorem qm_add {x y : K} (hx : QM q x) (hy : QM q y) : QM q (x + y) := by
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨t', ht', rfl⟩ := hy
  exact ⟨t + t', add_mem ht ht', by ring⟩

theorem qm_neg {x : K} (hx : QM q x) : QM q (-x) := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨-t, neg_mem ht, by ring⟩

theorem qm_mul_int {x y : K} (hx : QM q x) (hy : y ∈ 𝒪[K]) : QM q (x * y) := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t * y, mul_mem ht hy, by ring⟩

theorem qm_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, QM q (f i)) : QM q (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (QM q) (fun _ _ => qm_add q) (qm_zero q) h

theorem qm_inv_entry {R : Type} [CommRing R] (φ : R →+* K) (hφ : ∀ x, φ x ∈ 𝒪[K]) {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) R) (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (hc : ∀ a c, a < c → QM q (φ (ξ a c))) {k b : Fin n} (hkb : k < b) : QM q (φ (ξ⁻¹ k b)) := by
  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]
    simp [h2]
  have hmul : ξ * ξ⁻¹ = 1 := Matrix.mul_nonsing_inv ξ (by rw [hdet]; exact isUnit_one)
  have e1 := congrFun (congrFun hmul k) b
  rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hkb), ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    h2, one_mul] at e1
  have e2 : ξ⁻¹ k b = -∑ c ∈ Finset.univ.erase k, ξ k c * ξ⁻¹ c b := by
    linear_combination e1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_neg, map_sum]
  refine qm_neg q (qm_sum q _ _ fun c hc' => ?_)
  rw [map_mul]
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc') with hlt | hgt
  · rw [h1 k c hlt, map_zero, zero_mul]
    exact qm_zero q
  · exact qm_mul_int q (hc k c hgt) (hφ _)

end QMul

section XiPf

variable {D : Formalism.BasicNotions.D7}


set_option maxHeartbeats 1000000 in
theorem xiTyped_of_ctx {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hctx : CtxP u u' F0 what₂) : XiTyped Zd u u' F0 what₂ := by
  intro γ w hγ p g hs k b hkb
  have hN := normRepExists_ctx hctx
  have hrows := hctx.2.1
  have hex := Formalism.L2.SG.Pf.Coef.normRepElig_of hN γ w hγ
  have hrep : repF γ = hex.choose.2.1 := by
    unfold repF nrep
    rw [dite_eq_left hex]
  have hA1 : AdmWit γ.lam (gS D) (lf D F0) (repF γ) 1 := by
    rw [hrep]
    exact hex.choose_spec.2.1
  have hadm : IsAdmissible γ.lam (gS D) (lf D F0) (repF γ) := ⟨1, hA1⟩
  have hW : AdmWit γ.lam (gS D) (lf D F0) (repF γ) (admXi D γ.lam (lf D F0) (repF γ)) := by
    unfold admXi
    rw [dite_eq_left hadm]
    exact hadm.choose_spec
  generalize admXi D γ.lam (lf D F0) (repF γ) = ξ at hW ⊢

  obtain ⟨hq, hell⟩ := PI.CntNotIntW.split_ell Zd.δ Zd.agree p g hs
  obtain ⟨kk, hk⟩ := PI.CntNotIntW.gS_split p hell
  have hl0 : Loc.resChar p ≠ 0 := (D.s.atP p).ellPrime.out.ne_zero
  have hl : valuation (D.s.atP p).Fp ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) < 1 := by
    rw [← hq]; exact PI.CntNotIntW.val_q_lt p g
  have hg : ((gS D : ℕ) : (D.s.atP p).Fp) =
      (g.q : (D.s.atP p).Fp) ^ 1 * ((kk : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) := by
    rw [hk, hq]; push_cast; ring
  have hgv : valuation (D.s.atP p).Fp ((gS D : ℕ) : (D.s.atP p).Fp) < 1 := by
    rw [hg, pow_one, Valuation.map_mul]
    exact mul_lt_of_lt_of_le_one (PI.CntNotIntW.val_q_lt p g)
      ((Valuation.mem_integer_iff _ _).1 (kk : 𝒪[(D.s.atP p).Fp]).2)
  have hgP : ∀ σ : D.host.E →+* (D.s.atP p).Fp,
      ((gS D : ℕ) : 𝓞 D.host.E) ∈ (PI.CntNotIntW.vPrime σ (Loc.resChar p) hl0 hl).asIdeal := fun σ => by
    show _ ∈ PI.CntNotIntW.vIdeal σ
    rw [PI.CntNotIntW.mem_vIdeal]
    simpa using hgv

  obtain ⟨-, ⟨-, -, -, hFC⟩, -⟩ := hrows.1 γ.lam γ.mem
  have hlast : ∀ c : Fin (D.R.rS + 1), ((ξ (Fin.last D.R.rS) c : 𝓞 D.host.E) : D.host.E) -
      (if Fin.last D.R.rS = c then 1 else 0) = 0 := by
    intro c
    by_cases hc : Fin.last D.R.rS = c
    · rw [if_pos hc, ← hc, hW.2.1]; simp
    · rw [if_neg hc, hW.1 _ _ (lt_of_le_of_ne (Fin.le_last c) (Ne.symm hc))]; simp

  have hcoef : ∀ σ : D.host.E →+* (D.s.atP p).Fp, ∀ a c : Fin (D.R.rS + 1), a < c →
      QM (g.q : (D.s.atP p).Fp) (σ ((ξ a c : 𝓞 D.host.E) : D.host.E)) := by
    intro σ a c hac
    have hy : ModG (VS D) γ.lam (gS D) (frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c) := by
      intro Q hQ
      have h1 := hA1.2.2 c Q hQ
      have h2 := hW.2.2 c Q hQ
      rw [PI.CntNotIntW.frameAct_one] at h1
      have h3 := Submodule.sub_mem _ h1 h2
      convert h3 using 1
      abel

    have hyexp : frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c =
        ∑ i : Fin D.R.rS, (((ξ (Fin.castSucc i) c : 𝓞 D.host.E) : D.host.E) -
          (if Fin.castSucc i = c then 1 else 0)) • F0.e i := by
      have e1 : frame (lf D F0) c = ∑ a : Fin (D.R.rS + 1), (if a = c then (1 : D.host.E) else 0) • F0.fvec a := by
        rw [Finset.sum_eq_single c]
        · simp
        · intro a _ ha; simp [ha]
        · simp
      unfold frameAct
      rw [e1, ← Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
      simp only [← sub_smul]
      rw [hlast c, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [FlagG.fvec, Fin.snoc_castSucc]
    set P := PI.CntNotIntW.vPrime σ (Loc.resChar p) hl0 hl with hPdef
    obtain ⟨s, hsP, l, hlΛ, hsl⟩ := PI.CntNotIntW.modG_at D γ.lam hy P (hgP σ)

    have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have : (gS D : ℕ) ≠ 0 := by
        unfold Lat.gS
        exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact_mod_cast this
    have hlX : l ∈ (lf D F0).fl.X := by
      have hl2 : l = (((gS D : ℕ) : D.host.E)⁻¹ * (s : D.host.E)) •
          (frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c) := by
        rw [mul_smul, hsl, ← mul_smul, inv_mul_cancel₀ hgE, one_smul]
      rw [hl2, hyexp]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      exact Submodule.subset_span ⟨i, rfl⟩
    have hlXL : l ∈ XLam γ.lam (lf D F0) := ⟨hlΛ, hlX⟩
    obtain ⟨cc, -, hc1, hloc⟩ := hFC.1 P
    have hcc : ∀ i, cc i = 1 := hc1 (hgP σ)
    have hlloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam γ.lam (lf D F0)) := by
      show ∃ s ∈ P.asIdeal.primeCompl, s • l ∈ XLam γ.lam (lf D F0)
      exact ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hlXL⟩
    rw [hloc] at hlloc
    obtain ⟨t, htP, htl⟩ := hlloc
    simp only [hcc, one_smul] at htl
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).1 htl

    have hcomb : ∑ i : Fin D.R.rS, ((t : D.host.E) * s * (((ξ (Fin.castSucc i) c : 𝓞 D.host.E) : D.host.E) -
        (if Fin.castSucc i = c then 1 else 0)) - ((gS D : ℕ) : D.host.E) * (o i : D.host.E)) • F0.e i = 0 := by
      have hto : (t : D.host.E) • l = ∑ i, (o i : D.host.E) • F0.e i := by
        rw [show (t : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, algebraMap_smul, ← ho]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (o i : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (o i) from rfl, algebraMap_smul]
      have e2 : (t : D.host.E) • ((s : D.host.E) • (frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c)) =
          ((gS D : ℕ) : D.host.E) • ∑ i, (o i : D.host.E) • F0.e i := by
        rw [hsl, smul_comm, hto]
      rw [hyexp, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at e2
      simp only [smul_smul] at e2
      rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ _, Finset.sum_sub_distrib, sub_eq_zero]
      convert e2 using 2 <;> ring_nf
    have hz := (Fintype.linearIndependent_iff.1 F0.e_indep) _ hcomb
    have ha : a ≠ Fin.last D.R.rS := fun h => by
      rw [h] at hac; exact absurd hac (not_lt.2 (Fin.le_last c))
    obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.rS, Fin.castSucc i = a := ⟨a.castPred ha, Fin.castSucc_castPred a ha⟩
    have hzi := hz i
    rw [if_neg (ne_of_lt hac), sub_zero, sub_eq_zero] at hzi
    have hv : valuation (D.s.atP p).Fp (σ ((t : D.host.E) * s)) = 1 := by
      rw [map_mul, Valuation.map_mul, PI.CntNotIntW.val_one_of_not_mem σ _ hl0 hl t htP,
        PI.CntNotIntW.val_one_of_not_mem σ _ hl0 hl s hsP, one_mul]
    obtain ⟨t', ht'⟩ := PI.CntNotIntW.div_q σ g.q kk 1 (gS D) ((t : D.host.E) * s) _ (o i) hv hg hzi
    exact ⟨t', t'.2, by rw [ht', pow_one]⟩

  have hcoe : ∀ z : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E z = (z : D.host.E) := fun z => rfl
  have hinv : ∀ σ : D.host.E →+* (D.s.atP p).Fp,
      QM (g.q : (D.s.atP p).Fp) (σ ((ξ⁻¹ k b : 𝓞 D.host.E) : D.host.E)) := by
    intro σ
    obtain ⟨φ, hφ⟩ : ∃ φ : 𝓞 D.host.E →+* (D.s.atP p).Fp, ∀ o : 𝓞 D.host.E, φ o = σ (o : D.host.E) :=
      ⟨σ.comp (algebraMap (𝓞 D.host.E) D.host.E), fun o => rfl⟩
    rw [← hφ]
    exact qm_inv_entry _ φ (fun o => by rw [hφ]; exact PI.CntNotIntW.sig_int σ o) ξ hW.1 hW.2.1
      (fun a c hac => by rw [hφ]; exact hcoef σ a c hac) hkb
  obtain ⟨σ1, hσ1⟩ : ∃ σ1 : D.host.E →+* (D.s.atP p).Fp, ∀ y, σ1 y = (g.e ((D.s.atP p).ιE y)).1 :=
    ⟨(RingHom.fst _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE), fun y => rfl⟩
  obtain ⟨σ2, hσ2⟩ : ∃ σ2 : D.host.E →+* (D.s.atP p).Fp, ∀ y, σ2 y = (g.e ((D.s.atP p).ιE y)).2 :=
    ⟨(RingHom.snd _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE), fun y => rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, hxe⟩ := hinv σ1
    refine ⟨x, hx, ?_⟩
    rw [adeleInfiniteComponent_apply, Matrix.map_apply, hcoe, ← hσ1]
    exact hxe
  · obtain ⟨x, hx, hxe⟩ := hinv σ2
    refine ⟨x, hx, ?_⟩
    rw [adele_ext_components, Matrix.map_apply, hcoe, ← hσ2]
    exact hxe

theorem tau_one_holds {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} : TauOneReduction Zd u u' F0 what₂ :=
  tauOne_of_typed xiTyped_of_ctx

end XiPf

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBeta
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

def TermHyp (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
    IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

end BwdBetaCut

open BwdBetaCut

variable (u u' F0 what₂)

def BwdBeta' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        TermHyp (F0 := F0) Λ₂ F'₂ →
        ∃ x : Carrier (PD D γ.lam (lf D F0) u'), TermDef.mk _ _ _ x = γ.cls ∧ Gval (lf D F0) x.1 ≠ 0 ∧
          ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
            IsPair γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β (gS D) ∧
            Lat.s0 γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β D.R.k = 1 ∧
            IsScalar γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β

def RepG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ x : Carrier (PD D γ.lam (lf D F0) u'), x.1 = repF γ ∧ TermDef.mk _ _ _ x = γ.cls ∧ Gval (lf D F0) x.1 ≠ 0

def BetaCore : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        TermHyp (F0 := F0) Λ₂ F'₂ → PD D γ.lam (lf D F0) u' (repF γ) → Gval (lf D F0) (repF γ) ≠ 0 →
        ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
          IsPair γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β (gS D) ∧
          Hp γ.lam (lf D F0) (repF γ) ≤ Th γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β ∧
          IsScalar γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β

variable {u u' F0 what₂}

theorem bwdBeta'_of_core (hR : RepG u u' F0 what₂) (hB : BetaCore Zd u u' F0 what₂) : BwdBeta' Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT
  obtain ⟨x, hx, hmk, hG⟩ := hR hC γ Z hZ
  have hPD : PD D γ.lam (lf D F0) u' (repF γ) := hx ▸ x.2
  have hG' : Gval (lf D F0) (repF γ) ≠ 0 := hx ▸ hG
  obtain ⟨β, hP, hle, hsc⟩ := hB hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT hPD hG'
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hfix := hrow.2.1
  refine ⟨x, hmk, hG, β, hx ▸ hP, ?_, hx ▸ hsc⟩
  rw [hx]
  refine (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k (Corank.finrank_VS D) γ.lam hrow.1.1 (lf D F0) (repF γ) _ β
    hfix.2.2.1 hPD.1 hG').2 ?_
  exact le_antisymm (PI.PairCorankPos.W.Th_le_Hp _ _ _ _ _) hle

theorem bwdPair_of'' (h2 : BwdTerm' Zd u u' F0 what₂) (h4 : BwdBeta' Zd u u' F0 what₂) : BwdPair Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg
  have hT := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  obtain ⟨hT1, hA, hG, hO⟩ := hT
  have hE := mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT1 hA hG hO hS.1
  obtain ⟨x, hx, hGx, β, hP, hs0, hsc⟩ := h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg ⟨hT1, hA, hG, hO⟩
  have hPD : PD D γ.lam (lf D F0) u' (mapL n (isom_of_N0F hn) (liftF F'₂)) := ⟨hE.1.1, hE.1.2.1, hE.2.2.2.1⟩
  let pr : Corank.Pair D u u' F0 what₂ :=
    ⟨γ.lam, γ.mem, x, ⟨_, hPD⟩, hGx, hE.1.2.2, β, hP⟩
  refine ⟨⟨γ.lam, γ.mem, TermDef.mk _ _ _ ⟨_, hPD⟩⟩, ⟨pr, ?_, rfl, hs0, hsc⟩, hPD, rfl⟩
  exact congrArg (fun c => (⟨γ.lam, γ.mem, c⟩ : TermDef.Term D u u' F0 what₂)) hx

theorem bwdC_of''' (hC : CtxP u u' F0 what₂) (h1 : BwdN Zd u u' F0 what₂) (h2 : BwdTerm' Zd u u' F0 what₂)
    (h4 : BwdBeta' Zd u u' F0 what₂) : BwdC Zd u u' F0 what₂ := by
  intro γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨n, hn, himg⟩ := h1 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨hT, hA, hG, hO⟩ := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  refine ⟨mapL n (isom_of_N0F hn) (liftF F'₂),
    ⟨?_, bwdPair_of'' Zd h2 h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg⟩, n, hn, ⟨fun a => rfl, rfl⟩, himg⟩
  exact mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT hA hG hO hS.1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

