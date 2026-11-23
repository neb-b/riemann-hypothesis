module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0044
public import Development.AutomorphicArithmetic.OrbitLabellings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLedPart
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.Led

open Formalism.MainNotions.G IsDedekindDomain

theorem X'_le_X'' (s : Scale) (R : Ranks) : s.X' ≤ s.X'' R.n := by
  have hx := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hn : (1 : ℝ) ≤ R.n := by
    have : 1 ≤ R.n := by
      unfold Ranks.n
      have := R.two_le_m
      have := R.m_le_f
      omega
    exact_mod_cast this
  have hX : 0 < s.X' := Real.exp_pos _
  have ha : 0 < s.a := by unfold Scale.a Scale.b; positivity
  have : s.X'' R.n = s.X' * (s.x * R.n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  rw [this]
  exact le_mul_of_one_le_right hX.le (by nlinarith)

variable {D : D7}

theorem cand_of_VV {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : VV X K a b p ≠ ∅) :
    Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) := by
  by_contra h'
  apply h
  unfold VV
  rw [if_neg h']

theorem not_noGain {L : SizeData₂ D} (X : Inst D L) (K : Consts) (Cr : ℝ) (p : ℕ) (h : VV X K (aL L) (bL L) p ≠ ∅) :
    ¬ NoGain X K Cr p := by
  obtain ⟨hc, hs⟩ := cand_of_VV X K _ _ p h
  have hX := X'_le_X'' L.sc D.R
  rintro (⟨-, -, h1 | ⟨h1, i, hi, h2⟩ | ⟨-, h1⟩⟩ | h1 | h1 | h1)
  · exact absurd hc.2.2.2.1 (not_le.2 h1)
  · rw [abs_le] at h2
    exact hc.2.2.2.2 h1 ⟨h1, hc.2.1, i, hi, by linarith [h2.1], by linarith [h2.2]⟩
  · exact absurd hs (not_le.2 h1)
  · linarith [hc.2.1]
  · exact h1 (Or.inl hc.2.2.1)
  · exact HEv.not_isCs (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hc.2.2.2.1) h1

theorem locLe_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.LocLe w 0 A B ↔ ∀ x ∈ A, InLoc w B x := by
  unfold DV.LocLe InLoc
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

theorem inLoc_of_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) (x : V) (h : x ∈ A) : InLoc w A x :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

theorem locEq_of_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (h : ∀ x, InLoc w A x ↔ InLoc w B x) : DV.LocEq w A B :=
  ⟨(locLe_iff w A B).2 fun x hx => (h x).1 (inLoc_of_mem w A x hx),
    (locLe_iff w B A).2 fun x hx => (h x).2 (inLoc_of_mem w B x hx)⟩

theorem exists_sub {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (P : V → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : K) x, w.valuation K a ≤ 1 → P x → P (a • x)) :
    ∃ A : Submodule (𝓞 K) V, (∀ x, x ∈ A ↔ P x) ∧ ∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A → x ∈ A := by
  refine ⟨⟨⟨⟨{x | P x}, fun {x y} => hadd x y⟩, h0⟩, fun c x hx => ?_⟩, fun _ => Iff.rfl, fun t x ht hx => ?_⟩
  · show P (c • x)
    rw [← algebraMap_smul K c x]
    exact hs _ x (w.valuation_le_one c) hx
  · have hv : w.valuation K (algebraMap (𝓞 K) K t) = 1 := (w.valuation_eq_one_iff_notMem).2 ht
    have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have h1 := hs (algebraMap (𝓞 K) K t)⁻¹ (t • x) (by rw [map_inv₀, hv, inv_one]) hx
    rw [← algebraMap_smul K t x, smul_smul, inv_mul_cancel₀ ht0, one_smul] at h1
    exact h1

theorem exists_served {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ∃ A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V, (∀ x, x ∈ A ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ∧
      ∀ (t : 𝓞 D.what₂.LL) x, t ∉ (D.plEq w).asIdeal → t • x ∈ A → x ∈ A := by
  refine exists_sub (D.plEq w) (fun x => c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  · intro a x ha hx
    obtain ⟨o, ho⟩ := (c.embW_val u w hg a).1 ha
    show c.cmp u w hg (D.nuIn u (a • x)) ∈ _
    rw [map_smul, c.cmp_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

theorem exists_atT (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V, (∀ x, x ∈ A ↔ D.nuIn u x ∈ LT.Nlam D u w) ∧
      ∀ (t : 𝓞 D.what₂.LL) x, t ∉ (D.plEq w).asIdeal → t • x ∈ A → x ∈ A := by
  refine exists_sub (D.plEq w) (fun x => D.nuIn u x ∈ LT.Nlam D u w) ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  · intro a x ha hx
    show D.nuIn u (a • x) ∈ _
    rw [map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨a, (D.val_nonneg_iff w a).2 ha⟩ : intW D.what₂.places w) hx

theorem exists_lat {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (hfull : ∀ x : (D.div.Nu u).V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u)
    (hT : ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
      (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
      ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x))
    (hS : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        (∀ x, c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
        ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, c.cmp u w hg (D.nuIn u (n • x)) ∈ NP X Y K u w hg) :
    ∃ N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V,
      (∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ∧
      (∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
        ∀ x, InLoc (D.plEq w) N x ↔ D.nuIn u x ∈ LT.Nlam D u w) ∧
      (∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T → DV.LocLe (D.plEq w) 0 N (DV.MramL D u)) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T →
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅ → DV.LocEq (D.plEq w) N (DV.MramL D u) := by
  classical
  choose A1 hA1 hA1s using exists_served X Y K c u
  choose A2 hA2 hA2s using exists_atT (D := D) u
  let A : D.what₂.places.Pl → Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V := fun w =>
    if hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) then A1 w hg else A2 w
  let S : Set D.what₂.places.Pl := {w | (GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) ∨ D.what₂.places.resChar w = (D.mem u).A.T}
  have hng : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ¬ GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) :=
    fun w h hg => hg.2.2.2.2.2 (h ▸ dvd_rfl)
  have hSf : S.Finite := by
    refine ((GlobalTheory.Refill.finite_le D ⌈L.sc.X'⌉₊).union (GlobalTheory.Refill.finite_over D (D.mem u).A.T)).subset ?_
    rintro w (⟨-, h⟩ | h)
    · left
      have h1 := (cand_of_VV X K _ _ _ h).1.2.1
      have h2 := h1.le.trans (Nat.le_ceil _)
      exact_mod_cast h2
    · exact Or.inr h
  obtain ⟨N, hN1, hN2⟩ := GlobalTheory.EX.Glue.exists_glue D.what₂.LL (D.div.Nu u).V (DV.MramL D u) (D.plEq '' S)
    (fun v => A (D.plEq.symm v)) (hSf.image _) hfull (by
      rintro _ ⟨w, hw, rfl⟩
      simp only [Equiv.symm_apply_apply]
      rcases hw with ⟨hg, hV⟩ | hw
      · have hA : A w = A1 w hg := dif_pos hg
        rw [hA]
        obtain ⟨h1, n, hn, h2⟩ := hS w hg hV
        refine ⟨hA1s w hg, n, hn, fun x hx => (hA1 w hg _).2 (h2 x hx), fun x hx => h1 _ ?_⟩
        exact (hA1 w hg _).1 (Submodule.smul_of_tower_mem _ n hx)
      · have hA : A w = A2 w := dif_neg (hng w hw)
        rw [hA]
        obtain ⟨n, hn, h1, h2⟩ := hT w hw
        exact ⟨hA2s w, n, hn, fun x hx => (hA2 w _).2 (h1 x hx), fun x hx => h2 _ ((hA2 w _).1 hx)⟩)
  have e1 : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg := by
    intro w hg hV x
    have hA : A w = A1 w hg := dif_pos hg
    rw [hN1 _ ⟨w, Or.inl ⟨hg, hV⟩, rfl⟩, Equiv.symm_apply_apply, hA, hA1]
  have e2 : ∀ w, w ∉ S → DV.LocEq (D.plEq w) N (DV.MramL D u) := fun w hw =>
    locEq_of_iff _ _ _ (hN2 _ (fun h => hw ((D.plEq.injective.mem_set_image).1 h)))
  refine ⟨N, e1, fun w hw x => ?_, fun w hw => ?_, fun w hw hV => e2 w ?_⟩
  · have hA : A w = A2 w := dif_neg (hng w hw)
    rw [hN1 _ ⟨w, Or.inr hw, rfl⟩, Equiv.symm_apply_apply, hA, hA2]
  · by_cases h : w ∈ S
    · obtain ⟨hg, hV⟩ := h.resolve_right hw
      exact (locLe_iff _ _ _).2 fun x hx => (hS w hg hV).1 x ((e1 w hg hV x).1 (inLoc_of_mem _ _ _ hx))
    · exact (e2 w h).1
  · rintro (h | h)
    · exact h.2 hV
    · exact hw h

def setLat (L : SizeData₂ D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : SizeData₂ D :=
  { L with
    NuLat := N
    lenMN := fun u w => ((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) }

def setInst {L : SizeData₂ D} (X : Inst D L) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Inst D (setLat L N) :=
  { X with }

theorem exists_ledPart : ∀ (C : FC) (cD ch : ℝ) (s : Scale) (D : D7) (Y : Lay D) (e : Formalism.HC.Frame) (a b : e.A → ℤ) (L0 : SizeData₂ D), Std C → 10 ≤ C.cX.err.g → e = D.R.toFrame → L0.sc = s → WtEq L0 a b → Val C cD ch L0 → HostArith D.host → 1 ≤ s.w'' D.R.n → (∀ u, s.X' ≤ ((D.mem u).A.T : ℝ)) → RecOK s C cD D → LedOK s C cD ch Y a b → ∃ p : LedPart C Y, p.L.sc = s ∧ WtEq p.L a b ∧ Val C cD ch p.L ∧ CanonInst p.ta.Gx := by
  intro C cD ch s D Y e a b L0 hC hg _ hs hW hV0 hA hw _ hR hL
  obtain ⟨L, X, e1, e2, e3, hV, hcan, hep, hkap, hF, hE, hs1, hs2, hfill, hdrop⟩ :=
    GlobalTheory.Refill.exists_refill C cD ch D L0 Y.errX hC hV0 hA (hs ▸ hw) (X'_le_X'' _ _) hR.fin hR.dgam (hL L0 hs hW hV0).1
  have hWL : WtEq L a b := by
    intro t t' h
    rw [e2, e3]
    exact hW t t' h
  obtain ⟨htied, heptie, hS⟩ := (hL L (e1.trans hs) hWL hV).2 X hcan hep hkap hfill
  choose N hN1 hN2 hN3 hN4 using fun u => exists_lat X Y.Gy C.GK Y.cmp u (hR.full u) (hR.atT u) (hS u)
  have hlen : ∀ u w, ∀ l : ℕ, DV.lenLoc (D.plEq w) (N u) (DV.MramL D u) = l →
      (l : ℝ) = ((setLat L N).lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ) := by
    intro u w l h
    have h0 : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    show _ = ((((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) : ℚ) : ℝ) * _
    rw [h, ENat.toNat_natCast]
    push_cast
    rw [div_mul_cancel₀ _ h0]
  have hnu : DV.NuDef D (setLat L N) := by
    refine ⟨hN3, fun u w hT h => hN4 u w hT ?_, hlen⟩
    by_contra hVV
    rcases h with h | h
    · exact not_noGain X C.GK C.Cr _ hVV ((hdrop _ (D.what₂.places.resChar_prime w)).1 h).1
    · exact h (Or.inr (cand_of_VV X C.GK _ _ _ hVV).1.2.2.1)
  obtain ⟨-, -, -, -, f5, f6, -⟩ := hC.1
  refine ⟨⟨setLat L N, ⟨setInst X N, Y.Gy, hs1, hs2, hfill,
      fun w u h1 h2 => LatCmp.lenMN_unserved hnu u w (hN4 u w h2 h1), htied, hdrop⟩, rfl, hnu,
      ⟨Y.vram, hN1, hN2⟩, hep, heptie, hkap, hN4,
      ⟨⟨f5.ge, f6.ge, hg⟩, Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, Y.dgam, hE⟩, hF⟩, e1.trans hs, hWL,
    ⟨hV.ranks, hV.host, hV.hc, hV.dlog, hV.Del_eq, hV.eta_eq, hV.La_eq, hV.bT_le, hV.logFiveDepth_eq, hV.Ct_eq, hV.Cc_eq,
      hV.CGam_eq, hV.secondConstant_eq, hV.words, hV.etaF_eq⟩, hcan⟩

end GlobalTheory.EX.Led

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem exists_levCh_of_levelPrime : LevelPrime → ∀ (eps cs : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → 0 < cs → Std C → ∃ x0 : ℝ, ∀ (cD ch : ℝ) (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, 0 < du u) → 0 < Ds → (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ Lv : LevCh P, Lv.duStar = du ∧ Lv.Dstar = Ds ∧ Lv.GamP = GamS C s P.R := by
  intro hLP eps cs C he he' hcs hC
  obtain ⟨x1, h1⟩ := hLP eps cs he he' hcs
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨max (max x1 x2) (max x3 (max 2 ((1 / cs) ^ 4))), ?_⟩
  intro cD ch s P q1 a b c du Ds hs hx hOK hdu hDs hwin
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4, hx5⟩ := hx
  obtain ⟨-, -, hb, -⟩ := h2 s hs hx2
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, -, hm, -⟩ := h3 s P.R hs hx3 hOK.rank
  have hx0 : 0 < s.x := by linarith
  have hxone : 1 ≤ s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hm2 : (2 : ℝ) ≤ P.R.m := by exact_mod_cast P.R.two_le_m
  have hmf : (P.R.m : ℝ) ≤ P.R.f := by exact_mod_cast P.R.m_le_f
  have hGam : 1 < GamS C s P.R := by
    unfold GamS
    rw [Real.one_lt_exp_iff]
    have : (0 : ℝ) < P.R.f := by linarith
    have : (0 : ℝ) < P.R.m := by linarith
    have : 0 < C.CGam := by linarith
    have : 0 < s.L := by linarith
    positivity

  have hk : (P.R.k : ℝ) ≤ s.x ^ 5 := by
    have : (P.R.k : ℝ) ≤ P.R.r := by exact_mod_cast hkr
    have e : s.x ^ (5 : ℝ) = s.x ^ 5 := by exact_mod_cast Real.rpow_natCast s.x 5
    exact this.trans (hr.trans_eq e)
  have hb41 : s.x ^ 41 ≤ s.b := by
    have e : s.x ^ (41 : ℝ) = s.x ^ 41 := by exact_mod_cast Real.rpow_natCast s.x 41
    rw [e, Real.rpow_one] at hb
    exact (le_mul_of_one_le_right (by positivity) hX1).trans hb
  have hk8 : 2 * (P.R.k : ℝ) ^ 8 ≤ s.b := by
    have h8 : (P.R.k : ℝ) ^ 8 ≤ (s.x ^ 5) ^ 8 := pow_le_pow_left₀ (by positivity) hk 8
    calc 2 * (P.R.k : ℝ) ^ 8 ≤ s.x * (s.x ^ 5) ^ 8 := mul_le_mul hx4 h8 (by positivity) hx0.le
      _ = s.x ^ 41 := by ring
      _ ≤ s.b := hb41
  have hg : ∀ i, (P.H.g i : ℝ) ≤ s.b ^ 9 := fun i => by
    calc (P.H.g i : ℝ) ≤ 2 * ((P.R.k : ℝ) * s.b) ^ 8 := (hOK.val.2.2.2.2.1 i).2
      _ = (2 * (P.R.k : ℝ) ^ 8) * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := mul_le_mul_of_nonneg_right hk8 (by positivity)
      _ = s.b ^ 9 := by ring

  have hcm : 1 ≤ cs * P.R.m := by
    have a1 : 1 / cs ≤ s.x ^ ((1 : ℝ) / 4) := by
      have a0 : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hx5 (by norm_num)
      have e : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) = 1 / cs := by
        have := Real.pow_rpow_inv_natCast (x := 1 / cs) (n := 4) (by positivity) (by norm_num)
        simpa using this
      rwa [e] at a0
    have a2 : s.x ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    have a3 : 1 / cs ≤ P.R.m := a1.trans (a2.trans hm)
    rw [div_le_iff₀ hcs] at a3
    linarith
  have hXL : s.X' ≤ Real.exp (cs * P.R.m * s.L) := by
    unfold Scale.X'
    refine Real.exp_le_exp.2 ?_
    have a1 : s.x ^ (s.eps / 3) ≤ s.L :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    exact a1.trans (le_mul_of_one_le_left (by linarith) hcm)
  have hp : (P.H.pde : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.1 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).1
    · exact h
  have hp' : (P.H.pde' : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.2 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).2
    · exact h
  refine GlobalTheory.Mem.LevelChoice.exists_levCh P du Ds _ hdu hDs hGam fun u => ?_
  have hT0 : 0 < (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
    have : (0 : ℝ) < du u := by exact_mod_cast hdu u
    have : 0 < GamS C s P.R := by linarith
    positivity
  obtain ⟨T, hT, hlo, hhi, hN⟩ := h1 s P.R P.H.condN P.H.d (P.H.g 0) (P.H.g 1) _ hs hx1 hOK.rank hOK.val.modRow
    (P.H.g_prime 0).one_le (P.H.g_prime 1).one_le (hg 0) (hg 1) hT0 (hwin u)
  have hXT : s.X' ≤ T :=
    hXL.trans (((Real.le_log_iff_exp_le hT0).1 (hwin u)).trans hlo)
  have hM : 1 ≤ P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 := by
    have hn : 0 < P.H.QS := P.H.QS_pos
    have hq : 0 < P.H.q := P.H.hyp.1.pos
    have hd : 0 < P.H.d := P.H.hyp.2.1.pos
    have h0 := (P.H.g_prime 0).pos
    have h1 := (P.H.g_prime 1).pos
    exact Nat.succ_le_of_lt (by positivity)
  obtain ⟨⟨π, hK, hπ, hc⟩, -⟩ := GlobalTheory.EX.normOne_host P.R P.H _ T hM hN
  refine ⟨π, T, hT, ?_, ?_, hK, hπ, hc, hlo, hhi⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

end GlobalTheory.EX.OB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver
section
noncomputable section

namespace GlobalTheory.EX.OB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField


set_option maxHeartbeats 1000000 in
theorem exists_sizeData_over : ∀ (eps cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P) (D : D7), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R → Over D P Lv → RecOK s C cD D → HostArith D.host ∧ (∃ L : SizeData₂ D, L.sc = s ∧ WtEq L a b ∧ Val C cD ch L) ∧ D.R = P.R ∧ D.host.TT.image Formalism.HC.Frame.A.val = P.H.TT.image Formalism.HC.Frame.A.val ∧ D.host.T2 = P.H.T2 ∧ D.host.q = P.H.q ∧ D.host.d = P.H.d ∧ D.host.g = P.H.g ∧ D.host.pde = P.H.pde ∧ D.host.pde' = P.H.pde' ∧ P.H.levelPrimes ⊆ D.host.levelPrimes ∧ D.host.u0.val = P.H.u0.val ∧ (∀ l, (G.hP D l).val = (hPH P.H l).val) ∧ ∃ eW : D.what₂.Word ≃ P.Word, ∀ u l, wordBits D u l = if h : l < P.R.k - 2 then c (eW u) ⟨l, h⟩ else false := by
  intro eps cD ch C h0 h1 hC hcD hch
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv D hs hx hP hG hO hR
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hB, rfl⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (Pre.ofCh P Lv sp hT hY hA hV hz).level_split
  refine ⟨⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Finset.subset_union_left, rfl, fun l => rfl, Equiv.refl _, ?_⟩
  · obtain ⟨L, e1, e2, e3, e4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog hR.del hP.ct2
      hP.card hR.etaF (fun u => by
        have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
        rw [e, hG, GamS, Real.log_exp]; rfl)
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) hR.untw
    refine ⟨L, e1, ?_, e4⟩
    intro t t' htt
    have : t.1 = t' := Formalism.HC.Frame.A.val_injective _ htt
    rw [e2, e3]
    subst this
    exact ⟨rfl, rfl⟩
  · intro u l
    unfold wordBits
    by_cases h : l < P.R.k - 2
    · have h' : l < D.R.k - 2 := h
      rw [dite_eq_left h', dite_eq_left h]
      have τ : Tau P.R := tauPl D (false, 0)
      have a1 := D.s.u_letter u τ l h'
      have a2 := hP.code u τ l h
      have a3 := a1.symm.trans a2
      have hpos := D.s.Del_pos
      rw [← hR.del] at a3
      show D.s.letter u ⟨l, h'⟩ = c u ⟨l, h⟩
      have a4 : (if D.s.letter u ⟨l, h'⟩ = true then D.s.Del else 0) = (if c u ⟨l, h⟩ = true then D.s.Del else 0) :=
        sub_right_injective a3
      revert a4
      cases D.s.letter u ⟨l, h'⟩ <;> cases c u ⟨l, h⟩ <;> simp [hpos.ne', hpos.ne]
    · have h' : ¬ l < D.R.k - 2 := h
      rw [dite_eq_right h', dite_eq_right h]

end GlobalTheory.EX.OB

end
end

