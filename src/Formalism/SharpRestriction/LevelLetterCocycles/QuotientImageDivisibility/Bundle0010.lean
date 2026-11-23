module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusSqComparisonLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvROnePow
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem root_Zp {y : F} (hy : (1 + y) ^ (p ^ m) = 1) : Polynomial.aeval y (Zp (O := O) p m) = 0 := by
  simp only [Zp, map_sub, map_pow, map_add (f := _), map_one, Polynomial.aeval_X, hy, sub_self]

theorem evR_congr {x x' : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0)
    (hx' : Polynomial.aeval x' (Zp (O := O) p m) = 0) (h : x = x') (f : PowerSeries O) :
    evR p m hlm hx f = evR p m hlm hx' f := by
  subst h
  rfl

theorem evR_eq_cc {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (hx0 : x = 0)
    (f : PowerSeries O) : evR p m hlm hx f = algebraMap O F (PowerSeries.constantCoeff f) := by
  subst hx0
  obtain ⟨q, hq⟩ : ∃ q, f = Zs p m * q + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
    ⟨_, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
  show evP p m 0 f = _
  rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx f q _ hq]
  conv_rhs => rw [hq]
  rw [← Polynomial.coeff_zero_eq_aeval_zero']
  simp [Zs]

theorem evR_onePow {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (k : ℕ) :
    evR p m hlm hx ((1 + PowerSeries.X) ^ k) = (1 + x) ^ k := by
  have hX : evR p m hlm hx PowerSeries.X = x := by
    show evP p m x PowerSeries.X = x
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx PowerSeries.X 0 Polynomial.X (by simp)]
    simp
  rw [map_pow, map_add (f := _), map_one, hX]

end SlopeTestRemainingChoices

theorem exists_prim {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (N : ℕ) (hN : 0 < N) :
    ∃ ζ : F, IsPrimitiveRoot ζ N := by
  haveI : NeZero (N : F) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N F) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 hN).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusSqBoundOfLocal
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Main

variable (W : LocWach PD LL O v n)

theorem frobenius_sq_bound_at_zero [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB hh bb η' b' S : ℕ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    (hU : ∀ y ∈ W.Nl T₂ (c - 1), W.Q ^ bb • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1 - 1)))
    (hMη : ∀ z ∈ W.Nl T₂ (c - 1 - 1), W.Q ^ η' • W.φD T₂ z ∈ W.N T₂)
    (hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ hh • W.φD T₂ z ∈ W.N T₂)
    (hD0c : ∀ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c, ((PD.p : O) ^ S) • x ∈ Xd W T₂ c kB)
    (hD0c2 : ∀ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
      ((PD.p : O) ^ S) • x ∈ Xd W T₂ (c - 1 - 1) hh)
    (hle : DcrisL PD T₂.ρ (W.emb (c - 1)) ≤ FilCris PD T₂.ρ (b' : ℤ)) {k : ℤ}
    (hGc : ∀ x ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      x ∈ FilCris PD T₂.ρ (b' : ℤ) → (PD.p : LL) ^ k • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    {e pad : ℕ} (hexp : (e : ℤ) + hh = pad + k + bb)
    {y : W.DD T₂} (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) :
    ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e + S + S)) • y - W.map F x) := by
  obtain ⟨y1, hy1, e1⟩ := cmp_of_mem_X W T₂ hs hR h3₂ hM₂ (hD0c y hy)
  obtain ⟨y2, hy2, e2⟩ := cmp_up W T₂ hs h3₂ hmod₂ hU hMη hy1
  obtain ⟨y3, hy3, e3⟩ := cmp_of_mem_X W T₂ hs hR h3₂ hM₂' (hD0c2 y2 hy2)
  have hG := hGc _ (frobenius_sq_mem_lattice_image W T₂ c hy3) (hle (frobenius_sq_comparison_letter W T₂ c hy3))
  refine exists_inI_inPN_pow_smul_sub_map W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hy
    (d1 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y1) (d2 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y2)
    (d3 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y3) (s₁ := S) (s₂ := S) ?_ e2 ?_ hG hexp
  · rw [← e1, cmpD_osmul W T₂ _ (NDl_N W T₂ hy), map_pow, map_natCast]
  · rw [← e3, cmpD_osmul W T₂ _ (NDl_N W T₂ hy2), map_pow, map_natCast]

theorem frobenius_sq_bound_of_local [NeZero n] (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hG : Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaGs W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaDN W) (hD0 : LemmaDN0 W) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.LatticeBoundSix W := by
  intro d T₁ T₂ F b S η m hset
  have hset' := hset
  obtain ⟨hCA, hl, hn, ⟨hDom, hDVR, hFrac⟩, -, hSur, -, -, -, -⟩ := hset'
  haveI := hDom
  haveI := hDVR
  haveI := hFrac
  obtain ⟨hbij, hs, hp2⟩ := hCA
  have hK1 : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hbij
  obtain ⟨-, -, h9₁⟩ := h9 T₁ hSur.1 hs hp2
  obtain ⟨hR, hmod₁⟩ := h9₁ hK1
  obtain ⟨-, -, h9₂⟩ := h9 T₂ hSur.2.1 hs hp2
  obtain ⟨-, hmod₂⟩ := h9₂ hK1
  have h3₁ := h3 T₁ hSur.1
  have h3₂ := h3 T₂ hSur.2.1
  have h5₁ := h5 T₁ (boxM d b S η) (boxH d b S η) hSur.1 (rk_jumpsLet₁ W hset)
  have h5₂ := h5 T₂ (boxM d b S η) (boxH d b S η) hSur.2.1 (rk_jumpsLet₂ W hE hC hQ hset)
  have hl2 : 2 ≤ PD.p := by omega
  have hlam := one_le_lam PD.p (hpar n b S + η) hl2
  have haR := aR_nonneg PD.p (hpar n b S + η) hl2
  have hl1 : (0 : ℝ) < (PD.p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
    linarith
  set σ : ℝ := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (hpar n b S + η) with hσ
  set EGv : ℝ := EG PD.p (hpar n b S) η S with hEGv
  have hσ0 : 0 ≤ σ := by
    rw [hσ, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂]; positivity
  have hEG0 : 0 ≤ EGv := by
    rw [hEGv, EG]
    have : 0 ≤ (3 * (aN PD.p (hpar n b S + η) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by positivity) hl1.le
    linarith
  refine ⟨S + ⌈EGv + σ⌉₊, ?_, ?_⟩
  · unfold B6
    have h1 := Nat.ceil_lt_add_one (add_nonneg hEG0 hσ0)
    push_cast
    linarith
  intro c hc FF _ _ _ _ Fs w hw
  have hcD : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hc1 : ((c - 1).val + d) % 2 = 1 := by
    have := parity_succ hn d (c - 1)
    rw [sub_add_cancel] at this
    omega
  have hc2 : ((c - 1 - 1).val + d) % 2 = 0 := by
    have := parity_succ hn d (c - 1 - 1)
    rw [sub_add_cancel] at this
    omega
  have hc2m : c - 1 - 1 ∈ evens n d := Finset.mem_filter.2 ⟨Finset.mem_univ _, hc2⟩
  have hMc : boxM d b S η c = b c + S := if_pos hcD
  have hMc1 : boxM d b S η (c - 1) = η := if_neg (by omega)
  have hHc1 : boxH d b S η (c - 1) = b (c - 1) + S := if_neg (by omega)
  have hMc2 : boxM d b S η (c - 1 - 1) = b (c - 1 - 1) + S := if_pos hc2
  have hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ (b c + S) • W.φD T₁ z ∈ W.N T₁ := by
    rw [← hMc]; exact h5₁.1 c
  have hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ (b c + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc]; exact h5₂.1 c
  have hU : ∀ y ∈ W.Nl T₂ (c - 1), W.Q ^ (b (c - 1) + S) • y ∈
      Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1 - 1)) := by
    rw [← hHc1]; exact h5₂.2.1 (c - 1)
  have hMη : ∀ z ∈ W.Nl T₂ (c - 1 - 1), W.Q ^ η • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc1]; exact h5₂.1 (c - 1)
  have hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ (b (c - 1 - 1) + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc2]; exact h5₂.1 (c - 1 - 1)

  obtain ⟨E, hE', hGx⟩ := hG d T₁ T₂ F b S η m hset (c - 1) hc1
  have e12 : c - 1 - 2 = c - 1 - 1 - 1 := by ring
  rw [e12] at hGx
  have hEle : (E : ℝ) ≤ EGv := by
    refine hE'.trans ?_
    rw [hEGv, EG]
    have : 3 * aR PD.p (hpar n b S + η) ≤ 3 * (aN PD.p (hpar n b S + η) : ℝ) := by
      have := Nat.le_ceil (aR PD.p (hpar n b S + η)); unfold aN; linarith
    have := div_le_div_of_nonneg_right (a := 3 * aR PD.p (hpar n b S + η) + S + 2 * η)
      (b := 3 * (aN PD.p (hpar n b S + η) : ℝ) + S + 2 * η) (by linarith) hl1.le
    linarith
  set k : ℤ := ⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 PD.p (hpar n b S + η) +
    ((b (c - 1 - 1) + S : ℕ) : ℝ) - (b (c - 1) : ℝ)⌉ with hk
  have hk' : k = ⌈(E : ℝ) + σ⌉ + (((b (c - 1 - 1) + S : ℕ) : ℤ) - (b (c - 1) : ℤ)) := by
    rw [hk, ← Int.ceil_add_intCast]
    congr 1
    rw [hσ]
    push_cast
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂]
    ring
  have hceil : ⌈(E : ℝ) + σ⌉ ≤ ((⌈EGv + σ⌉₊ : ℕ) : ℤ) := by
    have h1 : ⌈(E : ℝ) + σ⌉ ≤ ⌈EGv + σ⌉ := Int.ceil_le_ceil (by linarith)
    have h2 : ((⌈EGv + σ⌉₊ : ℕ) : ℤ) = ⌈EGv + σ⌉ := Int.natCast_ceil_eq_ceil (add_nonneg hEG0 hσ0)
    omega
  set pad : ℕ := (((⌈EGv + σ⌉₊ : ℕ) : ℤ) - ⌈(E : ℝ) + σ⌉).toNat with hpad
  have hpad' : (pad : ℤ) = ((⌈EGv + σ⌉₊ : ℕ) : ℤ) - ⌈(E : ℝ) + σ⌉ := Int.toNat_of_nonneg (by omega)
  have hexp : ((S + ⌈EGv + σ⌉₊ : ℕ) : ℤ) + ((b (c - 1 - 1) + S : ℕ) : ℤ) =
      (pad : ℤ) + k + ((b (c - 1) + S : ℕ) : ℤ) := by
    rw [hpad', hk']
    push_cast
    ring
  haveI := rk_fd_letter₂ W hset (c - 1)
  have hw' : ∀ f, w f ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c := hw
  refine ⟨?_, ?_⟩
  · exact frobenius_sq_bound_at W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hU hMη hM₂'
      (hD d T₁ T₂ F b S η m hset c hc) (hD d T₁ T₂ F b S η m hset (c - 1 - 1) hc2m)
      (rk_corankQ₂ W hE hC hQ hset (c - 1) hc1) hGx hexp FF Fs w hw'
  · intro hm0 f
    have h := frobenius_sq_bound_at_zero W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hU hMη hM₂'
      (hD0 d T₁ T₂ F b S η m hset hm0 c hc) (hD0 d T₁ T₂ F b S η m hset hm0 (c - 1 - 1) hc2m)
      (rk_corank_zero₂ W hE hC hQ hset hm0 (c - 1) hc1) hGx hexp (hw' f)
    rw [show S + ⌈EGv + σ⌉₊ + 2 * S = S + ⌈EGv + σ⌉₊ + S + S by ring]
    exact h

end Main

section Record

theorem steps6_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hG : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaGs ((HW l).W K 1 LL hg))
    (hD : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaDN ((HW l).W K 1 LL hg))
    (hD0 : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaDN0 ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.steps6 D HW F := by
  intro l _ K LL hg _
  have h1 := hA.1 l K 1 LL hg
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  exact frobenius_sq_bound_of_local _ h1.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.1 h11.1 h11.2.1 h11.2.2
    (hG l K LL hg) (hD l K LL hg) (hD0 l K LL hg)

end Record

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Crit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def GamNΔ : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ ζ' : LL) (δ : W.Gam) (a : ℕ),
    IsPrimitiveRoot ζ PD.p → ζ' = ζ ^ a →
    ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ δ : O) - (a : LL)) →
    ∀ (x : ↥(W.N T)) (hx : W.γD T δ (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γD T δ x, hx⟩ k = (algebraMap O LL (W.χΓ δ : O)) ^ k • W.levN T i ζ' x k

def PtTrans : Prop :=
  ∀ ζ ζ' : LL, IsPrimitiveRoot ζ PD.p → IsPrimitiveRoot ζ' PD.p → ∃ δ ∈ W.DelF, ∃ a : ℕ,
    ζ' = ζ ^ a ∧ ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ δ : O) - (a : LL))

theorem gamΔ_of_tie {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamNΔ W := by
  intro T hT i ζ ζ' δ a hζ hζ' hv x hx k
  rw [C.levN_eq, C.levN_eq, C.levB_Γ T hT δ i ζ ζ' 1 a (by rwa [pow_one]) hv hζ' x hx k, map_smul]

theorem isExp_self (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T} (hx : x ∈ W.N T) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x (W.levN T i ζ ⟨x, hx⟩) := by
  have h1 : (1 : LetA O n) • x ∈ W.N T := by rwa [one_smul]
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨x, hx⟩
  refine ⟨⟨m, hm⟩, 1, h1, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
  have e : (⟨(1 : LetA O n) • x, h1⟩ : ↥(W.N T)) = ⟨x, hx⟩ := Subtype.ext (one_smul _ _)
  rw [e, map_one, conv_eq, smulS_one hm]

theorem isExp_smulA (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d) (a' : LetA O n) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (a' • x) (smulS (W.lev i ζ a') d) := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  have hmem : a • (a' • x) ∈ W.N T := by rw [smul_comm]; exact (W.N T).smul_mem a' ha
  refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
  have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
  rw [e1, levN_smulS, funext he]
  show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
  rw [smulS_comm hm]

theorem expCritN_of [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hdom : IsDomain O)
    (hFr : IsFractionRing O LL) (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hΓ : GamNΔ W) (hΔ : PtTrans W) :
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x →
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d →
        ((∃ k : ℕ, Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T) →
          (x ∈ W.N T ↔ ∀ k, d k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k))) := by
  intro T hT i ζ hζ x d hDL hd ⟨k, hk⟩
  have hs : W.s = 1 := hA.2.1
  haveI := hdom
  have hp := p_ne_zero_LL W
  have hFl : Antitone (Formalism.MainNotions.WachCoordinates.FilLev W T i 0) := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0
  constructor
  · intro hx j
    rw [isExp_unique W T i ζ hd (isExp_self W T i ζ hx)]
    exact (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 ⟨x, hx⟩ j
  · intro hcoef
    obtain ⟨w, hw⟩ := hR.2.2.2.2.1
    rw [eat_qp] at hw
    have hQ : W.Q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by rw [MC.Q_eq_q W hs, hw]
    have hQk : W.Q ^ k • x ∈ W.N T := by
      rw [hQ, mul_pow, mul_smul]; exact (W.N T).smul_mem _ hk
    refine memCrit_of W hA hFr h1 h3 h4 h5 hD T hT i x k hQk hDL.1 fun ζ' hζ' j => ?_

    obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
    have hlevQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
    obtain ⟨m, hm⟩ := hd.1
    have hEQ : W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ = smulS ((PowerSeries.X * u) ^ k) d := by
      have := isExp_unique W T i ζ (isExp_self W T i ζ hQk) (isExp_smulA W T i ζ hd (W.Q ^ k))
      rw [this, map_pow, hlevQ]
    have hDgζ : ∀ j : ℤ, W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ j ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 ((k : ℤ) - j) := by
      intro j
      rw [hEQ, mul_pow, smulS_mul hm, smulS_X_pow (LB_smulS hm _)]
      have := Dg_smulS hFl hm (s := 0) (fun j => by simpa using hcoef j) (u ^ k) (j - k)
      simp only at this ⊢
      rwa [show (0 : ℤ) - (j - (k : ℤ)) = (k : ℤ) - j by ring] at this

    obtain ⟨δ, hδ, a, hζa, hv⟩ := hΔ ζ' ζ hζ' hζ
    have hγy : W.γD T δ (W.Q ^ k • x) ∈ W.N T := W.N_Γ T δ _ hQk
    obtain ⟨vv, hvv, hvu⟩ := gam_q W δ
    obtain ⟨vU, rfl⟩ := hvu
    have hγQ : W.γA δ W.Q = W.Q * vU := by rw [MC.Q_eq_q W hs]; exact hvv
    have eγ : W.γD T δ (W.Q ^ k • x) = ((vU : LetA O n) ^ k) • (W.Q ^ k • x) := by
      rw [RL.γD_smulA, map_pow, hDL.2 δ hδ, hγQ, mul_pow, mul_comm, mul_smul]
    have eback : W.Q ^ k • x = (((vU⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k) • W.γD T δ (W.Q ^ k • x) := by
      rw [eγ, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hsub : (⟨W.Q ^ k • x, hQk⟩ : ↥(W.N T)) =
        (((vU⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k) • (⟨W.γD T δ (W.Q ^ k • x), hγy⟩ : ↥(W.N T)) :=
      Subtype.ext eback
    have htr : ∀ j, W.levN T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩ j =
        (algebraMap O LL (W.χΓ δ : O)) ^ j • W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ j :=
      fun j => hΓ T hT i ζ' ζ δ a hζ' hζa hv ⟨W.Q ^ k • x, hQk⟩ hγy j
    have hDg' : ∀ j : ℤ, W.levN T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩ j ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 ((k : ℤ) - j) := fun j => by
      rw [htr j]; exact Submodule.smul_mem _ _ (hDgζ j)
    obtain ⟨m', hm'⟩ := W.levN_supp T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩
    rw [hsub, levN_smulS]
    exact Dg_smulS hFl hm' hDg' _ j

end Crit

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemOfExp
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section E1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_of_exp [NeZero n] [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hMC : MemCrit W) (hT : IsCrys PD T.ρ) (c : ZMod n) (ζ₀ : LL)
    (hTr : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∃ δ ∈ W.DelF, ∃ χ : LL, χ ≠ 0 ∧
      (∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
        W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ₀ x k) ∧
      (∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ₀ f)))
    (u₀ : PowerSeries LL) (hu₀ : W.lev c ζ₀ W.q = X * u₀)
    {w : W.DD T} (hwl : (letE c : LetA O n) • w = w) (hwΔ : ∀ δ ∈ W.DelF, W.γD T δ w = w)
    {K : ℕ} (hK : W.Q ^ K • w ∈ W.N T) {dd : ℤ → T.V ⊗[Qp] BdR} (hdd : ∃ m, LB m dd)
    (he : W.levN T c ζ₀ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u₀) ^ K) dd)
    (hF : ∀ i : ℤ, dd i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)) : w ∈ W.N T := by
  apply hMC T hT c w K hK hwl
  intro ζ hζ j
  obtain ⟨u, hu, hu0⟩ := lev_q_simple W c ζ hζ
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ ⟨W.Q ^ K • w, hK⟩
  obtain ⟨dz, hdzLB, hdz⟩ := div_exists hm u hu0 K
  obtain ⟨δ, hδ, χ, hχ0, hN', hA'⟩ := hTr ζ hζ
  have htr := trans_d W T hs hR c δ hδ ζ ζ₀ χ hχ0 hN' hA' (hwΔ δ hδ) hK u u₀ hu hu₀ hu0
    ⟨_, hdzLB⟩ hdd hdz.symm he
  have hanti := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0
  have hDg : Dg (fun a => Formalism.MainNotions.WachCoordinates.FilLev W T c 0 a) 0 dz := by
    intro i
    rw [htr, zero_sub]
    exact (Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)).smul_mem _ (hF i)
  rw [← hdz, mul_pow, smulS_mul hdzLB, smulS_X_pow (LB_smulS hdzLB _)]
  have h := Dg_smulS hanti hdzLB hDg (u ^ K) (j - K)
  rw [show (0 : ℤ) - (j - K) = (K : ℤ) - j by ring] at h
  exact h

end E1

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

