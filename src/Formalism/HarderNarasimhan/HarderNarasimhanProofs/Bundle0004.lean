module

public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0002
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0003
public import Formalism.HarderNarasimhan.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.StatementPl

@[expose] public section

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
section
open Module Submodule

noncomputable section

namespace Formalism.HN

theorem muChar_zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ A, ρ x = y := hy
  exact (⟨x, h hx, rfl⟩ : ∃ x' ∈ B, ρ x' = ρ x)

universe u v w in
theorem muChar_of (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) (h3 : RatioMax.{u, v, w}) :
    MuChar.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL hL0
  obtain ⟨-, P2, P3, P4, P5, P6, -, P8⟩ := h2 R V E ρ L hL
  have hdisc : DiscreteTopology (zl ρ L) := hL.2
  have hrk0 : rk ρ (⊥ : Submodule R V) = 0 := (P4 ⊥ bot_le).2 rfl
  have hrkpos : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → (0 : ℝ) < rk ρ N := by
    intro N hN hN0
    have : rk ρ N ≠ 0 := fun h => hN0 ((P4 N hN).1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hslope : ∀ N : Submodule R V, slope ρ N = deg ρ N / rk ρ N := fun N => rfl
  have hzlne : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → zl ρ N ≠ ⊥ := by
    intro N hN hN0 h
    apply hN0
    apply (P4 N hN).1
    show Formalism.F.rk (zl ρ N) = 0
    rw [h]
    simp [Formalism.F.rk]
  obtain ⟨c, hc⟩ := Formalism.F.slopesBdd E (zl ρ L) hdisc
  have hsc : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → slope ρ N ≤ c := fun N hN hN0 =>
    hc ⟨zl ρ N, muChar_zl_mono ρ hN, hzlne N hN hN0, rfl⟩
  have hdegbd : ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ max c 0 * rk ρ L := by
    intro N hN
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [P5]
      exact mul_nonneg (le_max_right c 0) (Nat.cast_nonneg _)
    · have hpos := hrkpos N hN hN0
      have hs := hsc N hN hN0
      rw [hslope, div_le_iff₀ hpos] at hs
      have hr : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (P2 N L hN le_rfl).1
      have e1 : c * (rk ρ N : ℝ) ≤ max c 0 * rk ρ N :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg _)
      have e2 : max c 0 * (rk ρ N : ℝ) ≤ max c 0 * rk ρ L :=
        mul_le_mul_of_nonneg_left hr (le_max_right c 0)
      linarith

  set T : Set ℝ := {t | ∃ N : Submodule R V, N ≤ L ∧ N ≠ ⊥ ∧ slope ρ N = t} with hT
  have hmuMax : muMax ρ L = sSup T := rfl
  have hTne : T.Nonempty := ⟨_, L, le_rfl, hL0, rfl⟩
  have hTbdd : BddAbove T := by
    refine ⟨c, ?_⟩
    rintro t ⟨N, hN, hN0, rfl⟩
    exact hsc N hN hN0
  have part1 : ∀ θ : ℝ, muMax ρ L ≤ θ ↔
      ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N := by
    intro θ
    rw [hmuMax]
    constructor
    · intro h N hN
      by_cases hN0 : N = ⊥
      · subst hN0
        rw [P5, hrk0]
        simp
      · have h1 : slope ρ N ≤ θ := (le_csSup hTbdd ⟨N, hN, hN0, rfl⟩).trans h
        rw [hslope, div_le_iff₀ (hrkpos N hN hN0)] at h1
        exact h1
    · intro h
      refine csSup_le hTne ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      rw [hslope, div_le_iff₀ (hrkpos N hN hN0)]
      exact h N hN

  have hsatlt : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L → rk ρ S < rk ρ L := by
    intro S hS hSL
    have hle := (P8 S hS).2.1
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (P3 S L hS hS.1 le_rfl h.symm).symm hSL
  have hdpos : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L →
      (1 : ℝ) ≤ (rk ρ L : ℝ) - rk ρ S := by
    intro S hS hSL
    have h' : rk ρ S + 1 ≤ rk ρ L := hsatlt S hS hSL
    have : (rk ρ S : ℝ) + 1 ≤ rk ρ L := by exact_mod_cast h'
    linarith
  have hqslope : ∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ S)) =
        (deg ρ L - deg ρ S) / ((rk ρ L : ℝ) - rk ρ S) := by
    intro S hS
    obtain ⟨hr, hle, hd⟩ := P8 S hS
    show Formalism.F.deg _ / (Formalism.F.rk _ : ℝ) = _
    rw [hr, hd, Nat.cast_sub hle]
  set U : Set ℝ := {t | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧
    Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t} with hU
  have hmuMin : muMin ρ L = sInf U := rfl
  have hUne : U.Nonempty := ⟨_, ⊥, P6, hL0.symm, rfl⟩
  have hUbdd : BddBelow U := by
    refine ⟨min (deg ρ L - max c 0 * rk ρ L) 0, ?_⟩
    rintro t ⟨N, hN, hNL, rfl⟩
    rw [hqslope N hN]
    have hd := hdpos N hN hNL
    rw [le_div_iff₀ (by linarith)]
    have hb := hdegbd N hN.1
    have m1 := min_le_left (deg ρ L - max c 0 * rk ρ L) 0
    have m2 := min_le_right (deg ρ L - max c 0 * rk ρ L) 0
    have m3 := mul_le_mul_of_nonpos_left hd m2
    linarith
  have part2 : ∀ θ : ℝ, θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N := by
    intro θ
    rw [hmuMin]
    constructor
    · intro h N hN
      obtain ⟨N', hNN', hN'L, hzl⟩ := h1 R V E ρ L N hL hN
      obtain ⟨hsat, -, hrkeq⟩ :=
        Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc (muChar_zl_mono ρ hN)
      have hN'sat : IsSat ρ L N' := ⟨hN'L, by rw [hzl]; exact hsat⟩
      have hrk' : rk ρ N' = rk ρ N := by
        show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
        rw [hzl]
        exact hrkeq
      have hdeg' : deg ρ N ≤ deg ρ N' := (P2 N N' hNN' hN'L).2 hrk'.symm
      by_cases hN'L' : N' = L
      · have hr : rk ρ N = rk ρ L := by rw [← hrk', hN'L']
        have hdg : deg ρ N ≤ deg ρ L := hN'L' ▸ hdeg'
        rw [hr, sub_self, mul_zero]
        linarith
      · have ht := h.trans (csInf_le hUbdd ⟨N', hN'sat, hN'L', rfl⟩)
        rw [hqslope N' hN'sat] at ht
        have hd := hdpos N' hN'sat hN'L'
        rw [le_div_iff₀ (by linarith)] at ht
        rw [← hrk']
        linarith
    · intro h
      refine le_csInf hUne ?_
      rintro t ⟨N, hN, hNL, rfl⟩
      rw [hqslope N hN]
      have hd := hdpos N hN hNL
      rw [le_div_iff₀ (by linarith)]
      exact h N hN.1
  have part3 : ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ ⊥ ∧ slope ρ N = muMax ρ L := by
    obtain ⟨N, hbN, hNsat, hmax⟩ := h3 R V E ρ L ⊥ hL P6 hL0.symm
    have hN0 : N ≠ ⊥ := hbN.ne'
    refine ⟨N, hNsat, hN0, ?_⟩
    rw [hmuMax]
    refine (IsGreatest.csSup_eq ⟨(show slope ρ N ∈ T from ⟨N, hNsat.1, hN0, rfl⟩), ?_⟩).symm
    rintro t ⟨N', hN', hN'0, rfl⟩
    have hm := hmax N' (bot_lt_iff_ne_bot.2 hN'0) hN'
    rw [P5, hrk0] at hm
    simp only [sub_zero, Nat.cast_zero] at hm
    rw [hslope, hslope, div_le_div_iff₀ (hrkpos N' hN' hN'0) (hrkpos N hNsat.1 hN0)]
    linarith
  have hquotbot : Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) = slope ρ L := by
    rw [hqslope ⊥ P6, P5, hrk0, hslope]
    simp
  refine ⟨part1, part2, part3, ?_, ?_⟩
  · rw [hmuMin, ← hquotbot]
    exact csInf_le hUbdd
      (show Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) ∈ U from ⟨⊥, P6, hL0.symm, rfl⟩)
  · rw [hmuMax]
    exact le_csSup hTbdd (show slope ρ L ∈ T from ⟨L, le_rfl, hL0, rfl⟩)

theorem slope_characterization : MuChar := muChar_of real_saturation_property saturation_basic_properties maximal_slope_ratio

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
section
open Module NumberField

noncomputable section

namespace Formalism.HN

def rscMap {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (P × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun p => (c p.1)⁻¹ • LinearMap.proj p) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (P × ι × Fin 2 → ℝ)).toLinearMap

theorem rscMap_apply {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) (p : P × ι × Fin 2) :
    rscMap c x p = (c p.1)⁻¹ * x p := by
  simp [rscMap, LinearMap.pi_apply]

theorem mem_placePart_iff {P ι : Type*} [Fintype P] [Fintype ι] (v : P)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) :
    x ∈ placePart (ι := ι) v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → x p = 0 := by
  simp [placePart, Submodule.mem_iInf]

theorem inner_eq_sum_pl {P ι : Type*} [Fintype P] [Fintype ι]
    (x y : EuclideanSpace ℝ (P × ι × Fin 2)) :
    inner ℝ x y = ∑ p, x p * y p := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [mul_comm]

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem realize_smul_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (c : InfinitePlace K → ℝ) (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v) (x : V) :
    Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x = rscMap c (Formalism.HermitianLatticesTheory.realize b X x) := by
  have hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b (fun w => ((c w : ℂ)) • X w) v x =
      ((c v : ℂ))⁻¹ • Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro v
    have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
    have hi : ((c v : ℂ) • X v)⁻¹ = ((c v : ℂ))⁻¹ • (X v)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.nonsing_inv_mul _ (hX v)]
    simp only [Formalism.HermitianLatticesTheory.fcoord, hi]
    first
      | exact Matrix.smul_mulVec _ _ _
      | exact Matrix.smul_mulVec_assoc _ _ _
      | (funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
  ext p
  rw [rscMap_apply]
  by_cases h : p.2.2 = 0
  · have e1 : (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x) p =
        (Formalism.HermitianLatticesTheory.fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x p.2.1).re := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    have e2 : (Formalism.HermitianLatticesTheory.realize b X x) p = (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    rw [e1, e2, hf]
    simp [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  · have e1 : (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x) p =
        (Formalism.HermitianLatticesTheory.fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x p.2.1).im := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    have e2 : (Formalism.HermitianLatticesTheory.realize b X x) p = (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    rw [e1, e2, hf]
    simp [← Complex.ofReal_inv, Complex.im_ofReal_mul]
end

theorem rescaleCovol_of (h1 : PlaceSplit) (h2 : GramBlock) (h3 : PlLat) : RescaleCovol := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc N hN
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    have hc0 : (c v : ℂ) ≠ 0 := by exact_mod_cast (hc v).ne'
    rw [Matrix.det_smul]
    exact (hc0.isUnit.pow _).mul (hX v)
  have hρ' := realize_smul_eq b X c hX hc
  have hinj : Function.Injective ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    intro x y hxy
    ext p
    have := congrArg (fun z => z p) hxy
    simp only [LinearMap.restrictScalars_apply, rscMap_apply] at this
    exact mul_left_cancel₀ (inv_ne_zero (hc p.1).ne') this
  have hL' : zl (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N =
      (zl (Formalism.HermitianLatticesTheory.realize b X) N).map ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    ext y
    simp only [zl, Submodule.mem_map, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, (hρ' x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, hρ' x⟩
  obtain ⟨⟨_, hLd⟩, -, -⟩ := h3 K V ι b X hX N hN
  obtain ⟨⟨_, hL'd⟩, -, -⟩ := h3 K V ι b _ hX' N hN
  rw [hL'] at hL'd ⊢
  have := hLd
  have := hL'd
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  let L := zl (Formalism.HermitianLatticesTheory.realize b X) N
  let bL := Module.finBasis ℤ L
  let e := Submodule.equivMapOfInjective _ hinj L
  let bM := bL.map e
  have hbM : (fun i => (bM i : E)) = fun i => rscMap (ι := ι) c (bL i) := by
    funext i; simp [bM, e]
  rw [Formalism.F.covolEqGram _ _ _ bM, Formalism.F.covolEqGram _ L _ bL, hbM]
  have horth : ∀ v w : InfinitePlace K, v ≠ w → ∀ x ∈ placePart (ι := ι) v,
      ∀ y ∈ placePart (ι := ι) w, inner ℝ x y = 0 := by
    intro v w hvw x hx y hy
    rw [inner_eq_sum_pl]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p.1 = v
    · rw [(mem_placePart_iff w y).1 hy p (by rw [hp]; exact hvw), mul_zero]
    · rw [(mem_placePart_iff v x).1 hx p hp, zero_mul]
  have hTinner : ∀ v, ∀ x ∈ placePart (ι := ι) v, ∀ y ∈ placePart (ι := ι) v,
      inner ℝ (rscMap c x) (rscMap c y) = (c v)⁻¹ ^ 2 * inner ℝ x y := by
    intro v x hx y hy
    rw [inner_eq_sum_pl, inner_eq_sum_pl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rscMap_apply, rscMap_apply]
    by_cases hp : p.1 = v
    · rw [hp]; ring
    · rw [(mem_placePart_iff v x).1 hx p hp]; ring
  have hTmap : ∀ v, ∀ x ∈ placePart (ι := ι) v,
      rscMap c x ∈ placePart (ι := ι) v ∧ ‖rscMap c x‖ ≤ (c v)⁻¹ * ‖x‖ := by
    intro v x hx
    refine ⟨(mem_placePart_iff v _).2 fun p hp => ?_, le_of_eq ?_⟩
    · rw [rscMap_apply, (mem_placePart_iff v x).1 hx p hp, mul_zero]
    · have h := hTinner v x hx x hx
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← mul_pow] at h
      exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.2 (hc v).le) (norm_nonneg _))
        two_ne_zero).1 h
  have hspZ : Submodule.span ℤ (Set.range fun i => (bL i : E)) = L := by
    have := congrArg (Submodule.map L.subtype) bL.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range fun i => (bL i : E)) = Submodule.span ℝ (L : Set E) := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (bL i).2)
    · refine Submodule.span_le.2 fun x hx => ?_
      rw [← hspZ] at hx
      exact Submodule.span_le_restrictScalars ℤ ℝ _ hx
  classical
  obtain ⟨hsplit, hdim⟩ := h1 K V ι b X hX N hN
  have hG := (h2 (InfinitePlace K) E E (Fin (finrank ℤ L)) (placePart (ι := ι)) (placePart (ι := ι))
    (rscMap c) (fun v => (c v)⁻¹) (Submodule.span ℝ (L : Set E)) (fun i => (bL i : E))
    horth horth (fun v => inv_nonneg.2 (hc v).le) hTmap hsplit
    (Formalism.F.linearIndependent_coe_basis''' L bL) hspan).2 hTinner
  have hdim' : ∀ v, finrank ℝ (Submodule.span ℝ (L : Set E) ⊓ placePart (ι := ι) v :
      Submodule ℝ E) = 2 * rkK N := hdim
  simp only [hdim'] at hG
  rw [hG, Real.sqrt_mul (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.2 (hc v).le) _)]
  congr 1
  have hsq : (∏ v, (c v)⁻¹ ^ (2 * (2 * rkK N))) = (∏ v, (c v)⁻¹ ^ (2 * rkK N)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    ring
  rw [hsq, Real.sqrt_sq (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.2 (hc v).le) _),
    Real.rpow_neg (Finset.prod_nonneg fun v _ => (hc v).le),
    show (2 * (rkK N : ℝ)) = ((2 * rkK N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => inv_pow _ _

theorem rescale_covolume_formula : RescaleCovol := by
  exact rescaleCovol_of place_decomposition gram_block_determinant place_lattice_structure

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
section
open Module NumberField

noncomputable section

namespace Formalism.HN

theorem twist_finrank_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
  have key : Module.finrank ℚ K = 2 * nPl K := by
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := by
      refine ⟨fun w => ?_⟩
      have hc : w.1.IsComplex := IsTotallyComplex.isComplex w.1
      first
        | exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc) w.2
        | exact (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2) hc
    have h3 : Nat.card {w : InfinitePlace K // w.IsComplex} = Nat.card (InfinitePlace K) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))
    simp only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty, h3] at h1
    simp only [nPl, Fintype.card_eq_nat_card]
    omega
  exact_mod_cast key

theorem twist_of (h1 : RescaleCovol) (h2 : PlLat) (h3 : ShiftInvariance.{0, 0, 0, 0}) : Twist := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc
  dsimp only
  intro L hL
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)
  have hfg : ∀ N : Submodule (𝓞 K) V, N ≤ L → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian L hL
    have h1' : (N.comap L.subtype).FG := IsNoetherian.noetherian _
    have h2' := h1'.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2'
  have hnPl : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hfr := twist_finrank_eq K
  have hP : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc v
  have hlogP : Real.log (∏ v, c v) = ∑ v, Real.log (c v) := Real.log_prod fun v _ => (hc v).ne'
  have hkey : ∀ N : Submodule (𝓞 K) V, N ≤ L →
      rk (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = deg (Formalism.HermitianLatticesTheory.realize b X) N +
        (1 / (nPl K : ℝ)) * (∑ v, Real.log (c v)) * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
    intro N hN
    have hNfg := hfg N hN
    obtain ⟨hlat, hrk, -⟩ := h2 K V ι b X hX N hNfg
    obtain ⟨-, hrk₂, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' N hNfg
    refine ⟨by rw [hrk, hrk₂], ?_⟩
    have hcov := h1 K V ι b X c hX hc N hNfg
    haveI := hlat.2
    have hC := Formalism.F.covol_pos (zl (Formalism.HermitianLatticesTheory.realize b X) N)
    simp only [deg, Formalism.F.deg]
    rw [hcov, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hC.ne', Real.log_rpow hP, hlogP, hrk]
    push_cast
    rw [hfr]
    field_simp
    ring
  obtain ⟨hlatL, hrkL, -⟩ := h2 K V ι b X hX L hL
  obtain ⟨hlatL₂, -, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' L hL
  obtain ⟨-, hmu, hstep, -⟩ := h3 (𝓞 K) V _ _ (Formalism.HermitianLatticesTheory.realize b X)
    (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L ((1 / (nPl K : ℝ)) * ∑ v, Real.log (c v))
    hlatL hlatL₂ hkey
  have hrkpos : L ≠ ⊥ → (rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) ≠ 0 := by
    intro hne
    rw [hrkL]
    have h1' : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2' : 0 < rkK L := by
      obtain ⟨s, hs⟩ := hL
      unfold rkK
      rw [← hs, Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
      haveI : FiniteDimensional K (Submodule.span K (s : Set V)) := FiniteDimensional.span_finset K s
      rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
      intro h0
      apply hne
      rw [← hs, eq_bot_iff]
      intro x hx
      have hx' := Submodule.span_le_restrictScalars (𝓞 K) K (s : Set V) hx
      have hx0 : x = 0 := by simpa [h0] using hx'
      simp [hx0]
    exact_mod_cast (Nat.mul_pos h1' h2').ne'
  have hslope : L ≠ ⊥ → slope (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L =
      slope (Formalism.HermitianLatticesTheory.realize b X) L + (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) := by
    intro hne
    have hs : ∀ ρ' : V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
        slope ρ' L = deg ρ' L / (rk ρ' L : ℝ) := fun _ => rfl
    rw [hs, hs, (hkey L le_rfl).1, (hkey L le_rfl).2, add_div, mul_div_assoc, div_self (hrkpos hne),
      mul_one]
  refine ⟨hslope, hmu, fun hne => ?_, fun θ => hstep θ⟩
  simp only [muDef, muMaxDef, muMinDef, hslope hne, (hmu hne).1, (hmu hne).2]
  refine ⟨by ring, by ring, by ring⟩

end Formalism.HN
end
end

