module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHom
section
set_option autoImplicit false

noncomputable section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.DepthMono

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) : Fin d' → MvPowerSeries (Fin d) C :=
  fun b => ∑ a, M b a • (X a : MvPowerSeries (Fin d) C)

theorem constantCoeff_linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) (b : Fin d') :
    constantCoeff (linSub M b) = 0 := by
  simp [linSub]

theorem subst_expOf_hom {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    (c : Fin d') : subst (expOf G) (φ c) = subst (linSub M) (expOf G' c) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hE' : HasSubst (expOf G') := hasSubst_of_constantCoeff_zero (isExp_expOf G').1
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.1
  have hL : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hlg' : HasSubst G'.lg := hasSubst_of_constantCoeff_zero G'.lg_const
  set ψ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (expOf G) (φ c) with hψ
  set ρ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (linSub M) (expOf G' c) with hρ
  have hψ0 : ∀ c, constantCoeff (ψ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hE (isExp_expOf G).1 (hφ.1 c)
  have hρ0 : ∀ c, constantCoeff (ρ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hL (constantCoeff_linSub M) ((isExp_expOf G').1 c)
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hρs : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  have key : ∀ b, subst ψ (G'.lg b) = subst ρ (G'.lg b) := by
    intro b
    have h1 : subst ψ (G'.lg b) = subst (expOf G) (subst φ (G'.lg b)) :=
      (subst_comp_subst_apply hφs hE (G'.lg b)).symm
    have h2 : subst ρ (G'.lg b) = subst (linSub M) (subst (expOf G') (G'.lg b)) :=
      (subst_comp_subst_apply hE' hL (G'.lg b)).symm
    rw [h1, h2, hφ.2.2, (isExp_expOf G').2, subst_sum_smul hE, subst_X hL]
    simp only [(isExp_expOf G).2, linSub]
  have inj : ∀ c, ψ c = subst (fun b => subst ψ (G'.lg b)) (expOf G' c) ∧
      ρ c = subst (fun b => subst ρ (G'.lg b)) (expOf G' c) := by
    intro c
    constructor
    · rw [← subst_comp_subst_apply hlg' hψs, subst_lg_expOf, subst_X hψs]
    · rw [← subst_comp_subst_apply hlg' hρs, subst_lg_expOf, subst_X hρs]
  show ψ c = ρ c
  rw [(inj c).1, (inj c).2, funext key]

theorem subst_exp_hom {τ : Type} {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    {L : Fin d → MvPowerSeries τ C} (hL0 : ∀ e, constantCoeff (L e) = 0) (c : Fin d') :
    subst (fun e => (subst L (expOf G e) : MvPowerSeries τ C)) (φ c) =
      (subst (fun b => ∑ a, M b a • L a) (expOf G' c) : MvPowerSeries τ C) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hM : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  rw [← subst_comp_subst_apply hE hL, subst_expOf_hom hφ, subst_comp_subst_apply hM hL]
  congr 1
  funext b
  rw [linSub, subst_sum_smul hL]
  simp only [subst_X hL]

theorem detDepth_le_of_isIntHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)),
    ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
      (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C,
      detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  intro C _ _ v i d d' k G G' φ M hφ u
  have hX : ∀ b : Fin i, HasSubst
      (fun e : Fin d => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) := fun b =>
    hasSubst_of_constantCoeff_zero fun e => by simp
  let Φ : (Σ _ : Fin i, Fin d') → MvPowerSeries (Σ _ : Fin i, Fin d) C := fun x =>
    subst (fun e : Fin d => (X ⟨x.1, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (φ x.2)
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hX x.1) (fun e => by simp) (hφ.1 x.2)
  have hΦi : ∀ x, MvIsInt v (Φ x) := fun x =>
    ptIntSer_subst (v := v) (hX x.1) (fun e => ptIntSer_X _) (hφ.2.1 x.2)
  have hL0 : ∀ (b : Fin i) (e : Fin d), constantCoeff
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := fun b e => by simp
  have hA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hL0 x.1)) (hL0 x.1)
        ((isExp_expOf G).1 x.2)
  have hcol : (fun x => subst (expAlong (fun _ : Fin i => G) (fun _ => u)) (Φ x)) =
      expAlong (fun _ : Fin i => G') (fun _ a => M.mulVec (u a)) := by
    funext x
    simp only [Φ]
    rw [subst_comp_subst_apply (hX x.1) hA]
    simp only [subst_X hA, expAlong]
    rw [subst_exp_hom hφ (hL0 x.1)]
    congr 1
    funext b
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  refine le_iInf fun f => iInf_le_of_le ⟨subst Φ f.1, ptIntSer_subst (v := v) hΦ hΦi f.2⟩ (le_of_eq ?_)
  simp only
  rw [subst_comp_subst_apply hΦ hA, hcol]

end GlobalTheory.DepthMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnit
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem frame_cc_ev {C : Type} [CommRing C] {d m n : ℕ} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS C m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => a p.1 p.2)
    (hasSubst_of_constantCoeff_zero h0) h0 hf

theorem frame_subst_ev {C : Type} [CommRing C] {d m n : ℕ} {σ : Type} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t)
    (f : PS C m d) :
    subst t (ev a f) = subst (fun p : Fin m × Fin d => subst t (a p.1 p.2)) f := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact subst_comp_subst_apply (a := fun p : Fin m × Fin d => a p.1 p.2) (hasSubst_of_constantCoeff_zero h0) ht f

theorem frame_cc_pt {C : Type} [CommRing C] {d n : ℕ} (b : Fin n) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![pt C d b] : Fin 1 → Pt C n d) j i) = 0 := by
  simp [pt]

theorem frame_subst_ev_pt {C : Type} [CommRing C] {d n : ℕ} {σ : Type} (b : Fin n)
    {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t) (f : PS C 1 d) :
    subst t (ev ![pt C d b] f) = subst (fun p : Fin 1 × Fin d => t (b, p.2)) f := by
  rw [frame_subst_ev _ (frame_cc_pt b) ht]
  congr 1
  funext p
  rcases p with ⟨j, i⟩
  fin_cases j
  simpa [pt] using (subst_X (R := C) ht (b, i))

theorem frame_exp_zero {C : Type} [CommRing C] [Algebra ℚ C] {σ : Type} :
    PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  classical
  unfold PowerSeries.subst
  have e : (fun _ : Unit => (0 : MvPowerSeries σ C)) = 0 := rfl
  rw [e, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff,
      map_one]
    exact PowerSeries.constantCoeff_exp (A := C)
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg hx, MvPowerSeries.coeff_one, if_neg hx, map_zero]

theorem frameSt_of (hAct : ActSt) (hUnit : UnitSt) : FrameSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hh w0 n
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis hh.ax0
  have hact : ∀ i, constantCoeff (B.actK C w0 i) = 0 := fun i => by
    unfold FB.actK
    rw [constantCoeff_map, B.A.const, map_zero]
  have hpair : ∀ j i, constantCoeff
      ((![pt C d 0, comp1 (B.actK C w0) (pt C d 0)] : Fin 2 → Pt C 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · exact frame_cc_ev _ (frame_cc_pt 0) (hact i)
  have hcL : constantCoeff (B.hL C h w0) = 0 := frame_cc_ev _ hpair hc
  have hS : constantCoeff (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => frame_cc_ev _ (frame_cc_pt b) hcL
  obtain ⟨-, -, -, hadd, hone, -⟩ := hUnit C v (Fin n × Fin d)
  refine ⟨hone _ hS, fun k => ?_, fun σ _ y hy => ?_⟩
  · unfold frameSer FB.expS
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, frame_exp_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, hadd _ _ _ hS, ih, pow_succ]
      rw [smul_eq_C_mul, map_mul, hS, mul_zero]
  · have ht : HasSubst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy q.1) q.2
    have key : subst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2)
        (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) =
        ∑ j, pairSer (fglOf hB) h (y j) (mv (dAct C B w0) (y j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← coe_substAlgHom ht, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hs : HasSubst (fun p : Fin 1 × Fin d => expPt (fglOf hB) (y b) p.2) :=
        hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy b) q.2
      rw [coe_substAlgHom, frame_subst_ev_pt b ht]
      unfold FB.hL pairSer
      rw [frame_subst_ev _ hpair hs, (hAct C v d R O B hB σ w0).1 (y b) (hy b)]
      congr 1
      funext ⟨j, i⟩
      fin_cases j
      · exact subst_X hs _
      · exact frame_subst_ev_pt 0 hs _
    rw [← key]
    unfold frameSer FB.expS PowerSeries.subst
    exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hS) ht _

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuation
section
set_option autoImplicit false

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section ResidueField

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {d : ℕ}

theorem sqrtNeg_ne_neg (h2 : p ≠ 2) (hd : (d : ZMod p) ≠ 0) {r : k} (hr : r ^ 2 = -(d : k)) : r ≠ -r := by
  intro h
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h0)
    exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hr0 : r = 0 := by
    have : 2 * r = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2k
  have hdk : (d : k) = 0 := by
    rw [hr0] at hr
    linear_combination hr
  exact hd ((ZMod.natCast_eq_zero_iff d p).2 ((CharP.cast_eq_zero_iff k p d).1 hdk))

theorem sqrtNeg_pow_of_isSquare (hs : IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) : r ^ p = r := by
  obtain ⟨m, hm⟩ := hs
  have h1 : r ^ 2 = (ZMod.castHom (dvd_refl p) k m) ^ 2 := by
    rw [hr, ← map_pow, sq, ← hm, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, ← map_pow, ZMod.pow_card]
  · rw [h, ← map_neg, ← map_pow, ZMod.pow_card]

theorem sqrtNeg_pow_ne_of_not_isSquare (hs : ¬ IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) :
    r ^ p ≠ r := by
  have hd : (d : ZMod p) ≠ 0 := fun h => hs (by rw [h, neg_zero]; exact IsSquare.zero)
  have hd' : -(d : ZMod p) ≠ 0 := neg_ne_zero.2 hd
  have h2 : p ≠ 2 := by
    rintro rfl
    apply hs
    generalize (-(d : ZMod 2)) = x
    exact ⟨x, by rw [← sq, ZMod.pow_card]⟩
  have he : (-(d : ZMod p)) ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hd').resolve_left fun h => hs ((ZMod.euler_criterion p hd').2 h)
  have hk : (-(d : k)) ^ (p / 2) = -1 := by
    have := congrArg (ZMod.castHom (dvd_refl p) k) he
    rwa [map_pow, map_neg, map_neg, map_natCast, map_one] at this
  have hp : p = 2 * (p / 2) + 1 := by
    have := (Fact.out : p.Prime).eq_two_or_odd.resolve_left h2
    omega
  have h3 : r ^ p = -r := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hr, hk, neg_one_mul]
  rw [h3]
  exact (sqrtNeg_ne_neg h2 hd hr).symm

end ResidueField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem label_rt_sq (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq
  rwa [map_pow, map_neg, map_natCast] at this

theorem conj_label_rt (H : Host E) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = -σ (H.rt : E) := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have h := label_rt_sq H σ
  generalize σ (H.rt : E) = z at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : z.re = 0 := by
    by_contra h0
    have h4 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [h4] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h3]

theorem exists_w0_sq_even_constant (H : Host E) : ∃ n : ℕ, H.w0 ^ 2 = H.w0 - 2 * n := by
  refine ⟨(H.d + 1) / 8, ?_⟩
  have h8 : ((H.d : ℕ) : 𝓞 E) + 1 = 8 * (((H.d + 1) / 8 : ℕ) : 𝓞 E) := by
    have : H.d + 1 = 8 * ((H.d + 1) / 8) := by have := H.d_mod; omega
    exact_mod_cast this
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have h1 := H.two_weight_eq_one_add_root
  have h2 := H.rt_sq
  linear_combination (2 * H.w0 - 1 + H.rt) * h1 + h2 - h8

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem red_eq_of_label_eq {σ σ' : E →+* ℂ} {a b : 𝓞 E} (h : σ' (a : E) = σ (b : E)) :
    red io X σ' a = red io X σ b := by
  have h1 : embK c σ' a = embK c σ b := Subtype.ext h
  have h2 : embO io X σ' a = embO io X σ b := X.ints.hom_inj (by
    rw [algebraMap_embO, algebraMap_embO, embX, embX, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, h1])
  rw [red, red, RingHom.comp_apply, RingHom.comp_apply, h2]

theorem frobOnType : FrobOnType io X := by
  intro σ σ' hF
  haveI := charP_residueField_of_irreducible X
  have hred : ∀ a, red io X σ' a = red io X σ a ^ p := fun a => (red_eq_pow_iff io X σ σ' a p).2 (hF a)
  have hr : red io X σ H.rt ^ 2 = -(H.d : ResidueField X.O) := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hpm : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [label_rt_sq, label_rt_sq])
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have key : σ' (H.rt : E) = σ (H.rt : E) := by
      refine hpm.resolve_right fun h => ?_
      by_cases h2 : p = 2
      · subst h2
        obtain ⟨n, hn⟩ := exists_w0_sq_even_constant H
        have hw : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := fun τ => by
          have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        have h1 : σ' (H.w0 : E) = σ ((1 - H.w0 : 𝓞 E) : E) := by
          have e : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E) := by
            have := map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0
            rwa [map_one] at this
          rw [e]
          linear_combination (1 / 2) * hw σ' + (1 / 2) * hw σ + (1 / 2) * h
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, ← map_pow, hn, map_sub, map_sub, map_mul, map_one, map_ofNat] at h3
        have h4 : (2 : ResidueField X.O) = 0 := by
          exact_mod_cast CharP.cast_eq_zero (ResidueField X.O) 2
        apply one_ne_zero (α := ResidueField X.O)
        linear_combination -h3 + (red io X σ H.w0 - red io X σ n) * h4
      · have h1 : σ' (H.rt : E) = σ ((-H.rt : 𝓞 E) : E) := by
          rw [h]; exact (map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, sqrtNeg_pow_of_isSquare hs.2 hr, map_neg] at h3
        exact sqrtNeg_ne_neg h2 hs.1 hr h3
    rw [InPsi, InPsi, key]
  · have key : σ' (H.rt : E) = -σ (H.rt : E) := by
      refine hpm.resolve_left fun h => ?_
      have h3 := red_eq_of_label_eq io X h
      rw [hred] at h3
      exact sqrtNeg_pow_ne_of_not_isSquare hi hr h3
    rw [InPsi, InPsi, key, conj_label_rt]

theorem frobOnType_all (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) : FrobOnType io X :=
  frobOnType io X

end GlobalTheory.PrimePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.HermRead

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section Lin

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

theorem mv_sum (A : Matrix (Fin d) (Fin d) C) {β : Type} (s : Finset β) (x : β → Fin d → MvPowerSeries σ C) :
    mv A (∑ b ∈ s, x b) = ∑ b ∈ s, mv A (x b) := by
  funext e
  simp only [mv, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem mv_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv A (mv A' w) = mv (A * A') w := by
  funext e
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem add_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv (A + A') w = mv A w + mv A' w := by
  funext e
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

end Lin

theorem map_sum_of_additive {M Q : Type} [AddCommMonoid M] [AddCommGroup Q] (p : M → Prop) (h0 : p 0)
    (hp : ∀ x y, p x → p y → p (x + y)) (f : M → Q) (hf : ∀ x y, p x → p y → f (x + y) = f x + f y)
    {β : Type} (s : Finset β) (x : β → M) (hx : ∀ b, p (x b)) :
    p (∑ b ∈ s, x b) ∧ f (∑ b ∈ s, x b) = ∑ b ∈ s, f (x b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have := hf 0 0 h0 h0
    rw [add_zero] at this
    simpa using this
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact ⟨hp _ _ (hx b) ih.1, by rw [hf _ _ (hx b) ih.1, ih.2]⟩

theorem finSt_of (hAdd : AddSt) (hAct : ActSt) (hUnit : UnitSt) (hBi : BiaddSt) : FinSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hg σ _ κ _ w hw w0 n a ι _ e t ht
  obtain ⟨hU0, hUadd, hUneg, -⟩ := hUnit C v σ
  obtain ⟨hI0, -, hIadd⟩ := hAdd C v d (fglOf hB) σ
  have hIact := fun c => (hAct C v d R O B hB σ c).2
  have hbi := hBi C v d R O B hB h hg σ
  let U : AddSubgroup (MvPowerSeries σ C) :=
    { carrier := {s | LogUnit v s}
      add_mem' := fun {s t} hs ht => hUadd s t hs ht
      zero_mem' := hU0
      neg_mem' := fun {s} hs => hUneg s hs }
  let π := QuotientAddGroup.mk' U
  have key : ∀ s, π s = 0 ↔ LogUnit v s := fun s => QuotientAddGroup.eq_zero_iff s
  have h1 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h (x + y) z) = π (pairSer (fglOf hB) h x z) + π (pairSer (fglOf hB) h y z) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.1
    rw [map_sub, map_add (f := _), sub_eq_zero] at this
    exact this.symm
  have h2 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h z (x + y)) = π (pairSer (fglOf hB) h z x) + π (pairSer (fglOf hB) h z y) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.2.1
    rw [map_sub, map_add (f := _), sub_eq_zero] at this
    exact this.symm
  have h3 : ∀ (c : O) x z, IntLog (fglOf hB) x → IntLog (fglOf hB) z →
      π (pairSer (fglOf hB) h (mv (dAct C B c) x) z) =
        π (pairSer (fglOf hB) h x (mv (dAct C B (star c)) z)) := by
    intro c x z hx hz
    have := (key _).2 ((hbi x x z hx hx hz).2.2.2 c)
    rwa [map_sub, sub_eq_zero] at this
  let F : κ → κ → O →+ MvPowerSeries σ C ⧸ U := fun b b' =>
    AddMonoidHom.mk' (fun c => π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b')))) fun c c' => by
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, add_mv]
      exact h2 _ (hw b) _ _ (hIact _ _ (hw b')) (hIact _ _ (hw b'))
  have hF : ∀ b b' c, F b b' c = π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b'))) := fun _ _ _ => rfl
  have hj : ∀ j, π (pairSer (fglOf hB) h (∑ b, mv (dAct C B (a b j)) (w b))
      (mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)))) =
        ∑ b, ∑ b', F b b' (star (a b j) * a b' j * w0) := by
    intro j
    have hy : IntLog (fglOf hB) (∑ b, mv (dAct C B (a b j)) (w b)) :=
      (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun _ => (0 : ℤ)) (by simp) Finset.univ _
        fun b => hIact _ _ (hw b)).1
    have hz := hIact w0 _ hy
    generalize hzz : mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)) = z at hz
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h x z)) (h1 _ hz)
      Finset.univ _ fun b => hIact (a b j) _ (hw b)).2.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [h3 _ _ _ (hw b) hz, ← hzz, mv_mv, mv_sum, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul]
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h (w b) x))
      (h2 _ (hw b)) Finset.univ _ fun b' => hIact _ _ (hIact _ _ (hw b'))).2.trans
      (Finset.sum_congr rfl fun b' _ => ?_)
    rw [hF, mv_mv, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul, mul_right_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← key, map_sub, sub_eq_zero, map_sum, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Finset.sum_mul, ht, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, hF]

end GlobalTheory.IsoTriv.HermRead
end
end

