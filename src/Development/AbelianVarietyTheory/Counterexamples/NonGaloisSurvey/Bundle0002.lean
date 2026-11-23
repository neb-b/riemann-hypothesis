module

public import Mathlib
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CongruenceBoundParameters
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

namespace GlobalTheory.Survey.CongruenceBoundParameters

theorem window_pos {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (W : ℝ) (hW : W ∈ baseSizes L) (n : ℤ)
    (hn : n ∈ window L W) : 0 < n := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hl := lStar_pos L
  have hη := L.etaSz_pos
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (by positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    have : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
      unfold Scale.w'' Scale.b' Scale.a; field_simp
    rw [this]; exact div_le_self hb.le (by nlinarith)
  have hWw : L.sc.w'' D.R.n ≤ W := by
    rcases hW with rfl | rfl | ⟨t, rfl⟩
    · exact hw2
    · exact le_rfl
    · have h1 := L.bT_ge t
      have h2 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.floor_nonneg.2 (by positivity)
      linarith
  have h1 := P.h0_ge.1
  have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη.le (by linarith)
  have h3 := P.mteta
  have h4 : 16 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    mul_le_mul_of_nonneg_right (by nlinarith) hη.le
  have h5 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / LevelStarExponents.lStar L := Int.floor_le _
  have h6 : 0 < L.sc.b / LevelStarExponents.lStar L := by positivity
  have h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L) := by ring
  have h8 : 2 * L.sc.b / LevelStarExponents.lStar L = 2 * (L.sc.b / LevelStarExponents.lStar L) := by ring
  have : (0 : ℝ) < n := by linarith [hn.1]
  exact_mod_cast this

theorem two_lStar_lt_b {D : D7} (L : SizeData₂ D) : 2 * LevelStarExponents.lStar L < Real.exp L.sc.L := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : 3 * (D.R.m : ℝ) < D.R.t := by exact_mod_cast D.R.three_m_lt_t
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hS := L.Sc_pos
  have hN : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hA : (D.R.t : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by
    have a1 : (1 : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hn1 (by nlinarith)
    have a2 : (1 : ℝ) ≤ L.sc.L ^ 2 := by nlinarith
    have a3 : (D.R.t : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) := by nlinarith
    nlinarith
  have hB : (0 : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by positivity
  change 2 * LevelStarExponents.lStar L < L.sc.b
  unfold LevelStarExponents.lStar
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.Survey.CongruenceBoundParameters

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCharacterRatio
section
noncomputable section

namespace GlobalTheory.Survey.CrystallineCharacterRatio

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module TensorProduct
  GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]

end Abstract

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω]

theorem chi_eq_cyc (P : LocPrime l) (j : Ω →+* Om l) (σ : Formalism.ConjugateSelfDual.G E Ω) (g : GQ l)
    (h : ∀ x, g (j x) = j (σ x)) :
    ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  set c : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc

  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ' : IsPrimitiveRoot (j ζ) (l ^ m) := hζ.map_of_injective j.injective
    have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow m c).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G E Ω) Ω σ) ζ hζ.pow_eq_one
    obtain ⟨a, ha1, ha2⟩ := P.χQ_cyc g m (j ζ) hζ'.pow_eq_one
    have hne : j ζ ≠ 0 := hζ'.ne_zero (pow_ne_zero _ hl.ne_zero)
    have hpow : (j ζ) ^ a = (j ζ) ^ (PadicInt.toZModPow m c).val := by
      rw [← ha2, h, hσζ, map_pow]
    have hdvd : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - ((PadicInt.toZModPow m c).val : ℤ) := by
      rw [← hζ'.zpow_eq_one_iff_dvd, zpow_sub₀ hne, zpow_natCast, zpow_natCast, hpow,
        div_self (pow_ne_zero _ hne)]
    have h2 : ‖((a : ℚ_[l]) - (((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - ((PadicInt.toZModPow m c).val : ℤ)) m).mpr
        (by exact_mod_cast hdvd)
      exact_mod_cast this
    have h3 : ‖((((PadicInt.toZModPow m c).val : ℕ) : ℤ_[l]) - c)‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_natCast, ZMod.natCast_zmod_val, sub_self]
    have h3' : ‖((((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]) - (c : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_def] at h3
      exact_mod_cast h3
    have hsplit : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (c : ℚ_[l]) =
        (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) +
          (((a : ℚ_[l]) - (((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l])) +
            ((((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]) - (c : ℚ_[l]))) := by ring
    rw [hsplit]
    refine (Padic.nonarchimedean _ _).trans (max_le ha1 ((Padic.nonarchimedean _ _).trans (max_le h2 h3')))
  refine sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_))
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hl1
  refine (key m).trans ?_
  rw [zpow_neg, zpow_natCast, ← inv_pow, zero_add]
  exact hm.le

end Bridge

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem locChi_eps (g : Br.G D.nbr i w hw) :
    ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        (((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw g

  have hc := chi_eq_cyc (D.loc (D.nd.l i)) (D.nbr i w hw).j
    ((ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype ((D.nbr i w hw).e.symm g)) _ (fun x => by
      have := (D.nbr i w hw).e_comm ((D.nbr i w hw).e.symm g) x
      rw [MulEquiv.apply_symm_apply] at this
      exact this)
  unfold Br.locChi Br.chiG Br.PD
  rw [hχ, hc]
  unfold epsU Glob.epsO LocBridge.toLL decS Br.ι
  simp only [RingHom.comp_apply, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  erw [(D.nbr i w hw).eO_alg]
  rfl

end GlobalTheory.Survey.CrystallineCharacterRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowProbe

section Host
variable {R : Ranks} (H : Host R)

theorem conj_sqrt (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.toHostAx.conjE_apply φ x

theorem sqrt_sq (φ : H.E →+* ℂ) : φ (H.sqd) ^ 2 = -(H.d : ℂ) := by
  have h : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq
  rw [← map_pow, h]; simp

theorem mem_halfType_false (φ : H.E →+* ℂ) :
    φ ∈ halfType H false ↔ φ (H.sqd) = -(Complex.I * (Real.sqrt H.d : ℂ)) := by
  change φ (H.conj (H.sqd)) = _ ↔ _
  rw [conj_sqrt]
  constructor
  · intro h
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · intro h
    rw [h]; simp

theorem halfType_xor (φ : H.E →+* ℂ) : Xor (φ ∈ halfType H true) (φ ∈ halfType H false) := by
  rw [mem_halfType_false]
  change Xor (φ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ)) _
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have hs : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hd.le]; simp
  have hne : Complex.I * (Real.sqrt H.d : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hd).ne')
  have hne' : Complex.I * (Real.sqrt H.d : ℂ) ≠ -(Complex.I * (Real.sqrt H.d : ℂ)) := fun e =>
    hne (by linear_combination e / 2)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 ((sqrt_sq H φ).trans hs.symm) with h | h
  · exact Or.inl ⟨h, fun h' => hne' (h.symm.trans h')⟩
  · exact Or.inr ⟨h, fun h' => hne' (h'.symm.trans h)⟩

end Host

section Loc
variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem nonempty_emb : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :=
  ⟨((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra
    ((D.nbr i w hw).LL_split _)⟩

theorem embIn_xor (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    Xor (EmbIn (N := D.nd) D.nbr i true w hw τ) (EmbIn (N := D.nd) D.nbr i false w hw τ) := by
  obtain ⟨g, key, -⟩ := GlobalTheory.HTW.exists_letter_of_local_embedding D i w hw τ
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  have main : ∀ s, EmbIn (N := D.nd) D.nbr i s w hw τ ↔ D.host.emb g ∈ halfType D.host s := by
    intro s
    constructor
    · rintro ⟨-, φ, hφ, h⟩
      have : D.host.emb g = φ := RingHom.ext fun x => by
        rw [← hemb x]
        exact h x _ (key x).symm
      exact this ▸ hφ
    · intro hg
      refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, hg, fun x y hy => ?_⟩
      have hy' : y = D.embE (D.host.sigmaOf g x) :=
        (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
      rw [hy', hemb]
  rw [main, main]
  exact halfType_xor D.host _

theorem not_both_columns : ¬ (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w hw) := by
  rintro ⟨⟨⟨τ⟩, h1⟩, -, h2⟩
  rcases embIn_xor D i w hw τ with h | h
  · exact h.2 (h2 τ)
  · exact h.2 (h1 τ)

theorem bridge_place (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

end Loc

end GlobalTheory.SplitRowProbe
end
end

