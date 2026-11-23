module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0129
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ContentZeroAtSmallPrimes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private theorem exists_quotient_side_of_isType_lemma (k r : ℕ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (hk : 1 ≤ k)
    (z : Fin (2 * r + k + 1) → ℂ) (π : _root_.Formalism.FourierDecayAlt.B.Mat k r → W →L[ℂ] W) (u : ℕ → ℝ)
    (μW μN μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z)
    (hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW) (hN : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN)
    (hG : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.BranchingSupport.GG k r) μG) (hπ : _root_.Formalism.FourierDecayAlt.Q.IsType k r z π u) :
    ∃ ν, _root_.BranchingSupport.SideG k r z π u μW μN μG ν := by
  have hW' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW
  have hN' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1).2 hN
  have hG' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.BranchingSupport.GG k r) μG :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1).2 hG
  obtain ⟨ν, hν⟩ :=
    _root_.GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW μN μG hz hT hW' hN' hG'
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.besType_hcParam k r W z π u hz hT hπ
  exact ⟨ν, hz, hT, ⟨u₀, hu₀⟩, hπ.2.2.2.2.2, hW', hN', hG', hν⟩


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.exists_sideG_both_of_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type)
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z D.π u →
    _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z' D.π' u' → ∃ νq νq',
      _root_.BranchingSupport.SideG k r D.z D.π u D.μW D.μN D.μG νq ∧
        _root_.BranchingSupport.SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D u u' hp hq
  obtain ⟨z, z', π, π', μG, μW, μN, μW', _, _, hk, hz, hz', hT, hT', _, _, _, _, _, _, hG, hW,
    hN, hW', _, _, _, _⟩ := D
  obtain ⟨ν, hν⟩ := exists_quotient_side_of_isType_lemma k r Wp hk z π u μW μN μG hz hT hW hN hG hp
  obtain ⟨ν', hν'⟩ :=
    exists_quotient_side_of_isType_lemma k r Wq hk z' π' u' μW' μN μG hz' hT' hW' hN hG hq
  exact ⟨ν, ν', hν, hν'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximalStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  first | exact @GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' | exact GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' | (intros; apply GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegersStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  first | exact @GlobalTheory.CharDepth.isEigBasis_valExt | exact GlobalTheory.CharDepth.isEigBasis_valExt | (intros; apply GlobalTheory.CharDepth.isEigBasis_valExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeFrobeniusOrbitsLabelAtSplitPrime
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LabSplit

theorem exists_reps {P : Type} [Fintype P] (d : ℕ) [NeZero d] (pos : P → ℕ → P) (h0 : ∀ z, pos z 0 = z)
    (hadd : ∀ z s t, pos (pos z s) t = pos z (s + t)) (hfree : ∀ z s t, pos z s = pos z t ↔ s ≡ t [MOD d]) :
    ∃ Z : Finset P, ∀ z', ∃! p : P × ZMod d, p.1 ∈ Z ∧ pos p.1 p.2.val = z' := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  let S : Setoid P :=
    { r := fun z z' => ∃ s, pos z s = z'
      iseqv :=
        { refl := fun z => ⟨0, h0 z⟩
          symm := by
            rintro z _ ⟨s, rfl⟩
            refine ⟨(d - 1) * s, ?_⟩
            rw [hadd]
            conv_rhs => rw [← h0 z]
            rw [hfree]
            have : s + (d - 1) * s = d * s := by
              obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
              simp only [Nat.add_sub_cancel_left]; ring
            rw [this]
            exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
          trans := by
            rintro z _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
            exact ⟨s + t, (hadd z s t).symm⟩ } }
  refine ⟨Finset.univ.filter fun z => (Quotient.mk S z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, pos (Quotient.mk S z').out s = z' := Quotient.mk_out (s := S) z'
  have hmod : ((s : ZMod d)).val ≡ s [MOD d] := by
    rw [ZMod.val_natCast]; exact Nat.mod_modEq s d
  refine ⟨((Quotient.mk S z').out, (s : ZMod d)), ⟨by simp, ?_⟩, ?_⟩
  · exact ((hfree _ _ _).2 hmod).trans hs
  · rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ht
    have h1 : Quotient.mk S z = Quotient.mk S z' := Quotient.sound ⟨_, ht⟩
    have h2 : z = (Quotient.mk S z').out := by rw [← h1, hz]
    refine Prod.ext h2 ?_
    rw [h2, ← hs] at ht
    have h3 : pos (Quotient.mk S z').out t.val = pos (Quotient.mk S z').out s := by
      rw [hs] at ht ⊢; exact ht
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).2 ((hfree _ _ _).1 h3)
    simpa using h4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)

theorem rt_sq_field : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using this

theorem inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, rt_sq_field]; simp
  have h2 : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h := H.sqrt_neg_disc_sq
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have h0 : -H.rt0 ≠ H.rt0 := by
    intro h
    have h3 : H.rt0 = 0 := by linear_combination -h / 2
    have h4 := H.sqrt_neg_disc_sq
    rw [h3] at h4
    have : (H.d : ℂ) = 0 := by linear_combination h4
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, h2]; simp [h0]
  · rw [h, map_neg, h2]; simp [h0]

theorem not_MM_neg_sub_pow {C : Type} [Field C] (V : VF C) (d : ℕ) (r : C) (hr : r ^ 2 = -(d : C)) (hi : V.Ge 0 r)
    (h2 : V.l ≠ 2) (hj : jacobiSym (-(d : ℤ)) V.l = 1) : ¬ V.MM (-r - r ^ V.l) := by
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have hp := legendreSym.eq_pow V.l (-(d : ℤ))
  rw [hj] at hp
  have hdv : (V.l : ℤ) ∣ (-(d : ℤ)) ^ (V.l / 2) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hp ⊢
    rw [← hp, sub_self]
  obtain ⟨k, hk⟩ := hdv
  have hnd : ¬ (V.l : ℤ) ∣ -(d : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← legendreSym.eq_zero_iff, hj]
    exact one_ne_zero
  have hpr : Prime (V.l : ℤ) := Nat.prime_iff_prime_int.1 V.l_prime
  have hn2 : ¬ (V.l : ℤ) ∣ (2 : ℤ) := by
    intro h
    have : V.l ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq V.l_prime Nat.prime_two).1 this)
  have hv2 := GlobalTheory.EmbSep.v_intCast_eq_zero V hn2
  have hvd := GlobalTheory.EmbSep.v_intCast_eq_zero V hnd
  have hodd : V.l = 2 * (V.l / 2) + 1 := by
    have := V.l_prime.eq_two_or_odd.resolve_left h2
    omega
  have hkC : (-(d : C)) ^ (V.l / 2) = 1 + (V.l : C) * (k : C) := by
    have := congrArg (Int.cast : ℤ → C) hk
    push_cast at this
    linear_combination this
  have hpow : r ^ V.l = r + (V.l : C) * ((k : C) * r) := by
    conv_lhs => rw [hodd, pow_succ, pow_mul, hr, hkC]
    ring
  have hk0 : V.Ge 0 (k : C) := by
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa using VF.ge_natCast (V := V) n
    · simpa using (VF.ge_natCast (V := V) n).neg
  intro hM
  have h1 : 0 < V.v ((V.l : C) * ((k : C) * r)) := by
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (hk0.mul_int hi))
  have h3 := V.v.map_lt_add hM h1
  have h4 : -r - r ^ V.l + (V.l : C) * ((k : C) * r) = -(((2 : ℤ) : C) * r) := by
    rw [hpow]; push_cast; ring
  rw [h4, V.v.map_neg, V.v.map_mul, hv2, zero_add] at h3
  have h5 : ((-(d : ℤ) : ℤ) : C) = r * r := by push_cast; rw [← hr]; ring
  rw [h5, V.v.map_mul] at hvd
  have h6 : 0 < V.v r + V.v r := lt_of_lt_of_le h3 (le_add_of_nonneg_right h3.le)
  rw [hvd] at h6
  exact lt_irrefl _ h6

theorem labelling_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → N.cls V.l = PrimeClass.splitK → ∀ j : ℕ, ∃ (d : ℕ) (_ : NeZero d) (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)), RF.IsReps (parAt N j d pos) Z ∧ Z.Nonempty ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod d => tauSp N pl pos x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauSp (d := d) N pl pos z g) := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ V ι hE hl _ hcls j
  obtain ⟨φ, hφ⟩ := GlobalTheory.RowAt.exists_frob_all_embeddings E H lv c T io C V ι hE hP.galois hP.comm
  haveI : Inhabited (RPl N.R) := ⟨(false, 0)⟩
  have h2 : V.l ≠ 2 := by
    intro h
    unfold NumDatum.cls primeClass at hcls
    rw [if_pos (show V.l ∈ N.H.small from h ▸ Nat.mem_primeFactors.2 ⟨Nat.prime_two, N.H.two_dvd_QS, N.H.QS_pos.ne'⟩)] at hcls
    exact absurd hcls (by decide)
  have hj : jacobiSym (-(H.d : ℤ)) V.l = 1 := by
    rw [hP.d_eq]
    by_contra h
    unfold NumDatum.cls primeClass at hcls
    split_ifs at hcls
  have hfix : φ (H.rt : E) = H.rt := by
    have h1 : (φ (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      rw [← map_pow, rt_sq_field]; simp
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_right fun h => ?_
    let τ : E →+* ℂ := pl default
    have h3 : emA3 io ι (τ.comp (φ : E →+* E)) H.rt = -emA3 io ι τ H.rt := by
      have : embK c (τ.comp (φ : E →+* E)) H.rt = -embK c τ H.rt := by
        apply Subtype.ext
        rw [embK_coe]
        push_cast
        rw [embK_coe]
        simp [h]
      simp only [emA3, RingHom.comp_apply, this, map_neg]
    have h4 := hφ τ H.rt
    rw [h3] at h4
    refine not_MM_neg_sub_pow V H.d _ ?_ ?_ h2 hj h4
    · rw [← map_pow, H.rt_sq]; simp
    · exact ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral H.rt))
  have hfixs : ∀ s : ℕ, (φ ^ s) (H.rt : E) = H.rt := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [pow_succ, AlgEquiv.mul_apply, hfix, ih]
  have hex : ∀ (z : RPl N.R) (s : ℕ), ∃ z', pl z' = (pl z).comp ((φ ^ s : E ≃ₐ[ℚ] E) : E →+* E) := by
    intro z s
    refine (hP.psi _).1 ?_
    have : InPsi H (pl z) := (hP.psi _).2 ⟨z, rfl⟩
    unfold InPsi at this ⊢
    change pl z ((φ ^ s) (H.rt : E)) = H.rt0
    rw [hfixs]; exact this
  choose pos hpos using hex
  haveI : NeZero (orderOf φ) := ⟨(orderOf_pos φ).ne'⟩
  have h0 : ∀ z, pos z 0 = z := fun z => hP.inj (by rw [hpos]; ext x; simp)
  have hadd : ∀ z s t, pos (pos z s) t = pos z (s + t) := fun z s t =>
    hP.inj (by rw [hpos, hpos, hpos]; ext x; simp [pow_add])
  have hfree : ∀ z s t, pos z s = pos z t ↔ s ≡ t [MOD orderOf φ] := by
    intro z s t
    rw [← pow_eq_pow_iff_modEq, ← hP.inj.eq_iff, hpos, hpos]
    constructor
    · intro h
      ext x
      exact (pl z).injective (RingHom.congr_fun h x)
    · intro h; rw [h]
  obtain ⟨Z, hZ⟩ := exists_reps (orderOf φ) pos h0 hadd hfree
  have hin : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hnc : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff H _).1 (h ▸ hin z) (hin z')
  have huniq : ∀ (z z' : Z) (s s' : ZMod (orderOf φ)), pl (pos z s.val) = pl (pos z' s'.val) → z = z' ∧ s = s' := by
    intro z z' s s' h
    have := (hZ (pos z' s'.val)).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, hP.inj h⟩ ⟨z'.2, rfl⟩
    exact ⟨Subtype.ext (congrArg Prod.fst this), congrArg Prod.snd this⟩
  refine ⟨orderOf φ, inferInstance, pos, Z, hZ, ?_, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, -⟩ := hZ default
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    simp only [tauSp] at h
    split_ifs at h with hg hg' hg'
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ h
      rw [hg, hg']
    · exact absurd h (hnc _ _)
    · exact absurd h.symm (hnc _ _)
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ (star_injective h)
      have : g = g' := by omega
      rw [this]
  · intro τ
    by_cases hτ : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hP.psi _).1 hτ
      obtain ⟨p, hp, -⟩ := hZ z'
      exact ⟨(⟨p.1, hp.1⟩, 0, p.2), by simp [tauSp, hp.2]⟩
    · obtain ⟨z', hz'⟩ := (hP.psi _).1 ((inPsi_conj_iff H τ).2 hτ)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, 1, p.2), ?_⟩
      simp only [tauSp, hp.2, hz', one_ne_zero, if_false]
      exact star_star τ
  · intro z g s x
    have h1 : pos z (s + 1).val = pos z (s.val + 1) := by
      rw [hfree, ← ZMod.natCast_eq_natCast_iff]
      simp
    have h3 : pl (pos z (s + 1).val) = (pl (pos z s.val)).comp (φ : E →+* E) := by
      rw [h1, hpos, hpos]; ext y; simp [pow_succ]
    have h4 : tauSp (d := orderOf φ) N pl pos z g (s + 1) = (tauSp (d := orderOf φ) N pl pos z g s).comp (φ : E →+* E) := by
      unfold tauSp
      split_ifs
      · exact h3
      · rw [h3]; rfl
    rw [h4]
    exact hφ _ x

end GlobalTheory.LabSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem sum_fin_le_two_blocks {n K j : ℕ} (hn : n = K + j) (a : Fin n → ℝ) (A B : ℝ)
    (h1 : ∀ i, i.1 < K → a i ≤ A) (h2 : ∀ i, K ≤ i.1 → a i ≤ B) : ∑ i, a i ≤ K * A + j * B := by
  subst hn
  rw [Fin.sum_univ_add]
  have e1 : ∑ i : Fin K, a (Fin.castAdd j i) ≤ ∑ _i : Fin K, A :=
    Finset.sum_le_sum fun i _ => h1 _ (by simp)
  have e2 : ∑ i : Fin j, a (Fin.natAdd K i) ≤ ∑ _i : Fin j, B :=
    Finset.sum_le_sum fun i _ => h2 _ (by simp)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1 e2
  linarith

theorem four_sq_lt_of_eighth {k b g : ℝ} (hk : 5 ≤ k) (hb : 1 ≤ b) (hg : (k * b) ^ 8 ≤ g) :
    4 * k ^ 2 * b < (g - 2) / 2 := by
  have h5 : 5 ≤ k * b := by nlinarith
  have h0 : k ^ 2 * b ≤ (k * b) ^ 2 := by
    have : 0 ≤ k ^ 2 * b * (b - 1) := by
      have : 0 ≤ b - 1 := by linarith
      have : 0 ≤ b := by linarith
      positivity
    nlinarith
  set y := k * b
  have h2 : 25 ≤ y ^ 2 := by nlinarith
  have h6 : 25 ≤ y ^ 6 := h2.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have h8 : y ^ 8 = y ^ 6 * y ^ 2 := by ring
  nlinarith

theorem DF_kaR_le : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ j, InR D j → (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) ∧ ∀ i, (WeightAlgebra.DF (kaR Tp hK j) : ℝ) < ((D.host.g i : ℝ) - 2) / 2 := by
  intro D L Pm Tp hK hx hkb j hj
  obtain ⟨hSe, hw⟩ := _root_.GlobalTheory.RunDepth.sizes_le_two_mul D L Pm hx hkb
  have hw := (hw j hj).1
  have hrow := _root_.GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj
  have hcard := (_root_.GlobalTheory.RunDepth.plOf_bijective_card D).2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hj1 := hj.1
  have hj2 := hj.2
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hmkR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (D.R.f_le_k : D.R.f ≤ D.R.k)
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hb : 1 ≤ L.sc.b := by
    unfold Scale.b
    apply Real.one_le_exp
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hτ : ∀ τ : D.what₂.Tau, ((∑ i, ((kaR Tp hK j).aP τ i : ℝ)) + ∑ i, ((kaR Tp hK j).aM τ i : ℝ)) ≤
      (D.R.k : ℝ) * (2 * L.sc.b + (L.Sc + L.etaSz)) := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := hrow τ
    have s1 := sum_fin_le_two_blocks (n := (D.R.sigW j).1) (K := D.R.k - 1) (j := j)
      (by show D.R.k + j - 1 = _; omega) (fun i => ((kaR Tp hK j).aP τ i : ℝ)) (2 * L.sc.b + L.Sc) L.etaSz
      (fun i hi => (r1 i hi).trans (by linarith [(hw τ).2])) r2
    have s2 := sum_fin_le_two_blocks (n := (D.R.sigW j).2) (K := 0) (j := D.R.m - j)
      (by show D.R.m - j = _; omega) (fun i => ((kaR Tp hK j).aM τ i : ℝ)) 0 L.etaSz
      (fun i hi => absurd hi (Nat.not_lt_zero _)) (fun i _ => r3 i)
    rw [Nat.cast_sub (by omega : 1 ≤ D.R.k)] at s1
    rw [Nat.cast_sub hj2] at s2
    have t1 : (D.R.m : ℝ) * L.etaSz ≤ D.R.k * L.etaSz := mul_le_mul_of_nonneg_right hmkR he.le
    push_cast at s1 s2
    nlinarith
  have hmain : (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤
      (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) := by
    unfold WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hτ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    apply le_of_eq
    ring
  refine ⟨hmain, fun i => ?_⟩
  obtain ⟨Y, hY, -, -, hg⟩ := Pm.g_Y
  refine lt_of_le_of_lt (hmain.trans ?_) (four_sq_lt_of_eighth hkR hb (hY.trans (hg i).1))
  have u1 : (D.R.f : ℝ) * (L.Sc + L.etaSz) ≤ D.R.f * (2 * L.sc.b) := mul_le_mul_of_nonneg_left hSe hf0
  have u2 : (D.R.f : ℝ) * L.sc.b ≤ D.R.k * L.sc.b := mul_le_mul_of_nonneg_right hfk (by linarith)
  calc _ ≤ (D.R.k : ℝ) * (4 * (D.R.k * L.sc.b)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = _ := by ring

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthAtTwoOfUnscaledDepthBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthTwo_of_unscaled_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N Nd hE hσ hT hpr hsp hPg tF tP hB
  have hT0 : (0 : ℝ) ≤ O.T := by rw [hT]; positivity
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), plc v ∈ O.sm →
      (1 ≤ DepthTie.e1 c v ∧ 1 ≤ DepthTie.e2 c v ∧ ramw v = (DepthTie.e1 c v : ℤ) * (DepthTie.e2 c v : ℤ) ∧
        ∀ j, (O.E v j : ℤ) ≤ (DepthTie.e1 c v : ℤ) *
          ⌈(DepthTie.e2 c v : ℝ) * O.T * (DepthTie.nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ O.sC j + O.T + 1 := by
    intro v j hv ⟨he1, he2, hram, hEv⟩
    have hbad : plc v ∈ O.Bad := by simp [OnObj.Bad, hv]
    have hEj := hEv j
    rw [if_pos hbad] at hEj
    have hR := rounding_condition_holds (DepthTie.e1 c v) (DepthTie.e2 c v) (O.T * (DepthTie.nuT Xo c Dd ι v j + 1))
      (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hEj)
    have hramR : (ramw v : ℝ) = (DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ) := by simp [hram]
    have he2R : (1 : ℝ) ≤ DepthTie.e2 c v := by exact_mod_cast he2
    have hinv : 1 / (DepthTie.e2 c v : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact he2R
    have hs1 := GlobalTheory.RunDepth.sprime_nonneg_two E H l Dw Xo c Dd K Bs Df S P oc O ι hT hpr hσ hsp hPg v hv j
    obtain ⟨B, hTB, hν⟩ := hB (placeBelow (K := c.F) v) (by rw [DepthTie.resChar_below (F := c.F) v]; exact hv) j
    have hW : DepthTie.nuWT Xo c Dd ι v j ≤ B := by
      have h0 : (0 : EReal) ≤ nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j) := le_max_left _ _
      have ht := EReal.toReal_le_toReal hν (ne_bot_of_le_ne_bot EReal.zero_ne_bot h0) (EReal.coe_ne_top _)
      rw [EReal.toReal_coe] at ht
      unfold DepthTie.nuWT
      rw [div_le_iff₀ (by linarith), mul_comm]
      exact ht
    have hTW := mul_le_mul_of_nonneg_left hW hT0
    have he0 : O.e0 v j = (O.E v j : ℝ) / ((DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ)) -
        (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) := by
      unfold OnObj.e0
      rw [sub_div, hramR]
    unfold DepthTie.s1T DepthTie.sWT at hs1
    rw [he0]
    nlinarith
  intro w hw h2 j
  obtain ⟨h1, h1'⟩ := DepthTie.tieE Xo c Dd O ι hE hT hpr w hw
  exact ⟨key w j h2 h1, key (Formalism.DivisionValues.conjPl w) j (by rw [plc_conjPl]; exact h2) h1', content_zero_at_small_primes N O Nd ι hPg tF tP w h2 j⟩

end GlobalTheory.RunDepth
end

