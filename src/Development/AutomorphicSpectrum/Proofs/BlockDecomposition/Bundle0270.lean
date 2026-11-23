module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0162
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
public import GroundTheory.PAdicHodge.ACrisBdRGalois

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetShalikaBoundOfSteps
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatakeBound

theorem jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound := by
  intro h10 h11 h11b h12 g1 g2 g3 g4 E _ _ _ a π hU w B hB α hα
  obtain ⟨L, rfl⟩ : ∃ L : List ℂˣ, (L : Multiset ℂˣ) = B := ⟨B.toList, Multiset.coe_toList B⟩
  have hcard : L.length = a := by simpa using hB.card
  subst hcard
  have hBz : (L : Multiset ℂˣ) = Finset.univ.val.map L.get := by rw [Fin.univ_val_map, List.ofFn_get]
  obtain ⟨i, rfl⟩ : ∃ i, L.get i = α := List.mem_iff_get.1 (Multiset.mem_coe.1 hα)
  have ha : 1 ≤ L.length := Fin.pos i
  induction π using Quotient.inductionOn with | _ π => ?_
  set z := L.get with hz
  let F := w.adicCompletion E
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  have hB' : HasSatGL w (π.locRep w) (Finset.univ.val.map z) := by rw [← hBz]; exact hB
  obtain ⟨ψ, hψ, l, hl0, hW⟩ := g4 E L.length ha π w
  obtain ⟨v, g, hv, hlv⟩ := g2 E L.length π w _ hB' l hl0
  obtain ⟨Bf, hBf⟩ := g1 E L.length π hU w
  have hs := g3 E L.length π w
  obtain ⟨hq, h12'⟩ := h12 E w
  have hH : Heig (π.locRep w) v z := h12' L.length π.V (π.locRep w) v z hv
  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hpair := h11b L.length z (h11 F L.length π.V (π.locRep w) Bf hBf v z hv.1 hH)
  have hup : ∀ j, ‖(z j : ℂ)‖ < Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) := by
    intro j
    rcases Nat.lt_or_ge 1 L.length with h2 | h1
    · have := h10 F Measure.addHaar ψ hψ L.length π.V (π.locRep w) hs h2 l Bf hW hBf v z hH ⟨g, hlv⟩ j
      rwa [hq] at this
    · obtain ⟨k, hk⟩ := hpair j
      have hkj : k = j := Fin.ext (by have := k.2; have := j.2; omega)
      subst hkj
      have h0 : ‖(z k : ℂ)‖ = 1 := by
        have h00 : 0 ≤ ‖(z k : ℂ)‖ := norm_nonneg _
        nlinarith
      rw [h0, Real.lt_sqrt zero_le_one]
      simpa using hq1
  obtain ⟨k, hk⟩ := hpair i
  have hkpos : 0 < ‖(z k : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hi : ‖(z i : ℂ)‖ = ‖(z k : ℂ)‖⁻¹ := eq_inv_of_mul_eq_one_right hk
  have hsq : (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) :=
    (Real.sqrt_eq_rpow _).symm
  refine ⟨?_, ?_⟩
  · rw [Real.rpow_neg (by positivity), hsq, hi]
    exact inv_strictAnti₀ hkpos (hup k)
  · rw [hsq]; exact hup i

end GlobalTheory.CompanionTheory.SatakeBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMem
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_fk (l : ℕ) [Fact l.Prime] (k : ℕ) (w : Ainf l) :
    Lat.dk l k (Lat.fk l (k + 1) w) = Lat.fk l k w := by
  simp only [Lat.dk, Lat.fk, RingHom.comp_apply]
  exact Ideal.Quotient.factor_mk _ _

theorem dk_dpE (l : ℕ) [Fact l.Prime] (M k i : ℕ) :
    Lat.dk l k (Lat.dpE (Lat.fk l (k + 1)) (xi0 l) l M i) = Lat.dpE (Lat.fk l k) (xi0 l) l M i := by
  simp only [Lat.dpE, Lat.η, map_rat_smul, map_pow, dk_fk]

theorem dk_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) :
    ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro x hx
  have hle : Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M ≤
      (Lat.sub (Lat.fk l k) (xi0 l) l M).comap (Lat.dk l k) := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_fk]
      exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_dpE]
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  exact hle hx

end GlobalTheory.CompanionTheory.LatLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPow
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatPdpB

variable (l : ℕ) [Fact l.Prime]

theorem span_xi_eq_span_fontaine_t :
    Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)} = Ideal.span {tBdR l} := by
  haveI : IsPerfectoidField ℂ_[l] l := IsPerfectoidField.padicComplex l
  have hg := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  generalize IsPerfectoidField.kerThetaGenerator ℂ_[l] l = g at hg
  have hnorm : ∀ z : normInteger ℂ_[l], ‖(z : ℂ_[l])‖ ≤ 1 := fun z => mem_normInteger.1 z.2
  have hbound : ∀ w : WittVector l (PreTilt (normInteger ℂ_[l]) l),
      WittVector.fontaineTheta (normInteger ℂ_[l]) l w = 0 →
      ‖((PreTilt.untilt (WittVector.constantCoeff w) : normInteger ℂ_[l]) : ℂ_[l])‖ ≤
        ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
    intro w hw
    have h1 : Ideal.Quotient.mk (Ideal.span {(l : normInteger ℂ_[l])})
        (PreTilt.untilt (WittVector.constantCoeff w)) = 0 := by
      rw [PreTilt.mk_untilt_eq_coeff_zero]
      have h2 := WittVector.mk_fontaineTheta (R := normInteger ℂ_[l]) (p := l) w
      rw [hw, map_zero] at h2
      exact h2.symm
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    rw [← hz, Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hnorm z)
  have hx : xi0 l ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := by
    rw [RingHom.mem_ker, CrystallineSemistableComparison.xi0, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller,
      untilt_pFlat, sub_self]
  rw [hg, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  have hg0 : WittVector.fontaineTheta (normInteger ℂ_[l]) l g = 0 := by
    rw [← RingHom.mem_ker, hg]
    exact Ideal.mem_span_singleton_self g
  have hcn : WittVector.fontaineTheta (normInteger ℂ_[l]) l c ≠ 0 := by
    intro hc0
    have hcm : c ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := hc0
    rw [hg, Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, hd⟩ := hcm
    have hxe : xi0 l = d * g * g := by rw [← hc, ← hd]
    have hco := congrArg WittVector.constantCoeff hxe
    have hT : WittVector.constantCoeff (WittVector.teichmuller l (pFlat l)) = pFlat l :=
      WittVector.teichmuller_coeff_zero l _
    rw [CrystallineSemistableComparison.xi0, map_sub, map_natCast, hT, map_mul, map_mul,
      CharP.cast_eq_zero (PreTilt (normInteger ℂ_[l]) l) l, zero_sub] at hco
    have hpf : pFlat l = (-WittVector.constantCoeff d) * WittVector.constantCoeff g *
        WittVector.constantCoeff g := by
      rw [neg_mul, neg_mul, ← hco, neg_neg]
    have hu := congrArg (fun y => ‖((PreTilt.untilt y : normInteger ℂ_[l]) : ℂ_[l])‖) hpf
    simp only [map_mul, Subring.coe_mul, norm_mul, untilt_pFlat] at hu
    have hb := hbound g hg0
    have hd1 := hnorm (PreTilt.untilt (-WittVector.constantCoeff d))
    have hpos : 0 < ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
      rw [norm_pos_iff]; push_cast; exact natCast_p_ne_zero_cp
    have hlt : ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ < 1 :=
      IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l
    have hn0 := norm_nonneg ((PreTilt.untilt (WittVector.constantCoeff g) : normInteger ℂ_[l]) : ℂ_[l])
    have hn1 := norm_nonneg ((PreTilt.untilt (-WittVector.constantCoeff d) : normInteger ℂ_[l]) : ℂ_[l])
    nlinarith [mul_le_mul hb hb hn0 hpos.le, mul_le_mul_of_nonneg_right hd1 (mul_nonneg hn0 hn0),
      mul_lt_of_lt_one_left hpos hlt]
  have hcu : IsUnit (wittToBDeRhamPlus (normInteger ℂ_[l]) l c) := by
    by_contra hnu
    have hm : wittToBDeRhamPlus (normInteger ℂ_[l]) l c ∈
        IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at hm
    exact hcn (by exact_mod_cast hm)
  rw [← hc, map_mul, Ideal.span_singleton_mul_left_unit hcu,
    ← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hg, maximalIdeal_eq_span_tBdR]

theorem span_fk_pow (k r : ℕ) :
    Ideal.span {fk l k (xi0 l) ^ r} = Ideal.span {pk l k (tBdR l) ^ r} := by
  have h2 : Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l) ^ r} =
      Ideal.span {tBdR l ^ r} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, span_xi_eq_span_fontaine_t]
  have h3 := congrArg (Ideal.map (pk l k)) h2
  simp only [Ideal.map_span, Set.image_singleton, map_pow] at h3
  exact h3

theorem pInv_eq_tBdR {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (t : (per l K).P)
    (ht : (t : (per l K).B) = (per l K).tB) : pInv l t = tBdR l := by
  have hi : GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l) = tBdR l :=
    GroundTheory.PAdicHodge.ACris.iota_periodT (ε := epsilon l) untilt_epsilon
  have key : (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).rangeRestrict (tBdR l) = t := by
    apply Subtype.ext
    refine Eq.trans ?_ ht.symm
    show algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (tBdR l) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
        (GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l))
    rw [hi]
  rw [← key]
  unfold CrystallineSemistableComparison.Pb.Lat.pInv
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (RingEquiv.symm_apply_eq _).2 rfl

end GlobalTheory.CompanionTheory.LatPdpB


open GlobalTheory.CompanionTheory.LatPdpB in
theorem GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  intro l _ K M h k r t ht
  show pdP (γB (fk l k) (xi0 l)) r = Ideal.span {(pk l k) (pInv l t) ^ r}
  rw [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB, pInv_eq_tBdR l t ht, span_fk_pow]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesField
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem sigmaB_fixes_K {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : ∀ g (a : K),
    (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  intro g a
  have key : gP l g (kP l K a) = kP l K a := by
    have h1 : galBdRHom (toBot g.1) (algClToBdR l (a : PadicAlgCl l))
        = algClToBdR l ((toBot g.1) (a : PadicAlgCl l)) :=
      gal_smul_algClToBdR (toBot g.1) (a : PadicAlgCl l)
    have h2 : (toBot g.1) (a : PadicAlgCl l) = (a : PadicAlgCl l) := g.2 a
    rw [h2] at h1
    exact h1
  change gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  change Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = Ideal.Quotient.mk _ (kP l K a)
  rw [Ideal.quotientMap_mk, key]

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegers
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem gP_kP {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (x : K) : gP l g (kP l K x) = kP l K x := by
  have h1 : (toBot g.1) • algClToBdR l (K.val x) = algClToBdR l ((toBot g.1) (K.val x)) :=
    gal_smul_algClToBdR _ _
  have h2 : (toBot g.1) (K.val x) = K.val x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ x.2
  rw [h2] at h1
  exact h1

theorem sigA_fix : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  intro l _ K M h k g a
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  show Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = _
  rw [Ideal.quotientMap_mk, gP_kP]
  rfl

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphism
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatSigDP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem exists_gB_xi (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    ∃ u : Ainf l, gB h k g (fk l k (xi0 l)) = fk l k (u * xi0 l) := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.TwFil.exists_gal_xi (toBot g.1)
  refine ⟨u, ?_⟩
  have e : galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (u * xi0 l) := by
    rw [← hu, ← gal_smul_wittToBDeRhamPlus]
    rfl
  show Ideal.Quotient.mk _ (galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l))) = _
  rw [e]
  rfl

theorem sigA_isDPMorphism (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  obtain ⟨u, hu⟩ := exists_gB_xi h k g
  exact GlobalTheory.CompanionTheory.LatDP.isDPMorphism_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) u hu
    (h.hc k) (h.hc k)

end GlobalTheory.CompanionTheory.LatSigDP
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMap
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_IB_eq_map {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  have key : IB (fk l k) (xi0 l) = (I (fk l k) (xi0 l) l M).map (ι (fk l k) (xi0 l) l M) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨⟩
      have hm : ofW (fk l k) (xi0 l) l M (xi0 l) ∈ I (fk l k) (xi0 l) l M := by
        show ι (fk l k) (xi0 l) l M (ofW (fk l k) (xi0 l) l M (xi0 l)) ∈ IB (fk l k) (xi0 l)
        rw [ι_ofW]
        exact Ideal.subset_span rfl
      have := Ideal.mem_map_of_mem (ι (fk l k) (xi0 l) l M) hm
      rwa [ι_ofW] at this
    · exact Ideal.map_comap_le
  exact key

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToB
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem algebraMap_pInv {l : ℕ} [Fact l.Prime] (z : ↥(algebraMap (BdRp l) (BdR l)).range) :
    algebraMap (BdRp l) (BdR l) (pInv l z) = z.1 :=
  congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply z)

theorem iota_lam_eq_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c →
      (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  intro c y hy
  have h1 : (lev h k).ι ((lev h k).lam c) = pk l k (ACris.iota ℂ_[l] l c) := rfl
  have h2 : (lev h k).toB y = pk l k (pInv l y) := rfl
  rw [h1, h2]
  congr 1
  apply IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  exact hy.symm.trans (algebraMap_pInv y).symm

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariant
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCSig

variable {p : ℕ} [Fact p.Prime] {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galCp_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[p] →+* ℂ_[p]) = (galCp τ : ℂ_[p] →+* ℂ_[p]) := by
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_galCp σ) (continuous_galCp τ)) fun a => ?_
  show galCp σ (a : ℂ_[p]) = galCp τ (a : ℂ_[p])
  rw [galCp_coe, galCp_coe, h]

theorem galMap_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

theorem galAway_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galAway σ = galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt (normInteger ℂ_[p]) p)))
    (RingHom.ext fun w => by
      simp only [RingHom.comp_apply, galAway_algebraMap]
      rw [AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

theorem galQuot_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) (n : ℕ) : galQuot σ n = galQuot τ n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk]
    rw [galAway_congr σ τ h])

theorem galBdRHom_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galBdRHom σ = galBdRHom τ :=
  RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, evalB_galBdRHom, galQuot_congr σ τ h]

theorem gP_iota {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (c : Acris l) :
    gP l g (ACris.iota ℂ_[l] l c) =
      ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c) := by
  have h := ACris.iota_gal_smul (IntermediateField.fixingSubgroupEquiv K g) c
  rw [ACris.gal_smul_def, gal_smul_bdR_def] at h
  rw [h]
  exact congrArg (fun f => f (ACris.iota ℂ_[l] l c))
    (galBdRHom_congr (toBot g.1) (IntermediateField.fixingSubgroupEquiv K g) fun y => rfl)

theorem sig_lam : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), ∀ g c,
    (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  intro l _ K M h k g c
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (ACris.iota ℂ_[l] l c)) =
    pk l k (ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c))
  rw [← gP_iota]
  exact Ideal.quotientMap_mk

end GlobalTheory.CompanionTheory.LatCSig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisA
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_gB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (x : Bk l (k + 1)) :
    dk l k (gB h (k + 1) g x) = gB h k g (dk l k x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [dk, gB, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

theorem levSys_dA_σA {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g a,
    (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  intro m g a
  apply Subtype.ext
  exact dk_gB h (m + 1) g a.1

end GlobalTheory.CompanionTheory.LatLevel
end
end

