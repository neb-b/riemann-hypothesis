module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficients
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem thmT_descend : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  intro l _ Pl K' h hN hF hS LL LL' hL C hT
  intro T₁ T₂ F N η H U Sig Fr hp1 hp2 hon hFr hFS h1 hcard h2N hI1 hI2 hU h0U hUc hη hηH hJ1 hJ2 hl
  obtain ⟨k₁, b₁, hb₁⟩ := _root_.GlobalTheory.BaseCoef.lattice_basis_exists l LL T₁
  obtain ⟨k₂, b₂, hb₂⟩ := _root_.GlobalTheory.BaseCoef.lattice_basis_exists l LL T₂
  obtain ⟨r, hr1, hr2, hr3⟩ := _root_.GlobalTheory.CoefRetraction.exists_integral_retraction l LL LL' hL
  obtain ⟨hFS', hrP, hcard', h1'⟩ := _root_.GlobalTheory.BaseCoef.mapSig_props (incl hL).toRingHom (pc Pl h hN hF hS).Iner Fr Sig
  have key := hT (extLat hL T₁ b₁ hb₁) (extLat hL T₂ b₂ hb₂) (extHom hL hb₁ hb₂ F) N η H U
    (mapSig (incl hL).toRingHom Sig) Fr
    (_root_.GlobalTheory.BaseCoef.isPotCrys_extLat l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ hp1) (_root_.GlobalTheory.BaseCoef.isPotCrys_extLat l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ hp2)
    (_root_.GlobalTheory.BaseCoef.extHom_onto l LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hon) hFr (hFS' hFS) (h1' h1) (hcard'.trans hcard) h2N
    (_root_.GlobalTheory.BaseCoefIner.main l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ Sig hI1) (_root_.GlobalTheory.BaseCoefIner.main l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ Sig hI2)
    hU h0U hUc hη hηH
    (_root_.GlobalTheory.BaseCoef.jumpsInV_extLat l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ _ hJ1) (_root_.GlobalTheory.BaseCoef.jumpsInV_extLat l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ _ hJ2) hl
  rw [hrP] at key
  exact ⟨key.1, _root_.GlobalTheory.CoefDescent.liftF_descends l _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr1 hr2 hr3 (by haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2; exact LinearMap.continuous_of_finiteDimensional r) _ key.2⟩

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.LocInputs


open TensorProduct in
theorem _root_.GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler :
    _root_.Formalism.GaloisCohomology.LocalTateDualityK → _root_.Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : _root_.Formalism.BasicNotions.D7) (HW : _root_.Formalism.BasicNotions.HWOf D.loc) (F : _root_.Formalism.BasicNotions.FonOf D.loc D.locA HW),
        ∃ _J : _root_.Formalism.MainNotions.LocalSituation.Ties D.loc D.locA HW F, _root_.Formalism.MainNotions.LocalSituation.admitted D HW F := by
  intro hduality heuler D HW F
  refine ⟨⟨fun l _ => (_root_.GlobalTheory.ThetaTie.nonempty_thetaL D l).some⟩, ?_⟩
  refine ⟨?_, hduality, _root_.GlobalTheory.TateTop.tate_h2_of_local_duality hduality D, heuler,
    _root_.GlobalTheory.TateFilQuot.tate_fil_quot D, _root_.GlobalTheory.FundCont.fundamentalExactSequence_continuity_all_theories D,
    _root_.GlobalTheory.Per.FontaineAll.fontaine_bounds D, _root_.GlobalTheory.TateDualFil.main D, ?_⟩
  · refine _root_.GlobalTheory.FundSeq.surjective_half_of_onto (fun l _ => ?_) D
    obtain ⟨C⟩ := _root_.GlobalTheory.MemLoc.nonempty_core l
    exact _root_.GlobalTheory.FundSeq.ontoAt_of_core C
      (_root_.GlobalTheory.MemLoc.one_sub_phi_onto l C) (_root_.GlobalTheory.MemLoc.FundOnto.fundOnto l C)
  · intro l _ K s LL h
    exact ⟨_root_.GlobalTheory.Cyc.FontW.main D HW F l K s LL h,
      _root_.GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.LocInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZero
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.HubX.InvariantsNoJump

theorem mem_Jset_of_isJumpV (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (ha : IsJumpV S.PD Y.ρ τ a) : a ∈ LocalSituation.Jset S Y := by
  intro heq
  apply ha
  unfold FildR DdRE
  rw [inf_right_comm, heq, inf_right_comm]

theorem two_add_sum_jumps_le_intervalExponent (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (l m vd : ℕ)
    (hfin : (LocalSituation.Jset S Y).Finite) (h0 : ¬ IsJumpV S.PD Y.ρ τ 0) :
    2 + ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤ LocalSituation.cLL l m vd (LocalSituation.Jset S Y) 0 1 := by
  classical
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  unfold LocalSituation.cLL LocalSituation.rI
  rw [hI, Finset.sum_singleton]
  simp only [sub_zero]
  have hle : ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤
      ∑ᶠ (u : ℤ) (_ : u ∈ LocalSituation.Jset S Y) (_ : u ≠ 0), (m + LocalSituation.vZ l u) := by
    simp only [finsum_eq_if]
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    rotate_left
    all_goals try
      intro u hu
      rw [Set.Finite.coe_toFinset]
      by_contra hn
      have hn' : ¬ IsJumpV S.PD Y.ρ τ u := fun hj => hn (mem_Jset_of_isJumpV S Y τ u hj)
      apply hu
      simp [hn, hn']
    apply Finset.sum_le_sum
    · intro u _
      by_cases hj : IsJumpV S.PD Y.ρ τ u
      · have hu0 : u ≠ 0 := by rintro rfl; exact h0 hj
        simp only [if_pos hj, if_pos (mem_Jset_of_isJumpV S Y τ u hj), if_pos hu0, le_refl]
      · simp only [if_neg hj]
        exact Nat.zero_le _
  omega

end GlobalTheory.HubX.InvariantsNoJump

namespace GlobalTheory.HubX.InvariantsNoJump

theorem torsion_exponent_kills_invariants_no_jump_zero : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  intro _ _ _ D HW F _ l _ K s LL h S M0 h0 T hW hJ x hx
  have hat := GlobalTheory.T.invariants_vanish_at_prime_of_admissible D HW F (GlobalTheory.Per.FontaineAll.fontaine_bounds D) l K s LL h
  have hp : LocalSituation.ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hcard := Formalism.MainNotions.N.JsetEmb.card_emb_good h
  have hpos : 0 < Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    rw [hcard]; exact Module.finrank_pos
  obtain ⟨τ⟩ := (Nat.card_pos_iff.1 hpos).1
  have key := hat M0 h0 T τ hW (hJ τ) x hx
  have hfin : (LocalSituation.Jset S T).Finite :=
    (Set.finite_Icc (-(M0 : ℤ)) h0).subset fun a ha => hW.2.1 a ha
  have hle : LocalSituation.c0 S T τ M0 h0 ≤ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T := by
    unfold LocalSituation.c0
    rw [hp, hs]
    exact two_add_sum_jumps_le_intervalExponent S T τ l _ _ hfin (hJ τ)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm, mul_smul, key, smul_zero]

end GlobalTheory.HubX.InvariantsNoJump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem window_cLL_of_jumps_level_one (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (l h r n v : ℕ)
    [CharZero S.Qp] [FiniteDimensional S.Qp S.K] (hl : l.Prime)
    (hcard : Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K) (hn : finrank S.Qp S.K ≤ n) (hr : 1 ≤ r)
    (hv : v ≤ LocalSituation.mN l 1 (h + h) - 1)
    (hU : ∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
      ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) :
    (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧
      LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v (LocalSituation.Jset S Y) 0 1 ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := GlobalTheory.HubLoc.jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  exact ⟨fun a ha => hb a (Finset.mem_coe.1 (hsub ha)),
    GlobalTheory.HubLoc.cLL_unit_interval_le l h (n * r) v _ _ hl (Nat.mul_pos (by omega) hr) hsub hc hb hv⟩

theorem cH0all_le_of_jumps_at_embeddings : ∀ (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hs : Good K 1 LL) (h r n : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K 1 LL hs).G (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).LL (LocalSituation.sit LT HW l (AI l) K 1 LL hs).O), K.1 ≤ MaximalUnramifiedExtension l → finrank ℚ_[l] ↥K.1 ≤ n → 1 ≤ r → (∀ τ, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ a, IsJumpV (LocalSituation.sit LT HW l (AI l) K 1 LL hs).PD T.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ GlobalTheory.HubX.invariantsCountConstant LT HW AI l K 1 LL hs h h T ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  intro LT HW AI l _ K LL hs h r n T hK hn hr hU
  have hl : l.Prime := Fact.out

  have hK1 : K.1 ≤ Ks K 1 := GlobalTheory.HubLoc.le_Ks_one_of_Kur K hK
  have hsplit : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1 := by
    intro τ x
    have e := hs.2.2.2 ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩
    have e2 : τ.liftNormal (Om l) (algebraMap ↥K.1 (Om l) x) = algebraMap (Om l) (Om l) (τ x) :=
      AlgHom.liftNormal_commutes τ (Om l) x
    have e3 : ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩ = τ x := e2
    rwa [e3] at e
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := GlobalTheory.HubLoc.card_emb K LL hsplit
  have := K.2
  have hm : 0 < LocalSituation.mN l 1 (h + h) := by unfold LocalSituation.mN; omega
  obtain ⟨h1, h2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks l K
  have e1 := h1 _ hm
  have e2 := h2 hK
  have hv : padicValNat l (finrank ℚ_[l] ↥(Ks K (LocalSituation.mN l 1 (h + h)))) - padicValNat l (finrank ℚ_[l] ↥K.1) ≤
      LocalSituation.mN l 1 (h + h) - 1 := by omega
  haveI : CharZero (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp := (inferInstance : CharZero ℚ_[l])
  haveI : FiniteDimensional (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).K :=
    (inferInstance : FiniteDimensional ℚ_[l] ↥K.1)
  exact window_cLL_of_jumps_level_one (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T l h r n _ hl hcard hn hr hv hU

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
section
open Formalism.MainNotions.N

namespace GlobalTheory.TraceSemisimple

theorem trace_nondegenerate_of_isSSRep {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (hρ : IsSSRep ρ) (x : Matrix (Fin n) (Fin n) k) (hx : x ∈ spanAlg ρ)
    (htr : ∀ g, (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).trace = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4; revert Γ k h_2 h_3 h_4 n ρ hρ x hx htr; exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate)
  | exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | (apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate ..)

theorem isSSRep_mapRep :
    ∀ (Γ k k' : Type) [Group Γ] [Field k] [Field k'] [CharZero k] (ι : k →+* k') (n : ℕ)
      (ρ : Γ →* GL (Fin n) k), IsSSRep ρ → IsSSRep (mapRep ι ρ) := by
  intro Γ k k' _ _ _ _ ι n ρ hρ
  let _ : Algebra k k' := ι.toAlgebra
  have hφι : ∀ (φ : k' →ₗ[k] k) (c : k') (r : k), φ (c * ι r) = φ c * r := by
    intro φ c r
    rw [mul_comm c, mul_comm (φ c), ← smul_eq_mul r, ← map_smul]
    rfl
  have hent : ∀ g i j, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') i j =
      ι (((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := fun _ _ _ => rfl
  apply isSSRep_of_trace_nondegenerate
  intro x hx htr
  have hmem : ∀ φ : k' →ₗ[k] k, x.map φ ∈ spanAlg ρ := by
    clear htr
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      intro φ
      have : ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k').map φ =
          φ 1 • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
        ext i j
        rw [Matrix.map_apply, hent, Matrix.smul_apply, smul_eq_mul, ← hφι, one_mul]
      rw [this]
      exact (spanAlg ρ).smul_mem (Submodule.subset_span ⟨g, rfl⟩) _
    | zero =>
      intro φ
      have : (0 : Matrix (Fin n) (Fin n) k').map φ = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      intro φ
      have : (y + z).map φ = y.map φ + z.map φ := by ext i j; simp
      rw [this]; exact add_mem (hy φ) (hz φ)
    | smul c y _ hy =>
      intro φ
      exact hy (φ ∘ₗ LinearMap.mulLeft k c)
  have hzero : ∀ φ : k' →ₗ[k] k, x.map φ = 0 := by
    intro φ
    refine trace_nondegenerate_of_isSSRep ρ hρ _ (hmem φ) fun g => ?_
    have := congrArg φ (htr g)
    rw [map_zero] at this
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, hent, hφι, Matrix.map_apply]
  ext i j
  rw [Matrix.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  exact congrFun (congrFun (hzero φ) i) j

end GlobalTheory.TraceSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRhoConjLatTpsi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem twist_conj {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin k) B) (ρ₀ : Γ →* GL (Fin k) A) (χ₀ : Γ →* Aˣ) (ψ χ : Γ →* Bˣ)
    (hχ : χ = (Units.map (f : A →* B)).comp χ₀ * ψ) (U : GL (Fin k) B)
    (hU : ∀ g, mapRep f ρ₀ g * U = U * ρ g) (g : Γ) :
    twistM ((Units.coeHom _).comp ρ) χ⁻¹ g * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        twistM (mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹)) ψ⁻¹ g := by
  have h1 : ρ g * U⁻¹ = U⁻¹ * mapRep f ρ₀ g := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hU, mul_inv_cancel_right]
  have h2 : ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := congrArg Units.val h1
  have h3 : mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g =
      f (((χ₀ g)⁻¹ : Aˣ) : A) • ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := by
    ext i j
    exact map_mul f _ _
  have h4 : (((χ g)⁻¹ : Bˣ) : B) = (((ψ g)⁻¹ : Bˣ) : B) * f (((χ₀ g)⁻¹ : Aˣ) : A) := by
    rw [hχ, MonoidHom.mul_apply, mul_inv_rev, Units.val_mul, MonoidHom.comp_apply, ← map_inv]
    rfl
  change ((((χ g)⁻¹ : Bˣ) : B) • ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)) * _ =
    _ * ((((ψ g)⁻¹ : Bˣ) : B) • mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g)
  rw [h3, smul_smul, ← h4, Matrix.smul_mul, Matrix.mul_smul, h2]

theorem twistedRho_conj_latTpsi : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π) → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → AbsIrrSub (redRep D.nd a (ρ π)) ⊤ → ∃ U : GL (Fin D.R.r) (D.nd.O a), ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) = (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g := by
  intro hC D a π ρ s Sg hρ hP hT hirr
  have htr := _root_.GlobalTheory.TripleTrace.trace_eq hC D a π (ρ π) s Sg hρ hP hT
  obtain ⟨U, hU⟩ := _root_.GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq (D.nd.O a) (Formalism.MainNotions.N.GE D.nd) D.R.r (ρ π)
    (mapRep (D.ntw.twist₂ a) (D.ntw.rhoS _ s)) hirr (fun g => by
      rw [htr g]
      exact (AddMonoidHom.map_trace (D.ntw.twist₂ a) _))
  refine ⟨U⁻¹, fun g => ?_⟩
  refine twist_conj (D.ntw.twist₂ a) (ρ π) (D.ntw.rhoS _ s) _ (D.ntw.psiL a) (D.nd.chi a 1) ?_ U hU g
  rw [hT.1, hT.2.1]
  exact D.ntw.chi_tw a

end GlobalTheory.PtCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPow
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem zero_mem_QSet_goodU : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp

theorem uPow_mem_QSet_goodU [CharZero K] (m : ℕ) :
    (fun _ => C (X ^ m) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, m) then ((dpDen e 0 m : ℕ) : Wq l a) else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases h : (i, n) = (0, m)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have : (dpDen e 0 n : K) ≠ 0 := Nat.cast_ne_zero.mpr (dpDen_pos e 0 n).ne'
    simp only [if_true, map_natCast, coeff_X_pow_self]
    exact div_self this
  · rw [if_neg h]
    simp only [map_zero, zero_div]
    by_cases hi : i = 0
    · subst hi
      have hn : n ≠ m := fun hn => h (by rw [hn])
      rw [if_pos rfl, coeff_X_pow, if_neg hn]
    · rw [if_neg hi, map_zero]

end

theorem uFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hf : frob2 φ₂ (uFam a K) = (fun _ => C (X ^ l) : ZMod a → K⟦X⟧⟦X⟧) := by
    funext τ
    show φ₂ (C X) = _
    rw [hC, frob_X]
  refine ⟨?_, ?_, 0, zero_mem_QSet_goodU t K e, ?_⟩
  · have := uPow_mem_QSet_goodU t K e 1
    rw [pow_one] at this
    exact this
  · rw [hf]; exact uPow_mem_QSet_goodU t K e l
  · rw [hf, mul_zero, add_zero]
    funext τ
    simp [uFam]

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPower
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CokerFin


set_option maxHeartbeats 1000000 in
theorem coker_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  intro D HW F Cm l _ K s LL h W E C T₀ T₁ T₂ ι π h0 h1 h2 hs
  have hP : WachCharacterisationLattice W := _root_.GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F l K s LL h
  have hp10 : p10 W T₂ := hP T₂ h2
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hfl : Module.Flat (AA K LL) W.EE :=
    _root_.GlobalTheory.flat_letA_of_dense_sat ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) ((D.loc l).PD K).p W.EE W.EE_π
      W.EE_complete W.EE_dense W.EE_sat
  obtain ⟨hfree, hbc⟩ := GlobalTheory.T.wachSaturation_image_free_and_spans D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hs hfl
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.saturation_gamma_stable_of_good D HW F l K s LL h T₁ T₂ π h1 h2
  have hS := hp10 _ hfree hbc hg1 hg2 (GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power D HW F l K s LL h T₁ T₂ π h1 h2)
    (GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span D HW F l K s LL h T₁ T₂ π h1 h2 hfree hbc)
  obtain ⟨c, hc⟩ := GlobalTheory.NL.Coker.uniform (W.N_fg T₂) hS.ge
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩ := hc z hz
  exact ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩

end GlobalTheory.NL.CokerFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrimeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_good_reduction_at_prime : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  first | exact @GlobalTheory.TwistTors.twist_torsion_facts | exact GlobalTheory.TwistTors.twist_torsion_facts | (intros; apply GlobalTheory.TwistTors.twist_torsion_facts <;> assumption)
end

