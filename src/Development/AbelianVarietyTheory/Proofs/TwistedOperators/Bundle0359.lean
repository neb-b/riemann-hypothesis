module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceSubgroupLevelMemberClauses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct


set_option maxHeartbeats 4000000 in
theorem congLev_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  intro D c s 𝔪 h𝔪 hS hsd hJ
  have hΛ : Submodule.IsFullLattice D.host.E s.Λ :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice s.V s.Λ hsd
  obtain ⟨β, hβ⟩ := frame_exists_alt D.host.F D.host.E s.V.rank s.Λ hΛ
  have memJ : ∀ k, k ∈ s.J ↔ k ∈ GfC s.V ∧ Lev.finE s.V k ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 := by
    intro k; rw [hJ]; exact Iff.rfl
  have toSt : ∀ x, x ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 → x ∈ Formalism.L2.DIV.St β := fun x hx =>
    (GlobalTheory.LevSplit.mem_St_iff β s.Λ hβ x).2 (stab_of_mem_congLev hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; exact ((memJ k).1 hk).1
  · exact ⟨(congLev D.sp.cm s.V.gram s.Λ 𝔪).comap (Lev.finE s.V), (GlobalTheory.FunObj.congLev_open_compact s.V hΛ h𝔪).1,
      fun k hk hkf => (memJ k).2 ⟨hkf, hk⟩⟩
  · intro k hk v
    exact (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V β s.Λ hβ k).1 (toSt _ ((memJ k).1 hk).2) v
  · intro k hkf hint h1
    exact (memJ k).2 ⟨hkf, _root_.GlobalTheory.CongOff.finE_mem_congLev_of_off D s.V c.S 𝔪 h𝔪 hS k hkf hint h1⟩
  · intro P hP
    obtain ⟨T1, T2, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨e, f, hi⟩ := T2 P
    refine ⟨e, f, hi, fun g hg => ?_, fun _ _ _ => rfl⟩
    obtain ⟨hff, hcf, -, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, -, -⟩ := T1 f hff hcf
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hL0 : Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub s.V) = Formalism.L2.Herm.hatL (F := D.host.F) s.Λ := by
      congr 1; exact SetLike.coe_injective (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice s.V)
    rw [GlobalTheory.LevSplit.ksph_iff, hL0, SetLike.mem_coe, memJ]
    constructor
    · rintro ⟨hG, hK⟩
      exact ⟨hG, stab_of_mem_congLev hK⟩
    · rintro ⟨hG, h1, h2⟩
      have s1 := GlobalTheory.LevSplit.supp_fin s.V hg
      have s2 := GlobalTheory.LevSplit.supp_fin s.V ((hLf _).1 (Lf.inv_mem ((hLf _).2 hg)))
      rw [MonoidHom.map_inv] at s2
      rw [← hu] at s1 s2
      refine ⟨hG, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V g) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ s1.symm h1
      · exact cong_of_eq s.Λ ha u _ _ s2.symm h2
  · intro P e f hP hi k hk
    obtain ⟨T1, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨hff, hcf, hG, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, hsplit, -⟩ := T1 f hff hcf
    obtain ⟨⟨Lf', hLf'⟩, -, -⟩ := T1 (1 - f) (by rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero])
      (by rw [RingHom.map_sub, RingHom.map_one, hcf])
    obtain ⟨k₁, k₂, h1, h2, hk12⟩ := hsplit k
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hinv : SuppF s.V f k₁⁻¹ := (hLf _).1 (Lf.inv_mem ((hLf _).2 h1))
    have hinv' : SuppF s.V (1 - f) k₂⁻¹ := (hLf' _).1 (Lf'.inv_mem ((hLf' _).2 h2))
    have hφφ : GlobalTheory.LevSplit.finSw D f * GlobalTheory.LevSplit.finSw D f = GlobalTheory.LevSplit.finSw D f := by
      rw [← RingHom.map_mul, hff]
    rw [← hu] at hφφ
    have s1 := GlobalTheory.LevSplit.supp_fin s.V h1
    have s1' := GlobalTheory.LevSplit.supp_fin s.V hinv
    have s2 := GlobalTheory.LevSplit.supp_fin s.V h2
    have s2' := GlobalTheory.LevSplit.supp_fin s.V hinv'
    rw [MonoidHom.map_inv] at s1' s2'
    rw [RingHom.map_sub, RingHom.map_one] at s2 s2'
    rw [← hu] at s1 s1' s2 s2'
    obtain ⟨-, hkK⟩ := (memJ k).1 hk
    have hK' := stab_of_mem_congLev hkK
    have ek : Lev.finE s.V k = Lev.finE s.V k₁ * Lev.finE s.V k₂ := by rw [hk12, MonoidHom.map_mul]
    have m1 : k₁ ∈ s.J := by
      refine (memJ k₁).2 ⟨hG k₁ h1, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V k₁) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ (comp_sub_one _ hφφ _ _ _ s1 s2 (Or.inl (by rw [ek, Units.val_mul]))) hK'.1
      · exact cong_of_eq s.Λ ha u _ _
          (comp_sub_one _ hφφ _ _ _ s1' s2' (Or.inr (by rw [ek, _root_.mul_inv_rev, Units.val_mul]))) hK'.2
    refine ⟨k₁, m1, k₂, ?_, h1, h2, hk12⟩
    have : k₂ = k₁⁻¹ * k := by rw [hk12, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) hk

end GlobalTheory.CongMember
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacFix

open GlobalTheory.Hk3 GlobalTheory.WeilParts GlobalTheory.IdemSupport

variable {D : D7}

theorem infPart_eq_one {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {x : AE D}
    (hx : f * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := of_isPrimeIdem hΦ h
  have h1 := congrArg (infPart D) hx
  rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at h1
  exact h1

theorem exists_nonSplit {P : Pl D.host.E} (hP : Formalism.DivisionValues.conjPl P = P) :
    ∃ v ε, NonSplitAt D v ε ∧ ∀ e f, IsPrimeIdem P e f →
      e = algebraMap (AF D.host.F) (AE D) ε ∧ f = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hc : P = cP P := by
    refine (isConjPl_iff P P).1 fun c hc => ⟨cO D c, ?_, rfl⟩
    have h1 : cO D c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hd : IsDelta Φ P (algebraMap (AF D.host.F) (AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  refine ⟨_, ε, ⟨hε, ?_⟩, fun e f h => ?_⟩
  · rintro ⟨e, ⟨e1, e2, -⟩, e3⟩
    have key : ∀ a : AE D, a * a = a → algebraMap (AF D.host.F) (AE D) ε * a = a → Φ a P ≠ 0 → IsDelta Φ P a :=
      fun a a1 a2 a3 => ⟨by rw [← a2, RingHom.map_mul, h0, zero_mul],
        mul_left_cancel₀ a3 (by rw [← ev_mul, a1, mul_one]),
        fun Q hQ => by rw [← a2, ev_mul, hd.2.2 Q hQ, zero_mul]⟩
    have e1' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, e1]
    have hz : Φ e P * Φ (cA D e) P = 0 := by rw [← ev_mul, e2, ev_zero]
    have hs : Φ e P + Φ (cA D e) P = 1 := by rw [← ev_add, e3, hd.2.1]
    by_cases h : Φ e P = 0
    · have a := key (cA D e) e1' (by rw [← e3]; linear_combination e1' + e2)
        (by rw [h, zero_add] at hs; rw [hs]; exact one_ne_zero)
      have b := delta_conj hΦ a
      rw [cA_cA, ← hc] at b
      exact zero_ne_one (h.symm.trans b.2.1)
    · have a := key e e1 (by rw [← e3]; linear_combination e1 + e2) h
      have b := delta_conj hΦ a
      rw [← hc] at b
      rw [a.2.1, b.2.1, one_mul] at hz
      exact one_ne_zero hz
  · obtain ⟨k1, ε', k2, k3⟩ := of_isPrimeIdem hΦ h
    exact ⟨delta_unique hΦ k1 hd, by rw [k3, placeIdem_unique k2 hε]⟩

theorem isHalf_of_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun w => w = v) : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro i j
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w α
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => exact mul_zero _
  | add x x' _ _ h h' => rw [Matrix.add_apply, mul_add, h, h']
  | neg x _ h => rw [Matrix.neg_apply, mul_neg, h]

theorem vacFix_of_unrPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E) (hW : IsWeilDatumO ψ S T χS χT om)
    (uS : UnrPl P χS) (uT : UnrPl P χT) : VacFix ψ om P := by
  by_cases hP : Formalism.DivisionValues.conjPl P = P
  swap
  · exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace ψ S T χS χT om P hW hP uS uT).1
  obtain ⟨v, ε, hv, hu⟩ := exists_nonSplit hP
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, e', he⟩ := exists_isPrimeIdem hΦ P
  obtain ⟨rfl, rfl⟩ := hu e e' he
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  rintro f hf k ⟨hk, a, a', ha, sk⟩ k' ⟨hk', b, b', hb, sk'⟩
  rw [(hu a a' ha).2] at sk
  rw [(hu b b' hb).2] at sk'
  exact _root_.GlobalTheory.VacInert.fixesVacAt_of_unram D ψ hW.std S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
    χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv (uS _ _ he) (uT _ _ he) k k' sk sk'
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
      (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) v ε hv.1 k k'
      (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk.2.1) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk'.2.1))
    f hf.1 fun u hu => hf.2 _ _ he u
      (by
        rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hu
        exact GlobalTheory.PlaceModel.latO_le_top _ hu)
      (Or.inl (isHalf_of_mem hv.1 hu))

theorem unr_and_vacFix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → ∀ f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.UnrPl P μ' ∧ GlobalTheory.Hk3.UnrPl P (μ' * η'⁻¹) ∧ GlobalTheory.Hk3.VacFix R.ψ ω P := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hc i σ μ' η' H ω hW f₀ f B _ P hP
  have h0 := (_root_.GlobalTheory.UnrOffLevels.unrPl_of_good R F hc.lev A.μ0 P hP).2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have h1 : UnrPl P μ' := fun e f h x a b c => by
    refine (H.mu_cond x ⟨infPart_eq_one h a, b, c⟩).2 ?_
    have h2 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := h0 e f h x a b c
    rwa [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hc.lev.xi_base ▸ hc.lev.xi A.μ0) x, mul_one] at h2
  have h2 : UnrPl P (μ' * η'⁻¹) := fun e f h x a b c => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1 e f h x a b c, H.eta_unr x (infPart_eq_one h a) b c, inv_one, mul_one]
  exact ⟨h1, h2, vacFix_of_unrPl _ _ _ _ _ ω P hW h1 h2⟩

end GlobalTheory.ConjVacFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffPoincareSumOverRationalHomRealDirections
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSmooth

variable {D : D7}

theorem finite_rat_mem (m n : ℕ) (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  letI : IsTopologicalAddGroup (Mx D m n) := hg
  letI : T2Space (Mx D m n) := ht2
  letI : T1Space (Mx D m n) := T2Space.t1Space
  letI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem contDiff_of_additive {k : ℕ} (f : (Fin k → ℝ) → ℂ) (h0 : f 0 = 0) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hc : Continuous f) : ContDiff ℝ ∞ f :=
  GlobalTheory.WeilVacMove.contDiff_additive (⟨⟨f, h0⟩, hadd⟩ : (Fin k → ℝ) →+ ℂ) hc

def rmul {m n p : ℕ} (Q : Mx D n p) : Mx D m n →+ Mx D m p where
  toFun x := x ⬝ Q
  map_zero' := Matrix.zero_mul _
  map_add' x y := Matrix.add_mul _ _ _

theorem continuous_rmul {m n p : ℕ} (Q : Mx D n p) : Continuous (rmul (m := m) Q) :=
  continuous_id.matrix_mul continuous_const

theorem contDiff_psi_symplOH {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {k : ℕ}
    (A B : (Fin k → ℝ) →+ WO S T) (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ t, (A t).map (finPart D) = 0) (hB0 : ∀ t, (B t).map (finPart D) = 0) (c c' : WO S T) :
    ContDiff ℝ ∞ fun t => ψ (symplOH S T (c + A t) (c' + B t)) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hadd1 := GlobalTheory.WeilVacMove.symplOH_add_left S T
  have hadd2 := GlobalTheory.WeilVacMove.symplOH_add_right S T
  have hz1 := GlobalTheory.WeilVacMove.symplOH_zero_left S T
  have hz2 := GlobalTheory.WeilVacMove.symplOH_zero_right S T
  have h1 : ContDiff ℝ ∞ fun t => lam (symplOH S T c (B t)) :=
    contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add (f := _), hadd2, map_add (f := _)])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have h2 : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) c') :=
    contDiff_of_additive _ (by rw [map_zero, hz1, map_zero]) (fun x y => by rw [map_add (f := _), hadd1, map_add (f := _)])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const))
  have hQ : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) (B t)) := by
    let φ : (Fin k → ℝ) → ((Fin k → ℝ) →+ ℂ) := fun t =>
      { toFun := fun s => lam (symplOH S T (A s) (B t))
        map_zero' := by rw [map_zero, hz1, map_zero]
        map_add' := fun x y => by rw [map_add (f := _), hadd1, map_add (f := _)] }
    have hφ : ∀ t, Continuous (φ t) := fun t =>
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const)
    have e : (fun t => lam (symplOH S T (A t) (B t))) =
        fun t => ∑ i, t i • lam (symplOH S T (A fun j => if i = j then 1 else 0) (B t)) := by
      funext t
      exact LinearMap.pi_apply_eq_sum_univ ((φ t).toRealLinearMap (hφ t) : (Fin k → ℝ) →ₗ[ℝ] ℂ) t
    rw [e]
    refine ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ => ℝ) i).smul ?_
    exact contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add (f := _), hadd2, map_add (f := _)])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have e : ∀ t, ψ (symplOH S T (c + A t) (c' + B t)) = ψ (symplOH S T c c') *
      Complex.exp (lam (symplOH S T c (B t)) + lam (symplOH S T (A t) c') + lam (symplOH S T (A t) (B t))) := by
    intro t
    have hs : sndA D.host.F (symplOH S T c (B t) + symplOH S T (A t) c' + symplOH S T (A t) (B t)) = 0 := by
      rw [map_add (f := _), map_add (f := _), GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inr (hB0 t)),
        GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)), GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)),
        add_zero, add_zero]
    rw [hadd1, hadd2, hadd2, show ∀ a b c d : AF D.host.F, a + b + (c + d) = a + (b + c + d) from fun _ _ _ _ => by abel,
      AddChar.map_add_eq_mul, hlam _ hs, map_add, map_add]
  rw [show (fun t => ψ (symplOH S T (c + A t) (c' + B t))) = _ from funext e]
  exact contDiff_const.mul ((h1.add h2).add hQ).cexp

end GlobalTheory.BumpMixSmooth

namespace GlobalTheory.BumpMixSmooth

theorem poinX_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
    (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => poinX ψ d T β (w + L t) := by
  intro D ψ hψ S S₀ T ρ d β hβ k L hL hL0 w
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have hx : Continuous fun t => (w + L t) ⬝ d.jX := (continuous_const.add hL).matrix_mul continuous_const
  let lX := (rmul (m := T.rank) d.jX).comp L
  let lY := (rmul (m := T.rank) d.jY).comp L
  have hlX : Continuous lX := (continuous_rmul _).comp hL
  have hlY : Continuous lY := (continuous_rmul _).comp hL
  have hlX0 : ∀ t, (lX t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  have hlY0 : ∀ t, (lY t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  let A := (d.extX T).comp lX
  let B := (d.extY T).comp lY
  have hA : Continuous A := show Continuous fun t => lX t ⬝ d.pX from hlX.matrix_mul continuous_const
  have hB : Continuous B := show Continuous fun t => lY t ⬝ d.pY from hlY.matrix_mul continuous_const
  have hA0 : ∀ t, (A t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlX0 t) d.pX
  have hB0 : ∀ t, (B t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlY0 t) d.pY
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ContDiff ℝ ∞ fun t =>
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) := by
    intro γ
    have e : ∀ t, ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ) = ψ (symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ) + A t)
          (d.extY T (w ⬝ d.jY) + B t)) * β ((w ⬝ d.jX + rat γ) + lX t) := by
      intro t
      have hx' : (w + L t) ⬝ d.jX = w ⬝ d.jX + lX t := Matrix.add_mul _ _ _
      have hy' : (w + L t) ⬝ d.jY = w ⬝ d.jY + lY t := Matrix.add_mul _ _ _
      have e1 : d.extX T (w ⬝ d.jX + lX t + 2 • rat γ) = d.extX T (w ⬝ d.jX + 2 • rat γ) + A t := by
        rw [add_right_comm, map_add (f := _)]; rfl
      have e2 : d.extY T (w ⬝ d.jY + lY t) = d.extY T (w ⬝ d.jY) + B t := map_add _ _ _
      rw [hx', hy', ← d.symplOH_extX_extY T, e1, e2, add_right_comm (w ⬝ d.jX)]
    rw [show (fun t => ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ)) = _ from funext e]
    exact (contDiff_psi_symplOH hψ A B hA hB hA0 hB0 _ _).mul (hβ.smooth k lX hlX hlX0 _)
  rw [contDiff_iff_contDiffAt]
  intro t₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds t₀
  have hC : IsCompact ((fun p : Mx D T.rank ρ × Mx D T.rank ρ => p.1 - p.2) ''
      (tsupport β ×ˢ ((fun t => (w + L t) ⬝ d.jX) '' K))) :=
    (hβ.supp.isCompact.prod (hK.image hx)).image (continuous_fst.sub continuous_snd)
  have hF := finite_rat_mem T.rank ρ _ hC
  have hsum : ContDiff ℝ ∞ fun t => ∑ γ ∈ hF.toFinset,
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) :=
    ContDiff.sum fun γ _ => hterm γ
  refine hsum.contDiffAt.congr_of_eventuallyEq (Filter.eventually_of_mem hKn fun t ht => ?_)
  show poinX ψ d T β (w + L t) = _
  rw [poinX]
  refine tsum_eq_sum fun γ hγ => ?_
  have h0 : β ((w + L t) ⬝ d.jX + rat γ) = 0 := by
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨((w + L t) ⬝ d.jX + rat γ, (w + L t) ⬝ d.jX),
      ⟨subset_tsupport β hne, t, ht, rfl⟩, add_sub_cancel_left _ _⟩)
  rw [h0, mul_zero]

end GlobalTheory.BumpMixSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBump
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMix

theorem finite_rat_mem_of_isCompact {D : D7} {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, -, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := hg
  haveI : T2Space (Mx D m n) := ht2
  haveI : T1Space (Mx D m n) := @T2Space.t1Space _ _ ht2
  haveI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, rat_mem γ⟩, hγ, rfl⟩

theorem poinX_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  intro D ψ hψ S S₀ T ρ d β hβ
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank S.rank
  haveI : IsTopologicalAddGroup (WO S T) := hg
  haveI : LocallyCompactSpace (WO S T) := hlc
  obtain ⟨hg', -, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := hg'
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg'
  have hjX : Continuous fun u : WO S T => u ⬝ d.jX := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hjY : Continuous fun u : WO S T => u ⬝ d.jY := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, Continuous fun u : WO S T =>
      ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ) := by
    intro γ
    have e : (fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) =
        fun u : WO S T => symplOH S T (d.extX T (u ⬝ d.jX + 2 • rat γ)) (d.extY T (u ⬝ d.jY)) :=
      funext fun u => (d.symplOH_extX_extY T _ _).symm
    have hc : Continuous fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY)) := by
      rw [e]
      refine GlobalTheory.OrientedHeis.continuous_symplOH ?_ ?_
      · simp only [HypDec.extX_apply]
        exact (hjX.add continuous_const).matrix_mul continuous_const
      · simp only [HypDec.extY_apply]
        exact hjY.matrix_mul continuous_const
    exact (hψ.1.1.comp hc).mul (hβ.cont.comp (hjX.add continuous_const))
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
  have hK : IsCompact ((fun p : Mx D T.rank ρ × WO S T => p.1 - p.2 ⬝ d.jX) '' (tsupport β ×ˢ U)) :=
    (hβ.supp.isCompact.prod hU).image (continuous_fst.sub (Continuous.matrix_mul (A := fun p : Mx D T.rank ρ × WO S T => p.2) continuous_snd continuous_const))
  have hF := finite_rat_mem_of_isCompact _ hK
  have vanish : ∀ u ∈ U, ∀ γ, γ ∉ hF.toFinset → β (u ⬝ d.jX + rat γ) = 0 := by
    intro u hu γ hγ
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨(u ⬝ d.jX + rat γ, u), ⟨subset_tsupport β hne, hu⟩, add_sub_cancel_left _ _⟩)
  refine (continuous_finsetSum hF.toFinset fun γ _ => hterm γ).continuousAt.congr
    (Filter.eventually_of_mem hUn fun u hu => ?_)
  show _ = poinX ψ d T β u
  unfold poinX
  refine (tsum_eq_sum fun γ hγ => ?_).symm
  rw [vanish u hu γ hγ, mul_zero]

end GlobalTheory.BumpMix

end
end

