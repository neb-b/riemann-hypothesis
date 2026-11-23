module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0038

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolColPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.PoincareInHH.Cut

theorem gcS_sub {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    ((GcS X u hK c : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ⊆ X.NinfU u := by
  intro s hs
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hs
  exact (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hγ).2).1

theorem isSFund_conjImg {D : D7} (X : HidaSetting D) (S S' : Set X.B.I.Ginf) (Ω : Set X.B.I.Ginf) (c : X.B.I.Ginf)
    (hS : ∀ s, s ∈ S' ↔ ∃ t ∈ S, c * t * c⁻¹ = s) (hΩ : IsSFund X.B.I S Ω) :
    IsSFund X.B.I S' ((fun s => c * s * c⁻¹) '' Ω) := by
  have himg : (fun s => c * s * c⁻¹) '' Ω = (fun s => c⁻¹ * s * c) ⁻¹' Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨c⁻¹ * x * c, hx, by group⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [himg]
    exact ((measurable_const_mul c⁻¹).mul_const c) hΩ.1
  · intro x
    obtain ⟨t, ht, htx⟩ := hΩ.2.1 (c⁻¹ * x * c)
    refine ⟨c * t * c⁻¹, (hS _).2 ⟨t, ht, rfl⟩, ?_⟩
    exact ⟨t * (c⁻¹ * x * c), htx, by group⟩
  · intro x hx s hs hsx
    obtain ⟨ω, hω, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := (hS s).1 hs
    rw [himg] at hsx
    have h1 : t * ω ∈ Ω := by
      have e : c⁻¹ * (c * t * c⁻¹ * (c * ω * c⁻¹)) * c = t * ω := by group
      have h0 : c⁻¹ * (c * t * c⁻¹ * (c * ω * c⁻¹)) * c ∈ Ω := hsx
      rw [e] at h0
      exact h0
    have := hΩ.2.2 ω hω t ht h1
    rw [this]; group

theorem volColC_of (h1 : NOinfEqC) (h2 : NOcolEqC) (h3 : GcCountC) (h4 : FundMeasEqC) (h5 : IndexVolC)
    (h6 : IndexTransferC) (h7 : ConjUC) (h8 : GcFundC) (h9 : GcConjC) (h10 : HinfConjC) : VolColC := by
  intro D X Y u ρ Ω hΩ
  let Γ : Hfin X u → Subgroup X.B.I.Ginf := fun h => GcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)
  let U : Hfin X u → Subgroup X.B.I.Gf := fun h => UcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)
  have hsub : ∀ h, ((Γ h : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ⊆ X.NinfU u := fun h => gcS_sub X u Y.hK _
  have hcnt : ∀ h, Countable (Γ h) := fun h => h3 D X u Y.hK _
  let Ωh : Hfin X u → Set X.B.I.Ginf := fun h => Classical.choose (h8 D X Y u h)
  have hΩh : ∀ h, IsSFund X.B.I (Γ h) (Ωh h) := fun h => Classical.choose_spec (h8 D X Y u h)
  let F : Hfin X u → ℝ≥0∞ := fun h => X.muN u (Ωh h)
  have hF : ∀ h Ω', IsSFund X.B.I (Γ h) Ω' → X.muN u Ω' = F h := fun h Ω' hΩ' =>
    h4 D X u (Γ h) Ω' (Ωh h) (hsub h) (hcnt h) hΩ' (hΩh h)

  have hratio : ∀ g h : Hfin X u,
      F g * ((Γ h).relIndex (Γ g) : ℝ≥0∞) = F h * ((Γ g).relIndex (Γ h) : ℝ≥0∞) := by
    intro g h
    have hne1 : (Γ h ⊓ Γ g).relIndex (Γ g) ≠ 0 := by
      rw [Subgroup.inf_relIndex_right, (h6 D X u Y.hK g h).1]; exact (h6 D X u Y.hK g h).2
    have hne2 : (Γ g ⊓ Γ h).relIndex (Γ h) ≠ 0 := by
      rw [Subgroup.inf_relIndex_right, (h6 D X u Y.hK h g).1]; exact (h6 D X u Y.hK h g).2
    obtain ⟨Ω1, hΩ1, hμ1⟩ := h5 D X u (Γ g) (Γ h ⊓ Γ g) (Ωh g) inf_le_right (hsub g) (hcnt g) hne1 (hΩh g)
    obtain ⟨Ω2, hΩ2, hμ2⟩ := h5 D X u (Γ h) (Γ g ⊓ Γ h) (Ωh h) inf_le_right (hsub h) (hcnt h) hne2 (hΩh h)
    rw [inf_comm] at hΩ2
    have hc : Countable ↥(Γ h ⊓ Γ g) := by
      exact Set.countable_coe_iff.2 ((Set.countable_coe_iff.1 (hcnt g)).mono (fun x hx => (Subgroup.mem_inf.1 hx).2))
    have heq := h4 D X u (Γ h ⊓ Γ g) Ω1 Ω2 (fun x hx => hsub g (Subgroup.mem_inf.1 hx).2) hc hΩ1 hΩ2
    rw [hμ1, hμ2, Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at heq
    rw [mul_comm, heq, mul_comm]

  have hU : ∀ g h : Hfin X u, U (g * h) = (U h).map (MulAut.conj (g : X.B.I.Gf)).toMonoidHom := by
    intro g h
    have := h7 D X u Y.hK g ((h : X.B.I.Gf) * X.xu u)
    simp only [U, Subgroup.coe_mul, mul_assoc]
    exact this
  have hinj : ∀ g : Hfin X u, Function.Injective (MulAut.conj (g : X.B.I.Gf)).toMonoidHom :=
    fun g => (MulAut.conj (g : X.B.I.Gf)).injective
  have hidx : ∀ g h : Hfin X u, (U (g * h)).relIndex (U g) = (U h).relIndex (U 1) := by
    intro g h
    have e := hU g 1
    rw [mul_one] at e
    rw [hU g h, e, Subgroup.relIndex_map_map_of_injective _ _ (hinj g)]
  have hidx' : ∀ g h : Hfin X u, (U g).relIndex (U (g * h)) = (U 1).relIndex (U h) := by
    intro g h
    have e := hU g 1
    rw [mul_one] at e
    rw [hU g h, e, Subgroup.relIndex_map_map_of_injective _ _ (hinj g)]
  have hG : ∀ g h : Hfin X u, (Γ h).relIndex (Γ g) = (U h).relIndex (U g) := fun g h => (h6 D X u Y.hK g h).1
  have hGne : ∀ g h : Hfin X u, (Γ h).relIndex (Γ g) ≠ 0 := fun g h => by
    rw [hG]; exact (h6 D X u Y.hK g h).2

  have hmul : ∀ g h : Hfin X u, F (g * h) * F 1 = F g * F h := by
    intro g h
    have E1 := hratio g (g * h)
    have E2 := hratio 1 h
    set A : ℕ := (U h).relIndex (U 1) with hA
    set B : ℕ := (U 1).relIndex (U h) with hB
    have hA1 : (Γ (g * h)).relIndex (Γ g) = A := by
      rw [hG, hA, hidx g h]
    have hB1 : (Γ g).relIndex (Γ (g * h)) = B := by
      rw [hG, hB, hidx' g h]
    have hA2 : (Γ h).relIndex (Γ 1) = A := by rw [hG]
    have hB2 : (Γ 1).relIndex (Γ h) = B := by rw [hG]
    have hA0 : A ≠ 0 := by rw [← hA2]; exact hGne 1 h
    have hB0 : B ≠ 0 := by rw [← hB2]; exact hGne h 1
    rw [hA1, hB1] at E1
    rw [hA2, hB2] at E2
    have hAB0 : ((A : ℝ≥0∞) * B) ≠ 0 := mul_ne_zero (by exact_mod_cast hA0) (by exact_mod_cast hB0)
    have hABt : ((A : ℝ≥0∞) * B) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top A) (ENNReal.natCast_ne_top B)
    refine (ENNReal.mul_left_inj hAB0 hABt).1 ?_
    calc F (g * h) * F 1 * (A * B) = (F (g * h) * B) * (F 1 * A) := by ring
      _ = (F g * A) * (F h * B) := by rw [← E1, E2]
      _ = F g * F h * (A * B) := by ring

  have hinv : ∀ (γ : Gam X u) (h : Hfin X u) (κ : Ku X u Y.hK), F (iotaF X u γ * h * (κ : Hfin X u)) = F h := by
    intro γ h κ
    set c : X.B.I.Ginf := (γ : X.B.I.GA).1 with hc
    have hcH : c ∈ Hinf X u := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1
    have hset := h9 D X u Y.hK γ h κ
    have hS : ∀ s, s ∈ ((Γ (iotaF X u γ * h * (κ : Hfin X u)) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ↔
        ∃ t ∈ ((Γ h : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf), c * t * c⁻¹ = s := by
      intro s
      have := Set.ext_iff.1 hset s
      simpa [Γ] using this
    have hfund := isSFund_conjImg X _ _ (Ωh h) c hS (hΩh h)
    rw [← hF _ _ hfund]
    exact h10 D X u c hcH (Ωh h) (hΩh h).1

  have hfin : (Set.range F).Finite := by
    refine (Set.finite_range (fun ρ : (Y.cs u).Cl => F ((Y.cs u).h ρ))).subset ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := Y.colReps u h
    exact ⟨ρ, by rw [hh, hinv]⟩

  have hconst : ∀ h, F h = F 1 := by
    intro h
    have E := hratio 1 h
    have ha : (Γ h).relIndex (Γ 1) ≠ 0 := hGne 1 h
    have hb : (Γ 1).relIndex (Γ h) ≠ 0 := hGne h 1
    have ha' : ((Γ h).relIndex (Γ 1) : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
    have hb' : ((Γ 1).relIndex (Γ h) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
    by_cases h0 : F 1 = 0
    · rw [h0, zero_mul] at E
      rcases mul_eq_zero.1 E.symm with e | e
      · rw [e, h0]
      · exact absurd e hb'
    by_cases ht : F 1 = ⊤
    · rw [ht, ENNReal.top_mul ha'] at E
      rcases ENNReal.mul_eq_top.1 E.symm with ⟨-, e⟩ | ⟨e, -⟩
      · exact absurd e (ENNReal.natCast_ne_top _)
      · rw [e, ht]

    have hpos : ∀ k, F k ≠ 0 ∧ F k ≠ ⊤ := by
      intro k
      have Ek := hratio 1 k
      have hak : ((Γ k).relIndex (Γ 1) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hGne 1 k
      have hbk : ((Γ 1).relIndex (Γ k) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hGne k 1
      constructor
      · intro e; rw [e, zero_mul] at Ek
        rcases mul_eq_zero.1 Ek with e' | e'
        · exact h0 e'
        · exact hak e'
      · intro e; rw [e, ENNReal.top_mul hbk] at Ek
        rcases ENNReal.mul_eq_top.1 Ek with ⟨-, e'⟩ | ⟨e', -⟩
        · exact ENNReal.natCast_ne_top _ e'
        · exact ht e'
    let q : Hfin X u → ℝ := fun k => (F k).toReal / (F 1).toReal
    have hF1 : 0 < (F 1).toReal := ENNReal.toReal_pos h0 ht
    have hq : ∀ g k, q (g * k) = q g * q k := by
      intro g k
      have := congrArg ENNReal.toReal (hmul g k)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
      simp only [q]
      field_simp
      linarith [this]
    have hqpow : ∀ n : ℕ, q (h ^ n) = q h ^ n := by
      intro n
      induction n with
      | zero => simp [q, hF1.ne']
      | succ n ih => rw [pow_succ, hq, ih, pow_succ]
    have hqpos : 0 < q h := div_pos (ENNReal.toReal_pos (hpos h).1 (hpos h).2) hF1
    have hq1 : q h = 1 := by
      by_contra hne
      have hinjq : Function.Injective (fun n : ℕ => q h ^ n) := pow_right_injective₀ hqpos hne
      have hrange : (Set.range (fun n : ℕ => q h ^ n)).Finite := by
        refine ((hfin.image (fun x : ℝ≥0∞ => x.toReal / (F 1).toReal))).subset ?_
        rintro _ ⟨n, rfl⟩
        exact ⟨F (h ^ n), ⟨h ^ n, rfl⟩, by simp only [q] at hqpow; exact hqpow n⟩
      exact Set.infinite_range_of_injective hinjq hrange
    have : (F h).toReal = (F 1).toReal := by
      have := hq1; simp only [q] at this
      field_simp at this; linarith
    exact (ENNReal.toReal_eq_toReal_iff' (hpos h).2 ht).1 this

  have hρ : IsSFund X.B.I (Γ ((Y.cs u).h ρ)) Ω := by
    have := h2 D X Y u ρ
    rw [this] at hΩ
    exact hΩ
  have h1' : IsSFund X.B.I (Γ 1) (Y.FN u) := by
    have e := h1 D X u Y.hK
    have hFN := Y.FN_fund u
    rw [e] at hFN
    simpa [Γ] using hFN
  rw [hF _ _ hρ, hF _ _ h1', hconst]

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolEqPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem mem_gcS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) (s : X.B.I.Ginf) :
    s ∈ GcS X u hK c ↔ ∃ γ : X.B.I.GA, γ ∈ X.B.I.GFset ∧ γ.1 = s ∧ γ.1 ∈ X.NinfU u ∧ γ.2 ∈ X.NfinU u ∧
      c⁻¹ * γ.2 * c ∈ X.K2 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨hG, hP⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hP
    obtain ⟨hN, hk⟩ := Subgroup.mem_inf.1 h2
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hk
    refine ⟨γ, hG, rfl, h1, hN, ?_⟩
    have : γ.2 = c * k * c⁻¹ := by rw [← hke]; rfl
    rw [this]
    have : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    rw [this]; exact hk
  · rintro ⟨γ, hG, rfl, h1, hN, hk⟩
    refine ⟨γ, Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_prod.2 ⟨h1, Subgroup.mem_inf.2 ⟨hN, ?_⟩⟩⟩, rfl⟩
    refine Subgroup.mem_map.2 ⟨c⁻¹ * γ.2 * c, hk, ?_⟩
    show c * (c⁻¹ * γ.2 * c) * c⁻¹ = γ.2
    group

theorem noinfEqC_holds : NOinfEqC := by
  intro D X u hK
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩

theorem nocolEqC_holds : NOcolEqC := by
  intro D X Y u ρ
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, nLamNfin_holds D X u _ x n hx hn,
      (nilradical_conj_level' D X Y u ρ x n hn hx).1⟩
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    exact Formalism.L2.SG.Pf.SlabCoverPf.nilradical_rational_lattice D X Y u ρ γ (Formalism.L2.SG.Closed.level_subgroup_properties X) hG hN hF hk

theorem gcCountC_holds : GcCountC := by
  intro D X u hK c
  have hR : (RcS X u hK c : Set X.B.I.GA).Countable :=
    (Set.countable_coe_iff.1 (Formalism.MainNotions.LeviCoordinates.rr_GF_countable X.B.I)).mono (fun _ h => (Subgroup.mem_inf.1 h).1)
  have : (GcS X u hK c : Set X.B.I.Ginf).Countable := by
    unfold GcS
    rw [Subgroup.coe_map]
    exact hR.image _
  exact this.to_subtype

theorem conjUC_holds : ConjUC := by
  intro D X u hK g c
  ext x
  simp only [UcS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hN, k, hk, hke⟩
    refine ⟨(g : X.B.I.Gf)⁻¹ * x * (g : X.B.I.Gf), ⟨?_, k, hk, ?_⟩, ?_⟩
    · have := (nfinConj_holds X u g⁻¹ x hN).1
      simp only [InvMemClass.coe_inv, inv_inv] at this
      exact this
    · rw [← hke]; group
    · group
  · rintro ⟨y, ⟨hN, k, hk, hke⟩, rfl⟩
    refine ⟨(nfinConj_holds X u g y hN).1, k, hk, ?_⟩
    rw [← hke]; group

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolFundPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem muN_preimage (a : X.B.I.Ginf) (ha : a ∈ X.NinfU u) {A : Set X.B.I.Ginf} (hA : MeasurableSet A) :
    X.muN u {y | a * y ∈ A} = X.muN u A := by
  have h := Measure.map_apply (μ := X.muN u) (measurable_const_mul a) hA
  rw [(X.muN_haar u).2.2.2 a ha] at h
  exact h.symm

end Gen

theorem fundMeasEqC_holds : FundMeasEqC := by
  intro D X u Γ Ω Ω' hsub hc hΩ hΩ'
  have hcs : (Γ : Set X.B.I.Ginf).Countable := Set.countable_coe_iff.1 hc
  have hun : ∀ (P : Set X.B.I.Ginf), IsSFund X.B.I Γ P → ∀ n, ∀ a ∈ (Γ : Set X.B.I.Ginf), ∀ a' ∈ (Γ : Set X.B.I.Ginf),
      a * n ∈ P → a' * n ∈ P → a = a' := by
    intro P hP n a ha a' ha' h1 h2
    have h3 : (a' * a⁻¹) * (a * n) ∈ P := by simpa [mul_assoc] using h2
    have := hP.2.2 _ h1 _ (Γ.mul_mem ha' (Γ.inv_mem ha)) h3
    exact (mul_inv_eq_one.1 this).symm
  rw [Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω Ω' (X.muN u) hcs hΩ.1 hΩ'.1 hΩ'.2.1
      (hun Ω' hΩ'),
    Formalism.L2.SG.TermOp.IdBlocks.measure_decomp (Γ : Set X.B.I.Ginf) Ω' Ω (X.muN u) hcs hΩ'.1 hΩ.1 hΩ.2.1 (hun Ω hΩ)]
  have hterm : ∀ a : (Γ : Set X.B.I.Ginf),
      X.muN u (Ω ∩ {n | (a : X.B.I.Ginf) * n ∈ Ω'}) =
        X.muN u (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) := by
    intro a
    have hS : MeasurableSet (Ω' ∩ {m | ((a : X.B.I.Ginf))⁻¹ * m ∈ Ω}) :=
      hΩ'.1.inter ((measurable_const_mul _) hΩ.1)
    rw [← muN_preimage X u (a : X.B.I.Ginf) (hsub a.2) hS]
    congr 1
    ext n
    simp [and_comm]
  simp_rw [hterm]
  let e : (Γ : Set X.B.I.Ginf) ≃ (Γ : Set X.B.I.Ginf) :=
    ⟨fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩, fun a => ⟨(a : X.B.I.Ginf)⁻¹, Γ.inv_mem a.2⟩,
      fun a => by simp, fun a => by simp⟩
  exact e.tsum_eq (fun b : (Γ : Set X.B.I.Ginf) => X.muN u (Ω' ∩ {m | (b : X.B.I.Ginf) * m ∈ Ω}))

theorem indexVolC_holds : IndexVolC := by
  intro D X u Γ Γ' Ω hle hsub hc hk hΩ
  set H : Subgroup Γ := Γ'.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hk⟩
  have : Finite (Γ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let r : Γ ⧸ H → Γ := fun q => Quotient.out q
  have hr : ∀ q, ((r q : Γ) : Γ ⧸ H) = q := fun q => Quotient.out_eq q
  let A : Γ ⧸ H → Set X.B.I.Ginf := fun q => {y | ((r q : Γ) : X.B.I.Ginf) * y ∈ Ω}
  have hA : ∀ q, MeasurableSet (A q) := fun q => (measurable_const_mul _) hΩ.1

  have key : ∀ (a b : Γ) (y : X.B.I.Ginf), (a : X.B.I.Ginf) * y ∈ Ω → (b : X.B.I.Ginf) * y ∈ Ω → a = b := by
    intro a b y ha hb
    have h3 : ((b : X.B.I.Ginf) * (a : X.B.I.Ginf)⁻¹) * ((a : X.B.I.Ginf) * y) ∈ Ω := by
      simpa [mul_assoc] using hb
    have := hΩ.2.2 _ ha _ (Γ.mul_mem b.2 (Γ.inv_mem a.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  refine ⟨⋃ q, A q, ⟨MeasurableSet.iUnion hA, ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
    let sΓ : Γ := ⟨s, hs⟩
    have hq : (r (sΓ : Γ ⧸ H))⁻¹ * sΓ ∈ H := QuotientGroup.eq.1 (hr _)
    refine ⟨(((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf), Subgroup.mem_subgroupOf.1 hq, ?_⟩
    refine Set.mem_iUnion.2 ⟨(sΓ : Γ ⧸ H), ?_⟩
    show ((r (sΓ : Γ ⧸ H) : Γ) : X.B.I.Ginf) * ((((r (sΓ : Γ ⧸ H))⁻¹ * sΓ : Γ) : X.B.I.Ginf) * x) ∈ Ω
    simpa [mul_assoc, sΓ] using hsx
  · intro x hx s hs hsx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hsx
    let sΓ : Γ := ⟨s, hle hs⟩
    have hp0 : ((r p : Γ) : X.B.I.Ginf) * (s * x) ∈ Ω := hp
    have hp' : ((r p * sΓ : Γ) : X.B.I.Ginf) * x ∈ Ω := by
      simpa [mul_assoc, sΓ] using hp0
    have e1 : r p * sΓ = r q := key _ _ x hp' hq
    have e2 : sΓ = (r p)⁻¹ * r q := by rw [← e1]; group
    have hmem : (r p)⁻¹ * r q ∈ H := by
      rw [← e2]; exact Subgroup.mem_subgroupOf.2 hs
    have hpq : p = q := by
      have := QuotientGroup.eq.2 hmem
      rw [hr, hr] at this
      exact this
    subst hpq
    have : sΓ = 1 := by rw [e2]; group
    exact congrArg Subtype.val this
  · have hdisj : Pairwise (Function.onFun Disjoint A) := by
      intro p q hpq
      refine Set.disjoint_left.2 fun y hy1 hy2 => hpq ?_
      have := key _ _ y hy1 hy2
      rw [← hr p, ← hr q, this]
    rw [measure_iUnion hdisj hA, tsum_fintype]
    have hterm : ∀ q, X.muN u (A q) = X.muN u Ω := fun q =>
      muN_preimage X u _ (hsub (r q).2) hΩ.1
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfModGOfAt
section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.RegroupPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reduction_mod_g_holds : ModGOfAtC := by
  intro D X g1 Λ hΛ v hv
  obtain ⟨c, hcop, hcv⟩ := hv
  have hg0 : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hgE : (X.B.g : X.B.I.E) ≠ 0 := Nat.cast_ne_zero.mpr hg0
  set q : X.B.I.E := ((X.B.g : X.B.I.E))⁻¹ with hqdef
  set ι : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F) with hι
  have hq : ι q * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
    rw [← map_natCast ι, ← map_mul, hqdef, inv_mul_cancel₀ hgE, map_one]
  have key : ∀ z ∈ mL X.B.I X.B.g, ι q • z ∈ X.B.I.Lf := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [smul_smul, hq, one_smul]; exact hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul t a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ t ha
  set w : (VS D).V := (X.ιE (q * c)) • v with hwdef
  have hwΛ : w ∈ Λ := by
    rw [hΛ, hwdef, Formalism.L2.SG.NormCut.crd_smul' X, Formalism.L2.SG.NormCut.incl_smul' X, mulVec_smul,
      RingEquiv.symm_apply_apply, map_mul, map_natCast, mul_smul]
    exact key _ hcv
  intro P hgP
  have hcP : ((c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro hc
    have h1 : IsCoprime ((c : ℤ)) ((X.B.g : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨a, b, hab⟩ := h1.map (Int.castRingHom (𝓞 D.host.E))
    have hg' : (((X.B.g : ℕ) : ℤ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Int.cast_natCast, X.g_eq]; exact hgP
    have hc' : (((c : ℕ) : ℤ) : 𝓞 D.host.E) ∈ P.asIdeal := by rw [Int.cast_natCast]; exact hc
    have h1P : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [← hab]
      exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hc') (P.asIdeal.mul_mem_left _ hg')
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1P)
  have hcv' : ((c : ℕ) : 𝓞 D.host.E) • v = ((gS D : ℕ) : 𝓞 D.host.E) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hwdef, ← Nat.cast_smul_eq_nsmul D.host.E,
      ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul]
    congr 1
    rw [← map_natCast X.ιE (gS D), ← map_mul, ← mul_assoc, hqdef, show gS D = X.B.g from X.g_eq.symm,
      mul_inv_cancel₀ hgE, one_mul, map_natCast]
  exact ⟨_, hcP, by rw [hcv']; exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hwΛ⟩

end Formalism.L2.SG.Pf.RegroupPf
end
end

