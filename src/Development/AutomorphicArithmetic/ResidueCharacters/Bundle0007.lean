module

public import Mathlib
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0880
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AutomorphicArithmetic.ResidueCharacters.LocAllOf
public import Development.AutomorphicArithmetic.ResidueCharacters.RowDef
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.InvariantsLengthAdmissibleOfNonzeroJumps
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

variable {D : D7}

def JumpsNoZero (i : D.nd.Loc) (M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) (h : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) ∧
    ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1,
      (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
        ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem kill_of (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) (h : ℕ) (hM : JumpsNoZero i M h)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C M) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (TruncatedSeriesCountingIdentities.locC C M))) :
    ∀ x : (Fin D.R.r → ↥C.LL.1) ⧸ L2.T, (∀ g, actD L2 g x = x) →
      ((D.nd.l i : ↥(OL C.LL)) ^ c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV)) • x = 0 := by
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≤ 4 * D.R.n := by
    rw [GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)]
    exact GlobalTheory.bridge_finrank_le D i w hw
  haveI : Finite (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) := by
    haveI := (D.nbr i w hw).Kw.2
    infer_instance
  obtain ⟨U, h1, h2, h3⟩ := exists_union (4 * D.R.n) D.R.r h hcard
    (fun τ a => IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a) (fun τ => ((hM w hw C).2 τ).1)
  have hn : U.card ≤ 4 * D.R.n * D.R.nV := h1.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  exact hK N h _ (D.nbr i w hw).Kw C.LL (hC w hw C)
    { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (TruncatedSeriesCountingIdentities.locC C M), cont := hc, L := L2 } U hn h2 (hM w hw C).1
    (fun τ a ha => h3 τ a ha) (fun τ => ((hM w hw C).2 τ).2)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem invariants_length_admissible_of_nonzero_jumps (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h : ℕ)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))
    (hM : JumpsNoZero i (T2O D.nd i ρ π) h) :
    EmbeddingTypes.H0ColumnLengthBound i ρ π dc (fun _ => c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV)) := by
  intro _ u _ w hw _ C _ L2 hstd
  have hT2c : Continuous fun g => T2O D.nd i ρ π g := GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i ρ π hρ
  have hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  have hkill := kill_of i N hK hC _ h hM w hw C hc L2
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ _ ?_
  intro x hx
  rw [Br.PD_p]
  exact hkill x fun g => hx g


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem length_invariants_Wprime_divisible_le_of_nonzero_jumps (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (h : ℕ)
    (hW : Continuous fun g => WpO D.nd i ρ π g) (hM : JumpsNoZero i (WpO D.nd i ρ π) h)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) :
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * (c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV) : ℕ) := by
  let C := TruncatedSeriesCountingIdentities.CoefExt.self i u hu
  have e : TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) = Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) := by
    ext g a b
    rfl
  have hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hW).matrix_mulVec continuous_const
  have hkill := kill_of i N hK hC _ h hM u hu C hc
  rw [e] at hkill
  have hK' := GlobalTheory.LengthH0Bound.inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) _
    (hkill (Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))))
  have hq := GlobalTheory.LengthH0Bound.lenUnit_le_of_kill D.R.r (D.nd.l i) _ (GlobalTheory.LengthH0Bound.natCast_ne_zero (D.nbr i u hu)) _ hK'
  exact_mod_cast hq

end UpperTheory.N

end
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open IsDiscreteValuationRing GlobalTheory.InvariantsKO

namespace UpperTheory.N

theorem lenUnit_invariants_le (D : D7) (i : D.nd.Loc) (hl2 : D.nd.l i = 2 → 2 ≤ D.nd.s0 i) (hs : 1 ≤ D.nd.s0 i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ) (hn : 0 < n) :
    lenUnit (O := D.nd.O i) (D.nd.l i)
        ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w))) ≤
      ((D.nd.s0 i + padicValNat (D.nd.l i) n : ℕ) : ℚ) := by
  haveI := D.nd.lPrime i
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ hgI
  set b : (D.nd.O i)ˣ := Formalism.MainNotions.N.Glob.epsO D.nd i g with hbdef
  have hb : (b : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * ((1 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) := by
    rw [Units.val_one, mul_one, ← hg]
    rfl
  set a : D.nd.O i := (b : D.nd.O i) ^ n - 1 with hadef
  have hva : addVal (D.nd.O i) a =
      ((D.nd.s0 i + padicValNat (D.nd.l i) n : ℕ) : ℕ∞) * addVal (D.nd.O i) ((D.nd.l i : ℕ) : D.nd.O i) := by
    rw [hadef, hb]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_pow_sub_one (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_ne_zero D.nd i)
      (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) (D.nd.s0 i) hs hl2 1 n hn
  have ha0 : a ≠ 0 := by
    intro h
    have ht : addVal (D.nd.O i) a = ⊤ := by rw [h]; simp
    rw [hva] at ht
    obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
    rw [he] at ht
    exact absurd ht (by rw [← Nat.cast_mul]; exact ENat.coe_ne_top _)
  have hkill : ∀ x ∈ Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)),
      a • x = 0 := by
    intro x hx
    have hfix := (Representation.mem_invariants _ x).mp hx ⟨g, hgD⟩
    have hfix' : ((b ^ n)⁻¹ : (D.nd.O i)ˣ) • x = x := by
      have e1 : ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)) ⟨g, hgD⟩ x =
          (((b ^ (-(n : ℤ)) : (D.nd.O i)ˣ)) : D.nd.O i) • x := by
        rfl
      rw [e1] at hfix
      rw [Units.smul_def, ← zpow_natCast, ← zpow_neg]
      exact hfix
    rw [hadef, sub_smul, one_smul]
    conv_lhs => rw [← hfix']
    rw [Units.smul_def, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, ← Units.smul_def, hfix', sub_self]
  calc lenUnit (O := D.nd.O i) (D.nd.l i) _
      ≤ lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) :=
        lenUnit_le_of_smul_eq_zero (D.nd.l i) ha0 _ hkill
    _ = _ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i hva

theorem h0_le (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hl2 : D.nd.l i = 2 → 2 ≤ D.nd.s0 i)
    (hs : 1 ≤ D.nd.s0 i) (hcol : ∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) :
    ((h0 D.nd i col : ℚ) : ℝ) ≤ ((D.nd.s0 i + Nat.log (D.nd.l i) D.R.t : ℕ) : ℝ) := by
  haveI := D.nd.lPrime i
  have key : h0 D.nd i col ≤ ((D.nd.s0 i + Nat.log (D.nd.l i) D.R.t : ℕ) : ℚ) := by
    unfold h0
    refine unbotD_le ?_ (by positivity)
    apply Finset.max_le
    intro y hy
    obtain ⟨⟨w, n⟩, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hn0, hnt⟩ := Finset.mem_Ioo.mp hn
    refine WithBot.coe_le_coe.mpr ((UpperTheory.N.lenUnit_invariants_le D i hl2 hs w (hcol w hw) n hn0).trans ?_)
    have : padicValNat (D.nd.l i) n ≤ Nat.log (D.nd.l i) D.R.t := by
      rw [Nat.padicValNat_def]
      exact (multiplicity_le_nat_log n).trans (Nat.log_mono_right hnt.le)
    exact_mod_cast Nat.add_le_add_left this _
  exact_mod_cast key

end UpperTheory.N
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.LocAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem UpperTheory.N.locAll : Hypotheses₂ → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime],
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) :=
  fun hP D HW F Cm l _ => UpperTheory.N.locAll_of hP.bk hP.tate hP.euler D HW F Cm l
    (_root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hP.bk hP.tate hP.euler D HW F Cm).2.2.2.2.2.2.2 (_root_.GlobalTheory.NLink.wAll_holds D HW F Cm l)
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.NumRow
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

variable {D : D7}

theorem lam_eq (L : SizeData₂ D) (l : ℕ) : RowSmall.abelian₂ L l = Num.lam l (sN l D.host.condN) (RowSmall.hB L) := rfl

theorem sl_eq (D : D7) (l : ℕ) : RowSmall.sl D l = sN l D.host.condN := rfl

theorem one_le_hB (L : SizeData₂ D) (P : ParameterChoice' D L) : 1 ≤ RowSmall.hB L :=
  (Num.one_le_b L).trans (Num.hB_bounds L P).1

theorem condN_le_hB (L : SizeData₂ D) (P : ParameterChoice' D L) : (D.host.condN : ℝ) ≤ RowSmall.hB L :=
  (Num.condN_le L P).trans (Num.hB_bounds L P).1

theorem t_le_hB (L : SizeData₂ D) (P : ParameterChoice' D L) : (D.R.t : ℝ) ≤ RowSmall.hB L :=
  (Num.sizes_le_b L P).2.2.trans (Num.hB_bounds L P).1

theorem localLevel_eq_smallPrimeLevel (i : D.nd.Loc) (hs : D.nd.l i ∈ D.host.small) : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
  by_cases h2 : D.nd.l i = 2
  · have h1 : 1 ≤ D.host.QS.factorization (D.nd.l i) := by
      have h := Nat.mem_primeFactors.1 hs
      exact h.1.factorization_pos_of_dvd h.2.2 h.2.1
    unfold RowSmall.sl
    rw [Num.factorization_condN D hs, max_eq_right h1, D.nd.restNLevelExponent_of_two i h2, h2]
  · exact Num.s0_eq i hs h2

theorem bound_smallPrime_of_splitBound (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (hK : KillingConditions.KillAt ρ) (hSha : TwistedPlaces.ShaFinOdd D)
    (i : D.nd.Loc) (hTw : TwistedPlaces.TwLoc D i) (hs : D.nd.s0 i = RowSmall.sl D (D.nd.l i)) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Zgood i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (he : (e' : ℝ) ≤ c * RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ))
    (hc0 : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.f * D.R.nV * RowSmall.abelian₂ L (D.nd.l i))
    (hW : ∀ u ∈ dc.col, (Br.h0W i u (ρ i) π : ℝ) ≤ c * D.R.r * D.R.f * D.R.nV * RowSmall.abelian₂ L (D.nd.l i))
    (hB : (cB : ℝ) ≤ c * D.R.t * D.R.f * D.R.nV * RowSmall.abelian₂ L (D.nd.l i))
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * RowSmall.abelian₂ L (D.nd.l i))
    (hz : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) (hconds : EmbeddingTypes.ShaBoundTheoremB i (ρ i) π dc e' c0 cB) :
    Bd ρ i π (costC L (6 * c) (30 * c) (D.nd.l i)) := by
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  obtain ⟨hK1, hK2⟩ := hK i hTw
  obtain ⟨hFin, -⟩ := hK1 π hπ
  have hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)
  have hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t := by
    ext e; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    unfold TwistedPlaces.VVr
    simp only [Rows.Data.VV, hIco]
  have hT := (Rat.cast_le (K := ℝ)).2 (hconds hFin hShaT hz)
  have hs0 : (D.nd.s0 i : ℝ) + 1 ≤ RowSmall.abelian₂ L (D.nd.l i) := by
    rw [hs]
    exact Num.s_le_lam hl.two_le (one_le_hB L P)
  have hb := Num.boundSplit_le i (ρ i) π dc e' c0 cB (y := RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ)) hc hs0
    (by rw [← mul_assoc]; exact he) hc0 hW hB hh
  unfold Bd costC TwistedPlaces.vhE
  rw [hVV]
  have e : 6 * c * D.R.f * D.R.m * (RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ)) =
      6 * c * D.R.f * D.R.m * RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ) := by ring
  linarith

theorem bound_smallPrime_of_splitBound_cyclotomic_of_level_eq (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (hK : KillingConditions.KillAt ρ)
    (hSha : TwistedPlaces.ShaFinOdd D) (i : D.nd.Loc) (hTw : TwistedPlaces.TwLoc D i) (hs : D.nd.s0 i = RowSmall.sl D (D.nd.l i)) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Zgood i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h₁ h₂ h₃ : ℕ) (hh₁ : (h₁ : ℝ) ≤ 4 * RowSmall.hB L)
    (hh₂ : (h₂ : ℝ) ≤ 4 * RowSmall.hB L) (hh₃ : (h₃ : ℝ) ≤ 4 * RowSmall.hB L)
    (hW : ∀ u ∈ dc.col, (Br.h0W i u (ρ i) π : ℝ) ≤
      D.R.r * (c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV) : ℝ))
    (hh : (h0 D.nd i dc.col : ℝ) ≤ (D.nd.s0 i : ℝ) + (Nat.log (D.nd.l i) D.R.t : ℝ))
    (hz : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1)
    (hconds : EmbeddingTypes.ShaBoundTheoremB i (ρ i) π dc (eL (D.nd.l i) D.host.condN h₁)
      (fun _ => c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV))
      (cBL (D.nd.l i) D.host.condN h₃ (4 * D.R.n * D.R.nV) D.R.t)) :
    Bd ρ i π (costC L 6000 30000 (D.nd.l i)) := by
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hy := one_le_hB L P
  have hN : (D.host.condN : ℝ) ≤ 8 * RowSmall.hB L := by linarith [condN_le_hB L P]
  obtain ⟨r1, r2, r3, r4, r5, r6, -⟩ := Num.ranks D
  have ha : (1 : ℝ) ≤ D.R.f * D.R.nV := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hn : ((4 * D.R.n * D.R.nV : ℕ) : ℝ) = 2 * (D.R.f * D.R.nV) := by
    have e : D.R.f = 2 * D.R.n := rfl
    rw [e]; push_cast; ring
  have k0 := Num.cyclotomicWeightExponent_le hl.two_le hy hh₂ hN (n := 4 * D.R.n * D.R.nV) ha (by rw [hn]; linarith)
  have kB := Num.cBL_le hl.two_le hy hh₃ hN (n := 4 * D.R.n * D.R.nV) (t := D.R.t) ha hn.le
    (by have : (1 : ℝ) ≤ D.R.t := by linarith
        exact_mod_cast this)
  have kE := Num.eL_le hl.two_le hy hh₁ hN
  have kl := Num.natLog_le_lam hl.two_le (Num.one_le_sN (D.nd.l i) D.host.condN) hy (n := D.R.t)
    (by linarith [t_le_hB L P])
  have ks := Num.s_le_lam (s := sN (D.nd.l i) D.host.condN) hl.two_le hy
  have hΛ := Num.one_le_lam (s := sN (D.nd.l i) D.host.condN) hl.two_le hy
  rw [← lam_eq] at k0 kB kl ks hΛ
  have h := bound_smallPrime_of_splitBound L P ρ hK hSha i hTw hs π hπ dc _ _ _ (c := 1000) (by norm_num) kE
    (fun u _ => by rw [mul_assoc 1000]; exact k0)
    (fun u hu => (hW u hu).trans (by
      have := mul_le_mul_of_nonneg_left k0 (Nat.cast_nonneg (α := ℝ) D.R.r)
      linarith))
    (by linarith) (by rw [hs, sl_eq] at hh; linarith) hz hconds
  norm_num at h
  exact h

theorem bound_smallPrime_of_splitBound_cyclotomic (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (hK : KillingConditions.KillAt ρ)
    (hSha : TwistedPlaces.ShaFinOdd D) (i : D.nd.Loc) (hTw : TwistedPlaces.TwLoc D i) (hs : D.nd.l i ∈ D.host.small) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Zgood i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h₁ h₂ h₃ : ℕ) (hh₁ : (h₁ : ℝ) ≤ 4 * RowSmall.hB L)
    (hh₂ : (h₂ : ℝ) ≤ 4 * RowSmall.hB L) (hh₃ : (h₃ : ℝ) ≤ 4 * RowSmall.hB L)
    (hW : ∀ u ∈ dc.col, (Br.h0W i u (ρ i) π : ℝ) ≤
      D.R.r * (c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV) : ℝ))
    (hh : (h0 D.nd i dc.col : ℝ) ≤ (D.nd.s0 i : ℝ) + (Nat.log (D.nd.l i) D.R.t : ℝ))
    (hz : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1)
    (hconds : EmbeddingTypes.ShaBoundTheoremB i (ρ i) π dc (eL (D.nd.l i) D.host.condN h₁)
      (fun _ => c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV))
      (cBL (D.nd.l i) D.host.condN h₃ (4 * D.R.n * D.R.nV) D.R.t)) :
    Bd ρ i π (costC L 6000 30000 (D.nd.l i)) :=
  bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P ρ hK hSha i hTw (localLevel_eq_smallPrimeLevel i hs) π hπ dc h₁ h₂ h₃ hh₁ hh₂ hh₃ hW hh hz hconds

end UpperTheory.N

end
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.RowThreeC
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

def RowOnAt {D : D7} (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (Q : ℕ → Prop) (A B : ℝ) : Prop :=
  ∀ k, TwistedPlaces.TwLoc D k → Q (D.nd.l k) → ∀ π ∈ D.nd.Zgood k, Bd ρ k π (costC L A B (D.nd.l k))

end UpperTheory.N

end
end

