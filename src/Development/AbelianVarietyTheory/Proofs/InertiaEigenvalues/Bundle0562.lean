module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamily
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDualU

theorem dualLatLe_of {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] [IsDomain O] [IsFractionRing O LL]
    (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT' : Lattice (O := O) U'.ρ) (hLT' : IsDualLat1 PD LT LT' P) (hopen : IsOpen (LT'.T : Set U'.V)) (b : ℕ)
    (h : finrank LL (FiniteCohomology PD U'.ρ) + finrank O ↥LT.T ≤ b) : DualLatLe PD U U' LT P b :=
  ⟨LT', hLT', by rw [GlobalTheory.TopSteps.FinSummand.finrank_h1fT PD LT' hopen]; exact h⟩


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  intro D hF hDR hBK i r hR Xs w hw hK n hPot k M hSub
  have hSum := _root_.GlobalTheory.Pass.LocDual.isSummandTw_locU D i r hR Xs w hw k M hSub
  obtain ⟨hU, X', PX, hD1, hSF⟩ := GlobalTheory.T.potential_family_summand_restriction D hF hDR i r hR Xs w hw n hPot _ hSum
  have hX' := GlobalTheory.T.tateDual_twistedSumSummand_isDeRham D hF hDR i r hR Xs w hw n hPot _ hSum X' PX hD1
  have hGood := goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL
  have hcyc : ∀ g, ∃ u : (Br.OLL D.nbr i w hw)ˣ, ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :
      (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) (u : Br.OLL D.nbr i w hw) := by
    intro g
    rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
    exact ⟨Units.map (D.nbr i w hw).eO.toRingHom.toMonoidHom (epsU D.nd i ((decS D.nd w) (Br.iota D.nbr i w hw g))), rfl⟩
  obtain ⟨LT', hLT', hopen⟩ := GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing (Br.PD D.loc D.nbr i w hw) hGood hcyc _ X' PX hD1
    (Br.locLat D.nbr i w hw M)
  refine ⟨hU, X', PX, hSF, ?_⟩
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hGood
  haveI := hdom
  haveI := hfr
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  refine dualLatLe_of _ _ X' _ PX LT' hLT' hopen _ ?_
  have h2 := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL hK
    (hBK (D.nd.l i) (D.nbr i w hw).Kw) X' hX'
  have h3 : finrank (Br.LL D.nbr i w hw) X'.V = k := by
    rw [← hD1.2.2.2]
    exact Module.finrank_fin_fun _
  have h4 : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
    have e := LinearEquiv.ofInjective _ (stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k)
    exact (LinearEquiv.finrank_eq e).symm.trans (Module.finrank_fin_fun _)
  have h5 : finrank (Br.LL D.nbr i w hw) (FiniteCohomology (Br.PD D.loc D.nbr i w hw) X'.ρ) ≤ k := h3 ▸ h2
  exact le_trans (Nat.add_le_add h5 h4.le) (by omega)

end GlobalTheory.Pass.LocDualU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.ZVal


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem zval : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  intro D HW F l _ K s LL h T hT c b lam hlc hl1 hZk g₁ hg₁ z₁ hz₁ hZ₁
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have hcl : IsClosed (((HW l).W K s LL h).GKs : Set ↥(GK K)) :=
    (lam_exists D HW K s LL h).elim fun _ hx => hx.2.2.2.2
  have hcs : CompactSpace ↥((HW l).W K s LL h).GKs := isCompact_iff_compactSpace.1 hcl.isCompact
  refine (GlobalTheory.T.exists_weakTopology_wachImage_isClosed D HW F l K s LL h T hT).elim fun τ hτ => ?_
  letI := τ
  haveI hT2 : T2Space (TW (RW LL) T) := hτ.1
  have hTG : IsTopologicalAddGroup (TW (RW LL) T) := hτ.2.1
  have hact := hτ.2.2.1
  have hemb := hτ.2.2.2.1
  have hclo := hτ.2.2.2.2
  let a : ↥((HW l).W K s LL h).GKs → TW (RW LL) T →+ TW (RW LL) T := fun g =>
    (TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K))).toAddMonoidHom
  have ha1 : ∀ g x, a g x = TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K)) x :=
    fun g x => rfl
  have hamul : ∀ g g' x, a (g * g') x = a g (a g' x) := by
    intro g g' x
    simp only [ha1]
    exact GlobalTheory.HerrClassMaps.TWact_mul _ _ _
      (fun r => GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL _ _ r) T _ _ x
  have ha1t : ∀ g (t : ↥T.L.T), a g ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) =
      (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨T.ρ (g : ↥(GK K)) t, T.L.stable _ t t.2⟩ : ↥T.L.T) := fun g t =>
    GlobalTheory.HerrClassMaps.TWact_one_tmul _ T _ t
  have haj : ∀ g (w : ((HW l).W K s LL h).DD T), a g (((F l).E K s LL h).tie.jD T w) =
      ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ (g : ↥(GK K))) w) :=
    fun g w => (((F l).E K s LL h).tie.jD_act T (g : ↥(GK K)) w).symm
  let J : AddSubgroup (TW (RW LL) T) :=
    (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X).toAddSubgroup.map (((F l).E K s LL h).tie.jD T).toAddMonoidHom
  have hJm : ∀ x, x ∈ J ↔ ∃ w ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X,
      ((F l).E K s LL h).tie.jD T w = x := fun x => AddSubgroup.mem_map
  have hJ : IsClosed (J : Set (TW (RW LL) T)) := by
    have : (J : Set (TW (RW LL) T)) = ((F l).E K s LL h).tie.jD T ''
        (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T)) := by
      ext x
      exact (hJm x).trans Iff.rfl
    rw [this]; exact hclo
  have hJa : ∀ g, ∀ x ∈ J, a g x ∈ J := by
    intro g x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj]
    exact (hJm _).2 ⟨_, GlobalTheory.NL.XStab.xstab D HW l K s LL h T _ w hw.1, rfl⟩
  have hJk : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → ∀ x ∈ J, a h' x = x := by
    intro h' hh x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj, hl1 h' hh, ((HW l).W K s LL h).γD_one]
  haveI hCA : ContinuousAdd (TW (RW LL) T) := hTG.toContinuousAdd
  haveI hCN : ContinuousNeg (TW (RW LL) T) := hTG.toContinuousNeg
  haveI hCS : ContinuousSub (TW (RW LL) T) :=
    ⟨Continuous.congr (continuous_fst.add continuous_snd.neg) (fun p => (sub_eq_add_neg p.1 p.2).symm)⟩
  have hZc : Continuous (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) := by
    unfold Zf
    exact (hemb.comp (c.2.1.1.subtype_mk fun g => GlobalTheory.HerrClassMaps.mem_T c g)).add
      (((hact b).comp continuous_subtype_val).sub continuous_const)
  have hZm : ∀ g g', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b (g * g') =
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g + a g (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g') := by
    intro g g'
    have e : (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) (g * g'), GlobalTheory.HerrClassMaps.mem_T c (g * g')⟩ : ↥T.L.T) =
        ⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ +
          ⟨T.ρ (g : ↥(GK K)) ((c : ↥((HW l).W K s LL h).GKs → T.V) g'), T.L.stable _ _ (GlobalTheory.HerrClassMaps.mem_T c g')⟩ :=
      Subtype.ext (c.2.1.2 g g')
    have hz : ∀ g'', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g'' =
        (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g'', GlobalTheory.HerrClassMaps.mem_T c g''⟩ : ↥T.L.T) +
          (a g'' b - b) := fun _ => rfl
    simp only [hz, map_add (f := _), map_sub, ha1t, hamul, e, TensorProduct.tmul_add]
    abel
  have hZk' : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b h' = 0 :=
    fun h' hh => hZk h' (hl1 h' hh)
  have hzJ : ((F l).E K s LL h).tie.jD T z₁ ∈ J := (hJm _).2 ⟨z₁, hz₁, rfl⟩
  have HM := (GlobalTheory.NL.ZgAll.mem_and_comm a lam hlc g₁ hg₁ J hJ hJa hJk _ hzJ
    (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) hZc hZm hZk' hZ₁).1
  intro g
  exact ((hJm _).1 (HM g)).elim fun w hw => ⟨w, hw.1, hw.2.symm⟩

end GlobalTheory.NL.ZVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_list_sum_left {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (B : G → ℂ) :
    ip L.sum B = (L.map fun ρ => ip ρ B).sum := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem list_nat_sum {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) (B : G → ℂ)
    (hB : IsChar B) : ∃ N : ℕ, (L.map fun ρ => ip ρ B).sum = N ∧ ∀ ρ ∈ L, ip ρ B ≠ 0 → N ≠ 0 := by
  induction L with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ))
    obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat (hL ρ List.mem_cons_self) hB
    refine ⟨k + N, by simp [hN, hk], ?_⟩
    intro σ hσ h0
    rcases List.mem_cons.1 hσ with rfl | hσ
    · rw [hk] at h0
      have : k ≠ 0 := by exact_mod_cast h0
      omega
    · have := hN0 σ hσ h0
      omega

theorem ip_ne_zero_of_common {G : Type} [Group G] [Fintype G] {ψ A B : G → ℂ} (hψ : IsIrr ψ) (hA : IsChar A)
    (hB : IsChar B) (hψA : ip ψ A ≠ 0) (hψB : ip ψ B ≠ 0) : ip A B ≠ 0 := by
  obtain ⟨L, hL, rfl⟩ := (_root_.GlobalTheory.charDec G A).1 hA
  rw [GlobalTheory.GLq.LabelMul.ip_sum_eq_count hψ L hL] at hψA
  have hm : ψ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast hψA))
  obtain ⟨N, hN, hN0⟩ := list_nat_sum L hL B hB
  rw [ip_list_sum_left, hN]
  exact_mod_cast hN0 ψ hm hψB

theorem ip_add_ne_zero {G : Type} [Group G] [Fintype G] {ψ X Y : G → ℂ} (hψ : IsIrr ψ) (hX : IsChar X)
    (hY : IsChar Y) (h : ip ψ X ≠ 0) : ip ψ (X + Y) ≠ 0 := by
  rw [GlobalTheory.GLq.LabelMul.ip_add_right]
  obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hX
  obtain ⟨l, hl⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hY
  rw [hk] at h
  have hk0 : k ≠ 0 := by exact_mod_cast h
  rw [hk, hl]
  exact_mod_cast (show k + l ≠ 0 by omega)

theorem isChar_hcL_cusp (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (m : ℕ) (hm : degL K = m) :
    IsChar (hcL K m) :=
  (_root_.GlobalTheory.gl_list_product_perm_char g K K m hm.symm (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp))).1

theorem ip_hc_left (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc m 1 σ β (m + 1)) ≠ 0) : ip ψ (hc m 1 (hcL K m) β (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g m 1 (m + 1) rfl).1
  exact ip_add_ne_zero hψ (hc σ β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ) hβ) (hc R β hR hβ) h

theorem ip_hc_right (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc 1 m β σ (m + 1)) ≠ 0) : ip ψ (hc 1 m β (hcL K m) (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g 1 m (m + 1) (by omega)).1
  exact ip_add_ne_zero hψ (hc β σ hβ (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ)) (hc β R hβ hR) h

theorem eq_of_isCuspOf_det (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) (h : GlobalTheory.GLp.IsCharLab L θ c)
    (P : (ZMod g)[X])
    (hP : IsCuspOf L P (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) : P = X - C c := by
  obtain ⟨⟨hm, -, h0, hdeg⟩, -, hf⟩ := hP
  have hPe : P = X - C (-P.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hdeg
  have hc'0 : -P.coeff 0 ≠ 0 := neg_ne_zero.2 h0
  obtain ⟨u, hu⟩ := GlobalTheory.GLq.LabelDet.gen_one_mem L
  let y : Gn g 1 := Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Mt g 1).toMonoidHom u
  have hy00 : (y : Mt g 1) 0 0 = u := by simp [y]
  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    simp [Matrix.charpoly, Matrix.det_fin_one]
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0) ∈ Formalism.CyclotomicNorms.rootsBar P := by
    rw [hPe]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hz : L.gen 1 ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly := by
    rw [hcp, hy00, ← hu]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hirr : Irreducible (y : Mt g 1).charpoly := by rw [hcp]; exact irreducible_X_sub_C _
  have key := hf _ hx y hirr _ hz
  have hxp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc'0, map_one]
  have hth := GlobalTheory.GLq.LabelDet.theta_gen_pow L hxp 1
  rw [pow_one, pow_one] at hth
  have hdet : Matrix.GeneralLinearGroup.det y = u := by ext; simp [y, Matrix.det_fin_one]
  simp only [hdet, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one, hth] at key
  rw [h.2 u hu] at key
  have := L.teich_inj _ _ ((_root_.map_ne_zero _).2 h.1) ((_root_.map_ne_zero _).2 hc'0) key
  rw [hPe, (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective this]

end GlobalTheory.GLq.DetRoot

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

theorem root_of_hc_det : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]),
    IsIrr ψ → HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  intro g _ L n ψ f hψ hL σ hσ θ c hlab
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨K, hK, hKd, hKi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list g n σ hσ
  subst hKd
  have hβI : IsIrr (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hβC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβI
  have hβcusp : IsCusp (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hβI, fun a h1 h2 => by omega⟩
  have hQc : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (hQ q hq).2.1
  have hA := isChar_hcL_cusp _ hQc _ hQd

  have fin : ∀ K' : List (Pc g), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot c := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := eq_of_isCuspOf_det L θ c hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  have hbc : ∀ p ∈ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)], IsCusp p.2 := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hβcusp
  have hKc := fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := ip_hc_left _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc (degL K) 1 (hcL K (degL K))
        (hcL [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)] 1) (degL K + 1) =
        hcL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) (degL K + 1) :=
      (GlobalTheory.GLq.LabelMul.hcL_append K _ hKc (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hbc p hp))
        (degL K + 1) (by simp [degL])).symm
    rw [GlobalTheory.GLq.IpCuspProd.hcL_single 1 _ (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hβC)] at e2
    rw [e2] at h2
    have hKd' : degL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) =
        degL K + 1 := by simp [degL]
    have hB := isChar_hcL_cusp _ (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp) _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) ?_
      (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp)).1 hn)
  · have h2 := ip_hc_right _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc 1 (degL K) (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (hcL K (degL K))
        (degL K + 1) =
        hcL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) (degL K + 1) :=
      (hcL_cons (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) K (degL K + 1)).symm
    rw [e2] at h2
    have hKd' : degL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) =
        degL K + 1 := by simp [degL]; omega
    have hKc' : ∀ p ∈ (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K,
        IsCusp p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hβcusp
      · exact hK p hp
    have hB := isChar_hcL_cusp _ hKc' _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) ?_
      List.mem_cons_self
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc hKc').1 hn)

end GlobalTheory.GLq.DetRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mem_nonZeroDivisors_of_associated' {R : Type} [CommRing R] {a b : R} (h : Associated a b)
    (ha : a ∈ nonZeroDivisors R) : b ∈ nonZeroDivisors R := by
  obtain ⟨v, rfl⟩ := h
  exact mul_mem_nonZeroDivisors.mpr ⟨ha, v.isUnit.mem_nonZeroDivisors⟩

theorem mul_cancel_of_rel {R : Type} [CommRing R] {n : Type} [Fintype n] {N : ℕ} {ef eg eh : R}
    (hg : eg ∈ nonZeroDivisors R) (hh : eh ∈ nonZeroDivisors R) {Pf Pg Ph ε₁ ε₂ ε₃ : Matrix n n R}
    (r1 : eg ^ N • (Pf * ε₁) = ef ^ N • Pg) (r2 : eh ^ N • (Pg * ε₂) = eg ^ N • Ph)
    (r3 : eh ^ N • (Pf * ε₃) = ef ^ N • Ph) : Pf * (ε₁ * ε₂) = Pf * ε₃ := by
  have key : (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂)) = (eg ^ N * eh ^ N) • (Pf * ε₃) := by
    calc (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂))
        = eh ^ N • ((eg ^ N • (Pf * ε₁)) * ε₂) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = eh ^ N • ((ef ^ N • Pg) * ε₂) := by rw [r1]
      _ = ef ^ N • (eh ^ N • (Pg * ε₂)) := by
          rw [Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
      _ = ef ^ N • (eg ^ N • Ph) := by rw [r2]
      _ = eg ^ N • (ef ^ N • Ph) := by rw [smul_smul, smul_smul, mul_comm]
      _ = eg ^ N • (eh ^ N • (Pf * ε₃)) := by rw [r3]
      _ = (eg ^ N * eh ^ N) • (Pf * ε₃) := by rw [smul_smul]
  have hc : eg ^ N * eh ^ N ∈ nonZeroDivisors R :=
    mul_mem_nonZeroDivisors.mpr ⟨pow_mem hg _, pow_mem hh _⟩
  ext i j
  have e := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hc).mp e

theorem rel_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  intro l _ K bk d ρ τ s ht B f₀ h0 f g h ε₁ ε₂ ε₃ h1 h2 h3
  have hn : ∀ k : Hom bk.prism B, ‖toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k X)‖ ≤ bk.ρ₀ := fun k =>
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ k).1
  have hE : ∀ k : Hom bk.prism B,
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := fun k =>
    mem_nonZeroDivisors_of_associated' ((_root_.GlobalTheory.BSP.hf_E_pair l K bk B f₀ k).2.1.map (toDisc l (BK.hf f₀ X) bk.ρ₀)) h0
  have mf := isDiscMap_map (BK.hf f) (hn f)
  have mg := isDiscMap_map (BK.hf g) (hn g)
  have mh := isDiscMap_map (BK.hf h) (hn h)
  have hF : Disc.map (BK.hf f) (hn f) (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈
      nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    rw [mf.ext]; exact hE f
  exact _root_.GlobalTheory.BSP.Height.bas_map_cancel_left l K bk d ρ τ s ht (Disc l (BK.hf f₀ X) bk.ρ₀) _ hF _ _
    (mul_cancel_of_rel (hE g) (hE h) (h1 _ _ mf mg) (h2 _ _ mg mh) (h3 _ _ mf mh))

end GlobalTheory.BSP.Height
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.Height

theorem isDiscMap_comp' {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A'']
    {u : A} {u' : A'} {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''}
    {F : Disc l u ρ →+* Disc l u' ρ'} {G : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hG : IsDiscMap (l := _) (u := _) (ρ := _) g G) : IsDiscMap (l := _) (u := _) (ρ := _) (g.comp f) (G.comp F) :=
  ⟨fun a => by simp [hF.ext, hG.ext], fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem rel_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  intro l _ K bk d ρ τ s ht B B' f₀ f g f₀' k ε hrel
  have hk : ‖toDisc l (BK.hf f₀' X) bk.ρ₀ (k.f (BK.hf f₀ X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B' f₀' (k.comp f₀)).1
  refine ⟨⟨Disc.map k.f hk, isDiscMap_map k.f hk⟩, ?_⟩
  intro Fk hFk Ff' Fg' hf' hg'
  have hff := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ f).1
  have hgg := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ g).1
  have h := congrArg (fun M => Matrix.map M Fk)
    (hrel _ _ (isDiscMap_map (BK.hf f) hff) (isDiscMap_map (BK.hf g) hgg))
  have e1 : Fk.comp (Disc.map (BK.hf f) hff) = Ff' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf f) hff) hFk).unique hf'
  have e2 : Fk.comp (Disc.map (BK.hf g) hgg) = Fg' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf g) hgg) hFk).unique hg'
  subst e1 e2
  ext i j
  have h2 := congrFun (congrFun h i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_mul, map_pow, map_sum, smul_eq_mul,
    hFk.ext, RingHom.comp_apply] at h2 ⊢
  exact h2

end GlobalTheory.BSP.Height
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvaluesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeSpan_correction_distinct_eigenvalues : ∀ {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A), z ≠ 0 → (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) → (∀ x, AbsIrrDistinct (overK (rep x))) → InRing T rep eB → eB * eB = eB → (∀ x, ((eB x).map (toFr A)).rank = t) → ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable → ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x, (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t := by
  first | exact @GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | exact GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | (intros; apply GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues <;> assumption)
end

