module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
public import Development.AutomorphicArithmetic.ResidueCharacters.FiniteRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.LocRes
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N.LocRes

variable {l : ℕ} [Fact l.Prime]

abbrev res {K K' LL : FinExt l} (hle : GK K' ≤ GK K) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    LocLat ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL) :=
  LiftingTheory.resLoc (Subgroup.inclusion hle) (continuous_subtype_val.subtype_mk _) T

theorem res_crys (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((LT l).PD K) ↥LL.1 ↥(OL LL))
    {K K' LL : FinExt l} (hKK : K.1 ≤ K'.1) (hle : GK K' ≤ GK K) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys ((LT l).PD K) T.ρ) :
    IsCrys ((LT l).PD K') (res hle T).ρ ∧ ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      IsJumpV ((LT l).PD K') (res hle T).ρ τ a ↔
        IsJumpV ((LT l).PD K) T.ρ (τ.comp (IntermediateField.inclusion hKK)) a := by
  obtain ⟨h1, h2⟩ := hres l K' K hKK hle LL T hT
  refine ⟨h1, fun τ a => ?_⟩
  rw [isJumpV_iff _ _ ((hF K' LL).2.2.2 (GRep.ofLat (res hle T)) h1),
    isJumpV_iff _ _ ((hF K LL).2.2.2 (GRep.ofLat T) hT), h2]

theorem caseB (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (hK : Ks K s = K.1) :
    LiftingTheory.CaseB (H.W K s LL h) := by
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, H.W_s]
    show (x : GQ l) ∈ (Ks K s).fixingSubgroup
    rw [hK]
    exact x.2
  · have h1 := GlobalTheory.Cyc.finrank_Ks K s h.1
    haveI : Module.Free ↥(K0 K) ↥K.1 := Module.Free.of_divisionRing _ _
    rw [hK, ← Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1] at h1
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    rw [P.PD_p, H.W_s]
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem vdeg_le (K : FinExt l) {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) :
    padicValNat l (Module.finrank ℚ_[l] ↥(Ks K m)) - padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) ≤ m := by
  have hp : l.Prime := Fact.out
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have h0 : Module.finrank ℚ_[l] ↥(K0 K) ≠ 0 := Module.finrank_pos.ne'
  have h1 : l - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
  have key : ∀ j, 1 ≤ j → padicValNat l (Module.finrank ℚ_[l] ↥(Ks K j)) =
      padicValNat l (Module.finrank ℚ_[l] ↥(K0 K)) + (padicValNat l (l - 1) + (j - 1)) := by
    intro j hj
    rw [GlobalTheory.Cyc.finrank_Ks K j hj, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h0 (mul_ne_zero h1 (pow_ne_zero _ hp.ne_zero)),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h1 (pow_ne_zero _ hp.ne_zero), (show padicValNat l (l ^ (j - 1)) = j - 1 from by rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow])]
  rw [key m hm, key s hs]
  omega

theorem jset_sub (D : D7) (HW : HWOf D.loc) (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL))
    {K K' LL : FinExt l} (hKK : K.1 ≤ K'.1) (hle : GK K' ≤ GK K) {s : ℕ} (h : Good K' s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ) (U : Set ℤ)
    (hU : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ U) :
    LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K' s LL h) (res hle T) ⊆ U := by
  intro a ha
  obtain ⟨τ, hτ⟩ := JsetEmb.jsetSplit_all D HW l K' s LL h (res hle T) a ha
  exact hU _ a (((res_crys D.loc hres hF hKK hle T hT).2 τ a).1 hτ)

theorem pow_val_smul_mem (LL : FinExt l) {M : Type} [AddCommGroup M] [Module ↥(OL LL) M] (S : Submodule ↥(OL LL) M)
    {d : ℕ} (hd : d ≠ 0) {c : M} (hc : (d : ↥(OL LL)) • c ∈ S) :
    ((l : ↥(OL LL)) ^ padicValNat l d) • c ∈ S := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit ((ordCompl[l] d : ℕ) : ↥(OL LL)) := by
    have h1 : IsUnit ((ordCompl[l] d : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_ordCompl hp hd)
    simpa using h1.map (algebraMap ℤ_[l] ↥(OL LL))
  obtain ⟨u, hu⟩ := hu
  have e : (d : ↥(OL LL)) = u * (l : ↥(OL LL)) ^ padicValNat l d := by
    rw [hu, Nat.padicValNat_def, ← Nat.factorization_def d hp]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self d l]
    push_cast; ring
  have := S.smul_mem ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) hc
  rwa [e, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this

end UpperTheory.N.LocRes

end
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.TransferMemBlochKatoCocycles
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace UpperTheory.N.CorD

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]
    {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

open GlobalTheory.InducedSectionsSpanStatement

theorem transfer_mem_blochKato_cocycles [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G'))
    [Fintype (G' ⧸ ι.range)] (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) (T : LocLat G' Qp LL O)
    (z : G → T.V) (hz : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ) : trCochain ι T z ∈ finiteCocycles PD' T.ρ := by
  have hinj : Function.Injective ι := he.injective
  have hinv : ∀ a : G, Function.invFun ι (ι a) = a := fun a => Function.leftInverse_invFun hinj a
  have hmem := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  obtain ⟨hzc, x, hx⟩ := hz
  obtain ⟨hzcont, hzcoc⟩ := hzc
  set f : G' → T.V := fun h => z (Function.invFun ι h) with hf
  have htr : ∀ g, trCochain ι T z g =
      ∑ q : G' ⧸ ι.range, T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q)) := by
    intro g
    rw [trCochain_apply]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsTopologicalAddGroup T.V :=
      { continuous_neg := by
          have := continuous_const_smul (-1 : LL) (T := T.V)
          simpa using this }
    have hρc : ∀ g : G', Continuous (T.ρ g) := fun g =>
      IsModuleTopology.continuous_of_linearMap (R := LL) (T.ρ g)
    have hfc : ContinuousOn f (ι.range : Set G') := by
      rw [continuousOn_iff_continuous_restrict]
      refine (hzcont.comp (he.toHomeomorph).symm.continuous).congr ?_
      rintro ⟨h, a, rfl⟩
      simp only [Function.comp_apply, hf, hinv]
      congr 1
    have hc := GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho hρc f hfc
    have hfun : (trCochain ι T z : G' → T.V) = fun g => ∑ q : G' ⧸ ι.range,
        T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q)) := funext htr
    rw [hfun]
    exact hc
  · intro a b
    rw [htr, htr, htr]
    refine hmem.2.1 f ?_ a b
    rintro _ ⟨a', rfl⟩ _ ⟨b', rfl⟩
    simp only [hf, ← map_mul, hinv]
    exact hzcoc a' b'
  · have hW := GlobalTheory.transfer_cocycle_formula LL G' (T.V ⊗[Qp] B) (repVB PD' T) ι.range
    refine ⟨∑ q : G' ⧸ ι.range, repVB PD' T (Quotient.out q) x, fun g => ?_⟩
    have key := hW.2.2.1 (fun h => f h ⊗ₜ[Qp] (1 : B)) x (by
      rintro _ ⟨a, rfl⟩
      simp only [hf, hinv]
      rw [hx a, actVB_res PD PD' ι hι hact T a x]
      rfl) g
    simp only at key
    rw [htr, TensorProduct.sum_tmul]
    have hstep : ∀ (h : G') (v : T.V), (T.ρ h v) ⊗ₜ[Qp] (1 : B) = repVB PD' T h (v ⊗ₜ[Qp] 1) := by
      intro h v
      exact (actVB_tmul_one PD' T h v).symm
    simp only [hstep]
    rw [key]
    rfl

theorem index_smul_mem [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G'))
    [ι.range.FiniteIndex] (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) (T : LocLat G' Qp LL O)
    (c : G' → T.V ⧸ T.L.T) (hc : ∀ a b, c (a * b) = c a + actD T.L a (c b))
    (hres : (fun g => c (ι g)) ∈ HfD PD (LiftingTheory.resLoc ι hι T).L) :
    ((ι.range.index : ℕ) : O) • c ∈ HfD PD' T.L := by
  haveI : Fintype (G' ⧸ ι.range) := Subgroup.fintypeQuotientOfFiniteIndex
  have hinj : Function.Injective ι := he.injective
  have hinv : ∀ a : G, Function.invFun ι (ι a) = a := fun a => Function.leftInverse_invFun hinj a
  obtain ⟨y, hy, bb, hbb, hsum⟩ := Submodule.mem_sup.mp hres
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨w, rfl⟩ := hbb
  have hzf : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ := hz
  have htrz := transfer_mem_blochKato_cocycles PD PD' ι hι he ho hact T z hzf
  have hD := GlobalTheory.transfer_cocycle_formula O G' (T.V ⧸ T.L.T) (repD T.L) ι.range
  set S' : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, c (Quotient.out q) with hS'
  set S : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out q) w with hS
  have hcsplit : ∀ a : G, c (ι a) = T.L.T.mkQ (z a) + (actD T.L (ι a) w - w) := by
    intro a
    have := congrFun hsum a
    rw [← this]
    rfl
  have h4 := hD.2.2.2 c (fun a b => hc a b)
  have h3 := hD.2.2.1 (fun h => actD T.L h w - w) w (fun h _ => rfl)
  have hkey : ∀ g : G', ((ι.range.index : ℕ) : O) • c g =
      T.L.T.mkQ (trCochain ι T z g) + (repD T.L g (S - S') - (S - S')) := by
    intro g
    have h4g := h4 g
    have h3g := h3 g
    dsimp only at h4g h3g
    have e1 : (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
        (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) =
        T.L.T.mkQ (trCochain ι T z g) + ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
          (actD T.L ((Quotient.out (g • q))⁻¹ * g * Quotient.out q) w - w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [trCochain_apply, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hD.1 g q)
      rw [← ha, hcsplit a, hinv, map_add (f := _)]
      rfl
    rw [Nat.cast_smul_eq_nsmul]
    have hh : ι.range.index • c g = (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
        (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) - (repD T.L g S' - S') := by
      rw [h4g]
      abel
    rw [hh, e1, h3g, map_sub]
    abel
  refine Submodule.mem_sup.mpr ⟨T.L.T.mkQ.compLeft G' (trCochain ι T z), ⟨_, htrz, rfl⟩,
    fun g => repD T.L g (S - S') - (S - S'), ⟨S - S', rfl⟩, ?_⟩
  funext g
  rw [Pi.add_apply, Pi.smul_apply, hkey g]
  rfl

end UpperTheory.N.CorD

end
end

