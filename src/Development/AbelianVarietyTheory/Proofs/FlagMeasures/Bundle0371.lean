module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangular
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerOneModGAtPlaceZeroElsewhere
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CrtG

theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  unfold gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem exists_crt (D : D7) (p : PlF D) :
    ∃ a₀ : 𝓞 D.host.F,
      (∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧ s * (a₀ - 1) ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)}) ∧
      ∀ p' : PlF D, p' ≠ p → ∃ s : 𝓞 D.host.F, s ∉ p'.asIdeal ∧
        s * a₀ ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)} := by
  set G : Ideal (𝓞 D.host.F) := Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)} with hGdef
  have hG : G ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, hGdef, Ideal.span_singleton_eq_bot]
    exact_mod_cast gS_ne_zero D
  have hirr : Irreducible p.asIdeal := (Ideal.prime_of_isPrime p.ne_bot p.isPrime).irreducible
  obtain ⟨k, A, hA, hGA⟩ := WfDvdMonoid.max_power_factor hG hirr
  have hAp : ¬ A ≤ p.asIdeal := fun h => hA (Ideal.dvd_iff_le.2 h)
  have hsup : p.asIdeal ⊔ A = ⊤ := p.isMaximal.out.2 _ (left_lt_sup.2 hAp)
  have hcop : IsCoprime (p.asIdeal ^ k) A :=
    IsCoprime.pow_left ((Ideal.isCoprime_iff_sup_eq).2 hsup)
  obtain ⟨j, hj, a₀, ha₀, hja⟩ := (Ideal.isCoprime_iff_exists).1 hcop
  refine ⟨a₀, ?_, ?_⟩
  · obtain ⟨s, hsA, hsp⟩ := Set.not_subset.1 hAp
    refine ⟨s, hsp, ?_⟩
    have h1 : s * (a₀ - 1) = -(j * s) := by
      have : a₀ - 1 = -j := by rw [← hja]; ring
      rw [this]; ring
    rw [h1, hGA]
    exact neg_mem (Ideal.mul_mem_mul hj hsA)
  · intro p' hp'
    have hnot : ¬ p.asIdeal ^ k ≤ p'.asIdeal := by
      intro h
      have hle : p.asIdeal ≤ p'.asIdeal := p'.isPrime.le_of_pow_le h
      exact hp' (IsDedekindDomain.HeightOneSpectrum.ext
        (p.isMaximal.eq_of_le p'.isPrime.ne_top hle).symm)
    obtain ⟨s, hsk, hsp'⟩ := Set.not_subset.1 hnot
    refine ⟨s, hsp', ?_⟩
    rw [hGA]
    exact Ideal.mul_mem_mul hsk ha₀

end GlobalTheory.CrtG

namespace GlobalTheory.CrtG

theorem iE_div_g (D : D7) (p : PlF D) (y : 𝓞 D.host.F) (s : 𝓞 D.host.F) (hs : s ∉ p.asIdeal)
    (hy : s * y ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)}) :
    ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (algebraMap D.host.F D.host.E (y : D.host.F)) =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hy
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  set x : D.host.E := algebraMap D.host.F D.host.E (y : D.host.F) / ((gS D : ℕ) : D.host.E) with hx
  have hcx : algebraMap D.host.F D.host.E (s : D.host.F) * x = algebraMap D.host.F D.host.E (c : D.host.F) := by
    have h2 : ((c * ((gS D : ℕ) : 𝓞 D.host.F) : 𝓞 D.host.F) : D.host.F) = ((s * y : 𝓞 D.host.F) : D.host.F) := by
      rw [hc]
    push_cast at h2
    have h3 := congrArg (algebraMap D.host.F D.host.E) h2
    simp only [map_mul, map_natCast] at h3
    rw [hx, mul_div_assoc', div_eq_iff hg, ← h3]
  have hint : IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * x) := by
    rw [hcx]
    exact (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  refine ⟨(D.s.atP p).ιE x, (Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D p x).2 ⟨s, hs, hint⟩, ?_⟩
  rw [← map_mul, hx, mul_div_cancel₀ _ hg]

theorem exists_one_here_zero_elsewhere : ∀ (D : D7) (p : PlF D), ∃ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - 1 = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) ∧ ∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p
  obtain ⟨a₀, ⟨s, hs, h1⟩, h2⟩ := exists_crt D p
  have hint : IsIntegral ℤ (algebraMap D.host.F D.host.E (a₀ : D.host.F)) :=
    (RingOfIntegers.isIntegral_coe a₀).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  refine ⟨⟨algebraMap D.host.F D.host.E (a₀ : D.host.F), hint⟩, ?_, ?_⟩
  · obtain ⟨o, ho, he⟩ := iE_div_g D p (a₀ - 1) s hs h1
    refine ⟨o, ho, ?_⟩
    rw [← he]
    simp
    rfl
  · intro p' hp'
    obtain ⟨s', hs', h'⟩ := h2 p' hp'
    exact iE_div_g D p' a₀ s' hs' h'

end GlobalTheory.CrtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyStepOfFourGlobalLeaves
section
namespace GlobalTheory

theorem stepFamC_of_globalLeaves :
    Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric →
      Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC :=
  fun hG5 hW hG4 hE =>
    Formalism.L2.SG.FamDefs.stepFamC_of (fun D h => _root_.GlobalTheory.localMass_le_genericMass_nine _ _ h) _root_.GlobalTheory.HTieLeaf.main hG5 hW hG4 hE

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinitePlacesNotPrimeToBaseFrameInvariants
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimeAlmostAll

open Formalism.MainNotions.S.LocNG

theorem isUnitO_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} {x y : E} (hx : IsUnitO M x) (hy : IsUnitO M y) : IsUnitO M (x * y) := by
  obtain ⟨hx1, x', hx', hxx⟩ := hx
  obtain ⟨hy1, y', hy', hyy⟩ := hy
  refine ⟨mul_mem hx1 hy1, x' * y', mul_mem hx' hy', ?_⟩
  linear_combination (y * y') * hxx + hyy

theorem isUnitO_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} : IsUnitO M 1 :=
  ⟨one_mem _, 1, one_mem _, mul_one 1⟩

theorem isUnitO_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} {ι : Type} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, IsUnitO M (g i)) :
    IsUnitO M (∏ i ∈ s, g i) :=
  Finset.prod_induction g (IsUnitO M) (fun _ _ => isUnitO_mul) isUnitO_one h

theorem isUnitO_cj {D : D7} (Z : LocDat D) (p : PlF D) {x : (D.s.atP p).Ep} (hx : IsUnitO (Z.M p) x) :
    IsUnitO (Z.M p) ((Z.M p).L.cj x) := by
  obtain ⟨hx1, x', hx', hxx⟩ := hx
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : ∀ y ∈ (Z.M p).L.O, (Z.M p).L.cj y ∈ (Z.M p).L.O := by
    intro y hy
    rw [Z.hcj p, hO] at *
    exact Formalism.L2.SG.Pf.LocFacts.lf_cj_mem p y hy
  refine ⟨hc x hx1, (Z.M p).L.cj x', hc x' hx', ?_⟩
  rw [← map_mul, hxx, map_one]

end GlobalTheory.PrimeAlmostAll


open GlobalTheory.PrimeAlmostAll in
theorem GlobalTheory.PrimeAlmostAll.primeTo_finite : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Gval F00 F'0 ≠ 0 → ∀ FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS, (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p)) → {p : PlF D | ¬ (FP p).PrimeTo}.Finite := by
  intro D Z u u' F00 F'0 hG FP hFP
  let xs : Fin (D.R.rS + 2) → D.host.E := fun l => Formalism.MainNotions.S.Dl F00.fl F'0.fl (l : ℕ)
  have hfin : ({p : PlF D | (Z.M p).split ≠ none} ∪
      (⋃ a : Fin (D.R.rS + 1), {p : PlF D | ¬ LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}) ∪
      {p : PlF D | ¬ LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE (Gval F00 F'0))} ∪
      ⋃ l : Fin (D.R.rS + 2), {p : PlF D | xs l ≠ 0 ∧ ¬ LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE (xs l))}).Finite := by
    refine (((_root_.GlobalTheory.LocSplitFinite.split_finite D Z).union (Set.finite_iUnion fun a => _root_.GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite D Z a)).union (GlobalTheory.T.nonzero_cm_element_local_unit_almost_all D Z _ hG)).union
      (Set.finite_iUnion fun l => ?_)
    by_cases h : xs l = 0
    · simp [h]
    · exact (GlobalTheory.T.nonzero_cm_element_local_unit_almost_all D Z _ h).subset (fun p hp => hp.2)
  refine hfin.subset ?_
  intro p hp
  by_contra hgood
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_not] at hgood
  obtain ⟨⟨⟨hsp, hfr⟩, hGv⟩, hD⟩ := hgood
  apply hp
  have hL4 := _root_.GlobalTheory.LocMinor.leadMinor_atBase D Z p F00 F'0 (Tu D u) (Tu D u') (FP p) (hFP p)
  have hκ : ∀ l : ℕ, LocNG.IsUnitO (Z.M p)
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) := by
    intro l
    refine isUnitO_prod _ _ fun a _ => ?_
    split_ifs
    · exact isUnitO_mul (isUnitO_cj Z p (hfr a)) (hfr a)
    · exact isUnitO_one
  refine ⟨hsp, ?_, ?_⟩
  ·
    have hlast : ∀ a : Fin (D.R.rS + 1), ¬ a.val < D.R.rS → (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a = 1 := by
      intro a ha
      have h1 : a.val = D.R.rS := by omega
      have : frFac Z.δ p a = 1 := by
        unfold frFac
        rw [h1, Nat.sub_self, pow_zero, Ring.inverse_one]
      rw [this, map_one, one_mul]
    have hK : (∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS + 1 then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) =
        ∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1 := by
      refine Finset.prod_congr rfl fun a _ => ?_
      have ha : a.val < D.R.rS + 1 := a.2
      by_cases h : a.val < D.R.rS
      · rw [if_pos ha, if_pos h]
      · rw [if_pos ha, if_neg h, hlast a h]
    set K := ∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1 with hKdef
    have eG : (FP p).Gv = (FP p).Dm (D.R.rS + 1) * (Z.M p).L.cj ((FP p).Dm (D.R.rS + 1)) -
        algebraMap _ _ ((FP p).A.T * (FP p).B.T) * ((FP p).Dm D.R.rS * (Z.M p).L.cj ((FP p).Dm D.R.rS)) := rfl
    have hT := (hFP p).2.2
    rw [hT.1, hT.2, hL4 (D.R.rS + 1), hL4 D.R.rS, hK] at eG
    have eGv : (D.s.atP p).ιE (Gval F00 F'0) =
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F00.fl F'0.fl (D.R.rS + 1)) * (D.s.atP p).ιE (star (Formalism.MainNotions.S.Dl F00.fl F'0.fl (D.R.rS + 1))) -
        ((Tu D u : (D.s.atP p).Ep) * (Tu D u' : (D.s.atP p).Ep)) *
        ((D.s.atP p).ιE (Formalism.MainNotions.S.Dl F00.fl F'0.fl D.R.rS) * (D.s.atP p).ιE (star (Formalism.MainNotions.S.Dl F00.fl F'0.fl D.R.rS))) := by
      simp only [Gval, Formalism.MainNotions.S.Gflag, map_sub, map_mul, map_natCast, Tu]
    have hTT : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Tu D u : (D.s.atP p).Fp) * (Tu D u' : (D.s.atP p).Fp)) =
        (Tu D u : (D.s.atP p).Ep) * (Tu D u' : (D.s.atP p).Ep) := by
      rw [map_mul, map_natCast, map_natCast]
    rw [hTT, map_mul, map_mul, cj_iota (Z.hcj p), cj_iota (Z.hcj p)] at eG
    have : (FP p).Gv = (K * (Z.M p).L.cj K) * (D.s.atP p).ιE (Gval F00 F'0) := by
      rw [eG, eGv]; ring
    rw [this]
    exact isUnitO_mul (isUnitO_mul (hκ D.R.rS) (isUnitO_cj Z p (hκ D.R.rS))) hGv
  ·
    intro l hl
    simp only [LocNG.FPair.ends, Finset.mem_filter, Finset.mem_range] at hl
    obtain ⟨hlr, -, hu⟩ := hl
    rw [hL4 l] at hu ⊢
    by_cases h0 : xs ⟨l, hlr⟩ = 0
    · exfalso
      have h0' : Formalism.MainNotions.S.Dl F00.fl F'0.fl l = 0 := h0
      rw [h0', map_zero, mul_zero] at hu
      exact not_isUnit_zero hu
    · exact isUnitO_mul (hκ l) (hD ⟨l, hlr⟩ h0)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameStandardLatticeHermitianIntegral
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocStdInt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars (Valuation.integer (ValuativeRel.valuation F)))

def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

lemma h_prF (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h (Fr.prF v) y = H.h v y - ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      - ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  show hl H y (Fr.prF v) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [FrameD.prF, map_sub, map_sum, map_smul, smul_eq_mul]
  rfl

lemma h_expand (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h v y = H.h (Fr.prF v) y + ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  rw [h_prF H Fr v y]
  ring

lemma h_prF_es (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v : V) (b : Fin r) :
    H.h (Fr.prF v) (Fr.es b) = 0 := by
  rw [h_prF H Fr v (Fr.es b)]
  have hdual : ∀ a, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a => Fr.h_es a b
  simp [hdual, Fr.h_ss]

lemma h_symm_mem (H : HermSp M V) {x y : V} (h : H.h x y ∈ M.L.O) : H.h y x ∈ M.L.O := by
  rw [H.h_herm]
  exact cj_mem h

lemma span_left (H : HermSp M V) (S : Set V) (y : V) (h : ∀ x ∈ S, H.h x y ∈ M.L.O) :
    ∀ x ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : H.h 0 y = 0 := (hl H y).map_zero
    rw [h0]
    exact zero_mem _
  | add x x' _ _ hx hx' =>
    rw [H.h_add_left]
    exact add_mem hx hx'
  | smul c x _ hx =>
    rw [Subring.smul_def, H.h_smul_left]
    exact mul_mem c.2 hx

private lemma form_mem_O_of_frame_coords_mem_O (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) {u v : V}
    (hu : (∀ a, H.h u (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h u (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF u ∧ H.mkW Fr.f w ∈ L)
    (hv : (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L) :
    H.h u v ∈ M.L.O := by
  obtain ⟨hus, hue, wu, hwu, hwuL⟩ := hu
  obtain ⟨hvs, hve, wv, hwv, hwvL⟩ := hv
  have hpp : H.h (Fr.prF v) (Fr.prF u) ∈ M.L.O := by
    have h0 := (hL.2.1 wv).1 hwvL wu hwuL
    rwa [hwv, hwu] at h0
  have hwu0 : ∀ x ∈ H.X Fr.f, H.h (wu : V) x = 0 := wu.2
  have he0 : ∀ a, H.h (Fr.e a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, ← hwu, hwu0 (Fr.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero]
  have hs0 : ∀ a, H.h (Fr.es a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, h_prF_es H Fr u a, map_zero]
  have hvu : H.h v (Fr.prF u) ∈ M.L.O := by
    rw [h_expand H Fr v (Fr.prF u)]
    simp only [he0, hs0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hpp
  rw [h_expand H Fr u v]
  refine add_mem (add_mem (h_symm_mem H hvu) ?_) ?_
  · exact sum_mem fun a _ => mul_mem (hus a) (h_symm_mem H (hve a))
  · exact sum_mem fun a _ => mul_mem (hue a) (h_symm_mem H (hvs a))

theorem lamStd_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L), ∀ x ∈ Fr.LamStd L, ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr L hL x hx y hy
  unfold FrameD.LamStd at hx hy
  refine span_left H _ y ?_ x hx
  intro u hu
  exact h_symm_mem H (span_left H _ u (fun v hv => form_mem_O_of_frame_coords_mem_O H Fr L hL hv hu) y hy)

end GlobalTheory.LocStdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedFrameCongruentUnitriangularAtPrimes
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GluedCong

theorem bc_eq (D : D7) (Z : LocDat D) (p : PlF D) (v : (VS D).V) :
    (GlobalTheory.HL.placesOf Z).bc p ((VS D).frame.equivFun v) = baseChange₂ D p v := by
  funext i; rfl

theorem lat_eq (D : D7) (Z : LocDat D) (p : PlF D) (L : LV D) :
    (GlobalTheory.HL.placesOf Z).lat p (L.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))) = lattice₂ D Z.M p L := by
  unfold GlobalTheory.HL.Places.lat lattice₂
  congr 1
  ext z
  simp only [Set.mem_image, Submodule.map_coe, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (bc_eq D Z p v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, bc_eq D Z p v⟩

theorem smul_mem_gmap (D : D7) (γ : GV D) (I : Ideal (𝓞 D.host.E))
    (L : LV D) (v : (VS D).V) (s : 𝓞 D.host.E) (h : s • v ∈ I • L) :
    s • γ v ∈ I • Formalism.HermitianLatticesTheory.gmap γ L := by
  have hg1 : I • Formalism.HermitianLatticesTheory.gmap γ L = (I • L).map ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_smul'']
  rw [hg1]
  refine Submodule.mem_map.2 ⟨s • v, h, ?_⟩
  exact (γ : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower s v


set_option maxHeartbeats 1000000 in
theorem glued_loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP
  obtain ⟨sg, hsp, hdict⟩ := _root_.GlobalTheory.LocCong.qsmul_latP_le_gS D Z P hP
  have hL0 := hL
  obtain ⟨hlat, hloc⟩ := hL
  obtain ⟨τ, hτ, hτL⟩ := hloc (below D P)
  obtain ⟨B, hB1, hB2, hBy⟩ := _root_.GlobalTheory.Sloc.AdaptExpand.adapt_expand D (lf D (X.Fu u)) F g hA Z (below D P) (FP (below D P)).A.f (hB (below D P)).1
  obtain ⟨B', hB1', hB2', hBx⟩ := _root_.GlobalTheory.Sloc.AdaptExpand.adapt_expand D (lf D (X.Fu u')) F' g' hA' Z (below D P) (FP (below D P)).B.f (hB (below D P)).2.1
  have hU := _root_.GlobalTheory.FrameFactorG.frFac_unit_at_g D (Tu D u) (Tu D u') (X.Fu u) F F' Z FP hB Λ y hL0 g hA hr P hP
  have hmemg : ∀ (γ : GV D) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T), IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) →
      ∀ a, γ (frame (lf D F0) a) ∈ Λ := by
    intro γ T F0 h a
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.1 (_root_.GlobalTheory.Unfold.RowFrame.frame_mem D F0 _ h a)
    have e : γ (frame (lf D F0) a) = v := by
      rw [← hve]
      show γ (γ⁻¹ v) = v
      exact γ.apply_symm_apply v
    rw [e]; exact hv
  have hyL : ∀ a, baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g (X.Fu u) hr a, rfl⟩
  have hxL : ∀ a, baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g' (X.Fu u') hr' a, rfl⟩
  obtain ⟨ξp, hξO, hξ1, hξ2, hξc⟩ := _root_.GlobalTheory.loc_cong_unitri (locH Z (below D P)) (FP (below D P)) (y (below D P)) τ sg hsp hτ
    (fun b => baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) b))) (fun b => baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) b))) B B' hB1 hB1'
    (fun a => by rw [hB2, hB2'])
    (fun a => by
      rw [hB2]
      exact ⟨(hU a).2, frFac Z.δ (below D P) a, (hU a).1, Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z (below D P) a)⟩)
    hBy hBx hyL hxL
  have hfg : (Λ.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))).FG := hlat.fg.map _
  have hpos : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.HL.LocCongApprox.loc_cong_approx (GlobalTheory.HL.placesOf Z) (nV D) D.R.rS _ hfg
    (gS D) hpos (below D P) (fun a => (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)))
    (fun b => (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b))) ξp hξO hξ1 hξ2
    (fun a => by
      rw [lat_eq, bc_eq, ← hτL]
      exact hyL a)
    (fun b => by
      rw [← Submodule.map_smul'', lat_eq]
      have h1 := hdict Λ _ (hτL ▸ hξc b)
      simp only [bc_eq]
      exact h1)
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  obtain ⟨v, hv⟩ : ∃ v, v = g' (frame (lf D (X.Fu u')) b) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • g (frame (lf D (X.Fu u)) a) := ⟨_, rfl⟩
  have hφv : (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b)) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)) = (VS D).frame.equivFun v := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, map_sub, map_sum]
    simp only [map_smul]
  rw [hφv] at h
  obtain ⟨s, hs, hsv⟩ := h
  rw [← Submodule.map_smul''] at hsv
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hzs : z = s • v := by
    apply ((VS D).frame.equivFun).injective
    have e1 : (VS D).frame.equivFun z = s • (VS D).frame.equivFun v := hzv
    rw [e1]
    exact (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).map_smul_of_tower s v).symm
  have hiso : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hA.1) hA'.1
  have hfr : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b = (g⁻¹ * g') (frame (lf D (X.Fu u')) b) := by
    unfold mapLF
    rw [dite_eq_left hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(g⁻¹ * g')) _ _) b).symm
  have htarget : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b = g⁻¹ v := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfr, hv, map_sub, map_sum, LinearEquiv.mul_apply]
    unfold frameAct
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun a _ => ?_)
    exact (((g⁻¹ : GV D).map_smul _ _).trans (congrArg _ (g.symm_apply_apply _))).symm
  have hsv' : s • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    rw [← hzs]; exact hz
  refine ⟨s, hs, ?_⟩
  rw [htarget]
  exact smul_mem_gmap D g⁻¹ (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}) Λ v s hsv'

end GlobalTheory.Unfold.GluedCong
end
end

