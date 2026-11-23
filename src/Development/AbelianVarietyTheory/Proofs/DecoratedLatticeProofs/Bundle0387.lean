module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevYZero

open Formalism.IndefR.Lev Formalism.L2.DIV

theorem lev_datY_zero {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (r t : ℕ) (hr : r ≤ V.rank) (hn : V.rank = r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ ξ) (hL : L = datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (g : GL (Fin V.rank) (Lev.EAf D))
    (hU : g ∈ UA D.sp.cm V.gram) :
    (g ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ g ∈ St β ∧ (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H) ∧
      ∀ h : (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H, levFn β L g = P.chi ⟨_, h⟩ := by
  subst hL
  have hP : (datY (D := D) V.rank r t 0 hr Pg ∅ P χ ξ Frm.B).P = P := by simp [datY]
  constructor
  · rw [mem_lev, mem_parLev]
    constructor
    · rintro ⟨⟨-, hS, -, -⟩, hH⟩
      refine ⟨hS, ?_⟩
      rw [hP] at hH
      exact hH
    · rintro ⟨hS, hH⟩
      refine ⟨⟨hU, hS, fun PP _ => ?_, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
      · rw [mem_blockTri]
        intro i j hij
        exfalso
        have hi : (i : ℕ) < r := hn ▸ i.2
        have hj : (j : ℕ) < r := hn ▸ j.2
        simp [datY, blkOf, hi, hj] at hij
      · show rTup β _ g ∈ _
        rw [hP]
        exact hH
  · intro h
    unfold levFn
    change ext1 P.H P.chi (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) * _ * _ = _
    simp only [datY, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    exact extendOne_of_mem _ h

end GlobalTheory.LevYZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepComb

variable {D : D7}

theorem idem_mem_idAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) :
    es ∈ GlobalTheory.FinPl.idAt D (· = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  have h' := h
  obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := h'
  have hw := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D es PP w ε h hε a3
  have hε' := hε
  obtain ⟨α, rfl, -, h0⟩ := hε'
  have hm : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ GlobalTheory.FinPl.idAt D (· = w) :=
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = w)) (fun v hv => h0 v hv) 1
  have e1 : es = es * (es + cA D es) := by rw [mul_add, a1, a2, add_zero]
  rw [e1, a3, hw]
  exact Ideal.mul_mem_left _ _ hm

theorem idemSum_mem_idAt {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) :
    e ∈ GlobalTheory.FinPl.idAt D (fun p => ∃ PP ∈ Z, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  exact Ideal.sum_mem _ fun PP hPP =>
    GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => ⟨PP, hPP, hw⟩) (idem_mem_idAt (hes PP hPP))

theorem mxAt_of_mem_half {S T : HSp D} {a : AE D} {P : GlobalTheory.FinPl.Pl D → Prop} (ha : a ∈ GlobalTheory.FinPl.idAt D P)
    {u : WO S T} (hu : u ∈ GlobalTheory.PlaceModel.half S T a) : GlobalTheory.FinPl.MxAt P u := by
  intro i j
  rw [← (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu i j]
  exact Ideal.mul_mem_right _ _ ha

theorem isSBHalf_stepDatumQ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (e : AE D) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsIdemSum e (L.Pg ∪ Q)) :
    IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T =>
      if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
      else 0) := by
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ (L.Pg ∪ Q)
    (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
        GlobalTheory.PlaceDatum.omegaQ_congr Q L.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)]

theorem comb_add' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_add (f := _)]

theorem comb_smul' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_smul]

theorem comb_zero' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (f : WO S T → ℂ) :
    comb ψ S T 0 f = 0 := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_zero]

theorem comb_single' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_single]

theorem mem_of_mem_support_add {S T : HSp D} {H : Set (WO S T)} {c c' : WO S T →₀ ℂ} (hc : ∀ u ∈ c.support, u ∈ H)
    (hc' : ∀ u ∈ c'.support, u ∈ H) : ∀ u ∈ (c + c').support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  have h2 : c' u = 0 := by
    by_contra h
    exact hn (hc' u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.add_apply, h1, h2, add_zero])

theorem mem_of_mem_support_smul {S T : HSp D} {H : Set (WO S T)} (a : ℂ) {c : WO S T →₀ ℂ}
    (hc : ∀ u ∈ c.support, u ∈ H) : ∀ u ∈ (a • c).support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.smul_apply, h1, smul_zero])


set_option maxHeartbeats 1000000 in
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum in
theorem exists_comb_of_isThetaAt {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (e : AE D) (f₀ Φ f : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : e * e = e) (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    ∃ d : WO S T →₀ ℂ, (∀ u ∈ d.support, u ∈ half S T (e + cA D e)) ∧ f = comb ψ S T d f₀ := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine ⟨Finsupp.single (x + y) (ψ (symplOH S T x y)), fun u hu => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
      exact add_mem (GlobalTheory.FinPl.DatumBack.half_le_sum hce hx) (GlobalTheory.FinPl.DatumBack.half_le_sum' hec hy)
    · rw [comb_single']
  | zero =>
    exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), by rw [LinearMap.map_zero, comb_zero']⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, hc, hc'⟩ := hg
    obtain ⟨c', hd, hd'⟩ := hg'
    refine ⟨c + c', mem_of_mem_support_add hc hd, ?_⟩
    rw [LinearMap.map_add (f := _), hc', hd', comb_add']
  | smul a g _ hg =>
    obtain ⟨c, hc, hc'⟩ := hg
    refine ⟨a • c, mem_of_mem_support_smul a hc, ?_⟩
    rw [LinearMap.map_smul, hc', comb_smul']

theorem exists_comb_of_isStepVecOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧ f = comb ψ S T d f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f hS hT _ _ hv
  obtain ⟨hvac, e, he, hθ⟩ := hv
  have hSB := isSBHalf_stepDatumQ S T ΛS ΛT βS βT LS χj ξ Q e hS hT he
  obtain ⟨d, hd, hf⟩ := exists_comb_of_isThetaAt ψ ΛS ΛT e f₀ _ f hvac.1 hS hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hSB hθ
  have hI := idemSum_mem_idAt he
  exact ⟨d, fun u hu => mxAt_of_mem_half (add_mem hI (GlobalTheory.LastOpPf.cA_mem_idAt hI)) (hd u hu), hf⟩

end GlobalTheory.StepComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NChainChar

theorem edge_sum_typeFrame {K : Type} [Field K] (κ τ s N r p : ℕ) (hr : r ≤ N) (hrk : r = κ + (s + 1))
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) 0 ≃ Fin N) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (ϖ : Kˣ)
    (q : GL (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) K) (hq : GlobalTheory.RootEx.InN p q) :
    (∑ i : Fin r, ∑ j : Fin r, if GlobalTheory.chainEdge κ i j then
      (((GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas⁻¹).val * q.val *
        (GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas.val)
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (ϖ : K) * GlobalTheory.RootEx.simpleSum q := by
  subst hrk
  rw [GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_inv_val, GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  let ε : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have hε : ∀ a, e.symm (Fin.castLE hr (ε a)) = Sum.inl a := by
    intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [he]
    rcases a with a | a <;> simp [ε, GlobalTheory.SymBridge.zPos]
  rw [← ε.sum_comp]
  simp only [← ε.sum_comp (fun j => ite _ _ _), hε]
  have h1 : ∀ i : Fin κ, GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inl i)) =
      Sum.inl (Sum.inl (Sum.inl i)) := fun i => rfl
  have h2 : ∀ i : Fin (s + 1), GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inr i)) =
      Sum.inr i := fun i => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) i
  have hX : ∀ a b : GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0,
      q.val (Sum.inl a) (Sum.inl b) = (1 : Matrix (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) _ K) (Sum.inl a) (Sum.inl b) :=
    fun a b => hq _ _ le_rfl
  have eε1 : ∀ i : Fin κ, (ε (Sum.inl i)).val = i.val := fun i => rfl
  have eε2 : ∀ i : Fin (s + 1), (ε (Sum.inr i)).val = κ + i.val := fun i => rfl
  simp only [Fintype.sum_sum_type, h1, h2, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, GlobalTheory.chainEdge, eε1, eε2]
  have A : ∀ x : Fin κ, ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = 0 := by
    intro x
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro x_1 _
      rw [if_neg]
      omega
    · intro x_1 _
      split_ifs with h
      · rw [hX, Matrix.one_apply_ne]
        intro e
        have : x = x_1 := by simpa using e
        subst this
        omega
      · rfl
  have B : ∀ x : Fin (s + 1), ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = (ϖ : K) * ∑ x_1 : Fin (s + 1), if (x_1 : ℕ) = x + 1 then q.val (Sum.inr x) (Sum.inr x_1) else 0 := by
    intro x
    rw [Finset.sum_eq_zero, zero_add, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x_1 _ => ?_
      by_cases h : (x_1 : ℕ) = x + 1
      · rw [if_pos ⟨by omega, by omega⟩, if_pos h, h]
        have hϖ : (ϖ : K) ≠ 0 := ϖ.ne_zero
        field_simp
        ring
      · rw [if_neg (by omega), if_neg h, mul_zero]
    · intro x_1 _
      rw [if_neg]
      have := x_1.2
      omega
  simp only [A, B, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
  rfl


theorem redFn_conj_eq_one {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {a e : AE D} {P : Finset (Pl D.host.E)}
    {PP Q : Pl D.host.E} (ha : IsIdemSum a P) (hPP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP) {n : GA D V}
    (hn : SuppAt e V n) (t : GA D V) (hS : finE V (t⁻¹ * n * t) ∈ St β) (hQ : Q ∈ P) (hne : PP ≠ Q) :
    redFn β Q (finE V (t⁻¹ * n * t)) = 1 := by
  refine GlobalTheory.DiagLiftFix.redFn_eq_one_of_ne ha hPP he ?_ hS hQ hne
  intro i j
  have h2 : mt V t⁻¹ * mt V t = 1 := by
    show mt V (t⁻¹ * t) = 1
    rw [inv_mul_cancel]; rfl
  have e1 : mt V (t⁻¹ * n * t) - 1 = mt V t⁻¹ * (mt V n - 1) * mt V t := by
    show mt V t⁻¹ * mt V n * mt V t - 1 = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
  rw [e1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  have := hn m l
  linear_combination (mt V t⁻¹ i m * mt V t l j) * this

end GlobalTheory.NChainChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapPreimageIntegralGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

namespace GlobalTheory.HaarR

theorem rootExchangeEmbedGL_mem_integralGL {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (c : ℕ) {g : GL n k} (hg : g ∈ KO k n) :
    embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have key : ∀ x : GL n k, (∀ i j, x.val i j ∈ 𝒪[k]) → ∀ i j, (embX c x).val i j ∈ 𝒪[k] := by
    intro x hx i j
    rw [GlobalTheory.RootEx.Radical.embX_val]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hx i j
    · simp
    · simp
    · simp only [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨key g h1, ?_⟩
  rw [← map_inv]
  exact key _ h2

theorem prodR_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), prodR (k := k) (n := n) (c := c) p ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = (KO k n : Set (GL n k)) ×ˢ {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
  intro k _ _ _ _ n _ _ c p
  ext ⟨g, u⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodR_coe, Set.mem_prod, SetLike.mem_coe]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 h
    have hg : g ∈ KO k n := by
      refine (GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g u.2
        have := h1 (Sum.inl i) (Sum.inl j)
        rw [← e]; exact this
      · have hu' : embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹ ∈ N k n c p :=
          GlobalTheory.RootEx.Radical.conj_mem g (inv_mem u.2)
        have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g⁻¹ hu'
        have hinv : (embX c g * (u : GL (n ⊕ Fin c) k))⁻¹
            = embX c g⁻¹ * (embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹) := by
          rw [map_inv]; group
        have := h2 (Sum.inl i) (Sum.inl j)
        rw [hinv] at this
        rw [← e]
        exact this
    refine ⟨hg, ?_⟩
    have := mul_mem (inv_mem (rootExchangeEmbedGL_mem_integralGL c hg)) h
    rwa [inv_mul_cancel_left] at this
  · rintro ⟨hg, hu⟩
    exact mul_mem (rootExchangeEmbedGL_mem_integralGL c hg) hu

end GlobalTheory.HaarR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevelStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_rational_coset_sameOrbit_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  first | exact @GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | exact GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | (intros; apply GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level <;> assumption)
end

