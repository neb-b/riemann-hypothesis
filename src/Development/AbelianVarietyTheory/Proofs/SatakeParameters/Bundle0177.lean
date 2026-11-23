module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  first | exact @GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly | exact GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly | (intros; apply GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationNatCastLtOneOfInduces
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}


omit [IsAlgClosure E Ω] [IsCMField E] in
theorem norm_natCast_om_lt_one : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one


omit [NumberField E] [IsAlgClosure E Ω] [IsCMField E] in
theorem valuation_natCast_lt_one_of_induces {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    A.valuation ((l : ℕ) : Ω) < 1 := by
  have hn : ‖Bw.j ((l : ℕ) : Ω)‖ < 1 := by rw [map_natCast]; exact norm_natCast_om_lt_one
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    have h1 := congrArg Bw.j h0
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hmem : ((l : ℕ) : Ω) ∈ A := (hj _).2 hn.le
  have hinv : ((l : ℕ) : Ω)⁻¹ ∉ A := by
    intro hm
    have h1 := (hj _).1 hm
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖Bw.j ((l : ℕ) : Ω)‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hl0)
    have := (one_lt_inv₀ hpos).2 hn
    linarith
  refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 hmem) fun h1 => hinv ?_
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]


omit [IsAlgClosure E Ω] [IsCMField E] in
theorem mem_of_induces {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  refine (hA _).1 ?_
  have h := valuation_natCast_lt_one_of_induces Bw hj
  simpa [map_natCast] using h

end GlobalTheory.GalCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbit
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem reads_orbit_invFrob : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  intro D l _ P K LL W c κ h2 hq hd hcl hK
  set φ := DV.frobG D l with hφ
  set n := Module.finrank ℚ_[l] ↥(K0 K) with hn
  have hτ := fun a => _root_.GlobalTheory.HTW.Rec.existsUnique_over P K LL W hK a
  have hg := fun τ => _root_.GlobalTheory.HTW.Rec.existsUnique_reads D.host K LL c κ τ
  let τa : ZMod n → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := fun a => (hτ a).exists.choose
  have hover : ∀ a, Over W (τa a) a := fun a => (hτ a).exists.choose_spec
  let g : ZMod n → D.R.GG := fun a => (hg (τa a)).exists.choose
  have hread : ∀ a, Reads D.host c κ (τa a) (g a) := fun a => (hg (τa a)).exists.choose_spec
  have smul : ∀ u v : D.R.GG, D.host.sigmaOf (u * v) = D.host.sigmaOf u * D.host.sigmaOf v :=
    fun u v => map_mul (D.host.gal).symm u v
  have hK0 : K0 K = K.1 := inf_eq_left.mpr hK

  have step : ∀ a, g (a + 1) = g a * φ⁻¹ := by
    intro a
    refine (hg (τa (a + 1))).unique (hread (a + 1)) ?_
    intro z
    set x := D.host.sigmaOf φ⁻¹ z with hx
    have hz : D.host.sigmaOf φ x = z := by
      rw [hx, ← AlgEquiv.mul_apply, ← smul, mul_inv_cancel]
      show (D.host.gal).symm 1 z = z
      rw [map_one]; rfl
    let y : ↥(K0 K) := ⟨((c x : ↥K.1) : Om l), ⟨(c x).2, hK (c x).2⟩⟩
    have hy : algebraMap ↥(K0 K) ↥K.1 y = c x := Subtype.ext rfl
    have hσ := _root_.GlobalTheory.FrobPeriod.periodFrob_restrict D P K c h2 hq hd x y hy
    have ov : ∀ b (t : ↥(K0 K)), τa b (algebraMap ↥(K0 K) ↥K.1 t) = W.emb b t := by
      intro b t
      have := congrArg (fun f => f t) (hover b)
      simpa using this
    have hemb : W.emb (a + 1) ((P.PD K).σ y) = W.emb a y := by
      have := congrArg (fun f => f y) (W.emb_σ a)
      simpa using this
    calc τa (a + 1) (c z) = τa (a + 1) (c (D.host.sigmaOf φ x)) := by rw [hz]
      _ = τa (a + 1) (algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y)) := by rw [hσ]
      _ = W.emb (a + 1) ((P.PD K).σ y) := ov _ _
      _ = W.emb a y := hemb
      _ = τa a (algebraMap ↥(K0 K) ↥K.1 y) := (ov _ _).symm
      _ = τa a (c x) := by rw [hy]
      _ = κ (D.host.sigmaOf (g a) x) := hread a x
      _ = κ (D.host.sigmaOf (g a * φ⁻¹) z) := by rw [smul, AlgEquiv.mul_apply]

  have hfr : n = Module.finrank ℚ_[l] ↥K.1 := by
    rw [hn]; exact (IntermediateField.equivOfEq hK0).toLinearEquiv.finrank_eq
  have hlen : n = orderOf φ⁻¹ := by
    rw [orderOf_inv]
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (Ideal.span {(l : ℤ)}) (⊥ : Ideal (𝓞 D.host.E)) (by
        intro x hx
        simp only [Ideal.mem_comap, Ideal.mem_bot] at hx
        have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by simpa using hx)
        rw [this]; exact Ideal.zero_mem _)
    have := hQ
    have : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQc.symm⟩
    have hfrob := (_root_.GlobalTheory.FrobSign.frobG_isArithFrob_and_sign D l h2 hq hd).1 Q
    let c' : D.host.E →+* PadicAlgCl l := (K.1.val : ↥K.1 →ₐ[ℚ_[l]] Om l).toRingHom.comp c
    have hc' : ∀ x, c' x ∈ K.1 := fun x => (c x).2
    have hcl' : (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c') := hcl
    have := (_root_.GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit D.host l h2 hq hd c' K hc' hcl' Q (D.host.sigmaOf φ) hfrob).1
    have hφg : D.host.galE (D.host.sigmaOf φ) = φ :=
      (D.host.gal).apply_symm_apply φ
    rw [hfr, this, hφg]
  have hpos : 0 < n := by
    rw [hfr]
    have := K.2
    exact Module.finrank_pos
  have : NeZero n := ⟨hpos.ne'⟩
  refine ⟨g, ⟨hlen, ?_⟩, ?_⟩
  · have hk : ∀ k : ℕ, g (k : ZMod n) = g 0 * φ⁻¹ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, step, ih]
        exact (mul_assoc _ _ _).trans (congrArg _ (pow_succ φ⁻¹ k).symm)
    intro a
    have := hk a.val
    rwa [ZMod.natCast_zmod_val] at this
  · intro τ a h
    have : τ = τa a := (hτ a).unique h (hover a)
    subst this
    exact hread a

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopXiInv

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc

theorem xiTop_invariant : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word), Pr.Ok → R.m = m2 + 2 → cst.Ok → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u), Y ∈ ybSet sel mu cst p.deco.1.N → ∀ x z, z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst m2 p Y p' (x + z) = XiTop Ch sel mu cst m2 p Y p' x := by
  classical
  intro X Pr R Ch sel S mu cst m2 u hPr hm hc hD p Y p' hY x y hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiTop Ch sel mu cst m2 p Y p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold XiTop
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) x = x'
    have hz : ∀ v : Sp X.E (R.N (m2 + 1)), (∀ l, IntAt P.1 (v l)) → ∀ l,
        IntAt P.1 (inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l / (qOf P.1 : X.E) ^ cst.B) := by
      intro v hv l
      have h1 : frsF sel mu p P v ∈ p.deco.1.at P.1 := (frsF_mem p P v).2 ((mem_localization_standardLattice _ _).2 hv)
      have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
      have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) ∈ stdAt X.E _ P.1 := by
        refine (frsF_mem p' P _).1 ?_
        rw [LinearEquiv.apply_symm_apply]
        exact h2
      have h4 := (mem_localization_standardLattice _ _).1 h3 l
      obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
      have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l =
          (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) l := by
        change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P v)) l = _
        rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
      rw [h5, hc']
      convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
      push_cast
      field_simp
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) = z at hz ⊢
    unfold locTop
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.PhiTop_add mu Ch _ _ hm P.1 _ _ fun s l => ?_
      have h1 := hz (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1)) fun l' =>
        GlobalTheory.TopInv.single_int s _
      have h2 := GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos (h1 (Br.iC (N_m_succ R) l))
      rw [pow_one] at h2
      exact h2
    · refine GlobalTheory.TopInv.ftY_add sel mu cst hc P (hD P) _ _ _ (fun s => ?_) ?_
      · exact GlobalTheory.TopInv.atNL_int (R.N R.m - 1) _ _ (hz (Pi.single s 1) (GlobalTheory.TopInv.single_int s))
      · have h1 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
        have h2 := (frsF_mem p P ((frsF sel mu p P).symm
          (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Y))).1 (by
            rw [LinearEquiv.apply_symm_apply]
            exact h1)
        intro l
        have h3 := (mem_localization_standardLattice _ _).1 h2 l
        rw [map_smul] at h3
        exact h3

end GlobalTheory.TopXiInv
end
end

