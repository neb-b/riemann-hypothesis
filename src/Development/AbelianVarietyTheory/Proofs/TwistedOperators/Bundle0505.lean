module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

section SlopeTestRemainingChoices

open GlobalTheory.LatVac GlobalTheory.SplitScalar

def stO (x : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨star (x : D.host.E), (show IsIntegral ℤ (x : D.host.E) from x.2).map (starRingEnd D.host.E).toIntAlgHom⟩

theorem coe_stO (x : 𝓞 D.host.E) : ((stO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem mem_of_mem_conjI {P : Ideal (𝓞 D.host.E)} {x : 𝓞 D.host.E} (hx : x ∈ conjI P) : stO x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, hab⟩ := ha
    have : stO a = b := by
      apply RingOfIntegers.ext
      rw [coe_stO, show (a : D.host.E) = star (b : D.host.E) from hab, star_star]
    rw [this]; exact hb
  | zero =>
    have : stO (0 : 𝓞 D.host.E) = 0 := RingOfIntegers.ext (by rw [coe_stO]; simp)
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : stO (a + b) = stO a + stO b := RingOfIntegers.ext (by
      show star ((a : D.host.E) + b) = star (a : D.host.E) + star (b : D.host.E)
      exact star_add _ _)
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : stO (r • a) = stO r * stO a := RingOfIntegers.ext (by
      show star ((r : D.host.E) * a) = star (r : D.host.E) * star (a : D.host.E)
      exact star_mul' _ _)
    rw [this]; exact Ideal.mul_mem_left _ _ ha

theorem smul_mem_tens {n r : ℕ} {Λ : Lt D.host.E n} {L L' : Lt D.host.E r} (c : 𝓞 D.host.E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) D.host.E} (hy : y ∈ tens Λ L) :
    (c : D.host.E) • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_hatA_of_int {S T : HSp D} {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    (hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ A, (o : D.host.E) • y ∈ A) {z : AE D} (hz : finPart D z ∈ intAE D)
    {u : WO S T} (hu : u ∈ hatA S T A) : z • u ∈ hatA S T A := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => z • u ∈ hatA S T A) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    have key : ∀ x ∈ intAE D,
        (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D (x * (α ⊗ₜ[D.host.F] (yᵀ i j)))) ∈ hatA S T A := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, o, rfl⟩ := hx
        have e1 : (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D
            ((a ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] (yᵀ i j)))) =
            GlobalTheory.LatVac.finTens (a * α) (((o : D.host.E) • y)ᵀ) := by
          ext i j
          rw [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.TensLatMove.emb_tmul]
          rfl
        rw [e1]
        exact GlobalTheory.Ker.SignVac.finTens_mem (mul_mem_intAf ha hα) (hA o y hy)
      | zero =>
        convert zero_mem (hatA S T A) using 1
        ext i j
        rw [Matrix.of_apply, zero_mul, LinearMap.map_zero, Matrix.zero_apply]
      | add x x' _ _ hx hx' =>
        convert add_mem hx hx' using 1
        ext i j
        rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, add_mul, LinearMap.map_add (f := _)]
      | neg x _ hx =>
        convert neg_mem hx using 1
        ext i j
        rw [Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, neg_mul, LinearMap.map_neg]
    convert key _ hz using 1
    ext i j
    rw [Matrix.of_apply, GlobalTheory.TensLatMove.emb_mul, GlobalTheory.TensLatMove.emb_tmul]
    rfl
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

end SlopeTestRemainingChoices

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (x : WO S T) : partAt c x = c • x := by
  ext i j; rfl

theorem partAt_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ hPg _ e he a k₀ Λ' _ hMv hGen hMov Lv hLv u hu

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hMov
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩
  have hu' : actO S T k₀ 1 (actO S T k₀⁻¹ 1 u) = u := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k₀ 1 u
    rwa [inv_one] at this
  generalize actO S T k₀⁻¹ 1 u = w at hw hu'

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hs : stO t ∈ conjI Lv.𝔪 := Ideal.subset_span ⟨t, ht, rfl⟩
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPg
    intro h
    apply htP PP (Finset.mem_union_left _ hPP)
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _
  have hs0 : ((stO t : 𝓞 D.host.E) : D.host.E) ≠ 0 := by rw [coe_stO]; exact star_ne_zero.2 ht0

  have hsL : ∀ v ∈ Lv.sh C.X.Λ, stO t • v ∈ Lv.𝔪 • C.X.Λ := fun v hv => hv _ hs
  have h0 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w ∈
      hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)) := by
    refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)))
      ?_ ?_ ?_ ?_ hw
    · intro α hα y hy
      rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
      exact GlobalTheory.Ker.SignVac.finTens_mem hα (smul_mem_tens _ hsL hy)
    · rw [smul_zero]; exact zero_mem _
    · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
    · intro x hx; rw [smul_neg]; exact neg_mem hx

  have hz1 : finPart D (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    have h7 := (GlobalTheory.FinPl.FrameLat.cA_int_iff (e * incA D ((t : D.host.E))⁻¹)).2
      (GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP)
    rwa [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, star_inv₀] at h7
  have hA' : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ),
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ) :=
    fun o y hy => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hy
  have hx0 : partAt (cA D e) w ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
    have e1 : partAt (cA D e) w = (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) •
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w := by
      rw [smul_smul, mul_assoc]
      have e2 : incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) *
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hs0]
      rw [e2, mul_smul, GlobalTheory.Ker.SignVac.one_smul_hatA hw, partAt_eq_smul]
    rw [e1, ← hLv]
    exact smul_mem_hatA_of_int hA' hz1 h0

  have hidem : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : IsHalf (cA D e) (partAt (cA D e) w) := fun i j => by
    change cA D e * (cA D e * w i j) = cA D e * w i j
    rw [← mul_assoc, hidem]
  obtain ⟨hI, hR⟩ := ((hGen _ hhalf).2).2 hx0
  have hmv := hMv.2.2 _ hhalf
  have hcomm : partAt (cA D e) u = actO S T k₀ 1 (partAt (cA D e) w) := by
    rw [partAt_eq_smul, partAt_eq_smul, ← hu']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  rw [hcomm]
  refine ⟨GlobalTheory.WeilVacMove.isHalf_actO _ _ _ hhalf, ?_, fun PP hPP => ?_⟩
  · rw [hmv]; exact hI
  · rw [hmv]; exact hR PP hPP

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}


open Classical in
def cutPart (a : AE D) (V : HSp D) (g : GA D V) : GA D V :=
  if h : a * a = a ∧ cA D a = a then ⟨piece h.1 g.1, piece_mem _ _ h.1 h.2 g.2⟩ else g

theorem mt_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutPart a V g) = a • Formalism.L2.Theta.mt V g + (1 - a) • (1 : Matrix _ _ (AE D)) := by
  have e : cutPart a V g = ⟨piece h g.1, piece_mem _ _ h hc g.2⟩ := dif_pos ⟨h, hc⟩
  rw [e]
  rfl

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

theorem idem_conj_sum {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  have h1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  refine ⟨by linear_combination he + h1 + 2 * hc, ?_⟩
  rw [RingHom.map_add (f := _), GlobalTheory.SplitOnto.cA_cA, add_comm]

theorem idem_compl {f : AE D} (hf : f * f = f ∧ cA D f = f) : (1 - f) * (1 - f) = 1 - f ∧ cA D (1 - f) = 1 - f := by
  refine ⟨by linear_combination hf.1, ?_⟩
  rw [RingHom.map_sub, RingHom.map_one, hf.2]

theorem cutPart_mul {f : AE D} (hf : f * f = f ∧ cA D f = f) (V : HSp D) (g : GA D V) :
    g = cutPart f V g * cutPart (1 - f) V g := by
  have h2 := idem_compl hf
  refine GlobalTheory.IdemSupport.mt_inj V ?_
  rw [GlobalTheory.IdemSupport.mt_mul, mt_cutPart hf.1 hf.2, mt_cutPart h2.1 h2.2, sub_sub_cancel]
  exact (mix_split hf.1 rfl rfl).symm

theorem suppAt_cutPart {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    SuppAt e V (cutPart (e + cA D e) V g) := by
  have hf := idem_conj_sum he hc
  exact (supp_iff _ _).2 (smul_mix hf.1 (mt_cutPart hf.1 hf.2 V g))

theorem smul_mt_cutPart_compl {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    e • Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hf := idem_conj_sum he hc
  have h2 := idem_compl hf
  rw [mt_cutPart h2.1 h2.2, sub_sub_cancel, smul_add, smul_smul, smul_smul]
  have k1 : e * (1 - (e + cA D e)) = 0 := by linear_combination -he - hc
  have k2 : e * (e + cA D e) = e := by linear_combination he + hc
  rw [k1, k2, zero_smul, zero_add]

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem actO_cutPart_compl {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (g : GA D S) {z : WO S T}
    (hz : IsHalf e z) : actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹ z = z := by
  have hz' : e • z = z := Matrix.ext fun i j => hz i j
  unfold actO
  rw [inv_inv, inv_one, GlobalTheory.IdemSupport.mt_one, Matrix.one_mul]
  conv_lhs => rw [← hz']
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_mt_cutPart_compl he hc, Matrix.mul_smul, Matrix.mul_one, hz']

theorem halfInd_cutPart {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (g : GA D S) (x : WO S T) :
    halfInd e Λ (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) = halfInd e Λ (actO S T g⁻¹ 1⁻¹ x) := by
  have hf := idem_conj_sum he hc
  have hg : g = cutPart (e + cA D e) S g * cutPart (1 - (e + cA D e)) S g := cutPart_mul hf S g
  have key : actO S T g⁻¹ 1⁻¹ x = actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹
      (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, ← mul_inv_rev, ← hg, inv_one, mul_one]
  rw [key]
  by_cases hy : IsHalf e (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x)
  · rw [actO_cutPart_compl he hc g hy]
  · unfold halfInd
    rw [if_neg fun h => hy h.2, if_neg fun h => hy (GlobalTheory.ThetaMove.isHalf_of_act _ _ h.2)]

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulAddSmulAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinDecomp

theorem mem_of_compl_smul {D : D7} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : y ∈ Λ) :
    (1 - e - cA D e) • y ∈ Λ := by
  rw [sub_smul, sub_smul, one_smul]
  exact Λ.sub_mem (Λ.sub_mem hy (he y hy)) (hc y hy)

theorem half_mul_two (D : D7) : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem symplO_split_two {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplO S T x y = symplO S T (e • x) (cA D e • y) + symplO S T (cA D e • x) (e • y) +
      (symplO S T z ((1 - e - cA D e) • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  have hsplit := GlobalTheory.AdForm.HalfASign.symplO_split (S := S) (T := T) h1 h2 x y
  rw [hzx, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left S T] at hsplit
  exact hsplit

theorem symplO_smul_add_smul_add {D : D7} (S T : HSp D) (e : AE D) (x y : WO S T) :
    symplO S T (e • (x + y)) (cA D e • (x + y)) = symplO S T (e • x) (cA D e • x) + symplO S T (e • x) (cA D e • y) +
      (symplO S T (e • y) (cA D e • x) + symplO S T (e • y) (cA D e • y)) := by
  rw [smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left S T, GlobalTheory.PlaceModel.symplO_add_right S T,
    GlobalTheory.PlaceModel.symplO_add_right S T]

theorem symplOH_lamE_arg {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplOH S T (e • x) (cA D e • x) + symplOH S T (e • y) (cA D e • y) + symplOH S T x y =
      symplOH S T (e • (x + y)) (cA D e • (x + y)) +
        (symplO S T (cA D e • x) (e • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  unfold symplOH
  rw [symplO_split_two h1 h2 hzx, symplO_smul_add_smul_add S T e x y,
    GlobalTheory.PlaceModel.symplO_skew S T (cA D e • x) (e • y)]
  have hh := half_mul_two D
  generalize algebraMap D.host.F (AF D.host.F) (1 / 2) = h at hh ⊢
  generalize symplO S T (e • x) (cA D e • x) = a1
  generalize symplO S T (e • y) (cA D e • y) = a2
  generalize symplO S T (e • x) (cA D e • y) = a3
  generalize symplO S T (cA D e • x) (e • y) = a4
  generalize symplO S T z ((1 - e - cA D e) • y) = a5
  linear_combination (a4 + a5) * hh

theorem lamE_add_of_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D), e * e = e → e * cA D e = 0 → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) → (∀ u ∈ Λ, e • u ∈ Λ) → (∀ u ∈ Λ, cA D e • u ∈ Λ) → (∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z) → ∀ x ∈ Λ, ∀ y ∈ Λ, lamE ψ S T e (x + y) = lamE ψ S T e x * lamE ψ S T e y * ψ (symplOH S T x y) := by
  intro D ψ S T Λ e h1 h2 hψ he hc hr x hx y hy
  obtain ⟨z, hz, hzx⟩ := hr x hx
  have key := symplOH_lamE_arg (y := y) h1 h2 hzx
  have k1 : ψ (symplO S T (cA D e • x) (e • y)) = 1 := hψ _ (hc x hx) _ (he y hy)
  have k2 : ψ (symplO S T z ((1 - e - cA D e) • y)) = 1 := hψ _ hz _ (mem_of_compl_smul he hc hy)
  have := congrArg ψ key
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, k1, k2,
    mul_one, mul_one] at this
  unfold lamE
  exact this.symm

end GlobalTheory.FinDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto.UpLift

variable {D : D7}

theorem multT_le_noLevel' {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

theorem upSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' p hp u φ v _hv
  obtain ⟨T, hTK, hKT, hL⟩ := _root_.GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span h1 h2 h3 h4 D c k s s' p.ω p.f hc hk hs hs' hp.pre
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel' c.θ s.M _ _ u.2)
  have hlaw : ∀ P v', ∀ κ ∈ s'.J, ∀ g, F' (T P v') (g * κ) = F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M p.f P) =
        thetaKO p.ω g' g (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := hp.pre.law P 1 (one_mem _) κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, h2]
    simp only [hω]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact hs'.fin hκ
    · intro w hw κ hκ g
      have hx := hKT hw
      clear hw
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', rfl⟩ := hx
        simpa using hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

theorem upAdj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  intro hP D c hc k hk s s' hs hs' p hp u y φ v _ w _
  have hru : GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v) :=
    ((_root_.GlobalTheory.EvenOnto.ConjVal.values_conj_hecke hP D c hc k hk.le s hs).1 u v).2.2.2.2
  have hry : GlobalTheory.Grow.RapidDec s'.V (PiLocalization₂.val y w) :=
    ((_root_.GlobalTheory.EvenOnto.ConjVal.values_conj_hecke hP D c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs').1 y w).2.2.2.2
  have hF := _root_.GlobalTheory.ChainOnto.ThetaSwap.integral_swap D c.ψ c.θ s.V s'.V (c.χ k) (c.χ k) p.ω hc.inf hp.pre.weil (p.pt φ)
    (_root_.GlobalTheory.EvenOnto.fock_sph_vac D c hc k hk s s' hs hs' p hp φ).1
    s.ν s.fd s'.ν s'.fd hs.haar hs.fund hs'.haar hs'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w) hru hry
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w) g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w g

theorem upSpan_upAdj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D ∧ UpAdj D :=
  fun h1 h2 h3 h4 D => ⟨upSpan h1 h2 h3 h4 D, upAdj h3 D⟩

end GlobalTheory.EvenOnto.UpLift

end
end

