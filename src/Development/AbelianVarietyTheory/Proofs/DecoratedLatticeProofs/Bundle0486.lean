module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem PiLocalization₂.val_autCusp {D : D7} (c : Com D) (s : PiLocalization₂ D) (u : s.CC c) (x : SmT s.M) :
    IsAutFunSm c.θ s.V (PiLocalization₂.val u x) ∧ IsCuspFun s.V (PiLocalization₂.val u x) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D c.θ s.V _ s.M _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  have key : ∀ y : SmT s.M, PiLocalization₂.val u y =
      (PiTensorProduct.lift (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) y := by
    intro y; rw [LinearEquiv.apply_symm_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [key, map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    have e : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := map_add _ _ _
    rw [e]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem rankY_succ {D : D7} (k : ℕ) : D.R.rankY (k + 1) = D.R.rankY k + D.R.t := by
  show D.R.r + (k + 1) * D.R.t = D.R.r + k * D.R.t + D.R.t
  ring

theorem upPar_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, LevFacts D → UpPar D := by
  intro hRD hHowe D _ hND c hc k hk s s' hs hs' p hp u B φ hu v _ hne
  have hlat' := (_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc (k + 1) hk s' hs').2
  have hlat := (_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc k hk.le s hs).2
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : IsParamFunV s.V c.S (fun g => conj (y g)) B := (hlat _ B).1 (hu.2 v hy0)
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank, rankY_succ]
  have hYA := PiLocalization₂.val_autCusp c s u v
  unfold ParFun
  rw [hlat', hconj]
  intro w0 hw0 w h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact _root_.GlobalTheory.ChainOnto.thetaIntegral_param hRD D (_root_.GlobalTheory.ChainOnto.transferOn_all hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil D.R.t hrank s.ν s.fd
    hs.haar hs.fund w0 (fun w' hw' => _root_.GlobalTheory.ChainOnto.step_chars_unrAt D c hc k hk w0 hw0' w' hw') w h (p.pt φ)
    (_root_.GlobalTheory.ChainOnto.fock_vacFin_off D hND c hc k hk s s' hs hs' p hp φ w0 hw0') y (B w) hYA.1 hYA.2 (hyB w0 hw0 w h) hne'

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)

section Elem

variable {κ : Type} [CommRing κ] {r : ℕ}

def elem {i j : Fin r} (h : i ≠ j) (u : κ) : GL (Fin r) κ :=
  ⟨transvection i j u, transvection i j (-u), by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem elem_apply {i j : Fin r} (h : i ≠ j) (u : κ) (a b : Fin r) :
    (elem h u).val a b = (1 : Matrix (Fin r) (Fin r) κ) a b + if i = a ∧ j = b then u else 0 := rfl

theorem edgeSum_one (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) :
    edgeSum Ed (1 : GL (Fin r) κ) = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · exact one_apply_ne fun e => hE a (by rwa [← e] at h)
  · rfl

theorem edgeSum_elem (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) {i j : Fin r} (h : i ≠ j) (hij : Ed i j)
    (u : κ) : edgeSum Ed (elem h u) = u := by
  have h1 : ∀ a b, (if Ed a b then (elem h u).val a b else 0) = if i = a then (if j = b then u else 0) else 0 := fun a b => by
    rw [elem_apply]
    by_cases h2 : Ed a b
    · rw [if_pos h2, one_apply_ne fun e => hE a (by rwa [← e] at h2), zero_add, ite_and]
    · rw [if_neg h2, ← ite_and, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h2 hij
  unfold edgeSum
  simp only [h1]
  simp

theorem elem_mem_unipCol {i j : Fin r} (h : i ≠ j) (hij : i.val < j.val) (u : κ) (a c : ℕ) (hc : j.val ≠ c) :
    elem h u ∈ unipCol κ r a c := by
  refine ⟨⟨fun x y hxy => ?_, fun x => ?_⟩, fun x y h1 h2 h3 => ?_⟩
  · have hxy' : y.val < x.val := hxy
    rw [elem_apply, one_apply_ne (fun e => by rw [e] at hxy'; omega), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    omega
  · rw [elem_apply, one_apply_eq, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h rfl
  · rw [elem_apply, one_apply_ne (fun e => by rw [e] at h2; omega), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    omega

end Elem

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
include hψ in
theorem chr_near {t : kˣ} (ht : IsUnif t) {y y' : k} (hy : valuation k (y - y') < 1) :
    ψ (((t⁻¹ : kˣ) : k) * y) = ψ (((t⁻¹ : kˣ) : k) * y') := by
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  have triv : ψ (((t⁻¹ : kˣ) : k) * (y - y')) = 1 := (hψ 1).2 (by simp) _ (by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, map_one, inv_mul_le_one₀ tp]
    exact (ht _).1 hy)
  rw [show ((t⁻¹ : kˣ) : k) * y = ((t⁻¹ : kˣ) : k) * (y - y') + ((t⁻¹ : kˣ) : k) * y' by ring, AddChar.map_add_eq_mul, triv, one_mul]


include h hψ in
theorem exists_res {t : kˣ} (ht : IsUnif t) : ∃ α : AddChar (kP PP) ℂ,
    ∀ z, (ψ (((t⁻¹ : kˣ) : k) * prO q z) : ℂ) = α (Ideal.Quotient.mk _ z) := by
  have wd : ∀ z z' : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = Ideal.Quotient.mk PP.asIdeal z' →
      ψ (((t⁻¹ : kˣ) : k) * prO q z) = ψ (((t⁻¹ : kˣ) : k) * prO q z') := fun z z' e =>
    chr_near hψ ht (by rw [← map_sub, ← prO_lt q h]; exact Ideal.Quotient.eq.1 e)
  choose l hl using Ideal.Quotient.mk_surjective (I := PP.asIdeal)
  refine ⟨{ toFun := fun u => ψ (((t⁻¹ : kˣ) : k) * prO q (l u))
            map_zero_eq_one' := by rw [wd _ 0 (by rw [hl, map_zero])]; simp
            map_add_eq_mul' := fun a b => by
              rw [wd _ (l a + l b) (by rw [map_add (f := _), hl, hl, hl]), map_add (f := _), mul_add, AddChar.map_add_eq_mul, Circle.coe_mul] },
    fun z => congrArg (fun c : Circle => (c : ℂ)) (wd _ z (hl _)).symm⟩


include h in
theorem exists_near {y : k} (hy : valuation k y ≤ 1) : ∃ z, valuation k (y - prO q z) < 1 := by
  obtain ⟨-, hi, hd⟩ := place_facts q h
  have h2 : {x : k | valuation k (x - y) < 1} ∈ nhds y := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have ha' : valuation k ((ofSplit q).pr a - y) < 1 := ha
  have ha1 : valuation k ((ofSplit q).pr a) ≤ 1 := by
    simpa using Valuation.map_add_le (valuation k) ha'.le hy
  obtain ⟨r, s, hs, e⟩ := (hi a).1 ((Valuation.mem_integer_iff _ _).2 ha1)
  have e' : prO q s * (ofSplit q).pr a = prO q r :=
    ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
  obtain ⟨t, p, hp, htp⟩ := PP.isMaximal.exists_inv hs
  refine ⟨t * r, ?_⟩
  have e2 : prO q t * prO q s + prO q p = 1 := by rw [← map_mul, ← map_add (f := _), htp, map_one]
  have e3 : y - prO q (t * r) = (ofSplit q).pr a * prO q p - ((ofSplit q).pr a - y) := by
    rw [map_mul, ← e']
    linear_combination (-(ofSplit q).pr a) * e2
  rw [e3]
  refine Valuation.map_sub_lt _ ?_ ha'
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ha1) ((prO_lt q h p).1 hp)


include h hψ in
theorem near_of_res {t t' : kˣ} (ht : IsUnif t) (ht' : IsUnif t')
    (he : ∀ z, ψ (((t⁻¹ : kˣ) : k) * prO q z) = ψ (((t'⁻¹ : kˣ) : k) * prO q z)) :
    valuation k ((t : k) - t') < valuation k (t : k) := by
  have h1 : ∀ y, valuation k y ≤ 1 → ψ (((t⁻¹ : kˣ) : k) * y) = ψ (((t'⁻¹ : kˣ) : k) * y) := fun y hy => by
    obtain ⟨z, hz⟩ := exists_near q h hy
    rw [chr_near hψ ht hz, chr_near hψ ht' hz, he]
  set c : k := ((t⁻¹ : kˣ) : k) - ((t'⁻¹ : kˣ) : k) with hc
  have h2 : valuation k c ≤ 1 := by
    by_cases c0 : c = 0
    · rw [c0, map_zero]; exact zero_le
    have cp : 0 < valuation k c := zero_lt_iff.2 ((map_ne_zero _).2 c0)
    have := (hψ c).1 fun y hy => by
      have h3 := h1 (c⁻¹ * y) (by rw [map_mul, map_inv₀, inv_mul_le_one₀ cp]; exact hy)
      rw [← mul_inv_eq_one, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, ← hc,
        mul_inv_cancel_left₀ c0] at h3
      exact h3
    simpa using this
  have e : (t : k) - t' = (t : k) * (-c * t') := by
    rw [hc, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp
    ring
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  rw [e, map_mul]
  refine mul_lt_of_lt_one_right tp ?_
  rw [map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h2) ((ht' _).2 le_rfl)

theorem psiAt_eq {Ψ : AddChar (AF D.host.F) ℂ} (hc : (ofSplit q).IsChar Ψ ψ) (y : D.host.E) :
    Formalism.IndefR.Mi.psiAt Ψ q.e y = ψ ((ofSplit q).pr y) := by
  rw [hc]
  change _ = Ψ (Algebra.trace _ _ (incA D D.host.xi0 * q.sec (q.pr (incA D y))))
  rw [q.sec_pr, Formalism.IndefR.Mi.psiAt, map_mul (incA D), mul_left_comm]

end Local

theorem norm_notMem_sq {D : D7} {PP : Pl D.host.E} (h : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by
  have hspl : ∀ k, Formalism.MainNotions.S.SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := Formalism.MainNotions.BridgeLemma.span_isMaximal hp
    apply Formalism.MainNotions.S.splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (Formalism.MainNotions.BridgeLemma.span_ne_bot hp) (𝓞 D.host.E), ← Formalism.MainNotions.BridgeLemma.image_plOver _ hp,
      (Formalism.MainNotions.BridgeLemma.injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  rw [Nat.cast_mul] at h
  obtain ⟨k, hk⟩ : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal :=
    (PP.isPrime.mem_or_mem h).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
  obtain ⟨h1, h2⟩ := hspl k _ PP.isMaximal hk
  unfold Formalism.L2.Col.qOf
  rw [h1]
  exact h2

section Levels

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

theorem chi_of_eq {P P' : LevelP Pg r ℂ} (e : P = P') (x : G0 Pg r) (h : x ∈ P'.H) :
    ∃ h' : x ∈ P.H, P.chi ⟨x, h'⟩ = P'.chi ⟨x, h⟩ := by
  subst e
  exact ⟨h, rfl⟩

theorem prod_single {ι : Type} [Fintype ι] (pl : ι ≃ Pg) (α : ∀ i, AddChar (kP (pl i).1) ℂ) (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) {i j : Fin r} (h : i ≠ j) (hij : Ed i j) (n : ι) (u : kP (pl n).1) :
    ∏ m, α m (edgeSum Ed ((Pi.mulSingle (pl n) (elem h u) : G0 Pg r) (pl m))) = α n u := by
  rw [Finset.prod_eq_single n, Pi.mulSingle_eq_same, edgeSum_elem Ed hE h hij]
  · intro m _ hm
    rw [Pi.mulSingle_eq_of_ne (pl.injective.ne hm), edgeSum_one Ed hE, AddChar.map_zero_eq_one]
  · intro hn
    exact absurd (Finset.mem_univ n) hn

theorem single_mem (H : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (n : Pg) {x : GL (Fin r) (kP n.1)} (hx : x ∈ H n) :
    (Pi.mulSingle n x : G0 Pg r) ∈ Subgroup.pi Set.univ H := fun PP _ => by
  by_cases e : PP = n
  · subst e
    rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne e]
    exact (H PP).one_mem

end Levels

theorem edgeSum_eq_supSum {κ : Type} [CommRing κ] {r : ℕ} (g : GL (Fin r) κ) :
    edgeSum supEdge g = Formalism.IndefR.Mi.supSum (g : Matrix (Fin r) (Fin r) κ) := by
  unfold edgeSum Formalism.IndefR.Mi.supSum
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
    · exact if_pos (show supEdge i ⟨i.1 + 1, h⟩ from rfl)
    · intro j _ hj
      exact if_neg (fun hj' => hj (Fin.ext hj'))
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun j _ => ?_
    refine if_neg (fun hj => ?_)
    have := j.2
    unfold supEdge at hj
    omega

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end Gen

end GlobalTheory.LevelUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffTrace
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem supp_mulVec' {D : D7} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {I : Ideal (AE D)} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (X *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem colMul_zero' {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext r; simp [colMul]

theorem glued_stab_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (g : GL n k) :
    GlobalTheory.RootEx.embX 1 g • gluedS q 1 P.ker P.vec = gluedS q 1 P.ker P.vec ↔ g • P = P := by
  rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, Pair.smul_eq_iff P.hasVal_vec]
  constructor
  · intro h
    have h1 : g • P.ker = P.ker := by
      have := GlobalTheory.LevelUnfold.interX_gluedS (q := q) (le_refl 1) (g • P.ker) (g • P.vec)
      rw [h, GlobalTheory.LevelUnfold.interX_gluedS (le_refl 1)] at this
      exact this.symm
    refine ⟨h1, ?_⟩
    have h2 := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) (g • P.ker) (g • P.vec)
    rw [h] at h2
    exact (GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (le_refl 1)).1 h2
  · rintro ⟨h1, h2⟩
    rw [h1]
    exact GlobalTheory.LevelUnfold.gluedS_congr h2

theorem moves_emb_iff {D : D7} {S A B : HSp D} (o : OrthDec S A B) (M : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A)
    (LB : GlobalTheory.FinPl.Lat B) (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.OrthAt o M LA LB v) (κ : GA D A) :
    GlobalTheory.FinPl.Moves S (o.emb (κ, 1)) M M (· = v) ↔ GlobalTheory.FinPl.Moves A κ LA LA (· = v) := by
  have e1 : ∀ y, o.pA *ᵥ (Formalism.L2.Theta.mt S (o.emb (κ, 1)) *ᵥ y) = Formalism.L2.Theta.mt A κ *ᵥ (o.pA *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact o.pA_emb κ 1
  have e2 : ∀ y, o.pB *ᵥ (Formalism.L2.Theta.mt S (o.emb (κ, 1)) *ᵥ y) = o.pB *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, o.pB_emb]; simp [Formalism.L2.Theta.mt]
  constructor
  · intro hM yA hyA
    have hy : ∀ i, (o.jA *ᵥ yA) i ∈ idAt D (· = v) := supp_mulVec' _ hyA
    have hA1 : o.pA *ᵥ (o.jA *ᵥ yA) = yA := by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
    have hB1 : o.pB *ᵥ (o.jA *ᵥ yA) = 0 := by rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]
    have := hM _ hy
    rw [h, h, e1, e2, hA1, hB1] at this
    simpa only [zero_mem, and_true] using this
  · intro hA y hy
    rw [h, h, e1, e2, ← hA _ (supp_mulVec' _ hy)]

theorem carriesLattice_wittEmbedding_iff_core {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N : GlobalTheory.FinPl.Lat S) (M : GlobalTheory.FinPl.Lat S₀)
    (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.MonoAt d N M v) (g : GA D S₀) :
    GlobalTheory.FinPl.Moves S (d.emb0 g) N N (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g M M (· = v) := by
  have eX : ∀ y, d.pX *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have eY : ∀ y, d.pY *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have e0 : ∀ y, d.p0 *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = Formalism.L2.Theta.mt S₀ g *ᵥ (d.p0 *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact d.wittDecomp_projAnisotropic_anisotropicEmbedding g
  constructor
  · intro hM y₀ hy₀
    have hy : ∀ i, (d.j0 *ᵥ y₀) i ∈ idAt D (· = v) := supp_mulVec' _ hy₀
    have hX1 : d.pX *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
    have hY1 : d.pY *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
    have h01 : d.p0 *ᵥ (d.j0 *ᵥ y₀) = y₀ := by rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
    have := hM _ hy
    rw [h, h, eX, eY, e0, hX1, hY1, h01] at this
    simpa only [Pi.zero_apply, colMul_zero', zero_mem, true_and, implies_true] using this
  · intro hA y hy
    rw [h, h, eX, eY, e0, ← hA _ (supp_mulVec' _ hy)]

theorem exists_gl_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n)
    (κ : GA D S) : ∃ g : GL n k, (mt S κ).map p.pr = β.b * g.val * β.b' := by
  have e1 : mt S κ * mt S κ⁻¹ = 1 := by
    rw [show mt S κ * mt S κ⁻¹ = mt S (κ * κ⁻¹) from rfl, mul_inv_cancel]; rfl
  have e2 : mt S κ⁻¹ * mt S κ = 1 := by
    rw [show mt S κ⁻¹ * mt S κ = mt S (κ⁻¹ * κ) from rfl, inv_mul_cancel]; rfl
  have hM : (mt S κ).map p.pr * (mt S κ⁻¹).map p.pr = 1 := by
    rw [← Matrix.map_mul, e1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM' : (mt S κ⁻¹).map p.pr * (mt S κ).map p.pr = 1 := by
    rw [← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨β.b' * (mt S κ).map p.pr * β.b, β.b' * (mt S κ⁻¹).map p.pr * β.b, ?_, ?_⟩, ?_⟩
  · calc β.b' * (mt S κ).map p.pr * β.b * (β.b' * (mt S κ⁻¹).map p.pr * β.b)
          = β.b' * ((mt S κ).map p.pr * (β.b * β.b') * (mt S κ⁻¹).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM, Matrix.mul_one, β.b'b]
  · calc β.b' * (mt S κ⁻¹).map p.pr * β.b * (β.b' * (mt S κ).map p.pr * β.b)
          = β.b' * ((mt S κ⁻¹).map p.pr * (β.b * β.b') * (mt S κ).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM', Matrix.mul_one, β.b'b]
  · show _ = β.b * (β.b' * (mt S κ).map p.pr * β.b) * β.b'
    calc (mt S κ).map p.pr = (β.b * β.b') * (mt S κ).map p.pr * (β.b * β.b') := by
          rw [β.bb', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.OffTrace

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.FinData

theorem isFinComb_smul {D : D7} {S T : HSp D} (r : ℂ) (c : WO S T →₀ ℂ) (h : GlobalTheory.SeeSaw.IsFinComb c) :
    GlobalTheory.SeeSaw.IsFinComb (r • c) := fun u hu => h u (Finsupp.support_smul hu)

end GlobalTheory.Fam.FinData
end

