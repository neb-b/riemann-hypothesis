module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValOUnramifiedDegreeOne
section
open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.LocUnr

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_exp_neg_one (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (h1 : r ∈ P.asIdeal)
    (h2 : r ∉ P.asIdeal ^ 2) : P.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp (-1 : ℤ) := by
  have e : P.valuation K (algebraMap (𝓞 K) K r) = P.intValuation r := P.valuation_of_algebraMap r
  rw [e]
  have hr : r ≠ 0 := by rintro rfl; exact h2 (Submodule.zero_mem _)
  have a1 := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using h1)
  have a2 := mt (P.intValuation_le_pow_iff_mem r 2).1 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero r hr)] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  push_cast at a1 a2
  omega

end GlobalTheory.LvT.LocUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

abbrev baseOfParams {D : D7} (L : SizeData₂ D) : Arith.Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

theorem kapISet_eq_loc {D : D7} (L : SizeData₂ D) (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = Arith.Loc.kapISet (baseOfParams L) K p n' TT a b := rfl

theorem sig_eq_loc {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (hk : G.KapIDef X K)
    (hb : ∀ h t, X.bs h t = Arith.bsH h t) (a b : G.HH D → ℤ) (p : ℕ) :
    G.Sig X K a b p =
      Arith.Loc.Sig (baseOfParams L) (Arith.ins (baseOfParams L) K 1) K a b (G.hP D p) p := by
  have hb' : X.bs = Arith.bsH := by funext h t; exact hb h t
  have hk' : X.kapI = (Arith.ins (baseOfParams L) K 1).kapI := by
    funext p n' TT a b
    rw [hk p n' TT a b, kapISet_eq_loc]; rfl
  unfold G.Sig G.goodReps G.reps G.kapv G.kapLoc
  rw [hb', hk']
  rfl

theorem wreq_of_wok : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  intro C cD ch p R H a b M c u0 _ hV hF hC h0 hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, hw, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  have ha : G.aL p.L = a := by
    funext t
    unfold G.aL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).1
    · exact (h0 t (hTT' ▸ h)).1.symm
  have hb : G.bL p.L = b := by
    funext t
    unfold G.bL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).2
    · exact (h0 t (hTT' ▸ h)).2.symm
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
      p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
      (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
       open Classical in
       ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
        (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l then (1 : ℝ) else 0) +
          4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) →
      Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK a b := by
    intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6 hW
    obtain rfl : G.hP p.D = hf := funext e6
    subst e1 e2 e0 e3 e4 e5
    unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands
    simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1]
    exact hW
  rw [ha, hb]
  exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh' hW

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRational
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Heis

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (x y : VV ι a b) :
    Formalism.L2.Ker.HV sc y x = (starRingEnd ℂ) (Formalism.L2.Ker.HV sc x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem alpha_opU_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (c : ℝ) (x y : V) (F : V → ℂ) (z : V) :
    alphaQ (c / 2) H x * opU H x (fun w => alphaQ (c / 2) H y * opU H y F w) z =
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((c * (H x y).re + (H x y).im) / 2 : ℝ) : ℂ)) *
        (alphaQ (c / 2) H (x + y) * opU H (x + y) F z) := by
  simp only [alphaQ, opU, Formalism.L2.Th1.H.qOf]
  rw [← add_assoc z x y]
  have key : ∀ a b c d e f g u : ℂ, a + b + c + d = e + f + g →
      Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
        Complex.exp e * (Complex.exp f * (u * Complex.exp g)) := by
    intro a b c d e f g u h
    have : Complex.exp a * Complex.exp b * Complex.exp c * Complex.exp d =
        Complex.exp e * Complex.exp f * Complex.exp g := by
      simp only [← Complex.exp_add, h]
    linear_combination u * this
  apply key
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hH x y]
  have h1 : H x y = ((H x y).re : ℂ) + ((H x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (H x y) = ((H x y).re : ℂ) - ((H x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Complex.add_re, Complex.conj_re]
  rw [h2]
  generalize (H x y).re = r at *
  generalize (H x y).im = s at *
  rw [h1]
  push_cast
  ring

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add _ x y

theorem Wx_Wx (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z := by
  funext z
  have := alpha_opU_mul (Formalism.L2.Ker.HV A.sc) (fun x y => HV_conj A.sc x y) (Real.sqrt A.d) (emb A x) (emb A y) F z
  rw [← emb_add] at this
  exact this

theorem imH_eq (x y : HomE X.E a b) : imH A x y = coc A x y - coc A y x := by
  simp only [coc, imH, altE]
  rw [HV_conj A.sc (emb A x) (emb A y)]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

theorem imH_add_left (x y z : HomE X.E a b) : imH A (x + y) z = imH A x z + imH A y z := by
  simp only [imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_im]

theorem imH_add_right (x y z : HomE X.E a b) : imH A x (y + z) = imH A x y + imH A x z := by
  simp only [imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_im]

theorem Wx_comm (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z := by
  rw [Wx_Wx, Wx_Wx, add_comm y x]
  funext z
  have : brkE A y x = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A x y : ℂ)) := rfl
  rw [this, ← mul_assoc, ← Complex.exp_add, imH_eq]
  congr 2
  push_cast
  ring

theorem contDiff_Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) (k : ℕ) (hF : ContDiff ℂ k F) :
    ContDiff ℂ k (Wx A x F) := by
  have h : ContDiff ℂ k (fun z : VCx X.Tau a b => Formalism.L2.Ker.HV A.sc z (emb A x)) := by
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply]
    fun_prop
  unfold Wx opU
  exact contDiff_const.mul ((hF.comp (contDiff_id.add contDiff_const)).mul
    (((contDiff_const.mul h).sub contDiff_const).cexp))

theorem jetC_sum (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ)
    (hF : ∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m := by
  classical
  have hd : ∀ n : ℕ, iteratedFDeriv ℂ n (fun z => ∑ i ∈ T, c i * F i z) 0 = ∑ i ∈ T, c i • iteratedFDeriv ℂ n (F i) 0 := by
    intro n
    have e : (fun z => ∑ i ∈ T, c i * F i z) = ∑ i ∈ T, c i • F i := by
      funext z; simp
    rw [e, iteratedFDeriv_sum_apply (f := fun i => c i • F i) (fun i hi => ((hF i hi n).const_smul (c i)).contDiffAt)]
    exact Finset.sum_congr rfl fun i hi => iteratedFDeriv_const_smul_apply (hF i hi n).contDiffAt
  simp only [jetC, derivAt0, hd, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem calculus : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  intro X A a b
  refine ⟨Wx_Wx A, Wx_comm A, imH_eq A, fun x y z => ⟨?_, ?_, imH_add_left A x y z, imH_add_right A x y z⟩,
    fun _ _ => rfl, fun y t => ?_, fun x F hF k => contDiff_Wx A x F k (hF k), fun κ T c F hF m => jetC_sum A κ T c F hF m⟩
  · simp only [coc, imH_add_left, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re]; ring
  · simp only [coc, imH_add_right, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re]; ring
  · have : brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ)) := rfl
    rw [this, Complex.exp_eq_one_iff]
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have : ((imH A t y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination -hn
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring

end GlobalTheory.MomT.Heis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiIndEqInter
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.XiIndZero

open GlobalTheory.ThetaInter

variable {V : Type} [AddCommGroup V]

theorem isReps_repsOf {L₁ L₂ : AddSubgroup V} (h : relIdx L₁ L₂ ≠ 0) : IsReps L₁ L₂ (repsOf L₁ L₂) := by
  classical
  have : Fintype (L₂ ⧸ L₁.addSubgroupOf L₂) := AddSubgroup.fintypeOfIndexNeZero h
  refine Classical.epsilon_spec (p := fun S => IsReps L₁ L₂ S)
    ⟨Finset.univ.image fun c : L₂ ⧸ L₁.addSubgroupOf L₂ => ((Quotient.out c : L₂) : V), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out c : L₂).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    have : d = c := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      simpa [neg_add_eq_sub] using hxy
    rw [this]
  · intro y hy
    refine ⟨_, Finset.mem_image.2 ⟨((⟨y, hy⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂), Finset.mem_univ _, rfl⟩, ?_⟩
    have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' ((⟨y, hy⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂))
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [neg_add_eq_sub] using this

theorem sum_reps {M : Type*} [AddCommMonoid M] {L₁ L₂ : AddSubgroup V} [Fintype (L₂ ⧸ L₁.addSubgroupOf L₂)]
    {S : Finset V} (hS : IsReps L₁ L₂ S) (f : V → M) (hf : ∀ a ∈ L₂, ∀ s ∈ L₂, s ∈ L₁ → f (a + s) = f a) :
    ∑ x ∈ S, f x = ∑ c : L₂ ⧸ L₁.addSubgroupOf L₂, f ((Quotient.out c : L₂) : V) := by
  refine Finset.sum_bij (fun x hx => ((⟨x, hS.1 x hx⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx y hy hxy
    have := QuotientAddGroup.eq.1 hxy.symm
    rw [AddSubgroup.mem_addSubgroupOf] at this
    exact hS.2.1 x hx y hy (by simpa [neg_add_eq_sub] using this)
  · intro c _
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨x, hx, hxy⟩ := hS.2.2 y y.2
    refine ⟨x, hx, QuotientAddGroup.eq.2 ?_⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hxy
  · intro x hx
    set c := ((⟨x, hS.1 x hx⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂) with hc
    have := QuotientAddGroup.eq.1 ((QuotientAddGroup.out_eq' c).trans hc)
    rw [AddSubgroup.mem_addSubgroupOf] at this
    have h2 := hf _ (Quotient.out c : L₂).2 _ (-(Quotient.out c : L₂) + ⟨x, hS.1 x hx⟩ : L₂).2 this
    simpa using h2

theorem card_reps {L₁ L₂ : AddSubgroup V} (h : relIdx L₁ L₂ ≠ 0) {S : Finset V} (hS : IsReps L₁ L₂ S) :
    S.card = relIdx L₁ L₂ := by
  have : Fintype (L₂ ⧸ L₁.addSubgroupOf L₂) := AddSubgroup.fintypeOfIndexNeZero h
  have h1 := sum_reps hS (fun _ => (1 : ℕ)) fun _ _ _ _ _ => rfl
  rw [relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  simpa using h1

theorem xiInd_eq_inter : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) (vol : ℝ) (θ : V → ℂ) (s z : V), IsHerm H → IsSelfDual H B → IsSemiChar H B α → IsSelfDual H Λ → θ ∈ fixedBy H α Λ → 0 < vol → Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) → relIdx B Λ ≠ 0 → relIdx Λ B ≠ 0 → ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol B (repsOf B (Λ ⊓ A)) (repsOf Λ B) θ s z = ((Real.sqrt (relIdx B Λ : ℕ) : ℝ) : ℂ)⁻¹ * (α s * opU H (-s) (inter H α Λ B θ) z) := by
  intro V _ _ H α A B Λ vol θ s z hH hdB hsB hdΛ hθ hvol hle h1 h2
  classical
  have i1 : Fintype (Λ ⧸ B.addSubgroupOf Λ) := AddSubgroup.fintypeOfIndexNeZero h1
  have i2 : Fintype (B ⧸ Λ.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h2
  have hA : IsReps B (Λ ⊓ A) (repsOf B (Λ ⊓ A)) :=
    isReps_repsOf fun h => h1 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have hB : IsReps Λ B (repsOf Λ B) := isReps_repsOf h2
  set SA := repsOf B (Λ ⊓ A)
  set SB := repsOf Λ B
  have hA' : IsReps B Λ SA := by
    refine ⟨fun x hx => (hA.1 x hx).1, hA.2.1, fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
    obtain ⟨x, hx, hxa⟩ := hA.2.2 a ha
    exact ⟨x, hx, by rw [add_sub_right_comm]; exact B.add_mem hxa hb.2⟩
  have hcard : SA.card = relIdx B Λ := card_reps h1 hA'
  have hidx : relIdx Λ B = relIdx B Λ := by
    simp only [relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    exact card_eq_card hH hdB hdΛ
  obtain ⟨t₀, ht₀, ht₀B⟩ := hA'.2.2 0 Λ.zero_mem
  have ht₀B' : t₀ ∈ B := by simpa using ht₀B
  have hhat : ∀ y ∈ B, hatS H vol SA (indL B) y =
      ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℂ) / (relIdx B Λ : ℂ)) := by
    intro y hy
    rw [hatS, hcard, Finset.sum_eq_single_of_mem t₀ ht₀]
    · have : brk H y t₀ = 1 := by
        rw [← (chi_eq_one_iff t₀ y).2 (hdB.ge ht₀B' y hy), brk, chi]
        congr 1; ring
      simp [this, indL, ht₀B']
    · intro t ht hne
      have : t ∉ B := fun h => hne (hA'.2.1 t ht t₀ ht₀ (B.sub_mem h ht₀B'))
      simp [indL, this]
  have hn : (0 : ℝ) < (relIdx B Λ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h1
  set r : ℂ := ((Real.sqrt (relIdx B Λ : ℕ) : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by rw [hr]; exact_mod_cast (Real.sqrt_pos.2 hn).ne'
  have hr2 : (relIdx B Λ : ℂ) = r ^ 2 := by rw [hr]; exact_mod_cast (Real.sq_sqrt hn.le).symm
  set v : ℂ := ((Real.sqrt vol : ℝ) : ℂ) with hv
  have hv0 : v ≠ 0 := by rw [hv]; exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hv2 : (vol : ℂ) = v ^ 2 := by rw [hv]; exact_mod_cast (Real.sq_sqrt hvol.le).symm
  have hxi : xiS H α vol SA SB (indL B) θ = fun w => (v * r⁻¹) * inter H α Λ B θ w := by
    funext w
    rw [inter, finsum_eq_sum_of_fintype, hidx, ← hr,
      ← sum_reps hB (fun y => α y * opU H y θ w) ?_, xiS, sumU, ← mul_assoc, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [hhat y (hB.1 y hy), hr2, hv2]
      field_simp
    · intro a ha b hb hbΛ
      have e : (fun w => α b * opU H b θ w) = θ := funext (hθ b hbΛ)
      show α (a + b) * opU H (a + b) θ w = α a * opU H a θ w
      rw [alpha_opU_add hH hdB hsB ha hb, ← opU_mul, e]
  rw [xiInd, hxi]
  simp only [opU_mul]
  field_simp

end GlobalTheory.XiIndZero
end

