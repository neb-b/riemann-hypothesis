module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTrans
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalTrans

open Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem isScalar_trans {Λ : Submodule (𝓞 E) S.V} {r k : ℕ} {T T' : E} {F : LFlag S r T}
    {F' F'' F''' : LFlag S r T'} {β γ : S.V ≃ₗ[E] S.V}
    (hΛ : Submodule.IsFullLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) (hL'' : IsLift Λ F'')
    (hG'' : Gval F F'' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) (hz : β F'.fl.z = F''.fl.z)
    (hs1 : s0 Λ F F' F'' β k = 1) (hS1 : IsScalar Λ F F' F'' β) (hS2 : IsScalar Λ F F'' F''' γ) :
    IsScalar Λ F F' F''' (β.trans γ) := by
  have n' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL' hG'
  have n'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL'' hG''
  have hTh1'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.thEq''Q hΛ hdim n' n'' hs1
  intro y1 hy1 y3 hy3 y1' hy1' y3' hy3' h13 h31 al al'
  have hy1b : y1 ∈ orth S (Xplus F) := hy1.2
  have hy1'b : y1' ∈ orth S (Xplus F') := hy1'.2
  have hy2 : y1 ∈ Ylift Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh1'' hy1, hy1b⟩
  have hy2' : β y1' ∈ Ylift' Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi hX hTh1'' hy1',
      _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.mapOrthXplusQ hi hX hz hy1'b⟩
  have a := hS1 y1 hy1 y1 hy2 y1' hy1' (β y1') hy2' (by simp) (by simp) al al'
  have b := hS2 y1 hy2 y3 hy3 (β y1') hy2' y3' hy3' h13 h31 al al'
  exact a.trans b

end Gen

theorem scalar_pair_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 →
    (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 →
    (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  intro D X Y u u' t t' t'' hG hG' hG'' h1 hsc1 h2 hsc2
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ s : TauC Y u u', s.G ≠ 0 → Gval (lf D (X.Fu u)) s.frame ≠ 0 := fun s hs h =>
    hs ((Formalism.L2.SG.Pf.SatGram.gterm_G Y s).trans h)
  have hfull : Submodule.IsFullLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ s : TauC Y u u', IsLift s.lam s.frame := fun s => s.rep.2.2.2.2.1
  obtain ⟨⟨hl1, hl1'⟩, hs1, hS1⟩ := (show scalT t t' from hsc1)
  obtain ⟨⟨hl2, hl2'⟩, hs2, hS2⟩ := (show scalT t' t'' from hsc2)
  rw [← hl1] at hs2 hS2
  have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
  have hL'' : IsLift t.lam t''.frame := by rw [hl1, hl2]; exact hLt t''
  have hth1 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hfull _ t.frame t'.frame _ hLF (hLt t)
    (hGv t hG)).1 hs1
  have hth2 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hfull _ t'.frame t''.frame _ hLF hL'
    (hGv t' hG')).1 hs2
  have htr := Formalism.L2.SG.NGCut.CorankRelation.Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹)
    (t''.lin * t'.lin⁻¹) (fun x hx => (Formalism.L2.SG.NGCut.CorankRelation.frame_mem_iff t' t'' x).1 hx) hth1 hth2
  have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
  rw [hmul] at htr
  have hs3 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t''.frame (t''.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hfull _ t.frame t''.frame _ hLF (hLt t) (hGv t hG)).2 htr

  have hi1 := t.rep.2.2.1
  have hi2 := t'.rep.2.2.1
  have hiβ : t'.lin * t.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hi2 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hi1)
  have hX : ∀ j, (Xflag t.frame j).map ((t'.lin * t.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
      (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag t'.frame j := by
    intro j
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t'.lin hi2,
      ← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hz : (t'.lin * t.lin⁻¹) t.frame.fl.z = t'.frame.fl.z := by
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t'.lin hi2]
    simp
  have hsc3 := isScalar_trans (β := t'.lin * t.lin⁻¹) (γ := t''.lin * t'.lin⁻¹) hfull hdim hLF (hLt t) (hGv t hG) hL'
    (hGv t' hG') hiβ hX hz hs1 hS1 hS2
  have e3 : (t'.lin * t.lin⁻¹).trans (t''.lin * t'.lin⁻¹) = t''.lin * t.lin⁻¹ := hmul
  rw [e3] at hsc3
  have hl : t.lam = t''.lam ∧ t.lam' = t''.lam' := ⟨hl1.trans hl2, hl1'.trans hl2'⟩
  refine ⟨?_, ?_⟩
  · show s0T t t'' = 1
    unfold s0T
    rw [if_pos hl]
    exact hs3
  · show scalT t t''
    exact ⟨hl, hs3, hsc3⟩

end GlobalTheory.ScalTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumSeriesIdempotentCoeffRightTranslation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabFix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_mul (a b : GAf L n) (f : GAf L n → ℂ) :
    Formalism.L2.NG.rt L n (a * b) f = Formalism.L2.NG.rt L n a (Formalism.L2.NG.rt L n b f) := by
  funext g
  show f (g * (a * b)) = f (g * a * b)
  rw [mul_assoc]

theorem rt_one (f : GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext g
  show f (g * 1) = f g
  rw [mul_one]

theorem exists_lifts (n : ℕ) (s : SplitPlace L) (g : ℕ) (hg : g.Prime) :
    ∃ ℓ : GL (Fin n) (ZMod g) → GAf L n, ∀ γ, IsLift s (ℓ γ) γ := by
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  have key : ∀ γ : GL (Fin n) (ZMod g), ∃ x : GAf L n, IsLift s x γ := by
    intro γ
    let A : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
    have hA : (Int.castRingHom (ZMod g)).mapMatrix A = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
      ext i j
      show ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ) : ZMod g) = _
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdet : A.det ≠ 0 := by
      intro h0
      have h1 := congrArg (Int.castRingHom (ZMod g)) h0
      rw [RingHom.map_det, hA, map_zero] at h1
      exact (Matrix.isUnits_det_units γ).ne_zero h1
    let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
      (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))).mapMatrix A
    have hB : IsUnit B.det := by
      rw [isUnit_iff_ne_zero, ← RingHom.map_det, eq_intCast]
      exact Int.cast_ne_zero.mpr hdet
    obtain ⟨x, hx, hloc⟩ := _root_.GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s (Matrix.nonsingInvUnit B hB)
    refine ⟨x, hx, fun i j => ?_⟩
    have hij : (s.loc n x : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j =
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L)) := by
      rw [hloc]
      show (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) (A i j) = _
      rw [eq_intCast]
      exact Int.cast_natCast _
    rw [hij, sub_self, map_zero]
    exact zero_lt_one
  choose ℓ hℓ using key
  exact ⟨ℓ, hℓ⟩

end Gen

theorem sum_serCoef_rt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) (lf : G0g D.nd → GAf D.host.E D.R.r), FrameRed X h t PY c red → IsSec X red sec → (∀ γ, PY.ψ (lf γ) = kap X h t (sec γ)) → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (τ : Tup2 D), HasTuple D π τ → ∀ φ ∈ π.S, (∀ k ∈ X.B.I.Kg X.B.g, ∀ κ, PY.ψ κ = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r κ φ = φ) → ∑ᶠ γ, serCoef τ γ • Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ = φ := by
  intro D X h t PY c red sec lf hFR hsec hlf π τ hτ φ hφ hfix
  classical
  obtain ⟨hred, hex, hlift⟩ := hFR
  obtain ⟨-, hmul, -, hker⟩ := hred
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have kap_mul : ∀ k k' : X.B.I.Gf, kap X h t (k * k') = kap X h t k * kap X h t k' := by
    intro k k'
    have e : ((1, k * k') : X.B.I.GA) = (1, k) * (1, k') := by rw [Prod.mk_mul_mk, one_mul]
    have cm : ∀ a b : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * (a * b) * t = t⁻¹ * a * t * (t⁻¹ * b * t) := by
      intro a b; group
    unfold kap
    rw [e, map_mul]
    exact cm _ _
  have kap_inv : ∀ k : X.B.I.Gf, kap X h t k⁻¹ = (kap X h t k)⁻¹ := by
    intro k
    have e : ((1, k⁻¹) : X.B.I.GA) = (1, k)⁻¹ := by rw [Prod.inv_mk, inv_one]
    have ci : ∀ a : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by
      intro a; group
    unfold kap
    rw [e, map_inv]
    exact ci _
  have K_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, OneMemClass.coe_one]
    exact one_mem _
  have K_mul : ∀ a b : X.B.I.Gf, a ∈ X.B.I.Kset → b ∈ X.B.I.Kset → a * b ∈ X.B.I.Kset := by
    intro a b ha hb
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_mul] at *
    exact mul_mem ha hb
  have K_inv : ∀ a : X.B.I.Gf, a ∈ X.B.I.Kset → a⁻¹ ∈ X.B.I.Kset := by
    intro a ha
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, InvMemClass.coe_inv] at *
    exact inv_mem ha
  have red_one : red 1 = 1 := by
    have e := hmul 1 K_one 1 K_one
    rw [one_mul] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have red_inv : ∀ k ∈ X.B.I.Kset, red k⁻¹ = (red k)⁻¹ := by
    intro k hk
    have e := hmul k⁻¹ (K_inv k hk) k hk
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have key : ∀ (γ : G0g D.nd) (y : GAf D.host.E D.R.r) (k : X.B.I.Gf), k ∈ X.B.I.Kset → red k = γ →
      PY.ψ y = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r y φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro γ y k hk hrk hy
    obtain ⟨hs1, hs2⟩ := hsec γ
    have hm : (sec γ)⁻¹ * k ∈ X.B.I.Kg X.B.g := by
      refine (hker _ (K_mul _ _ (K_inv _ hs1) hk)).1 ?_
      rw [hmul _ (K_inv _ hs1) _ hk, red_inv _ hs1, hs2, hrk, inv_mul_cancel]
    have hψ : PY.ψ ((lf γ)⁻¹ * y) = kap X h t ((sec γ)⁻¹ * k) := by
      rw [map_mul, map_inv, hlf, hy, kap_mul, kap_inv]
    have e := hfix _ hm _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r y φ
        = Formalism.L2.NG.rt D.host.E D.R.r (lf γ * ((lf γ)⁻¹ * y)) φ := by rw [mul_inv_cancel_left]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r ((lf γ)⁻¹ * y) φ) := rt_mul _ _ _
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [e]
  set φ' := Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ φ with hφ'
  have hφ'S : φ' ∈ π.S := π.stable _ _ hφ
  have back : Formalism.L2.NG.rt D.host.E D.R.r c φ' = φ := by
    rw [hφ', ← rt_mul, mul_inv_cancel, rt_one]
  have fix1 : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
      ∀ x, IsLift s x (1 : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) → Formalism.L2.NG.rt D.host.E D.R.r x φ' = φ' := by
    intro kv s hs x hx
    obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs x 1 hx
    have hrk : red k = 1 := by
      funext kv'
      rw [Pi.one_apply]
      by_cases e : kv' = kv
      · subst e; exact hr1
      · exact hr2 kv' e
    have e := hfix k ((hker k hk).1 hrk) _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r x φ'
        = Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ (Formalism.L2.NG.rt D.host.E D.R.r (c * x * c⁻¹) φ) := by
          rw [hφ', ← rt_mul, ← rt_mul]; congr 1; group
      _ = φ' := by rw [e]
  have step : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (γ : G0g D.nd), γ kv = 1 →
      ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
        Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro kv γ hγ
    obtain ⟨s, hs⟩ := hex kv
    obtain ⟨ℓ, hℓ⟩ := exists_lifts D.R.r s (D.host.g kv.1) (D.host.g_prime kv.1)
    have hser := ((hτ kv.1 kv.2).2 s hs) ℓ hℓ φ' hφ'S (fix1 kv s hs)
    rw [finsum_eq_sum_of_fintype] at hser
    have hterm : ∀ β, Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ =
        Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
      intro β
      obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs (ℓ β) β (hℓ β)
      obtain ⟨hs1, hs2⟩ := hsec γ
      have hred : red (sec γ * k) = Function.update γ kv β := by
        rw [hmul _ hs1 _ hk, hs2]
        funext kv'
        by_cases e : kv' = kv
        · subst e; simp [hγ, hr1]
        · simp [Function.update_of_ne e, hr2 kv' e]
      have e := key _ (lf γ * (c * ℓ β * c⁻¹)) (sec γ * k) (K_mul _ _ hs1 hk) hred
        (by rw [map_mul, hlf, hψ, kap_mul])
      rw [← e, hφ', ← rt_mul, ← rt_mul, ← rt_mul]
      congr 1
      group
    calc ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ
        = ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) :=
          Finset.sum_congr rfl fun β _ => by rw [hterm]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c
          (∑ β, (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β • Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [hser, back]
  have hfin := GlobalTheory.T.sum_prod_fixed_place_average_alt (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (fun kv β => (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β) (fun γ => Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ) step
  have h1 : Formalism.L2.NG.rt D.host.E D.R.r (lf 1) φ = φ :=
    hfix (sec 1) ((hker _ (hsec 1).1).1 ((hsec 1).2)) _ (hlf 1)
  rw [finsum_eq_sum_of_fintype]
  exact hfin.trans h1

end GlobalTheory.LabFix

end
end

