module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverSwap

variable {D : D7}

theorem eq_zero_of_two {v v' : Pl D} (hne : v ≠ v') {z : AE D} (h : z ∈ idAt D (· = v))
    (h' : z ∈ idAt D (· = v')) : z = 0 := by
  have hc : compAt D v z = 0 := by
    unfold idAt at h'
    exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h').2 ⟨v, hne⟩
  rw [GlobalTheory.FinPl.Model.eq_single h, hc]
  exact (GlobalTheory.AdelicU.Supp.singleTens D.host.E v).map_zero'

theorem cA_mem_idAt {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem symplO_eq_zero_of_ne {v v' : Pl D} (hne : v ≠ v') {S T : HSp D} {x y : WO S T} (hx : MxAt (· = v) x)
    (hy : MxAt (· = v') y) : symplO S T x y = 0 := by
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * x d a = 0 :=
      eq_zero_of_two hne (Ideal.mul_mem_left _ _ (hx d a)) (Ideal.mul_mem_right _ _ (cA_mem_idAt (hy c b)))
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a
        = incA D (S.gram⁻¹ a b) * incA D (T.gram c d) * (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem comb_comm {v v' : Pl D} (hne : v ≠ v') (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {c c' : WO S T →₀ ℂ}
    (hc : CombAt (· = v) c) (hc' : CombAt (· = v') c') (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f) = GlobalTheory.SeeSaw.comb ψ S T c' (GlobalTheory.SeeSaw.comb ψ S T c f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.1 c c' (fun x hx y hy => symplO_eq_zero_of_ne hne (hc x hx) (hc' y hy)) f

end GlobalTheory.FinPl.OverSwap

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.OverSwap in
theorem overSwap : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  intro D k _ _ _ _ p p' n n' m m' _ _ _ _ _ _ _ _ ψ hψ hp hp' hne S T α β α' β' LS LT f₀ g h Ψ Ψ' hv' hO1 hO2
  obtain ⟨hLS, hLT, hf₀, hΨ, -⟩ := id hO1
  obtain ⟨-, -, hg, hΨ', -⟩ := id hO2
  obtain ⟨c, hc, hcO⟩ := (_root_.GlobalTheory.FinPl.Rebase.rebase D k p n n' ψ hψ hp S T α β LS LS LT LT hLS hLT hLS hLT).2 Ψ hΨ
  obtain ⟨c', hc', hcO'⟩ := (_root_.GlobalTheory.FinPl.Rebase.rebase D k p' m m' ψ hψ hp' S T α' β' LS LS LT LT hLS hLT hLS hLT).2 Ψ' hΨ'
  have eg : g = GlobalTheory.SeeSaw.comb ψ S T c f₀ :=
    ((_root_.GlobalTheory.FinPl.overBasic D k p n n' ψ hψ S T α β LS LT hLS hLT f₀ hf₀).1 Ψ hΨ).unique hO1 (hcO f₀ hf₀)
  have eh : h = GlobalTheory.SeeSaw.comb ψ S T c' g :=
    ((_root_.GlobalTheory.FinPl.overBasic D k p' m m' ψ hψ S T α' β' LS LT hLS hLT g hg).1 Ψ' hΨ').unique hO2 (hcO' g hg)
  have hO3 := hcO' f₀ hv'
  have hvac : Vac ψ S T LS LT (· = p.v) (GlobalTheory.SeeSaw.comb ψ S T c' f₀) :=
    ((_root_.GlobalTheory.FinPl.overBasic D k p' m m' ψ hψ S T α' β' LS LT hLS hLT f₀ hv').2.1 Ψ' _ hO3).2 LS LT (· = p.v)
      (fun e => hne e.symm) hf₀
  refine ⟨_, hO3, ?_⟩
  have e : h = GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f₀) := by
    rw [eh, eg, comb_comm hne ψ hc hc']
  rw [e]
  exact hcO _ hvac

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SplitProj

open Formalism.IndefR.Datum Formalism.L2.Theta

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (n : ℕ) :
    ∃ k : F, Valued.v (c - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set r : v.adicCompletion F := algebraMap F _ (π ^ n) with hr_def
  have hr : Valued.v r = WithZero.exp (-(n : ℤ)) := by
    rw [hr_def]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (π ^ n)).trans ?_
    rw [map_pow, hπ]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hr0 : Valued.v r ≠ 0 := by rw [hr]; exact WithZero.exp_ne_zero
  have hN : {y : v.adicCompletion F | Valued.v (c - y) < Valued.v r} ∈ nhds c := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict r)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => c - y)
    simp only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (c - c) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hr0
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hN
  exact ⟨k, (le_of_lt hk).trans_eq hr⟩

theorem afIso_one_tmul_apply (a : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P = GlobalTheory.AdeleBaseChange.adMap F E a P := by
  have key : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≤
      WithZero.exp (-(n : ℤ)) := fun n => by
    obtain ⟨k, hk⟩ := exists_near (P.under (𝓞 F)) (a (P.under (𝓞 F))) n
    have h1 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n hk
    have h2 : Valued.v (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) ≤
        WithZero.exp (-(n : ℤ)) := by
      rw [GlobalTheory.AdeleBaseChange.adMap_apply, ← GlobalTheory.AdeleBaseChange.locMap_algebraMap, ← map_sub]
      exact GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk
    have e : GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P =
        (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) -
          (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 h2)
  by_contra hne
  have h0 : Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := key (1 - WithZero.log (Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P -
    GlobalTheory.AdeleBaseChange.adMap F E a P))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

end Base

variable {D : Formalism.BasicNotions.D7}

theorem toAd_eq_afIso (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.toAd D w = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x a =>
    rw [GlobalTheory.StdFrames.toAd_spec]
    have e : (x ⊗ₜ[D.host.F] a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, GlobalTheory.Mem.Col2.afIso_tmul_one]
    congr 1
    exact FiniteAdeleRing.ext _ fun P => (afIso_one_tmul_apply a P).symm
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem cpt_eq_adAt (Q : HeightOneSpectrum (𝓞 D.host.E)) (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.cpt Q w = GlobalTheory.Mem.Col2.adAt D.host.F Q w := by
  show Formalism.UG.evalV D.host.E Q (GlobalTheory.StdFrames.toAd D w) = Formalism.UG.evalV D.host.E Q (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w)
  rw [toAd_eq_afIso]

theorem pr_eq_of_adAt : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  intro D k _ _ _ _ q PP he z x hz
  have hx : GlobalTheory.StdFrames.cpt PP (toEAf D (incA D x)) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)
  have hz' : GlobalTheory.StdFrames.cpt PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans hz
  have h1 : toEAf D (q.e * z) = toEAf D (q.e * incA D x) := by
    rw [RingHom.map_mul, RingHom.map_mul]
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hQ : Q = PP
    · rw [hQ, hx, hz']
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]
  have h2 : q.pr (q.e * z - q.e * incA D x) = 0 :=
    q.pr_eq_zero_of_toEAf he _ (by rw [RingHom.map_sub, h1, sub_self])
  rw [RingHom.map_sub, sub_eq_zero, ← q.sec_pr, ← q.sec_pr, q.pr_sec, q.pr_sec] at h2
  exact h2

end GlobalTheory.SplitProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_self (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h := p.sec_pr (p.sec a * p.sec b)
  rw [map_mul, p.pr_sec, p.pr_sec] at h
  rw [h, ← mul_assoc, sec_self]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  have h := p.sec_pr 1
  rwa [map_one, mul_one] at h

theorem splitPlaceSection_add_complement_mul (p : SplitPt D k) (a b : k) :
    (p.sec a + (1 - p.e)) * (p.sec b + (1 - p.e)) = p.sec (a * b) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p a
  have hb := sec_self p b
  rw [sec_mul]
  linear_combination (-1 : AE D) * ha + (-1 : AE D) * hb + he

def idl (p : SplitPt D k) : kˣ →* (AE D)ˣ where
  toFun a := ⟨p.sec a + (1 - p.e), p.sec ((a⁻¹ : kˣ) : k) + (1 - p.e),
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, sec_one]; ring,
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, sec_one]; ring⟩
  map_one' := Units.ext (by simp only [Units.val_one, sec_one]; ring)
  map_mul' a b := Units.ext (by simp only [Units.val_mul, splitPlaceSection_add_complement_mul])

theorem idl_val (p : SplitPt D k) (a : kˣ) : ((idl p a : (AE D)ˣ) : AE D) = p.sec (a : k) + (1 - p.e) := rfl

def lam (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) : kˣ →* ℂˣ where
  toFun a := Units.mk0 ((χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _)
      (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _) r).ne'))
  map_one' := Units.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV])
  map_mul' a b := Units.ext (by
    simp only [map_mul, Units.val_mk0, Units.val_mul, Circle.coe_mul, GlobalTheory.SplitLinear.absFin_mul,
      Real.mul_rpow (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le, Complex.ofReal_mul]
    ring)

theorem lam_val (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) (a : kˣ) :
    ((lam p χ r a : ℂˣ) : ℂ) = (χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ) := rfl

end GlobalTheory.SplitLinAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.PlacesDistinct

variable {D : D7}

theorem placeIdem_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  congr 1
  refine RestrictedProduct.ext _ _ fun u => ?_
  by_cases hu : u = v
  · subst hu
    exact h1.trans h1'.symm
  · exact (h2 u hu).trans (h2' u hu).symm

theorem finPart_idem_int {e : AE D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w) :
    finPart D e ∈ intAE D := by
  have h1 := (h.2 1 one_ne_zero).not
  have hw : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have := not_not.1 (h1.1 hw)
  simpa using this

theorem conj_mem_of {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {x x' : 𝓞 D.host.E} (hx' : (x' : D.host.E) = star (x : D.host.E))
    (hx0 : x ≠ 0) (hxw : x ∈ w.asIdeal) (hxw' : x ∉ w'.asIdeal) : x' ∈ w'.asIdeal := by
  have hx'0 : x' ≠ 0 := by
    intro h0
    apply hx0
    have : star (x : D.host.E) = 0 := by rw [← hx', h0]; rfl
    exact RingOfIntegers.coe_eq_zero_iff.mp (star_eq_zero.mp this)
  have hN : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := (h.2 x hx0).1 hxw
  have hI' : finPart D (e' * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := not_not.1 (mt (h'.2 x hx0).2 hxw')
  have he := finPart_idem_int h
  have hee : e = e * e' + e * cA D e' := by
    rw [← mul_add, ← hsum, mul_add, h.1.1, h.1.2.1, add_zero]
  have hsplit : e * incA D ((x : D.host.E)⁻¹) =
      e * (e' * incA D ((x : D.host.E)⁻¹)) + e * (cA D e' * incA D ((x : D.host.E)⁻¹)) := by
    conv_lhs => rw [hee]
    ring
  have hA : finPart D (e * (e' * incA D ((x : D.host.E)⁻¹))) ∈ intAE D := by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hI'
  have hB : finPart D (cA D e' * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := by
    intro hB
    apply hN
    rw [hsplit, map_add (f := _)]
    refine add_mem hA ?_
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hB
  have hC : cA D e' * incA D ((x : D.host.E)⁻¹) = cA D (e' * incA D ((x' : D.host.E)⁻¹)) := by
    rw [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, hx', star_inv₀, star_star]
  rw [hC, GlobalTheory.FinPl.FrameLat.cA_int_iff] at hB
  exact (h'.2 x' hx'0).2 hB

theorem prime_eq {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {π π' : 𝓞 D.host.E}
    (hπ' : (π' : D.host.E) = star (π : D.host.E)) (hw : π ∈ w.asIdeal) (hw' : π ∈ w'.asIdeal)
    (hc : π' ∉ w'.asIdeal) : w = w' := by
  by_contra hne
  have hnle : ¬ w.asIdeal ≤ w'.asIdeal := by
    intro hle
    apply hne
    exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)
  obtain ⟨x₀, hx₀w, hx₀w'⟩ := Set.not_subset.1 hnle
  have hx₀0 : x₀ ≠ 0 := fun h0 => hx₀w' (h0 ▸ w'.asIdeal.zero_mem)
  have hy : π + x₀ ∉ w'.asIdeal := fun hm => hx₀w' (by simpa using w'.asIdeal.sub_mem hm hw')
  have hy0 : π + x₀ ≠ 0 := fun h0 => hy (h0 ▸ w'.asIdeal.zero_mem)
  obtain ⟨c₀, hc₀⟩ : ∃ c : 𝓞 D.host.E, (c : D.host.E) = star (x₀ : D.host.E) :=
    ⟨⟨star (x₀ : D.host.E), (x₀.2).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩
  have h1 : c₀ ∈ w'.asIdeal := conj_mem_of h h' hsum hc₀ hx₀0 hx₀w hx₀w'
  have h2 : π' + c₀ ∈ w'.asIdeal :=
    conj_mem_of h h' hsum (x := π + x₀) (by push_cast; rw [star_add]; exact congrArg₂ (· + ·) hπ' hc₀) hy0 (w.asIdeal.add_mem hw hx₀w) hy
  exact hc (by simpa using w'.asIdeal.sub_mem h2 h1)

end GlobalTheory.AdForm.PlacesDistinct


open GlobalTheory.AdForm.PlacesDistinct in
theorem GlobalTheory.AdForm.StdT.places_injective : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → Function.Injective fun i => (p i).v := by
  intro B X I _ _ l Z u k _ _ _ _ ι p β Q L hS
  obtain ⟨⟨e, he⟩, -⟩ := hS
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  intro i i' hv
  have hv : (p i).v = (p i').v := hv
  apply e.injective
  apply Subtype.ext
  have hmem : ∀ j, X.piT u ∈ (e j).1.asIdeal := fun j => (Formalism.L2.Col.mem_divs hne _).1 (e j).2
  obtain ⟨ε, hε, hε'⟩ := (p i).above
  obtain ⟨ε', hε2, hε2'⟩ := (p i').above
  rw [hv] at hε
  have hsum : (p i).e + cA (I.rec7 l Z) (p i).e = (p i').e + cA (I.rec7 l Z) (p i').e := by
    rw [hε', hε2', placeIdem_unique hε hε2]
  refine prime_eq (he i) (he i') hsum (π := X.piT u) (π' := B.fields.conjO (X.piT u)) rfl (hmem i) (hmem i') ?_
  intro hc
  obtain ⟨a, b, hab⟩ := hcop
  exact (e i').1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ (e i').1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i')) (Ideal.mul_mem_left _ b hc)))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

namespace Place

def intInd (Y Y' : Type) : Matrix Y Y' k → ℂ := Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1

def tensorAt (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) : WO S T → ℂ :=
  fun t => Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)

def tensorL (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := p.tensorAt FS FT Φ Ψ.1
  map_add' Ψ Ψ' := by
    funext t
    simp only [tensorAt, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c Ψ := by
    funext t
    simp only [tensorAt, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorL_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : SB (Matrix Y Y' k)) :
    p.tensorL FS FT Φ Ψ = p.tensorAt FS FT Φ Ψ.1 := rfl

def tensorOne (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ (intInd Y Y')
  map_add' Φ Φ' := by
    funext t
    simp only [tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorOne_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    p.tensorOne FS FT Φ = p.tensorAt FS FT Φ (intInd Y Y') := rfl

end Place
end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Collect

variable {D : D7}

theorem theta_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) : IsThetaFunO ψ S T (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) ih

end GlobalTheory.Core.Rk.Collect

namespace GlobalTheory.Core.Rk.Collect

end GlobalTheory.Core.Rk.Collect
end
end

