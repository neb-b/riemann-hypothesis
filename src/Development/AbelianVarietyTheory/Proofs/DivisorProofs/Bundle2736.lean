module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatch
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  classical
  have := X.smooth_str
  obtain ⟨hUo, hUeq, hK⟩ := _root_.GlobalTheory.GoodTop.goodPatch_image E O H hP
  set g : V X.dim → ℝ := corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    with hg
  have hKc : IsCompact (e '' tsupport ρ) := hK _ (isClosed_tsupport ρ) hsupp
  have hint : IntegrableOn (corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()))
      (offHyp S (e '' W)) := by
    refine _root_.GlobalTheory.GoodTop.integrableOn_corrC S (e '' W) (e '' tsupport ρ) _ _ _ c hUo hKc (Set.image_mono hsupp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      have htop : z ∈ ptsIn X.str σ (⊤ : X.X.Opens) := by
        simp [ptsIn]
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E ⊤ H₀ hH₀ hP.holo htop (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv a i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j
    · intro v hv a b i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j
    · rintro _ ⟨z, hz, rfl⟩
      exact (_root_.GlobalTheory.GoodTop.contDiffAt_holoChart hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hP.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' (ptsIn X.str σ O ∩ W)) := by
    rw [hUeq]
    exact (hint.re).const_mul _
  have hval : (∫ v in e '' (ptsIn X.str σ O ∩ W), g v) = (Real.pi ^ X.dim)⁻¹ *
      (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re := by
    rw [hUeq, hg]
    simp only [corrTop]
    rw [integral_const_mul]
    congr 1
    exact integral_re hint
  rw [← hval]
  refine _root_.GlobalTheory.GoodTop.hasInt_of_chart (fun c : AlgChart X.str σ X.dim => c.e) (fun i j => i.holo_trans j)
    (fun y => AlgChart.exists_mem_source y) (isOpen_ptsIn O).measurableSet e W g hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (_root_.GlobalTheory.GoodTop.isTopForm_corrDens E O H H₀ hH hH₀ hρ) ?_ ?_ hgi
  · intro i y _ hyW hyi
    have hy : y ∉ tsupport ρ := fun h => hyW (hsupp h)
    have h0 : ρ =ᶠ[𝓝 y] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : (fun v => ρ (i.e.symm v)) =ᶠ[𝓝 (i.e y)] fun _ => 0 := by
      have ht := (i.e.continuousAt_symm (i.e.map_source hyi)).tendsto
      rw [i.e.left_inv hyi] at ht
      exact ht.eventually h0
    simp only [corrDens, corrTop]
    rw [GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero _ _ h1]
    simp
  · intro j y hyS hyW hyj
    exact _root_.GlobalTheory.GoodTop.corrTop_holoChart_trans E O H H₀ hH hH₀ hρ hP.holo j hyS (hP.sub hyW) hyj (hP.frame y hyW)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointExtendsAlongThetaMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtP

theorem genericFibre_polAV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)), GenOf Xo c y t → ∃ (P : PolAV (Sp (FractionRing R))) (α : P.A.left ⟶ Xo.univ.t.G.left) (α' : P.A.left ⟶ t.G.left), P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ IsGrpPullback P.A Xo.univ.t.G (y ≫ pullback.fst _ _) α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsGrpPullback P.A t.G (jK R) α' ∧ LBIso P.L (t.PP.L.pull α') := by
  intro E _ _ _ H Dw l Xo c R _ _ y t hy
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  have hw₁ : LBIso tK.PP.L (t.PP.L.pull m₁.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₁.lin; exact ⟨w, hw⟩
  have hw₂ : LBIso tK.PP.L (Xo.univ.t.PP.L.pull m₂.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₂.lin; exact ⟨w, hw⟩
  have hd := GlobalTheory.UMin.polFib_univ E H Dw l Xo c (FractionRing R) (𝟙 _ ≫ y ≫ pullback.fst _ _)
  obtain ⟨P, α₀, hgP, hpb₀, hL₀⟩ := ((_root_.GlobalTheory.UMin.FibMove.polFib_move _ _ Xo.univ.t.G Xo.univ.t.PP.L tK.G tK.PP.L
    (y ≫ pullback.fst _ _) m₂.cm.F Xo.univ.t.PP.isLB tK.PP.isLB m₂.cart hw₂ _ (FractionRing R) (𝟙 _)).1).2 hd
  refine ⟨P, α₀ ≫ m₂.cm.F, α₀ ≫ m₁.cm.F, hgP, ?_, ?_, ?_, ?_⟩
  · have h := hpb₀.comp m₂.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB Xo.univ.t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₂ α₀ rfl)
  · have h := hpb₀.comp m₁.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₁ α₀ rfl)

theorem extend_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ b : o →+* c.F, f ≫ PSpace.str o n = pullback.snd _ _ ≫ spMap b → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t → ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b → ∃ ξ : Sp R ⟶ PSpace o n, jK R ≫ ξ = y ≫ f ∧ ξ ≫ PSpace.str o n = σ := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm h3 hmu hn hTh b hb R _ _ _ hR t hP y hy σ hσ
  haveI : IsNoetherianRing R := hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgdef
  obtain ⟨σ₀, hnz⟩ := _root_.GlobalTheory.UMin.ExtNZ.exists_sec_nz E H R hR t hP
  obtain ⟨P, α, α', hg, hpb, hL, hpb', hL'⟩ := genericFibre_polAV E H Dw l Xo c R y t hy
  have hpb₁ : IsGrpPullback P.A t.G (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) α' := by
    rw [Category.comp_id]; exact hpb'
  have hpf : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) := ⟨P, α', hg, hpb₁, hL'⟩
  let θ := SecAt.pull t.G t.PP.L σ₀ (algebraMap R (FractionRing R))
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UMin.SymRat.symAt_exists (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R)
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) θ hm hn hpf
  let β : o →+* R := (Spec.preimage σ).hom
  have hβ : spMap β = σ := Spec.map_preimage σ
  have hmR : IsUnit (m : R) := by simpa [β] using hmu.map β
  obtain ⟨e', he', j, hj⟩ := _root_.GlobalTheory.UMin.IntTheta.integral_with_unit E H (Sp R) t g m (n + 1) R (𝟙 _) σ₀ e hm h3 hmR hn hpf hnz he
  have hne : ∃ j, e j ≠ 0 := ⟨j, fun h0 => hj.ne_zero (IsFractionRing.injective R (FractionRing R)
    ((he' j).trans (h0.trans (map_zero _).symm)))⟩
  have hgen := _root_.GlobalTheory.UMin.GenSym.isGenSec_of_symAt (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R) _ θ e hm hn hpf he hne
  have hcrd : PCrd (y ≫ f) e := _root_.GlobalTheory.UMin.pCrd_of_symAt Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m n o (Xo.XF c) (pullback.fst _ _) f (Sp R) t.G t.PP.L t.PP.rig (FractionRing R) y
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) P α α' θ e hm hn hTh t.PP.isLB t.PP.rigGen hg hpb hL hpb₁ hL'
    hgen he
  obtain ⟨ξ, hξ1, hξ2⟩ := _root_.GlobalTheory.UMin.exists_pCrd_of_isUnit o R n β e' ⟨j, hj⟩
  refine ⟨ξ, ?_, hξ1.trans hβ⟩
  have hc1 : PCrd (jK R ≫ ξ) e := by
    have := (_root_.GlobalTheory.UMin.CrdBasic.pCrd_basic).1 o R (FractionRing R) n ξ e' (algebraMap R (FractionRing R)) hξ2
    have ee : (fun j => algebraMap R (FractionRing R) (e' j)) = e := funext he'
    rw [ee] at this; exact this
  refine (_root_.GlobalTheory.UMin.CrdUniq.main).1 o (FractionRing R) n (jK R ≫ ξ) (y ≫ f) e ?_ hc1 hcrd
  rw [Category.assoc, hξ1, hβ, Category.assoc, hb]; exact hσ

end GlobalTheory.UMin.ExtP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.ULift

theorem psiQ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ) (hq : ∀ χ, u.PsiNorm χ (Real.exp (-q χ))) (χ : u.D.toPre.X) : l.q χ = q χ := by
  have h := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ))
  linarith


set_option maxHeartbeats 1000000 in
theorem labels_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p _ z₁ ct yy₁ hL y h
  unfold UIsLabW at hL
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, hi, hu, hR, G, iG, α, β, hα, hβ, hLB, hm, y₀, hy₀, u, lb, j,
    hq, hyy, hcong⟩ := hL
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
    y₂, hy₂, hint₂, u₂, e, T, hpsi, hpt, hw, hfw, hbw⟩ :=
    GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup E H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G iG α β
      hα hβ hLB hm y₀ hy₀ u
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨lb₂⟩ := GlobalTheory.ZH.labels_exist hLaws hLaws2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  have hmap : (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      AddSubgroup.comap (e.trans j).toAddMonoidHom
        (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : ct.T.P.D.toPre.X →+ ct.T.P.D.toPre.X).range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(e.trans j) z, by simp [map_nsmul]⟩
  refine ⟨(QuotientAddGroup.map _ _ (e.trans j).toAddMonoidHom hmap).comp lb₂.yy, ?_, ?_⟩
  · unfold UIsLabW
    refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
      y₂, hy₂, u₂, lb₂, e.trans j, ?_, ?_, ?_⟩
    · intro χ
      rw [psiQ u₂ lb₂ (fun χ => lb.q (e χ)) (fun χ => hpsi χ _ (lb.q_eq (e χ))) χ]
      exact hq (e χ)
    · intro a χ hχ
      rw [AddMonoidHom.comp_apply, hχ, QuotientAddGroup.map_mk]
      rfl
    · intro k a pk pk' x x' w w' hk hx hx' hwx hwx' hww
      obtain ⟨q, hqy, hq'⟩ := hfw k pk x hk hx
      obtain ⟨q', hqy', hq''⟩ := hfw k pk' x' hk hx'
      obtain ⟨v, hvα, hvβ⟩ := hw x w hwx
      obtain ⟨v', hvα', hvβ'⟩ := hw x' w' hwx'
      have hc := hcong k a q q' (T x) (T x') v v' hk hq' hq'' hvα hvα'
        (by rw [hvβ', hww, ← Category.assoc v, hvβ, Category.assoc])
      rw [hqy, hqy'] at hc
      exact hc
  · unfold UDeep.Compat
    intro a μ hμ
    have hN₁ : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
    have hr₁ : 0 < X₁.S.r := by
      obtain ⟨i, -, hi'⟩ := X₁.ρ.r_eq
      rw [hi']; exact pow_pos X₁.ρ.n_prime.pos _
    have hN₂ : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
    have hr₂ : 0 < D.X.S.r := by
      obtain ⟨i, -, hi'⟩ := D.X.ρ.r_eq
      rw [hi']; exact pow_pos D.X.ρ.n_prime.pos _
    have hk1 : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos hr₁ hN₁
    have hk2 : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos hr₂ hN₂
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]
      exact Dvd.dvd.mul_left (D.dvd.trans (dvd_pow_self _ two_ne_zero)) _
    have hd : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) = D.X.S.r * D.X.S.N :=
      Nat.div_mul_cancel hdvd
    have hd1 : 1 ≤ D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) := Nat.div_pos (Nat.le_of_dvd hk2 hdvd) hk1
    obtain ⟨pk₀, x₀, hx₀, hx₀φ⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest _ _ _ ρ' p y₀ u a
    have h1 : lb.yy a = QuotientAddGroup.mk pk₀.y := lb.yy_eq a pk₀ x₀ hx₀ hx₀φ
    have h2 := hyy a pk₀.y h1
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.QLevelRescale.exists_qkPt_rescale _ _ _ ρ' p y₀ u (X₁.S.r * X₁.S.N)
      (D.X.S.r * D.X.S.N) (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) pk₀ x₀ hk1 hd1 hd.symm hx₀
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw _ pk' x₀ hk2 hpk'
    have hx₂ : (T.symm x₀).left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left :=
      (hpt (T.symm x₀) a).2 (by rw [Equiv.apply_symm_apply]; exact hx₀φ)
    have h3 : lb₂.yy (D.lab a) = QuotientAddGroup.mk pk₂.y := lb₂.yy_eq (D.lab a) pk₂ (T.symm x₀) hpk₂ hx₂
    rw [AddMonoidHom.comp_apply, h3, QuotientAddGroup.map_mk]
    have h4 : (e.trans j).toAddMonoidHom pk₂.y = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • j pk₀.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h4]
    rw [h2] at hμ
    rw [QuotientAddGroup.eq] at hμ ⊢
    obtain ⟨z, hz⟩ := hμ
    refine ⟨z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    calc (D.X.S.r * D.X.S.N) • z
        = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • (X₁.S.r * X₁.S.N) • z := by rw [smul_smul, hd]
      _ = _ := by rw [hz, smul_add, smul_neg]

end GlobalTheory.UPoinc.ULift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeve
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer.RangeLe

theorem contW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := _root_.GlobalTheory.BCT.TrKer.continuous_coef_wInf

theorem ratSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := _root_.GlobalTheory.BCT.RatSplit.ratU_split

theorem spanW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := _root_.GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU

theorem semis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def dualW (lam : InfinitePlace E → DomWeight n) : UA E n →* Module.End ℂ (Module.Dual ℂ (Wsp lam)) where
  toFun g := (wInf lam g⁻¹).dualMap
  map_one' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply]
  map_mul' a b := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply, _root_.mul_inv_rev, map_mul]

theorem dualW_apply (lam : InfinitePlace E → DomWeight n) (g : UA E n) (φ : Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    dualW lam g φ w = φ (wInf lam g⁻¹ w) := rfl

theorem wInf_inv_rat (lam : InfinitePlace E → DomWeight n) (γ : UA E n) (γ₀ : UE E n)
    (h : ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1) :
    wInf lam γ⁻¹ = wAt lam γ₀⁻¹ := by
  have e : ∀ v : InfinitePlace E, cEmb v.embedding γ⁻¹ = GeneralLinearGroup.map v.embedding (γ₀⁻¹ : UE E n).1 :=
    fun v => by rw [map_inv, h v, InvMemClass.coe_inv, map_inv]
  unfold wInf wAt
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, e]

theorem phiFun_wInf (lam : InfinitePlace E → DomWeight n) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (x : infU E n)
    (w : Wsp lam) : phiFun lam F (wInf lam x.1 w) = RU E n x.1 (phiFun lam F w) := by
  funext g
  change F (splitFin E n g) (wInf lam g (wInf lam x.1 w)) = F (splitFin E n (g * x.1)) (wInf lam (g * x.1) w)
  rw [map_mul (splitFin E n), splitFin_inf x, mul_one, map_mul (wInf lam), Module.End.mul_apply]

theorem phiFun_mem_fixed (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ fixed (RF E n) (globLev S K') := by
  intro k
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  funext g
  change phiFun lam F w (g * ((k : finU (E := E) (n := n)) : UA E n)) = phiFun lam F w g
  rw [phiFun_mul_fin]
  have e : rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) (k : finU (E := E) (n := n)) F = F := funext fun x => hF.2 k k.2 x
  rw [e]

theorem isAutFormU_phiFun (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    IsAutFormU (phiFun lam F w) := by
  have hfin : ∀ k ∈ finU (E := E) (n := n), dualW lam k = 1 := by
    intro k hk
    refine LinearMap.ext fun φ => LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_fin lam ⟨k⁻¹, (finU (E := E) (n := n)).inv_mem hk⟩]
    rfl
  have hcont : ∀ (u : Module.Dual ℂ (Wsp lam)) (ℓ : Module.Dual ℂ (Module.Dual ℂ (Wsp lam))),
      Continuous fun g => ℓ (dualW lam g u) := by
    intro u ℓ
    obtain ⟨w', rfl⟩ := (Module.evalEquiv ℂ (Wsp lam)).surjective ℓ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, dualW_apply]
    exact (contW E n lam w' u).comp continuous_inv
  have hinf : ∀ y ∈ infU E n, ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    intro y hy g
    simp only [map_mul, splitFin_inf ⟨y, hy⟩, mul_one]
  have hrat : ∀ γ ∈ ratU E n, ∀ g, (fun g => F (splitFin E n g)) (γ * g) = dualW lam γ (F (splitFin E n g)) := by
    intro γ hγ g
    obtain ⟨γ₀, h1, h2⟩ := ratSplit E n γ hγ
    simp only [map_mul, h1]
    rw [hF.1 γ₀ (splitFin E n g)]
    refine LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_inv_rat lam γ γ₀ h2]
    rfl
  have hsm : ∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    have ho : IsOpen ((splitFin E n) ⁻¹' (globLev S K' : Set (finU (E := E) (n := n)))) :=
      (isOpen_globLev E hU n S K' hK).preimage continuous_splitFin
    filter_upwards [ho.mem_nhds (by simp [(globLev S K').one_mem])] with y hy g
    simp only [map_mul]
    exact hF.2 _ hy _
  have h := GlobalTheory.EquivCoef.isAutFormU_coef E n (Module.Dual ℂ (Wsp lam)) (dualW lam) (fun g => F (splitFin E n g))
    hfin hcont hinf hrat hsm (Module.Dual.eval ℂ (Wsp lam) w)
  convert h using 1
  funext g
  simp [dualW_apply]

theorem hasWeightAt_of_wInf (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ))
    (f' : Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (h0 : f' ≠ 0) (hπ : ∀ u, f' u ∈ π)
    (heq : ∀ (x : infU E n) u, f' (wInf lam x.1 u) = RU E n x.1 (f' u)) (v : InfinitePlace E) :
    HasWeightAt π v.embedding (lam v) := by
  obtain ⟨e, he⟩ : ∃ e : ∀ v, nablaSq ℂ n (lam v), f' (PiTensorProduct.tprod ℂ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (PiTensorProduct.ext (MultilinearMap.ext fun e => by simpa using hc e))
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n (lam v), f' ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap e v, ?_,
    fun a => hπ _, fun x a => ?_⟩
  · intro h
    apply he
    have := LinearMap.congr_fun h (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have h2 := heq ⟨x.1, hx⟩ (PiTensorProduct.tprod ℂ (Function.update e v a))
    have h3 : wInf lam x.1 (PiTensorProduct.tprod ℂ (Function.update e v a)) =
        PiTensorProduct.tprod ℂ (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) a)) := by
      change PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext u
      by_cases h : u = v
      · subst h
        simp
      · have h1 := (Subgroup.mem_inf.1 x.2).2
        rw [Subgroup.mem_iInf] at h1
        have h4 := h1 u.embedding
        rw [Subgroup.mem_iInf] at h4
        have h5 : cEmb u.embedding x.1 = 1 := MonoidHom.mem_ker.1 (h4 (by simpa using h))
        simp only [Function.update_of_ne h, h5, map_one, Module.End.one_apply]
    rw [h3] at h2
    simpa [MultilinearMap.toLinearMap] using h2

theorem phiFun_mem_forms (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ forms S lam K' := by
  have h := semis E n (Wsp lam) ((wInf lam).comp (infU E n).subtype) (spanW E n lam) (globLev S K')
    (isOpen_globLev E hU n S K' hK) (phiFun lam F) (fun u => isAutFormU_phiFun hU S lam K' hK F hF u)
    (fun x u => phiFun_wInf lam F x u) (fun u => phiFun_mem_fixed S lam K' F hF u) w
  refine SetLike.le_def.1 ?_ h
  refine iSup_mono fun π => iSup_mono' fun hP => ⟨⟨hP.1, fun v => ?_⟩, le_rfl⟩
  obtain ⟨f', h0, hπ, heq⟩ := hP.2
  exact hasWeightAt_of_wInf lam π f' h0 hπ (fun x u => heq x u) v

end GlobalTheory.BCT.TrKer.RangeLe

namespace GlobalTheory.BCT.TrKer


open GlobalTheory.BCT.TrKer.RangeLe in
theorem range_Phi_le_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  intro E _ _ _ hU n _ S _ lam K' hK
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨F, w, rfl⟩, rfl⟩
  rw [Phi_tmul]
  exact phiFun_mem_forms hU S lam K' hK F.1 F.2 w

end GlobalTheory.BCT.TrKer
end
end

