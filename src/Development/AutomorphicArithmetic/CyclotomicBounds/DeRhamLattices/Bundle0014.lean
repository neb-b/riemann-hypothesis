module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0012
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AutomorphicFormIffRationalLevelLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem exists_finPt {D : D7} (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, finPt V k = x := by
  obtain ⟨hsplit, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨g, hg⟩ := x.2
  obtain ⟨a, ha, k, hk, rfl⟩ := hsplit g
  have ha' : finHom V a = 1 := ha
  refine ⟨k, hk, Subtype.ext ?_⟩
  rw [MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul]

private theorem lev_iff {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : GA D S →* Module.End ℂ W) (hρ : ∀ h ∈ GfC S, ρ h = 1) (J : Set (GA D S)) (χ : GA D S → ℂ)
    (hJ : ∀ k, (k ∈ J ↔ k ∈ Lev.levG S B.F.βS (B.levS ψ)) ∧
      (k ∈ Lev.levG S B.F.βS (B.levS ψ) → χ k = Lev.levChi S B.F.βS (B.levS ψ) k))
    (f : Bridge.Gf S → W) (F : GA D S → W) (hF : ∀ g, F g = ρ g⁻¹ (f (finPt S g))) :
    F ∈ RecTie.levSubV S W J χ ↔
      ∀ (h : Bridge.Gf S) (k : B.levJ ψ), f (h * (k : Bridge.Gf S)) = ((B.levLam ψ k : ℂˣ) : ℂ) • f h := by
  change (∀ k ∈ J, ∀ g, F (g * k) = χ k • F g) ↔ _
  constructor
  · rintro H h ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := exists_finPt S h
    obtain ⟨k, hk', rfl⟩ := exists_finPt S k
    have hkG := (B.finPt_mem_levJ ψ hk').1 hk
    have := H k ((hJ k).1.2 hkG) h
    rw [hF, hF, hρ _ ((GfC S).inv_mem hh), hρ _ ((GfC S).inv_mem ((GfC S).mul_mem hh hk')), (hJ k).2 hkG,
      ← B.levLam_finPt ψ hk, finPt, map_mul] at this
    exact this
  · intro H k hk g
    have hkG := (hJ k).1.1 hk
    have hk' : k ∈ GfC S := hkG.1
    have hkJ := (B.finPt_mem_levJ ψ hk').2 hkG
    have h1 := H (finPt S g) ⟨_, hkJ⟩
    have h2 : finPt S (g * k) = finPt S g * finPt S k := map_mul _ _ _
    rw [hF, hF, h2, h1, (hJ k).2 hkG, ← B.levLam_finPt ψ hkJ, mul_inv_rev, map_mul ρ, hρ _ ((GfC S).inv_mem hk'),
      Module.End.mul_apply, Module.End.one_apply]
    exact LinearMap.map_smul (ρ g⁻¹) _ _

private theorem adForms_left {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (γ : Γ) (g : G) : F (ι γ * g) = ρ γ (F g) := by
  simpa using hF γ g 1

private theorem law_right {G A W : Type} [Group G] [Group A] {Γ : Subgroup A} {ι : Γ →* G} [AddCommGroup W] [Module ℂ W]
    {ρ : A →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * (k : G)) = ((χ k : ℂˣ) : ℂ) • ρ (γ : A) (F h)) (h : G) (k : J) :
    F (h * (k : G)) = ((χ k : ℂˣ) : ℂ) • F h := by
  simpa using hF 1 h k

theorem _root_.UpperTheory.KN.automorphic_form_iff_rational_level_law :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ f : Bridge.Gf (Vc D j) → (X.R.cV j).W, (∃ x, (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) = f) ↔
      ∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)),
        f (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) = (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) (f h) := by
  intro D X X0 Y S YS Z c w j H ι hι f
  have hrange := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).2.1
  have key := fun y : (X.R.HV j (Y.tupT (D.what₂.muTw w))).H =>
    lev_iff (baseOf Z c w j) (twVia Z.ρ ι) (X.R.cV j).ρ (X.char.models.cV j).1 _ _
      (UpperTheory.KN.levS_iff_levG_and_levChi_eq D X X0 Y S YS Z c w j H ι hι) ((X.R.HV j (Y.tupT (D.what₂.muTw w))).e y)
      (X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) y) (fun _ => rfl)
  constructor
  · rintro ⟨x, rfl⟩ γ h k
    have h1 := (key (formOf Y (used_of_tw H.tw) j x)).1 (by
      rw [extV_formOf]
      exact (Y.IL.jMt _ (used_of_tw H.tw) j x).2.2)
    have h2 := adForms_left (hrange.le (LinearMap.mem_range_self _ (formOf Y (used_of_tw H.tw) j x))) γ h
    exact (h1 _ k).trans (congrArg (fun v => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) • v) h2)
  · intro hf
    have hA : f ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).J
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).χ := by
      intro γ h k
      obtain ⟨hk, hχ⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
      exact (hf γ h ⟨k, hk⟩).trans (congrArg (fun u : ℂˣ => (u : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) (f h)) hχ)
    obtain ⟨y, rfl⟩ := hrange.ge hA
    have h1 := (key y).2 (law_right hf)
    refine ⟨(Y.IL.jMt _ (used_of_tw H.tw) j).symm ⟨X.R.toRealDat.extV j _ y, ⟨y, rfl⟩, h1⟩, congrArg _ ?_⟩
    apply Y.hinj j
    rw [extV_formOf]
    exact congrArg Subtype.val ((Y.IL.jMt _ (used_of_tw H.tw) j).apply_symm_apply _)
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemMtLatOfCoefficientsMemCoefLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ F ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι), (∀ a, F ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a)) →
      F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι F hF hy
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hc : IsCoefRing D.what₂.embLL (labLL D) (intLL D) :=
    ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ⟨a, rfl⟩⟩
  refine (Base.mem_mtLat _ _ _ _).2 ⟨hF, fun h => ?_⟩
  obtain ⟨a, γ, k, e⟩ := ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.reps h).exists
  obtain ⟨hk, -⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
  have h1 := ((Base.mem_formsC _).1 hF).2 γ ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ⟨k, hk⟩
  have h2 := Base.act_mem_coefLat hB.frame hc γ _ k (Base.mem_St_of_mem_levJ hk) (hy a)
  have h3 := GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι ⟨k, hk⟩
  have h4 := Submodule.smul_mem _ (⟨_, h3⟩ : intLL D) h2
  subst e
  exact h1 ▸ h4
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormCoefficientsIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem exists_of_mem_coefLatFn {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (φ : GLR D n → ℂ)
    (hφ : φ ∈ coefLatFn D.what₂.embLL (labLL D) (intLL D) lam M) :
    ∃ F : VV D.what₂.LL lam, F ∈ nabAtr (labLL D) lam M ∧ φ = coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ => exact hφ
  | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
  | add φ ψ _ _ h1 h2 =>
    obtain ⟨F1, m1, rfl⟩ := h1
    obtain ⟨F2, m2, rfl⟩ := h2
    exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
  | smul a φ _ h1 =>
    obtain ⟨F1, m1, rfl⟩ := h1
    obtain ⟨t, ht⟩ := a.2
    refine ⟨t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
    have e1 : ((t • F1 : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) =
        MvPolynomial.C (t : D.what₂.LL) * (F1 : Pol D.what₂.LL D.what₂.Tau n) := by
      rw [← MvPolynomial.smul_eq_C_mul]
      rfl
    have e2 : D.what₂.embLL (t : D.what₂.LL) = (a : ℂ) := by
      rw [← ht]
      rfl
    show (a : ℂ) * coefFn _ _ (F1 : Pol D.what₂.LL D.what₂.Tau n) y = _
    rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
    ring

theorem _root_.UpperTheory.KN.scaled_fock_form_coefficients_integral :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ gramR c0R c0L, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L →
      ∀ κ : ℂ, κ ≠ 0 → (∀ F : VV D.what₂.LL (lamV D j), harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) = κ • coefFn D.what₂.embLL (lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) →
      ∀ (h : Bridge.Gf (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank), P ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) h ↔
        ∃ F : VV D.what₂.LL (lamV D j), F ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) h) ∧ P = κ⁻¹ • X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu gramR c0R c0L _ κ hκ hF h P
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hval : ∀ v, X.R.ioP j (PiTensorProduct.tprod ℂ u) v ∈
      harm (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS := fun v => by
    have h1 := LinearMap.mem_range_self (X.R.ioP j (PiTensorProduct.tprod ℂ u)) v
    rw [(UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu).2] at h1
    exact h1
  have hM : (baseOf Z c w j).latAt h = Bridge.hLat (Vc D j) h :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (Z.good.latS _ j _)) _
  have hlam : (baseOf Z c w j).w.lam = lamV D j := hBo.lam
  unfold Base.coefLat
  rw [mem_harmLat, hlam, hM]
  constructor
  · rintro ⟨hPh, hPF⟩
    obtain ⟨F, hF0, hFe⟩ := exists_of_mem_coefLatFn _ _ _ hPF
    refine ⟨F, hF0, ?_⟩
    have hm : ∀ τ, (baseOf Z c w j).w.p τ + (baseOf Z c w j).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have hinj := _root_.GlobalTheory.ExportSeries.HarmInj.harm_inj _ _ _ _ (baseOf Z c w j).F.BS hB.wt hm
    exact (eq_inv_smul_iff₀ hκ).2
      (IsScaleAt.ioP_eq (Rl := X.R) (B := baseOf Z c w j) (c0 := c0L j) hF hinj hPh (hval _) hFe).symm
  · rintro ⟨F, hF0, rfl⟩
    refine ⟨Submodule.smul_mem _ _ (hval _), ?_⟩
    rw [map_smul, hF F, inv_smul_smul₀ hκ]
    exact Submodule.subset_span ⟨F, hF0, rfl⟩
end

