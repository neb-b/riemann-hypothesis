module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartQuot

open GlobalTheory.FinPl GlobalTheory.FinPlLoc ValuativeRel

variable {D : D7}

theorem chrEq_div {a c : (AE D)ˣ →* Circle} {α γ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a α) (hc : ChrEq c γ) :
    ChrEq (a * c⁻¹) (α * γ⁻¹) := by
  refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
  · show ((a x * (c x)⁻¹ : Circle) : ℂ) = ((α.locK P k * (γ.locK P k)⁻¹ : ℂˣ) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx,
      Units.val_mul, Units.val_inv_eq_inv_val]

theorem quot_triv {a c : (AE D)ˣ →* Circle} {α γ ξ : Formalism.L2.Host.HChar D.host.E} (ha : ChrEq a (α * ξ)) (hc : ChrEq c (γ * ξ))
    (hα : α.TrivOn D.host.F) (hγ : γ.TrivOn D.host.F) (b : (AF D.host.F)ˣ) : (a * c⁻¹) (idF D b) = 1 := by
  have h := chrEq_div ha hc
  rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right] at h
  exact GlobalTheory.GridWeil.triv_base h (hα.mul hγ.inv) b

theorem eq_of_finM {V : HSp D} {n : ℕ} (hn : V.rank = n) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : finM V hn g = finM V hn g') : g = g' := by
  subst hn
  have e0 : ∀ g : GA D V, finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := fun g => by simp [finM]
  rw [e0, e0] at h
  apply mt_inj
  ext i j
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = infPart D (Formalism.L2.Theta.mt V g' i j) := by
    have a : infHom V g = infHom V g' := (show infHom V g = 1 from hg).trans (show infHom V g' = 1 from hg').symm
    exact congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => z.1 i j) a
  have h2 : finPart D (Formalism.L2.Theta.mt V g i j) = finPart D (Formalism.L2.Theta.mt V g' i j) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (congrFun (congrFun h i) j)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, h1, sub_self]
  · intro w
    rw [RingHom.map_sub]
    unfold GlobalTheory.FinPl.compAt
    rw [RingHom.comp_apply, RingHom.comp_apply, h2, sub_self]

section Pt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem sum_parts : infPart D (p.e + cA D p.e) = 0 ∧
    ∀ w, compAt D w (p.e + cA D p.e) = if w = p.v then 1 else 0 := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, he⟩ := p.above
  rw [he]
  change infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧
    ∀ w, compAt D w (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
  refine ⟨infPart_pair _ _, fun w => ?_⟩
  rw [compAt_pair]
  split_ifs with hw
  · rw [hw, h1]; rfl
  · rw [h0 w hw, TensorProduct.zero_tmul]

theorem idele_off {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 0) (a : kˣ) :
    φ (p.idele a : AE D) = 1 ∧ φ (cA D (p.idele a : AE D)) = 1 := by
  have e1 := p.split.1
  have e2 := p.split.2.1
  have e3 : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, e1]
  have f1 : φ p.e = 0 := by
    have : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, e1, e2, add_zero]
    rw [this, map_mul, h, mul_zero]
  have f2 : φ (cA D p.e) = 0 := by
    rw [map_add (f := _), f1, zero_add] at h; exact h
  have s : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
  rw [p.idele_val, s]
  simp only [map_add (f := _), map_sub, map_mul, map_one, f1, f2]
  simp

theorem idele_on {R : Type} [CommRing R] (φ : AE D →+* R) (h : φ (p.e + cA D p.e) = 1) (a : kˣ) (δ : AE D)
    (hδ : cA D δ * δ = 1) (ha : p.pr δ = a) :
    φ (p.idele a : AE D) = φ δ * φ (cA D (p.idele a : AE D)) := by
  have s : p.sec a = p.e * δ := by rw [← ha, p.sec_pr]
  rw [p.idele_val, s]
  have h2 := congrArg φ hδ
  simp only [map_add (f := _), map_sub, map_mul, map_one] at h h2 ⊢
  linear_combination (φ δ - 1) * h - φ (cA D p.e) * h2

end Pt

theorem det_sub_one_mem {V : HSp D} {I : Ideal (AE D)} {h : GA D V} (hh : h ∈ congGrp V I) :
    (Formalism.L2.Theta.mt V h).det - 1 ∈ I := by
  rw [mem_congGrp] at hh
  rw [← Ideal.Quotient.eq, map_one, RingHom.map_det]
  have : (Ideal.Quotient.mk I).mapMatrix (Formalism.L2.Theta.mt V h) = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact hh i j
  rw [this, map_one, Matrix.det_one]


set_option maxHeartbeats 1000000 in
theorem isDetRoot_prod {ι : Type} [Fintype ι] {k : ι → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (p : ∀ i, SplitPt D (k i))
    (hp : Function.Injective fun i => (p i).v) {V : HSp D} {h : GA D V} (hh : h ∈ grpAt V fun w => ∃ i, (p i).v = w)
    (d : ∀ i, (k i)ˣ) (hd : ∀ i, (p i).pr (Formalism.L2.Theta.mt V h).det = d i) :
    IsDetRoot V h (∏ i, (p i).idele (d i)) := by
  have hδ := det_sub_one_mem hh
  have hn := Formalism.L2.Theta.det_conj_mul V h
  show _ = (Formalism.L2.Theta.mt V h).det * cA D _
  have off : ∀ {R : Type} [CommRing R] (φ : AE D →+* R), (∀ i, φ ((p i).e + cA D (p i).e) = 0) →
      φ ((Formalism.L2.Theta.mt V h).det - 1) = 0 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ h1 h2
    rw [map_sub, map_one, sub_eq_zero] at h2
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod, h2,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).1,
      Finset.prod_eq_one fun i _ => (idele_off (p i) φ (h1 i) (d i)).2, mul_one, sub_self]
  have on : ∀ {R : Type} [CommRing R] (φ : AE D →+* R) (i : ι), (∀ j, j ≠ i → φ ((p j).e + cA D (p j).e) = 0) →
      φ ((p i).e + cA D (p i).e) = 1 →
      φ (((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D) - (Formalism.L2.Theta.mt V h).det * cA D ((∏ i, (p i).idele (d i) : (AE D)ˣ) : AE D)) = 0 := by
    intro R _ φ i o h1
    rw [Units.coe_prod, map_sub, map_mul, map_prod, map_prod, map_prod,
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).1) (fun h => absurd (Finset.mem_univ i) h),
      Finset.prod_eq_single i (fun j _ hj => (idele_off (p j) _ (o j hj) (d j)).2) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
    exact idele_on (p i) _ h1 _ _ hn (hd i)
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · exact off (infPart D) (fun i => (sum_parts (p i)).1) (infPart_of_idAt hδ)
  · intro w
    by_cases hw : ∃ i, (p i).v = w
    · obtain ⟨i, rfl⟩ := hw
      refine on (compAt D (p i).v) i (fun j hj => ?_) ?_
      · rw [(sum_parts (p j)).2, if_neg fun e => hj (hp e).symm]
      · rw [(sum_parts (p i)).2, if_pos rfl]
    · refine off (compAt D w) (fun i => ?_) (compAt_of_idAt hδ hw)
      rw [(sum_parts (p i)).2, if_neg fun e => hw ⟨i, e.symm⟩]

theorem exists_unit_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (g : GL (Y ⊕ Fin 0) k)
    (hg : g ∈ GlobalTheory.SplitWeil.KO k (Y ⊕ Fin 0)) :
    ∃ d : kˣ, valuation k (d : k) = 1 ∧ (F.β * g.val.toBlocks₁₁ * F.γ).det = d := by
  refine ⟨Matrix.GeneralLinearGroup.det g, ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hg
    have e : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀) : kˣ) : k) =
        algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g₀ : 𝒪[k]ˣ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
      rfl
    rw [e]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  · rw [Matrix.det_conj_of_mul_eq_one F.βγ F.γβ, Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.det_submatrix_equiv_self (Equiv.sumEmpty Y (Fin 0)).symm]
    rfl

theorem chr_eq_of_root {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g : GA D V} {x x' : (AE D)ˣ}
    (h : IsDetRoot V g x) (h' : IsDetRoot V g x') : χ x = χ x' := by
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g _ _ h h'
  rw [ha, map_mul, hF, mul_one]

theorem chr_eq_of_root_mul {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) {V : HSp D} {g h : GA D V} {x y z : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot V h y) (h1 : χ y = 1) (hz : IsDetRoot V (g * h) z) : χ z = χ x := by
  rw [chr_eq_of_root hF hz ((GlobalTheory.Member.isDetRoot_laws D V).2.2.2 _ _ _ _ hx hy), map_mul, h1, mul_one]

theorem eq_on_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {c c' : (AE D)ˣ →* Circle} {η η' δ : kˣ →* ℂˣ} (h : (ofSplit p).IsComp c⁻¹ (η * δ)) (h' : (ofSplit p).IsComp c'⁻¹ (η' * δ))
    (hη : GlobalTheory.SplitWeil.IsUnram η) (hη' : GlobalTheory.SplitWeil.IsUnram η') (d : kˣ) (hd : valuation k (d : k) = 1) :
    c (p.idele d) = c' (p.idele d) := by
  have e : (p.idele d : AE D) = (ofSplit p).ι d + (1 - (ofSplit p).e) := by
    rw [p.idele_val, add_comm]; rfl
  have a := h d _ e
  have a' := h' d _ e
  rw [MonoidHom.mul_apply, hη d hd] at a
  rw [MonoidHom.mul_apply, hη' d hd, a] at a'
  have := Circle.ext a'
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply] at this
  exact inv_injective this

theorem det_cast (n n' : ℕ) (e : n = n') (h : GA D (D.sp.X n')) :
    (Formalism.L2.Theta.mt _ (e ▸ h : GA D (D.sp.X n))).det = (Formalism.L2.Theta.mt _ h).det := by
  subst e; rfl


end GlobalTheory.ChartQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChainTw


open GlobalTheory.LFun in
theorem dv_center_of_isSplit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (a t : ℕ) :
    dv E a (a + t) v ((t : ℂ) / 2) =
      (∏ n ∈ Finset.Ioc t (a + t), (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ n)⁻¹))⁻¹ := by
  have hI : Finset.Icc (t + 1) (t + a) = Finset.Ioc t (a + t) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have he : etaU E v = 1 := by unfold etaU; exact if_pos hv
  rw [dv_center, hI, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [locL, etaFam_of_unram (isUnram_of_isSplit h2 hv), he, one_pow, eulerFac_singleton, Units.val_one, one_mul,
    npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem dSfun_twist_restore : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ a : ℕ, GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) ≠ 0 ∧ GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ((D.R.t : ℂ) / 2) = GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) * ((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ) := by
  intro D c w hw a
  classical
  obtain ⟨hS, hQS₀, hinj, hsplit, -⟩ := GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients D c w hw
  have ht : 0 < ((D.R.t : ℂ) / 2).re := by
    have h3 := D.R.three_m_lt_t
    have h1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 1 ≤ D.R.t)
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set s : ℂ := (D.R.t : ℂ) / 2 with hs_def
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + D.R.t) v s with hf
  set Qv : Finset (HeightOneSpectrum (𝓞 D.host.F)) := w.Q.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hQv
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ w.S₀}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv w.S₀ a (a + D.R.t) ht).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ht).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Qv : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Qv f)
  have hmem : ∀ v, v ∈ Qv ↔ ∃ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := fun v => by simp [hQv]
  have hsplitf : Set.mulIndicator {v | v ∉ w.S₀} f =
      Set.mulIndicator {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Qv : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe]
    by_cases hq : v ∈ Qv
    · obtain ⟨PP, hPP, rfl⟩ := (hmem _).1 hq
      have hc : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := (hS _).2 (Or.inr ⟨PP, hPP, rfl⟩)
      simp [hQS₀ PP hPP, hc, hq]
    · by_cases h0' : v ∈ w.S₀
      · have hc : v ∈ c.S := (hS _).2 (Or.inl h0')
        simp [h0', hc, hq]
      · have hc : v ∉ c.S := fun hc => ((hS _).1 hc).elim h0' fun hx => hq ((hmem _).2 hx)
        simp [h0', hc, hq]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s =
      GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) s * ∏ v ∈ Qv, f v :=
    h0.unique (h1.mul h2)
  have hloc : ∀ PP ∈ w.Q, f ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) = ((zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ)⁻¹ := by
    intro PP hPP
    obtain ⟨hsp, hN, -⟩ := hsplit PP hPP
    show GlobalTheory.LFun.dv D.host.E a (a + D.R.t) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((D.R.t : ℂ) / 2) = _
    rw [dv_center_of_isSplit D.sp.cm.deg2 hsp, hN, zinv]
    push_cast
    rfl
  have hprod : ∏ v ∈ Qv, f v = (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ)⁻¹ := by
    rw [hQv, Finset.prod_image (fun x hx y hy h => hinj hx hy h), Finset.prod_congr rfl hloc,
      Finset.prod_inv_distrib]
    push_cast
    rfl
  have hne : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s ≠ 0 := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ ht
  rw [hprod] at key
  have hZ : (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ) ≠ 0 := by
    intro h0
    apply hne
    rw [key, h0, _root_.inv_zero, mul_zero]
  refine ⟨hne, ?_⟩
  rw [key, mul_assoc, inv_mul_cancel₀ hZ, mul_one]

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelSection

theorem fock_mem_degenerate : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) := by
  intro D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp a ha g
    exact GlobalTheory.StdUnn.SiegelLaw.value_zero_parabolic D n V ψ χ θ μ ω hω Φ p hp a ha g
  · exact _root_.GlobalTheory.StdUnn.weilSch_apply_zero_continuous D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω Φ
  · have hfin := _root_.GlobalTheory.StdUnn.KFin.fock_kfinite D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
    let L : schwartzA θ V.rank n →ₗ[ℂ] (G D n → ℂ) :=
      { toFun := fun Ψ g => (ω g Ψ).1 0
        map_add' := fun Ψ₁ Ψ₂ => by funext g; simp
        map_smul' := fun c Ψ => by funext g; simp }
    rw [isKFinite_iff]
    refine ⟨(Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}).map L, inferInstance, ?_⟩
    intro k hk
    have e : (fun g : G D n => (ω (g * k) Φ).1 0) = L (ω k Φ) := by
      funext g; simp [L, map_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.StdUnn.SiegelSection
end

