module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.NrmLCharpoly
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbTest
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem cmbTest : CmbTest := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  have := A.ha
  have := A.hb
  have : BorelSpace (G a) := ⟨rfl⟩
  have : BorelSpace (G b) := ⟨rfl⟩
  obtain ⟨ca, hca⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 a
  obtain ⟨cb, hcb⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 b
  set c₀ : ℝ := max 0 (max ca cb) with hc₀
  have hc₀0 : 0 ≤ c₀ := le_max_left _ _
  refine ⟨2 * Fintype.card (InfinitePlace E) * c₀ + 1, by positivity, ?_⟩
  intro φ T e₁ e₂ C R hφ hreg hR hC
  have hVC := (lefL E a b l₁ l₂ D A).1
  obtain ⟨hfix, -, hposition⟩ := positionTest E a b S Z L hZ
  have h₁ := (hposition φ hφ).2 T e₁
  have h₂ := (hposition L.ln hfix).2 T e₂
  have hReg : ∃ w ∈ S, IsSplitAt w ∧ ∀ y z, intersection_update_fsHerm_neg_one Z T φ e₁ w y ≠ 0 → intersection_update_fsHerm_neg_one Z T L.ln e₂ w z ≠ 0 →
      ((y * z).1.val.charpoly * (y * z).2.val.charpoly).Separable := by
    obtain ⟨w, hwZ, hw⟩ := hreg
    obtain ⟨hwS, hsp⟩ := hZ w hwZ
    refine ⟨w, hwS, hsp, fun y z hy hz => ?_⟩
    rw [intersection_update_fsHerm_neg_one, if_pos hwZ] at hy hz
    have hzm : z ∈ (L.L₁ w).prod (L.L₂ w) := by
      by_contra hn
      exact hz (Set.indicator_of_notMem hn _)
    have hne : φ w (y * z) ≠ 0 := by
      rw [((hφ w hwZ).2 z hzm y).2]
      exact hy
    have := hw _ hne
    simpa only [nrmL, if_pos hsp] using this
  obtain ⟨hr₁, hr₂⟩ := regS E a b S u₁ u₂ hu₁ hu₂ _ _ h₁ h₂ hReg
  obtain ⟨-, hFC⟩ := BlockFiniteConvolution.finConv' E A.blk S hS
  obtain ⟨hcs, ⟨U, hUo, hU⟩, -⟩ := hFC _ _ h₁ h₂
  have term : ∀ t : PT A.blk, t.Ok → t.ψ = rt u₁ u₂ (A.fx S L T φ e₁ e₂) → t.T ≤ R → t.r ≤ R →
      D4.IsTest2J (trM t.Φ A.tw) ((2 * Fintype.card (InfinitePlace E) * c₀ + 1) * (1 + R)) := by
    intro t ht hψ hT hr
    set γ : Hf E a b := (ratF E a u₁, ratF E b u₂) with hγ
    set Ψ : Hf E a b → ℂ := fun h => A.blk.vol⁻¹ * finFn S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂) (h * γ⁻¹) with hΨ
    have hΨeq : ∀ h, ∑ x, ∑ y, t.ψ x y h * (1 : Matrix Unit Unit ℂ) y x = Ψ h := by
      intro h
      rw [hψ]
      simp [PositivityTheory.Rg.BcB.F.rt, Ar.fx, Ar.ff, hΨ, hγ]
    have hT1 : 0 ≤ 1 + t.T := by linarith [ht.T]
    have hR0 : 0 ≤ c₀ * (1 + t.T) := mul_nonneg hc₀0 hT1
    have hfa : ∀ v, Continuous (phiOf (A.blk.Ma v) (Tl l₁ v) (t.ka v)) ∧ VeryCusp (phiOf (A.blk.Ma v) (Tl l₁ v) (t.ka v)) ∧
        ∀ y, phiOf (A.blk.Ma v) (Tl l₁ v) (t.ka v) y ≠ 0 → lg y.val ≤ c₀ * (1 + t.T) := fun v =>
      ⟨Reg.phiOf_cont _ (ht.ka v), hVC.1 v _ _ _ (ht.ka v), fun y hy =>
        (Reg.phiOf_lg _ ca t.T ((hca A.blk.μa (A.blk.Ma v)).2 _ _ t.T ht.T (ht.ka v)) y hy).trans
          (mul_le_mul_of_nonneg_right ((le_max_left ca cb).trans (le_max_right _ _)) hT1)⟩
    have hfb : ∀ v, Continuous (phiOf (A.blk.Mb v) (Tl l₂ v) (t.kb v)) ∧ VeryCusp (phiOf (A.blk.Mb v) (Tl l₂ v) (t.kb v)) ∧
        ∀ y, phiOf (A.blk.Mb v) (Tl l₂ v) (t.kb v) y ≠ 0 → lg y.val ≤ c₀ * (1 + t.T) := fun v =>
      ⟨Reg.phiOf_cont _ (ht.kb v), hVC.2 v _ _ _ (ht.kb v), fun y hy =>
        (Reg.phiOf_lg _ cb t.T ((hcb A.blk.μb (A.blk.Mb v)).2 _ _ t.T ht.T (ht.kb v)) y hy).trans
          (mul_le_mul_of_nonneg_right ((le_max_right ca cb).trans (le_max_right _ _)) hT1)⟩
    have hsz : ∀ h, Ψ h ≠ 0 → logSize (finGL E a h.1) ≤ t.r ∧ logSize (finGL E b h.2) ≤ t.r := by
      intro h hh
      rw [← hΨeq] at hh
      obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact ht.size x y h (left_ne_zero_of_mul hy)
    have hfin : ∀ g, Ψ g ≠ 0 → finFn S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂) (g * γ⁻¹) ≠ 0 :=
      fun g hg => right_ne_zero_of_mul hg
    set U' : Subgroup (Hf E a b) := U ⊓ U.comap (MulAut.conj γ).toMonoidHom with hU'
    have hU'o : IsOpen (U' : Set (Hf E a b)) := by
      rw [hU', Subgroup.coe_inf, Subgroup.coe_comap]
      exact hUo.inter (hUo.preimage (by
        show Continuous fun x : Hf E a b => γ * x * γ⁻¹
        fun_prop))
    have hΨU : ∀ u ∈ U', ∀ h, Ψ (u * h) = Ψ h ∧ Ψ (h * u) = Ψ h := by
      intro u hu h
      have hc : γ * u * γ⁻¹ ∈ U := hu.2
      have e : h * u * γ⁻¹ = h * γ⁻¹ * (γ * u * γ⁻¹) := by group
      refine ⟨?_, ?_⟩
      · show A.blk.vol⁻¹ * finFn S _ _ (u * h * γ⁻¹) = A.blk.vol⁻¹ * finFn S _ _ (h * γ⁻¹)
        rw [mul_assoc u h, (hU u hu.1 _).1]
      · show A.blk.vol⁻¹ * finFn S _ _ (h * u * γ⁻¹) = A.blk.vol⁻¹ * finFn S _ _ (h * γ⁻¹)
        rw [e, (hU _ hc _).2]
    have hcsΨ : HasCompactSupport Ψ :=
      (hcs.comp_homeomorph (Homeomorph.mulRight γ⁻¹)).mul_left (f := fun _ => A.blk.vol⁻¹)
    have key := PositivityTheory.Rg.BcB.CG.test2J E a b (fun v => phiOf (A.blk.Ma v) (Tl l₁ v) (t.ka v))
      (fun v => phiOf (A.blk.Mb v) (Tl l₂ v) (t.kb v)) Ψ (c₀ * (1 + t.T)) t.r U' hR0 hfa hfb hcsΨ hU'o hΨU hsz
      (fun d x h₂ hne => hr₁ d x h₂ (hfin _ hne)) (fun d x h₁ hne => hr₂ d x h₁ (hfin _ hne))
    have hfun : trM t.Φ A.tw = fun g =>
        (∏ v, phiOf (A.blk.Ma v) (Tl l₁ v) (t.ka v) (gInf v g.1)) * (∏ v, phiOf (A.blk.Mb v) (Tl l₂ v) (t.kb v) (gInf v g.2)) *
          Ψ (hFin g) := by
      funext g
      rw [PT.Φ, Ar.tw, PositivityTheory.Rg.BcB.CG.tensTr, hΨeq]
    rw [hfun]
    refine PositivityTheory.Rg.BcB.CG.isTest2J_mono key ?_
    have hcard : 0 ≤ 2 * (Fintype.card (InfinitePlace E) : ℝ) * c₀ := by positivity
    have h1 : 2 * (Fintype.card (InfinitePlace E) : ℝ) * (c₀ * (1 + t.T)) ≤
        2 * (Fintype.card (InfinitePlace E) : ℝ) * c₀ * (1 + R) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hcard
    nlinarith
  refine ⟨fun j hj => ?_, ?_⟩
  · obtain ⟨ho, hψ, hT, hr⟩ := hC j hj
    exact term _ ho hψ hT hr
  · rw [Cmb.Φ, Growth.trM_sum]
    exact isTest2J_sum _ fun j hj => isTest2J_smul _ (by
      obtain ⟨ho, hψ, hT, hr⟩ := hC j hj
      exact term _ ho hψ hT hr)

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.FinSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem position_off {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z)
    {w i : Pl E} (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (hi : i ≠ w) :
    intersection_update_fsHerm_neg_one Z {w} L.ln e i = intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one) i := by
  simp [intersection_update_fsHerm_neg_one, hi]

private theorem position_at {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z)
    {w : Pl E} (hZ : w ∉ Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) :
    intersection_update_fsHerm_neg_one Z {w} L.ln e w = fn2 a b w (e w) := by
  simp [intersection_update_fsHerm_neg_one, hZ]

private theorem position_cof {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z) :
    ∀ᶠ i in cofinite, intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one) i = ((K2 a b i : Subgroup _) : Set _).indicator 1 := by
  filter_upwards [Z.finite_toSet.compl_mem_cofinite] with i hi
  have hi' : i ∉ Z := hi
  simp [intersection_update_fsHerm_neg_one, hi']

private theorem fin_split {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (S : Set (Pl E)) {Z : Finset (Pl E)}
    (L : Lv a b Z) {w : Pl E} (hw : w ∈ S) (hZ : w ∉ Z) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (y : Gf E a b) :
    finFn S (intersection_update_fsHerm_neg_one Z {w} L.ln e₁) (intersection_update_fsHerm_neg_one Z {w} L.ln e₂) y =
      (fn2 a b w (e₁ w) (atW w y) * if IsSplitAt w then fn2 a b w (e₂ w) (atW w (thP E a b y)) else 1) *
        ∏ᶠ i ∈ S \ ↑({w} : Finset (Pl E)), Fm.fac (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) y i := by
  rw [Fm.finFn_eq, Fm.fp_split S {w} (by simpa using hw) _ _ (fun i hi => ?_)
    (Fm.fac_fin S (position_cof L) (position_cof L) y)]
  · congr 1
    simp [Fm.fac, position_at L hZ]
  · have hi' : i ≠ w := by simpa using hi
    simp only [Fm.fac, position_off L _ hi']

private theorem ex_add {ι G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) (x y : Ex ι) (h : G) :
    (x.add y).fn K g h = x.fn K g h + y.fn K g h := rfl

private theorem ex_smul {ι G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) (c : ℂ) (x : Ex ι) (h : G) :
    (Ex.smul c x).fn K g h = c * x.fn K g h := rfl

theorem hkLin : HkLin := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ' w hw hZ x y z c
  have key : ∀ (e₁ e₂ : Ex (Fin (a + 1) × Fin (b + 1))) (u v : Unit) (h : Hf E a b), A.hk S L {w} (fun _ => e₁) (fun _ => e₂) u v h =
      A.blk.vol⁻¹ * ((fn2 a b w e₁ (atW w h) * if IsSplitAt w then fn2 a b w e₂ (atW w (thP E a b h)) else 1) *
        ∏ᶠ i ∈ S \ ↑({w} : Finset (Pl E)), Fm.fac (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) h i) := by
    intro e₁ e₂ u v h
    exact congrArg _ (fin_split S L hw hZ _ _ h)
  refine ⟨?_, ?_, fun hs => ⟨?_, ?_⟩, fun hs => ?_⟩ <;> funext u v h
  · simp only [Matrix.add_apply, Pi.add_apply, key, fn2, ex_add]; ring
  · simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, key, fn2, ex_smul]; ring
  · simp only [Matrix.add_apply, Pi.add_apply, key, fn2, ex_add, if_pos hs]; ring
  · simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, key, fn2, ex_smul, if_pos hs]; ring
  · simp only [key, if_neg hs]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_in {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∈ Z) :
    intersection_update_fsHerm_neg_one Z T φ e w = φ w := by simp [intersection_update_fsHerm_neg_one, h]

private theorem slot_eq_fn2_of_not_mem_of_mem {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∉ Z) (h' : w ∈ T) :
    intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w) := by simp [intersection_update_fsHerm_neg_one, h, h']

private theorem position_out {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∉ Z) (h' : w ∉ T) :
    intersection_update_fsHerm_neg_one Z T φ e w = (K2 a b w : Set _).indicator 1 := by simp [intersection_update_fsHerm_neg_one, h, h']

private theorem heckeFunction_mul (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := by
  funext m
  simp only [fn2, Ex.fn, PositivityTheory.Rg.BcN.F2.mconv]

private theorem heckeFunction_one (w : Pl E) : fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem heckeFunction_isHecke (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) : IsHecke (K2 a b w) (fn2 a b w e) :=
  Asm.exHecke2 E a b w e

private theorem ind_hecke (w : Pl E) : IsHecke (K2 a b w) ((K2 a b w : Set _).indicator 1) := heckeFunction_isHecke w .one

private theorem ind_ind (w : Pl E) : PositivityTheory.Rg.BcN.F2.mconv ((K2 a b w : Set _).indicator 1) ((K2 a b w : Set _).indicator 1) =
    ((K2 a b w : Set _).indicator 1 : GLw a w × GLw b w → ℂ) :=
  ((locAlg E a b ∅ ⟨fun w => KGL w (n := a), fun w => KGL w (n := b), fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩ w).2.2.2.2 _ (ind_hecke w)).1

variable {Z : Finset (Pl E)} (L : Lv a b Z)

private theorem position_hecke {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    IsHecke ((L.L₁ w).prod (L.L₂ w)) (intersection_update_fsHerm_neg_one Z T φ e w) := by
  by_cases hZ : w ∈ Z
  · rw [position_in hZ]; exact hφ w hZ
  · obtain ⟨h₁, h₂⟩ := L.off w hZ
    rw [h₁, h₂]
    by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT]; exact heckeFunction_isHecke w _
    · rw [position_out hZ hT]; exact ind_hecke w

private theorem ln_fix : L.Fix L.ln := fun w _ => (locAlg E a b Z L w).1

private theorem position_ln {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T φ e w) (L.ln w) = intersection_update_fsHerm_neg_one Z T φ e w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (position_hecke L hφ e w)).1

private theorem ln_position {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (L.ln w) (intersection_update_fsHerm_neg_one Z T φ e w) = intersection_update_fsHerm_neg_one Z T φ e w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (position_hecke L hφ e w)).2

private theorem ln_ln (w : Pl E) : PositivityTheory.Rg.BcN.F2.mconv (L.ln w) (L.ln w) = L.ln w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (locAlg E a b Z L w).1).1

private theorem position_one (T : Finset (Pl E)) : intersection_update_fsHerm_neg_one Z T L.ln (fun _ => .one) = L.ln := by
  funext w
  by_cases hZ : w ∈ Z
  · exact position_in hZ
  · have h := (locAlg E a b Z L w).2.2.1 hZ
    by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT, heckeFunction_one, h]
    · rw [position_out hZ hT, h]

private theorem position_empty (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : intersection_update_fsHerm_neg_one Z ∅ L.ln e = L.ln := by
  funext w
  by_cases hZ : w ∈ Z
  · exact position_in hZ
  · rw [position_out hZ (Finset.notMem_empty w), (locAlg E a b Z L w).2.2.1 hZ]

private theorem position_mul {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T φ e w) (intersection_update_fsHerm_neg_one Z T L.ln e' w) = intersection_update_fsHerm_neg_one Z T φ (fun w => (e w).mul (e' w)) w := by
  by_cases hZ : w ∈ Z
  · rw [position_in hZ, position_in hZ, position_in hZ]
    exact ((locAlg E a b Z L w).2.2.2.1 _ (hφ w hZ)).1
  · by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ hT, heckeFunction_mul]
    · rw [position_out hZ hT, position_out hZ hT, position_out hZ hT, ind_ind]

private theorem position_insert {T : Finset (Pl E)} {w : Pl E} (hw : w ∉ T)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (x : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z {w} L.ln e x) (intersection_update_fsHerm_neg_one Z T L.ln e x) = intersection_update_fsHerm_neg_one Z (insert w T) L.ln e x := by
  by_cases hZ : x ∈ Z
  · rw [position_in hZ, position_in hZ, position_in hZ]
    exact ln_ln L x
  · by_cases hx : x = w
    · subst hx
      rw [slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_singleton_self x), position_out hZ hw, slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_insert_self x T)]
      exact ((locAlg E a b Z L x).2.2.2.2 _ (heckeFunction_isHecke x _)).1
    · by_cases hT : x ∈ T
      · rw [position_out hZ (by simpa using hx), slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_insert_of_mem hT)]
        exact ((locAlg E a b Z L x).2.2.2.2 _ (heckeFunction_isHecke x _)).2.1
      · rw [position_out hZ (by simpa using hx), position_out hZ hT, position_out hZ (by simp [hx, hT]), ind_ind]

end

theorem hkMul : HkMul := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ
  have hF := (ffAlg E a b l₁ l₂ D A S hS).2
  have hT := positionTest E a b S Z L hZ
  have hln : IsTestP L.ln := hT.2.1
  have hfix : L.Fix L.ln := ln_fix L
  have hs : ∀ T φ e, L.Fix φ → IsTestP (intersection_update_fsHerm_neg_one Z T φ e) := fun T φ e h => (hT.2.2 φ h).2 T e
  have hsl : ∀ T e, IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) := fun T e => hs T L.ln e hfix
  refine ⟨(hF _ _ hln hln).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show mulF A.ν (A.ff S L.ln L.ln) (A.ff S L.ln L.ln) = A.ff S L.ln L.ln
    rw [(hF _ _ hln hln).2.2.2.2 _ _ hln hln]
    exact congrArg₂ (A.ff S) (funext (ln_ln L)) (funext (ln_ln L))
  · show adjF (A.ff S L.ln L.ln) = A.ff S L.ln L.ln
    rw [(hF _ _ hln hln).2.1]
    have h : (fun w => lfStar (L.ln w)) = L.ln := funext fun w => (locAlg E a b Z L w).2.1
    rw [h]
  · intro T
    show A.ff S (intersection_update_fsHerm_neg_one Z T L.ln fun _ => .one) (intersection_update_fsHerm_neg_one Z T L.ln fun _ => .one) = A.ff S L.ln L.ln
    rw [position_one L T]
  · intro e₁ e₂
    show A.ff S (intersection_update_fsHerm_neg_one Z ∅ L.ln e₁) (intersection_update_fsHerm_neg_one Z ∅ L.ln e₂) = A.ff S L.ln L.ln
    rw [position_empty L, position_empty L]
  · intro T φ e₁ e₂ hφ
    have t₁ := hs T φ e₁ hφ
    have t₂ := hsl T e₂
    refine ⟨(hF _ _ t₁ t₂).1, ?_, fun e₁' e₂' => ?_⟩
    · show mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) (A.ff S L.ln L.ln) =
        A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)
      rw [(hF _ _ t₁ t₂).2.2.2.2 _ _ hln hln]
      exact congrArg₂ (A.ff S) (funext (position_ln L hφ e₁)) (funext (position_ln L hfix e₂))
    · show mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))
          (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁') (intersection_update_fsHerm_neg_one Z T L.ln e₂')) =
        A.ff S (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).mul (e₁' w)) (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).mul (e₂' w))
      rw [(hF _ _ t₁ t₂).2.2.2.2 _ _ (hsl T e₁') (hsl T e₂')]
      exact congrArg₂ (A.ff S) (funext (position_mul L hφ e₁ e₁')) (funext (position_mul L hfix e₂ e₂'))
  · intro T e₁ e₂
    have t₁ := hsl T e₁
    have t₂ := hsl T e₂
    refine ⟨(hF _ _ t₁ t₂).1, ?_⟩
    show mulF A.ν (A.ff S L.ln L.ln) (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) =
      A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)
    rw [(hF _ _ hln hln).2.2.2.2 _ _ t₁ t₂]
    exact congrArg₂ (A.ff S) (funext (ln_position L hfix e₁)) (funext (ln_position L hfix e₂))
  · intro T w e₁ e₂ hw
    show A.ff S (intersection_update_fsHerm_neg_one Z (insert w T) L.ln e₁) (intersection_update_fsHerm_neg_one Z (insert w T) L.ln e₂) =
      mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln e₁) (intersection_update_fsHerm_neg_one Z {w} L.ln e₂))
        (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))
    rw [(hF _ _ (hsl _ e₁) (hsl _ e₂)).2.2.2.2 _ _ (hsl T e₁) (hsl T e₂)]
    exact (congrArg₂ (A.ff S) (funext (position_insert L hw e₁)) (funext (position_insert L hw e₂))).symm

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HkComm
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_sph (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∉ Z) : IsHecke (K2 a b w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_neg hw]
  split_ifs
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

private theorem position_Z (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∈ Z) : intersection_update_fsHerm_neg_one Z T L.ln e w = L.ln w := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_pos hw]

private theorem position_comm (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (intersection_update_fsHerm_neg_one Z T' L.ln e' w) =
      PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T' L.ln e' w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) (position_sph Z T' L e' w hw)

private theorem position_comm_star (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) =
      PositivityTheory.Rg.BcN.F2.mconv (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  have hl := UpperTheory.Zero.ConvolutionTheory.EB.locAlg E a b Z L w
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw, hl.2.1]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw)
      ((hl.2.2.2.2 _ (position_sph Z T' L e' w hw)).2.2)

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.hkComm :
    UpperTheory.Zero.ConvolutionTheory.EB.HkComm := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T T' e₁ e₂ e₁' e₂'
  have hst := UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ
  have ht : ∀ (T : Finset (Pl E)) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) :=
    fun T e => (hst.2.2 L.ln hst.1).2 T e
  have hf := (UpperTheory.Zero.ConvolutionTheory.EB.ffAlg E a b l₁ l₂ D A S hS).2
  have h1 := hf _ _ (ht T e₁) (ht T e₂)
  have h2 := hf _ _ (ht T' e₁') (ht T' e₂')
  have hstar := h2.2.1
  refine ⟨?_, ?_⟩
  · show mulF A.ν (A.ff S _ _) (A.ff S _ _) = mulF A.ν (A.ff S _ _) (A.ff S _ _)
    rw [h1.2.2.2.2 _ _ (ht T' e₁') (ht T' e₂'), h2.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm Z T T' L e₁ e₁', position_comm Z T T' L e₂ e₂']
  · show mulF A.ν (A.ff S _ _) (adjF (A.ff S _ _)) = mulF A.ν (adjF (A.ff S _ _)) (A.ff S _ _)
    rw [hstar]
    have hs := hf _ _ h2.2.2.1 h2.2.2.2.1
    rw [h1.2.2.2.2 _ _ h2.2.2.1 h2.2.2.2.1, hs.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm_star Z T T' L e₁ e₁', position_comm_star Z T T' L e₂ e₂']

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

