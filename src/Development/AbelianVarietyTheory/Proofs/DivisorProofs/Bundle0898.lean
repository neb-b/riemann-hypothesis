module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AlgChart

variable (c c' : AlgChart p σ D) {S : Set (CxPts p σ)} {y : CxPts p σ} {f g : CxPts p σ → ℝ}

def levi (f : CxPts p σ → ℝ) (y : CxPts p σ) (ξ : Fin D → ℂ) : ℝ :=
  (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

def dtrans (y : CxPts p σ) (ξ : Fin D → ℂ) : Fin D → ℂ :=
  fun b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (WithLp.toLp 2 ξ) b

variable {c c'}

theorem levi_congr (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S) (h : ∀ z ∈ S, f z = g z)
    (ξ : Fin D → ℂ) : c.levi f y ξ = c.levi g y ξ :=
  congrArg Complex.re (leviV_congr (eventually_of_mem
    ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      congrArg Complex.ofReal (h _ hv.2)) ξ)

theorem levi_add (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y))
    (hg : ContDiffAt ℝ 2 (g ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => f z + g z) y ξ = c.levi f y ξ + c.levi g y ξ :=
  (congrArg Complex.re (flA_leviV_add hf hg ξ)).trans (Complex.add_re _ _)

theorem levi_const_mul (a : ℝ) (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => a * f z) y ξ = a * c.levi f y ξ :=
  (congrArg Complex.re (LocalMaximumSecondDerivative.leviV_ofReal_const_mul a hf ξ)).trans (Complex.re_ofReal_mul _ _)

theorem levi_log_normSq {u : CxPts p σ → ℂ} (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S)
    (hu : DifferentiableOn ℂ (u ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) (h0 : u y ≠ 0)
    (ξ : Fin D → ℂ) : c.levi (fun z => Real.log (‖u z‖ ^ 2)) y ξ = 0 :=
  congrArg Complex.re (flA_leviV_log_normSq (h := u ∘ c.e.symm)
    (eventually_of_mem ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      hu.differentiableAt ((isOpen_over c.e hS).mem_nhds hv))
    (by rwa [Function.comp_apply, c.e.left_inv hy]) ξ)

theorem levi_trans (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source)
    (hf : ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y)) (ξ : Fin D → ℂ) :
    c.levi f y ξ = c'.levi f y (c.dtrans c' y ξ) := by
  have ho := isOpen_over c.e c'.e.open_source
  have hn := ho.mem_nhds (mem_over c.e hy hy')
  have ht : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
    (((contDiffOn_piLp 2).2 fun a => contDiffOn_of_differentiableOn D _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') a)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have e : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hU : ContDiffAt ℝ 2 (fun v => (f (c'.e.symm v) : ℂ)) ((c'.e ∘ c.e.symm) (c.e y)) :=
    e ▸ Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have := flA_leviV_comp hU ht ξ
  rw [e] at this
  refine congrArg Complex.re (Eq.trans (leviV_congr (eventually_of_mem hn fun v hv => ?_) ξ) this)
  simp only [Function.comp_apply, c'.e.left_inv hv.2]

theorem dtrans_ne_zero (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) {ξ : Fin D → ℂ}
    (hξ : ξ ≠ 0) : c.dtrans c' y ξ ≠ 0 := fun h => by
  have hd : transDet c.e c'.e y ≠ 0 := rv_chart c c' hy hy' ▸
    rv_ne_zero _ _ (c.source_subset hy) (c'.source_subset hy')
  have hi := (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  have := LinearMap.ker_eq_bot'.1 hi (WithLp.toLp 2 ξ) (PiLp.ext fun b => congrFun h b)
  exact hξ (congrArg WithLp.ofLp this)

end AlgChart

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)} {y : CxPts p σ}

theorem SmoothOn.contDiffAt_two {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    {c : AlgChart p σ D} (hy : y ∈ c.e.source) (hyS : y ∈ S) :
    ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) :=
  ((h.chart hS c).contDiffAt ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS))).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem levi_eq_of_add_log {f g : CxPts p σ → ℝ} {u : CxPts p σ → ℂ} (hS : IsOpen S)
    (hf : R.SmoothOn S f) (hu : R.HoloOn S u) (h0 : ∀ z ∈ S, u z ≠ 0)
    (h : ∀ z ∈ S, g z = f z + Real.log (‖u z‖ ^ 2)) {c : AlgChart p σ D} (hy : y ∈ c.e.source)
    (hyS : y ∈ S) (ξ : Fin D → ℂ) : c.levi g y ξ = c.levi f y ξ := by
  rw [AlgChart.levi_congr hS hy hyS h, AlgChart.levi_add (hf.contDiffAt_two hS hy hyS)
    ((hu.smoothOn_log hS h0).contDiffAt_two hS hy hyS),
    AlgChart.levi_log_normSq hS hy hyS (hu.chart hS c) (h0 y hyS), add_zero]

end AnRead

namespace Weight

open AnRead

variable {R R' : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B} {ψ : Weight p σ A}
  {c : AlgChart p σ D} {y : CxPts p σ}

theorem IsSmooth.contDiffAt_two (h : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : ContDiffAt ℝ 2 (φ.φ i ∘ c.e.symm) (c.e y) :=
  (h i).contDiffAt_two (isOpen_ptsIn _) hy hi

theorem IsSmooth.levi_frame (h : φ.IsSmooth R) {i j : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) (ξ : Fin D → ℂ) :
    c.levi (φ.φ i) y ξ = c.levi (φ.φ j) y ξ :=
  levi_eq_of_add_log ((isOpen_ptsIn (B.U i)).inter (isOpen_ptsIn (B.U j)))
    ((h j).mono inter_subset_right) (u := gv p σ B i j)
    (holoOn_ev_of_subset _ fun _ => mem_ptsIn_inf.2) (fun _ hz => gv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [φ.trans i j z hz.1 hz.2, sub_add_cancel]) hy ⟨hi, hj⟩ ξ

theorem IsSmooth.strictPos_of_exists (hs : φ.IsSmooth R)
    (h : ∀ y, ∃ (c : AlgChart p σ D) (i : B.ι), y ∈ c.e.source ∧ y ∈ ptsIn p σ (B.U i) ∧
      ∀ ξ, ξ ≠ 0 → 0 < c.levi (φ.φ i) y ξ) : φ.StrictPos R := fun j c' y hy ξ hξ => by
  obtain ⟨c, i, hc, hi, h⟩ := h y
  exact (h _ (AlgChart.dtrans_ne_zero hy.1 hc hξ)).trans_eq ((hs.levi_frame hc hi hy.2 _).trans
    (AlgChart.levi_trans hy.1 hc (hs.contDiffAt_two hc hy.2) ξ).symm)

theorem levi_tens (hψ : ψ.IsSmooth R) (hφ : φ.IsSmooth R) {i : (CechPic.tens A B).ι}
    (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ ((CechPic.tens A B).U i)) (ξ : Fin D → ℂ) :
    c.levi ((ψ.tens φ).φ i) y ξ = c.levi (ψ.φ i.1) y ξ + c.levi (φ.φ i.2) y ξ :=
  AlgChart.levi_add (hψ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).1)
    (hφ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).2) ξ

theorem levi_zpow (hφ : φ.IsSmooth R) (n : ℤ) {j : PUnit → B.ι} (hy : y ∈ c.e.source)
    (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) (ξ : Fin D → ℂ) :
    c.levi ((φ.zpow n).φ j) y ξ = n * c.levi (φ.φ (j PUnit.unit)) y ξ := by
  rw [funext (φ.zpow_φ n j)]
  exact AlgChart.levi_const_mul _ (hφ.contDiffAt_two hy hj) ξ

theorem SemiPos.tens (h' : ψ.SemiPos R) (h : φ.SemiPos R) (hψ : ψ.IsSmooth R)
    (hφ : φ.IsSmooth R) : (ψ.tens φ).SemiPos R := fun i c y hy ξ =>
  (add_nonneg (h' _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).1⟩ ξ)
    (h _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).2⟩ ξ)).trans_eq (levi_tens hψ hφ hy.1 hy.2 ξ).symm

theorem SemiPos.zpow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) {n : ℤ} (hn : 0 ≤ n) :
    (φ.zpow n).SemiPos R := fun j c y hy ξ =>
  (mul_nonneg (Int.cast_nonneg hn) (h _ c y ⟨hy.1, mem_pow_iff.1 hy.2⟩ ξ)).trans_eq
    (levi_zpow hφ n hy.1 (mem_pow_iff.1 hy.2) ξ).symm

theorem SemiPos.pow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) (n : ℕ) : (φ.pow n).SemiPos R :=
  h.zpow hφ (Int.natCast_nonneg n)

theorem semiPos_fs {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ} (hB : B.IsLB)
    (he : ∀ a, e a ∈ R.holSec B) (h : NoCommonZero e) :
    (fs hB e (fun a => (he a).1) h).SemiPos R := fun i c y hy ξ => by
  have ho := isOpen_over (R.chart c).e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hc (a) : ContDiffAt ℂ 2 (e a i ∘ (R.chart c).e.symm) ((R.chart c).e y) :=
    ((contDiffOn_of_differentiableOn D _ _ ho ((he a).2 i c)).contDiffAt
      (ho.mem_nhds (mem_over _ hy.1 hy.2))).of_le (WithTop.coe_le_coe.2 le_top)
  have hs (v) : ∑ j, Complex.normSq ((e ((Fintype.equivFin α).symm j) i ∘ (R.chart c).e.symm) v) =
      ∑ a, ‖e a i ((R.chart c).e.symm v)‖ ^ 2 :=
    Fintype.sum_equiv (Fintype.equivFin α).symm _ _ fun _ => Complex.normSq_eq_norm_sq _
  have := leviV_log_sum_nonneg (fun j => contDiffAt_normSq_comp (hc ((Fintype.equivFin α).symm j)))
    (fun j => logPshAt_normSq (hc _))
    (by rw [hs, (R.chart c).e.left_inv hy.1]; exact h.sum_pos hy.2) ξ
  simp only [hs] at this
  exact this

end Weight

namespace WeightFamily.Reading

variable [SmoothOfRelativeDimension D p] {R : AnRead p σ D} {κ : Type} [Fintype κ] [DecidableEq κ]
  [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] {F : WeightFamily R κ} {B : LB Y}
  {m : Option κ → ℤ} {r : F.Reading B m} {φ : Weight p σ B}

end WeightFamily.Reading

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharacters
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorLie

section Grp
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G]

theorem one_left' (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

theorem mul_left_congr {T T' : Over S} (x y : T ⟶ G) (x' y' : T' ⟶ G) (u : Z ⟶ T.left) (u' : Z ⟶ T'.left)
    (hx : u ≫ x.left = u' ≫ x'.left) (hy : u ≫ y.left = u' ≫ y'.left) :
    u ≫ (x * y).left = u' ≫ (x' * y').left := by
  have hb : u' ≫ T'.hom = u ≫ T.hom := by
    rw [← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]
  let U : Over.mk (u ≫ T.hom) ⟶ T := Over.homMk u rfl
  let U' : Over.mk (u ≫ T.hom) ⟶ T' := Over.homMk u' hb
  have e1 : U ≫ x = U' ≫ x' := Over.OverMorphism.ext hx
  have e2 : U ≫ y = U' ≫ y' := Over.OverMorphism.ext hy
  have : U ≫ (x * y) = U' ≫ (x' * y') := by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]
  exact congrArg (fun k => k.left) this

end Grp

theorem pull_one_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (T.hom ≫ f) ≫ η[G].left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have hm := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at hm
  have hx : x₀ * x₀ = x₀ := Over.OverMorphism.ext hm
  have h1 : x₀ = 1 := by simpa using hx
  have : x₀.left = (Over.mk (T.hom ≫ f)).hom ≫ η[G].left := by rw [h1, one_left']
  exact this

end GlobalTheory.TorLie

open GlobalTheory.TorLie in
theorem GlobalTheory.torus_part_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  intro S G _ _ O _ act hhom h1 hmul hadd k _ x E
  letI := E.addCommGroup
  haveI := E.i_hom
  set Gx := (Over.pullback x).obj G with hGx
  have hGP := isGrpPullback_pullback G x
  obtain ⟨act', ⟨hhom', h1', hmul', hadd'⟩, hact'⟩ :=
    _root_.GlobalTheory.ActPull.exists_act_pull S (Sp k) x G Gx (pullback.fst G.hom x) hGP O act hhom h1 hmul hadd
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action k Gx E O act' hhom' h1' hmul' hadd'
  obtain ⟨U₀, hinj, hone, hU₀mul, hscale, hequi⟩ := _root_.GlobalTheory.splitTorus_tangent_addHom k E.X

  have heq : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt (𝟙 (Sp k))).hom ≫ x := by
    intro l
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w (U₀ l ≫ E.i))
  have hw : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt x).hom := by
    intro l; rw [heq l]; simp [epsPt]
  let U : (E.X →+ k) → (epsPt x ⟶ G) := fun l => Over.homMk _ (hw l)
  have hUl : ∀ l, (U l).left = (U₀ l).left ≫ E.i.left ≫ pullback.fst G.hom x := by
    intro l; simp [U]
  haveI : Mono E.i := E.isKernel.mono_fst_of_mono (IsTerminal.mono_from isTerminalTensorUnit _)
  refine ⟨ρ, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    have hl := congrArg Over.Hom.left h
    rw [hUl, hUl, ← Category.assoc, ← Category.assoc] at hl
    have h2 : (U₀ l ≫ E.i).left = (U₀ l' ≫ E.i).left := by
      apply pullback.hom_ext
      · simpa [Over.comp_left] using hl
      · exact (Over.w (U₀ l ≫ E.i)).trans (Over.w (U₀ l' ≫ E.i)).symm
    exact hinj ((cancel_mono E.i).1 (Over.OverMorphism.ext h2))
  · intro l
    rw [hUl, ← Category.assoc, hone l, ← Category.assoc, ← Over.comp_left, MonObj.one_comp,
      pull_one_left hGP, one_left']
    simp
  · intro l l'
    let x₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l)
    let y₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l')
    have key := hGP.2 (epsPt (𝟙 (Sp k))) (U₀ l ≫ E.i) (U₀ l' ≫ E.i) x₀ y₀ rfl rfl
    rw [← mul_comp, ← hU₀mul] at key
    apply Over.OverMorphism.ext
    have hc := mul_left_congr (U l) (U l') x₀ y₀ (𝟙 _) (𝟙 _) rfl rfl
    simp only [Category.id_comp] at hc
    rw [hc, key, hUl, Over.comp_left, Category.assoc]
  · intro t l
    rw [hUl, hUl, hscale]
    simp [Category.assoc]
  · intro a l
    obtain ⟨τ, hτ, hχ⟩ := hρ a
    have hτl : τ.left ≫ E.i.left = E.i.left ≫ (act' a).left := by
      simpa using congrArg Over.Hom.left hτ
    apply Over.OverMorphism.ext
    have hτU : U₀ l ≫ τ = U₀ (l.comp (ρ a).toAddMonoidHom) := hequi τ (ρ a).toAddMonoidHom (fun χ => hχ χ) l
    rw [Over.comp_left, hUl, hUl, ← hτU, Over.comp_left]
    simp only [Category.assoc, ← hact' a, reassoc_of% hτl]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.ObjModel

namespace GlobalTheory.ToricSumValue

theorem cpow_pos_eq {r : ℝ} (hr : 0 < r) (z : ℂ) : (r : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le]

theorem term_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s) (σ : ℂ) (k : Eˣ) :
    term φ (2 * s) κ σ k = (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) *
      ((modF (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℝ) : ℂ) ^ ((s : ℂ) + σ) := by
  have hpos : ∀ i, 0 < ‖φ i (k : E)‖ := fun i => by simp
  have hN : 0 < ∏ i, ‖φ i (k : E)‖ ^ 2 := Finset.prod_pos fun i _ => pow_pos (hpos i) 2
  rw [modF_princ k, ← prod_normSq hφ k,
    Complex.cpow_add _ _ (by exact_mod_cast (inv_pos.2 hN).ne'), Complex.cpow_natCast]
  have h1 : term φ (2 * s) κ σ k = term φ (2 * s) κ 0 k * ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    unfold term
    rw [← Finset.prod_mul_distrib]
    simp
  have h2 : ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) = (((∏ i, ‖φ i (k : E)‖ ^ 2)⁻¹ : ℝ) : ℂ) ^ σ := by
    rw [cpow_pos_eq (inv_pos.2 hN), Real.log_inv, Real.log_prod (fun i _ => (pow_pos (hpos i) 2).ne')]
    simp only [cpow_pos_eq (hpos _)]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_pow]
    push_cast
    ring
  have h3 := term_mul_inf h k
  have h4 : ∏ i, (φ i k * starRingEnd ℂ (φ i k)) ^ s = (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s := by
    rw [Finset.prod_pow]
    congr 1
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.mul_conj' _
  have h5 : (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * (χ.inf k : ℂ) = 1 := by
    rw [← Units.val_mul, finPart_mul_inf, Units.val_one]
  rw [h4] at h3
  have hN' : (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [h1, h2, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_inv, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hN')]
  linear_combination (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * h3 -
    (term φ (2 * s) κ 0 k * (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s) * h5

def twistFin {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) : (Af E)ˣ →* ℂ where
  toFun y := (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S
  map_one' := by
    have : modF (1 : (Af E)ˣ) = 1 := modF_unit (c := ⊤) (one_mem _)
    simp [this]
  map_mul' y y' := by
    rw [map_mul, modF_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (modF_pos y).le (modF_pos y').le,
      Units.val_mul]
    ring

theorem twistFin_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) (y : (Af E)ˣ) :
    twistFin χ S y = (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S := rfl

theorem hasSum_classes {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s)
    {𝔣 c : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) (hd : 𝔣 ∣ c) (hc : c ≠ ⊥) (hχ : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    {σ T : ℂ} {S : PicO c → ℂ}
    (hS : ∀ q, HasSum (fun x : modUnits (lattice c q.out) => term φ (2 * s) κ σ x.1.out) (S q))
    (hT : HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ,
      (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} => twistFin χ (s + σ) z.1.out) T) :
    HasSum (fun q : PicO c => (twistFin χ (s + σ) q.out)⁻¹ * S q) T := by
  obtain ⟨e, he⟩ := _root_.GlobalTheory.CMVal.LatBij.exists_equiv E 𝔣 c h𝔣 hd hc
  rw [← e.hasSum_iff] at hT
  refine HasSum.sigma hT fun q => ?_
  refine ((hS q).mul_left (twistFin χ (s + σ) q.out)⁻¹).congr_fun fun x => ?_
  let k : Eˣ := Units.mk0 x.1.out (out_mem_lattice x).2
  have h1 := he ⟨q, x⟩ (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹) rfl
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (hatOUnits c)
    (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹)
  have h2 : twistFin χ (s + σ) u = 1 := by
    rw [twistFin_apply, hχ u u.2, modF_unit u.2]; simp
  have h3 : term φ (2 * s) κ σ x.1.out = twistFin χ (s + σ) (Units.map (algebraMap E (Af E)).toMonoidHom k) :=
    term_eq hφ h σ k
  show twistFin χ (s + σ) (e ⟨q, x⟩).1.out = _
  rw [h1, hu, map_mul, map_mul, h2, h3, mul_one, mul_comm, map_inv]

theorem toricSum_eq : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  intro hH E _ _ _ I _ φ hφ s κ 𝔣 Q χ Pq Λ hU hs h𝔣 hQ hχ hP hΛ
  classical
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hd : 𝔣 ∣ condQ 𝔣 Q := dvd_mul_right _ _
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hU h𝔣 hQ hχ
  have hfin := _root_.GlobalTheory.CMVal.PicFin.finite_picO E _ hc
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    _root_.GlobalTheory.CMVal.LatEnt.exists_isLatSum hH E I φ hφ s κ 𝔣 _ χ hU hs h𝔣 hd hc hχ.1 hχ.2.2.1 htriv q.out
  refine ⟨hfin, S, hS, ?_⟩
  have := Fintype.ofFinite (PicO (condQ 𝔣 Q))
  have key : (fun σ : ℂ => ∑ q : PicO (condQ 𝔣 Q), (twistFin χ (s + σ) q.out)⁻¹ * S q σ) = fun σ : ℂ =>
      Λ (s + σ) * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)),
        ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) *
          (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) +
          ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) ^ 2) := by
    refine entire_eq_of_halfPlane ?_ ?_ (1 - s) fun σ hσ => ?_
    · refine Differentiable.fun_sum fun q _ => Differentiable.mul ?_ (hS q).1
      simp only [twistFin_apply, mul_inv, ← Complex.cpow_neg]
      refine Differentiable.const_mul ?_ _
      exact Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (modF_pos _).ne'))
    · refine (hΛ.1.comp (by fun_prop)).mul (Differentiable.fun_finsetProd fun q _ => ?_)
      have h0 : Differentiable ℂ fun σ : ℂ => (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ)) := by
        refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
        rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
        exact q.ne_bot
      fun_prop
    · have h1 : 1 < ((s : ℂ) + σ).re := by simp; linarith
      have h2 := GlobalTheory.T.hasSum_integralIdeles_eulerProduct E I φ hφ s κ 𝔣 Q χ Pq (s + σ) _ hU h𝔣 hQ hχ hP h1 (hΛ.2 _ h1)
      exact (hasSum_fintype _).unique (hasSum_classes hφ hχ.2.2.1 h𝔣 hd hc htriv
        (fun q => (hS q).2 σ (by push_cast; linarith)) h2)
  have h0 := congrFun key 0
  simp only [add_zero, twistFin_apply, Complex.cpow_neg, Complex.cpow_natCast] at h0
  rw [finsum_eq_sum_of_fintype]
  simp only [Formalism.PairingDivisionLocalBalance.eq, Complex.ofReal_pow]
  exact h0.symm

end GlobalTheory.ToricSumValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompact
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isTest_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨-, -, -, S, hS⟩ := hf
  have hK : IsCompact ((L.K.toSubgroup : Subgroup G.GAf) : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun ab : G.GAf × G.GAf => ab.1 * s * ab.2) ''
      ((L.K.toSubgroup : Set G.GAf) ×ˢ (L.K.toSubgroup : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => (hK.prod hK).image ?_
    fun_prop
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory
end

