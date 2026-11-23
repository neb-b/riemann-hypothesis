module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
section
open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.GenericReading

theorem countable_of_fg_top {K L : Type} [Field K] [Countable K] [Field L] [Algebra K L]
    (h : (⊤ : IntermediateField K L).FG) : Countable L := by
  obtain ⟨s, hs⟩ := h
  have h1 := IntermediateField.cardinalMk_adjoin_le K (s : Set L)
  rw [hs, Cardinal.mk_congr (IntermediateField.topEquiv (F := K) (E := L)).toEquiv] at h1
  refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
  · exact Cardinal.mk_le_aleph0
  · exact Cardinal.mk_le_aleph0

theorem countable_fractionRing_mvPolynomial (ι L : Type) [Countable ι] [Field L] [Countable L] :
    Countable (FractionRing (MvPolynomial ι L)) := by
  have h : Countable (MvPolynomial ι L) := by
    refine Cardinal.mk_le_aleph0_iff.1 (MvPolynomial.cardinalMk_le_max.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0
  refine Cardinal.mk_le_aleph0_iff.1 ?_
  rw [FractionRing.cardinalMk]
  exact Cardinal.mk_le_aleph0

theorem embedding_read_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c), Nonempty (Om Z →ₐ[c.F] CAt σ) ∧ ∀ φ : Om Z →ₐ[c.F] CAt σ, ∃ (k : U.Comp) (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU h Z
  refine ⟨?_, fun φ => ?_⟩
  · have hfin : FiniteDimensional ℚ c.F := c.fin
    have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
      simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
    have hk : Countable (kap Z) := countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
    have hO : Countable (Om Z) := countable_fractionRing_mvPolynomial _ _
    let _ : Algebra c.F ℂ := σ.toAlgebra
    exact GlobalTheory.nonempty_algHom_complex_of_countable c.F (Om Z)
  · obtain ⟨y', hy⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c (Om Z)
      (CAt σ) φ (genFr h Z)
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y'
    exact ⟨k, x, y', t, hy, ht⟩

end GlobalTheory.GenericReading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSection
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.GenFactor

open GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_factor (hT : Out.SecTwistSt) {Z : Type} (x u : Sp ℂ ⟶ Xo.X) (hxu : x = u) (s : LB.Sec (PPx x))
    (hs : SecGen x s) (e : Z → (Over.mk u ⟶ Xo.univ.t.G)) (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ)
    (hθ : ∃ z, θ z ≠ 0) (hfr : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (t : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).Sec)
    (ht : ∀ j z (p : Sp ℂ ⟶ pullback Xo.univ.t.G.hom u), p ≫ pullback.fst _ _ = (e z).left →
      p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' p ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).U (fun _ => j)) (t.f (fun _ => j)) =
        θ z * fr j z) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (e z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z := by
  subst hxu
  obtain ⟨s', hs'⟩ := GlobalTheory.FibreSection.exists_sec_same_values E H Dw l Xo x t
  obtain ⟨a, ha, -⟩ := hs s'
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (e z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      a * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z := by
    intro j z pt e₁ e₂ hj
    have hw : (e z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ x := (Over.w (e z)).trans (Category.id_comp _).symm
    have p₁ := pullback.lift_fst (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    have p₂ := pullback.lift_snd (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    refine ((sec_values_complex_fibre hT E H Dw l Xo x s).1 a (fun _ => j) pt e₂).symm.trans ?_
    refine (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).symm.trans ?_
    exact (hs' j pt _ (p₁.trans e₁.symm) p₂ e₂).trans (ht j z _ p₁ p₂ hj)
  obtain ⟨z₀, hz₀⟩ := hθ
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e z₀).left
  obtain ⟨pt₀, e₁, e₂⟩ := exists_pt (R := ℂ) x (𝟙 _) (e z₀).left
    ((Category.id_comp _).trans (Over.w (e z₀)).symm)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := key j₀ z₀ pt₀ e₁ e₂ hj₀
    rw [zero_mul] at this
    exact mul_ne_zero hz₀ (hfr j₀ z₀ hj₀) this.symm
  refine ⟨a⁻¹, inv_ne_zero ha0, fun j z pt e₁ e₂ hj => ?_⟩
  rw [mul_assoc, ← key j z pt e₁ e₂ hj, inv_mul_cancel_left₀ ha0]

end

theorem exists_holomorphic_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) ty B P → (∀ b ∈ B, (y b).x = F.u k (P b)) → (∀ z, DifferentiableOn ℂ (fun b => θ b z) B) → (∀ b ∈ B, ∃ z, θ b z ≠ 0) → IsThetaFrame Xo.univ.t.PP B (fun b => F.u k (P b)) (fun b z => (F.ex k (P b) z).left) θ → ∃ (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (κ : (Fin m → ℂ) → ℂ), RigFrame F k B P fr ∧ DifferentiableOn ℂ κ B ∧ ∀ b ∈ B, κ b ≠ 0 ∧ SecVal F k (P b) (y b).x (y b).s (fun z => κ b * θ b z) (fun j z => fr j (b, z)) := by
  intro E _ _ _ H Dw l Xo c σ σ' g ty F k A _ _ yA m B ψ y P θ hB hψ hb hP hxu hθ hθ0 hfr
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨fr, f₁, f₂, f₃, f₄, f₅⟩ := hfr
  have hκ₁ : ∀ b, ∃ κ : ℂ, b ∈ B → κ ≠ 0 ∧
      SecVal F k (P b) (y b).x (y b).s (fun z => κ * θ b z) (fun j z => fr j (b, z)) := fun b => by
    by_cases h : b ∈ B
    · obtain ⟨t, ht⟩ := f₅ b h
      obtain ⟨κ, h₁, h₂⟩ := exists_factor hT (y b).x (F.u k (P b)) (hxu b h) (y b).s (y b).gen (F.ex k (P b)) (θ b)
        (fun j z => fr j (b, z)) (hθ0 b h) (fun j z hz => f₂ j b z h hz) t ht
      exact ⟨κ, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose κ hκ using hκ₁
  refine ⟨fr, κ, ⟨f₁, f₂, f₃, f₄⟩, fun b₀ hb₀ => ?_, hκ⟩
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd yA.x) (gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have d₁ : DifferentiableOn ℂ (fun b => θ b w₀) W := (hθ w₀).mono fun b h => h.1
  have d₂ : DifferentiableOn ℂ (fun b => fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) (g := fr j)
      (f₁ j) hι.differentiableOn fun b h => ⟨h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      κ b * (θ b w₀ * fr j (b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hκ b h.1).2 j w₀ pt e₁ e₂ (m₂ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, θ b w₀ * fr j (b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : DifferentiableOn ℂ κ W := (d₃.mul ((d₁.mul d₂).inv nz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.GenFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExtendByZeroConstMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem extendByZero_const_mul {p : ℕ} (k : ℕ) (f : Fin p → ℕ) (i : ℕ) :
    Formalism.L2.Pj.ext0 (fun s => k * f s) i = k * Formalism.L2.Pj.ext0 f i := by
  unfold Formalism.L2.Pj.ext0; split_ifs <;> simp

theorem wtA_wsmul_eq {D : D7} {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) : wtA (wsmul k w) = k • wtA w := by
  funext x
  simp only [wtA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : Formalism.L2.Pj.ext0 ((wsmul k w).aP t) x.2 = k * Formalism.L2.Pj.ext0 (w.aP t) x.2 := extendByZero_const_mul _ _ _
  have h2 : Formalism.L2.Pj.ext0 ((wsmul k w).aM t) x.2 = k * Formalism.L2.Pj.ext0 (w.aM t) x.2 := extendByZero_const_mul _ _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem intFormSt_holds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (wL : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL), IntFormSt h j hG w := by
  intro D T h j hj hG wL N w Z k n cf b hk hcf hb
  have hw : ∀ i, ((w i : (recB h.toLawsCore).Cusp j wL) : T.R j) ∈
      cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA wL) wL.n := fun i => cutR_le T.C j wL (w i).2
  obtain ⟨g, hg, hgb⟩ := exists_cusp_of_integral_all _ _ _ _ (T.Q.Xo j) T.Q.c hG _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ)))
    (wtA wL) wL.n N (fun i => ((w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) (dom_wtA wL)
    (fun i => by rw [Formalism.L2.PjFree.cusp_ofPj]; exact hw i) Z k n cf b hk hcf hb
  rw [Formalism.L2.PjFree.cusp_ofPj, ← wtA_wsmul_eq] at hg
  have hg' : g ∈ cutR T.C j (wsmul k wL) := by
    rw [cutR_eq T.C hj]; exact hg
  exact ⟨⟨g, hg'⟩, hgb⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwiseStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  first | exact @GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | exact GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | (intros; apply GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Comparison₂

theorem isReduced_cAt {K : Type} [Field K] (σ : K →+* ℂ) : IsReduced (CAt σ) :=
  inferInstanceAs (IsReduced ℂ)

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (z w : CAt σ) : cabs (z * w) = cabs z * cabs w :=
  norm_mul (show ℂ from z) (show ℂ from w)

theorem cabs_wchar {K : Type} [Field K] {σ : K →+* ℂ} {ι : Type} [Fintype ι] (e : ι → ℕ) (t : ι → (CAt σ)ˣ) :
    cabs (wchar e t) = ∏ i, cabs (t i : CAt σ) ^ e i := by
  have h := norm_prod (α := ℂ) Finset.univ (fun i => (show ℂ from (t i : CAt σ)) ^ e i)
  exact h.trans (Finset.prod_congr rfl fun i _ => norm_pow (α := ℂ) _ _)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (u : (CAt σ)ˣ) : 0 < cabs (u : CAt σ) :=
  norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) u)

theorem cabs_conjAlg {K : Type} [Field K] (σ : K →+* ℂ) (z : CAt σ) : cabs (conjAlg σ z) = cabs z :=
  Complex.norm_conj (show ℂ from z)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem baseNorm_pos (Dw : Datum H) {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some p => exact Real.sqrt_pos.2 (by positivity)

theorem prod_baseNorm (Dw : Datum H) {x : ℝ} (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∏ i, (baseNorm Dw x i)⁻¹ ^ ex Dw a n i = Formalism.L2.PjFree.lieFac Dw x a := by
  classical
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hs : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, ← Real.exp_neg]
    congr 1; ring
  rw [Fintype.prod_option]
  simp only [baseNorm, ex, inv_one, one_pow, one_mul, hs, ← Real.exp_nat_mul]
  rw [← Real.exp_sum, Formalism.L2.PjFree.lieFac, ← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_sigma]
  ring

theorem ptNorm_eq_pnorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hP
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ y i, fn σ y i ≠ 0 := by
    intro σ hσ y i
    obtain ⟨k, x, t, hx1, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).2 y
    have h := hP.1 σ hσ k x hx1 t y ht i
    rw [← abs_pos, h]
    exact mul_pos (cabs_unit_pos _) (baseNorm_pos Dw hx i)
  refine ⟨fun σ y i => ?_, fun σ hσ k x t y ht a n hd f hf => ?_, fun σ y y' hm a n f hf => ?_⟩
  · by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · exact hgood σ hσ y i
    · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
        have h := Formalism.L2.PjFree.goodEmb_goodOf c σ
        rwa [Formalism.L2.PjFree.goodOf, if_neg hσ] at h
      obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
      rw [← abs_pos, ← hP.2 σ y y' hy' i, abs_pos]
      exact hgood _ hσ' y' i
  · obtain ⟨x', hx', -, ⟨t', ht'⟩, hpn⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).1 k x
    have htt := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).2.1 t' t _ _ _ ht' ht
    have hfn := hP.1 σ hσ k x' hx' _ y htt
    have hev := hwt (CAt σ) (isReduced_cAt σ) a n f hf _ _ _ htt
    rw [hpn _ _ ((hU σ hσ).2.2.2.2.1 a n hd f hf k)]
    have hrd : ‖Formalism.L2.PjFree.rdU (U σ) f k x'.1‖ = cabs (evR Xo c f ((U σ).un k x')) := by
      have e : Formalism.L2.PjFree.rdU (U σ) f k x'.1 = Formalism.L2.PjFree.toC (evR Xo c f ((U σ).un k x')) :=
        dif_pos x'.2
      rw [e]; rfl
    rw [hrd, ← prod_baseNorm Dw hx a n]
    change cabs (evR Xo c f y) * _ = _
    rw [hev, cabs_mul, cabs_wchar, mul_right_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hfn i, ← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (cabs_unit_pos _).ne', one_mul]
  · have := isReduced_cAt σ
    have hev := evR_frMap hWD f hf.1 (conjAlg σ) y (hT _ y) y' hm
    change cabs (evR Xo c f y') * _ = cabs (evR Xo c f y) * _
    rw [hev, cabs_conjAlg]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [hP.2 σ y y' hm i]

end GlobalTheory.FrameNorm.Comparison₂
end

