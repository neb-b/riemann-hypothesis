module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.CoeffCongFactor
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem evR_eq_clsSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂), FrOver d y₂ y → IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y₂.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk → A.Marked mk → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), LatsOK d.l₂.M La Nc → (∀ k, io (xs k) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ k, IsRoots d.l₂ L mk (Nc k) (Y k)) → ∀ f : Rul Xo c, IsThClsD Xo c d w La Nc gam vol ep io xs f → evR Xo c f y = evR d.Xo₂ d.c₂ d.cδ y₂ * κ * clsSum (algebraMap c.F ℂ) X hr bas idx eL w La Nc gam vol ep (fun k => io (xs k)) L v Y x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hF ⟨inst, hnab⟩ r g X bas idx e x L y y₂ A hov hs hx hL q0 hr eL hr' hn
    hlet θ v κ hread hvac hκ mk hmk hA Cl _ w La Nc gam vol ep Vs _ _ io xs a hLa hH Y hY f hf
  obtain ⟨vc, hvc, hev⟩ := hf ℂ hF y y₂ hov
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = algebraMap c.F ℂ :=
    RingHom.ext fun t => hF t
  rw [hev, mul_assoc, clsSum, Finset.mul_sum _ _ κ]
  refine congrArg (fun t => evR d.Xo₂ d.c₂ d.cδ y₂ * t) (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨h1, h2, h3⟩ := hLa k
  have hV : (La k).La ∈ Vset E n d.l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset E n (La k).La).2.1 _ (Nc k) d.l₂.odd.pos h1 h2 h3
  have hP := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hH k)
  have h := _root_.GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X bas idx e x L y₂ A hs hx hL q0 n hr eL hr' hn hlet
    d.nab₂ hnab θ v κ hread hvac hκ mk hmk hA (La k).La hV (Nc k) h3 (Y k) (hY k) a _ hP _ 1 (vc k) (hvc k)
  rw [h, MvPolynomial.map_map, hcomp]
  simp only [hF, map_mul, map_inv₀, map_natCast, inv_one, map_one]
  ring

end GlobalTheory.ClsVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem readings_independent :
    ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  intro D T hM j hj a n

  have hA := GlobalTheory.FramedBaseChange.bcEx_all _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀
  have hF := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact jInjRd_of_wt T hM hj a n hA hF

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsComponentsLatticesMovedToLevelFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Setup

open GlobalTheory.SW.Lev

section Algebra

variable {O : Type} [CommRing O] {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module O V]
  {r : ℕ} {𝔞 𝔟 : Ideal O} {L : Submodule O V} {δ : M →ₗ[O] V}

theorem exists_lift_gens (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ 𝔞 • L)
    (hin : ∀ a, δ a ∈ 𝔞 • L → a ∈ 𝔞 • (⊤ : Submodule O M)) {v : Fin r → V} (hv : ∀ i, v i ∈ L)
    (hs : L ≤ Submodule.span O (Set.range v) ⊔ 𝔞 • L) :
    ∃ b : Fin r → M, Submodule.span O (Set.range b) ⊔ 𝔞 • (⊤ : Submodule O M) = ⊤ := by
  have h (i) : ∃ b, v i - δ b ∈ 𝔞 • L := by
    obtain ⟨_, ⟨b, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (hon (hv i))
    exact ⟨b, by rw [← e, add_sub_cancel_left]; exact hw⟩
  choose b hb using h
  refine ⟨b, eq_top_iff.2 fun a _ => ?_⟩
  have h1 : L ≤ (Submodule.span O (Set.range b)).map δ ⊔ 𝔞 • L := by
    refine hs.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    rw [← add_sub_cancel (δ (b i)) (v i)]
    exact Submodule.add_mem_sup ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩ (hb i)
  obtain ⟨_, ⟨s, hs, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (h1 (hδ a))
  rw [← add_sub_cancel s a]
  refine Submodule.add_mem_sup hs (hin _ ?_)
  rw [map_sub, ← e, add_sub_cancel_left]; exact hw

theorem mem_of_gens {N : Submodule O V} (hδ : ∀ a, δ a ∈ L) (hN : 𝔞 • L ≤ N) {b : Fin r → M}
    (hb : Submodule.span O (Set.range b) ⊔ 𝔞 • (⊤ : Submodule O M) = ⊤) (h : ∀ i, δ (b i) ∈ N) (a : M) :
    δ a ∈ N := by
  have : (⊤ : Submodule O M) ≤ N.comap δ := by
    rw [← hb]
    refine sup_le (Submodule.span_le.2 ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩; exact h i
    · refine Submodule.smul_induction_on hx (fun c hc y _ => ?_) fun y z hy hz => add_mem hy hz
      rw [Submodule.mem_comap, map_smul]
      exact hN (Submodule.smul_mem_smul hc (hδ y))
  exact this trivial

theorem exists_glue_gens (hc : IsCoprime 𝔞 𝔟) {v w : Fin r → V} (hv : ∀ i, v i ∈ L) (hw : ∀ i, w i ∈ L)
    (hv' : ∀ N, 𝔞 • L ≤ N → (∀ i, v i ∈ N) → L ≤ N) (hw' : L ≤ Submodule.span O (Set.range w) ⊔ 𝔟 • L) :
    ∃ u : Fin r → V, (∀ i, u i ∈ L) ∧ (∀ i, v i - u i ∈ 𝔞 • L) ∧
      L ≤ Submodule.span O (Set.range u) ⊔ (𝔞 * 𝔟) • L := by
  obtain ⟨e, he, f, hf, hef⟩ := Ideal.isCoprime_iff_exists.1 hc
  let u : Fin r → V := fun i => f • v i + e • w i
  have e1 (i) : v i - u i = e • (v i - w i) := by
    rw [show e = 1 - f from eq_sub_of_add_eq hef]
    simp only [u, show e = 1 - f from eq_sub_of_add_eq hef]
    module
  have e2 (i) : w i - u i = f • (w i - v i) := by
    simp only [u, show e = 1 - f from eq_sub_of_add_eq hef]
    module
  have h1 (i) : v i - u i ∈ 𝔞 • L := e1 i ▸ Submodule.smul_mem_smul he (sub_mem (hv i) (hw i))
  have h2 (i) : w i - u i ∈ 𝔟 • L := e2 i ▸ Submodule.smul_mem_smul hf (sub_mem (hw i) (hv i))
  have ha : L ≤ Submodule.span O (Set.range u) ⊔ 𝔞 • L := hv' _ le_sup_right fun i => by
    rw [← add_sub_cancel (u i) (v i)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (h1 i)
  have hb : L ≤ Submodule.span O (Set.range u) ⊔ 𝔟 • L := by
    refine hw'.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    rw [← add_sub_cancel (u i) (w i)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (h2 i)
  refine ⟨u, fun i => add_mem (L.smul_mem _ (hv i)) (L.smul_mem _ (hw i)), h1, fun x hx => ?_⟩
  obtain ⟨s, hs, y, hy, ey⟩ := Submodule.mem_sup.1 (ha hx)
  obtain ⟨t, ht, z, hz, ez⟩ := Submodule.mem_sup.1 (hb hx)
  have : x = (e • t + f • s) + (e • z + f • y) := by
    conv_lhs => rw [← one_smul O x, ← hef, add_smul]
    conv_lhs => enter [1]; rw [← ez]
    conv_lhs => enter [2]; rw [← ey]
    module
  rw [this]
  refine Submodule.add_mem_sup (add_mem (Submodule.smul_mem _ _ ht) (Submodule.smul_mem _ _ hs)) (add_mem ?_ ?_)
  · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he hz
  · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hf hy

end Algebra

end GlobalTheory.Dict.Setup

namespace GlobalTheory.Dict.Setup

open GlobalTheory.SW.Lev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X X' : Data E r}

theorem ef_eq (h : SameSp X X') : EF X = EF X' := by
  funext u v
  unfold GlobalTheory.ThFr.EF
  rw [h.ka, h.gm]

theorem selfD_of_same (h : SameSp X X') {L : Lt E r} (hL : SelfD X L) : SelfD X' L := by
  unfold SelfD at hL ⊢
  rwa [← ef_eq h]

theorem isUn_of_same (h : SameSp X X') {ga : GL (Fin r) E} (hu : IsUn X' ga) : IsUn X ga := by
  unfold IsUn at hu ⊢
  rwa [h.gm]

theorem sameSp_trans_symm {X'' : Data E r} (h : SameSp X X'') (h' : SameSp X' X'') : SameSp X X' :=
  ⟨h.psi.trans h'.psi.symm, h.gm.trans h'.gm.symm, h.p0.trans h'.p0.symm, h.xi.trans h'.xi.symm,
    h.ka.trans h'.ka.symm⟩

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M] {𝔞 𝔟 : Ideal (𝓞 E)}

theorem exists_move (D : SW.Level X) (hm : D.𝔪 = 𝔞 * 𝔟) (hc : IsCoprime 𝔞 𝔟) (hΛ : SelfD X X.Λ) {L : Lt E r}
    (hL : SelfD X L) {δ : M →ₗ[𝓞 E] (Fin r → E)} (hδ : ∀ a, δ a ∈ L) (hon : L ≤ LinearMap.range δ ⊔ 𝔞 • L)
    {b : Fin r → M} (hb : Submodule.span (𝓞 E) (Set.range b) ⊔ 𝔞 • (⊤ : Submodule (𝓞 E) M) = ⊤)
    {p : 𝓞 E} (hp : IsCoprime (Ideal.span {p}) 𝔞) :
    ∃ ga : GL (Fin r) E, IsUn X ga ∧ mapL ga L ∈ D.lats ∧ ∀ i, Cong X 𝔞 (p • lin ga (δ (b i))) (D.β i) := by
  have hle : D.𝔪 ≤ 𝔞 := hm.le.trans Ideal.mul_le_left
  have h0 : 𝔟 ≠ ⊥ := fun e => D.ne_bot (by rw [hm, e, Ideal.mul_bot])
  obtain ⟨w, hw, hw'⟩ := TieModel.exists_gens h0 r L hL.1
  obtain ⟨u, hu, h1, h2⟩ := exists_glue_gens hc (v := fun i => p • δ (b i)) (fun i => L.smul_mem _ (hδ _)) hw
    (fun N hN h => hon.trans (sup_le (by
      rintro _ ⟨a, rfl⟩
      exact mem_of_gens hδ hN hb (fun i => mem_of_loc (hδ _) hN ⟨p, hp, h i⟩) a) hN)) hw'
  obtain ⟨ga, hun, hl, hcg⟩ := exists_move_marked E r X D L u hΛ hL hu (hm ▸ h2)
  refine ⟨ga, hun, hl, fun i => cong_trans ?_ (TieModel.cong_mono hle (hcg i))⟩
  obtain ⟨-, s, hs, hLΛ, -⟩ := hl
  refine ⟨s, Stab.cop_mono hle hs.of_mul_right_left, ?_⟩
  rw [← lin_apply, ← map_smul, ← map_sub]
  exact smul_map_mem (lin ga) (fun v hv => hLΛ _ ⟨v, hv, rfl⟩) (h1 i)

theorem sub_mem_of_cong (D : SW.Level X) (hle : D.𝔪 ≤ 𝔞) {L : Lt E r} (hL : L ∈ D.lats)
    {δ δ' : M →ₗ[𝓞 E] (Fin r → E)} (hδ : ∀ a, δ a ∈ L) (hδ' : ∀ a, δ' a ∈ L)
    {b : Fin r → M} (hb : Submodule.span (𝓞 E) (Set.range b) ⊔ 𝔞 • (⊤ : Submodule (𝓞 E) M) = ⊤)
    {p : 𝓞 E} (hp : IsCoprime (Ideal.span {p}) 𝔞) (h : ∀ i, Cong X 𝔞 (p • δ (b i)) (p • δ' (b i))) (a : M) :
    δ a - δ' a ∈ 𝔞 • L := by
  obtain ⟨-, s, hs, -, hΛL⟩ := hL
  refine mem_of_gens (δ := δ - δ') (fun a => sub_mem (hδ a) (hδ' a)) le_rfl hb (fun i => ?_) a
  refine mem_of_loc (sub_mem (hδ _) (hδ' _)) le_rfl (loc_loc hp ?_)
  obtain ⟨t, ht, h⟩ := h i
  refine loc_loc ht ⟨s, Stab.cop_mono hle hs.of_mul_right_left, ?_⟩
  rw [LinearMap.sub_apply, smul_sub p]
  exact smul_map_mem LinearMap.id hΛL h

end GlobalTheory.Dict.Setup

theorem GlobalTheory.Dict.exists_components_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → d.IsLev → ∀ (W : UW U) (k₀ : U.Comp), (∀ k, SameSp (U.X k) (U.X k₀)) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (D : SW.Level (U.X k₀)) (hn : r ≤ n), LevTie d σ ph D hn → ∃ (x0 : Fin n → Dw.La) (ga : U.Comp → GL (Fin r) E) (δ : U.Comp → (Dw.La →ₗ[𝓞 E] (Fin r → E))), (∀ rk, AdmX (l := l) rk x0) ∧ (∀ k, IsUn (U.X k₀) (ga k) ∧ mapL (ga k) (U.X k).Λ ∈ D.lats ∧ IsMark l (mapL (ga k) (U.X k).Λ) (mvMap (ga k) (W.mark k)) ∧ IsDual (U.X k₀) l (σ (zetaM c)) (mapL (ga k) (U.X k).Λ) (mvMap (ga k) (W.mark k)) (δ k) ∧ IsBaseClassLevelAdapted d D hn x0 (δ k)) ∧ ∀ k k', ∀ g' ∈ D.grp, mapL g' (mapL (ga k) (U.X k).Λ) = mapL (ga k') (U.X k').Λ → k = k' := by
  intro E _ _ _ H Dw l Xo c n d σ r U hσ hU hr hA hd W k₀ hs ph D hn hT
  have hζ : IsPrimitiveRoot (σ (zetaM c)) l.M :=
    (GlobalTheory.LevelPairing.zetaM_prim c).map_of_injective σ.injective
  have hL (k) : SelfD (U.X k₀) (U.X k).Λ :=
    Setup.selfD_of_same (hs k) (_root_.GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr W k).2.1
  have hmk (k) : IsMark l (U.X k).Λ (W.mark k) := (_root_.GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr W k).2.2.1
  have hdual (k) := _root_.GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k₀) _ _ _ (hL k) (hmk k) hζ
  choose δ hδ using fun k => (hdual k).1
  have hle : D.𝔪 ≤ Mfr l := hT.prod.le.trans Ideal.mul_le_left
  have hp : IsCoprime (Ideal.span {(d.pd : 𝓞 E)}) (Mfr l) := by
    obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hd.2.2.1).map (Int.castRingHom (𝓞 E))
    exact Lev.cop_iff.2 ⟨a, _, Ideal.mul_mem_left _ b (TieModel.m_mem l), by simpa using e⟩
  obtain ⟨b, hb⟩ := Setup.exists_lift_gens (hδ k₀).mem ((hdual k₀).2.1 _ (hδ k₀)).1
    (fun a => (((hdual k₀).2.1 _ (hδ k₀)).2.1 a).1) D.β_mem
    (D.β_span.trans (sup_le_sup_left (Submodule.smul_mono hle le_rfl) _))
  choose ga hun hl hcg using fun k => Setup.exists_move D hT.prod hT.cop (hL k₀) (hL k) (hδ k).mem
    ((hdual k).2.1 _ (hδ k)).1 hb hp
  have hmv (k) := ((hdual k).2.1 _ (hδ k)).2.2.1 (ga k) (hun k)
  refine ⟨fun j => if h : (j : ℕ) < r then b ⟨j, h⟩ else 0, ga, fun k => mvMap (ga k) (δ k), fun rk => ?_,
    fun k => ⟨hun k, hl k, (hmv k).1, (hmv k).2, fun i => ?_, fun j hj => ?_⟩, fun k k' g' hg' e => ?_⟩
  · rw [AdmX, eq_top_iff]
    refine hb.ge.trans (sup_le_sup_right (Submodule.span_mono ?_) _)
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castLE hn i, Or.inr (hU.1 ▸ i.2), dif_pos i.2⟩
  · have e : (if h : ((Fin.castLE hn i : Fin n) : ℕ) < r then b ⟨Fin.castLE hn i, h⟩ else 0) = b i := dif_pos i.2
    beta_reduce
    rw [e, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hcg k i
  · beta_reduce
    rw [dite_eq_right (not_lt.2 hj)]
    exact zero_mem _
  · obtain ⟨hu', kk, -, hred⟩ := (Lev.mem_grp g').1 hg'
    obtain ⟨s, hs', hk, -⟩ := Lev.keeps hred
    have h1 := ((_root_.GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k₀) _ _ _ (hl k).1 (hmv k).1 hζ).2.1 _ (hmv k).2).2.2.1 g' hu'
    rw [e] at h1
    have h2 := Setup.sub_mem_of_cong D hle (hl k') h1.2.mem (hmv k').2.mem hb hp fun i => by
      refine Lev.cong_trans ?_ (Lev.cong_symm (hcg k' i))
      refine Lev.cong_trans ?_ (Stab.cong_frame hle (fun k hk => (hT.grp k).1 hk) hg' i)
      have := Lev.cong_lin (Stab.cop_mono hle hs') hk (hcg k i)
      rwa [map_smul] at this
    have h3 := ((_root_.GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k₀) _ _ _ (hl k').1 h1.1 hζ).2.1 _ h1.2).2.2.2 _ _
      (hmv k').1 (hmv k').2 h2
    refine _root_.GlobalTheory.Dict.comp_eq_of_matched E H Dw l Xo c σ r U hσ hU hr hA W k k' (Setup.sameSp_trans_symm (hs k) (hs k'))
      ((ga k')⁻¹ * (g' * ga k))
      (Setup.isUn_of_same (hs k) (Lev.isUn_mul (Lev.isUn_inv (hun k')) (Lev.isUn_mul hu' (hun k)))) ?_
      fun a ha => ?_
    · ext v
      have := SetLike.ext_iff.1 e (Lev.lin (ga k') v)
      rw [Lev.mem_mapL, Lev.mem_mapL, Lev.mem_mapL, Lev.lin_inv] at this
      rw [← this, Lev.mem_mapL, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Lev.lin_mul, Lev.lin_mul]
    · obtain ⟨u, hu, e'⟩ := h3 a ha
      refine ⟨_, Lev.mem_mapL.1 hu, ?_⟩
      rw [← Lev.lin_apply, Lev.lin_mul, Lev.lin_mul]
      have e'' : Lev.lin g' (Lev.lin (ga k) (W.mark k a)) = Lev.lin (ga k') (W.mark k' a) + l.M • u := e'
      rw [e'', map_add (f := _), Lev.lin_inv, map_nsmul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerOntoStd

open GlobalTheory.AdelTranslate GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem glue_map (c : E ≃ₐ[F] E) (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) :
    (glue e γ).map (sg (FiniteAdeleRing (𝓞 F) F) c) = glue e (γ.map c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [glue, fm, sg]
  · simp [glue, fm, sg, Matrix.one_apply_ne h]

theorem mul_glue_sub_one {e α : FiniteAdeleRing (𝓞 F) F} (h : α * e = 0) (γ : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (α ⊗ₜ[F] (1 : E) : RA F E) * (glue e γ - 1) i j = 0 := by
  have h0 : (α ⊗ₜ[F] (1 : E) : RA F E) * (e ⊗ₜ[F] (1 : E)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h, TensorProduct.zero_tmul]
  simp only [glue, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (fm F γ i j - (1 : Matrix (Fin n) (Fin n) (RA F E)) i j) * h0

theorem mul_idem_eq_zero {k M : ℕ} (hk : k.Coprime M) {v : HeightOneSpectrum (𝓞 F)} (hv : (M : 𝓞 F) ∈ v.asIdeal)
    {α : FiniteAdeleRing (𝓞 F) F} (hα : ∀ v', v' ≠ v → α v' = 0) : α * idem F k = 0 := by
  refine DFunLike.ext _ _ fun w => ?_
  change α w * idem F k w = 0
  by_cases h : w = v
  · subst h
    rw [idem_apply, if_neg, mul_zero]
    intro hk'
    obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 F) (M : 𝓞 F) := Nat.Coprime.cast hk
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (w.asIdeal.mul_mem_left a hk') (w.asIdeal.mul_mem_left b hv)))
  · rw [hα w h, zero_mul]

end General

theorem finPart_cA (D : D7) (x : AE D) :
    finPart D (cA D x) = sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (finPart D x) :=
  GlobalTheory.UnitarySplit.map_sig (sndA D.host.F) D.sp.cm.sig x


set_option maxHeartbeats 1000000 in
theorem exists_trivAt_isMov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  rintro D S T C M - Λ ⟨-, hU', k, hk0, hkM, h1, h2⟩
  have hU : (⟨Λ⟩ : GenLat D.host.E S.rank).Unimod := (GlobalTheory.Dict.GenLatCmp.unimod_iff Λ).2 hU'
  have h₁ : ∀ x ∈ Λ, k • x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h₂ : ∀ x ∈ stdL D.host.E S.rank, k • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  obtain ⟨k', γ, hk', hγ, h₃, h₄⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted D.host.E (hostOfRecord D) S.rank ⟨Λ⟩ k hU hk0
    (by rw [GlobalTheory.Dict.GenLatCmp.std_eq, span_smul_le_iff]; exact h₂) k hk0
  rw [GlobalTheory.Dict.GenLatCmp.std_eq] at h₃ h₄
  set c := GlobalTheory.Member.cF D with hc
  have c2 : ∀ x, c (c x) = x := fun x => star_star x
  set δ : Matrix (Fin S.rank) (Fin S.rank) D.host.E := (γ.map c)ᵀ with hδ
  have hδγ : δ * γ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← hγ i j]
    rfl
  have hγδ : γ * δ = 1 := mul_eq_one_comm.1 hδγ
  have hδc : γᵀ.map c = δ := rfl
  have h₅ : ∀ x ∈ stdL D.host.E S.rank, k' • δ *ᵥ x ∈ Λ := fun x hx => by
    obtain ⟨w, hw, e⟩ := h₄ x hx
    rwa [← Nat.cast_smul_eq_nsmul D.host.E, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
  have h₆ : ∀ x ∈ Λ, k' • γ *ᵥ x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    exact h₃ x hx
  have he := idem_mul (F := D.host.F) k
  have t1 : γᵀ * δᵀ = 1 := by rw [← Matrix.transpose_mul, hδγ, Matrix.transpose_one]
  have t2 : δᵀ * γᵀ = 1 := by rw [← Matrix.transpose_mul, hγδ, Matrix.transpose_one]
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨h, hh, eh⟩ := lift ⟨glue (idem _ k) γᵀ, glue (idem _ k) δᵀ, glue_mul he t1, glue_mul he t2⟩ (by
    rw [C.m.gS, Matrix.transpose_one]
    refine isUnA_of c ?_
    change ((glue (idem _ k) γᵀ).map _)ᵀ * glue (idem _ k) γᵀ = 1
    rw [glue_map_sg, hδc]
    exact glue_mul he t2)
  have e1 : fmt S h = glue (idem _ k) γᵀ := congrArg Units.val eh
  have e2 : fmtC S h = glue (idem _ k) δ := by
    rw [← hδc, ← glue_map, ← e1]
    ext i j
    exact finPart_cA D _
  refine ⟨h, hh, ?_, ?_⟩
  · rintro v hv ε ⟨α, rfl, -, hα⟩ i j
    have hM : (M : 𝓞 D.host.F) ∈ v.asIdeal := hv (Ideal.mem_span_singleton_self _)
    apply GlobalTheory.UnitarySplit.parts_inj D
    · rw [map_mul, map_zero]
      have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
        change ((0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
        exact TensorProduct.zero_tmul _ _
      rw [this, zero_mul]
    · rw [map_mul, map_zero]
      have : finPart D ((mt S h - 1) i j) = (fmt S h - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
        congr 1
        by_cases hij : i = j
        · subst hij
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq, (finPart D).map_one]
        · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, (finPart D).map_zero]
      rw [this, e1]
      exact mul_glue_sub_one (mul_idem_eq_zero hkM hM hα) _ i j
  · rw [e2]
    intro u
    constructor
    · intro hu
      refine ⟨_, glue_mem_hat (F := D.host.F) hk' h₆ h₁ u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, glue_mul he hδγ, Matrix.one_mulVec]
    · rintro ⟨z, hz, ez⟩
      rw [ez]
      exact glue_mem_hat (F := D.host.F) hk' h₅ h₂ z hz

end GlobalTheory.KerOntoStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLatticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  first | exact @GlobalTheory.PushKeeps.push_keeps | exact GlobalTheory.PushKeeps.push_keeps | (intros; apply GlobalTheory.PushKeeps.push_keeps <;> assumption)
end

