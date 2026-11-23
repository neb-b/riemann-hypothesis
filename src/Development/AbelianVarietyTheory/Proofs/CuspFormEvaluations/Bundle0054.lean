module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShiftNullValNeZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaBase

open GlobalTheory.ThetaCoord GlobalTheory.VVRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mk_eq_zero_iff (k : ℕ) (m : Dw.La) :
    (Submodule.Quotient.mk m : LatMod Dw k) = 0 ↔ ∃ m' : Dw.La, k • m' = m := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

theorem exists_shift {R : ℕ} (hR : R ≠ 0) (q : LatMod Dw (R ^ 4)) (hq : R • q = 0) :
    ∃ u : LatMod Dw R, (Submodule.Quotient.mk (R ^ 3 • qRep u) : LatMod Dw (R ^ 4)) = q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨m', hm⟩ := (mk_eq_zero_iff (R ^ 4) (R • m)).1 hq
  have e : R ^ 3 • m' = m := by
    have h : R • R ^ 3 • m' = R • m := by rw [← hm, ← mul_nsmul', ← pow_succ']
    refine Dw.unimod.1 (LinearMap.ext fun v => nsmul_right_injective hR ?_)
    have := congrArg (fun t => Dw.EF t v) h
    simpa only [map_nsmul, LinearMap.smul_apply] using this
  refine ⟨Submodule.Quotient.mk m', ?_⟩
  have h : (Submodule.Quotient.mk (qRep (Submodule.Quotient.mk m' : LatMod Dw R)) : LatMod Dw R) =
      Submodule.Quotient.mk m' := Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h ⊢
  obtain ⟨d, hd⟩ := (mk_eq_zero_iff R _).1 h
  refine (mk_eq_zero_iff _ _).2 ⟨d, ?_⟩
  rw [← e, ← smul_sub, ← hd, ← mul_nsmul', ← pow_succ]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem gen_ne_zero {K : Type} [CommRing K] [Nontrivial K] [Algebra c.F K] (y : FrPt Xo c K) :
    (SecM.ofSec Xo.univ.t.G y.s : SecM Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk y.x)) ≠ 0 := fun h => by
  have h₀ : ∀ i, y.s.f i = 0 := fun i => congrFun (congrArg Subtype.val h) i
  exact zero_ne_one ((y.gen y.s).unique (y₁ := 0) (y₂ := 1) (fun i => by rw [h₀, MulZeroClass.mul_zero])
    (fun i => by rw [h₀, MulZeroClass.mul_zero]))

theorem exists_nullVal_ne_zero (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K)
    (N : ℕ) {n : ℕ} (hn : 2 ≤ n) (a : ptO Xo y.x ⟶ Xo.univ.t.G) :
    ∃ z : ptO Xo y.x ⟶ Xo.univ.t.G, z ^ n = 1 ∧
      ∀ p w, IsNullVal Xo c N y p w → p ^ N = a * z → w ≠ 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange (UnivPol.pol Xo) y.x hn hK y.s
    (gen_ne_zero Xo c y) a
  refine ⟨z, hz, ?_⟩
  rintro p w ⟨F, ⟨t', α₀, α, s₁, U, -, rfl, -, -, -, hs₁, hU, hF⟩, hw⟩ hp h₀
  let o : (Over.mk y.x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk y.x).left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ o)
  replace hJ : Good Xo.univ.t.PP.L o J := hJ
  have b₁ := sv_act hU.pt_eq hF (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ t'
  have b₃ := sv_of_isValueAt hw (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [b₃, b₂, hp, h₀, map_zero, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu o J hJ))).ne_zero b₁.symm

end GlobalTheory.EtaBase

namespace GlobalTheory

open GlobalTheory.EtaBase

theorem exists_shift_nullVal_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → K), IsFullLev Xo (R ^ 4) y.x ev → (∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) → ∀ (n : ℕ) (x₀ : Fin n → Dw.La) (g : LevGrp Dw (R ^ 4)), ∃ u : Fin n → LatMod Dw R, ∀ b, w (g (shiftFam R x₀ u b)) ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R _ hR K _ _ _ y ev w hev hw n x₀ g
  have hR₀ : R ≠ 0 := by omega
  have e₀ : ev 0 = 1 := by
    have := hev.1 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have es : ∀ (m : ℕ) q, ev (m • q) = ev q ^ m := fun m q => by
    induction m with
    | zero => rw [zero_smul, e₀, pow_zero]
    | succ m ih => rw [succ_nsmul, hev.1, ih, pow_succ]
  have sur := ((_root_.GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)).2.2.1 K y.x ev hev).1
  have key : ∀ x : Dw.La, ∃ u : LatMod Dw R,
      w (g (Submodule.Quotient.mk (x + R • qRep u))) ≠ 0 := fun x => by
    obtain ⟨z, hz, h⟩ := exists_nullVal_ne_zero Xo c hL y (R ^ 2) hR (ev (g (Submodule.Quotient.mk x)) ^ R ^ 2)
    obtain ⟨q, rfl⟩ := sur z (by rw [pow_succ', pow_mul, hz, one_pow])
    have hq : R • q = 0 := hev.2.2 K (RingHom.id K) _ _ (by rw [es, hz, e₀])
    obtain ⟨u, hu⟩ := exists_shift hR₀ (g.symm q) (by rw [← map_nsmul, hq, map_zero])
    refine ⟨u, h _ _ (hw _) ?_⟩
    rw [← es, ← es, ← hev.1, ← g.apply_symm_apply q, ← hu, ← map_nsmul, ← map_nsmul, ← map_add (f := _)]
    congr 2
    show (Submodule.Quotient.mk (R ^ 2 • (x + R • qRep u)) : LatMod Dw (R ^ 4)) =
      Submodule.Quotient.mk (R ^ 2 • x + R ^ 3 • qRep u)
    rw [smul_add, ← mul_nsmul', ← pow_succ]
  choose u hu using key
  exact ⟨fun b => u (x₀ b), fun b => hu (x₀ b)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairing
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem cc_eq_host_conj (D : D7) (x : D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem principalDatum_trace_perfect : ∀ D : D7, ∃ AA : Submodule (𝓞 D.host.E) D.host.E,
    AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * ReciprocityTheory.ChartRestriction.G.FD.cc b) = z) ↔
        IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hA := AA_ne_zero hP D
  have hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  refine ⟨(D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ?_, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  · intro h0
    exact hA (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  · have h1 : ∀ w ∈ D.host.AA * D.host.AAbar, ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z := by
      intro w hw
      refine FractionalIdeal.mul_induction_on (C := fun w => ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z) hw
        (fun a ha b hb c => ?_) (fun u v hu hv c => ?_)
      · obtain ⟨z, hz⟩ := h (c • a) (Submodule.smul_mem _ c ha) (D.host.conj b) (conj_mem_AA D hb)
        refine ⟨z, ?_⟩
        rw [cc_eq_host_conj, conj_conj] at hz
        rw [← hz, ← smul_mul_assoc, mul_assoc (D.host.xi0 * x)]
      · obtain ⟨z, hz⟩ := hu c
        obtain ⟨z', hz'⟩ := hv c
        refine ⟨z + z', ?_⟩
        rw [smul_add, mul_add, map_add (f := _), hz, hz', Int.cast_add]
    have h2 : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) := by
      rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ hone)]
      intro a ha
      rw [← dual_eq hP D, mul_assoc, FractionalIdeal.mem_singleton_mul] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨z, hz⟩ := h1 w hw 1
      rw [one_smul] at hz
      refine ⟨z, ?_⟩
      rw [Algebra.traceForm_apply, ← mul_assoc, mul_comm x, hz]
      exact eq_intCast _ _
    rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h2
    obtain ⟨c, rfl⟩ := h2
    exact c.isIntegral_coe
  · intro a ha b hb
    have hm : (⟨x, h⟩ : 𝓞 D.host.E) • (a * D.host.conj b) ∈ NAA D :=
      Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
    obtain ⟨z, hz⟩ := trace_int_of_mem hP D hm
    refine ⟨z, ?_⟩
    rw [← hz, cc_eq_host_conj, Algebra.smul_def]
    congr 1
    change _ = D.host.xi0 * (x * (a * D.host.conj b))
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionAtLevelPointEqTranslateByRepresentative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.VtLevel

theorem tyAct_natCast_mul {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ) (a : 𝓞 E)
    (z : Fin g → ℂ) : tyAct ty ((n : 𝓞 E) * a) z = (n : ℂ) • tyAct ty a z := by
  funext k
  simp [tyAct, _root_.mul_assoc]

theorem tyAct_natCast {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ)
    (z : Fin g → ℂ) : tyAct ty (n : 𝓞 E) z = (n : ℂ) • z := by
  funext k
  simp [tyAct]

theorem hermForm_smul_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

theorem hermForm_two_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z ((2 : ℂ) • w) = 2 * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

theorem hermForm_add_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem e_natCast_smul (n : ℕ) (z : Fin g → ℂ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero => simpa using (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem sub_mem_of_e_eq {z w : Fin g → ℂ} (h : Φ.e z = Φ.e w) : z - w ∈ Φ.lat := by
  rw [← Φ.e_ker]
  have h1 := Φ.e_add (z - w) w
  rw [sub_add_cancel, h] at h1
  exact (mul_eq_right.1 h1.symm)

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

theorem bar_mem {r : 𝓞 E} (hr : r ∈ Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) :
    ∃ α ∈ l.Mb ^ 2, H.bar r = ((2 : ℕ) : 𝓞 E) * α := by
  have h1 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hr
  have h2 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar a
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_map, h2, Ideal.map_id, Ideal.map_span, Set.image_singleton,
    map_ofNat, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨α, hα, h⟩ := h1
  exact ⟨α, hα, by rw [Nat.cast_ofNat, h]; rfl⟩

theorem smul_eq_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La))
    {α : 𝓞 E} (hα : α ∈ l.Mb ^ 2) : ∃ w : Dw.La, α • x2 = ((l.M ^ 2 : ℕ) : 𝓞 E) • w := by
  have h1 := Submodule.smul_mem_smul hα hx
  rw [← Submodule.mul_smul] at h1
  have h2 : l.Mb ^ 2 * (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) ≤
      Ideal.span {((l.M ^ 2 : ℕ) : 𝓞 E)} := by
    rw [mul_left_comm, ← mul_pow, l.prod, Ideal.span_singleton_pow, Nat.cast_pow]
    exact Ideal.mul_le_right
  have h3 := Submodule.smul_mono_left h2 h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, hw.symm⟩

theorem eq_two_smul_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ w : Dw.La, x2 = w + w := by
  have h3 := Submodule.smul_mono_left (Ideal.mul_le_left) hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, by rw [← hw, two_smul]⟩

variable {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem killedBy_iff (I : Ideal (𝓞 E)) (z : Fin g → ℂ) :
    KilledBy Xo I (Φ.e z) ↔ ∀ α ∈ I, tyAct ty α z ∈ Φ.lat := by
  refine forall₂_congr fun α _ => ?_
  rw [← Φ.lin, Φ.e_ker]

theorem levPt_eq {x x2 : Dw.La} (h : x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y.x x2 = levPt Xo y.x x := by
  have h1 := Xo.univ.eta_add (x2 - x) x
  rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
  unfold levPt
  rw [h1]

theorem im_even (mk : Dw.La →+ (Fin g → ℂ)) (hmk : ∀ a, mk a ∈ Φ.lat)
    (hlin : ∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) {u : Fin g → ℂ}
    (hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α u ∈ Φ.lat) {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ k : ℤ, (hermForm Φ.Hm (mk x2) u).im = 2 * k := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr w _
    obtain ⟨α, hα, h⟩ := bar_mem hr
    obtain ⟨k, hk⟩ := ((anFr_semichar _ _ _ _ _ Φ.toAnFr).1 _ (hmk w) _ (hu α hα)).1
    refine ⟨k, ?_⟩
    rw [hlin, Φ.adj, h, tyAct_natCast_mul, Nat.cast_ofNat, hermForm_two_right, ← hk]
    simp
  · rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
    refine ⟨k + k', ?_⟩
    rw [map_add (f := _), hermForm_add_left', Complex.add_im, hk, hk']
    push_cast
    ring

end

end GlobalTheory.AnVal.VtLevel

open GlobalTheory.AnVal.VtLevel in
theorem GlobalTheory.AnVal.rd_vt_levPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ x x2 : Dw.La, x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) → x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) → (KilledBy Xo (l.Mb ^ 2) (Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2)) ∧ Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x) ∧ ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)), IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F → Φ.toAnFr.Rd ((l.M : ℤ) ^ 2) F (fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk x2) fun z => θ ((l.M : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ mk hmk hlin hlev θ hθ x x2 hx2 hx
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hk : ∀ α ∈ l.Mb ^ 2, tyAct ty α (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ∈ Φ.lat := by
    intro α hα
    obtain ⟨w, hw⟩ := smul_eq_of_mem hx2 hα
    rw [map_smul, ← hlin, hw, hlin, tyAct_natCast, smul_smul, Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM),
      one_smul]
    exact hmk w
  have hp : Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x := by
    have hm : x2 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mono_left (Ideal.mul_le_right.trans (Ideal.pow_le_self two_ne_zero)) hx2
    rw [← levPt_eq hx, hlev x2 hm, ← e_natCast_smul, smul_smul]
    congr 2
    field_simp
  refine ⟨⟨(killedBy_iff Φ _ _).2 hk, hp⟩, fun F hF => ?_⟩
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha => (chi_eq_sign E H Dw l Xo c y g ty el Φ a ha).1
  have hMm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
    rw [Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ 2
    refine (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) ?_
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨x', δ, hδ, h2, hok, hpow, hrd⟩ :=
    (rd_vt_and_uu _ _ _ _ _ Φ.toAnFr hχ l.M l.odd y.s θ hθ).1 _ _ F hF (by
      intro t' ht' _
      obtain ⟨z, rfl⟩ := Φ.e_onto t'
      have h1 := (killedBy_iff Φ _ _).1 ht' _ hMm
      rw [tyAct_natCast] at h1
      rw [← e_natCast_smul, Φ.e_ker]
      exact h1)
  set a : Fin g → ℂ := ((l.M : ℂ) ^ 2)⁻¹ • mk x2 with ha
  have hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α (x' - a) ∈ Φ.lat := fun α hα => by
    rw [map_sub]
    exact Φ.lat.sub_mem ((killedBy_iff Φ _ _).1 hok α hα) (hk α hα)
  have hb : (l.M : ℂ) • (x' - a) ∈ Φ.lat := by
    rw [smul_sub]
    apply sub_mem_of_e_eq
    rw [e_natCast_smul, e_natCast_smul, hpow, hp]
  obtain ⟨w, hw⟩ := eq_two_smul_of_mem hx2
  obtain ⟨k, hk2⟩ := l.odd
  have hMa : ((l.M : ℂ) ^ 2) • a = mk w + mk w := by
    rw [ha, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul, hw, map_add (f := _)]
  have hb2 : (l.M : ℂ) • (x' - a) = (2 : ℂ) • (δ - mk w - k • ((l.M : ℂ) • (x' - a))) := by
    have h3 : (l.M : ℂ) • ((l.M : ℂ) • (x' - a)) = (2 : ℂ) • δ - (mk w + mk w) := by
      rw [smul_smul, ← sq, smul_sub, h2, hMa]
    generalize (l.M : ℂ) • (x' - a) = b at h3 ⊢
    rw [hk2] at h3
    funext i
    have := congrFun h3 i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    rw [nsmul_eq_mul]
    push_cast at this
    linear_combination this
  have hχb : Φ.χ ((l.M : ℂ) • (x' - a)) = 1 := by
    rw [hb2]
    exact (anFr_semichar _ _ _ _ _ Φ.toAnFr).2.2 hχ _
      (Φ.lat.sub_mem (Φ.lat.sub_mem hδ (hmk w)) (Φ.lat.nsmul_mem hb k))
  obtain ⟨f1, f2, f3⟩ := fock_laws _ _ _ _ _ Φ.toAnFr
  have hth := (reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 y.s).2.1 θ hθ
  obtain ⟨m, hm⟩ := im_even Φ mk hmk hlin hu hx2
  have hx' : x' = a + (x' - a) := by abel
  rw [hx', f1, f2 l.M (x' - a), f3 θ hth _ hb, hχb] at hrd
  have he : Complex.exp (((((l.M : ℤ) ^ 2 : ℤ) : ℂ)) * Real.pi * Complex.I *
      ((hermForm Φ.Hm a (x' - a)).im : ℂ)) = 1 := by
    have h4 : (hermForm Φ.Hm a (x' - a)).im = ((l.M : ℝ) ^ 2)⁻¹ * (2 * m) := by
      rw [← hm]
      nth_rewrite 1 [ha]
      rw [hermForm_smul_left', ← Complex.im_ofReal_mul]
      push_cast
      rfl
    rw [h4, ← Complex.exp_int_mul_two_pi_mul_I m]
    congr 1
    push_cast
    field_simp
  rw [he] at hrd
  simpa only [_root_.one_mul] using hrd
end

