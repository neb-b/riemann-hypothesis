module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.LevLaws

open GlobalTheory.PrincCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_one_of_norm_one {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ} (hM : 3 ≤ M) (u : E)
    (hint : IsIntegral ℤ ((u - 1) / M)) (hc : u * IsCMField.complexConj E u = 1) : u = 1 := by
  have hM0 : M ≠ 0 := by omega
  by_contra hne
  have hx : (⟨(u - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (u - 1) / (M : E) = 0 := congrArg Subtype.val h
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hM0 (Nat.cast_eq_zero.mp h)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((u - 1) / M)‖ := hσ
  have h1 : ‖σ u‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ u)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ u - 1‖ ≤ 2 := by
    have := norm_sub_le (σ u) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith


set_option maxHeartbeats 800000 in
theorem det_eq_one {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hmu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ) :
    (γ' : Matrix (Fin r) (Fin r) D.host.E).det = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨-, hrat, -, hsur⟩ := (_root_.GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    rw [this, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg0 : (archM V (th k τ) g).det ≠ 0 := by
    have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact right_ne_zero_of_mul_eq_one this.symm
  have hconj : δ.1.map τ.1 * archM V (th k τ) g = archM V (th k τ) g * γ'.1.map τ.1 := by
    rw [← hw τ, ← hδ1 τ, ← hm, ← hm]
    unfold archM
    rw [map_mul, map_mul, hinf]
  have hdd : γ'.1.det = δ.1.det := by
    have := congrArg Matrix.det hconj
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ← RingHom.map_det] at this
    exact τ.1.injective (mul_left_cancel₀ hg0 this).symm
  refine eq_one_of_norm_one hM _ ?_
    (GlobalTheory.CongruenceDet.det_mul_conj (X k).Gm _ (X k).Gm_det ((X k).Γ_stab γ' hγ').1)
  rw [hdd]
  refine isIntegral_trans (A := 𝓞 D.host.E) _
    (GlobalTheory.CongruenceDet.isIntegral_det_sub_one (by omega) Λ' _ g1 g2 fun v hv => ?_)
  obtain ⟨y, hy, e⟩ := g3 v hv
  exact ⟨y, hy, by rw [← Nat.cast_smul_eq_nsmul D.host.E, ← e, add_sub_cancel]⟩


open Module GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore in
set_option maxHeartbeats 1000000 in
theorem laws_of_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → GlobalTheory.FlatCore.Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  intro D j H Dw l Xo c U dict h hF hg
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  refine ⟨⟨?_, h.levA, hg, h.unf, hF, h.xiAbs, h.chiTriv, fun σ hσ k γ hγ => ?_, fun σ hσ a n ha hp hn => ?_,
    GlobalTheory.RankOneDatum.exists_datum_of_rt D H h.host.2.1 h.host.2.2.1⟩, GlobalTheory.FlatRow.isHostField D H h.host.1⟩
  · have e : D.R.r = Dw.p + Dw.q := (h.unf c.F.val.toRingHom rfl).1
    omega
  · obtain ⟨Kf, th, hrk, hK, hth, hD, hu⟩ := h.dictU σ hσ
    exact det_eq_one _ hrk hr (U σ).X (dict σ) Kf th hth hD hu l.M l.three_le hK k γ hγ
  · obtain ⟨hrk, hM⟩ := h.modelW σ hσ
    obtain ⟨Kf, th, hrk', hK, hth, hD, hu⟩ := h.dictU σ hσ
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E H Dw l
      Xo c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (U s)) hr h.levA
      (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf s hs)) σ hσ
      (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
      (fun k γ hγ hc0 => by
        have hc : ∀ x ∈ ((U σ).X k).Λ, ∃ y ∈ ((U σ).X k).Λ,
            Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (l.M : D.host.E) • y := by
          intro x hx
          obtain ⟨y, hy, e⟩ := hc0 x hx
          exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
        obtain ⟨γ', hγ', u, m, hm, hum, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
          (Formalism.L2.PjFree.Unf.ofPj (U σ)) (h.unf σ hσ) h.levA hr k γ hγ hc
        have h1 := root_eq_one _ hrk' hr (U σ).X (dict σ) (fun _ => 1) Kf th hth hD
          ⟨fun _ _ => (one_mul _).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩ _ l.three_le hK k γ γ' hγ' hc u m hm hum he
        rw [h1, one_smul] at he
        exact Units.ext he ▸ hγ')
      a n ha (fun τ _ h0 => hp τ _ (by omega)) hn (fun k => h.chiTriv σ hσ a n ha k)
    intro P hP
    exact key ⟨hP.1, hP.2⟩

end GlobalTheory.LevLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlace
section
open NumberField IsDedekindDomain

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem norm_map_le_one_of_isIntegral_int {F C : Type} [CommRing F] [NormedField C] [IsUltrametricDist C] (f : F →+* C) {x : F}
    (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (f x) := hx.map f.toIntAlgHom
  have := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hy.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_le_one_iff_integral_at : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  intro K _ _ l _ w e0 hw x
  constructor
  · intro hx
    obtain ⟨n, d, h | h⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact h⟩
    · by_cases hn : n ∈ w.asIdeal
      · exfalso
        refine d.2 ((hw d).2 ?_)
        have h1 : ‖e0 ((d : 𝓞 K) : K)‖ = ‖e0 x‖ * ‖e0 (n : K)‖ := by
          have : ((d : 𝓞 K) : K) = x * (n : K) := h.symm
          rw [this, map_mul, norm_mul]
        rw [h1]
        have h2 : ‖e0 (n : K)‖ < 1 := (hw n).1 hn
        calc ‖e0 x‖ * ‖e0 (n : K)‖ ≤ 1 * ‖e0 (n : K)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact h2
      · exact ⟨n, hn, d, by rw [mul_comm]; exact h⟩
  · rintro ⟨s, hs, r, hr⟩
    have hs1 : 1 ≤ ‖e0 (s : K)‖ := by
      by_contra h
      exact hs ((hw s).2 (lt_of_not_ge h))
    have hr1 : ‖e0 (r : K)‖ ≤ 1 := norm_map_le_one_of_isIntegral_int e0 r.isIntegral_coe
    have h1 : ‖e0 (s : K)‖ * ‖e0 x‖ ≤ 1 := by rw [← norm_mul, ← map_mul, hr]; exact hr1
    nlinarith [norm_nonneg (e0 x)]

end GlobalTheory.FrameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvection
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory

theorem one_add_strictLower_mem_closure_transvection (R : Type) [CommRing R] (N : ℕ)
    (c : Matrix (Fin N) (Fin N) R) (hc : ∀ a b, a ≤ b → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  have key : ∀ S : Finset (Fin N × Fin N), ∀ c : Matrix (Fin N) (Fin N) R,
      (∀ a b, a ≤ b → c a b = 0) → (∀ a b, (a, b) ∉ S → c a b = 0) →
      1 + c ∈ Submonoid.closure
        {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
    intro S
    induction S using Finset.induction_on_max_value (fun p : Fin N × Fin N => p.2) with
    | empty =>
      intro c _ h
      have : c = 0 := by
        ext a b
        simpa using h a b (by simp)
      rw [this, add_zero]
      exact Submonoid.one_mem _
    | insert p S hp hmax ih =>
      intro c hc hS
      obtain ⟨a, b⟩ := p
      by_cases hab : a ≤ b
      · refine ih c hc fun i j hij => ?_
        by_cases h : (i, j) = (a, b)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact hc _ _ hab
        · exact hS i j (by simp only [Finset.mem_insert, not_or]; exact ⟨h, hij⟩)
      · have hba : b < a := lt_of_not_ge hab
        set c' : Matrix (Fin N) (Fin N) R := c - Matrix.single a b (c a b) with hc'
        have h2 : ∀ i j, (i, j) ∉ S → c' i j = 0 := by
          intro i j hij
          by_cases h : (i, j) = (a, b)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            simp [hc']
          · have h0 : c i j = 0 :=
              hS i j (by simp only [Finset.mem_insert, not_or]; exact ⟨h, hij⟩)
            have h' : ¬ (a = i ∧ b = j) := by
              rintro ⟨rfl, rfl⟩; exact h rfl
            simp [hc', h0, Matrix.single_apply, h']
        have h1 : ∀ i j, i ≤ j → c' i j = 0 := by
          intro i j hij
          have h' : ¬ (a = i ∧ b = j) := by
            rintro ⟨rfl, rfl⟩; exact hab hij
          simp [hc', hc i j hij, Matrix.single_apply, h']
        have h3 : c' * Matrix.single a b (c a b) = 0 := by
          ext i j
          have hz : c' i a = 0 := by
            apply h2
            intro hmem
            exact absurd (hmax _ hmem) (not_le.mpr hba)
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun e _ => ?_
          by_cases he : a = e
          · subst he; simp [hz]
          · simp [Matrix.single_apply, he]
        have h4 : 1 + c = (1 + c') * Matrix.transvection a b (c a b) := by
          rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, h3, add_zero, hc']
          abel
        rw [h4]
        exact Submonoid.mul_mem _ (ih c' h1 h2)
          (Submonoid.subset_closure ⟨a, b, _, hba.ne', rfl⟩)
  exact key Finset.univ c hc (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvection
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.UpperTransvection

theorem upper_mem_closure (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R)
    (hc : ∀ a b, b ≤ a → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  set S := Submonoid.closure
      {M : Matrix (Fin N) (Fin N) R | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}
  suffices key : ∀ n : ℕ, ∀ c : Matrix (Fin N) (Fin N) R, (∀ a b, b ≤ a → c a b = 0) →
      (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0).card ≤ n → 1 + c ∈ S from
    key _ c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro c _ hcard
    have hc0 : c = 0 := by
      ext i j
      by_contra h
      have : (i, j) ∈ (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) := by
        simpa using h
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard] at this
    subst hc0
    simpa using S.one_mem
  | succ n ih =>
    intro c hc hcard
    set T := (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) with hT
    rcases T.eq_empty_or_nonempty with hE | hne
    · exact ih c hc (by rw [← hT, hE]; simp)
    obtain ⟨p, hpT, hpmin⟩ := Finset.exists_min_image T (fun p => p.1) hne
    obtain ⟨a, b⟩ := p
    have hab : c a b ≠ 0 := by simpa [hT] using hpT
    have hlt : a < b := by
      by_contra h
      exact hab (hc a b (not_lt.mp h))

    have hcol : ∀ i, c i a = 0 := by
      intro i
      by_contra h
      have hi : (i, a) ∈ T := by simpa [hT] using h
      have h1 := hpmin _ hi
      have h2 : a ≤ i := h1
      exact h (hc i a h2)
    set r := c a b
    set c' := c - Matrix.single a b r with hc'
    have hc'_apply : ∀ i j, c' i j = if i = a ∧ j = b then 0 else c i j := by
      intro i j
      simp only [hc', Matrix.sub_apply, Matrix.single_apply]
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h; simp [r]
      · have h' : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
        simp [h, h']
    have hc'up : ∀ i j, j ≤ i → c' i j = 0 := by
      intro i j hji
      rw [hc'_apply]; split_ifs
      · rfl
      · exact hc i j hji
    have hT' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0) ⊆ T.erase (a, b) := by
      intro q hq
      obtain ⟨i, j⟩ := q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hc'_apply] at hq
      split_ifs at hq with h
      · exact absurd rfl hq
      · rw [Finset.mem_erase]
        refine ⟨?_, by simpa [hT] using hq⟩
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact h heq
    have hcard' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0).card ≤ n := by
      have := Finset.card_le_card hT'
      rw [Finset.card_erase_of_mem hpT] at this
      omega
    have hmem' : 1 + c' ∈ S := ih c' hc'up hcard'
    have hcolz : c' * Matrix.single a b r = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [hc'_apply]; split_ifs
        · simp
        · rw [hcol]; simp
      · simp
    have heq : 1 + c = (1 + c') * Matrix.transvection a b r := by
      rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hcolz, add_zero, hc']
      abel
    rw [heq]
    refine S.mul_mem hmem' (Submonoid.subset_closure ⟨a, b, r, hlt.ne, rfl⟩)

end GlobalTheory.UpperTransvection
end

