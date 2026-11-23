module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L2OneEqIntegralFundamentalDomainDivVolume
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPT

open MeasureTheory

theorem Hf_add_smul_left {κ : Type} [Fintype κ] (c : ℂ) (v w u : EuclideanSpace ℂ κ) :
    I2.Hf (v + c • w) u = I2.Hf v u + c * I2.Hf w u := by
  unfold I2.Hf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem Hf_neg_right {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf v (-w) = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem Hf_neg_left {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf (-v) w = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem cexp_pi_int (k : ℤ) : cexp (Real.pi * I * (k : ℂ)) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
  have h : (Real.pi : ℂ) * I * (k : ℂ) = ((Real.pi * k : ℝ) : ℂ) * I := by push_cast; ring
  have hs : Real.sin (Real.pi * k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hs]
  simp

theorem l2_one_eq_integral_fundamentalDomain_div_volume {E : Type} [Field E] [NumberField E] {g : ℕ} (T : I2.PT E)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ)
    (hs : (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1)
    (A : AddSubgroup (Fin g → ℂ)) (hL : ∀ z, z ∈ A ↔ ψ z ∈ T.L) (Fd : Set (Fin g → ℂ))
    (hFd : IsAddFundamentalDomain A Fd volume) :
    T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re)) / (volume Fd).toReal := by
  classical

  have hper : ∀ (a : A) (z : Fin g → ℂ),
      ‖θ (a +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ (a +ᵥ z)) (ψ (a +ᵥ z))).re) =
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    intro a z
    have ha : ψ a ∈ T.L := (hL a).1 a.2
    obtain ⟨-, hq⟩ := hs
    have h := hq (fun _ => ψ a) (fun _ => ha) (fun _ => ψ z)
    simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
      _root_.one_mul, map_add, LinearEquiv.symm_apply_apply] at h
    have hε : ‖((T.eps (ψ a) : ℤ) : ℂ)‖ = 1 := by
      rcases T.eps_pm _ ha with h1 | h1 <;> simp [h1]
    have hv : (a +ᵥ z : Fin g → ℂ) = z + a := by
      change (a : Fin g → ℂ) + z = z + a
      exact add_comm _ _
    have hre : ((Real.pi : ℂ) * I2.Hf (ψ z) (ψ a) + (Real.pi : ℂ) * I2.Hf (ψ a) (ψ a) / 2).re =
        Real.pi * (I2.Hf (ψ z) (ψ a)).re + Real.pi * (I2.Hf (ψ a) (ψ a)).re / 2 := by
      simp [Complex.add_re, Complex.div_ofNat_re]
    rw [hv, h, map_add (f := _), GlobalTheory.EtaAn.ThetaTorus.Hf_add_re, norm_mul, norm_mul, hε, _root_.one_mul,
      Complex.norm_exp, hre, mul_pow, sq (Real.exp _), ← Real.exp_add,
      mul_comm (Real.exp _) (‖θ z‖ ^ 2), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring

  let ψR : (Fin g → ℂ) ≃L[ℝ] I2.Vsp T.dim := (ψ.restrictScalars ℝ).toContinuousLinearEquiv
  have hψR : ∀ z, ψR z = ψ z := fun z => rfl
  let eR : (Fin g → ℂ) ≃L[ℝ] (Fin 1 → I2.Vsp T.dim) :=
    ψR.trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (I2.Vsp T.dim)).symm
  have heR : ∀ z, eR z = fun _ => ψ z := fun z => rfl

  have hl2 : T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      ⨍ z in ψ ⁻¹' ZSpan.fundamentalDomain T.b,
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    have hset : eR ⁻¹' T.fd 1 = ψ ⁻¹' ZSpan.fundamentalDomain T.b := by
      ext z
      simp [I2.PT.fd, heR]
    unfold I2.PT.l2
    rw [GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv volume volume eR, hset]
    congr 1
    funext z
    simp [I2.PT.ptN2, I2.HC, heR]

  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving ψR volume volume :=
    ⟨ψR.continuous.measurable.aemeasurable, MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩

  have hfd0 : IsAddFundamentalDomain A (ψ ⁻¹' ZSpan.fundamentalDomain T.b) volume := by
    have h0 := ZSpan.isAddFundamentalDomain T.b (volume : Measure (I2.Vsp T.dim))
    refine h0.preimage_of_equiv hqmp
      (e := fun y => (⟨ψ.symm y, (hL _).2 (by simp only [LinearEquiv.apply_symm_apply]; exact y.2)⟩ : A)) ⟨?_, ?_⟩ ?_
    · intro y y' hyy
      have := congrArg Subtype.val hyy
      exact Subtype.ext (ψ.symm.injective this)
    · intro a
      refine ⟨⟨ψ a, (hL a).1 a.2⟩, ?_⟩
      ext1
      simp
    · intro y z
      change ψ (ψ.symm (y : I2.Vsp T.dim) + z) = (y : I2.Vsp T.dim) + ψ z
      simp
  have hcA : Countable A := by
    have : Countable (Submodule.span ℤ (Set.range T.b)) := inferInstance
    refine Function.Injective.countable
      (f := fun a : A => (⟨ψ a, (hL a).1 a.2⟩ : Submodule.span ℤ (Set.range T.b))) ?_
    intro a a' h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  rw [hl2, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, hfd0.measure_eq hFd,
    hfd0.setIntegral_eq hFd hper, smul_eq_mul, div_eq_inv_mul]

theorem theta_on_torus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (w : 𝓞 E) (L : Lt E r) (x : Frame X.Ψ r) (t : ℝ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (e : Fin g ≃ I2.Idx T.dim), IsSympl X bas → x ∈ X.dom → (w : E) + cc (w : E) = 1 → (T.r = r ∧ (∀ z z', I2.Hf (ψ z) (ψ z') = hx X bas idx x z z') ∧ (∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u)) ∧ (∀ (a : 𝓞 E) u, ψ (pv X idx x ((a : E) • u)) = I2.act a (ψ (pv X idx x u))) ∧ (∀ ga ∈ T.L, (T.eps ga : ℝ) = Real.cos (Real.pi * (I2.Hf ga (I2.act w ga)).im)) ∧ (∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = ((Real.sqrt t : ℝ) : ℂ) • EuclideanSpace.single (e j) (1 : ℂ))) → (∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx (w : E) x L θ → (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ (MeanOne X bas idx x L θ → T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) = 1)) ∧ (∀ (n k : ℕ) (th : Fin n → (Fin g → ℂ) → ℂ) (a z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x k (a b) (th b) (z b) = T.U k (fun b => -ψ (a b)) (fun v => ∏ b, th b (ψ.symm (v b))) (fun b => ψ (z b))) ∧ ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
  intro E _ _ _ r X g bas idx w L x t T ψ e hsy hxd hw hT
  obtain ⟨-, hH, hL, hact, heps, -⟩ := hT
  have hlaws := hx_laws E r X g bas idx 0 hsy ⟨0, rfl⟩ x hxd
  have hpvL : ∀ u ∈ L, ψ (pv X idx x u) ∈ T.L := fun u hu => (hL _).2 ⟨u, hu, rfl⟩

  have hsign : ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
    intro u hu
    have hmem := hpvL u hu
    obtain ⟨k, hk⟩ := T.integral _ _ hmem (T.stable w _ hmem)
    have him : (I2.Hf (ψ (pv X idx x u)) (I2.act w (ψ (pv X idx x u)))).im =
        (EF X u ((w : E) • u) : ℝ) := by
      rw [← hact, hH]
      exact hlaws.2.2.1 u _
    have hq : ((EF X u ((w : E) • u) : ℚ) : ℂ) = (k : ℂ) := by
      have h1 : ((EF X u ((w : E) • u) : ℚ) : ℝ) = (k : ℝ) := by rw [← him, hk]
      have h2 := congrArg (fun s : ℝ => (s : ℂ)) h1
      push_cast at h2
      exact h2
    have hs1 : ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
      have h1 := heps _ hmem
      rw [hk] at h1
      rw [← h1]
      norm_cast
    unfold eps1
    rw [hq, cexp_pi_int, hs1]

  have hHadd : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      I2.Hf (ψ z) (ψ a) + I2.Hf (ψ a) (ψ a) / 2 := by
    intro z a
    rw [← hH, map_add (f := _), map_smul, Hf_add_smul_left]
    ring
  have hHadd' : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      hx X bas idx x z a + hx X bas idx x a a / 2 := by
    intro z a
    rw [hHadd, hH, hH]

  have hthper : ∀ θ, IsTheta1 X bas idx (w : E) x L θ → ∀ u ∈ L, ∀ z,
      θ (z + pv X idx x u) = (T.eps (ψ (pv X idx x u)) : ℂ) *
        cexp (Real.pi * I2.Hf (ψ z) (ψ (pv X idx x u)) +
          Real.pi * I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u)) / 2) * θ z := by
    intro θ hθ u hu z
    obtain ⟨-, hθp⟩ := hθ
    have h := congrFun (hθp u hu) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hHadd, hsign u hu, Nat.cast_one, _root_.one_mul] at h
    set ε : ℂ := ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) with hεdef
    set P := I2.Hf (ψ z) (ψ (pv X idx x u))
    set Q := I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u))
    have hε : ε * ε = 1 := by
      rcases T.eps_pm _ (hpvL u hu) with h1 | h1 <;> simp [hεdef, h1]
    have hc : cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2))) = 1 := by
      rw [← Complex.exp_add, show (Real.pi : ℂ) * P + Real.pi * Q / 2 + -(Real.pi * (P + Q / 2)) = 0 by ring,
        Complex.exp_zero]
    rw [← h]
    linear_combination (-(cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2)))) *
      θ (z + pv X idx x u)) * hε - θ (z + pv X idx x u) * hc

  have hsec : ∀ θ, IsTheta1 X bas idx (w : E) x L θ →
      (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 := by
    intro θ hθ
    show Differentiable ℂ (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∧ _
    refine ⟨?_, ?_⟩
    · have hd : Differentiable ℂ (fun y : I2.Vsp T.dim => ψ.symm y) := by
        simpa using (LinearMap.toContinuousLinearMap
          (ψ.symm : I2.Vsp T.dim →ₗ[ℂ] (Fin g → ℂ))).differentiable
      obtain ⟨hθd, -⟩ := hθ
      exact hθd.comp (hd.comp (differentiable_apply 0))
    · intro gam hgam v
      obtain ⟨u, hu, hgu⟩ := (hL (gam 0)).1 (hgam 0)
      have h := hthper θ hθ u hu (ψ.symm (v 0))
      simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
        _root_.one_mul, map_add]
      rw [hgu, LinearEquiv.symm_apply_apply, h, LinearEquiv.apply_symm_apply]
  refine ⟨fun θ hθ => ⟨hsec θ hθ, fun hM => ?_⟩, ?_, hsign⟩
  · obtain ⟨A, Fd, hA, hFd, hmean⟩ := hM
    have hAL : ∀ z, z ∈ A ↔ ψ z ∈ T.L := by
      intro z
      rw [hA z, hL]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, h⟩
        exact ⟨v, hv, ψ.injective h⟩
    rw [l2_one_eq_integral_fundamentalDomain_div_volume T ψ θ (hsec θ hθ) A hAL Fd hFd]
    simpa only [hH] using hmean
  · intro n k th a z
    simp only [fock, I2.PT.U, Pi.sub_apply, sub_neg_eq_add, map_add (f := _), LinearEquiv.symm_apply_apply]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    simp only [I2.HC, Hf_neg_right, Hf_neg_left, neg_neg, hH, hHadd']
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.Dict.ThetaPT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThetaIsotropy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Tate

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_sum (I : TateIso Dw k Q act e) (m : ℕ) (hm : 0 < m) {n : ℕ} (a : Fin n → Dw.La) :
    I.ev m (∑ j, a j) = ∏ j, I.ev m (a j) := by
  have h0 : I.ev m 0 = 1 := (I.ker m hm 0).2 ⟨0, (smul_zero _).symm⟩
  let f : Multiplicative Dw.La →* Q :=
    { toFun := fun x => I.ev m x.toAdd, map_one' := h0, map_mul' := fun x y => I.add m _ _ }
  exact map_prod f (fun j => Multiplicative.ofAdd (a j)) Finset.univ

theorem dvd_EF_of_killed (m j : ℕ) (a b : Dw.La) (ha : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • a))
    (hb : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • b)) : (m : ℤ) ∣ Dw.EF a b := by
  have cop : l.Mb ^ j ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ j = ⊤ :=
    Ideal.sup_pow_eq_top' (Ideal.pow_sup_eq_top l.coprime)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (cop.ge (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨a', ha'⟩ := ha r hr
  obtain ⟨b', hb'⟩ := hb p hp
  have e₁ : Dw.EF a b = Dw.EF a (p • b) + Dw.EF (r • a) b := by
    rw [Dw.adj, ← map_add (f := _), ← add_smul]
    have : p + H.bar r = 1 := hpq
    rw [this, one_smul]
  rw [e₁, ha', hb', map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

end Tate

variable (Xo : Moduli Dw l) {B : Type} [CommRing B] (x0 : Sp B ⟶ Xo.X)

noncomputable def bc {K : Type} [CommRing K] (χ : B →+* K) : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 :=
  Over.homMk (spMap χ) rfl

theorem unit_eq_one (hL : Laws) (N : ℕ) (hN : 0 < N) (u : Γ((ptO Xo x0).left, ⊤)ˣ) (hu : u ^ (N ^ 2) = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K),
      Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom u = 1) : u = 1 := by
  let i₀ := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  have hi : Function.Injective i₀.hom := (ConcreteCategory.bijective_of_isIso i₀).1
  have hU : IsUnit ((N ^ 2 : ℕ) : B) := by
    have := ((baseKA l).unit (N ^ 2) (pow_pos hN 2)).map (Spec.preimage (x0 ≫ Xo.s)).hom
    rwa [map_natCast] at this
  have key := (_root_.GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN).2.2 B (i₀.hom u.val) (N ^ 2) hU
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]) (fun K _ _ χ => by
      have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
      have e := congrArg (fun φ => φ.hom u.val) nat
      have h1 : (spMap χ).appTop.hom u.val = 1 := congrArg Units.val (h K χ)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [← e]
      exact (congrArg _ h1).trans (map_one _))
  exact Units.ext (hi (key.trans (map_one _).symm))

theorem exists_tate (hL : Laws) (N : ℕ) (hN : 0 < N) (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K) :
    ∃ I : TateIso Dw K (ptO Xo (spMap χ ≫ x0) ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
        (fun n g g' c => WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c)),
      ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 →
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → ∀ a b, I.ev (N ^ 2) a = bc Xo x0 χ ≫ x →
        I.ev (N ^ 2) b = bc Xo x0 χ ≫ y →
        Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom e = unitOn (I.ζ (N ^ 2) ^ Dw.EF a b) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K (spMap χ ≫ x0) (Spec.preimage ((spMap χ ≫ x0) ≫ Xo.s)).hom
    (Spec.map_preimage _).symm
  refine ⟨I, fun x y e hx hy he a b ha hb => ?_⟩
  obtain ⟨W₁, W₂, -⟩ := _root_.GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN
  have h₁ := W₁ _ _ (bc Xo x0 χ) x y e hx hy he
  have h₂ := I.isom (N ^ 2) (pow_pos hN 2) a b
  rw [ha, hb, Nat.cast_pow] at h₂
  obtain ⟨e₀, -, -, hu⟩ := W₂ _ (bc Xo x0 χ ≫ x) (bc Xo x0 χ ≫ y)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact (hu _ h₁).trans (hu _ h₂).symm

theorem unitOn_prod {K : Type} [CommRing K] {n : ℕ} (c : Fin n → Kˣ) : ∏ b, unitOn (c b) = unitOn (∏ b, c b) :=
  (map_prod (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom) c Finset.univ).symm

theorem prod_zpow_eq {U : Type} [CommGroup U] (z : U) {n : ℕ} (c : Fin n → ℤ) : ∏ b, z ^ c b = z ^ ∑ b, c b :=
  (map_prod (zpowersHom U z) (fun b => Multiplicative.ofAdd (c b)) Finset.univ).symm

theorem unitOn_one {K : Type} [CommRing K] : unitOn (1 : Kˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) : h ≫ (List.ofFn x).prod = ∏ j, h ≫ x j := by
  rw [List.prod_ofFn]
  let f : (T ⟶ G) →* (T' ⟶ G) :=
    { toFun := fun g => h ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  exact map_prod f x Finset.univ

end ThetaIsotropy


open ThetaIsotropy in
theorem zh_isotropic_and_half_isotropic : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → (∀ (a a' : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (e : Fin n → Γ((ptO Xo x0).left, ⊤)ˣ), InZh Xo Λ N a → InZh Xo Λ N a' → (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (a b) (a' b) (e b)) → ∏ b, e b = 1) ∧ ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (j : ℕ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → KilledBy Xo (l.Mb ^ j) x → KilledBy Xo (l.Mb ^ j) y → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y 1 := by
  intro hL E _ _ _ H Dw l Xo B _ x0 n Λ N hΛ hN hle
  have hN2 : 0 < N ^ 2 := pow_pos hN 2
  obtain ⟨-, W₂, -⟩ := _root_.GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN
  have tors : ∀ {K : Type} [CommRing K] (χ : B →+* K) {x : ptO Xo x0 ⟶ Xo.univ.t.G}, x ^ (N ^ 2) = 1 →
      (ThetaIsotropy.bc Xo x0 χ ≫ x) ^ (N ^ 2) = 1 := fun χ x hx => by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  refine ⟨fun a a' e ha ha' he => ?_, fun x y j hx hy kx ky => ?_⟩
  · refine ThetaIsotropy.unit_eq_one Xo x0 hL N hN _ ?_ fun K _ _ χ => ?_
    · rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun b _ => ?_
      obtain ⟨e₀, -, h₀, hu⟩ := W₂ _ (a b) (a' b) (ha.1 b) (ha'.1 b)
      rw [hu _ (he b), h₀]
    · obtain ⟨I, hI⟩ := ThetaIsotropy.exists_tate Xo x0 hL N hN K χ
      choose v hv using fun b => (I.onto _ hN2 _).1 (tors χ (ha.1 b))
      choose v' hv' using fun b => (I.onto _ hN2 _).1 (tors χ (ha'.1 b))
      have lat : ∀ {a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)} {v : Fin n → Dw.La}, InZh Xo Λ N a →
          (∀ b, I.ev (N ^ 2) (v b) = ThetaIsotropy.bc Xo x0 χ ≫ a b) →
          ∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
            ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
              ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • v j) := fun {a v} ha hv mu hmu cm hcm i => by
        refine (I.ker _ hN2 _).1 ?_
        have h₁ := congrArg (ThetaIsotropy.bc Xo x0 χ ≫ ·) (ha.2 mu hmu cm hcm i)
        simp only [MonObj.comp_one] at h₁
        rw [ThetaIsotropy.comp_prod] at h₁
        rw [ThetaIsotropy.ev_sum I _ hN2, ← h₁]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [I.lin, hv, Category.assoc]
      have hd := _root_.GlobalTheory.sq_dvd_sum_EF_of_killed E H Dw n Λ N hΛ hN hle v v' (lat ha hv) (lat ha' hv')
      rw [map_prod, Finset.prod_congr rfl fun b _ => hI _ _ _ (ha.1 b) (ha'.1 b) (he b) _ _ (hv b) (hv' b)]
      refine (ThetaIsotropy.unitOn_prod _).trans ?_
      rw [ThetaIsotropy.prod_zpow_eq,
        ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 (by rwa [Nat.cast_pow]), ThetaIsotropy.unitOn_one]
  · obtain ⟨e, he, h₀, -⟩ := W₂ _ x y hx hy
    suffices e = 1 by rwa [this] at he
    refine ThetaIsotropy.unit_eq_one Xo x0 hL N hN _ h₀ fun K _ _ χ => ?_
    obtain ⟨I, hI⟩ := ThetaIsotropy.exists_tate Xo x0 hL N hN K χ
    obtain ⟨v, hv⟩ := (I.onto _ hN2 _).1 (tors χ hx)
    obtain ⟨v', hv'⟩ := (I.onto _ hN2 _).1 (tors χ hy)
    have lat : ∀ {x : ptO Xo x0 ⟶ Xo.univ.t.G} {v : Dw.La}, KilledBy Xo (l.Mb ^ j) x →
        I.ev (N ^ 2) v = ThetaIsotropy.bc Xo x0 χ ≫ x → ∀ c ∈ l.Mb ^ j, Dw.ModN (N ^ 2) (c • v) := fun {x v} kx hv c hc => by
      refine (I.ker _ hN2 _).1 ?_
      rw [I.lin, hv, Category.assoc, kx c hc, MonObj.comp_one]
    have hd := ThetaIsotropy.dvd_EF_of_killed (N ^ 2) j v v' (lat kx hv) (lat ky hv')
    rw [hI _ _ _ hx hy he _ _ hv hv', ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 hd]
    exact ThetaIsotropy.unitOn_one

end GlobalTheory
end

