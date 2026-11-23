module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfRows
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ScalarTorus

open GlobalTheory.PeriodTorus

private theorem mem_lat_basis_map_iff {J K : Type} [Fintype J] (b : Module.Basis K ℝ (EuclideanSpace ℂ J))
    (f : EuclideanSpace ℂ J ≃ₗ[ℝ] EuclideanSpace ℂ J) (x : EuclideanSpace ℂ J) :
    x ∈ I2.lat (b.map f) ↔ f.symm x ∈ I2.lat b := by
  let fz : EuclideanSpace ℂ J ≃ₗ[ℤ] EuclideanSpace ℂ J := f.toAddEquiv.toIntLinearEquiv
  have hr : Set.range (b.map f) = fz '' Set.range b := by
    rw [Module.Basis.coe_map, Set.range_comp]
    congr 1
  show x ∈ Submodule.span ℤ (Set.range (b.map f)) ↔ f.symm x ∈ Submodule.span ℤ (Set.range b)
  rw [hr, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv]
  rfl


open TorusAtAssembly in
theorem exists_torusOf_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (t : ℝ) (row : Fin g → ℕ), 0 < t → IsTypeFn H D.p D.q ty → IsPeriod D ty Pm → (∀ a b, (hermForm (Matrix.diagonal fun _ => (t : ℂ)) (Pm a) (Pm b)).im = D.EF a b) → (∀ j, row j < D.mult (ty j)) → (∀ j j', ty j = ty j' → row j = row j' → j = j') → ∃ (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsTorusOf D ty Pm (Matrix.diagonal fun _ => (t : ℂ)) T ψ ∧ ∀ j, ∃ h : row j < T.dim (ty j), ψ (Pi.single j 1) = open Classical in (Real.sqrt t : ℂ) • EuclideanSpace.single (⟨ty j, ⟨row j, h⟩⟩ : I2.Idx T.dim) (1 : ℂ) := by
  classical
  intro E _ _ _ H D g ty Pm t row ht hty hP hE hrow hinj
  have hform : ∀ z w : Fin g → ℂ, hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w =
      ∑ j, z j * ((t : ℂ) * (starRingEnd ℂ) (w j)) := by
    intro z w
    simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
  have hH : (Matrix.diagonal fun _ : Fin g => (t : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      show star _ = _
      funext i
      simp)
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Matrix.diagonal fun _ : Fin g => (t : ℂ)) z z).re := by
    intro z hz
    rw [hform]
    have hterm : ∀ j, z j * ((t : ℂ) * (starRingEnd ℂ) (z j)) = ((t * Complex.normSq (z j) : ℝ) : ℂ) := by
      intro j
      rw [Complex.ofReal_mul, ← Complex.mul_conj]
      ring
    simp only [hterm, ← Complex.ofReal_sum, Complex.ofReal_re]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
    exact Finset.sum_pos' (fun i _ => mul_nonneg ht.le (Complex.normSq_nonneg _))
      ⟨j, Finset.mem_univ _, mul_pos ht (Complex.normSq_pos.2 hj)⟩
  obtain ⟨T₀, ψ₀, hr, hdim, hHf, hL, hact, heps⟩ := exists_torusOf E H D g ty Pm _ hty hP hH hpos hE
  have hrow' : ∀ j, row j < T₀.dim (ty j) := by
    intro j
    rw [hdim]
    exact hrow j
  let f : Fin g → I2.Idx T₀.dim := fun j => ⟨ty j, ⟨row j, hrow' j⟩⟩
  have hfinj : Function.Injective f := by
    have hc : Function.Injective ((fun i : I2.Idx T₀.dim => (i.1, (i.2 : ℕ))) ∘ f) := by
      intro j j' h
      simp only [Function.comp, f, Prod.mk.injEq] at h
      exact hinj j j' h.1 h.2
    exact Function.Injective.of_comp hc
  have hcard : Fintype.card (Fin g) = Fintype.card (I2.Idx T₀.dim) := by
    have h1 : Fintype.card (Fin g) = ∑ τ, Fintype.card {i // ty i = τ} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv ty).symm
    rw [h1, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.card_fin, hdim τ, ← Nat.card_eq_fintype_card, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult]
    split_ifs with h
    · exact (hty τ).1 h
    · exact (hty τ).2 h
  let e : Fin g ≃ I2.Idx T₀.dim :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩)
  have he_ty : ∀ i, ty (e.symm i) = i.1 := by
    intro i
    exact congrArg Sigma.fst (e.apply_symm_apply i)
  have hs2 : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = t := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  let ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T₀.dim :=
    { toFun := fun z => WithLp.toLp 2 (fun i => (Real.sqrt t : ℂ) * z (e.symm i))
      invFun := fun v j => v (e j) / (Real.sqrt t : ℂ)
      map_add' := by
        intro z w
        ext i
        simp [mul_add]
      map_smul' := by
        intro c z
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
        ring
      left_inv := by
        intro z
        funext j
        simp only [Equiv.symm_apply_apply]
        field_simp
      right_inv := by
        intro v
        ext i
        simp only [Equiv.apply_symm_apply]
        field_simp }
  have hψ : ∀ z i, ψ z i = (Real.sqrt t : ℂ) * z (e.symm i) := fun z i => rfl
  have hψHf : ∀ z w, I2.Hf (ψ z) (ψ w) = hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w := by
    intro z w
    rw [hform]
    unfold I2.Hf
    simp only [hψ]
    refine (e.symm.sum_comp (fun j => (Real.sqrt t : ℂ) * z j * (starRingEnd ℂ) ((Real.sqrt t : ℂ) * w j))).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (z j * (starRingEnd ℂ) (w j)) * hs2
  have hψact : ∀ (α : 𝓞 E) z, ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z) := by
    intro α z
    ext i
    simp only [hψ, I2.act, PiLp.toLp_apply]
    rw [he_ty]
    ring
  let U : I2.Vsp T₀.dim ≃ₗ[ℂ] I2.Vsp T₀.dim := ψ₀.symm.trans ψ
  have hUHf : ∀ x y, I2.Hf (U x) (U y) = I2.Hf x y := by
    intro x y
    have h1 := hHf (ψ₀.symm x) (ψ₀.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [h1, ← hψHf]
    rfl
  have hUact : ∀ (α : 𝓞 E) x, U (I2.act α x) = I2.act α (U x) := by
    intro α x
    obtain ⟨z, rfl⟩ := ψ₀.surjective x
    rw [← hact α z]
    simp only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact hψact α z
  have hUsymm_act : ∀ (α : 𝓞 E) x, U.symm (I2.act α x) = I2.act α (U.symm x) := by
    intro α x
    apply U.injective
    rw [hUact, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hUsymmHf : ∀ x y, I2.Hf (U.symm x) (U.symm y) = I2.Hf x y := by
    intro x y
    rw [← hUHf, U.apply_symm_apply, U.apply_symm_apply]
  have hmem : ∀ x, x ∈ I2.lat (T₀.b.map (U.restrictScalars ℝ)) ↔ U.symm x ∈ I2.lat T₀.b :=
    fun x => mem_lat_basis_map_iff _ _ x
  let T' : I2.PT E :=
    { dim := T₀.dim
      r := T₀.r
      dim_conj := T₀.dim_conj
      b := T₀.b.map (U.restrictScalars ℝ)
      stable := by
        intro α x hx
        rw [hmem] at hx ⊢
        rw [hUsymm_act]
        exact T₀.stable α _ hx
      integral := by
        intro x y hx hy
        rw [hmem] at hx hy
        rw [← hUsymmHf]
        exact T₀.integral _ _ hx hy
      perfect := by
        intro φ
        let m : I2.lat T₀.b →+ I2.lat (T₀.b.map (U.restrictScalars ℝ)) :=
          AddMonoidHom.mk' (fun y => ⟨U y, (hmem _).2 (by rw [U.symm_apply_apply]; exact y.2)⟩)
            (by
              intro a b
              apply Subtype.ext
              simp)
        obtain ⟨x₀, hx₀, hφ⟩ := T₀.perfect (φ.comp m)
        refine ⟨U x₀, (hmem _).2 (by rw [U.symm_apply_apply]; exact hx₀), fun y => ?_⟩
        have hy : U.symm (y : I2.Vsp T₀.dim) ∈ I2.lat T₀.b := (hmem _).1 y.2
        have h1 := hφ ⟨_, hy⟩
        have h2 : m ⟨_, hy⟩ = y := Subtype.ext (U.apply_symm_apply _)
        rw [AddMonoidHom.comp_apply, h2] at h1
        rw [h1, ← hUHf, U.apply_symm_apply]
      eps := fun v => T₀.eps (U.symm v)
      eps_pm := by
        intro x hx
        rw [hmem] at hx
        exact T₀.eps_pm _ hx
      eps_add := by
        intro x hx y hy
        rw [hmem] at hx hy
        rw [map_add (f := _), T₀.eps_add _ hx _ hy, hUsymmHf]
      eps_iso := by
        intro x hx h
        rw [hmem] at hx
        exact T₀.eps_iso _ hx fun α => by rw [← hUsymm_act, hUsymmHf]; exact h α }
  have hTL : ∀ v, v ∈ T'.L ↔ U.symm v ∈ I2.lat T₀.b := hmem
  have hTeps : ∀ v, T'.eps v = T₀.eps (U.symm v) := fun v => rfl
  refine ⟨T', ψ, ⟨hr, hdim, hψHf, ?_, hψact, ?_⟩, ?_⟩
  · intro v
    rw [hTL, hL]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← U.apply_symm_apply v, ← ha]
      simp [U]
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← ha]
      simp [U]
  · intro a
    rw [hTeps, ← heps a]
    congr 1
    simp [U]
  · intro j
    refine ⟨hrow' j, ?_⟩
    ext i
    rw [hψ]
    simp only [PiLp.smul_apply, EuclideanSpace.single, PiLp.ofLp_single, smul_eq_mul, Pi.single_apply]
    have hiff : e.symm i = j ↔ i = ⟨ty j, ⟨row j, hrow' j⟩⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    rcases em (i = ⟨ty j, ⟨row j, hrow' j⟩⟩) with h | h
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (mt hiff.1 h), if_neg h]

end GlobalTheory.ScalarTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusSign

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem exists_torusAt_of_isom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {r : ℕ} (X : FD.Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)))
    (x : FD.Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ A : I2.TorusAt X x, A.w0 = H.w0 := by
  have key : ∀ a b, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)) = -((D.EF a b : ℤ) : ℚ) := by
    intro a b
    rw [isom, neg_mul, map_neg, neg_neg]
  refine GlobalTheory.torusAtExists E r X ?_ H.w0 ?_ x hx
  · intro f
    obtain ⟨a, ha⟩ := D.unimod.2 (-(f.comp φ.toLinearMap.toAddMonoidHom).toIntLinearMap)
    refine ⟨φ a, (φ a).2, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := φ.surjective v
    rw [key, ha]
    simp
  · intro u hu v hv
    obtain ⟨a, ha⟩ := φ.surjective ⟨u, hu⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨v, hv⟩
    have hu' : u = (φ a : Fin r → E) := by rw [ha]
    have hv' : v = (φ b : Fin r → E) := by rw [hb]
    have hw : H.w0 - H.bar H.w0 = 1 - (H.bar H.w0 + H.bar H.w0) := by
      have := cmHostUnit_add_conj_eq_one H
      linear_combination this
    have hs : ((H.w0 : E) - FD.cc (H.w0 : E)) • v = (φ ((H.w0 - H.bar H.w0) • b) : Fin r → E) := by
      rw [map_smul, hb, FD.cc, ← H.bar_eq]
      funext i
      simp [Algebra.smul_def]
    refine ⟨D.EF a (H.bar H.w0 • b), ?_⟩
    rw [hs, hu', hv', key, key, hw, sub_smul, add_smul, one_smul, map_sub, map_add (f := _)]
    push_cast
    ring

theorem exists_torusAt_w0_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W
  exact exists_torusAt_of_isom (W.F.Di (W.ik k)) (U.X k) (W.φ k) (W.isom k) x.1 x.2

end GlobalTheory.TorusSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FockLaws
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem fock_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (q : ℤ) (a b : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) :
    fock Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Hm a b).im : ℂ)) *
      fock Hm q a (fock Hm q b θ) z := by
  have hl : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp [hermForm, add_dotProduct]
  have hr : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have hs : hermForm Hm b a = star (hermForm Hm a b) := by
    rw [hermForm, hermForm, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
      Matrix.dotProduct_mulVec]
  have hsc : hermForm Hm b a = hermForm Hm a b - 2 * Complex.I * ((hermForm Hm a b).im : ℂ) := by
    rw [hs]
    apply Complex.ext <;> simp
    ring
  funext z
  simp only [fock]
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [hl, hr, hsc]
  ring

theorem fock_sq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    fock Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z) := by
  have h : ∀ z w, hermForm Hm ((N : ℂ) • z) ((N : ℂ) • w) = (N : ℂ) ^ 2 * hermForm Hm z w := fun z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      star_natCast]
    ring
  funext z
  simp only [fock, h, smul_add]
  congr 2
  push_cast
  ring

theorem fock_laws : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ (q : ℤ) (a b : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) * fock Φ.Hm q a (fock Φ.Hm q b θ) z) ∧ (∀ (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Φ.Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ ∀ θ, Φ.IsTh 1 θ → ∀ a ∈ Φ.lat, fock Φ.Hm 1 a θ = fun z => Φ.χ a * θ z := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun q a b θ => fock_add Φ.herm q a b θ, fun N a θ => fock_sq Φ.Hm N a θ, fun θ hθ a ha => ?_⟩
  funext z
  simp only [fock, hθ.2 a ha z, AnFr.fac, zpow_one]
  have : Complex.exp (-(((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm z a) - ((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm a a / 2) *
      Complex.exp (Real.pi * hermForm Φ.Hm z a + Real.pi / 2 * hermForm Φ.Hm a a) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (Φ.χ a * θ z) * this

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsPiActLOfIsTorusOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.IsPiAct

theorem negOnePow_natCast_mul (M : ℕ) (k : ℤ) :
    Int.negOnePow ((M : ℤ) * k) = Int.negOnePow k ^ M := by
  induction M with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, _root_.one_mul, Int.negOnePow_add, ih, pow_succ]

theorem isPi_actL_of_isTorusOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsPeriod D ty Pm → IsTorusOf D ty Pm Hm T ψ → ∀ (α : 𝓞 E) (M : ℕ), α * H.bar α = (M : 𝓞 E) → I2.IsPi T M (vspActL α) := by
  intro E _ _ _ H D g ty Pm Hm T ψ hP hT α M hM
  obtain ⟨-, -, -, hL, hact, heps⟩ := hT

  have hnorm : ∀ τ : E →+* ℂ, τ (α : E) * starRingEnd ℂ (τ (α : E)) = (M : ℂ) := by
    intro τ
    have h := congrArg (fun x : 𝓞 E => τ (x : E)) hM
    push_cast at h
    have hb := congrArg τ (H.bar_eq α)
    rw [IsCMField.complexEmbedding_complexConj] at hb
    rw [map_mul, map_natCast] at h
    rw [← hb]
    exact h
  have hcoord : ∀ (u : I2.Vsp T.dim) i, (I2.act α u) i = i.1 (α : E) * u i := fun _ _ => rfl

  have hlat : ∀ a, I2.act α (ψ (Pm a)) = ψ (Pm (α • a)) := by
    intro a
    rw [← hact]
    congr 1
    funext k
    exact (hP.1 α a k).symm
  unfold I2.IsPi
  refine ⟨fun β v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩ <;>
    simp only [vspActL, LinearMap.coe_mk, AddHom.coe_mk]
  · ext i
    change i.1 (α : E) * (i.1 (β : E) * v i) = i.1 (β : E) * (i.1 (α : E) * v i)
    ring
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    rw [hlat, hL]
    exact ⟨α • a, rfl⟩
  · unfold I2.Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord, hcoord, map_mul]
    linear_combination (v i * starRingEnd ℂ (w i)) * hnorm i.1
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    have hEF : D.EF (α • a) (H.w0 • α • a) = (M : ℤ) * D.EF a (H.w0 • a) := by
      have hc : H.bar α * H.w0 * α = (M : 𝓞 E) * H.w0 := by rw [← hM]; ring
      rw [D.adj, smul_smul, smul_smul, hc, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    rw [hlat, heps, heps, hEF, negOnePow_natCast_mul, Units.val_pow_eq_pow_val]

end GlobalTheory.AnVal.IsPiAct
end

