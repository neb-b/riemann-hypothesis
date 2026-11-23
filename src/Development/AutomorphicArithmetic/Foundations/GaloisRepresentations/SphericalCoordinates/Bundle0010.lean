module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ActComm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.PActY

variable {p : ℕ} [Fact p.Prime]

private theorem sh_sh' (G : HTGroup p) (a : G.C) : sh G (sh G a) = a := G.star_star a

private theorem key (G : HTGroup p) (β y : G.Cˣ) (s : ℚ)
    (h : (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β) :
    sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
  calc sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y
      = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β * sh G y) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
    _ = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * β) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        rw [h]
    _ = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
        simp only [_root_.mul_assoc, Units.mul_inv_cancel_left]
        rw [Algebra.commutes s (y : G.C), Units.inv_mul_cancel_left]
        exact (Algebra.commutes s _).symm

private theorem form_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (u w : VQ D) : formB L β (actY L y u) (actY L y w) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * formB L β u w := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.2.1
  have h1 := L.adj (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
    (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) w
  rw [sh_sh'] at h1
  have h2 : L.rep (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) =
      (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) • L.rep ((β⁻¹ : G.Cˣ) : G.C) u := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hk, map_mul,
      AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [formB, actY]
  rw [← h1, h2, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem act_comm {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (c : D.O) (w : VQ D) : actY L y (actQ D c w) = actQ D c (actY L y w) := by
  have h := (L.rep_range (actY L y)).1 ⟨_, rfl⟩ c
  exact LinearMap.congr_fun h w

private theorem act_inv {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (w : VQ D) : actY L y (L.rep (((((y : G.Cˣ × ℚˣ).1 : G.Cˣ))⁻¹ : G.Cˣ) : G.C) w) = w := by
  simp only [actY]
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

private theorem per_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q Q' : VQ D →+ (Fin D.g → ℂ)) (hP : IsPerQ L β ρ Q)
    (hQ : ∀ w, Q' (actY L y w) = Q w) : IsPerQ L β ρ Q' := by
  obtain ⟨h1, h2, Hm, hH, hpos, him⟩ := hP
  have hsc : ∀ (c : ℂ) (z z' : Fin D.g → ℂ), hermForm (c • Hm) z z' = c * hermForm Hm z z' := by
    intro c z z'
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hQ' : ∀ u, Q' u = Q (L.rep ((((y : G.Cˣ × ℚˣ).1 : G.Cˣ)⁻¹ : G.Cˣ) : G.C) u) := by
    intro u
    rw [← hQ, act_inv]
  refine ⟨fun c w => ?_, ?_, (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • Hm, ?_, fun z hz => ?_, fun u w => ?_⟩
  · rw [hQ', hQ', ← h1]
    congr 1
    exact LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) w
  · rw [eq_top_iff, ← h2]
    apply Submodule.span_mono
    rintro _ ⟨w, rfl⟩
    exact ⟨_, hQ w⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [hsc, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)
  · rw [← act_inv L β y u, ← act_inv L β y w, hQ, hQ, hsc, form_act, Complex.im_ofReal_mul, him]
    push_cast
    ring

private theorem psi_rat (G : HTGroup p) (v : InfinitePlace G.F) (s : ℚ) :
    G.psi v (algebraMap ℚ G.C s) = ((s : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have he : v.embedding (algebraMap ℚ G.F s) = (s : ℂ) := map_ratCast (v.embedding.comp (algebraMap ℚ G.F)) s
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F, he]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

private theorem pos_act (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (z : GlobalTheory.LKCx.PosV G v β) :
    0 < (star ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (GlobalTheory.LKCx.herm G v β *ᵥ ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.prop.1
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hV : ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) =
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
  have hg : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram v =
      G.gram v * G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    rw [show sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      MulOpposite.unop (G.star (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) from rfl, G.psi_star,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v)), Matrix.one_mul]
  have hpsi : G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * G.psi v ((β⁻¹ : G.Cˣ) : G.C) *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [← map_mul, ← map_mul, hk, map_mul, psi_rat, smul_one_mul]
  have hM : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * GlobalTheory.LKCx.herm G v β *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • GlobalTheory.LKCx.herm G v β := by
    simp only [GlobalTheory.LKCx.herm]
    rw [← Matrix.mul_assoc, hg, ← Matrix.mul_smul, ← hpsi]
    simp only [Matrix.mul_assoc]
  rw [hV, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hr z.2

end UpperTheory.Gal.W2.PActY

open UpperTheory.Gal.W2.PActY in
theorem UpperTheory.Gal.W2.actY_of :
    UpperTheory.Gal.W2.ActY := by
  intro p _ D G L β y
  exact ⟨form_act L β y, act_comm L β y, fun ρ Q Q' hP hQ => per_act L β y ρ Q Q' hP hQ,
    fun v z _ => ⟨⟨_, pos_act G v β y z⟩, rfl⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ArchFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

def sgnV (v : InfinitePlace G.F) : ℂ := if v.embedding (L.e (D.ω : D.F)) = D.ρc then 1 else -1

abbrev Arch (G : HTGroup p) : Type := InfinitePlace G.F → Fin G.n → ℂ

def hv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ := star y ⬝ᵥ (M *ᵥ x)

structure ArchFrame where
  th : VQ D →+ Arch G
  r : InfinitePlace G.F → ℝ
  r_pos : ∀ v, 0 < r v
  act : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v
  form : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, r v * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
  span : Submodule.span ℝ (Set.range th) = ⊤
  dim : Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D)
  dimg : Module.finrank ℝ (Arch G) = 2 * D.g

def IsFMat (kp : VQ D ≃+ (Fin G.n → G.F)) (σ : G.C ≃ₐ[G.F] Matrix (Fin G.n) (Fin G.n) G.F) : Prop :=
  ∀ c w, kp (L.rep c w) = σ c *ᵥ kp w

def IsPosJ {n : ℕ} (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : Prop :=
  J * J = -1 ∧ Jᴴ * M * J = M ∧ ∀ x, x ≠ 0 → 0 < (-s * Complex.I * hv M (J *ᵥ x) x).re

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdOfWit
section
private theorem UpperTheory.Gal.W2.mul_inv_star_of_triv {S A : Type*} [Ring S] [CommRing A] [Algebra A S]
    (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ) (t t' : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x * x'⁻¹ : Sˣ) : S) * (σ ((x * x'⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t * t'⁻¹ : Aˣ) : A) := by
  have key : ∀ u : Sˣ, (σ (u : S)).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    intro u
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = ((x'⁻¹ : Sˣ) : S) * (algebraMap A S t' * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
    rw [← hx']
    calc b = (((x'⁻¹ : Sˣ) : S) * x') * b * ((σ (x' : S)).unop * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, key, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [hb] at hx
  simp only [mul_assoc, Algebra.left_comm] at hx
  simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  calc _ = algebraMap A S ((t'⁻¹ * t' : Aˣ) : A) * ((x : S) * (((x'⁻¹ : Sˣ) : S) *
        ((σ ((x'⁻¹ : Sˣ) : S)).unop * (σ (x : S)).unop))) := by simp
    _ = algebraMap A S ((t'⁻¹ : Aˣ) : A) * algebraMap A S t := by
        rw [Units.val_mul, map_mul, mul_assoc, hx]
    _ = _ := Algebra.commutes _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.adOfWit_of :
    UpperTheory.Gal.W2.AdCore → UpperTheory.Gal.W2.AdOfWit := by
  intro hcore
  unfold AdCore at hcore
  unfold AdOfWit
  intro p _ D G L B D' j hpl f nu hw
  obtain ⟨x, c, hxc, hread⟩ := hcore p D G L B.β D' j hpl f nu hw
  obtain ⟨t0, ht0⟩ := B.trivAf.choose_spec
  have hmem : ((trivX B * x⁻¹, t0 * c⁻¹) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) ∈ UPts G.star (AfP p) := by
    rw [UPts, mem_uGroup]
    exact mul_inv_star_of_triv _ _ _ _ _ _ ht0 hxc
  let h : G.GAf := ⟨(trivX B * x⁻¹, t0 * c⁻¹), hmem⟩
  refine ⟨h, ?_⟩
  have hrd : ∀ w, rd L (trivX B) h w = rd L x 1 w := by
    intro w
    have hy : (((trivX B * x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C) = x := by
      rw [← Units.val_mul]
      congr 1
      group
    simp only [rd, inv_one, map_one, one_apply_eq_self]
    rw [← hy, map_mul, mul_apply_eq_comp]
    rfl
  intro n hn hcop
  obtain ⟨h1, h2⟩ := hread n hn hcop
  exact ⟨fun w => by rw [hrd]; exact h1 w, fun a => by rw [hrd]; exact h2 a⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBaseC
section
noncomputable section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped Classical

namespace UpperTheory.Gal.W2

private theorem rho_ne_conj {p : ℕ} [Fact p.Prime] (D : Datum p) :
    (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h0 := D.ρc_root
  rw [hr] at h0
  have h1 : (r : ℝ) ^ 2 - D.tr * r + D.nm = 0 := by exact_mod_cast h0
  have h2 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * r - D.tr)]

private theorem type_sum {p : ℕ} [Fact p.Prime] (D : Datum p) (t₀ : D.F →+* ℂ) (h₀ : t₀ (D.ω : D.F) = D.ρc)
    (hn : 1 ≤ D.n) (c : 𝓞 D.F) :
    ∑ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      t₀ (c : D.F) + ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (t₀ (c : D.F)) := by
  have hne : ComplexEmbedding.conjugate t₀ ≠ t₀ := by
    intro h
    apply rho_ne_conj D
    have := congrArg (fun τ : D.F →+* ℂ => τ (D.ω : D.F)) h
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using this
  have hc : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc := by
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using rho_ne_conj D
  have key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      (if τ = t₀ then τ (c : D.F) else 0) + (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) -
        (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0) := by
    intro τ
    unfold typeMult epsD
    by_cases h1 : τ = t₀
    · subst h1
      simp [hne.symm, h₀]
    · by_cases h2 : τ = ComplexEmbedding.conjugate t₀
      · subst h2
        have hc' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc := by
          simpa [ComplexEmbedding.conjugate_coe_eq] using hc
        simp [h1, hc', Nat.cast_sub hn]
        ring
      · by_cases h3 : τ (D.ω : D.F) = D.ρc <;> simp [h1, h2, h3]
  rw [Finset.sum_congr rfl fun τ _ => key τ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_filter]
  simp [ComplexEmbedding.conjugate_coe_eq]

theorem baseC_of : BaseC := by
  intro p _ D ha hm t₀ ht ρ hs gb hst
  have hsub : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
  let i₀ : Fin D.a := ⟨0, by omega⟩
  let b : Base D ℂ :=
    { unit := fun k hk => by
        refine isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 fun h => ?_)
        subst h
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
      ρ := gb.ρ
      ρ_root := gb.ρ_root
      t := gb.t
      t_ω := gb.t_ω
      comax := fun i j hij => absurd (hsub.elim i j) hij
      apart := fun i j hij => absurd (hsub.elim i j) hij }
  refine ⟨b, rfl, fun i => (RingHom.id_comp _).symm, ?_⟩
  intro c
  have hti : b.t i₀ c = t₀ (c : D.F) := by
    have := hst.2 i₀ c
    rw [ht i₀] at this
    exact this
  have hb : b.ρ = D.ρc := hst.1
  have h₀ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  rw [hs.tr c, type_sum D t₀ h₀ hs.pos c, hm, Fintype.sum_subsingleton _ i₀, Fintype.sum_subsingleton _ i₀]
  simp [hti, hb]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PClsScalar
section
noncomputable section

open GlobalTheory.PELU GlobalTheory.UPel.HT

namespace UpperTheory.Gal.W2

private lemma power_free {T : Type} (X Y : T → ℤ) (a b : ℕ) (hab : a.Coprime b)
    (h : ∀ t, (b : ℤ) * X t = a * Y t)
    (hP : ∀ q k : ℕ, q.Prime → ((∀ t, ((q ^ k : ℕ) : ℤ) ∣ X t) ↔ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t))
    (t₀ : T) (h0 : Y t₀ ≠ 0) : a = 1 := by
  classical
  by_contra ha
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd ha
  have hqb : ¬ q ∣ b := fun hqb => hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hab hqa hqb)
  have hex : ∃ k, ¬ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t := by
    refine ⟨(Y t₀).natAbs, fun hall => h0 ?_⟩
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hall t₀) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hq.one_lt
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this (fun t => by simp)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmY : ∀ t, ((q ^ m : ℕ) : ℤ) ∣ Y t := by
    by_contra hc
    exact Nat.find_min hex (by omega) hc
  have hcop : IsCoprime ((q ^ (m + 1) : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb))
  have hX : ∀ t, ((q ^ (m + 1) : ℕ) : ℤ) ∣ X t := by
    intro t
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [h t, pow_succ, Nat.cast_mul, mul_comm (a : ℤ)]
    exact mul_dvd_mul (hmY t) (Int.natCast_dvd_natCast.mpr hqa)
  have := Nat.find_spec hex
  rw [hm] at this
  exact this ((hP q (m + 1) hq).mp hX)

private lemma genus_dvd {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (h : Genus p N D₀ D' t) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (∀ x y, (n : ℤ) ∣ D'.EF x y) ↔ ∀ a a', (n : ℤ) ∣ D₀.EF a a' := by
  obtain ⟨f, ν, -, -, H⟩ := h
  obtain ⟨hν, -, -, honto, hsim⟩ := H n hn hc
  constructor
  · intro hd a a'
    have h1 : (n : ℤ) ∣ ν n * D₀.EF a a' := (dvd_sub_right (hd _ _)).1 (hsim a a')
    exact hν.symm.dvd_of_dvd_mul_left h1
  · intro hd x y
    obtain ⟨a, e, rfl⟩ := honto x
    obtain ⟨a', e', rfl⟩ := honto y
    have h1 : (n : ℤ) ∣ D'.EF (f n a) (f n a') := by
      have h2 := hsim a a'
      have h3 : (n : ℤ) ∣ ν n * D₀.EF a a' := Dvd.dvd.mul_left (hd a a') _
      exact (dvd_sub_left h3).1 h2
    simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_add (dvd_add h1 (Dvd.intro _ rfl)) (Dvd.intro _ rfl)

private lemma half_value {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] :
    ∃ (E₁ : LinearMap.BilinForm ℤ D'.La) (e : ℕ) (x y : D'.La), D'.EF = (2 : ℤ) • E₁ ∧ e.Coprime p ∧ E₁ x y = e := by
  obtain ⟨E₁, hE, e, he, hx⟩ := h
  let b := Module.Free.chooseBasis ℤ D'.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨x, hx⟩ := hx (b.coord i)
  refine ⟨E₁, e, x, b i, hE, he, ?_⟩
  rw [hx]
  simp

private lemma half_dvd {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] (k : ℕ) :
    (∀ x y, ((p ^ k : ℕ) : ℤ) ∣ D'.EF x y) ↔ ((p ^ k : ℕ) : ℤ) ∣ 2 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  constructor
  · intro hall
    have h1 := hall x y
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul] at h1
    have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (e : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ he.symm)
    exact hcop.dvd_of_dvd_mul_right h1
  · intro h2 x' y'
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left h2 _

private lemma half_ne {O : Type} [Ring O] {bar : O → O} {p : ℕ} (hp : p.Prime) {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] : ∃ x y, D'.EF x y ≠ 0 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  refine ⟨x, y, ?_⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp he)
  rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul]
  exact mul_ne_zero two_ne_zero (by exact_mod_cast he0)

private lemma genus_nontrivial {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (hp : p.Prime) (h : Genus p N D₀ D' t) [Nontrivial D₀.La] : Nontrivial D'.La := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨f, ν, -, -, hf⟩ := h
  have hn : 0 < 1 + p := by omega
  have hc : (1 + p).Coprime p := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)
  obtain ⟨-, -, hdiv, -, -⟩ := hf (1 + p) hn hc
  let b := Module.Free.chooseBasis ℤ D₀.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨e, he⟩ := (hdiv (b i)).mp ⟨0, Subsingleton.elim _ _⟩
  have h1 := congrArg (b.coord i) he
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul,
    Finsupp.smul_apply, nsmul_eq_mul] at h1
  have h2 := Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm
  have := hp.two_le
  omega

theorem clsScalar_of : ClsScalar := by
  intro p _ D N N' D' t D'' t'' hD' hD'' w r hr hEF
  have hp : p.Prime := Fact.out
  haveI : Nontrivial D.plat.La := by
    show Nontrivial D.La
    refine Module.nontrivial_of_finrank_pos (R := ℤ) ?_
    rw [D.rankLa]
    have h1 := D.m_pos
    have h2 := D.n_pos
    have h3 : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    positivity
  haveI : Nontrivial D'.La := genus_nontrivial hp hD'.1
  haveI : Nontrivial D''.La := genus_nontrivial hp hD''.1
  let X : D''.La × D''.La → ℤ := fun u => D'.EF (w u.1) (w u.2)
  let Y : D''.La × D''.La → ℤ := fun u => D''.EF u.1 u.2
  have hXall : ∀ m : ℤ, (∀ u, m ∣ X u) ↔ ∀ x y, m ∣ D'.EF x y := fun m =>
    ⟨fun h x y => by simpa [X] using h (w.symm x, w.symm y), fun h u => h _ _⟩
  have hYall : ∀ m : ℤ, (∀ u, m ∣ Y u) ↔ ∀ x y, m ∣ D''.EF x y := fun m =>
    ⟨fun h x y => h (x, y), fun h u => h _ _⟩
  have hP : ∀ q k : ℕ, q.Prime → ((∀ u, ((q ^ k : ℕ) : ℤ) ∣ X u) ↔ ∀ u, ((q ^ k : ℕ) : ℤ) ∣ Y u) := by
    intro q k hq
    rw [hXall, hYall]
    by_cases hqp : q = p
    · subst hqp
      rw [half_dvd hD'.2, half_dvd hD''.2]
    · have hpos : 0 < q ^ k := pow_pos hq.pos k
      have hcop : (q ^ k).Coprime p := Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).mpr hqp)
      rw [genus_dvd hD'.1 _ hpos hcop, genus_dvd hD''.1 _ hpos hcop]
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hkey : ∀ u, (r.den : ℤ) * X u = (r.num.natAbs : ℤ) * Y u := by
    intro u
    rw [Int.natAbs_of_nonneg hnum.le]
    have h1 := hEF u.1 u.2
    have h2 : ((r.den : ℤ) * X u : ℚ) = (r.num * Y u : ℚ) := by
      push_cast
      rw [show (X u : ℚ) = ((D'.EF (w u.1) (w u.2) : ℤ) : ℚ) from rfl, h1, ← Rat.mul_den_eq_num]
      ring
    exact_mod_cast h2
  obtain ⟨x₀, y₀, h0⟩ := half_ne hp hD''.2
  obtain ⟨x₁, y₁, h1⟩ := half_ne hp hD'.2
  have ha : r.num.natAbs = 1 :=
    power_free X Y r.num.natAbs r.den r.reduced hkey hP (x₀, y₀) h0
  have hb : r.den = 1 :=
    power_free Y X r.den r.num.natAbs r.reduced.symm (fun u => (hkey u).symm)
      (fun q k hq => (hP q k hq).symm) (w.symm x₁, w.symm y₁) (by simpa [X] using h1)
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hb]
  norm_num

end UpperTheory.Gal.W2
end
end

