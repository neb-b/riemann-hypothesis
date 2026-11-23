module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv


set_option maxHeartbeats 1000000 in
theorem ratio_local_norm_dpair : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  intro p _ G Ω hΩ P₁ L _ _ ι c hinj hcent hc
  obtain ⟨x₁, t₁, hx₁⟩ := P₁.trivAf
  have hβ₁inv := sh_inv_unit G P₁.β P₁.sym
  have hcc : ∀ x, c (c x) = x := fun x => hinj (by
    rw [hc, hc, sh_mul', sh_mul', sh_sh, hβ₁inv, P₁.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])
  have hcne : ∃ x, c x ≠ x := by
    obtain ⟨τ⟩ : Nonempty (G.F →+* ℂ) := inferInstance
    obtain ⟨f, -, hf⟩ := G.hKq.2 τ
    have hconj : IsCMField.complexConj G.F f ≠ f := by
      intro h
      apply hf
      have e := IsCMField.complexEmbedding_complexConj G.F τ f
      rw [h] at e
      exact Complex.conj_eq_iff_im.1 e.symm
    obtain ⟨w, hw⟩ := (hcent (algebraMap G.F G.C f)).1 (Algebra.commutes f _)
    refine ⟨w, fun h => hconj ?_⟩
    have e2 : ι (c w) = algebraMap G.F G.C (IsCMField.complexConj G.F f) := by
      rw [hc, hw, sh_algebraMap, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    rw [h, hw] at e2
    exact ((algebraMap G.F G.C).injective e2).symm
  obtain ⟨S1, hS1⟩ := exists_finset_of_eventually (GlobalTheory.OrbFinAf.cptInt p G Ω hΩ)
  obtain ⟨S2, hS2⟩ := exists_finset_of_eventually
    (GlobalTheory.OrbFinAf.cptInt p G {P₁.toAf x₁ t₁ hx₁ P₁.self} isCompact_singleton)
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.eventually_adic_integral_span_closed_mul_star G.C G.star _ (Module.finBasis ℚ G.C)
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer p G P₁.γ P₁.reg.1 P₁.reg.2 L ι hinj hcent _ (Module.finBasis ℚ G.C)
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.almost_all_places_twisted_unit_integral G.C L ι hinj _ (Module.finBasis ℚ G.C) _ (Module.finBasis ℚ L)
  obtain ⟨S6, hS6⟩ := GlobalTheory.T.fixed_unit_eq_norm_almost_all_places L c hcc hcne _ (Module.finBasis ℚ L)
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ (finite_above p).toFinset, ?_⟩
  intro P hγ hcP hex a ha v hv
  obtain ⟨x, t, hx, hxΩ⟩ := hex
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hv6⟩, hvp⟩ := hv
  have hvp' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h => hvp ((Set.Finite.mem_toFinset _).2 h)
  let w : AwayP p := ⟨v, hvp'⟩
  let K := v.adicCompletion ℚ
  let φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let ιv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ K) ι
  let cv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] L := Algebra.TensorProduct.map (AlgHom.id ℚ K) c
  let X : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x
  let X₁ : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x₁
  have key : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ) (hy : Triv G (AfP p) Q.β y s),
      ((((GlobalTheory.OrbFinAf.piV G w (Q.toAf y s hy Q.self) : GlobalTheory.OrbFinAf.Gv G w) :
        (K ⊗[ℚ] G.C)ˣ × Kˣ).1 : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) =
        ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) * ((1 : K) ⊗ₜ[ℚ] (Q.γ : G.C)) *
          ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)⁻¹ := by
    intro Q y s hy
    show φ (↑y * ((1 : AfP p) ⊗ₜ[ℚ] (Q.γ : G.C)) * ↑y⁻¹) = _
    rw [map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rfl
  have hXg : IsIntB v (Module.finBasis ℚ G.C) (↑X * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X⁻¹) := by
    have h := (hS1 w hv1 ⟨_, hxΩ, rfl⟩).1
    rw [key P x t hx, hγ] at h
    exact h
  have hX₁g : IsIntB v (Module.finBasis ℚ G.C) (↑X₁ * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X₁⁻¹) := by
    have h := (hS2 w hv2 ⟨_, rfl, rfl⟩).1
    rw [key P₁ x₁ t₁ hx₁] at h
    exact h

  obtain ⟨m, hm1, hm2⟩ := hS4 v hv4 X X₁ hXg hX₁g
  obtain ⟨hmul, hstar⟩ := hS3 v hv3
  let T : Kˣ := Units.map (AfP.eval w : AfP p →* K) t
  let T₁ : Kˣ := Units.map (AfP.eval w : AfP p →* K) t₁
  let β₁v : (K ⊗[ℚ] G.C)ˣ :=
    Units.map ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] K ⊗[ℚ] G.C) : G.C →* K ⊗[ℚ] G.C) P₁.β
  have hiota_a : ιv ((1 : K) ⊗ₜ[ℚ] a) * (β₁v : K ⊗[ℚ] G.C) = (1 : K) ⊗ₜ[ℚ] (P.β : G.C) := by
    show (1 : K) ⊗ₜ[ℚ] ι a * (1 : K) ⊗ₜ[ℚ] (P₁.β : G.C) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ha, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have htriv : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ), Triv G (AfP p) Q.β y s →
      (↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) : K ⊗[ℚ] G.C) * ((1 : K) ⊗ₜ[ℚ] (Q.β : G.C)) *
        (starT G.star K ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)).unop =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
    intro Q y s hy
    have hy' : (y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) Q.β * (starT G.star (AfP p) y).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s := hy
    have h := congrArg (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)) hy'
    rw [map_mul, map_mul, map_starT] at h
    have e1 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) Q.β) =
        (1 : K) ⊗ₜ[ℚ] (Q.β : G.C) := by
      simp [inC, Algebra.TensorProduct.map_tmul]
    have e2 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
    rw [e1, e2] at h
    exact h
  have h1 : (X : K ⊗[ℚ] G.C) * (ιv ((1 : K) ⊗ₜ[ℚ] a) * β₁v) * (starT G.star K X).unop =
      algebraMap K (K ⊗[ℚ] G.C) (T : K) := by
    rw [hiota_a]; exact htriv P x t hx
  have h2 : (X₁ : K ⊗[ℚ] G.C) * β₁v * (starT G.star K X₁).unop = algebraMap K (K ⊗[ℚ] G.C) (T₁ : K) :=
    htriv P₁ x₁ t₁ hx₁
  have hιR : ∀ r : K, ιv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] G.C) r := by
    intro r; simp [ιv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcm : ιv (cv ↑m) = ↑β₁v * (starT G.star K (ιv ↑m)).unop * ↑β₁v⁻¹ := map_conj_ext G K ι c P₁.β hc ↑m
  have hcore := selfDual_conj_eq_one (R := K) (ιv : K ⊗[ℚ] L →+* K ⊗[ℚ] G.C) hιR (starT G.star K) (cv : K ⊗[ℚ] L →+* K ⊗[ℚ] L)
    β₁v X X₁ T T₁ ((1 : K) ⊗ₜ[ℚ] a) m hcm h1 h2
  simp only [RingHom.coe_coe] at hcore

  have hu'u : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹) = 1 := by
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑m⁻¹ * ((↑X⁻¹ : K ⊗[ℚ] G.C) * ↑X) * ιv ↑m) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one, mul_one, Units.mul_inv]
  have hshu : (starT G.star K ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)).unop *
      (starT G.star K ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, hu'u, map_one, MulOpposite.unop_one]
  set u := (X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹ with hu
  set u' := (X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹ with hu'
  set E := algebraMap K (K ⊗[ℚ] L) (↑T⁻¹ * ↑T₁) * ((1 : K) ⊗ₜ[ℚ] a) * (↑m⁻¹ * cv ↑m⁻¹) with hE
  set wv := (X₁ : K ⊗[ℚ] G.C) * ιv E * ↑X₁⁻¹ with hwvdef
  have hwv : wv = u' * (starT G.star K u').unop := by
    calc wv = (u' * u) * wv * ((starT G.star K u).unop * (starT G.star K u').unop) := by
          rw [hu'u, hshu, one_mul, mul_one]
      _ = u' * (u * wv * (starT G.star K u).unop) * (starT G.star K u').unop := by simp only [mul_assoc]
      _ = _ := by rw [hcore, mul_one]
  have hwvI : IsIntB v (Module.finBasis ℚ G.C) wv := hwv ▸ hmul _ _ hm2 (hstar _ hm2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  obtain ⟨Eu, hEu⟩ : ∃ Eu : (K ⊗[ℚ] L)ˣ, (Eu : K ⊗[ℚ] L) = E :=
    ⟨Units.map (algebraMap K (K ⊗[ℚ] L) : K →* K ⊗[ℚ] L) (T⁻¹ * T₁) *
      Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] K ⊗[ℚ] L) : L →* K ⊗[ℚ] L) (Units.mk0 a ha0) *
        (m⁻¹ * Units.map (cv : K ⊗[ℚ] L →* K ⊗[ℚ] L) m⁻¹), by
      simp only [Units.val_mul, Units.coe_map, Units.val_mk0, hE, map_mul]
      rfl⟩
  have h_a : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv = 1 := by
    rw [hwvdef, ← hEu]
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑Eu⁻¹ * ((↑X₁⁻¹ : K ⊗[ℚ] G.C) * ↑X₁) * ιv ↑Eu) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul X₁, mul_one, ← map_mul ιv, Units.inv_mul Eu, map_one, mul_one, Units.mul_inv X₁]
  have h_b : wv * ((starT G.star K u).unop * u) = 1 := by
    calc wv * ((starT G.star K u).unop * u) = (u' * u) * wv * (starT G.star K u).unop * u := by
          rw [hu'u, one_mul]; simp only [mul_assoc]
      _ = u' * (u * wv * (starT G.star K u).unop) * u := by simp only [mul_assoc]
      _ = 1 := by rw [hcore, mul_one, hu'u]
  have hwv' : (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹ = (starT G.star K u).unop * u := by
    calc (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹
        = ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * (wv * ((starT G.star K u).unop * u)) := by rw [h_b, mul_one]
      _ = (((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv) * ((starT G.star K u).unop * u) := by
          rw [← mul_assoc]
      _ = _ := by rw [h_a, one_mul]
  have hE1 : IsIntB v (Module.finBasis ℚ L) (Eu : K ⊗[ℚ] L) := hS5 v hv5 X₁ _ (by rw [hEu]; exact hwvI)
  have hE2 : IsIntB v (Module.finBasis ℚ L) ((Eu⁻¹ : (K ⊗[ℚ] L)ˣ) : K ⊗[ℚ] L) :=
    hS5 v hv5 X₁ _ (by rw [hwv']; exact hmul _ _ (hstar _ hm1) hm1)
  have hca : c a = a := hinj (by
    rw [hc, ha, Units.val_mul, sh_mul', hβ₁inv, P.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left])
  have hcalg : ∀ r : K, cv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] L) r := by
    intro r; simp [cv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcinv : cv (cv ↑m⁻¹) = ↑m⁻¹ := map_invol c hcc _
  have hfix : cv ↑Eu = ↑Eu := by
    have : cv ((1 : K) ⊗ₜ[ℚ] a) = (1 : K) ⊗ₜ[ℚ] a := by
      show (1 : K) ⊗ₜ[ℚ] c a = _
      rw [hca]
    rw [hEu, hE]
    simp only [map_mul, hcalg, hcinv, this]
    ring
  obtain ⟨y₀, hy₀⟩ := hS6 v hv6 Eu hfix hE1 hE2
  refine ⟨T * T₁⁻¹, m * y₀, ?_⟩
  rw [hEu, hE, map_mul] at hy₀
  have hm' : (m : K ⊗[ℚ] L) * ↑m⁻¹ = 1 := Units.mul_inv m
  have hcm' : cv ↑m * cv ↑m⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hT : algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hT₁ : algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  show (1 : K) ⊗ₜ[ℚ] a = algebraMap K (K ⊗[ℚ] L) ↑(T * T₁⁻¹) * (↑(m * y₀) * cv ↑(m * y₀))
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  linear_combination (algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * cv ↑m) * hy₀ -
    ((1 : K) ⊗ₜ[ℚ] a) * hT - ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ * hT₁ -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * hm' -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * ↑m⁻¹ * hcm'

end GlobalTheory.LocTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

def entryR {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))

theorem entryR_apply {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    entryR τ a b Z = Z τ a b := rfl

def dSq {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (entryR τ a b)

theorem dSq_apply {m n : ℕ} (Z V : D.what₂.Tau → Fin m → Fin n → ℂ) :
    dSq Z V = ∑ τ, ∑ a, ∑ b, 2 * (V τ a b * starRingEnd ℂ (Z τ a b)).re := by
  simp [dSq, ContinuousLinearMap.sum_apply, entryR_apply, Complex.inner, two_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hasFDerivAt_sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    HasFDerivAt (fun Z : D.what₂.Tau → Fin m → Fin n → ℂ => sqSum Z) (dSq Z) Z := by
  unfold sqSum dSq
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun τ (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
    fun τ _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun a (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ b, ‖Z τ a b‖ ^ 2)
    fun a _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun b (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ‖Z τ a b‖ ^ 2)
    fun b _ => ?_
  exact (entryR τ a b).hasFDerivAt.norm_sq

def frL {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    { toFun := frPt B B'
      map_add' := fun x y => by
        funext τ
        show B' τ * Matrix.of (x τ + y τ) * (B τ)⁻¹ = B' τ * Matrix.of (x τ) * (B τ)⁻¹ + B' τ * Matrix.of (y τ) * (B τ)⁻¹
        rw [show Matrix.of (x τ + y τ) = Matrix.of (x τ) + Matrix.of (y τ) from rfl, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        funext τ
        show B' τ * Matrix.of (c • x τ) * (B τ)⁻¹ = c • (B' τ * Matrix.of (x τ) * (B τ)⁻¹)
        rw [show Matrix.of (c • x τ) = c • Matrix.of (x τ) from rfl, Matrix.mul_smul, Matrix.smul_mul] }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem frL_apply {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : frL B B' Z = frPt B B' Z := rfl

def toCLin {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] ℂ :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c v => by
        have e : c • v = c.re • v + c.im • (Complex.I • v) := by
          funext τ a b
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [e, map_add L, L.map_smul, L.map_smul, hL, RingHom.id_apply, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem toCLin_restrict {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (toCLin L hL).restrictScalars ℝ = L := by
  ext v; rfl

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I := by
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have him := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hn := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D (tauE D τ)
  have e : tauE D τ D.host.xi0 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos him] at hn
  rw [e, hn]

theorem hAt_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (τ : D.what₂.Tau)
    (Z V : Fin T.rank → Fin S.rank → ℂ) :
    hAt S T τ (GlobalTheory.FockPos.frAt frT τ * Matrix.of Z * (GlobalTheory.FockPos.frAt frS τ)⁻¹)
      (GlobalTheory.FockPos.frAt frT τ * Matrix.of V * (GlobalTheory.FockPos.frAt frS τ)⁻¹) =
      ∑ a, ∑ b, starRingEnd ℂ (V a b) * Z a b := by
  set B := GlobalTheory.FockPos.frAt frS τ
  set B' := GlobalTheory.FockPos.frAt frT τ
  have h1 : Bᴴ * gramAt D S τ * B = 1 := GlobalTheory.FockPos.frAt_on frS hS τ
  have h2 : B'ᴴ * gramAt D T τ * B' = 1 := GlobalTheory.FockPos.frAt_on frT hT τ
  have hBd : IsUnit B.det := isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne frS τ)
  have hGi : (gramAt D S τ)⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    have e1 : Bᴴ * (gramAt D S τ * B) = 1 := by rw [← Matrix.mul_assoc]; exact h1
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 e1
  have hBB : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hBd, Matrix.conjTranspose_one]
  have e : (gramAt D S τ)⁻¹ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹) =
      B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
    rw [hGi]
    calc B * Bᴴ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹)
        = B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.of V)ᴴ * (B'ᴴ * gramAt D T τ * B') * Matrix.of Z * B⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
          rw [hBB, h2, Matrix.one_mul, Matrix.mul_one]
  unfold hAt
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hBd]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  exact Finset.sum_comm

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (Z V : RW T S) :
    omO S T (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) Z)
      (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) V) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (V τ a b) * Z τ a b)).re := by
  rw [omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  unfold GlobalTheory.VacUnique.omAt
  rw [frPt, frPt, hAt_frame frS frT hS hT τ (Z τ) (V τ), realPlace_cmTrace_zero_element_eq_I_mul_abs]
  simp only [Finset.mul_sum, Complex.re_sum]

theorem differentiable_gZ_of_frames {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E)
    (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) :
    Differentiable ℂ (gZ σ S T (fun τ => (frS.1).map (tauE D τ)) (fun τ => (frT.1).map (tauE D τ)) f) := by
  obtain rfl := GlobalTheory.FockPos.cart_one frS hS hcS
  obtain rfl := GlobalTheory.FockPos.cart_one frT hT hcT
  obtain ⟨hd, hann⟩ := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ h ψ hψ S T _ _ f hf hfock
  have hJ : ∀ z : RW T S, jO S T (fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))
      (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) z = Complex.I • z := fun z => by
    funext τ i k
    simp [jO_apply, cplxO, Matrix.mul_apply, Matrix.one_apply, Pi.mul_apply, Pi.one_apply]
    first
      | exact congrFun (congrFun (Matrix.one_mul (M := (z τ : Matrix (Fin T.rank) (Fin S.rank) ℂ))) i) k
      | (erw [Matrix.mul_apply]; simp [Matrix.one_apply])
      | (rw [Matrix.one_mul])
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hF
  set Φ := frL (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) with hΦ
  intro Z
  have h1 : HasFDerivAt (fun Z => F (Φ Z)) ((fderiv ℝ F (Φ Z)).comp (Φ.restrictScalars ℝ)) Z :=
    (hd (Φ Z)).hasFDerivAt.comp Z (Φ.restrictScalars ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun Z : RW T S => Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ))
      (Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * Formalism.L2.Pj.xiR D) • dSq Z)) Z :=
    (Complex.ofRealCLM.hasFDerivAt.comp Z ((hasFDerivAt_sqSum Z).const_mul (Real.pi * Formalism.L2.Pj.xiR D))).cexp
  have h3 := h1.mul h2
  refine (hasFDerivAt_of_restrictScalars ℝ h3 (toCLin_restrict _ ?_)).differentiableAt
  intro v
  have hω1 : omO S T (Φ Z) (Φ v) = -(Formalism.L2.Pj.xiR D * dSq Z (Complex.I • v)) := by
    rw [hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hω2 : omO S T (Φ Z) (Complex.I • Φ v) = Formalism.L2.Pj.xiR D * dSq Z v := by
    rw [← map_smul, hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have ha := hann (Φ Z) (Φ v)
  rw [hJ, hω1, hω2, show f (iotaW σ T S (Φ Z)) = F (Φ Z) from rfl] at ha
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast at ha ⊢
  generalize Complex.exp ((Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) * (sqSum Z : ℂ)) = E
  generalize (fderiv ℝ F (Φ Z)) (Complex.I • Φ v) = b at ha ⊢
  generalize (fderiv ℝ F (Φ Z)) (Φ v) = a at ha ⊢
  linear_combination (-Complex.I * E) * ha + (F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z (Complex.I • v) : ℝ) : ℂ) +
    E * b - Complex.I * F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z v : ℝ) : ℂ)) * Complex.I_sq

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem differentiable_gZ_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  intro D T L sc G W U N σ hσ t j hj f hf
  exact differentiable_gZ_of_frames hσ hf.1 _ _ (N.fr (.top j)) (N.fr (.top (j + 1)))
    (N.fr_on (.top j) (show j ≤ D.R.m by omega)) (N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) _ _
    (W.cart_is (.top j) (show j ≤ D.R.m by omega)) (W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) f
    hf.2.theta hf.2.fock

end GlobalTheory.VacRealForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeCard

theorem encard_smallSec_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  intro k _ X _ p A B hBA
  obtain ⟨P, rfl, rfl, h1⟩ := hBA
  have hrep := Pair.rep_base k X p P
  have eL : P.L.smallSec.encard = (P.Bl 1 0 1).encard :=
    SmallBall.encard_eq_Bl P hrep.1 P.L.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have eA : P.A.smallSec.encard = (P.Bl 0 1 1).encard :=
    SmallBall.encard_eq_Bl P hrep.2.1 P.A.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  rw [eL, eA]
  refine Set.encard_le_encard fun f hf => ?_
  have e := NuMul.mul_mem_H_and_nu_mul k X p P 1 (-1) 0 1 1 f h1.1 hf.1
  rw [one_mul, add_zero, neg_add_cancel] at e
  refine ⟨e.1, fun σ y => ?_⟩
  rw [e.2 σ y]
  calc P.nu 1 (-1) σ y 1 * P.nu 0 1 σ y f ≤ 1 * 1 :=
        mul_le_mul (h1.2 σ y) (hf.2 σ y) (SmallBall.nu_nonneg P 0 1 σ y f) zero_le_one
    _ = 1 := one_mul 1

end GlobalTheory.HSNef.LeCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleGL
section
theorem GlobalTheory.FourClauses.irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  GlobalTheory.FourClauses.adm GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
end

