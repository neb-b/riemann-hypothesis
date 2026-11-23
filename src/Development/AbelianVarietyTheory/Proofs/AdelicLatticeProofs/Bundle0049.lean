module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletion
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletionStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F), (∀ v, e v ∈ v.adicCompletionIntegers F) → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) → ∀ X : Matrix (Fin n) (Fin n) (RA F E), (∀ z ∈ hat F (L : Set (Fin n → E)), X *ᵥ z ∈ hat F (L : Set (Fin n → E))) → ∃ W : Matrix (Fin n) (Fin n) (RA F E), (1 + (e ⊗ₜ[F] (1 : E) : RA F E) • (N • X)) * W = 1 ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), W *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | exact GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | (intros; apply GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceIsSquareAndNotIsSquare
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_place_isSquare_and_not_isSquare :
    ∀ (F : Type) [Field F] [NumberField F] (δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → u ≠ 0 → ¬ IsSquare δ → ¬ IsSquare u → ¬ IsSquare (u * δ) → ∃ v, v ∉ S₀ ∧ IsSquare (algebraMap F (v.adicCompletion F) δ) ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ δ u S₀ hδ hu hδs hus huδs
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδs
  have hbasic := isQuad_basic F E δ θ σ hq
  have huE : ¬ IsSquare (algebraMap F E u) := fun h => (hbasic.2.2.2.2.2.1 u h).elim hus huδs
  have hu0E : algebraMap F E u ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hu
  obtain ⟨S, hS₀, hSunits⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu, Units.mk0 (u * δ) (mul_ne_zero hu hδ)} S₀
  have hgood : ∀ v, v ∉ S → ∀ x ∈ ({Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu,
      Units.mk0 (u * δ) (mul_ne_zero hu hδ)} : Finset Fˣ), v.valuation F (x : F) = 1 :=
    fun v hv x hx => (mem_sUnits F S x).mp (hSunits S subset_rfl x hx) v hv
  obtain ⟨hover, -, -⟩ := places_over F E
  obtain ⟨SE, hSE⟩ := hover S
  obtain ⟨w, hwS, hwu⟩ := _root_.GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion E (algebraMap F E u) SE hu0E huE
  have hvS : w.under (𝓞 F) ∉ S := fun h => hwS ((hSE w).mpr h)
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hθ : algebraMap E (w.adicCompletion E) θ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).mpr hq.root_ne_zero
  have hnu : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) := by
    intro h
    apply hwu
    have h' := h.map φ
    rwa [hφ] at h'
  have hnuδ : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) := by
    intro h
    apply hwu
    have h' := h.map φ
    rw [hφ, map_mul, map_mul, ← hq.sq, map_pow] at h'
    obtain ⟨r, hr⟩ := h'
    refine ⟨r / algebraMap E (w.adicCompletion E) θ, ?_⟩
    rw [div_mul_div_comm, ← hr]
    field_simp
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
      (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (w.under (𝓞 F)) x
  have h2 : Valued.v (2 : (w.under (𝓞 F)).adicCompletion F) = 1 := by
    rw [show (2 : (w.under (𝓞 F)).adicCompletion F) = algebraMap F _ 2 from (map_ofNat _ 2).symm,
      hval]
    simpa using hgood _ hvS (Units.mk0 (2 : F) two_ne_zero) (Finset.mem_insert_self _ _)
  have hvu : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 u hu)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hvuδ : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 (u * δ) (mul_ne_zero hu hδ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨s, hs⟩ := isSquare_mul_of_nonsquare_units F (w.under (𝓞 F)) h2 _ _ hvu hvuδ hnu hnuδ
  have ha : algebraMap F ((w.under (𝓞 F)).adicCompletion F) u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F _).injective).mpr hu
  refine ⟨w.under (𝓞 F), fun h => hvS (hS₀ h), ⟨s / algebraMap F _ u, ?_⟩, hnu⟩
  rw [div_mul_div_comm, ← hs, map_mul]
  field_simp

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlacePowAndNotPow
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_pow_and_not_pow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → δ ≠ 0 → u ≠ 0 → (∀ r : F, r ^ p ≠ δ) → (∀ (k : ℕ) (r : F), u ≠ δ ^ k * r ^ p) → ∃ v, v ∉ S₀ ∧ (∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) δ) ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ δ u S₀ hp hζ hδ hu hδs huδ
  obtain ⟨E, _, _, θ, σ, hq⟩ := exists_isKum p F ζ δ hp hζ hδs
  obtain ⟨hfd, -, -, -, -, hpow, -⟩ := _root_.GlobalTheory.CNorm.kummer_basic p F E ζ δ θ σ hq
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  have huE : ∀ y : E, y ^ p ≠ algebraMap F E u := by
    intro y h
    obtain ⟨k, r, hr⟩ := hpow u y h
    exact huδ k r hr
  have h2 : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨S, hS, hSu⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (p : F) h2, Units.mk0 δ hδ, Units.mk0 u hu} S₀
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  obtain ⟨w, hw, hwu⟩ := _root_.GlobalTheory.CNorm.exists_not_mem_not_pow_completion p E (algebraMap F E ζ) (algebraMap F E u) SE hp
    (hζ.map_of_injective (algebraMap F E).injective) (by simpa using hu) huE
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x)
      = (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ x
  have hv2 : (w.under (𝓞 F)).valuation F (p : F) = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 (p : F) h2) (by simp)) _ hv
  have hvδ : (w.under (𝓞 F)).valuation F δ = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 δ hδ) (by simp)) _ hv
  have hvu : (w.under (𝓞 F)).valuation F u = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 u hu) (by simp)) _ hv
  have hunsq : ∀ r : (w.under (𝓞 F)).adicCompletion F,
      r ^ p ≠ algebraMap F ((w.under (𝓞 F)).adicCompletion F) u := by
    intro r h
    apply hwu (φ r)
    rw [← hφ, ← h, map_pow]
  refine ⟨w.under (𝓞 F), fun h => hv (hS h), ?_, hunsq⟩
  by_contra hδn
  push Not at hδn
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_unit p F (w.under (𝓞 F)) _ _ hp hv2
    ((hval δ).trans hvδ) ((hval u).trans hvu) hδn
  apply hwu (algebraMap E (w.adicCompletion E) θ ^ k * φ r)
  rw [← hφ, hr, map_mul, map_pow, map_pow, hφ, ← hq.pow, map_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm k p]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalRational
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.PolySection

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsNatural (F : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R) : Prop :=
  ∀ (R S : Type) [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (x : Matrix ι ι R),
    φ.mapMatrix (F R x) = F S (φ.mapMatrix x)

noncomputable def evHom {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R :=
  MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2)

theorem evHom_generic {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    (evHom y).mapMatrix (Matrix.mvPolynomialX ι ι ℚ) = y := by
  ext i j
  simp [evHom, Matrix.mvPolynomialX]

theorem map_ev {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (f : MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι R) : φ (ev f x) = ev f (φ.mapMatrix x) := by
  unfold ev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem map_rat {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (e : Matrix ι ι ℚ) : φ.mapMatrix (e.map (algebraMap ℚ R)) = e.map (algebraMap ℚ S) := by
  ext i j
  exact φ.commutes _

theorem map_blk {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (e : Matrix ι ι ℚ) (x : Matrix ι ι R) : φ.mapMatrix (blk e x) = blk e (φ.mapMatrix x) := by
  simp only [blk, map_add (f := _), map_mul, map_sub, map_one, map_rat]

theorem map_linExt {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (c : ι × ι → ι × ι → ℚ) (x : Matrix ι ι R) : φ.mapMatrix (linExt c x) = linExt c (φ.mapMatrix x) := by
  ext i j
  show φ (∑ kl : ι × ι, algebraMap ℚ R (c (i, j) kl) * x kl.1 kl.2) =
    ∑ kl : ι × ι, algebraMap ℚ S (c (i, j) kl) * φ (x kl.1 kl.2)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.commutes]

theorem map_poly {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (b : ι → ι → MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι R) :
    φ.mapMatrix (Matrix.of fun i j => ev (b i j) x) = Matrix.of fun i j => ev (b i j) (φ.mapMatrix x) := by
  ext i j
  exact map_ev φ _ _

theorem transfer_mem {F : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R}
    (hF : IsNatural F) {Γ Γ' : Set (Matrix ι ι ℂ)} (h : ∀ g ∈ Γ, F ℂ g ∈ Γ')
    {R : Type} [CommRing R] [Algebra ℚ R] {y : Matrix ι ι R} (hy : y ∈ pts Γ R) : F R y ∈ pts Γ' R := by
  intro f hf
  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S),
      ev (ev f (F _ (Matrix.mvPolynomialX ι ι ℚ))) z = ev f (F S z) := by
    intro S _ _ z
    have := map_ev (evHom z) f (F _ (Matrix.mvPolynomialX ι ι ℚ))
    rw [hF, evHom_generic] at this
    exact this
  rw [← key]
  apply hy
  intro g hg
  rw [key]
  exact hf _ (h g hg)

theorem transfer_eq {F G : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R}
    (hF : IsNatural F) (hG : IsNatural G) {Γ : Set (Matrix ι ι ℂ)} (h : ∀ g ∈ Γ, F ℂ g = G ℂ g)
    {R : Type} [CommRing R] [Algebra ℚ R] {y : Matrix ι ι R} (hy : y ∈ pts Γ R) : F R y = G R y := by
  ext i j
  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S),
      ev (F _ (Matrix.mvPolynomialX ι ι ℚ) i j - G _ (Matrix.mvPolynomialX ι ι ℚ) i j) z
        = F S z i j - G S z i j := by
    intro S _ _ z
    have h1 := hF _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)
    have h2 := hG _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)
    rw [evHom_generic] at h1 h2
    rw [← h1, ← h2]
    exact map_sub (evHom z) _ _
  rw [← sub_eq_zero, ← key]
  apply hy
  intro g hg
  rw [key, h g hg, sub_self]

theorem mem_pts_univ {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    y ∈ pts (Set.univ : Set (Matrix ι ι ℂ)) R := by
  intro f hf
  have h0 : MvPolynomial.map (algebraMap ℚ ℂ) f = 0 := by
    apply MvPolynomial.funext
    intro x
    have := hf (Matrix.of fun i j => x (i, j)) (Set.mem_univ _)
    rw [map_zero, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this
  have : f = 0 := MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  subst this
  simp [ev]

theorem exists_section : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), ∀ (R : Type) [CommRing R] [Algebra ℚ R], (∀ X : Matrix ι ι R, 1 + linExt c X ∈ pts Γ R) ∧ (∀ X Y : Matrix ι ι R, linExt c X * linExt c Y = 0) ∧ (∀ y ∈ pts Γ R, blk e y = 1 → ∃ X : Matrix ι ι R, y = 1 + linExt c X) ∧ (∀ x ∈ pts Γ R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 ∧ blk e x ∈ pts (blk e '' Γ) R) ∧ ∀ y ∈ pts (blk e '' Γ) R, (Matrix.of fun i j => ev (b i j) (y)) ∈ pts Γ R ∧ blk e (Matrix.of fun i j => ev (b i j) (y)) = y := by
  intro ι _ _ Γ e hΓ he htri
  obtain ⟨c, b, hc, h1, hb⟩ := _root_.GlobalTheory.ClassFin.exists_blk_section ι Γ e hΓ he htri
  refine ⟨c, b, fun R _ _ => ⟨fun X => ?_, fun X Y => ?_, fun y hy hy1 => ?_, fun x hx => ⟨?_, ?_⟩,
    fun y hy => ⟨?_, ?_⟩⟩⟩
  · have h := transfer_mem (F := fun R _ _ X => 1 + linExt c X)
      (fun R S _ _ _ _ φ x => by simp only [map_add (f := _), map_one, map_linExt])
      (fun g _ => (hc g).1) (mem_pts_univ X)
    exact h
  · have hp : ∀ X : Matrix ι ι R,
        e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)) = linExt c X := fun X => by
      have h := transfer_eq (F := fun R _ _ X => e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)))
        (G := fun R _ _ X => linExt c X)
        (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_linExt, map_rat])
        (fun R S _ _ _ _ φ x => by simp only [map_linExt])
        (by intro g _; beta_reduce; exact (hc g).2) (mem_pts_univ X)
      exact h
    have hE : (1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R) = 0 := by
      rw [sub_mul, one_mul, ← Matrix.map_mul, he, sub_self]
    rw [← hp X, ← hp Y]
    calc _ = e.map (algebraMap ℚ R) * linExt c X * ((1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R)) *
          linExt c Y * (1 - e.map (algebraMap ℚ R)) := by simp only [mul_assoc]
      _ = 0 := by rw [hE]; simp
  · have hone : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι R)) = 1 := by
      have hq : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℚ)) = 1 := by
        have := map_poly (Algebra.ofId ℚ ℂ) b 1
        rw [map_one, h1] at this
        ext i j
        apply (algebraMap ℚ ℂ).injective
        have h2 := congrFun (congrFun this i) j
        rw [← map_one (Algebra.ofId ℚ ℂ).mapMatrix] at h2
        exact h2
      have := map_poly (Algebra.ofId ℚ R) b 1
      rw [hq, map_one] at this
      exact this.symm
    have h := transfer_eq (F := fun R _ _ g => g)
      (G := fun R _ _ g => (1 + linExt c (e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) *
        (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)))
      (fun R S _ _ _ _ φ x => rfl)
      (fun R S _ _ _ _ φ x => by
        simp only [map_mul, map_add (f := _), map_sub, map_one, map_linExt, map_rat, map_poly, map_blk,
          AlgHom.map_adjugate])
      (Γ := Γ) (by intro g hg; beta_reduce; exact (hb g hg).2.2) hy
    simp only [hy1, hone, mul_one] at h
    exact ⟨_, h⟩
  · have h := transfer_eq (F := fun R _ _ x => (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R))
      (G := fun R _ _ _ => 0)
      (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_rat])
      (fun R S _ _ _ _ φ x => by simp only [map_zero])
      (by intro g hg; beta_reduce; exact htri g hg) hx
    exact h
  · have h := transfer_mem (F := fun R _ _ x => blk e x) (fun R S _ _ _ _ φ x => map_blk φ e x)
      (Γ' := blk e '' Γ) (fun g hg => ⟨g, hg, rfl⟩) hx
    exact h
  · have h := transfer_mem (F := fun R _ _ x => Matrix.of fun i j => ev (b i j) x)
      (fun R S _ _ _ _ φ x => map_poly φ b x)
      (Γ' := Γ) (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).1) hy
    exact h
  · have h := transfer_eq (F := fun R _ _ x => blk e (Matrix.of fun i j => ev (b i j) x))
      (G := fun R _ _ x => x)
      (fun R S _ _ _ _ φ x => by simp only [map_blk, map_poly])
      (fun R S _ _ _ _ φ x => rfl)
      (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).2.1) hy
    exact h

end GlobalTheory.ClassFin.PolySection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorStabiliserClosedSLOrbit
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_tensor_stabiliser_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ (∀ y : Matrix ι ι ℂ, y.det = 1 → act d (fun k => ((t k : ℚ) : ℂ)) y = (fun k => ((t k : ℚ) : ℂ)) → y ∈ Γ) ∧ IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, hRey⟩ := _root_.GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds ι Γ hΓ.toIsPre hss
  obtain ⟨m, d, t, hfix, hgen⟩ := _root_.GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor ι Γ hΓ.toIsPre hss
  obtain ⟨h1, hmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d (fun k => ((t k : ℚ) : ℂ))
  refine ⟨m, d, t, hfix, ?_, ?_⟩
  · intro y hy hyt
    by_contra hn
    obtain ⟨f, hf, hne⟩ := _root_.GlobalTheory.ClassFin.exists_isInv_evC_one_ne ι Γ Rey hΓ hRey y hy hn
    obtain ⟨P, hP⟩ := hgen f hf
    apply hne
    rw [hP, hP, h1, hyt]
  · obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.ClassFin.exists_mvPolynomial_ev_eq_act ι m d t
    have hev : ∀ (y : Matrix ι ι ℂ) (k : TIdx ι d),
        evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y = act d (fun k => ((t k : ℚ) : ℂ)) y k := by
      intro y k
      have h := hΦ ℂ y k
      simp only [eq_ratCast] at h
      rw [← h, evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have hcl := GlobalTheory.T.isClosed_image_SL_under_generating_invariants ι Γ Rey (TIdx ι d) (fun k => MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) hRey
      hΓ.det_eq (fun k g hg y => by rw [hev, hev, hmul, hfix g hg]) (fun f hf => by
        obtain ⟨P, hP⟩ := hgen f hf
        rw [Algebra.adjoin_range_eq_range_aeval]
        refine ⟨P, ?_⟩
        apply MvPolynomial.funext
        intro x
        have h := hP (Matrix.of fun i j => x (i, j))
        have hx : (fun ij : ι × ι => (Matrix.of fun i j => x (i, j)) ij.1 ij.2) = x := rfl
        have h2 : act d (fun k => ((t k : ℚ) : ℂ)) (Matrix.of fun i j => x (i, j)) =
            fun k => MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) := by
          funext k
          rw [← hev, evC, hx]
        rw [evC, hx, h2] at h
        rw [h]
        show MvPolynomial.eval x (MvPolynomial.aeval _ P) = _
        clear hP h
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p n hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X])
    have : orb d (fun k => ((t k : ℚ) : ℂ)) = {z : TIdx ι d → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧
        z = fun k => evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y} := by
      ext z
      simp only [orb, hev]
    rw [this]
    exact hcl

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupLocalSquaresEqTop
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_union_sup_finSq_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by
  intro F _ _ _ S T hS hST hA
  classical
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  obtain ⟨u, hu, huA⟩ := hA (T.filter fun v =>
    ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))
  have huU : u ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits] at hu ⊢
    intro v hv
    exact hu v fun h => hv (Finset.mem_union_left _ h)
  have hsq : u * (a * x) ∈ finSq F T := by
    simp only [finSq, Subgroup.mem_iInf]
    intro v hv
    rw [mem_sqSub, Units.val_mul, map_mul]
    have h := huA v hv
    rw [Finset.mem_filter] at h
    by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))
    · exact (h.2 fun hh => hh.2 hs).mul hs
    · refine isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs
      · rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]
        exact (hS v (hTS v hv)).1
      · rw [hval]
        exact (mem_sUnits F S u).1 hu v (hTS v hv)
      · rw [hval]
        exact hy v hv
  have hx : x = (u * a)⁻¹ * (u * (a * x)) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq

end GlobalTheory.QNorm
end

