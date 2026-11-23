module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsHermitianDiagonalizationAtInfinitePlaceOfS
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma archPlace_core {C : Type} [Ring C] {n : ℕ} (hn : 0 < n)
    (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (T : C → Matrix (Fin n) (Fin n) ℂ) (s : C → C)
    (hs : Function.Surjective s) (S g A' : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.det ≠ 0) (hgH : g.IsHermitian) (hgd : g.det ≠ 0)
    (hψ : ∀ c, ψ c * S = S * T c)
    (hstar : ∀ c, ψ (s c) = g⁻¹ * (ψ c)ᴴ * g)
    (hrel : ∀ c, A' * T (s c) = (T c)ᴴ * A')
    (hskew : A'ᴴ = -A')
    (hspan : ∀ i j, ∃ c, T c = Matrix.single i j (1 : ℂ)) :
    ∃ lam : ℂ, (starRingEnd ℂ) lam = -lam ∧ (S⁻¹)ᴴ * A' * S⁻¹ = lam • g := by
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.mpr hgd
  have SiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSu
  have SSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSu
  have giG : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgu
  have gGi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  have h1 : ∀ c, T c * S⁻¹ = S⁻¹ * ψ c := fun c => by
    calc T c * S⁻¹ = S⁻¹ * (S * T c) * S⁻¹ := by
          rw [← Matrix.mul_assoc, SiS, Matrix.one_mul]
      _ = S⁻¹ * ψ c := by
          rw [← hψ, Matrix.mul_assoc, Matrix.mul_assoc, SSi, Matrix.mul_one]
  set Av := (S⁻¹)ᴴ * A' * S⁻¹ with hAv
  have h2 : ∀ c, Av * ψ (s c) = (ψ c)ᴴ * Av := fun c => by
    have e : (S⁻¹)ᴴ * (T c)ᴴ = (ψ c)ᴴ * (S⁻¹)ᴴ := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_mul]
    calc Av * ψ (s c) = (S⁻¹)ᴴ * A' * (S⁻¹ * ψ (s c)) := by
          rw [hAv, Matrix.mul_assoc _ S⁻¹]
      _ = (S⁻¹)ᴴ * (A' * T (s c)) * S⁻¹ := by
          rw [← h1]; simp only [Matrix.mul_assoc]
      _ = ((S⁻¹)ᴴ * (T c)ᴴ) * A' * S⁻¹ := by
          rw [hrel]; simp only [Matrix.mul_assoc]
      _ = (ψ c)ᴴ * Av := by
          rw [e, hAv]; simp only [Matrix.mul_assoc]
  have h3 : ∀ c, g * ψ (s c) = (ψ c)ᴴ * g := fun c => by
    rw [hstar, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gGi, Matrix.one_mul]
  set B := g⁻¹ * Av with hB
  have h4 : ∀ c, B * ψ c = ψ c * B := fun c => by
    obtain ⟨d, rfl⟩ := hs c
    calc B * ψ (s d) = g⁻¹ * ((ψ d)ᴴ * Av) := by rw [hB, Matrix.mul_assoc, h2]
      _ = (g⁻¹ * ((ψ d)ᴴ * g)) * (g⁻¹ * Av) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc g g⁻¹, gGi, Matrix.one_mul]
      _ = ψ (s d) * B := by
          rw [hB, ← h3, ← Matrix.mul_assoc g⁻¹ g, giG, Matrix.one_mul]
  have hT : ∀ c, T c = S⁻¹ * ψ c * S := fun c => by
    rw [← h1, Matrix.mul_assoc, SiS, Matrix.mul_one]
  have h5 : ∀ c, (S⁻¹ * B * S) * T c = T c * (S⁻¹ * B * S) := fun c => by
    rw [hT]
    calc S⁻¹ * B * S * (S⁻¹ * ψ c * S) = S⁻¹ * B * (S * S⁻¹) * ψ c * S := by
          simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (B * ψ c) * S := by
          rw [SSi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S⁻¹ * ψ c * (S * S⁻¹) * B * S := by
          rw [h4, SSi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S⁻¹ * ψ c * S * (S⁻¹ * B * S) := by
          simp only [Matrix.mul_assoc]
  obtain ⟨lam, hlam⟩ := Matrix.mem_range_scalar_of_commute_single (M := S⁻¹ * B * S)
    (fun i j _ => by
      obtain ⟨c, hc⟩ := hspan i j
      have := h5 c
      rw [hc] at this
      exact this.symm)
  have hlam' : S⁻¹ * B * S = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hlam]; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hBl : B = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc B = S * (S⁻¹ * B * S) * S⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [SSi, Matrix.mul_one, ← Matrix.mul_assoc, SSi, Matrix.one_mul]
      _ = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hlam', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, SSi]
  have hAl : Av = lam • g := by
    calc Av = g * B := by rw [hB, ← Matrix.mul_assoc, gGi, Matrix.one_mul]
      _ = lam • g := by rw [hBl, Matrix.mul_smul, Matrix.mul_one]
  have hsk : Avᴴ = -Av := by
    rw [hAv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hg0 : g ≠ 0 := by
    rintro rfl
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact hgd Matrix.det_zero
  refine ⟨lam, ?_, hAl⟩
  rw [hAl, Matrix.conjTranspose_smul, hgH.eq] at hsk
  have h6 : ((starRingEnd ℂ) lam + lam) • g = 0 := by
    rw [add_smul]
    have : star lam • g = -(lam • g) := hsk
    change star lam • g + lam • g = 0
    rw [this, neg_add_cancel]
  rcases smul_eq_zero.mp h6 with h | h
  · exact eq_neg_of_add_eq_zero_left h
  · exact absurd h hg0

theorem UpperTheory.exists_hermitian_diagonalization_at_infinitePlace_of_skewHermitian :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (σ : G.C ≃ₐ[G.F] Matrix (Fin G.n) (Fin G.n) G.F) (A : Matrix (Fin G.n) (Fin G.n) G.F), UpperTheory.Gal.W2.SN → A.det ≠ 0 → (A.map (IsCMField.complexConj G.F))ᵀ = -A → (∀ c, A * σ (sh G c) = ((σ c).map (IsCMField.complexConj G.F))ᵀ * A) → ∀ v : InfinitePlace G.F, ∃ (S : Matrix (Fin G.n) (Fin G.n) ℂ) (lam : ℂ), S.det ≠ 0 ∧ (∀ c, G.psi v c * S = S * (σ c).map v.embedding) ∧ (starRingEnd ℂ) lam = -lam ∧ (S⁻¹)ᴴ * A.map v.embedding * S⁻¹ = lam • G.gram v := by
  intro p _ G σ A hSN _ hskew hrel v
  let ψ : Matrix (Fin G.n) (Fin G.n) G.F →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
    (G.psi v).comp (σ.symm : Matrix (Fin G.n) (Fin G.n) G.F →ₐ[G.F] G.C).toRingHom
  have hψ : ∀ x : G.F, ψ (Matrix.scalar (Fin G.n) x) = Matrix.scalar (Fin G.n) (v.embedding x) := fun x => by
    have e : Matrix.scalar (Fin G.n) x = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x := by
      rw [Matrix.algebraMap_eq_diagonal]; rfl
    change G.psi v (σ.symm (Matrix.scalar (Fin G.n) x)) = _
    rw [e, AlgEquiv.commutes, G.psi_F]
  obtain ⟨S, hS, hSψ⟩ := hSN G.F ℂ G.n v.embedding ψ hψ
  have hpsi : ∀ c, G.psi v c * S = S * (σ c).map v.embedding := fun c => by
    have := hSψ (σ c)
    have e : ψ (σ c) = G.psi v c := by
      change G.psi v (σ.symm (σ c)) = _
      rw [AlgEquiv.symm_apply_apply]
    rwa [e] at this
  have hconj : ∀ M : Matrix (Fin G.n) (Fin G.n) G.F,
      ((M.map (IsCMField.complexConj G.F))ᵀ).map v.embedding = (M.map v.embedding)ᴴ := fun M => by
    ext i j
    simp [Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  have hrel' : ∀ c, A.map v.embedding * (σ (sh G c)).map v.embedding
      = ((σ c).map v.embedding)ᴴ * A.map v.embedding := fun c => by
    have := congrArg (fun M => M.map v.embedding) (hrel c)
    simpa only [Matrix.map_mul, hconj] using this
  have hskew' : (A.map v.embedding)ᴴ = -A.map v.embedding := by
    rw [← hconj, hskew]
    ext i j
    simp
  obtain ⟨lam, h1, h2⟩ := archPlace_core G.n_pos (G.psi v) (fun c => (σ c).map v.embedding) (sh G)
    (fun c => ⟨sh G c, by simp [sh, G.star_star]⟩) S (G.gram v) (A.map v.embedding) hS
    (G.gram_herm v) (G.gram_det v) hpsi (fun c => G.psi_star v c) hrel' hskew'
    (fun i j => ⟨σ.symm (Matrix.single i j 1), by
      ext a b
      simp [Matrix.single_apply]⟩)
  exact ⟨S, lam, hS, hpsi, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRationalEquivOfIsPlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim
open UpperTheory.Gal.W2

private theorem exists_lattice_basis_of_rational {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (j : N →+ ℚ ⊗[ℤ] M) (hj : Function.Injective j)
    (hs : ∀ w, ∃ (m : ℕ) (u : N), m ≠ 0 ∧ m • w = j u) :
    ∃ (ψ : N ≃+ M) (T : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M)), ∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u := by
  classical
  let jL : N →ₗ[ℤ] ℚ ⊗[ℤ] M := j.toIntLinearMap
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) jL := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [Module.End.isUnit_iff]
      have hx : ((x : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero x.2)
      have hsm : ∀ v : ℚ ⊗[ℤ] M,
          (algebraMap ℤ (Module.End ℤ (ℚ ⊗[ℤ] M)) x) v = ((x : ℤ) : ℚ) • v := by
        intro v
        rw [Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
      refine ⟨fun v w h => ?_, fun v => ⟨((x : ℤ) : ℚ)⁻¹ • v, ?_⟩⟩
      · rw [hsm, hsm] at h
        exact smul_right_injective _ hx h
      · rw [hsm, smul_smul, mul_inv_cancel₀ hx, one_smul]
    · intro w
      obtain ⟨m, u, hm, h⟩ := hs w
      refine ⟨⟨u, ⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩⟩, ?_⟩
      show (m : ℤ) • w = j u
      rw [natCast_zsmul]
      exact h
    · intro x1 x2 h
      exact ⟨1, by rw [one_smul, one_smul]; exact hj h⟩
  have hb : IsBaseChange ℚ jL := IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ jL
  have hrank : Module.finrank ℤ N = Module.finrank ℤ M := by
    rw [← Module.finrank_of_isLocalizedModule_of_free ℚ (nonZeroDivisors ℤ) jL,
      Module.finrank_baseChange]
  let e : N ≃ₗ[ℤ] M := LinearEquiv.ofFinrankEq N M hrank
  refine ⟨e.toAddEquiv, (LinearEquiv.baseChange ℤ ℚ N M e).symm.trans hb.equiv, fun u => ?_⟩
  have h1 : (LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u) = (1 : ℚ) ⊗ₜ[ℤ] u := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show hb.equiv ((LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u)) = j u
  rw [h1, hb.equiv_tmul, one_smul]
  rfl

theorem UpperTheory.exists_rational_equiv_of_isPlace :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ} {D' : PLat D.O D.inv} {j : D'.La →+ VQ D}, IsPlace L β D' j →
        ∃ (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D), ∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u := by
  intro p _ D G L β D' j h
  haveI := D.freeLa
  haveI := D.finLa
  exact exists_lattice_basis_of_rational j h.1 h.2.2.1
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsUnitTrivOfSimilitudeFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem trivCore {A S : Type} [CommRing A] [Ring S] [Algebra A S] (σ : S → S)
    (hm : ∀ a b, σ (a * b) = σ b * σ a) (hs : ∀ x, σ (σ x) = x)
    (ha : ∀ r, σ (algebraMap A S r) = algebraMap A S r)
    (B b y y' : S) (hBb : B * b = 1) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (u t : A) (hut : t * u = 1)
    (h : σ (B * y) * y = algebraMap A S u) : y' * b * σ y' = algebraMap A S t := by
  have s1 : σ 1 = 1 := by
    have h0 := ha 1
    rwa [map_one] at h0
  have hσ : σ y' * σ y = 1 := by rw [← hm, h₂, s1]
  have hσ' : σ y * σ y' = 1 := by rw [← hm, h₁, s1]
  have hU : σ y * B * y = algebraMap A S u := by
    have h3 := congrArg σ h
    rw [hm, hs, ha] at h3
    rw [_root_.mul_assoc]
    exact h3
  have hB : B = σ y' * algebraMap A S u * y' := by
    rw [← hU]
    calc B = (σ y' * σ y) * B * (y * y') := by rw [hσ, h₂, _root_.one_mul, _root_.mul_one]
      _ = σ y' * (σ y * B * y) * y' := by simp only [_root_.mul_assoc]
  have e1 : algebraMap A S u * (σ y' * y' * b) = 1 := by
    rw [← hBb, hB, (Algebra.commutes u (σ y')).symm]
    simp only [_root_.mul_assoc]
  have hX : σ y' * y' * b = algebraMap A S t := by
    calc σ y' * y' * b = (algebraMap A S t * algebraMap A S u) * (σ y' * y' * b) := by
          rw [← map_mul, hut, map_one, _root_.one_mul]
      _ = algebraMap A S t := by rw [_root_.mul_assoc, e1, _root_.mul_one]
  calc y' * b * σ y' = (σ y * σ y') * y' * b * σ y' := by rw [hσ', _root_.one_mul]
    _ = σ y * (σ y' * y' * b) * σ y' := by simp only [_root_.mul_assoc]
    _ = σ y * algebraMap A S t * σ y' := by rw [hX]
    _ = algebraMap A S t * (σ y * σ y') := by rw [← Algebra.commutes, _root_.mul_assoc]
    _ = algebraMap A S t := by rw [hσ', _root_.mul_one]

private theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (x : R ⊗[ℚ] G.C) : (starT G.star R (starT G.star R x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]

private theorem starT_alg {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (r : R) : (starT G.star R (algebraMap R (R ⊗[ℚ] G.C) r)).unop = algebraMap R (R ⊗[ℚ] G.C) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, starT_tmul, map_one, MulOpposite.unop_one]

theorem UpperTheory.exists_unit_triv_of_similitude_factor :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y y' : AfP p ⊗[ℚ] G.C) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (s : ℚ),
        0 < s → ∀ (c : (AfP p)ˣ),
        (∀ v w, algebraMap ℚ (AfP p) s * formAf D (actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C))
          (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w) = (2 * (c : AfP p)) * formAf D v w) →
        ∃ t : (AfP p)ˣ, Triv G (AfP p) β ⟨y', y, h₁, h₂⟩ t := by
  intro p _ D G L β y y' h₁ h₂ s hs0 c hyp
  have hs : s ≠ 0 := ne_of_gt hs0
  set Bi := inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C) with hBi
  set b := inC G (AfP p) (β : G.C) with hb
  have hBb : Bi * b = 1 := by
    rw [hBi, hb, ← map_mul, Units.inv_mul, map_one]
  let u : AfP p := algebraMap ℚ (AfP p) (2 * s⁻¹) * (c : AfP p)
  let t : AfP p := algebraMap ℚ (AfP p) (s / 2) * ((c⁻¹ : (AfP p)ˣ) : AfP p)
  have hut : t * u = 1 := by
    have hq : s / 2 * (2 * s⁻¹) = 1 := by field_simp
    calc t * u = algebraMap ℚ (AfP p) (s / 2 * (2 * s⁻¹)) * (((c⁻¹ : (AfP p)ˣ) : AfP p) * c) := by
          simp only [t, u, map_mul]
          ring
      _ = 1 := by rw [hq, map_one, Units.inv_mul, _root_.one_mul]
  have htu : u * t = 1 := by rw [_root_.mul_comm]; exact hut
  let σ : AfP p ⊗[ℚ] G.C → AfP p ⊗[ℚ] G.C := fun x => (starT G.star (AfP p) x).unop
  have hkey : σ (Bi * y) * y = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) u := by
    apply GlobalTheory.AdelicSim.inj L
    apply LinearMap.ext
    intro w
    rw [AlgHom.commutes, Module.algebraMap_end_apply, ← sub_eq_zero]
    apply nondeg D
    intro v
    rw [map_sub, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
    simp only [σ]
    rw [← adjAf L, map_mul, Module.End.mul_apply]
    have hsinv : algebraMap ℚ (AfP p) s⁻¹ * algebraMap ℚ (AfP p) s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs, map_one]
    calc _ = algebraMap ℚ (AfP p) s⁻¹ * (algebraMap ℚ (AfP p) s *
            formAf D (actOn L.rep (AfP p) Bi (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w))
            - u * formAf D v w := by
          rw [← _root_.mul_assoc, hsinv, _root_.one_mul]
      _ = 0 := by
          rw [hyp v w]
          simp only [u]
          rw [map_mul, map_ofNat]
          ring
  refine ⟨⟨t, u, hut, htu⟩, ?_⟩
  exact trivCore σ (fun a a' => by simp only [σ]; rw [map_mul, MulOpposite.unop_mul])
    (starT_invol G (AfP p)) (starT_alg G (AfP p)) Bi b y y' hBb h₁ h₂ u t hut hkey
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.FinrankArchimedeanEqTwoMulDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.finrank_archimedean_eq_two_mul_dim :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → UpperTheory.Gal.W2.ArchSpan → Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D) ∧ Module.finrank ℝ (Arch G) = 2 * D.g := by
  intro p _ D G L hm hA
  have h1 : Module.finrank ℝ (Arch G) = Fintype.card (InfinitePlace G.F) * (G.n * 2) := by
    have hc : Module.finrank ℝ (Fin G.n → ℂ) = G.n * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    unfold Arch
    rw [Module.finrank_pi_fintype]
    simp [hc]
  have h2 : Module.finrank ℝ (Arch G) = G.n * Module.finrank ℚ G.F := (hA G.F G.n).2.1
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa
    rw [← D.rankLa]
    exact Module.finrank_baseChange
  have hg : D.g = D.m * D.n * Module.finrank ℚ D.F / 2 := rfl
  have h2' : Module.finrank ℝ (Arch G) = D.n * Module.finrank ℚ D.F := by
    rw [h2, h3, L.n_eq]
  have h1' : Module.finrank ℝ (Arch G) = 2 * (Fintype.card (InfinitePlace G.F) * D.n) := by
    rw [h1, L.n_eq]; ring
  rw [hm, _root_.one_mul] at h4 hg
  refine ⟨by rw [h2', h4], ?_⟩
  rw [hg, ← h2', h1']
  omega
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.FormScalarOfAdelicEndoPreservingLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem formIntegral {p : ℕ} [Fact p.Prime] {D : Datum p}
    (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ)
    (hF : ∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p))
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : IsIntAf (F v w) := by
  have ez : ∀ (a : AfP p) (x : D.La), a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAf D x := by
    intro a x
    rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hgen : ∀ (a : AfP p) (x : D.La), IsIntAf a → ∀ w ∈ LaHat D, IsIntAf (F (a • inAf D x) w) := by
    intro a x ha w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      rw [ez, map_smul, map_smul, LinearMap.smul_apply, hF, smul_eq_mul, smul_eq_mul]
      exact isInt_mul ha' (isInt_mul ha (isInt_intCast _))
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [ez]
    exact hgen a x ha w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

theorem UpperTheory.form_scalar_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ),
        (∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p)) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) → ∀ (gs : ℕ → D.La →+ D.La),
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (gs n x) + n • w) →
        ∀ (nu : ℕ → ℤ) (c : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : AfP p, IsIntAf b ∧ c = (nu n : AfP p) + n • b) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ e (gs n x) (gs n y) - nu n * (2 * D.EF x y)) →
        ∀ v w, F (A v) (A w) = (2 * c) * formAf D v w := by
  intro p _ D F e hF A _ gs hA nu c hc hsim
  have key : ∀ x x', F (A (inAf D x)) (A (inAf D x')) = (2 * c) * formAf D (inAf D x) (inAf D x') := by
    intro x x'
    have := zero p (F (A (inAf D x)) (A (inAf D x')) - (2 * c) * formAf D (inAf D x) (inAf D x'))
      fun n hn hnp => by
      obtain ⟨w, hw, e₁⟩ := hA n hn hnp x
      obtain ⟨w', hw', e₂⟩ := hA n hn hnp x'
      obtain ⟨β, hβ, eβ⟩ := hc n hn hnp
      obtain ⟨k, hk⟩ := hsim n hn hnp x x'
      refine ⟨(k : AfP p) + F (inAf D (gs n x)) w' + F w (inAf D (gs n x')) +
        n • F w w' - (2 : ℤ) * β * (D.EF x x' : AfP p), ?_, ?_⟩
      · exact isInt_sub (isInt_add (isInt_add (isInt_add (isInt_intCast k)
          (formIntegral F e hF (inAf_mem D _) hw')) (formIntegral F e hF hw (inAf_mem D _)))
          (isInt_nsmul (formIntegral F e hF hw hw') n))
          (isInt_mul (isInt_mul (isInt_intCast 2) hβ) (isInt_intCast _))
      · have hk' := congrArg (Int.cast : ℤ → AfP p) hk
        push_cast at hk'
        rw [e₁, e₂, eβ]
        simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, form_inAf, hF, nsmul_eq_mul]
        push_cast
        linear_combination hk'
    exact sub_eq_zero.1 this
  have e2 := bilinear_ext_adelic_inclusion D (f := F.compl₁₂ A A) (g := (2 * c) • formAf D) fun x x' => by
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]; exact key x x'
  intro v w
  have := LinearMap.congr_fun₂ e2 v w
  simpa using this
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.SpanRealMatrixMulVecInfinitePlaceEmbeddingEqTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ), UpperTheory.Gal.W2.ArchSpan → ∀ S : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ, (∀ v, (S v).det ≠ 0) → Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) => S v *ᵥ fun i => v.embedding (x i)) = ⊤ := by
  intro F _ _ _ n hA S hS
  let Ph : (InfinitePlace F → Fin n → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
    { toFun := fun x v => S v *ᵥ x v
      map_add' := fun x y => by
        funext v
        simp [Matrix.mulVec_add]
      map_smul' := fun c x => by
        funext v
        simp [Matrix.mulVec_smul] }
  have hsurj : Function.Surjective Ph := by
    intro y
    refine ⟨fun v => (S v)⁻¹ *ᵥ y v, ?_⟩
    funext v
    have hu : IsUnit (S v).det := isUnit_iff_ne_zero.2 (hS v)
    change S v *ᵥ ((S v)⁻¹ *ᵥ y v) = y v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h := congrArg (Submodule.map Ph) (hA F n).1
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.2 hsurj, ← Set.range_comp] at h
  exact h
end

