module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnit
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm IsLocalRing
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_eq_pow_mul_pow_of_isCyclic {G : Type*} [CommGroup G] [IsCyclic G] {p : ℕ}
    (hp : p.Prime) {x : G} (hx : ∀ r : G, r ^ p ≠ x) (y : G) :
    ∃ (k : ℕ) (r : G), y = x ^ k * r ^ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
  have hpa : ¬ (p : ℤ) ∣ a := by
    rintro ⟨c, rfl⟩
    exact hx (g ^ c) (by rw [← zpow_natCast, ← zpow_mul, mul_comm])
  have hcop : IsCoprime (p : ℤ) a :=
    ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hpa
  obtain ⟨u, w, huw⟩ := hcop
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg (b * w) hp0)
  refine ⟨k, g ^ (b * u + a * (b * w / p)), ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hk]
  congr 1
  have := Int.emod_add_mul_ediv (b * w) p
  linear_combination (-b) * huw - a * this

theorem exists_pow_eq_of_residue_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u)
    (c : ResidueField R) (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨a, rfl⟩ := residue_surjective c
  have ha : IsUnit a := by
    have : IsUnit (residue R a ^ n) := hc ▸ hu.map _
    exact (isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)
  obtain ⟨v, hv, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (X ^ n - C u : R[X])
    (monic_X_pow_sub_C u hn0) a
    (by rw [← residue_eq_zero_iff]; simp [hc])
    (IsUnit.map _ (by simpa [derivative_X_pow] using hn.mul (ha.pow _)))
  exact ⟨v, by simpa [sub_eq_zero] using hv⟩

theorem exists_eq_pow_mul_pow_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] {p : ℕ} (hp : p.Prime)
    (hn : IsUnit (p : R)) (x y : Rˣ) (hx : ∀ r : R, r ^ p ≠ x) :
    ∃ (k : ℕ) (r : R), (y : R) = x ^ k * r ^ p := by
  let f : Rˣ →* (ResidueField R)ˣ := Units.map (residue R : R →* ResidueField R)
  have hx' : ∀ r : (ResidueField R)ˣ, r ^ p ≠ f x := by
    intro r hr
    obtain ⟨s, hs⟩ := exists_pow_eq_of_residue_pow hn x.isUnit (r : ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, hr]; rfl)
    exact hx s hs
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_isCyclic hp hx' (f y)
  have h1 : r ^ p = f ((x ^ k)⁻¹ * y) := by
    rw [map_mul, map_inv, map_pow, hr, inv_mul_cancel_left]
  obtain ⟨s, hs⟩ := exists_pow_eq_of_residue_pow hn ((x ^ k)⁻¹ * y).isUnit (r : ResidueField R)
    (by rw [← Units.val_pow_eq_pow_val, h1]; rfl)
  refine ⟨k, s, ?_⟩
  rw [hs, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel_left]

theorem exists_eq_pow_mul_pow_of_unit : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F), p.Prime → v.valuation F (p : F) = 1 → Valued.v x = 1 → Valued.v y = 1 → (∀ r : v.adicCompletion F, r ^ p ≠ x) → ∃ (k : ℕ) (r : v.adicCompletion F), y = x ^ k * r ^ p := by
  intro p F _ _ v x y hp hv hx hy hx'
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  let a : v.adicCompletionIntegers F := ⟨x, hx.le⟩
  let b : v.adicCompletionIntegers F := ⟨y, hy.le⟩
  have ha : IsUnit a := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hb : IsUnit b := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hy
  have hn : IsUnit (p : v.adicCompletionIntegers F) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (p : F)).trans hv
    have e : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (p : F) := by simp
    rw [e]
    exact h
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_henselian hp hn ha.unit hb.unit
    (fun r hr => hx' r (congrArg Subtype.val hr))
  exact ⟨k, r, congrArg Subtype.val hr⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalMap
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.IdempotentCornerSection

section ring
variable {A : Type} [Ring A] {E : A}

lemma corner_mul (hE : E * E = E) {x y : A} (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) :
    x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by noncomm_ring
    _ = 0 := by rw [h]; simp

lemma diag_comm (hE : E * E = E) (g : A) :
    E * (E * g * E + (1 - E) * g * (1 - E)) = (E * g * E + (1 - E) * g * (1 - E)) * E := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h' : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  calc E * (E * g * E + (1 - E) * g * (1 - E))
      = (E * E) * g * E + (E * (1 - E)) * g * (1 - E) := by simp only [mul_add, mul_assoc]
    _ = E * g * (E * E) + (1 - E) * g * ((1 - E) * E) := by rw [hE, h, h']; simp
    _ = _ := by simp only [add_mul, mul_assoc]

lemma corner_mul_comm {x D : A} (hD : E * D = D * E) (hx : E * x * (1 - E) = x) :
    E * (x * D) * (1 - E) = x * D := by
  have h : D * (1 - E) = (1 - E) * D := by rw [mul_sub, sub_mul, hD, mul_one, one_mul]
  calc E * (x * D) * (1 - E) = E * x * (D * (1 - E)) := by simp only [mul_assoc]
    _ = E * x * (1 - E) * D := by rw [h]; simp only [mul_assoc]
    _ = x * D := by rw [hx]

lemma corner_idem (hE : E * E = E) (g : A) : E * (E * g * (1 - E)) * (1 - E) = E * g * (1 - E) := by
  have h : (1 - E) * (1 - E) = 1 - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hE, sub_self, sub_zero]
  calc E * (E * g * (1 - E)) * (1 - E) = (E * E) * g * ((1 - E) * (1 - E)) := by simp only [mul_assoc]
    _ = _ := by rw [hE, h]

lemma corner_diag (hE : E * E = E) {x : A} (hx : E * x * (1 - E) = x) :
    E * x * E + (1 - E) * x * (1 - E) = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc E * x * E + (1 - E) * x * (1 - E)
      = E * (E * x * (1 - E)) * E + (1 - E) * (E * x * (1 - E)) * (1 - E) := by rw [hx]
    _ = E * E * x * ((1 - E) * E) + ((1 - E) * E) * x * (1 - E) * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

lemma inv_comm {D D' : A} (hD : E * D = D * E) (h1 : D * D' = 1) (h2 : D' * D = 1) :
    E * D' = D' * E := by
  calc E * D' = (D' * D) * E * D' := by rw [h2, one_mul]
    _ = D' * (D * E) * D' := by simp only [mul_assoc]
    _ = D' * E * (D * D') := by rw [← hD]; simp only [mul_assoc]
    _ = D' * E := by rw [h1, mul_one]

end ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def beta {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (g : Matrix ι ι R) :
    Matrix ι ι R :=
  e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) * (blk e g).adjugate

noncomputable def sec {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ)
    (g : Matrix ι ι R) : Matrix ι ι R :=
  (1 - linExt c (beta e g)) * g

section natural
variable {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)

lemma map_rat (e : Matrix ι ι ℚ) :
    φ.mapMatrix (e.map (algebraMap ℚ R)) = e.map (algebraMap ℚ S) := by
  ext i j; simp [AlgHom.mapMatrix_apply, -eq_ratCast]

lemma map_blk (e : Matrix ι ι ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (blk e g) = blk e (φ.mapMatrix g) := by
  simp only [blk, map_add (f := _), map_mul, map_sub, map_one, map_rat]

lemma map_linExt (c : ι × ι → ι × ι → ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (linExt c g) = linExt c (φ.mapMatrix g) := by
  ext i j; simp [linExt, AlgHom.mapMatrix_apply, map_sum, -eq_ratCast]

lemma map_sec (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (sec e c g) = sec e c (φ.mapMatrix g) := by
  simp only [sec, beta, map_mul, map_sub, map_one, map_rat, map_linExt, AlgHom.map_adjugate, map_blk]

end natural

lemma exists_poly (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ) :
    ∃ f : ι → ι → MvPolynomial (ι × ι) ℚ, ∀ (g : Matrix ι ι ℂ) i j, ev (f i j) g = sec e c g i j := by
  refine ⟨fun i j => sec e c (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ)) i j,
    fun g i j => ?_⟩
  have h := map_sec (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) e c
    (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ))
  have h2 : (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)).mapMatrix
      (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ)) = g := by
    ext k l; simp [AlgHom.mapMatrix_apply]
  rw [h2] at h
  rw [← h]; rfl

lemma linExt_sub (c : ι × ι → ι × ι → ℚ) (x y : Matrix ι ι ℂ) :
    linExt c (x - y) = linExt c x - linExt c y := by
  ext i j; simp [linExt, mul_sub, Finset.sum_sub_distrib]

lemma linExt_zero (c : ι × ι → ι × ι → ℚ) : linExt c (0 : Matrix ι ι ℂ) = 0 := by
  ext i j; simp [linExt]

end GlobalTheory.ClassFin.IdempotentCornerSection


open GlobalTheory.ClassFin.IdempotentCornerSection in
theorem GlobalTheory.ClassFin.exists_blk_section : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℂ)) = 1 ∧ ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) ∈ Γ ∧ blk e (Matrix.of fun i j => ev (b i j) (blk e g)) = blk e g ∧ g = (1 + linExt c (e.map (algebraMap ℚ ℂ) * g * (1 - e.map (algebraMap ℚ ℂ)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)) := by
  intro ι _ _ Γ e hΓ he htri
  obtain ⟨c, hc, hfix⟩ := _root_.GlobalTheory.ClassFin.exists_linExt_corner_proj ι Γ e hΓ he
  have hpre := _root_.GlobalTheory.ClassFin.isPre_blk_image ι Γ e hΓ.toIsPre he htri
  obtain ⟨hb1, -, hdec, hbb, -⟩ := _root_.GlobalTheory.ClassFin.blk_mul_of_triangular ι e ℂ he
  obtain ⟨f, hf⟩ := exists_poly e c
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hcomm : ∀ g : Matrix ι ι ℂ, e.map (algebraMap ℚ ℂ) * blk e g = blk e g * e.map (algebraMap ℚ ℂ) :=
    fun g => diag_comm hE g
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => hpre.det_eq _ ⟨g, hg, rfl⟩
  have h1 : ∀ g ∈ Γ, blk e g * (blk e g).adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hdet g hg, one_smul]
  have h2 : ∀ g ∈ Γ, (blk e g).adjugate * blk e g = 1 := fun g hg => by
    rw [Matrix.adjugate_mul, hdet g hg, one_smul]
  have hβ : ∀ g ∈ Γ, e.map (algebraMap ℚ ℂ) * beta e g * (1 - e.map (algebraMap ℚ ℂ)) = beta e g :=
    fun g hg => corner_mul_comm (inv_comm (hcomm g) (h1 g hg) (h2 g hg)) (corner_idem hE g)
  have hg1 : ∀ g ∈ Γ, g = (1 + beta e g) * blk e g := fun g hg => by
    rw [add_mul, one_mul, beta, mul_assoc _ _ (blk e g), h2 g hg, mul_one]
    exact hdec g (htri g hg)
  have hs : ∀ g ∈ Γ, sec e c g = (1 + (beta e g - linExt c (beta e g))) * blk e g := fun g hg => by
    have h0 := corner_mul hE (hc (beta e g)).2 (hβ g hg)
    have : sec e c g = (1 - linExt c (beta e g)) * ((1 + beta e g) * blk e g) := by
      rw [← hg1 g hg]; rfl
    rw [this, ← mul_assoc]
    congr 1
    rw [mul_add, sub_mul, sub_mul, h0]
    simp only [mul_one, one_mul, sub_zero]
    abel
  have hsub : ∀ x y : Matrix ι ι ℂ, e.map (algebraMap ℚ ℂ) * x * (1 - e.map (algebraMap ℚ ℂ)) = x →
      e.map (algebraMap ℚ ℂ) * y * (1 - e.map (algebraMap ℚ ℂ)) = y →
      e.map (algebraMap ℚ ℂ) * (x - y) * (1 - e.map (algebraMap ℚ ℂ)) = x - y := fun x y hx hy => by
    rw [mul_sub (e.map (algebraMap ℚ ℂ)) x y, sub_mul, hx, hy]
  have hconst : ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → sec e c x = sec e c x' := by
    intro x hx x' hx' hxx
    have hε := hsub _ _ (hβ x hx) (hβ x' hx')
    have h0 := corner_mul hE hε (hβ x' hx')
    have hxe : x = (1 + (beta e x - beta e x')) * x' := by
      have : (1 + (beta e x - beta e x')) * x'
          = (1 + (beta e x - beta e x')) * ((1 + beta e x') * blk e x') := by rw [← hg1 x' hx']
      rw [this, ← mul_assoc, ← hxx]
      have h3 : (1 + (beta e x - beta e x')) * (1 + beta e x') = 1 + beta e x := by
        rw [mul_add, add_mul _ _ (beta e x'), h0]
        simp only [mul_one, one_mul, add_zero]
        abel
      rw [h3]; exact hg1 x hx
    have hmem : 1 + (beta e x - beta e x') ∈ Γ := by
      have h4 : x * x'.adjugate = 1 + (beta e x - beta e x') := by
        have : x * x'.adjugate = ((1 + (beta e x - beta e x')) * x') * x'.adjugate := by rw [← hxe]
        rw [this, mul_assoc, Matrix.mul_adjugate, hΓ.det_eq x' hx', one_smul, mul_one]
      rw [← h4]
      exact hΓ.mul_mem _ hx _ (hΓ.adj_mem _ hx')
    have h5 := hfix _ hmem hε
    rw [linExt_sub] at h5
    rw [hs x hx, hs x' hx', hxx]
    congr 2
    rw [sub_eq_iff_eq_add.mp h5]
    abel
  have hb : ∀ i j, ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev (f i j) x = ev b (blk e x) := fun i j =>
    _root_.GlobalTheory.ClassFin.descend_blk_rat ι Γ e hΓ he htri (f i j) fun x hx x' hx' hxx => by
      rw [hf, hf, hconst x hx x' hx' hxx]
  choose b hb using hb
  have hbs : ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) = sec e c g := fun g hg => by
    ext i j; rw [Matrix.of_apply, ← hb i j g hg, hf]
  refine ⟨c, b, hc, ?_, fun g hg => ?_⟩
  · have h := hbs 1 hΓ.one_mem
    rw [hb1] at h
    rw [h]
    have h0 : beta e (1 : Matrix ι ι ℂ) = 0 := by
      rw [beta, mul_one, mul_sub, mul_one, hE, sub_self, zero_mul]
    rw [sec, h0, linExt_zero, sub_zero, mul_one]
  · rw [hbs g hg]
    refine ⟨?_, ?_, ?_⟩
    · have h := (hc (0 - beta e g)).1
      rw [linExt_sub, linExt_zero, ← add_sub_assoc, add_zero] at h
      exact hΓ.mul_mem _ h _ hg
    · have h := corner_diag hE (corner_mul_comm (hcomm g) (hsub _ _ (hβ g hg) (hc (beta e g)).2))
      have h' := hbb g
      rw [hs g hg, add_mul, one_mul]
      generalize (beta e g - linExt c (beta e g)) * blk e g = y at h
      generalize blk e g = D at h' ⊢
      have : blk e (D + y) = blk e D + (e.map (algebraMap ℚ ℂ) * y * e.map (algebraMap ℚ ℂ) +
          (1 - e.map (algebraMap ℚ ℂ)) * y * (1 - e.map (algebraMap ℚ ℂ))) := by
        simp only [blk, mul_add, add_mul]; abel
      rw [this, h, h', add_zero]
    · have h0 := corner_mul hE (hc (beta e g)).2 (hc (beta e g)).2
      change g = (1 + linExt c (beta e g)) * ((1 - linExt c (beta e g)) * g)
      rw [← mul_assoc, mul_sub, add_mul _ _ (linExt c (beta e g)), h0]
      simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalInvariantTensor
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatInvTensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordAlg (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Subalgebra ℂ (Matrix ι ι ℂ → ℂ) :=
  Algebra.adjoin ℂ {φ | ∃ p ∈ S, ∃ b, φ = fun y => ((fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 y) b}

def AllFixed (Γ : Set (Matrix ι ι ℂ)) (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Prop :=
  ∀ p ∈ S, ∀ g ∈ Γ, (fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 g = fun a => ((p.2 a : ℚ) : ℂ)

def Good (Γ : Set (Matrix ι ι ℂ)) (φ : Matrix ι ι ℂ → ℂ) : Prop :=
  ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧ φ ∈ coordAlg S

theorem coordAlg_mono {S T : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))} (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  apply Algebra.adjoin_mono
  rintro φ ⟨p, hp, b, rfl⟩
  exact ⟨p, h hp, b, rfl⟩

theorem good_zero (Γ : Set (Matrix ι ι ℂ)) : Good Γ 0 :=
  ⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩

theorem Good.add {Γ : Set (Matrix ι ι ℂ)} {φ ψ : Matrix ι ι ℂ → ℂ} (h1 : Good Γ φ) (h2 : Good Γ ψ) :
    Good Γ (φ + ψ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  obtain ⟨T, hT, fT, mT⟩ := h2
  refine ⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS)
    (coordAlg_mono Set.subset_union_right mT)⟩
  rintro p (hp | hp)
  · exact fS p hp
  · exact fT p hp

theorem Good.smul {Γ : Set (Matrix ι ι ℂ)} {φ : Matrix ι ι ℂ → ℂ} (c : ℂ) (h1 : Good Γ φ) :
    Good Γ (c • φ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  exact ⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩

theorem good_sum {Γ : Set (Matrix ι ι ℂ)} {β : Type} (s : Finset β) (φ : β → Matrix ι ι ℂ → ℂ)
    (h : ∀ b, Good Γ (φ b)) : Good Γ (∑ b ∈ s, φ b) :=
  Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)

theorem good_coord {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (n : ℕ) (l : (Fin n → ι) → ℂ)
    (hl : ∀ g ∈ Γ, l ᵥ* tpow n g = l) (b : Fin n → ι) : Good Γ (fun y => (l ᵥ* tpow n y) b) := by
  have h := _root_.GlobalTheory.ClassFin.RationalInvariants.mem_span_rational ι Γ hΓ.aut_mem n l hl
  clear hl
  induction h using Submodule.span_induction with
  | mem μ hμ =>
    obtain ⟨h1, h2⟩ := hμ
    choose q hq using h2
    have hμ : μ = fun a => ((q a : ℚ) : ℂ) := funext hq
    subst hμ
    refine ⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩
    rintro p rfl
    exact h1
  | zero =>
    have : (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0 := by
      funext y; simp
    rw [this]; exact good_zero Γ
  | add u v _ _ hu hv =>
    have : (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) =
        (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b := by
      funext y; simp [Matrix.add_vecMul]
    rw [this]; exact hu.add hv
  | smul c u _ hu =>
    have : (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) =
        c • (fun y => (u ᵥ* tpow n y) b) := by
      funext y; simp [Matrix.smul_vecMul]
    rw [this]; exact hu.smul c

theorem good_homog {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) (n : ℕ)
    (F : MvPolynomial (ι × ι) ℂ) (hF : IsInv Γ F) (hn : F.IsHomogeneous n) : Good Γ (evC F) := by
  obtain ⟨l, hl, hev⟩ := _root_.GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors ι Γ hΓ hS n F hF hn
  have : evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b := by
    funext y; rw [hev, Finset.sum_apply]
  rw [this]
  exact good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b

theorem exists_finite_family {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) :
    ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧
      ∀ f, IsInv Γ f → evC f ∈ coordAlg S := by
  obtain ⟨Rey, hR⟩ := _root_.GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds ι Γ hΓ hS
  obtain ⟨s, hs, hgen⟩ := _root_.GlobalTheory.ClassFin.HilbertFin.hilbert_finiteness ι Γ Rey hR
  have hg : ∀ F : s, Good Γ (evC F.1) := fun F => by
    obtain ⟨h1, n, h2⟩ := hs F.1 F.2
    exact good_homog hΓ hS n F.1 h1 h2
  choose S hfin hfix hmem using hg
  refine ⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩
  · intro p hp
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hp
    exact hfix F p hF
  · intro f hf
    have h := hgen f hf
    clear hf
    induction h using Algebra.adjoin_induction with
    | mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)
    | algebraMap c =>
      have : evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c := by
        funext y; simp [evC]
      rw [this]; exact Subalgebra.algebraMap_mem _ c
    | add u v _ _ hu hv =>
      have : evC (u + v) = evC u + evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv =>
      have : evC (u * v) = evC u * evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.mul_mem _ hu hv

theorem exists_rational_invariant_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  intro ι _ _ Γ hΓ hS
  obtain ⟨S, hfin, hfix, hmem⟩ := exists_finite_family hΓ hS
  obtain ⟨m, e, -, he⟩ := hfin.fin_param
  refine ⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩
  · intro g hg
    funext k
    exact congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2
  · intro f hf
    have h := hmem f hf
    generalize evC f = φ at h
    induction h using Algebra.adjoin_induction with
    | mem φ hφ =>
      obtain ⟨p, hp, b, rfl⟩ := hφ
      rw [← he] at hp
      obtain ⟨i, rfl⟩ := hp
      exact ⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩
    | algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P + Q, fun y => by rw [map_add (f := _), ← hP, ← hQ]; rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩

end GlobalTheory.ClassFin.RatInvTensor
end

