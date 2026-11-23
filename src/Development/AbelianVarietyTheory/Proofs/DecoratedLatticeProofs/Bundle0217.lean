module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramified
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SelfDualStabConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_sq_conj_sub (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (x : 𝓞 E) (d : 𝓞 F), d ∉ v.asIdeal ∧ algebraMap F E d = ((x : E) - σ x) ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have := v.isMaximal
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => GlobalTheory.LFun.InertChart.conj_ne h fun x => congrArg (fun t : E ≃ₐ[F] E => t x) hs
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, s • x - x ∉ Q := by
    by_contra hn
    push Not at hn
    have hs : s ∈ Q.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 hn
    rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
    exact hs1 hs
  have hfix : ∀ t : E ≃ₐ[F] E, t (((x : E) - σ x) ^ 2) = ((x : E) - σ x) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have e : (((s • x - x) ^ 2 : 𝓞 E) : E) = ((x : E) - σ x) ^ 2 := by
    change (σ x - (x : E)) ^ 2 = _
    ring
  have hi : IsIntegral ℤ d := by
    rw [← isIntegral_algebraMap_iff (B := E), hd, ← e]
    exact RingOfIntegers.isIntegral_coe _
  refine ⟨x, ⟨d, hi⟩, fun hm => hx (hQ.isPrime.mem_of_pow_mem 2 ?_), hd⟩
  have : (s • x - x) ^ 2 = algebraMap (𝓞 F) (𝓞 E) ⟨d, hi⟩ := RingOfIntegers.ext (e.trans hd.symm)
  rw [this]
  rwa [hQv.over] at hm

def conjInt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict _ _ fun _ => sigR_mem_intLoc σ

theorem exists_isUnit_sub_conj (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E))
    (v : HeightOneSpectrum (𝓞 F)) : ∃ ω : intLoc F E v, IsUnit (ω - conjInt σ v ω) := by
  obtain ⟨x, d, hd, e⟩ := exists_sq_conj_sub h hU v
  have hd0 : (d : F) ≠ 0 := fun h0 => hd (by
    rw [show d = 0 from RingOfIntegers.coe_injective (by simpa using h0)]; exact zero_mem _)
  have ha : algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (d : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hd
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (d : F)⁻¹
    exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))
  refine ⟨⟨_, tmul_mem_intLoc (one_mem _) x⟩, (isUnit_pow_iff two_ne_zero).1
    (IsUnit.of_mul_eq_one ⟨_, tmul_mem_intLoc ha 1⟩ (Subtype.ext ?_))⟩
  change (inclR (Fv F v) (x : E) - inclR (Fv F v) (σ x)) ^ 2 * (algebraMap F (Fv F v) (d : F)⁻¹ ⊗ₜ[F] (1 : E)) = 1
  rw [← map_sub, ← map_pow, ← e, Algebra.algebraMap_eq_smul_one (d : F)⁻¹, TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  change inclR (Fv F v) _ * inclR (Fv F v) _ = 1
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ hd0, map_one, map_one]

theorem exists_norm (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} {B : Matrix (Fin n) (Fin n) (intLoc F E v)} (hB : cT (conjInt σ v) B = B) (hu : IsUnit B) :
    ∃ u : GL (Fin n) (intLoc F E v), cT (conjInt σ v) u.1 * u.1 = B := by
  let O := intLoc F E v
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := GlobalTheory.Orb.finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing (v.adicCompletionIntegers F) O
  let s : O →+* O := conjInt σ v
  have hs : ∀ y : O, s (s y) = y := fun y =>
    Subtype.ext (GlobalTheory.Doubling.sigR_invol (GlobalTheory.LFun.InertChart.conj_conj h) y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hs
    (GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X O I s hs (fun y hy => hI hy) (exists_isUnit_sub_conj h hU v)) hB hu
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (hp ▸ hu)
  exact ⟨h2.unit, hp⟩

theorem cT_mul {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (P Q : Matrix (Fin n) (Fin n) A) :
    cT s (P * Q) = cT s Q * cT s P := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} : cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem exists_orthonormal_frame (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) :
    ∃ b : GL (Fin n) (Fv F v ⊗[F] E), cT (sigR _ σ) b.1 * JR (Fv F v) J * b.1 = 1 ∧
      ∀ y, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v := by
  obtain ⟨a₀, ha₀⟩ := Frames.exists_isLatticeFrame (F := F) L
  have ha := ha₀ v
  generalize bc (compFin F E v) a₀ = a at ha
  have hσ := GlobalTheory.Doubling.sigR_invol (R := Fv F v) (GlobalTheory.LFun.InertChart.conj_conj h)
  have hJu : IsUnit (JR (F := F) (Fv F v) J) := (Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.Doubling.isUnit_det_JR hJ.2)
  have hJh : cT (sigR _ σ) (JR (F := F) (Fv F v) J) = JR (Fv F v) J := by
    ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j)
  have hau : IsUnit (cT (sigR _ σ) a.1) := IsUnit.of_mul_eq_one (cT (sigR _ σ) (a⁻¹).1) (by
    rw [← cT_mul, Units.inv_mul, cT_one])
  obtain ⟨H, hH⟩ := (hau.mul hJu).mul a.isUnit
  obtain ⟨h1, h2⟩ := GlobalTheory.StdUnn.Unimod.gram_int (sigR _ σ) (intLoc F E v) (fun _ => sigR_mem_intLoc σ)
    (JR (Fv F v) J) a.1 (a⁻¹).1 (H⁻¹).1 (fun y => y ∈ latLoc F L v) a.mul_inv (hH ▸ H.mul_inv) ha
    (fun y => SetLike.ext_iff.1 hL y)
  let ι := (intLoc F E v).subtype
  have hinj : ∀ {M N : Matrix (Fin n) (Fin n) (intLoc F E v)}, M.map ι = N.map ι → M = N :=
    fun e => Matrix.map_injective Subtype.val_injective e
  have hcT : ∀ M : Matrix (Fin n) (Fin n) (intLoc F E v), (cT (conjInt σ v) M).map ι = cT (sigR _ σ) (M.map ι) :=
    fun _ => rfl
  let B : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B' : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have eB : B.map ι = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := rfl
  obtain ⟨u, hu⟩ := exists_norm h hU v (B := B)
    (hinj (by rw [hcT, eB, cT_mul, cT_mul, hJh, GlobalTheory.UnitaryDoubleCoset.cT_cT hσ, Matrix.mul_assoc]))
    (IsUnit.of_mul_eq_one B' (hinj (by
      rw [Matrix.map_mul, eB, ← hH, Matrix.map_one _ (map_zero ι) (map_one ι)]; exact H.mul_inv)))
  have hu' : cT (sigR _ σ) (bc ι u).1 * (bc ι u).1 = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := by
    rw [← eB, ← hu, Matrix.map_mul]; rfl
  have hm : ∀ (k : GL (Fin n) (intLoc F E v)) (y : Fin n → Fv F v ⊗[F] E), (∀ i, y i ∈ intLoc F E v) →
      ∀ i, ((bc ι k).1 *ᵥ y) i ∈ intLoc F E v := fun k y hy i => by
    rw [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (k.1 i j).2 (hy j)
  refine ⟨a * (bc ι u)⁻¹, ?_, fun y => ?_⟩
  · have : cT (sigR _ σ) (a * (bc ι u)⁻¹).1 * JR (Fv F v) J * (a * (bc ι u)⁻¹).1 =
        cT (sigR _ σ) ((bc ι u)⁻¹).1 * (cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1) * ((bc ι u)⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, ← hu', ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul, Units.mul_inv]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
    refine ⟨fun hy => by rw [← map_inv]; exact hm _ y hy, fun hy => ?_⟩
    have := hm u _ hy
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem exists_conj_stabLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → Submodule.IsFullLattice E L' →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ J L v → IsSelfDualAt σ J L' v →
    ∃ g : GLoc σ J v, ∀ k : GLoc σ J v, k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v := by
  intro F E _ _ _ _ _ σ h hU n J hJ L L' _ _ v hL hL'
  obtain ⟨b, hb, fb⟩ := exists_orthonormal_frame h hU hJ L hL
  obtain ⟨c, hc, fc⟩ := exists_orthonormal_frame h hU hJ L' hL'
  have hg : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 = JR (Fv F v) J := by
    have : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 =
        cT (sigR _ σ) (b⁻¹).1 * (cT (sigR _ σ) c.1 * JR (Fv F v) J * c.1) * (b⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, hc, ← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let g : GLoc σ J v := ⟨c * b⁻¹, hg⟩
  have eg : matHom _ σ J g = c * b⁻¹ := rfl
  have hm : ∀ y, y ∈ latLoc F L v ↔ (matHom _ σ J g).1 *ᵥ y ∈ latLoc F L' v := fun y => by
    rw [eg, Units.val_mul, ← Matrix.mulVec_mulVec, ← fc, fb, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hact : ∀ (p q : GLoc σ J v) y,
      (matHom _ σ J p).1 *ᵥ ((matHom _ σ J q).1 *ᵥ y) = (matHom _ σ J (p * q)).1 *ᵥ y := fun p q y => by
    rw [Matrix.mulVec_mulVec, map_mul, Units.val_mul]
  refine ⟨g, fun k => ?_⟩
  rw [mem_stabLoc, mem_stabLoc]
  refine ⟨fun hk y => ?_, fun hk y => ?_⟩
  · rw [hm, hm, hk, hact, hact, ← mul_assoc, mul_inv_cancel_left]
  · have := hk ((matHom _ σ J g⁻¹).1 *ᵥ y)
    rwa [hm, hm, hact, hact, hact, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec, mul_assoc,
      mul_inv_cancel_right, mul_inv_cancel_left] at this

end GlobalTheory.SelfDualStabConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsLatticeFrameBcEq
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem idem_glue_mul {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] {e : R} (hee : e * e = e)
    {x y x' y' : Matrix m m R} (h1 : x * x' = 1) (h2 : y * y' = 1) :
    ((1 - e) • x + e • y) * ((1 - e) • x' + e • y') = 1 := by
  have hce : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have hec : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hcc : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, hec, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, h2, hce, hec, hcc, hee, zero_smul,
    add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

def idemGlue {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (e : R) (hee : e * e = e)
    (x y : GL m R) : GL m R :=
  ⟨(1 - e) • (x : Matrix m m R) + e • (y : Matrix m m R),
    (1 - e) • ((x⁻¹ : GL m R) : Matrix m m R) + e • ((y⁻¹ : GL m R) : Matrix m m R),
    idem_glue_mul hee (Units.mul_inv x) (Units.mul_inv y), idem_glue_mul hee (Units.inv_mul x) (Units.inv_mul y)⟩

theorem bc_idemGlue_of_zero {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 0) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ x := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((x : Matrix m m R) i j)
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h, sub_zero, one_mul, zero_mul, add_zero]

theorem bc_idemGlue_of_one {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 1) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ y := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((y : Matrix m m R) i j)
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h, sub_self, zero_mul, one_mul, zero_add]

theorem isLatticeFrame_idemGlue {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {e : AF F ⊗[F] E} (hee : e * e = e) {x : GL (Fin n) (AF F ⊗[F] E)}
    (hx : IsLatticeFrame L x) (y : GL (Fin n) (AF F ⊗[F] E)) (he : ∀ v, compFin F E v e = 0) :
    IsLatticeFrame L (idemGlue e hee x y) := by
  intro v z
  rw [bc_idemGlue_of_zero hee x y _ (he v)]
  exact hx v z

theorem exists_isLatticeFrame_bc_eq (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)) :
    ∃ b : GL (Fin A.rank) (AE D), IsLatticeFrame (frameLat A) b ∧
      ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a := by
  let : Submodule.IsFullLattice D.host.E (frameLat A) := SelfDual.isLattice_frameLat A
  obtain ⟨b₀, hb₀, -⟩ : ∃ b : GL (Fin A.rank) (AE D),
      IsLatticeFrame (frameLat A) b ∧ IsMajorantFrame D.sp.cm.sig A.gram b :=
    Frames.exists_isLatticeFrame_isMajorantFrame (isCMExt_host D) (isHermND_gram A) (frameLat A)
  obtain ⟨e, hee, -, hfin, hinf, -, -⟩ := _root_.GlobalTheory.StdUnn.realIdem_exists D
  exact ⟨idemGlue e hee b₀ a, isLatticeFrame_idemGlue hee hb₀ a hfin, fun w => bc_idemGlue_of_one hee b₀ a _ (hinf w)⟩

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartExist

open Formalism.UG

variable {R : Type} [CommRing R]

theorem cT_mul_gen (σ : R →+* R) {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_gen (σ : R →+* R) {n : Type} [Fintype n] [DecidableEq n] : cT σ (1 : Matrix n n R) = 1 := by
  simp [cT]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) (g : GL n R) (hg : g ∈ UJ σ Q) :
    T⁻¹ * g * T ∈ UJ σ J := by
  have hg' : cT σ (g : Matrix n n R) * Q * g = Q := hg
  show cT σ (((T⁻¹ * g * T : GL n R)) : Matrix n n R) * J * ((T⁻¹ * g * T : GL n R) : Matrix n n R) = J
  have h1 : ((T⁻¹ : GL n R) : Matrix n n R) * T = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ]
  simp only [Units.val_mul, cT_mul_gen, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = cT σ (T : Matrix n n R) * cT σ (g : Matrix n n R) *
        (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) * g * T := by
          simp only [Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * (cT σ (g : Matrix n n R) * Q * g) * T := by
          rw [h3, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * Q * T := by rw [hg']

theorem conj_back (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) :
    cT σ ((T⁻¹ : GL n R) : Matrix n n R) * J * ((T⁻¹ : GL n R) : Matrix n n R) = ((c⁻¹ : Rˣ) : R) • Q := by
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc cT σ ((T⁻¹ : GL n R) : Matrix n n R) * (cT σ (T : Matrix n n R) * Q * T) * ((T⁻¹ : GL n R) : Matrix n n R)
      = (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [h3, h2, Matrix.one_mul, Matrix.mul_one]

def conjEquiv (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) : UJ σ Q ≃* UJ σ J where
  toFun g := ⟨T⁻¹ * g.1 * T, conj_mem σ Q J T c hT g.1 g.2⟩
  invFun h := ⟨T * h.1 * T⁻¹, by
    have := conj_mem σ J Q T⁻¹ c⁻¹ (conj_back σ Q J T c hT) h.1 h.2
    rwa [inv_inv] at this⟩
  left_inv g := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]
  map_mul' g h := by ext1; simp [mul_assoc]

end GlobalTheory.StdUnn.ChartExist


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.ChartExist.gram_adelic (D : D7) (A : HSp D) (μ : D.host.E)
    (hgram : (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank)
    (T : GL (Fin (A.rank + A.rank)) (AE D)) (hTv : T.val = rat (Tm A μ)) (c : (AE D)ˣ) (hc : (c : AE D) = incA D μ) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val
      * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (dblSp A).gram : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) (AE D)) * T.val
      = (c : AE D) • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (Jst D A.rank) := by
  have e1 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val = ((Tm A μ)ᴴ).map (incA D) := by
    rw [hTv]; ext i j; rfl
  rw [e1, hTv, hc]
  change ((Tm A μ)ᴴ).map (incA D) * ((dblSp A).gram).map (incA D) * (Tm A μ).map (incA D) = (incA D μ) • (Jst D A.rank).map (incA D)
  rw [← Matrix.map_mul, ← Matrix.map_mul, hgram]
  ext i j
  simp [Matrix.map_apply, map_mul]


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.chart_exists : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∃ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ := by
  intro D A μ hμ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hdetR : IsUnit (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det := by
    have : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det = incA D (Tm A μ).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hdet.map (incA D)
  let T : GL (Fin (A.rank + A.rank)) (AE D) := Matrix.nonsingInvUnit _ hdetR
  have hTv : T.val = rat (Tm A μ) := rfl
  have hμu : IsUnit (incA D μ) := (Ne.isUnit hμ.1).map (incA D)
  refine ⟨conjEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) _ _ T hμu.unit
    (gram_adelic D A μ hgram T hTv hμu.unit hμu.unit_spec), ?_⟩
  intro g
  show (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * (T⁻¹ * g.1 * T).val = g.1.val * rat (Tm A μ)
  rw [← hTv]
  simp only [Units.val_mul, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn

theorem exists_unique_of_comp_finPart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  intro D θ hθ m n z x₀
  have hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w) := fun τ w =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)
  let C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ := fun τ =>
    (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix
  have hC : ∀ τ w, compAt θ τ w = C τ w := fun τ w => rfl
  let P : Mx D m n →+ Matrix (Fin m) (Fin n) _ := ((finPart D).toAddMonoidHom).mapMatrix
  have hP : ∀ w : Mx D m n, w.map (finPart D) = P w := fun w => rfl
  have key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y := by
    intro x y h1 h2
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    refine (_root_.GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_
    · have := congrFun (congrFun (h1 τ) i) j
      simp only [compAt, Matrix.map_apply] at this
      rw [(infPart D).map_sub, (θ τ).map_sub, this, sub_self]
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at this
      rw [(finPart D).map_sub, this, sub_self]
  refine ⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hC, map_add (f := _), map_sum, ← hC]
    simp_rw [← hC, (hL _ _).2.2 1 τ]
    rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
    abel
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hP, map_add (f := _), map_sum]
    simp_rw [← hP, (hL _ _).2.1 1]
    simp
  · rintro y ⟨hy1, hy2⟩
    apply key
    · intro τ
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy1, hC, map_add (f := _), map_sum, ← hC]
      simp_rw [← hC, (hL _ _).2.2 1 τ]
      rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
      abel
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hy2, hP, hP, map_add (f := _), map_sum]
      simp_rw [← hP, (hL _ _).2.1 1]
      simp

end GlobalTheory.StdUnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilationStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSchwartz_killed_by_longAnnihilation : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ φ ∈ fockA θ V n l s, ∃ N : ℕ, ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0 := by
  first | exact @GlobalTheory.FockAnnKill.fockA_killed_by_annS | exact GlobalTheory.FockAnnKill.fockA_killed_by_annS | (intros; apply GlobalTheory.FockAnnKill.fockA_killed_by_annS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpace
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

theorem GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA :
    ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ ↔ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n φ
  exact ⟨fun h => GlobalTheory.SchwartzBruhatTensor.mem_schwartzA_of_isSchwartzBruhat D θ hθ m n φ h,
    fun h => _root_.GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ h⟩
end

