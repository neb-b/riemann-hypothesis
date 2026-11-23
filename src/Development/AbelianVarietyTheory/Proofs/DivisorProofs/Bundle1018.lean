module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0979
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.HeckeEpsAbs

variable {E : Type} [Field E] [NumberField E]

theorem norm_gaussSumAt_sq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hχ : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow χ w a c ha hχ hu hc

theorem norm_locK {χ : HChar E} (hu : IsUnitary χ) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ‖((χ.locK w x : ℂˣ) : ℂ)‖ = 1 := hu _

theorem absNorm_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < Ideal.absNorm w.asIdeal :=
  Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem natCast_pow_cpow {N : ℕ} (hN : (N : ℂ) ≠ 0) (k : ℕ) (t : ℂ) :
    (((N ^ k : ℕ) : ℂ)) ^ t = (N : ℂ) ^ ((k : ℂ) * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, ← Complex.cpow_add _ _ hN]
    congr 1; push_cast; ring

theorem prod_natCast_cpow {ι : Type} (S : Finset ι) (f : ι → ℕ) (t : ℂ) :
    ∏ i ∈ S, ((f i : ℕ) : ℂ) ^ t = (((∏ i ∈ S, f i : ℕ)) : ℂ) ^ t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem locEps_eq_mul (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (s : ℂ) :
    locEps χ w k s = locEps χ w k (1 / 2) * (((Ideal.absNorm w.asIdeal ^ (k + diffExp w) : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (absNorm_pos w).ne'
  rw [natCast_pow_cpow hN]
  simp only [locEps]
  have e : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * ((k + diffExp w : ℕ) : ℂ)) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(1 / 2) * ((k + diffExp w : ℕ) : ℂ)) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((k + diffExp w : ℕ) : ℂ) * (1 / 2 - s)) := by
    rw [← Complex.cpow_add _ _ hN]; congr 1; ring
  rw [e]; ring

theorem norm_locEps_half {χ : HChar E} (hu : IsUnitary χ) {w : HeightOneSpectrum (𝓞 E)} {k : ℕ} (hk : ExpAt χ w k) :
    ‖locEps χ w k (1 / 2)‖ = 1 := by
  have hNpos : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos w
  have hG : ‖(if k = 0 then (1 : ℂ) else gaussSumAt χ w k (unif w ^ (k + diffExp w)))‖ =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
    split_ifs with h
    · simp [h]
    · have := norm_gaussSumAt_sq χ w k _ h hk hu (valuation_unif_pow w _)
      rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      ring_nf
  rw [locEps, norm_mul, norm_mul, norm_mul, norm_locK hu, hG, Complex.norm_natCast_cpow_of_pos (absNorm_pos w),
    Complex.norm_natCast_cpow_of_pos (absNorm_pos w), one_mul, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  convert Real.rpow_zero _ using 2
  simp
  ring

theorem absNorm_different_eq_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ w, w ∉ S → diffExp w = 0) :
    Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ diffExp w := by
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hm : ∀ w : HeightOneSpectrum (𝓞 E), w.maxPowDividing (differentIdeal ℤ (𝓞 E)) = w.asIdeal ^ diffExp w := by
    intro w
    rw [w.maxPowDividing_eq_pow_multiset_count hD, diffExp, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hD]
  have h := Ideal.finprod_heightOneSpectrum_factorization hD
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_] at h
  · conv_lhs => rw [← h]
    rw [map_prod]
    simp only [hm, map_pow]
  · intro w hw
    by_contra h'
    apply hw
    show w.maxPowDividing _ = 1
    rw [hm, hS w h', pow_zero]

theorem finEps_eq (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    finEps χ a s = finEps χ a (1 / 2) *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  classical
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  set S : Finset (HeightOneSpectrum (𝓞 E)) := ((Ideal.finite_factors hD).union a.support.finite_toSet).toFinset with hSdef
  have hS : ∀ w, w ∉ S → diffExp w = 0 ∧ a w = 0 := by
    intro w hw
    simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at hw
    exact ⟨multiplicity_eq_zero_of_not_dvd hw.1, hw.2⟩
  have hsub : ∀ f : HeightOneSpectrum (𝓞 E) → ℂ, (∀ w, diffExp w = 0 → a w = 0 → f w = 1) → Function.mulSupport f ⊆ S := by
    intro f hf w hw
    by_contra h
    exact hw (hf w (hS w h).1 (hS w h).2)
  have e1 : ∀ z, finEps χ a z = ∏ w ∈ S, locEps χ w (a w) z := fun z =>
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun w h0 h1 => by rw [h1]; exact locEps_eq_one χ h0 z)
  have e3 : (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ)) =
      ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ (a w + diffExp w) := by
    rw [← absNorm_differentIdeal E (𝓞 E), absNorm_different_eq_prod S fun w hw => (hS w hw).1, Finsupp.prod,
      Finset.prod_subset (s₁ := a.support) (s₂ := S) ?_ ?_, ← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [← pow_add, add_comm]
    · intro w hw
      simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe]
      exact Or.inr hw
    · intro w _ hw
      rw [Finsupp.notMem_support_iff.1 hw, pow_zero]
  rw [e1, e1, e3, ← prod_natCast_cpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => locEps_eq_mul χ w (a w) s

theorem norm_finEps_half {χ : HChar E} (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    ‖finEps χ a (1 / 2)‖ = 1 := by
  have hf := finite_mulSupport_locEps χ a (1 / 2)
  rw [finEps, finprod_eq_prod_of_mulSupport_subset _ hf.coe_toFinset.ge, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_locEps_half hu (ha w)

theorem norm_archEps {I : Type} [Fintype I] (n : I → ℤ) : ‖archEps n‖ = 1 := by
  simp [archEps]

end GlobalTheory.HeckeEpsAbs

namespace GlobalTheory.Published

open GlobalTheory.HeckeEpsAbs

theorem HeckeTateFunctionalEquation.abs (h : HeckeTateFunctionalEquation) : HeckeFunctionalEquationAbs := by
  intro E _ _ _ I _ φ hφ χ n a Λ Λ' hu hi hn ha hΛ hΛ'
  obtain ⟨Λ₀, Λ₀', h1, h2, h3⟩ := h E I φ hφ χ n a hu hi hn ha
  obtain rfl := hΛ.unique h1
  obtain rfl := hΛ'.unique h2
  refine ⟨archEps n * finEps χ a (1 / 2), ?_, fun s => ?_⟩
  · rw [norm_mul, norm_archEps, norm_finEps_half hu ha, one_mul]
  · rw [h3 s, finEps_eq χ a s]
    ring

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic : GlobalTheory.EtC.B5 := by
  first | (exact @GlobalTheory.EtC.b5) | (exact GlobalTheory.EtC.b5) | (intros; apply GlobalTheory.EtC.b5  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adele_ext : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  intro F E _ _ _ _ _
  classical
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  let φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun c => ∑ i, c i • B i
  have hφ : Continuous φ := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  refine ⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩
  choose x hx using fun i => hK' (B.repr a i)
  refine ⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hincl : inclR (F := F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul,
      Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]
  simp only [φ, sub_smul, Finset.sum_sub_distrib, hincl]
  rw [B.sum_repr a]

end GlobalTheory.AdeleCocompactExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIwasawaMaximalParabolicFiniteReps
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.IwaParab

def projP (R : Type) [CommRing R] (a r : ℕ) : Matrix (Fin a) (Fin a) R :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

theorem projP_mul_self (R : Type) [CommRing R] (a r : ℕ) : projP R a r * projP R a r = projP R a r := by
  rw [projP, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem entry_QMP {R : Type} [CommRing R] {a r : ℕ} (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    ((1 - projP R a r) * M * projP R a r) i j = if r ≤ (i : ℕ) ∧ (j : ℕ) < r then M i j else 0 := by
  simp only [projP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
  split_ifs <;> first | (exfalso; omega) | ring

theorem entry_PMQ {R : Type} [CommRing R] {a r : ℕ} (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    (projP R a r * M * (1 - projP R a r)) i j = if (i : ℕ) < r ∧ r ≤ (j : ℕ) then M i j else 0 := by
  simp only [projP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
  split_ifs <;> first | (exfalso; omega) | ring

end GlobalTheory.IwaParab

namespace GlobalTheory.IwaParab

theorem nilM_neg {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) : nilM (-x) = -nilM x := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.neg_apply, Pi.neg_apply]; split_ifs <;> simp

theorem exists_unip_mul {R : Type} [CommRing R] (a r : ℕ) (g : GL (Fin a) R)
    (hg : ∀ i j : Fin a, (j : ℕ) < r → r ≤ (i : ℕ) → g.1 i j = 0) :
    ∃ (y : BlockIx a r → R) (m : GL (Fin a) R),
      (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧ g = unip y * m := by
  classical
  set P := projP R a r with hPdef
  have hPP : P * P = P := projP_mul_self R a r
  set G : Matrix (Fin a) (Fin a) R := g.1 with hG
  set H : Matrix (Fin a) (Fin a) R := (g⁻¹ : GL (Fin a) R).1 with hH
  have hHG : H * G = 1 := by rw [hH, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  let blk : Fin a → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hBT : G.BlockTriangular blk := by
    intro i j h
    have : (j : ℕ) < r ∧ r ≤ (i : ℕ) := by
      simp only [blk] at h; split_ifs at h <;> first | (exfalso; omega) | (constructor <;> omega)
    exact hg i j this.1 this.2
  letI : Invertible G := Units.invertible g
  have hBTi : H.BlockTriangular blk := by
    have h := Matrix.blockTriangular_inv_of_blockTriangular hBT
    have e : H = G⁻¹ := by rw [hH, hG, Matrix.coe_units_inv]
    rw [e]; exact h
  have hGP : (1 - P) * G * P = 0 := by
    ext i j; rw [entry_QMP, Matrix.zero_apply]; split_ifs with h
    · exact hg i j h.2 h.1
    · rfl
  have hHP : (1 - P) * H * P = 0 := by
    ext i j; rw [entry_QMP, Matrix.zero_apply]; split_ifs with h
    · exact hBTi (by simp only [blk]; split_ifs <;> omega)
    · rfl

  set X : Matrix (Fin a) (Fin a) R := P * (G * (1 - P) * H) * (1 - P) with hX
  let y : BlockIx a r → R := fun p => X p.1.1 p.1.2
  have hy : nilM y = X := by
    ext i j
    simp only [nilM, Matrix.of_apply, y]
    split_ifs with h
    · rfl
    · rw [hX, entry_PMQ, if_neg h]
  refine ⟨y, unip (-y) * g, ?_, ?_⟩
  · have hm : (unip (-y) * g).1 = (1 - X) * G := by
      change (1 + nilM (-y)) * G = _
      rw [nilM_neg, hy, sub_eq_add_neg]
    have h1 : (1 - P) * (unip (-y) * g).1 * P = 0 := by
      rw [hm]
      have e : (1 - P) * ((1 - X) * G) * P =
          (1 - P) * G * P - (P - P * P) * (G * (1 - P) * H * (1 - P) * G * P) := by
        rw [hX]; noncomm_ring
      rw [e, hGP, hPP, sub_self, zero_mul, sub_zero]
    have key : (1 - P) * H * (1 - P) * G * (1 - P) = 1 - P := by
      have e2 : (1 - P) * H * (1 - P) * G * (1 - P) =
          (1 - P) * (H * G) * (1 - P) - ((1 - P) * H * P) * (G * (1 - P)) := by noncomm_ring
      have e3 : (1 - P) * (1 - P) = 1 - P - (P - P * P) := by noncomm_ring
      rw [e2, hHG, hHP, zero_mul, sub_zero, mul_one, e3, hPP, sub_self, sub_zero]
    have h2 : P * (unip (-y) * g).1 * (1 - P) = 0 := by
      rw [hm]
      have e : P * ((1 - X) * G) * (1 - P) =
          P * G * (1 - P) - (P * P) * G * ((1 - P) * H * (1 - P) * G * (1 - P)) := by
        rw [hX]; noncomm_ring
      rw [e, key, hPP]; noncomm_ring
    intro i j
    by_cases hij : ((i : ℕ) < r ↔ (j : ℕ) < r)
    · exact Or.inl hij
    · right
      by_cases hi : (i : ℕ) < r
      · have := congrFun (congrFun h2 i) j
        rw [entry_PMQ, if_pos ⟨hi, by by_contra hj; exact hij ⟨fun _ => by omega, fun _ => hi⟩⟩] at this
        exact this
      · have := congrFun (congrFun h1 i) j
        rw [entry_QMP, if_pos ⟨by omega, by by_contra hj; exact hij ⟨fun h => absurd h hi, fun h => absurd h hj⟩⟩] at this
        exact this
  · rw [← mul_assoc, ← unip_add, add_neg_cancel]
    have h0 : unip (0 : BlockIx a r → R) = 1 := by
      ext i j
      change (1 + nilM (0 : BlockIx a r → R)) i j = (1 : Matrix (Fin a) (Fin a) R) i j
      simp [nilM]
    rw [h0, one_mul]

end GlobalTheory.IwaParab

namespace GlobalTheory.IwaParab

open scoped Pointwise

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ T : Finset (GL (Fin a) (Af E)), ∀ k ∈ PIW.ClassFinD.KGL E a, ∃ t ∈ T, ∃ l ∈ L, k = t * l := by
  classical
  have hK := GlobalTheory.isCompact_KGL E a
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun t : PIW.ClassFinD.KGL E a => (t : GL (Fin a) (Af E)) • (L : Set (GL (Fin a) (Af E))))
    (fun t => hL.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, ⟨1, L.one_mem, mul_one k⟩⟩)
  refine ⟨s.image Subtype.val, fun k hk => ?_⟩
  obtain ⟨t, ht, hkt⟩ := Set.mem_iUnion₂.1 (hs hk)
  obtain ⟨l, hl, hlk⟩ := hkt
  exact ⟨t, Finset.mem_image_of_mem _ ht, l, hl, hlk.symm⟩

theorem upper_infGL_mul_finGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (b : GL (Fin a) (Cinf E)) (hb : (b : Matrix (Fin a) (Fin a) (Cinf E)).BlockTriangular id)
    (c : GL (Fin a) (Af E)) (hc : (c : Matrix (Fin a) (Fin a) (Af E)).BlockTriangular id) :
    ((infGL E a b * finGL E a c : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).BlockTriangular id := by
  rw [Units.val_mul]
  refine Matrix.BlockTriangular.mul ?_ ?_
  · intro i j h
    replace h : j < i := h
    change (cornerGL a (sInf E) b).val i j = 0
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ (ne_of_gt h), hb h, map_zero]
  · intro i j h
    replace h : j < i := h
    change (cornerGL a (sFin E) c).val i j = 0
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ (ne_of_gt h), hc h, map_zero]

theorem iwasawa_parab : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∃ T : Finset (GL (Fin a) (Af E)), ∀ g : GA E a, ∃ (y : BlockIx a r → Ad E) (m : GA E a),
      (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧
      ∃ t ∈ T, ∃ k : Kinf E a, ∃ l ∈ L,
        g = unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l := by
  intro E _ _ _ a r L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E a L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hbk⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E a (Matrix.GeneralLinearGroup.map (pInf E) g)
  obtain ⟨u, s, kf, hu, hs, hkf, hx⟩ := GlobalTheory.IwasawaFinAd.iwasawaAf E a (Matrix.GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, hkt⟩ := hT kf hkf
  have hus : ((u * s : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)).BlockTriangular id := by
    rw [Units.val_mul]
    exact Matrix.BlockTriangular.mul (fun i j h => hu.1 i j h) (fun i j h => hs i j (ne_of_gt h))
  have hB := upper_infGL_mul_finGL b hb (u * s) hus
  obtain ⟨y, m, hm, hBm⟩ := exists_unip_mul a r (infGL E a b * finGL E a (u * s))
    (fun i j hj hi => hB (show j < i from Fin.lt_def.2 (by omega)))
  refine ⟨y, m, hm, t, ht, k, l, hl, ?_⟩
  rw [← hBm]
  conv_lhs => rw [← infGL_mul_finGL g, hbk, hx, hkt]
  have e : u * s * (t * l) = u * s * t * l := by group
  rw [e]
  rw [map_mul (finGL E a) (u * s * t) l, map_mul (infGL E a) b, map_mul (finGL E a) (u * s) t]
  have c : infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t) =
      finGL E a (u * s) * finGL E a t * infGL E a (Unitary.toUnits k) := by
    rw [← map_mul]; exact infGL_comm _ _
  calc infGL E a b * infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t * finGL E a l)
      = infGL E a b * (infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t)) * finGL E a l := by
        simp only [mul_assoc]
    _ = infGL E a b * (finGL E a (u * s) * finGL E a t * infGL E a (Unitary.toUnits k)) * finGL E a l := by rw [c]
    _ = _ := by simp only [mul_assoc]

end GlobalTheory.IwaParab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.SymplSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_inv {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (a b : Fin n) :
    σ (J⁻¹ b a) = J⁻¹ a b := by
  have hmap : J.map σ = Jᵀ := by ext i j; simp [Matrix.transpose_apply, hJ.1 j i]
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have h1 : (J⁻¹).map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]; simp
  have h2 : (J⁻¹).map σ = (J⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, ← hmap]; exact (Matrix.inv_eq_left_inv h1).symm
  have := congrFun (congrFun h2 b) a
  rw [Matrix.map_apply] at this
  rw [this, Matrix.transpose_apply]

noncomputable def cEquiv (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) : AEF F E ≃ₐ[AF F] AEF F E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) (AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun e => hσ e) (AlgHom.ext fun e => hσ e))

theorem cEquiv_apply (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cEquiv σ hσ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ e)) = a ⊗ₜ e
    simp [hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((1 : AF F) ⊗ₜ e) = (1 : AF F) ⊗ₜ σ e
  simp

theorem cAF_hOF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x := by
  unfold hOF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, cAF_incAF, cAF_cAF σ hσ, herm_inv hS, hT.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem symplOF_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  intro F E _ _ _ _ _ σ hσ nS nT JS JT hS hT ξ₀ hξ x y
  unfold symplOF
  have hx : incAF F E ξ₀ = cAF σ (incAF F E (-ξ₀)) := by rw [cAF_incAF, ← hξ, hσ]
  rw [← cAF_hOF σ hσ hS hT x y]
  have key : incAF F E ξ₀ * cAF σ (hOF σ JS JT x y) = cEquiv σ hσ (incAF F E (-ξ₀) * hOF σ JS JT x y) := by
    rw [cEquiv_apply, map_mul, ← hx]
  rw [key, Algebra.trace_eq_of_algEquiv, map_neg, neg_mul, map_neg]

end GlobalTheory.SymplSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitaryStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U, UnitOn s F U → (∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re) ∧ (U ≠ ⊥ → ∃ (ω : ℝ) (v : M), v ∈ U ∧ v ≠ 0 ∧ cas s F v = (ω : ℂ) • v) := by
  first | exact @GlobalTheory.HoweR.cas_diag_unitOn | exact GlobalTheory.HoweR.cas_diag_unitOn | (intros; apply GlobalTheory.HoweR.cas_diag_unitOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerElementPadicBounded
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_element_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_le_one_at_u) | (exact GlobalTheory.StabFin.norm_le_one_at_u) | (intros; apply GlobalTheory.StabFin.norm_le_one_at_u  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilocalConjugateSameCharpoly
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilocal_conjugate_same_charpoly : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} → ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable → ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  first | (exact @GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (exact GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (intros; apply GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable <;> assumption)
end

