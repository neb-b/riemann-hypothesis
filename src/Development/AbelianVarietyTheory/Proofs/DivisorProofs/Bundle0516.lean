module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointClosureFiniteEtaleStrictHenselian
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale :
    ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : _root_.GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (_root_.GlobalTheory.LocAcyc.GenFib A R) D → _root_.GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  intro A R O B _ _ _ _ _ _ _ _ _ _ j β ψ hψ D _ _ hfin hE
  letI : Algebra R D := (_root_.GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI : Algebra R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) :=
    _root_.GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨hEfin, hEet, hEnt⟩ := hE
  haveI := hEfin
  haveI := hEet
  haveI := hEnt
  haveI := hfin
  letI : Algebra R O := j.toAlgebra
  haveI : Module.Free R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) := Module.free_of_flat_of_isLocalRing
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := _root_.GlobalTheory.KeyOriginNoeth.closure A R D)
    ⟨RingHom.ker (algebraMap R (ResidueField O)), RingHom.ker_isPrime _⟩
  have hq' : Ideal.comap (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)) q.asIdeal =
      RingHom.ker (algebraMap R (ResidueField O)) := congrArg PrimeSpectrum.asIdeal hq
  obtain ⟨φ₀⟩ := _root_.GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed q.asIdeal hq'
  obtain ⟨φ, -⟩ := (_root_.GlobalTheory.EtaleHensel.bijective_residue_comp R
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) O).2 φ₀
  letI : Algebra (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  haveI : IsScalarTower R (_root_.GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalization ((Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D))) D := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map
        (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D)
    · intro d
      obtain ⟨⟨m, hm⟩, hmint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) d
        (Algebra.IsIntegral.isIntegral (R := _root_.GlobalTheory.LocAcyc.GenFib A R) d)
      refine ⟨⟨⟨m • d, hmint⟩, ⟨algebraMap R _ m, m, hm, rfl⟩⟩, ?_⟩
      show d * algebraMap R D m = m • d
      rw [Algebra.smul_def, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  have hσ : ∀ r : R, β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r)) =
      ψ (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R) r) := by
    intro r
    rw [φ.commutes]
    exact (RingHom.congr_fun hψ r).symm
  have hunits : ∀ y : (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)), IsUnit ((β.comp φ.toRingHom) y) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    show IsUnit (β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) s)))
    rw [hσ]
    exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map ψ
  refine ⟨IsLocalization.lift (S := D) hunits, ?_⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  ext r
  have hr : algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D (algebraMap R _ r) =
      algebraMap (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D
        (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r) := rfl
  simp only [RingHom.comp_apply]
  rw [hr, IsLocalization.lift_eq]
  exact hσ r

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
section
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_pow_eq_of_integers {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {n : ℕ} (hn : 0 < n) (a : O) : ∃ b : O, b ^ n = a := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) hn
  have h1 : v c ^ n ≤ 1 := by
    rw [← map_pow, hc]
    exact hv.map_le_one a
  obtain ⟨b, rfl⟩ := hv.exists_of_le_one ((pow_le_one_iff hn.ne').1 h1)
  exact ⟨b, hv.hom_inj (by rw [map_pow, hc])⟩

theorem omega_finite_projective (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) :
    Module.Finite O G.omega ∧ Module.Projective O G.omega := by
  have : IsDomain O := hv.hom_inj.isDomain _
  have : ValuationRing O := ValuationRing.of_integers v hv
  have hp : (p : O) ≠ 0 := fun h => by
    have := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 this)
  have htf : ∀ w : G.omega, (p : O) • w = 0 → w = 0 :=
    _root_.GlobalTheory.omega_eq_zero_of_p_smul_eq_zero p O G fun n => _root_.GlobalTheory.PDiv.cotMap_injective_of_sq O _ _ (G.mulP n)
      (_root_.GlobalTheory.PDivGroup.mulP_mem_sq_counit p O hp Fact.out (exists_pow_eq_of_integers hv (Fact.out : p.Prime).pos) G n)
  have htfk : ∀ (k : ℕ) (w : G.omega), (p : O) ^ k • w = 0 → w = 0 := fun k => by
    induction k with
    | zero => intro w hw; rwa [pow_zero, one_smul] at hw
    | succ k ih => intro w hw; exact htf w (ih _ (by rw [← mul_smul, ← pow_succ, hw]))
  have : Module.Finite O G.omega := by
    have h := Module.Finite.equiv (G.omegaQuotEquiv 1).symm
    rw [pow_one] at h
    exact GlobalTheory.finite_of_isHausdorff_of_finite_quotient (Ideal.span {(p : O)}) _
  have : Module.Flat O G.omega := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro w ⟨⟨a, ha⟩, hw⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have : ∃ k, a ∣ (p : O) ^ k := by
      by_contra! hk
      refine ha0 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) a fun k => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact (ValuationRing.dvd_total _ _).resolve_left (hk k)
    obtain ⟨k, c, hc⟩ := this
    have hw' : a • w = 0 := hw
    exact htfk k w (by rw [hc, mul_comm, mul_smul, hw', smul_zero])
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConvolutionEqDerivative
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem foldr_rightDeriv_leftTranslate {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    (l : List 𝔤) (f : G → ℂ) (g : G) :
    l.foldr h.rightDeriv (fun y => f (g * y)) = fun x => l.foldr h.rightDeriv f (g * x) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, ih]
    exact h.rightDeriv_leftTranslate X (l.foldr h.rightDeriv f) g

theorem exists_alpha_convolution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ l : List 𝔤, ∃ α : G → ℂ, h.IsSmoothFun α ∧ Continuous α ∧ HasCompactSupport α ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g, ∫ y, (f : G → ℂ) (g * y) * α y ∂μ = l.foldr h.rightDeriv (f : G → ℂ) g := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ l
  obtain ⟨hcont, hinv, K, hK, hfam⟩ := _root_.GlobalTheory.HCA.solG_smFn 𝔸 G 𝔤 h d b P hP μ hμ
  obtain ⟨α, hαs, hαc, hα⟩ := _root_.GlobalTheory.HCA.smFn_nil_eq_integral_smooth 𝔸 G 𝔤 h d b μ hμ (solG h b P) hcont hinv K hK _ (hfam l)
  refine ⟨α, hαs, ?_, hαc, ?_⟩
  · letI := h.chartedSpace
    exact hαs.continuous
  · intro f hf g
    have hmem : (f : G → ℂ) ∈ solG h b P := (mem_solG h b).2 ⟨f.2, hf⟩
    have h1 := hα _ (hinv _ hmem g)
    simp only [List.map_nil, List.nil_append] at h1
    rw [h1, foldr_rightDeriv_leftTranslate h l (f : G → ℂ) g]
    simp only [mul_one]

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Inh

variable {A : Type} [CommRing A] {n : ℕ}

theorem isUniUp_one : IsUniUp (1 : Matrix (Fin n) (Fin n) A) := by
  intro a b
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => ?_⟩
  subst h; exact Matrix.one_apply_eq a

theorem diag_mul_of_tri {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ a c : Fin n, c < a → M a c = 0)
    (hN : ∀ a c : Fin n, c < a → N a c = 0) (a : Fin n) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h, zero_mul]
    · rw [hN c a h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem isUniUp_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : IsUniUp (M * N) := by
  intro a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [(hM a c).1 h, zero_mul]
    · rw [(hN c b).1 (lt_of_lt_of_le hba h), mul_zero]
  · rintro rfl
    rw [diag_mul_of_tri (fun a c h => (hM a c).1 h) (fun a c h => (hN a c).1 h), (hM a a).2 rfl, (hN a a).2 rfl, one_mul]

theorem isUniUp_inv (u : GL (Fin n) A) (hu : IsUniUp (u : Matrix (Fin n) (Fin n) A)) :
    IsUniUp ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  have hb : Matrix.BlockTriangular (u : Matrix (Fin n) (Fin n) A) id := fun i j h => (hu i j).1 h
  have hinv : Matrix.BlockTriangular ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) id := by
    rw [Matrix.coe_units_inv]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  intro a b
  refine ⟨fun h => hinv h, ?_⟩
  rintro rfl
  have h1 : (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (u : Matrix (Fin n) (Fin n) A)) a a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [diag_mul_of_tri (fun a c h => hinv h) (fun a c h => hb h), (hu a a).2 rfl, mul_one] at h1
  exact h1

def uniUpGL : Subgroup (GL (Fin n) A) where
  carrier := {u | IsUniUp (u : Matrix (Fin n) (Fin n) A)}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq, Units.val_mul]; exact isUniUp_mul ha hb
  one_mem' := by rw [Set.mem_setOf_eq, Units.val_one]; exact isUniUp_one
  inv_mem' := fun {u} hu => isUniUp_inv u hu

theorem mem_uniUpGL (u : GL (Fin n) A) : u ∈ (uniUpGL : Subgroup (GL (Fin n) A)) ↔ IsUniUp (u : Matrix (Fin n) (Fin n) A) :=
  Iff.rfl

def sd (M : Matrix (Fin n) (Fin n) A) : A := ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)

theorem entN_mul_super {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) {i : ℕ} (hi : i + 1 < n) :
    entN (M * N) i (i + 1) = entN M i (i + 1) + entN N i (i + 1) := by
  have h0 : i < n := by omega
  simp only [entN, dif_pos (And.intro h0 hi)]
  rw [Matrix.mul_apply, Fintype.sum_eq_add (⟨i, h0⟩ : Fin n) ⟨i + 1, hi⟩]
  · rw [(hM _ _).2 rfl, (hN _ _).2 rfl, one_mul, mul_one, add_comm]
  · simp [Fin.ext_iff]
  · rintro c ⟨h1, h2⟩
    have h1' : c.val ≠ i := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ i + 1 := fun h => h2 (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne h1' with h | h
    · rw [(hM ⟨i, h0⟩ c).1 (by change c.val < i; omega), zero_mul]
    · rw [(hN c ⟨i + 1, hi⟩).1 (by change i + 1 < c.val; omega), mul_zero]

theorem sd_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : sd (M * N) = sd M + sd N := by
  unfold sd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => entN_mul_super hM hN ?_
  have := Finset.mem_range.1 hi; omega

theorem sd_one : sd (1 : Matrix (Fin n) (Fin n) A) = 0 := by
  unfold sd
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold entN
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by simpa using congrArg Fin.val e)
  · rfl

variable (D : D7)

def whitP : Subgroup (G0g D.nd) := Subgroup.pi Set.univ fun _ => uniUpGL

theorem mem_whitP (g : G0g D.nd) :
    g ∈ whitP D ↔ ∀ kv, IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [whitP, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_uniUpGL]

def whitChar (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) : whitP D →* ℂ where
  toFun g := ∏ kv, ψ kv (sd ((g : G0g D.nd) kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))
  map_one' := by
    refine Finset.prod_eq_one fun kv _ => ?_
    simp [sd_one]
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← AddChar.map_add_eq_mul, ← sd_mul ((mem_whitP D _).1 g.2 kv) ((mem_whitP D _).1 h.2 kv)]
    rfl

def halfH (k : Fin 2) : Subgroup (G0g D.nd) := Subgroup.pi {kv | kv.1 ≠ k} fun _ => uniUpGL

theorem isHalf_halfH (k : Fin 2) : IsHalf D k (halfH D k) := by
  intro g
  rw [halfH, Subgroup.mem_pi]
  simp only [Set.mem_setOf_eq, mem_uniUpGL]

theorem isWhit_whitP (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (hψ : ∀ kv, ψ kv ≠ 1) :
    IsWhit D (whitP D) (whitChar D ψ).toHomUnits ψ :=
  ⟨hψ, mem_whitP D, fun _ => rfl⟩

theorem exists_whit_half : ∀ (D : D7) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ),
    (∀ kv, ψ kv ≠ 1) → (∃ (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ), IsWhit D P lam ψ) ∧ ∀ k, ∃ H, IsHalf D k H :=
  fun D ψ hψ => ⟨⟨whitP D, _, isWhit_whitP D ψ hψ⟩, fun k => ⟨halfH D k, isHalf_halfH D k⟩⟩

end GlobalTheory.BadCount.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
section
open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_baseChange : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L]
    [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f →
    ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) →
      finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧
        (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  intro K L V W ι _ _ _ _ _ _ _ _ _ _ _ f hf a a' ha
  refine ⟨GlobalTheory.finrank_iInf_ker_of_isBaseChange K L V W ι f a a' hf ha, ?_⟩
  rw [GlobalTheory.GaloisDescent.span_image_iInf hf]
  exact iInf_congr fun i =>
    (GlobalTheory.GaloisDescent.span_image_ker hf hf (a i) (a' i) (fun v => ha i v)).symm

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankCharacterSpaceBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
open scoped TensorProduct

namespace GlobalTheory.BadCount

theorem tmul_one_mem_nonZeroDivisors_of_field {K L R : Type} [Field K] [Field L] [Algebra K L]
    [CommRing R] [Algebra K R] (d : R) (hd : d ∈ nonZeroDivisors R) :
    ((1 : L) ⊗ₜ[K] d) ∈ nonZeroDivisors (L ⊗[K] R) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hinj : Function.Injective ((LinearMap.mulRight K d).lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b hab => by
      have : (a - b) * d = 0 := by simpa [sub_mul, sub_eq_zero] using hab
      exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hd) _ this))
  have heq : ∀ y : L ⊗[K] R, (LinearMap.mulRight K d).lTensor L y = y * ((1 : L) ⊗ₜ[K] d) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => simp [map_add (f := _), add_mul, ha, hb]
  apply hinj
  rw [heq, hx, map_zero]

theorem finrank_le_card_mul_finrank_eig_baseChange : ∀ (K L Γ R W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V : Submodule K R) [FiniteDimensional K V] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ Vm, x * act h u ∈ V) → ∀ [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ lam : H →* Lˣ, finrank K Vm ≤ Nat.card H * finrank L (eig ρ' H lam) := by
  intro K L Γ R W _ _ _ _ _ _ _ act H _ _ u hdet Vm V _ ρ hρ hVm _ _ _ _ f hf ρ' hρ' lam
  classical
  let actL : Γ → (L ⊗[K] R →ₐ[L] L ⊗[K] R) := fun g => Algebra.TensorProduct.map (AlgHom.id L L) (act g)
  have actL_tmul : ∀ g (l : L) (r : R), actL g (l ⊗ₜ r) = l ⊗ₜ act g r := fun g l r => by
    simp [actL, Algebra.TensorProduct.map_tmul]
  have actL_mul : ∀ g g' x, actL (g * g') x = actL g (actL g' x) := by
    intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_mul, AlgHom.mul_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have actL_one : ∀ x, actL 1 x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_one, AlgHom.one_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have inj_of : ∀ {M : Type} [AddCommGroup M] [Module K M] (g : M →ₗ[K] R), Function.Injective g →
      Function.Injective (g.baseChange L) := by
    intro M _ _ g hg
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap g hg
  let ιV : L ⊗[K] V →ₗ[L] L ⊗[K] R := V.subtype.baseChange L
  let ιm : L ⊗[K] Vm →ₗ[L] L ⊗[K] R := Vm.subtype.baseChange L
  let A : H → (Vm →ₗ[K] V) := fun h =>
    { toFun := fun x => ⟨(x : R) * act h u, hVm h x x.2⟩
      map_add' := by intro x y; ext; simp [add_mul]
      map_smul' := by intro c x; ext; simp [smul_mul_assoc] }
  have hA : ∀ h y, ιV ((A h).baseChange L y) = ιm y * ((1 : L) ⊗ₜ act h u) := by
    intro h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l x => simp [ιV, ιm, A, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  let e := hf.equiv
  let j : W →ₗ[L] L ⊗[K] R := ιV ∘ₗ e.symm.toLinearMap
  have hj : ∀ (g : Γ) w, j (ρ' g w) = actL g (j w) := by
    intro g w
    obtain ⟨z, rfl⟩ := e.surjective w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l v =>
      have h1 : e (l ⊗ₜ v) = l • f v := hf.equiv_tmul l v
      have h2 : e (l ⊗ₜ ρ g v) = l • f (ρ g v) := hf.equiv_tmul l _
      simp only [j, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, map_smul, hρ', ← h2, ← h1, e.symm_apply_apply, e.symm_apply_apply]
      simp [ιV, actL_tmul, hρ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hje : ∀ z, j (e z) = ιV z := fun z => by simp [j]
  let T : W →ₗ[L] W := ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • ρ' g
  have hT : ∀ w, T w ∈ eig ρ' H lam := by
    intro w
    rw [mem_eig]
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ (fun g => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul ρ', Module.End.mul_apply, smul_smul, map_mul lam]
    congr 1
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have hjT : ∀ w, j (T w) = ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (j w) := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hj]
  let Ψ : L ⊗[K] Vm →ₗ[L] (H → eig ρ' H lam) :=
    LinearMap.pi fun h => LinearMap.codRestrict (eig ρ' H lam) (T ∘ₗ e.toLinearMap ∘ₗ (A h).baseChange L)
      (fun y => hT _)
  have hΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have P : ∀ h : H, ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (ιm y * ((1 : L) ⊗ₜ act h u)) = 0 := by
      intro h
      have h0 := congrArg Subtype.val (congrFun hy h)
      simp only [Ψ, LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Pi.zero_apply, ZeroMemClass.coe_zero] at h0
      have h1 := congrArg j h0
      rw [hjT, hje, hA, map_zero] at h1
      exact h1
    have key := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H L (L ⊗[K] R)
      (fun h => actL ((h : Γ)⁻¹)) (fun x => by simp [actL_one])
      (fun h h' x => by simp [mul_inv_rev, actL_mul]) lam⁻¹ ((1 : L) ⊗ₜ u) ?_
    · have hy0 : ιm y = 0 := by
        refine key.2.1 (ιm y) (fun h' => ?_)
        rw [← P h'⁻¹]
        refine Fintype.sum_equiv (Equiv.inv H) _ _ (fun g => ?_)
        simp [actL_tmul]
      exact inj_of _ Vm.injective_subtype (by rw [hy0, map_zero])
    · have hM : (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)) =
          (Algebra.TensorProduct.includeRight : R →ₐ[K] L ⊗[K] R).mapMatrix
            ((Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u)).submatrix (Equiv.inv H) (Equiv.inv H)) := by
        ext h g
        simp [actL_tmul, mul_inv_rev, Function.swap]
      show (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)).det ∈ _
      rw [hM, ← AlgHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose,
        Algebra.TensorProduct.includeRight_apply]
      exact tmul_one_mem_nonZeroDivisors_of_field _ hdet
  have hfinW : Module.Finite L W := Module.Finite.equiv e
  have h1 : finrank K Vm = finrank L (L ⊗[K] Vm) := (Module.finrank_baseChange).symm
  rw [h1]
  refine (LinearMap.finrank_le_finrank_of_injective hΨ).trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
end

