module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierPreservesTestAdditive
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  haveI : Module.Finite A.K A.L := Module.Finite.equiv A.push.symm.out.equiv
  exact Module.Finite.trans A.K A.L

theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, mul_comm, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]

def beta (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  LinearMap.mk₂ F (fun y' y => Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)))
    (by intro a b c; simp only [star_add, add_mul, map_add (f := _), mul_add])
    (by intro c a b
        rw [star_smul_F, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])
    (by intro a b c; simp only [mul_add, map_add (f := _)])
    (by intro c a b
        rw [mul_smul_comm, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])

theorem beta_apply (A : Et F E) (x : A.K) (y' y : A.L) :
    beta A x y' y = Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)) := rfl

theorem algMap_inj (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    Function.Injective (algebraMap A.K A.L) := by
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro k hk
  by_contra hne
  obtain ⟨k', hk'⟩ := hK.mul_inv_cancel hne
  have h : algebraMap A.K A.L (k * k') = 0 := by rw [map_mul, hk, zero_mul]
  rw [hk', map_one] at h
  exact one_ne_zero h

theorem beta_symm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    ∀ a b, beta A x a b = beta A x b a := by
  intro a b
  rw [beta_apply, beta_apply]
  congr 2
  apply algMap_inj A hK hL
  rw [(_root_.GlobalTheory.JR.EtFacts.main F E A).2.1, (_root_.GlobalTheory.JR.EtFacts.main F E A).2.1, star_mul, star_mul, star_star, star_star]
  ring

theorem trace_algMap [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (c : A.K) :
    Algebra.trace A.K A.L (algebraMap A.K A.L c) = 2 * c := by
  apply algMap_inj A hK hL
  rw [(_root_.GlobalTheory.JR.EtFacts.main F E A).2.1, A.star_K, map_mul, map_ofNat]
  ring

theorem beta_sepLeft [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).SeparatingLeft := by
  haveI : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  intro a ha
  by_contra hne
  have hsa : star a ≠ 0 := by
    intro h; apply hne; simpa using congrArg star h
  obtain ⟨u, hu⟩ := hL.mul_inv_cancel hsa
  have h2 : (2 : A.K) ≠ 0 := by
    have : (2 : A.K) = algebraMap F A.K 2 := by rw [map_ofNat]
    rw [this]
    intro h
    exact two_ne_zero ((injective_iff_map_eq_zero (algebraMap F A.K)).1 (algebraMap F A.K).injective _ h)
  obtain ⟨t, ht⟩ := hK.mul_inv_cancel h2
  have htr : ∀ k : A.K, Algebra.trace F A.K k = 0 := by
    intro k
    have := ha (u * algebraMap A.K A.L (((x⁻¹ : A.Kˣ) : A.K) * t * k))
    rw [beta_apply, ← mul_assoc, hu, one_mul, trace_algMap A hK hL] at this
    have e : (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k)) = k := by
      calc (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k))
          = ((x : A.K) * ((x⁻¹ : A.Kˣ) : A.K)) * (2 * t) * k := by ring
        _ = k := by rw [Units.mul_inv, ht, one_mul, one_mul]
    rwa [e] at this
  have h1 : (1 : A.K) = 0 :=
    (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.1.1 1 (fun n => by rw [Algebra.traceForm_apply, one_mul]; exact htr n)
  exact one_ne_zero h1

theorem beta_isSymm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    (beta A x).IsSymm := LinearMap.BilinForm.isSymm_def.2 (beta_symm A hK hL x)

theorem beta_nondeg [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).Nondegenerate :=
  ((beta_isSymm A hK hL x).isRefl.nondegenerate_iff_separatingLeft).2 (beta_sepLeft A hK hL x)

theorem cont_psi {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have h : (fun b => ψ b) =ᶠ[𝓝 a] fun _ => ψ a := by
    filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
    have h1 : ψ (b - a) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact le_of_lt hb)
    calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
      _ = ψ a * ψ (b - a) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ a := by rw [h1, mul_one]
  exact continuousAt_const.congr h.symm

end GlobalTheory.JR.WeilQuad.FourierTest


open GlobalTheory.JR.WeilQuad.FourierTest in
theorem GlobalTheory.JR.WeilQuad.fOp_isTest_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧
      ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  have hker : A.kerL ψ (x : A.K) = fun a b => ψ (beta A x a b) := rfl
  have hint : ∀ f : A.L → ℂ, IsTest f → ∀ y, Integrable (fun y' => f y' * A.kerL ψ (x : A.K) y' y) μ := by
    intro f hf y
    rw [hker]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hf.2.mul_right)
    exact hf.1.continuous.mul
      ((cont_psi hψ).comp (IsModuleTopology.continuous_of_linearMap ((beta A x).flip y)))
  refine ⟨?_, fun φ' hφ' => ?_⟩
  · have := (GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.L (beta A x)
      (beta_isSymm A hK hL x) (beta_nondeg A hK hL x)).2 μ hsd.1 φ hφ
    unfold fOp
    rw [hker]
    exact this
  · funext y
    simp only [fOp, fourB, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGeneratesUnramifiedExtResidueField
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem residue_generates : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A → (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 → Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree → ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z := by
  intro K K' d φ hU B ψ hψ hnt hO s Q hQm hQg hQr y
  set Ψ : K'.O →+* B.A := ψ.comp (algebraMap K'.O K'.E) with hΨdef
  have hΨφ : ∀ a : K.O, Ψ (intMap hU a) = algebraMap K.O B.A a := by
    intro a
    simp only [Ψ, RingHom.comp_apply, intMap_spec, hψ]
    exact (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hcomp : (algebraMap K'.O K'.E).comp (intMap hU) = φ.comp (algebraMap K.O K.E) := by
    ext a; simp [intMap_spec]
  obtain ⟨f, hf⟩ : ∃ f : K.O[X], aeval B.g f = ψ (algebraMap K'.O K'.E y) := by
    have := hO y
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  refine ⟨f, y - f.eval₂ (intMap hU) s, ?_, ?_⟩
  swap
  · rw [map_sub, Polynomial.hom_eval₂, hcomp]; ring

  by_contra hz
  have hzu : IsUnit (y - f.eval₂ (intMap hU) s) := by
    by_contra h; exact hz ((IsLocalRing.mem_maximalIdeal _).2 h)
  set z := y - f.eval₂ (intMap hU) s with hzdef
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hRdef
  haveI := hnt

  have hΨz : Ψ z = aeval B.g f - aeval (Ψ s) f := by
    rw [hzdef, map_sub, hf, Polynomial.hom_eval₂]
    have : Ψ.comp (intMap hU) = algebraMap K.O B.A := by ext a; exact hΨφ a
    rw [this]; rfl
  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let x' : R := ⟨Ψ s, hO s⟩
  obtain ⟨h, hh⟩ := Polynomial.sub_dvd_eval_sub g' x' (f.map (algebraMap K.O R))
  have hh' : Ψ z = (B.g - Ψ s) * (h : B.A) := by
    rw [hΨz]
    have := congrArg Subtype.val hh
    simp only [Polynomial.eval_map_algebraMap, Subalgebra.coe_sub, Subalgebra.coe_mul,
      Polynomial.aeval_subalgebra_coe] at this
    exact this

  obtain ⟨zu, hzu'⟩ := hzu
  let zi : R := ⟨Ψ ((zu⁻¹ : K'.Oˣ) : K'.O), hO _⟩
  have hunit : (g' - x') * (h * zi) = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, g', x', zi]
    rw [← mul_assoc, ← hh', ← hzu', ← map_mul, Units.mul_inv, map_one]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hmax : IsLocalRing.maximalIdeal K'.O = Ideal.span {intMap hU ϖ} := by
    rw [← map_maximalIdeal hU, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.map_span, Set.image_singleton]
  have hdvd : C (intMap hU ϖ) ∣ Q - (X - C s) ^ Q.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [← Ideal.mem_span_singleton, ← hmax, ← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map,
      Polynomial.map_sub, hQr]
    simp
  obtain ⟨R', hR'⟩ := hdvd
  have hev := congrArg (Polynomial.eval₂ Ψ B.g) hR'
  rw [Polynomial.eval₂_sub, hQg, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, hΨφ] at hev
  have hRmem : ∀ P : K'.O[X], P.eval₂ Ψ B.g ∈ R := by
    intro P
    rw [Polynomial.eval₂_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ =>
      Subalgebra.mul_mem _ (hO _) (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O B.g) _)
  let r : R := ⟨R'.eval₂ Ψ B.g, hRmem R'⟩
  have hpow : (g' - x') ^ Q.natDegree = -(algebraMap K.O R ϖ * r) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_sub, Subalgebra.coe_neg, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap, g', x', r]
    rw [← hev]; ring
  set u := h * zi
  have hinv : algebraMap K.O R ϖ * (-(r * u ^ Q.natDegree)) = 1 := by
    have : ((g' - x') * u) ^ Q.natDegree = 1 := by rw [hunit, one_pow]
    rw [mul_pow, hpow] at this
    rw [← this]; ring

  letI : Algebra K'.O B.A := Ψ.toAlgebra
  have hgint : IsIntegral K'.O B.g := ⟨Q, hQm, hQg⟩
  have hRint : ∀ w ∈ R, IsIntegral K'.O w := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hgint
    | algebraMap a =>
      rw [← hΨφ a]; exact isIntegral_algebraMap (R := K'.O) (x := intMap hU a)
    | add x y _ _ hx hy => exact hx.add hy
    | mul x y _ _ hx hy => exact hx.mul hy
  set v : R := -(r * u ^ Q.natDegree)
  have hvint : IsIntegral K'.O (v : B.A) := hRint _ v.2
  have hv1 : Ψ (intMap hU ϖ) * (v : B.A) = 1 := by
    have := congrArg Subtype.val hinv
    simpa [hΨφ] using this
  have hϖ0 : intMap hU ϖ ≠ 0 := fun h0 => hϖ.ne_zero ((intMap_injective hU) (by rw [h0, map_zero]))
  have hπ0 : algebraMap K'.O K'.E (intMap hU ϖ) ≠ 0 := by
    intro h0; exact hϖ0 (IsFractionRing.injective K'.O K'.E (by rw [h0, map_zero]))
  set t : K'.E := (algebraMap K'.O K'.E (intMap hU ϖ))⁻¹
  have hψt : ψ t = v := by
    have h1 : Ψ (intMap hU ϖ) * ψ t = 1 := by
      rw [hΨdef, RingHom.comp_apply, ← map_mul, mul_inv_cancel₀ hπ0, map_one]
    calc ψ t = ((v : B.A) * Ψ (intMap hU ϖ)) * ψ t := by rw [mul_comm (v : B.A), hv1, one_mul]
      _ = v := by rw [mul_assoc, h1, mul_one]
  let ψA : K'.E →ₐ[K'.O] B.A := { toRingHom := ψ, commutes' := fun _ => rfl }
  have htint : IsIntegral K'.O t := by
    rw [← isIntegral_algHom_iff ψA ψ.injective]
    show IsIntegral K'.O (ψ t)
    rw [hψt]; exact hvint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 htint
  have hb1 : intMap hU ϖ * b = 1 := by
    apply IsFractionRing.injective K'.O K'.E
    rw [map_mul, hb, mul_inv_cancel₀ hπ0, map_one]
  have hmem : intMap hU ϖ ∈ IsLocalRing.maximalIdeal K'.O := by
    rw [hmax]; exact Ideal.subset_span rfl
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem ⟨⟨_, b, hb1, by rw [mul_comm]; exact hb1⟩, rfl⟩

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledIntegersKAnnihilatorSmallNearZero
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.annihilator_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  intro F E _ _ _ _ hU A ψ hψ U hUmem
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  have hfacts := _root_.GlobalTheory.JR.EtFacts.main F E A
  have hnd : (Algebra.traceForm F A.K).Nondegenerate := hfacts.2.2.1
  have hOKopen : IsOpen A.OK := hfacts.2.2.2.2.2.2.2.2.2.1
  obtain ⟨R, hR⟩ := hfacts.2.2.2.2.2.2.2.2.2.2.2
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K)
    (Algebra.traceForm_isSymm F (S := A.K)) hnd
  obtain ⟨M, N, hMU, -, -, -, hNc, -, hM⟩ := hsmall U hUmem
  have hev : ∀ᶠ c in 𝓝 (0 : F), ∀ y ∈ (N : Set A.K), c • y ∈ A.OK := by
    refine hNc.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : ContinuousAt (fun p : F × A.K => p.1 • p.2) ((0 : F), y) := continuous_smul.continuousAt
    have : A.OK ∈ 𝓝 ((fun p : F × A.K => p.1 • p.2) ((0 : F), y)) := by
      simpa using hOKopen.mem_nhds h0
    exact hc this
  filter_upwards [nhdsWithin_le_nhds hev] with c hc b hb
  apply hMU
  rw [SetLike.mem_coe, hM]
  intro y hy
  have := hb y (hc y hy)
  simpa [Et.psiK, Algebra.traceForm_apply, mul_comm] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherel
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SelfDualLat

theorem isLC_indicator_one {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClopen s) :
    IsLocallyConstant (s.indicator (fun _ => (1 : ℂ))) := by
  classical
  intro B
  rw [Set.indicator_preimage, Set.ite]
  refine (IsOpen.inter ?_ h.isOpen).union ?_
  · rw [Set.preimage_const]; split_ifs <;> simp
  · rw [Set.diff_eq]
    refine IsOpen.inter ?_ h.isClosed.isOpen_compl
    change IsOpen ((fun _ : X => (0:ℂ)) ⁻¹' B)
    rw [Set.preimage_const]; split_ifs <;> simp

theorem topo : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V], LocallyCompactSpace V ∧ SecondCountableTopology V ∧ T2Space V ∧ IsTopologicalAddGroup V := by
  intro F E _ _ _ _ _ V _ _ _ _ _
  haveI := (inferInstance : Unram F E).lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousNeg V := ⟨by
    have := IsModuleTopology.continuous_of_linearMap (R := F) (A := V) (B := V) (-LinearMap.id)
    exact this⟩
  let e : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) := ⟨e.toEquiv, hc, hc'⟩
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space,
    IsTopologicalAddGroup.mk⟩
theorem orth : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V) (μ : Measure V), μ.IsAddHaarMeasure → ∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ β μ hμ M hMo hMc y
  classical
  by_cases hy : y ∈ {y | ∀ x ∈ M, ψ (β x y) = 1}
  · rw [Set.indicator_of_mem hy, setIntegral_congr_fun hMo.measurableSet (fun x hx => hy x hx)]
    simp [Measure.real]
  · rw [Set.indicator_of_notMem hy]
    simp only [Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    have ht := integral_add_left_eq_self (μ := μ) (fun x => (M : Set V).indicator (fun x => ψ (β x y)) x) x0
    have hpt : ∀ x, (M : Set V).indicator (fun x => ψ (β x y)) (x0 + x) =
        ψ (β x0 y) * (M : Set V).indicator (fun x => ψ (β x y)) x := by
      intro x
      by_cases hx : x ∈ M
      · have : x0 + x ∈ M := M.add_mem hx0 hx
        simp [Set.indicator_of_mem (show x0 + x ∈ (M : Set V) from this),
          Set.indicator_of_mem (show x ∈ (M : Set V) from hx), map_add, AddChar.map_add_eq_mul]
      · have : x0 + x ∉ M := fun h => hx (by simpa using M.sub_mem h hx0)
        simp [Set.indicator_of_notMem (show x0 + x ∉ (M : Set V) from this),
          Set.indicator_of_notMem (show x ∉ (M : Set V) from hx)]
    simp_rw [hpt] at ht
    rw [integral_const_mul, integral_indicator hMo.measurableSet] at ht
    have h0 : (ψ (β x0 y) - 1) * ∫ x in (M : Set V), ψ (β x y) ∂μ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
theorem planch : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ _ _ _ β hβs hβn μ hsd f hf
  haveI := hsd.1
  have hψ' := (_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ
  have hI := _root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ V β hβs hβn
  set B : V → V → ℂ := fun x y => ψ (β x y) with hB
  set g := fourB μ B f with hgdef
  have hg : IsTest g := hI.2 μ hsd.1 f hf
  have hψc : Continuous (fun t : F => ψ t) := hψ'.1.continuous
  have hβc : Continuous (fun p : V × V => β p.1 p.2) := IsModuleTopology.continuous_bilinear_of_finite_left β
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hf.2
  have hgi : Integrable g μ := hgc.integrable_of_hasCompactSupport hg.2
  have key : ∀ h : V → ℂ, ((∫ y, ‖h y‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ y, h y * (starRingEnd ℂ) (h y) ∂μ := by
    intro h
    rw [← integral_complex_ofReal]
    congr 1; ext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hconj : ∀ t : F, (starRingEnd ℂ) (ψ t) = ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv]
    have h1 : ‖ψ t‖ = 1 := hψ'.2.1 t
    have h0 : ψ t ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
  have hinner : ∀ x, ∫ y, ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ = (starRingEnd ℂ) (f x) := by
    intro x
    have := hsd.2 f hf (-x)
    rw [neg_neg] at this
    rw [← this]
    show _ = (starRingEnd ℂ) (∫ y, g y * B y (-x) ∂μ)
    rw [← integral_conj]
    congr 1; ext y
    rw [map_mul, hconj]
    simp only [map_neg, neg_neg, hβs.eq x y]
    ring
  have hint : Integrable (Function.uncurry fun y x => f x * ψ (β x y) * (starRingEnd ℂ) (g y)) (μ.prod μ) := by
    refine Integrable.mono' ((hgi.norm).mul_prod hfi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hfc.comp continuous_snd).mul (hψc.comp (hβc.comp continuous_swap))).mul
        (Complex.continuous_conj.comp (hgc.comp continuous_fst))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, Complex.norm_conj]
      rw [mul_comm]
  apply Complex.ofReal_injective
  rw [key, key]
  calc ∫ y, g y * (starRingEnd ℂ) (g y) ∂μ
      = ∫ y, ∫ x, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := by
        congr 1; ext y
        rw [hgdef]; unfold fourB
        rw [← integral_mul_const]
    _ = ∫ x, ∫ y, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ := by
        congr 1; ext x
        simp_rw [mul_assoc]
        rw [integral_const_mul, hinner]

end GlobalTheory.JR.SelfDualLat

open GlobalTheory.JR.SelfDualLat in
theorem GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ β hβs hβn μ hμ
  obtain ⟨hLC, hSC, hT2, hTG⟩ := topo F E V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hI := _root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ V β hβs hβn
  have fwd : ∀ ν : Measure V, SelfDual ν (fun x y => ψ (β x y)) → ∀ M : AddSubgroup V, IsOpen (M : Set V) →
      IsCompact (M : Set V) → ν M * ν {y | ∀ x ∈ M, ψ (β x y) = 1} = 1 := by
    intro ν hν M hMo hMc
    haveI := hν.1
    set P : Set V := {y | ∀ x ∈ M, ψ (β x y) = 1} with hP
    set g : V → ℂ := (M : Set V).indicator (fun _ => 1) with hg
    have hMcl : IsClosed (M : Set V) := AddSubgroup.isClosed_of_isOpen M hMo
    have hgt : IsTest g := ⟨isLC_indicator_one _ ⟨hMcl, hMo⟩,
      HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)⟩
    have h1 : ∀ x, fourB ν (fun x y => ψ (β x y)) g x = P.indicator (fun _ => ((ν M).toReal : ℂ)) x := by
      intro x
      rw [← orth F E ψ hψ V β ν hν.1 M hMo hMc x]
      unfold fourB
      rw [← integral_indicator hMo.measurableSet]
      congr 1; ext t
      by_cases ht : t ∈ (M : Set V) <;> simp [hg, ht]
    have hc : ((ν M).toReal : ℂ) ≠ 0 := by
      have h0 : ν M ≠ 0 := (hMo.measure_pos ν ⟨0, M.zero_mem⟩).ne'
      have ht : ν M ≠ ⊤ := hMc.measure_lt_top.ne
      exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
    have hft := hI.2 ν hν.1 g hgt
    have hPm : MeasurableSet P := by
      have : P = (fourB ν (fun x y => ψ (β x y)) g) ⁻¹' {((ν M).toReal : ℂ)} := by
        ext y
        show y ∈ P ↔ fourB ν (fun x y => ψ (β x y)) g y = ((ν M).toReal : ℂ)
        rw [h1]
        by_cases hy : y ∈ P
        · simp [Set.indicator_of_mem hy, hy]
        · rw [Set.indicator_of_notMem hy]; exact ⟨fun h => absurd h hy, fun h => absurd h.symm hc⟩
      rw [this]; exact (hft.1.isOpen_fiber _).measurableSet
    have h2 := hν.2 g hgt 0
    rw [neg_zero, show g 0 = 1 by simp [hg, M.zero_mem]] at h2
    have h3 : fourB ν (fun x y => ψ (β x y)) (fourB ν (fun x y => ψ (β x y)) g) 0 =
        (ν P).toReal * (ν M).toReal := by
      show ∫ x, fourB ν (fun x y => ψ (β x y)) g x * ψ (β x 0) ∂ν = _
      simp_rw [h1, map_zero, AddChar.map_zero_eq_one, mul_one]
      rw [integral_indicator_const _ hPm]
      simp [Measure.real]
    rw [h3] at h2
    rw [← ENNReal.toReal_eq_one_iff, ENNReal.toReal_mul]
    have h4 : (((ν M).toReal * (ν P).toReal : ℝ) : ℂ) = 1 := by push_cast; linear_combination h2
    exact_mod_cast h4
  refine ⟨fun M hMo hMc => ⟨⟨fun hsd => fwd μ hsd M hMo hMc, fun h => ?_⟩, orth F E ψ hψ V β μ hμ M hMo hMc⟩,
    fun hsd f hf => planch F E ψ hψ V β hβs hβn μ hsd f hf⟩
  obtain ⟨⟨μ0, hμ0, -⟩, -⟩ := hI
  haveI := hμ0.1
  have hsc : μ = Measure.addHaarScalarFactor μ μ0 • μ0 := Measure.isAddLeftInvariant_eq_smul μ μ0
  set c := Measure.addHaarScalarFactor μ μ0 with hcdef
  have h0 := fwd μ0 hμ0 M hMo hMc
  rw [hsc] at h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcc : ((c * c : NNReal) : ENNReal) = 1 := by
    calc ((c * c : NNReal) : ENNReal) = (c : ENNReal) * c * (μ0 M * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by
          rw [h0, mul_one, ENNReal.coe_mul]
      _ = (c : ENNReal) * μ0 M * ((c : ENNReal) * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by ring
      _ = 1 := h
  have hcc' : (c : ℝ) * c = 1 := by exact_mod_cast (ENNReal.coe_eq_one.1 hcc)
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.2]
    exact_mod_cast this
  have : μ = μ0 := by rw [hsc, hc1, one_smul]
  rw [this]; exact hμ0
end

