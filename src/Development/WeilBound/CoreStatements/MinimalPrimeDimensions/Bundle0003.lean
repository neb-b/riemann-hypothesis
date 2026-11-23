module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ContinuousAeval
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FiniteTypeSections
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.GenericDenseBound

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem finiteType_sections {K : Type} [Field K] [NumberField K] {X : Scheme.{0}} {p : X ⟶ Sp (𝓞 K)}
    (hp : IsProjOver p) {W : X.Opens} (hW : IsAffineOpen W) : Algebra.FiniteType ℤ Γ(X, W) := by
  have : IsProper p := by
    obtain ⟨N, j, _, e⟩ := hp
    have := isProper_str (𝓞 K) N
    rw [← e]
    infer_instance
  have hft : (algX p W).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩
      (show W ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).symm.commRingCatIsoToRingEquiv.surjective)
  have h0 : (algebraMap ℤ (𝓞 K)).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h1 := hft.comp h0
  rw [Subsingleton.elim ((algX p W).comp (algebraMap ℤ (𝓞 K))) (algebraMap ℤ Γ(X, W))] at h1
  exact RingHom.finiteType_algebraMap.1 h1

theorem final_ineq {a Q t : ℝ} {τ : ℕ} (hQ : 0 ≤ Q) (h : a ≤ Real.exp (2 * (τ : ℝ) * t) * Q ^ τ) :
    a * Real.exp (-((τ : ℝ) * Real.log Q)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  rcases hQ.eq_or_lt with h0 | h0
  · subst h0
    rw [Real.log_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact h.trans (mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ le_rfl zero_le_one))
  · rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log h0, mul_inv_le_iff₀ (pow_pos h0 τ)]
    exact h

theorem norm_le_of_emb {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (β : Ω) (τ : ℕ)
    (t : ℝ)
    (hb : ∀ (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm W b g A → ∀ (σ : K →+* ℂ) (ρ : Ω →+* ℂ),
      ρ.comp (algebraMap K Ω) = σ → ‖ρ β‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (ev (b i))) ^ τ)
    (w : W) (hw : ev w ≠ 0) (σ : 𝓞 K →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U k))
    (hr : RegAt (under y) (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ)) :
    ‖ratVal (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ) y‖ ^ 2 *
      Real.exp (-((τ : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, -, hbc, hφ⟩ := hM.fs
  obtain ⟨U', hU', a, ha⟩ := hr.exists_fnOf
  have hyk : under y ∈ L.B.U k := mem_ptsIn.1 hy
  obtain ⟨O, hO, hyO, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (memInf hU' hyk)
  have hO' : IsAffineOpen O := hO
  have hle1 : O ≤ U' := hle.trans inf_le_left
  have hle2 : O ≤ L.B.U k := hle.trans inf_le_right
  have hyO' : y ∈ ptsIn p σ O := mem_ptsIn.2 hyO
  have hg : genericPoint X ∈ O := gen_mem hyO
  have : Nonempty O := ⟨⟨_, hyO⟩⟩
  have := finiteType_sections hM.arith.isProjOver hO'
  have := functionField_isFractionRing_of_isAffineOpen X O hO'
  have halg : ∀ z : Γ(X, O), algebraMap Γ(X, O) X.functionField z = fnOf O hg z := fun _ => rfl
  let r : Option (Fin n) → Γ(X, O) := fun j => j.elim (resG X hle1 a) fun j => resG X hle2 ((s (gw j)).f k)
  have hψw : ψ (ev w) ≠ 0 := (map_ne_zero ψ).2 hw
  set u := fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) with hu
  obtain ⟨σ', hσ', hineq⟩ := bound_of_emb (Ω := X.functionField) (ψ.comp (algebraMap K Ω)) (algX p O)
    (fun z => by
      rw [halg, RingHom.comp_apply, hM.base]
      exact (RingHom.congr_fun (fnOf_comp_algX p O hg) z).trans rfl)
    (evHom hyO') r (fun _ v => ‖v none‖ ^ 2)
    (fun σ' v => Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ j, (∑ m, σ' (c j m) * A σ' m a) * v (some j)‖ ^ 2) ^ τ)
    (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun ρ => by
      have h1 := hb N n b g A hF _ (ρ.comp ψ) rfl
      have e0 : (ρ.comp ψ).comp (algebraMap K Ω) = ρ.comp (ψ.comp (algebraMap K Ω)) := rfl
      rw [e0] at h1
      generalize hσ' : ρ.comp (ψ.comp (algebraMap K Ω)) = σ' at h1 ⊢
      have hσa : ∀ z, σ' z = ρ (ψ (algebraMap K Ω z)) := fun z => by rw [← hσ']; rfl
      set lam := ρ ((ψ (ev w))⁻¹ * u) with hlam
      have e1 : ρ (algebraMap Γ(X, O) X.functionField (r none)) = ρ (ψ β) * lam ^ τ := by
        rw [halg]
        show ρ (fnOf O hg (resG X hle1 a)) = _
        rw [fnOf_resG, ha, hlam, ← map_pow ρ, ← map_mul ρ, mul_pow, mul_assoc]
      have e2 : ∀ j, ρ (algebraMap Γ(X, O) X.functionField (r (some j))) = ρ (ψ (ev (gw j))) * lam := fun j => by
        rw [halg]
        show ρ (fnOf O hg (resG X hle2 ((s (gw j)).f k))) = _
        rw [fnOf_resG, hlam, ← map_mul ρ]
        congr 1
        have := hM.ratio w (gw j) k (hle2 hg)
        rw [← mul_assoc, mul_comm (ψ (ev (gw j))), mul_assoc, eq_inv_mul_iff_mul_eq₀ hψw]
        exact this
      have e3 : ∀ m, ρ (ψ (ev (b m))) = ∑ j, σ' (c j m) * ρ (ψ (ev (gw j))) := fun m => by
        rw [hbc m]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Algebra.smul_def, map_mul, hσa]
      have e4 : ∀ a, ∑ j, (∑ m, σ' (c j m) * A σ' m a) * (ρ (ψ (ev (gw j))) * lam) =
          lam * ∑ m, A σ' m a * ρ (ψ (ev (b m))) := fun a => by
        simp only [e3, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      simp only [e1, e2, e4, norm_mul, mul_pow, norm_pow, ← Finset.mul_sum]
      have hS : 0 ≤ ∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2 := by positivity
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have e5 : (Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ') (fun i => (ρ.comp ψ) (ev (b i))) ^ τ) ^ 2 =
          Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2) ^ τ := by
        rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, mul_comm τ 2, pow_mul]
        unfold GlobalTheory.Adelic.archSize
        simp only [RingHom.comp_apply]
        rw [Real.sq_sqrt hS]
        congr 2
        push_cast
        ring
      rw [e5] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (‖lam‖ ^ τ) ^ 2 by positivity)
      refine h3.trans_eq ?_
      ring)
  have hσ : σ'.comp (algebraMap (𝓞 K) K) = σ := hσ'.trans (RingHom.ext fun z =>
    (ev_eq hyO' _).symm.trans (ev_algX hyO' z))
  subst hσ
  rw [hφ σ' k y, ← ha, ratVal_fnOf (mem_ptsIn.2 hU')]
  refine final_ineq (by positivity) ?_
  have f1 : evHom hyO' (r none) = GlobalTheory.CxPts.ev p _ U' a y := (ev_eq hyO' _).symm.trans (ev_res hle1 hyO' a)
  have f2 : ∀ j, evHom hyO' (r (some j)) = valR y.1 (L.B.U k) ((s (gw j)).f k) := fun j =>
    (ev_eq hyO' _).symm.trans (ev_res hle2 hyO' _)
  simp only [f1, f2] at hineq
  exact hineq

end ChowFormHeightComparison₂.GenericDenseBound
end

-- bundled from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.LeDimQuotientHorizontal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

namespace ChowFormHeightComparison₂.CF

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem le_dim_quotient_horizontal (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1) (hinj : Function.Injective (algebraMap ℤ (A ⧸ q))) {d : ℕ}
    (hd : Algebra.trdeg ℤ A = d) : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have : FaithfulSMul ℤ (A ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.FiniteType ℤ (A ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q) (Ideal.Quotient.mkₐ_surjective ℤ q)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast ℤ (A := A ⧸ q)
  have h1 := GroundTheory.Heights₂.Heights.IntDomainDim.proof (A ⧸ q) hinj
  rw [he, Cardinal.toENat_nat] at h1
  have hB := ringKrullDim_genericFibre_eq ℤ ℚ hd
  have hB' := ringKrullDim_genericFibre_eq ℤ ℚ he
  have := IsLocalization.tensorRight (S := A) ℚ (nonZeroDivisors ℤ)
  have := IsLocalization.tensorRight (S := A ⧸ q) ℚ (nonZeroDivisors ℤ)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have hle' : Algebra.algebraMapSubmonoid (A ⧸ q) (nonZeroDivisors ℤ) ≤ nonZeroDivisors (A ⧸ q) :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hx))
  have : IsDomain (ℚ ⊗[ℤ] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : IsDomain (ℚ ⊗[ℤ] (A ⧸ q)) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle'
  let φ : ℚ ⊗[ℤ] A →ₐ[ℚ] ℚ ⊗[ℤ] (A ⧸ q) := Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Ideal.Quotient.mkₐ ℤ q)
  have hφ : Function.Surjective φ := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨a ⊗ₜ b, rfl⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
  have : (RingHom.ker φ).IsPrime := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact RingHom.ker_isPrime _
  have hc : (RingHom.ker φ).comap (algebraMap A (ℚ ⊗[ℤ] A)) = q := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff _ (IsLocalization.injective (ℚ ⊗[ℤ] (A ⧸ q)) hle')]
    exact Iff.rfl
  have h2 := IsLocalization.height_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ)) (RingHom.ker φ)
  replace h2 : q.height = (RingHom.ker φ).height := (congrArg Ideal.height hc).symm.trans h2
  have h3 := height_add_ringKrullDim_quotient_of_finiteType ℚ (RingHom.ker φ)
  have h4 : ringKrullDim ((ℚ ⊗[ℤ] A) ⧸ RingHom.ker φ) = ringKrullDim (ℚ ⊗[ℤ] (A ⧸ q)) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ)
  rw [h4, hB, hB', ← h2] at h3
  rw [h1, ← h3, add_comm, WithBot.coe_add]
  refine add_le_add (le_of_eq (by norm_cast)) ?_
  exact_mod_cast hq

theorem le_dim_quotient (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] (hmin : ∀ f ∈ q, f ≠ 0 → q ∈ (Ideal.span {f}).minimalPrimes) {d : ℕ}
    (hd : Algebra.trdeg ℤ A = d) : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨l, hl⟩ := CharP.exists (A ⧸ q)
  rcases CharP.char_is_prime_or_zero (A ⧸ q) l with h | rfl
  · have : Fact l.Prime := ⟨h⟩
    have hlq : (l : A) ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero _ l
    exact (GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q
      (hmin _ hlq (Nat.cast_ne_zero.2 h.ne_zero)) d hd).ge
  · have : CharZero (A ⧸ q) := CharP.charP_to_charZero _
    refine le_dim_quotient_horizontal A q ?_ (algebraMap ℤ (A ⧸ q)).injective_int hd
    by_cases h0 : q = ⊥
    · subst h0
      rw [Ideal.height_bot]
      exact zero_le_one
    · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ (hmin f hf hf0)

theorem stDim : StDim := by
  intro k _ X p D hX Z i _ _ hcoh
  have := hX.isIntegral
  generalize hiz : i (genericPoint Z) = z at hcoh
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hrange : Set.range i = closure {z} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hiz] at h₁
    exact h₁.def.symm
  rw [← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  have hgen : genericPoint X ∉ closure ({z} : Set X) := by
    intro h
    have e : z = genericPoint X :=
      ((genericPoint_specializes z).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hcoh
    exact zero_ne_one hcoh
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (D + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX.dim_eq
  have hup : topologicalKrullDim (closure ({z} : Set X)) + 1 ≤ (D + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x hx => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩
  obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  have : LocallyOfFiniteType t := inferInstance
  have : Flat t := hX.flat
  obtain ⟨A, _, _, instA, _, _, j, _, ⟨a, ha⟩, hjt, hA⟩ := exists_affine_chart_trdeg_eq t z
  obtain rfl : instA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  have : CharZero A := ⟨fun m n h => Nat.cast_injective (R := ℤ) (FaithfulSMul.algebraMap_injective ℤ A (by simpa using h))⟩
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  have hdimX : topologicalKrullDim X ≤ (d + 1 : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_
    have hdB : Algebra.trdeg ℤ B = d := hB.trans (hA.symm.trans hd)
    have hZ1 : ringKrullDim ℤ ≤ 1 := by
      exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
    refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
    rw [ringKrullDim_genericFibre_eq ℤ ℚ hdB]
    refine (add_le_add hZ1 (le_refl ((d : ℕ) : WithBot ℕ∞))).trans_eq ?_
    push_cast
    exact add_comm _ _
  have hDd : D ≤ d := by
    have := hX.dim_eq.symm.trans_le hdimX
    have : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := this
    exact Nat.le_of_succ_le_succ (by exact_mod_cast this)
  have : a.asIdeal.IsPrime := a.isPrime
  have hmin : ∀ f ∈ a.asIdeal, f ≠ 0 → a.asIdeal ∈ (Ideal.span {f}).minimalPrimes := fun f hf hf0 => by
    refine ⟨⟨a.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hf⟩, fun q' hq' hle => ?_⟩
    obtain ⟨hq'p, hlq'⟩ := hq'
    by_contra hne
    have hbot : (⊥ : Ideal A) ≠ q' := by
      intro h0
      have h1 : f ∈ q' := (Ideal.span_singleton_le_iff_mem _).1 hlq'
      rw [← h0, Ideal.mem_bot] at h1
      exact hf0 h1
    let b' : PrimeSpectrum A := ⟨q', hq'p⟩
    let g : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hsp (u v : PrimeSpectrum A) : j u ⤳ j v ↔ u.asIdeal ≤ v.asIdeal :=
      j.isOpenEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes u v).symm
    have h₁ : z < j b' := by
      rw [← ha]
      exact ⟨(hsp b' a).2 hle, fun h => hne ((hsp a b').1 h)⟩
    have h₂ : j b' < j g := ⟨(hsp g b').2 bot_le, fun h => hbot (le_bot_iff.1 ((hsp b' g).1 h)).symm⟩
    have h₃ := Order.coheight_add_one_le h₁
    have h₄ := Order.coheight_add_one_le h₂
    rw [hcoh] at h₃
    have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
    exact absurd h₅ (by decide)
  have hq := le_dim_quotient A a.asIdeal hmin hd
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({z} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  replace hlow := hq.trans hlow
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim (closure ({z} : Set X)) = e :=
    have ⟨e, he⟩ := hX.exists_dim_eq i
    ⟨e, (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange).trans he⟩
  rw [he] at hlow hup ⊢
  have h1 : d ≤ e := by exact_mod_cast hlow
  have h2 : e + 1 ≤ D + 1 := by exact_mod_cast hup
  have : e = D := by omega
  rw [this]

end ChowFormHeightComparison₂.CF
end
end

