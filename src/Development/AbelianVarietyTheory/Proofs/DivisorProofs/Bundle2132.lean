module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

theorem ahFactor_im_int_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := by
    haveI := q.isPrime
    haveI := p0.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime p0.asIdeal).symm)
  rw [this]
  exact hj

theorem ahFactor_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (v w : Fin g → ℂ) : w ⬝ᵥ Hm.mulVec (star v) = star (v ⬝ᵥ Hm.mulVec (star w)) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b, star_star]
  ring

theorem ahFactor_im_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  intro g A _ L u Hm χ hL hF l hl l' hl'
  obtain ⟨hH, hχ, hfac⟩ := hF
  obtain ⟨i, hi⟩ := ahFactor_im_int_chart L hL (u.ex 0).left
  have hex : ∀ z ∈ u.Λ, u.ex z = u.ex 0 := fun z hz => by
    rw [(u.ker z).mpr hz, (u.ker 0).mpr (zero_mem _)]
  have hc : ∀ z ∈ u.Λ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := fun z hz => by rw [hex z hz]; exact hi
  have e1 := hfac ⟨l, hl⟩ i 0 (hc 0 (zero_mem _))
  have e2 := hfac ⟨l', hl'⟩ i l (hc l hl)
  have e3 := hfac ⟨l', hl'⟩ i 0 (hc 0 (zero_mem _))
  have e4 := hfac ⟨l, hl⟩ i l' (hc l' hl')
  have hne := u.fr_ne i (l + l') (hc _ (add_mem hl hl'))
  have hχ1 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
  have hχ2 : χ ⟨l', hl'⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l', hl'⟩
  have hsw := ahFactor_herm_swap hH l l'
  simp only [zero_add, zero_dotProduct, mul_zero] at e1 e3
  rw [e2] at e1
  rw [e4, add_comm l' l] at e3
  have key := e1.symm.trans e3
  set F := u.fr i (l + l')
  set H := l ⬝ᵥ Hm.mulVec (star l')
  set H' := l' ⬝ᵥ Hm.mulVec (star l')
  set H0 := l ⬝ᵥ Hm.mulVec (star l)
  set Hs := l' ⬝ᵥ Hm.mulVec (star l)
  set c1 := χ ⟨l, hl⟩
  set c2 := χ ⟨l', hl'⟩
  have key2 : (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) =
      (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0)) := by
    simp only [Complex.exp_add] at key ⊢
    linear_combination key
  have hnz : c1 * c2 * F ≠ 0 := mul_ne_zero (mul_ne_zero hχ1 hχ2) hne
  have key3 := mul_left_cancel₀ hnz key2
  have key4 : Complex.exp ((Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) -
      (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0))) = 1 := by
    rw [Complex.exp_sub, key3, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp key4
  refine ⟨n, ?_⟩
  have hsc : H - Hs = 2 * (H.im : ℂ) * Complex.I := by
    rw [hsw]
    have h7 := Complex.sub_conj H
    push_cast at h7
    exact h7
  have h5 : ((H.im : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination hn - (Real.pi : ℂ) * hsc
  have h6 := sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right Complex.two_pi_I_ne_zero)
  exact_mod_cast h6

end GlobalTheory.TorusRM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleHermPos

open Complex Matrix
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues AnalyticHom

variable {g : ℕ}

lemma form_smul (c : ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ ((c : ℂ) • Hm).mulVec (star w) = c * (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma isHermitian_smul {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (c : ℝ) :
    ((c : ℂ) • Hm).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]

lemma theta_add_smul_eq (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    {v : Fin g → ℂ} (hv : Hm.mulVec (star v) = 0) (z : Fin g → ℂ) (t : ℂ) :
    θ (z + t • v) = θ z := by
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
  have hq : ∀ t : ℂ, ((z + t • v) ⬝ᵥ Hm.mulVec (star (z + t • v))) = z ⬝ᵥ Hm.mulVec (star z) := by
    intro t
    have h1 : Hm.mulVec (star (t • v)) = 0 := by rw [star_smul, mulVec_smul, hv, smul_zero]
    have h2 : v ⬝ᵥ Hm.mulVec (star z) = 0 := by
      rw [ThetaPositivity.form_conj hH z v, hv, dotProduct_zero, star_zero]
    rw [star_add, mulVec_add, h1, add_zero, add_dotProduct, smul_dotProduct, h2, smul_zero, add_zero]
  have hd : Differentiable ℂ fun t : ℂ => θ (z + t • v) :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const v))
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => θ (z + t • v)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have := hC (z + t • v)
    rwa [hq t] at this
  have := hd.apply_eq_apply_of_bounded hb t 0
  simpa using this

lemma eq_zero_of_smul_mem (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] {v : Fin g → ℂ}
    (h : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • v, h t⟩ : Λ) :=
    (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

theorem re_form_pos_of_relAmple :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    Out.RelAmple A L → ∀ (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
      (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
        u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro A _ _ hA L hL ha g u Hm χ hH hχ hfr
  haveI : Smooth A.hom := hA.smooth
  haveI := isReduced_of_smooth_complex _ A.hom inferInstance
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  obtain ⟨N, hN, M, s, hcov, hD⟩ := ha ⊤ (isAffineOpen_top _)
  choose hDa r hr hsurj using hD
  have hrg : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    trivial
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, σ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrg⟩
  choose s' hs' using fun i => exists_sec_pow L _ σ hσ N A.hom (s i)
  choose θ hθd hθfn _hθu hθper using fun i => ThetaBundleSec.exists_fn u hL N (s' i)
  choose ch hch using fun z => PullHermitian.exists_chart (u.ex z).left hL
  have hU : ∀ z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ (Out.powOver A L ⊤ N).U (fun _ => ch z) := fun z =>
    le_preimage_mono (u.ex z).left (chart_le L _ σ hσ N fun _ => ch z)
      ((le_preimage_lbPow _ L N fun _ => ch z).2 (hch z))
  have hval : ∀ i z, valAt' ((u.ex z).left ≫ σ) ((Out.powOver A L ⊤ N).U fun _ => ch z)
      ((s i).f fun _ => ch z) = θ i z * u.fr (ch z) z ^ N := fun i z =>
    have k := (le_preimage_lbPow _ L N fun _ => ch z).2 (hch z)
    (hs' i _ _ k).symm.trans (hθfn i _ z k)
  have hfr0 : ∀ z, u.fr (ch z) z ^ N ≠ 0 := fun z => pow_ne_zero _ (u.fr_ne _ _ (hch z))
  have hmem : ∀ i z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ Out.nonzeroLocus (s i) ↔ θ i z ≠ 0 := fun i z => by
    rw [le_preimage_nonzeroLocus _ (s i) _ (hU z), hval, mul_ne_zero_iff_right (hfr0 z)]
  have hcov' : ∀ z, ∃ i, θ i z ≠ 0 := fun z => by
    have hz : ((u.ex z).left ≫ σ) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
      rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, (hmem i z).1 ((top_le_preimage_iff_mem _ _).2 hi)⟩

  set HN : Matrix (Fin g) (Fin g) ℂ := ((N : ℝ) : ℂ) • Hm with hHNdef
  have hHN : HN.IsHermitian := isHermitian_smul hH _
  have htr : ∀ i (l : u.Λ) z, θ i (z + l) =
      (χ l ^ N * cexp (Real.pi * (z ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))))) * θ i z := by
    intro i l z
    have hper : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    rw [hθper i z (z + l) _ hper fun j hj => hfr l j z hj, form_smul, form_smul, mul_pow,
      ← Complex.exp_nat_mul]
    congr 3
    push_cast
    ring
  have hχN : ∀ l, ‖χ l ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]

  obtain ⟨i0, hi0⟩ := hcov' 0
  have hne : θ i0 ≠ 0 := fun h => hi0 (by rw [h]; rfl)
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le u.Λ hHN (fun l => χ l ^ N) hχN
    (hθd i0).continuous (htr i0)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w => by
    by_contra hw
    push_neg at hw
    have hw' : (w ⬝ᵥ HN.mulVec (star w)).re < 0 := by
      rw [form_smul, re_ofReal_mul]
      exact mul_neg_of_pos_of_neg hNpos hw
    exact hne (ThetaPositivity.eq_zero_of_neg hHN (hθd i0) hC hw')

  have hrval : ∀ i j w, θ i w ≠ 0 →
      valAt' ((u.ex w).left ≫ σ) (Out.nonzeroLocus (s i)) (r i j) * θ i w = θ j w := by
    intro i j w hw
    have hw' := (hmem i w).2 hw
    have k := (le_preimage_inf _ _ _).2 ⟨hw', hU w⟩
    have k₁ := congrArg (valAt' ((u.ex w).left ≫ σ) _) (hr i j fun _ => ch w)
    rw [val_mul _ k, val_resG _ _ k, val_resG _ _ k, val_resG _ _ k, hval, hval,
      ← _root_.mul_assoc] at k₁
    exact (mul_right_cancel₀ (hfr0 w) k₁).symm
  have hc : ∀ w w', ((u.ex w).left ≫ σ) ≫ (A.hom ∣_ ⊤) = ((u.ex w').left ≫ σ) ≫ (A.hom ∣_ ⊤) := by
    intro w w'
    rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hσ, Over.w]

  have hker : ∀ v : Fin g → ℂ, Hm.mulVec (star v) = 0 → v = 0 := by
    intro v hv
    have hvN : HN.mulVec (star v) = 0 := by rw [hHNdef, Matrix.smul_mulVec, hv, smul_zero]
    have hinv : ∀ i (t : ℂ), θ i (t • v) = θ i 0 := fun i t => by
      simpa using theta_add_smul_eq u.Λ hHN _ hχN (hθd i) (htr i) hvN 0 t
    have hpt : ∀ t : ℂ, (u.ex (t • v)).left ≫ σ = (u.ex 0).left ≫ σ := by
      intro t
      obtain ⟨i, h0⟩ := hcov' 0
      have h0' : θ i (t • v) ≠ 0 := by rw [hinv]; exact h0
      have m0 := (hmem i 0).2 h0
      have mt := (hmem i _).2 h0'
      refine UnifTangent.eq_of_values (hDa i) mt m0 fun f => ?_
      obtain ⟨Q, rfl⟩ := hsurj i f
      induction Q using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a mt).trans
          ((congrArg (fun y => valAt' y ⊤ a) (hc _ 0)).trans (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a m0).symm)
      | add Q Q' h h' => rw [map_add (f := _), val_add _ mt, val_add _ m0, h, h']
      | mul_X Q j h =>
        rw [map_mul, val_mul _ mt, val_mul _ m0, h, MvPolynomial.eval₂Hom_X']
        congr 1
        have a1 := hrval i j _ h0'
        have a2 := hrval i j 0 h0
        rw [hinv, hinv] at a1
        exact mul_right_cancel₀ h0 (a1.trans a2.symm)
    refine eq_zero_of_smul_mem u.Λ fun t => (u.ker _).1 ?_
    have e : u.ex (t • v) = u.ex 0 := by
      ext1
      have := hpt t =≫ (A.hom ⁻¹ᵁ ⊤).ι
      rwa [Category.assoc, Category.assoc, hσ, Category.comp_id, Category.comp_id] at this
    have e0 : u.ex 0 = 1 := by
      have h00 := u.ex_add 0 0
      rw [add_zero] at h00
      exact (mul_eq_left.mp h00.symm)
    rw [e, e0]

  intro z hz
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (ThetaPositivity.form_conj hH w w)
    simp only [star_def, conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => hz (hker z ?_)
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  refine (hpsd.dotProduct_mulVec_zero_iff).mp ?_
  rw [star_star]
  exact Complex.ext h0.symm (him z)

end GlobalTheory.AmpleHermPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.AbCoh.StepPrim

theorem pO1_comp {R : Type} [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) g.left (ovw g) R X.left X.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (Over.comp_left _ _ _ f g)
    (fun _ ↦ rfl)).1 a |>.symm

theorem pO1_id {R : Type} [CommRing R] (A : Over (Sp R)) (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).2.2 R A).1 a

theorem eq_zero_of_base {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI := ((GlobalTheory.AbCoh.Vanish.main).1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom
    (inferInstanceAs (IsAffine (Sp R)))).1
  exact Subsingleton.elim _ _

theorem axes_defect {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (x : HO1 A.hom) :
    pO1 (lift (𝟙 A) (1 : A ⟶ A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 ∧
    pO1 (lift (1 : A ⟶ A) (𝟙 A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 := by
  have h1 : ∀ a : HO1 A.hom, pO1 (1 : A ⟶ A) a = 0 := fun a ↦ by
    rw [Hom.one_def, pO1_comp, eq_zero_of_base (pO1 η[A] a), map_zero]
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.mul_one, pO1_id, h1, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.one_mul, pO1_id, h1, sub_zero, sub_self]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ _ t R' _ σ' hsurj hker ht hmt hfield hR' A _ g hab hsm
  letI : Algebra R R' := σ'.toAlgebra
  have hkF : IsField (R ⧸ IsLocalRing.maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hSE : SmallExt t (algebraMap R R') (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) := by
    refine ⟨hsurj, hker, Ideal.Quotient.mk_surjective, fun a ↦ ?_⟩
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨hmt a, fun h ↦ ?_⟩
    by_contra hna
    exact ht ((IsLocalRing.notMem_maximalIdeal.mp hna).mul_right_eq_zero.mp h)
  haveI := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : Flat A.hom := inferInstance
  have hfl2 : Flat (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨B', _, pr, pr', hab', hsm', hpr, hpr', hμ', hf', hs', he1', he2'⟩ := _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R R' A g hab hsm
  obtain ⟨B₀, _, pr0, pr0', hab0, hsm0, hpr0, hpr0', -, -, -, he10, he20⟩ :=
    _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R (R ⧸ IsLocalRing.maximalIdeal R) A g hab hsm
  intro x
  have key : pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x = 0 := by
    set y := pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x with hy
    have hnat := GlobalTheory.AbCoh.pull_over_baseChange_comm R R' (algebraMap R R') A (A ⊗ A) B' (B' ⊗ B')
    have ya : pullHO1 hpr'.w y = 0 := by
      have hP := hR' B' g hab' hsm' (pullHO1 hpr.w x)
      rw [hy, map_sub, map_sub, (hnat μ[A] μ[B'] pr pr' hpr.w hpr'.w hμ').1,
        (hnat (fst A A) (fst B' B') pr pr' hpr.w hpr'.w hf').1,
        (hnat (snd A A) (snd B' B') pr pr' hpr.w hpr'.w hs').1, hP]
      abel
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.AbCoh.tmul_of_pull_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y ya
    have hH0 := (_root_.GlobalTheory.AbCoh.uConst_of_isAbelianScheme R A hab) R' B'.left B'.hom pr hpr
    have hax := axes_defect A x
    have hu1 : pO1 (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)) u = 0 :=
      _root_.GlobalTheory.AbCoh.tmul_pull_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 B') (1 : B' ⟶ B')).left (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)).left
        (ovw _) (ovw _) (ovw _) he1' he10 hSE hfl2 inferInstance hH0 u y hu hax.1
    have hu2 : pO1 (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)) u = 0 :=
      _root_.GlobalTheory.AbCoh.tmul_pull_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : B' ⟶ B') (𝟙 B')).left (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
        (ovw _) (ovw _) (ovw _) he2' he20 hSE hfl2 inferInstance hH0 u y hu hax.2
    have hu0 : u = 0 := (hfield _ hkF B₀ g hab0 hsm0).1 u hu1 hu2
    subst hu0
    exact _root_.GlobalTheory.AbCoh.tMul_zero_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y hu
  rw [sub_sub, sub_eq_zero] at key
  exact key

end GlobalTheory.AbCoh.StepPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBis
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem Good.good_of_isPullback' {g : ℕ} {X Y X' Y' : Scheme.{0}} {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {h : Y' ⟶ Y} (sq : IsPullback k f' f h) (hf : Good g f) : Good g f' := by
  exact
    { proper := MorphismProperty.of_isPullback (P := @IsProper) sq hf.proper
      smooth := MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) sq hf.smooth
      conn := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hf.conn }

theorem HasRep.baseChange (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (h : S'' ⟶ S')
    (H : HasRep A g S') : HasRep A g S'' := by
  obtain ⟨B, b, P, hRep, hGood⟩ := H

  have sq := IsPullback.of_hasPullback b h
  refine ⟨pullback b h, pullback.snd b h, ev P (fst A (pullback b h)) (snd A (pullback b h) ≫ pullback.fst b h),
    GlobalTheory.T.rep_ev_of_isPullback S A B S' S'' (pullback b h) b P h _ _ hRep sq, ?_⟩

  exact Good.good_of_isPullback' (sq.map (Over.forget S)) hGood

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCoefficientComparisonCommPairPullback
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open Opposite
namespace GlobalTheory.Obs.BC

theorem tensPair_extMap_pairPull : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  intro R₀ R₁ _ _ _ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' _ _ w w' f₀ f₁ h₀ h₁ e p b
  have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (U : X₀.Opens) (V : Y₁.Opens) (k : V ≤ g ⁻¹ᵁ U) (k' : V ≤ g' ⁻¹ᵁ U),
      g.appLE U V k = g'.appLE U V k' := by
    rintro g _ rfl U V k k'; rfl
  change tensHom w' (unop ((pairFst f₀).obj p)) _ (extHom R₁ (coefHom (pairPull h₀) p) b) =
    GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop) (tensHom w (unop ((pairSnd f₀).obj p)) _ b)
  induction b using TensorProduct.induction_on with
  | zero => repeat erw [map_zero]
            all_goals exact rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]; exact rfl
  | tmul r x =>
    refine (congrArg (tensHom w' _ _) (Algebra.TensorProduct.map_tmul _ _ r x)).trans ?_
    refine (tensHom_tmul w' _ _ r _).trans ?_
    have h2 := congrArg (GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop))
      (tensHom_tmul w (unop ((pairSnd f₀).obj p)) ((isAffine_aff _).preimage pr) r x)
    refine Eq.trans ?_ h2.symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    · exact ((semiHom_secPull h₁ (pairBCObj pr pr' e p.unop)).map_algebraMap r).symm
    · change (pr'.appLE _ _ _).hom ((f₀.appLE _ _ _).hom x) = (f₁.appLE _ _ _).hom ((pr.appLE _ _ _).hom x)
      have c1 := Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1 (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl
      have c2 := Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1 (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl
        (pairBCObj pr pr' e p.unop).2
      rw [key (pr' ≫ f₀) (f₁ ≫ pr) e.symm _ _ _ (by rw [e]; exact pr'.preimage_mono p.unop.2)] at c1
      exact (congrArg (fun t ↦ t.hom x) c1).trans (congrArg (fun t ↦ t.hom x) c2).symm

end GlobalTheory.Obs.BC
end
end

