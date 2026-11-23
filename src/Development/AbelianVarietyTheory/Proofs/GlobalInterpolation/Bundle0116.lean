module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

private theorem polyConj_coord_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (x : E) :
    coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by
    first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]
  unfold coord
  split_ifs with hτ
  · simp only [Pi.evalRingHom_apply, h, hτ]
  · rcases InfinitePlace.embedding_mk_eq τ with h' | h'
    · exact absurd h' hτ
    · simp [h, h']

theorem exists_cEmb_entry_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {γ : UA E n}
    (hγ : γ ∈ ratU E n) {k : UA E n} (hk : cInf k = cInf γ) (i j : Fin n) :
    ∃ x : E, ∀ τ : E →+* ℂ, (cEmb τ k).val i j = τ x := by
  obtain ⟨γ₀, h₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine ⟨γ₀.val i j, fun τ => ?_⟩
  have h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j) := rfl
  have h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j) := rfl
  rw [h1, hk, h2, ← h₀]
  exact polyConj_coord_pInf τ _

theorem exists_conj_polyFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  intro E _ _ _ n σ p hp
  induction hp using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    refine ⟨_, Algebra.subset_adjoin ⟨σ.toRingHom.comp τ, i, j, rfl⟩, fun γ hγ k hk => ?_⟩
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk i j
    simp only [hx]
    rfl
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ (σ c), fun _ _ _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add (f := _), hf γ hγ k hk, hg γ hγ k hk]
  | mul f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' * g', mul_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, hf γ hγ k hk, hg γ hγ k hk]

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC
open scoped ComplexConjugate

namespace GlobalTheory.CMGen

theorem exists_integer_not_mem (K : Type) [Field K] [NumberField K] [IsCMField K] :
    ∃ x : 𝓞 K, (x : K) ∉ maximalRealSubfield K := by
  by_contra h
  push_neg at h
  apply NumberField.IsCMField.complexConj_ne_one K
  ext y
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have ha : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K) K a :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h a)
  have hb : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K b) = algebraMap (𝓞 K) K b :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h b)
  rw [map_div₀, ha, hb, AlgEquiv.one_apply]

theorem exists_extension (K : Type) [Field K] [NumberField K] (φ : maximalRealSubfield K →+* ℝ) :
    ∃ ψ : K →+* ℂ, ∀ x : maximalRealSubfield K,
      ψ (algebraMap (maximalRealSubfield K) K x) = (φ x : ℂ) := by
  letI : Algebra (maximalRealSubfield K) ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  haveI : Algebra.IsAlgebraic (maximalRealSubfield K) K := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let f : K →ₐ[maximalRealSubfield K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem exists_sqrt_totallyNegative : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    ∃ (d : 𝓞 (maximalRealSubfield K)) (δ : K), δ ^ 2 = algebraMap (maximalRealSubfield K) K d ∧
      δ ∉ maximalRealSubfield K ∧
      ∀ φ : maximalRealSubfield K →+* ℝ, φ (d : maximalRealSubfield K) < 0 := by
  intro K _ _ _
  obtain ⟨x, hx⟩ := exists_integer_not_mem K
  let y : 𝓞 K := x - NumberField.IsCMField.ringOfIntegersComplexConj K x
  have hy : (y : K) = (x : K) - NumberField.IsCMField.complexConj K (x : K) := by
    simp [y, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  have hconj : NumberField.IsCMField.complexConj K (y : K) = -(y : K) := by
    rw [hy, map_sub, NumberField.IsCMField.complexConj_apply_apply, neg_sub]
  have hy0 : (y : K) ≠ 0 := by
    intro h0
    apply hx
    rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    rw [hy, sub_eq_zero] at h0
    exact h0.symm
  have hsq : (y : K) ^ 2 ∈ maximalRealSubfield K := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  have hint : IsIntegral ℤ (⟨(y : K) ^ 2, hsq⟩ : maximalRealSubfield K) := by
    refine (isIntegral_algebraMap_iff (B := K)).mp ?_
    change IsIntegral ℤ ((y : K) ^ 2)
    exact (RingOfIntegers.isIntegral_coe y).pow 2
  refine ⟨⟨⟨(y : K) ^ 2, hsq⟩, hint⟩, (y : K), rfl, ?_, ?_⟩
  · intro hmem
    apply hy0
    have h2 := hconj
    rw [(NumberField.IsCMField.complexConj_eq_self_iff K _).mpr hmem] at h2
    have h3 : (2 : K) * (y : K) = 0 := by rw [two_mul]; nth_rewrite 1 [h2]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  · intro φ
    obtain ⟨ψ, hψ⟩ := exists_extension K φ
    have hval := hψ ⟨(y : K) ^ 2, hsq⟩
    have hψy : ψ (y : K) = ψ (x : K) - conj (ψ (x : K)) := by
      rw [hy, map_sub, NumberField.IsCMField.complexEmbedding_complexConj]
    have hne : ψ (y : K) ≠ 0 := by
      rw [map_ne_zero]; exact hy0
    have him : (ψ (x : K)).im ≠ 0 := by
      intro h0
      apply hne
      rw [hψy, Complex.sub_conj, h0]
      simp
    have key : ((φ ⟨(y : K) ^ 2, hsq⟩ : ℝ) : ℂ) = ((-(2 * (ψ (x : K)).im) ^ 2 : ℝ) : ℂ) := by
      rw [← hval]
      change ψ ((y : K) ^ 2) = _
      rw [map_pow, hψy, Complex.sub_conj]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have key' : φ ⟨(y : K) ^ 2, hsq⟩ = -(2 * (ψ (x : K)).im) ^ 2 := by exact_mod_cast key
    show φ ⟨(y : K) ^ 2, hsq⟩ < 0
    rw [key']
    have : 0 < (2 * (ψ (x : K)).im) ^ 2 := by positivity
    linarith

end GlobalTheory.CMGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfMulTwoAF
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] {N : ℕ}

namespace HeisenbergBilinear

section Forms

variable {R : Type} [CommRing R] [Algebra F R] (a : Fin N → F)

theorem qd_add (u x : Fin N → R) : qd R a (u + x) = qd R a u + qd R a x + Bd R a u x := by
  simp only [qd, Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_ofNat]
  ring

theorem Bd_add_left (u u' x : Fin N → R) : Bd R a (u + u') x = Bd R a u x + Bd R a u' x := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_add_right (u x x' : Fin N → R) : Bd R a u (x + x') = Bd R a u x + Bd R a u x' := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_smul_left (t : R) (u x : Fin N → R) : Bd R a (t • u) x = t * Bd R a u x := by
  simp only [Bd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_smul_right (t : R) (u x : Fin N → R) : Bd R a u (t • x) = t * Bd R a u x := by
  simp only [Bd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_neg_left (u x : Fin N → R) : Bd R a (-u) x = -Bd R a u x := by
  simp only [Bd, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_comm (u x : Fin N → R) : Bd R a u x = Bd R a x u := by
  simp only [Bd]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_self (x : Fin N → R) : Bd R a x x = 2 * qd R a x := by
  simp only [Bd, qd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_ofNat]
  ring

end Forms

variable [NumberField F]

theorem half_mul_two_AF : algebraMap F (AF F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem qd_rat (a : Fin N → F) (ξ : Fin N → F) : qd (AF F) a (rat ξ) = algebraMap F (AF F) (qd F a ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qd, rat, map_sum, map_mul, map_pow]
  rfl

end HeisenbergBilinear

open HeisenbergBilinear in
theorem weil_intertwine : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ,
      (∀ b x y, rho ψ a x y (Ub ψ a b Φ) = Ub ψ a b (rho ψ a x (y + b • x) Φ)) ∧
      (∀ (t t' : AF F) x y, t * t' = 1 → rho ψ a x y (Da t Φ) = Da t (rho ψ a (t • x) (t' • y) Φ)) ∧
      (∀ x y, rho ψ a x y (Fo ψ ν a Φ) = Fo ψ ν a (rho ψ a (-y) x Φ)) ∧
      (∀ b : F, th (Ub ψ a (algebraMap F (AF F) b) Φ) = th Φ) ∧
      ∀ t : F, t ≠ 0 → th (Da (algebraMap F (AF F) t) Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ
  obtain ⟨-, ⟨-, -, hchar, -⟩, -, ⟨hHaar, -⟩, -⟩ := hC
  have hh : algebraMap F (AF F) (1 / 2) * 2 = 1 := half_mul_two_AF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro b x y
    funext u
    simp only [rho, Ub]
    have key : ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) *
          ψ (b * qd (AF F) a (u + x)) =
        ψ (b * qd (AF F) a u) *
          ψ (Bd (AF F) a u (y + b • x) + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x (y + b • x)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [qd_add, Bd_add_right, Bd_smul_right, Bd_self]
      linear_combination (-(b * qd (AF F) a x)) * hh
    linear_combination (Φ (u + x)) * key
  ·
    intro t t' x y htt
    funext u
    simp only [rho, Da]
    have key : Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y =
        Bd (AF F) a (t • u) (t' • y) + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (t • x) (t' • y) := by
      simp only [Bd_smul_left, Bd_smul_right]
      linear_combination (-(Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y)) * htt
    rw [key, smul_add]
  ·
    intro x y
    funext u
    have : ν.IsAddHaarMeasure := hHaar
    have : (muV N ν).IsAddRightInvariant := by unfold muV; infer_instance
    simp only [rho, Fo]
    refine Eq.trans ?_ (integral_add_right_eq_self (μ := muV N ν)
      (fun s => ψ (Bd (AF F) a s x + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (-y) x) * Φ (s + -y) *
        ψ (Bd (AF F) a s u)) y)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only
    rw [add_neg_cancel_right]
    have key : ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) *
          ψ (Bd (AF F) a s (u + x)) =
        ψ (Bd (AF F) a (s + y) x + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (-y) x) *
          ψ (Bd (AF F) a (s + y) u) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have e1 := Bd_comm a u y
      have e2 := Bd_comm a x y
      simp only [Bd_add_left, Bd_add_right, Bd_neg_left]
      linear_combination e1 + algebraMap F (AF F) (1 / 2) * e2 + Bd (AF F) a y x * hh
    linear_combination (Φ s) * key
  ·
    intro b
    simp only [th, Ub]
    refine tsum_congr fun ξ => ?_
    rw [qd_rat, ← map_mul, hchar, one_mul]
  ·
    intro t ht
    simp only [th, Da]
    have e : ∀ ξ : Fin N → F, algebraMap F (AF F) t • rat ξ = rat (t • ξ) := by
      intro ξ
      funext l
      simp only [rat, Pi.smul_apply, smul_eq_mul, map_mul]
    simp only [e]
    exact Equiv.tsum_eq
      { toFun := fun ξ : Fin N → F => t • ξ
        invFun := fun ξ => t⁻¹ • ξ
        left_inv := fun ξ => by simp only [smul_smul, inv_mul_cancel₀ ht, one_smul]
        right_inv := fun ξ => by simp only [smul_smul, mul_inv_cancel₀ ht, one_smul] }
      (fun ξ => Φ (rat ξ))

end GlobalTheory.SWQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonality
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem Bd_add_left_AF (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem Bd_rat_rat (a : Fin N → F) (η ξ : Fin N → F) :
    Bd (AF F) a (rat η) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bd, rat, map_sum, map_mul, Algebra.algebraMap_self, RingHom.id_apply]

theorem charOrth : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  intro F _ _ N ψ lam ν a hC D hD _ ξ hξ
  haveI := hC.2.2.2.1.1
  have hmem : ∀ u : Fin N → AF F, u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) →
      ∃ η, u = rat η := by
    let φ : (Fin N → F) →+ (Fin N → AF F) :=
      AddMonoidHom.mk' rat (fun x y => by funext l; simp only [rat, Pi.add_apply, map_add (f := _)])
    intro u hu
    have hle : AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ≤ φ.range :=
      (AddSubgroup.closure_le _).mpr (by rintro _ ⟨η, rfl⟩; exact ⟨η, rfl⟩)
    obtain ⟨η, hη⟩ := hle hu
    exact ⟨η, hη.symm⟩
  haveI : (muV N ν).IsAddLeftInvariant := by unfold muV; infer_instance
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) := by
    have hs : (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) :
        Set (Fin N → AF F)).Countable :=
      (Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun u hu => by
        obtain ⟨η, rfl⟩ := hmem u hu
        exact ⟨η, rfl⟩
    exact hs.to_subtype
  obtain ⟨_, ⟨_, _, hF, x, hx⟩, _, _, ha⟩ := hC
  have hadd : ∀ u v : Fin N → AF F, ψ (Bd (AF F) a (u + v) (rat ξ)) =
      ψ (Bd (AF F) a u (rat ξ)) * ψ (Bd (AF F) a v (rat ξ)) := fun u v => by
    rw [Bd_add_left_AF, AddChar.map_add_eq_mul]
  have hper : ∀ g ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))),
      ∀ u, ψ (Bd (AF F) a (g + u) (rat ξ)) = ψ (Bd (AF F) a u (rat ξ)) := by
    intro g hg u
    obtain ⟨η, rfl⟩ := hmem g hg
    rw [hadd, Bd_rat_rat, hF, one_mul]
  obtain ⟨l, hl⟩ : ∃ l, ξ l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hξ (funext h)
  have hc : (2 * a l * ξ l) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ha l)) hl
  set u₀ : Fin N → AF F := Pi.single l (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) with hu₀def
  have hu₀ : ψ (Bd (AF F) a u₀ (rat ξ)) = ψ x := by
    congr 1
    simp only [Bd, rat]
    rw [Finset.sum_eq_single l]
    · rw [hu₀def, Pi.single_eq_same]
      have e : algebraMap F (AF F) (2 * a l) * (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) *
          algebraMap F (AF F) (ξ l) = algebraMap F (AF F) (2 * a l * ξ l * (2 * a l * ξ l)⁻¹) * x := by
        simp only [map_mul]; ring
      rw [e, mul_inv_cancel₀ hc, map_one, one_mul]
    · intro b _ hb
      rw [hu₀def, Pi.single_eq_of_ne hb]
      simp
    · intro h; exact absurd (Finset.mem_univ l) h
  have hD' := hD.vadd_of_comm u₀
  have h1 := hD.setIntegral_eq hD' (f := fun u => ψ (Bd (AF F) a u (rat ξ))) (fun g s => by
    show ψ (Bd (AF F) a ((g : Fin N → AF F) + s) (rat ξ)) = _
    exact hper g g.2 s)
  have h2 := (measurePreserving_add_left (muV N ν) u₀).setIntegral_image_emb
    (measurableEmbedding_addLeft u₀) (fun u => ψ (Bd (AF F) a u (rat ξ))) D
  have e : u₀ +ᵥ D = (fun s => u₀ + s) '' D := rfl
  rw [e, h2] at h1
  simp only [hadd, hu₀] at h1
  rw [integral_const_mul] at h1
  have hx1 : (1 : ℂ) - ψ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : ((1 : ℂ) - ψ x) * ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hx1

end GlobalTheory.SWQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.HenselSquare

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem isAdicComplete_integers (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    IsAdicComplete (maximalIdeal (u.adicCompletionIntegers F)) (u.adicCompletionIntegers F) := by
  letI := GlobalTheory.LocalData.complRel u
  haveI := GlobalTheory.LocalData.isLocalField u
  haveI := Valuation.Compatible.ofValuation
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hE : (ValuativeRel.valuation (u.adicCompletion F)).IsEquiv
      (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hmem : ∀ x : u.adicCompletion F,
      x ∈ (ValuativeRel.valuation (u.adicCompletion F)).integer ↔
        x ∈ u.adicCompletionIntegers F := fun x => by
    rw [mem_adicCompletionIntegers, Valuation.mem_integer_iff]
    exact hE.le_one_iff_le_one
  let e : (ValuativeRel.valuation (u.adicCompletion F)).integer ≃+* u.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hm : (maximalIdeal (ValuativeRel.valuation (u.adicCompletion F)).integer).map e =
      maximalIdeal (u.adicCompletionIntegers F) := by
    ext y
    rw [← Ideal.comap_symm, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff e.symm y)
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv _ e).2 inferInstance

theorem exists_sq_add_eq {O : Type} [CommRing O] [Nontrivial O] (I : Ideal O) [HenselianRing O I]
    (z : O) (hz : z ∈ I) : ∃ s : O, s ^ 2 + s = z := by
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C z) (by monicity!) 0
    (by simpa using hz) (by simp)
  refine ⟨s, ?_⟩
  have h2 : eval s (X ^ 2 + X - C z) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  linear_combination h2

theorem isSquare_one_add_four_mul : ∀ (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (z : 𝓞 F), z ∈ u.asIdeal → IsSquare (algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F)) := by
  intro F _ _ u z hz
  haveI := isAdicComplete_integers F u
  set z' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) z with hz'
  have hcoe : (z' : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (z : F) := by
    rw [hz', algebraMap_adicCompletionIntegers_apply]
    rfl
  have hv : Valued.v (algebraMap F (u.adicCompletion F) (z : F)) < 1 := by
    have h1 : u.valuation F (algebraMap (𝓞 F) F z) < 1 := by
      rw [valuation_of_algebraMap]
      exact (intValuation_lt_one_iff_mem (v := u) z).2 hz
    have h2 : Valued.v (((z : F) : u.adicCompletion F)) = u.valuation F (z : F) :=
      valuedAdicCompletion_eq_valuation' (v := u) (z : F)
    exact (h2.trans_lt h1 :)
  have hzm : z' ∈ maximalIdeal (u.adicCompletionIntegers F) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    rw [show (z'.1 : u.adicCompletion F) = (z' : u.adicCompletion F) from rfl, hcoe]
    exact ne_of_lt hv
  obtain ⟨s, hs⟩ := exists_sq_add_eq (maximalIdeal (u.adicCompletionIntegers F)) z' hzm
  have hsK : (s : u.adicCompletion F) ^ 2 + (s : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (z : F) := by
    rw [← hcoe, ← hs]
    norm_cast
  have hL : algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F) =
      1 + 4 * algebraMap F (u.adicCompletion F) (z : F) := by
    have e1 : ((1 + 4 * z : 𝓞 F) : F) = 1 + 4 * (z : F) := by
      rw [show (4 : 𝓞 F) = 1 + 1 + 1 + 1 by norm_num]
      push_cast
      ring
    rw [e1]
    simp only [map_add (f := _), map_one, map_mul, map_ofNat]
  refine ⟨1 + 2 * (s : u.adicCompletion F), ?_⟩
  rw [hL]
  linear_combination (-4 : u.adicCompletion F) * hsK

end GlobalTheory.HenselSquare
end

