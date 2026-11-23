module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUniformiserAdjoinRootTensorIsReduced
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial TensorProduct

namespace KummerRootTensor

variable {E : Type} [CommRing E] (B : Type) [CommRing B] [Algebra E B]

theorem aeval_root_map (Q : E[X]) :
    Polynomial.aeval (AdjoinRoot.root (Q.map (algebraMap E B))) Q = 0 := by
  rw [← Polynomial.aeval_map_algebraMap B, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem aeval_one_tmul_root (Q : E[X]) :
    Polynomial.aeval ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q) (Q.map (algebraMap E B)) = 0 := by
  have h : (1 : B) ⊗ₜ[E] AdjoinRoot.root Q =
      (Algebra.TensorProduct.includeRight : AdjoinRoot Q →ₐ[E] B ⊗[E] AdjoinRoot Q)
        (AdjoinRoot.root Q) := rfl
  rw [Polynomial.aeval_map_algebraMap, h, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self, map_zero]

noncomputable def toMap (Q : E[X]) : AdjoinRoot Q →ₐ[E] AdjoinRoot (Q.map (algebraMap E B)) :=
  AdjoinRoot.liftAlgHom Q (Algebra.ofId E _) (AdjoinRoot.root (Q.map (algebraMap E B)))
    (aeval_root_map B Q)

noncomputable def fromMap (Q : E[X]) :
    AdjoinRoot (Q.map (algebraMap E B)) →ₐ[B] B ⊗[E] AdjoinRoot Q :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q)
    (aeval_one_tmul_root B Q)

theorem toMap_root (Q : E[X]) :
    toMap B Q (AdjoinRoot.root Q) = AdjoinRoot.root (Q.map (algebraMap E B)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem fromMap_root (Q : E[X]) :
    fromMap B Q (AdjoinRoot.root (Q.map (algebraMap E B))) = (1 : B) ⊗ₜ[E] AdjoinRoot.root Q :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

noncomputable def toTensorMap (Q : E[X]) :
    B ⊗[E] AdjoinRoot Q →ₐ[B] AdjoinRoot (Q.map (algebraMap E B)) :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (toMap B Q) (fun _ _ => Commute.all _ _)

theorem toTensorMap_one_tmul_root (Q : E[X]) :
    toTensorMap B Q ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q) = AdjoinRoot.root (Q.map (algebraMap E B)) := by
  rw [toTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul, toMap_root]

noncomputable def tensorEquiv (Q : E[X]) :
    B ⊗[E] AdjoinRoot Q ≃ₐ[B] AdjoinRoot (Q.map (algebraMap E B)) :=
  AlgEquiv.ofAlgHom (toTensorMap B Q) (fromMap B Q)
    (by
      apply AdjoinRoot.algHom_ext
      show toTensorMap B Q (fromMap B Q (AdjoinRoot.root _)) = _
      rw [fromMap_root, toTensorMap_one_tmul_root]; rfl)
    (by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · apply AdjoinRoot.algHom_ext
        show fromMap B Q (toTensorMap B Q ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q)) = _
        rw [toTensorMap_one_tmul_root, fromMap_root]; rfl)

end KummerRootTensor

theorem kummer_uniformiser_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hφ hπ he
  obtain ⟨φ⟩ := hφ
  set f : S[X] := X ^ e - C π with hf
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have hπ' : algebraMap S L π ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have he' : (e : L) ≠ 0 := by
    have := he.map (algebraMap S L)
    rw [map_natCast] at this
    exact this.ne_zero
  have hmap : f.map (algebraMap S L) = X ^ e - C (algebraMap S L π) := by
    simp [hf, Polynomial.map_sub, Polynomial.map_pow]
  have hsep : (f.map (algebraMap S L)).Separable := by
    rw [hmap]; exact separable_X_pow_sub_C _ he' hπ'
  have hred : IsReduced (AdjoinRoot (f.map (algebraMap S L))) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  let ψ : TensorProduct S D L ≃ₐ[S] AdjoinRoot (f.map (algebraMap S L)) :=
    (Algebra.TensorProduct.comm S D L).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl φ).trans
        ((KummerRootTensor.tensorEquiv L f).restrictScalars S))
  exact isReduced_of_injective ψ.toRingHom ψ.injective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLeibniz
section
namespace GlobalTheory.TensorLeibnizRule

open TensorProduct

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : TensorProduct ℂ R S) :
    (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) (x * y) =
      x * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) y +
      y * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' s' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, TensorProduct.tmul_add]
      rw [mul_comm r' r]
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), h₁, h₂, map_add (f := _), mul_add, add_mul]
      abel
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), h₁, h₂, map_add (f := _), add_mul, mul_add]
    abel

end GlobalTheory.TensorLeibnizRule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowNumericalEnd
section
namespace GlobalTheory

theorem lamLow_numerical_end : ∀ (f n r : ℕ) (L' dmax mass Lq lam : ℝ) (H dt dk dD : Fin f → ℝ), 8 ≤ n → 2 * r ≤ n → 1 ≤ r → 1 ≤ f → (5.5 : ℝ) ≤ L' → Real.log n ≤ L' → 0 ≤ dmax → Real.log (dmax + 2) ≤ 2 * L' → 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass → 0 < Lq → |Real.log Lq| ≤ f * r / 4 → (∀ ρ, 0 < H ρ ∧ 1 ≤ dt ρ ∧ 1 ≤ dk ρ ∧ 0 < dD ρ ∧ Real.log (dD ρ) ≤ 2 + (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2))) → lam = mass * Lq * ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) → ∑ ρ, Real.log (H ρ) - 2 * f * (n : ℝ) ^ 2 * L' ≤ Real.log lam := by
  intro f n r L' dmax mass Lq lam H dt dk dD hn hr hr1 hf hL' hlogn hdmax hlogd hmass hLq hlogLq hρ hlam
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2 : 2 * (r : ℝ) ≤ n := by exact_mod_cast hr
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hmpos : 0 < mass := lt_of_lt_of_le (by positivity) hmass
  have hlogmass : -((n : ℝ) * Real.log 2 + (n : ℝ) * Real.log n) ≤ Real.log mass := by
    have h1 := Real.log_le_log (by positivity) hmass
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have hfac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.factorial_le_pow n
    linarith
  have hX : Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 * L' := by
    have hd : (0 : ℝ) < dmax + 2 := by linarith
    have h3 : 3 * (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hle : 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 3 * (dmax + 2) := by
      calc 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 2 * n * (dmax + 2) := by gcongr
        _ = (n : ℝ) ^ 3 * (dmax + 2) := by ring
    have hpos : 0 < 3 * (r : ℝ) ^ 2 * n * (dmax + 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hrpos 2)) hnpos) hd
    have h4 := Real.log_le_log hpos hle
    rw [Real.log_mul (pow_pos hnpos 3).ne' hd.ne', Real.log_pow] at h4
    push_cast at h4
    linarith
  have hsq : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by nlinarith
  have hdD : (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 / 4 * (n : ℝ) ^ 2 * L' := by
    calc (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ (r : ℝ) ^ 2 * (5 * L') :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 4 * (5 * L') := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = 5 / 4 * (n : ℝ) ^ 2 * L' := by ring
  have hfac_pos : ∀ ρ, 0 < H ρ * dt ρ * dk ρ / dD ρ := fun ρ => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    exact div_pos (mul_pos (mul_pos h1 ht) hk) h4
  have hprodpos : 0 < ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) := Finset.prod_pos (fun ρ _ => hfac_pos ρ)
  have e1 : Real.log lam = Real.log mass + Real.log Lq + ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    rw [hlam, Real.log_mul (mul_pos hmpos hLq).ne' hprodpos.ne', Real.log_mul hmpos.ne' hLq.ne',
      Real.log_prod (fun ρ _ => (hfac_pos ρ).ne')]
  have e2 : ∀ ρ, Real.log (H ρ) - (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤ Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    rw [Real.log_div (mul_pos (mul_pos h1 ht) hk).ne' h4.ne', Real.log_mul (mul_pos h1 ht).ne' hk.ne',
      Real.log_mul h1.ne' ht.ne']
    have := Real.log_nonneg h2
    have := Real.log_nonneg h3
    linarith
  have hsum : ∑ ρ, Real.log (H ρ) - (f : ℝ) * (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤
      ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    have := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => e2 ρ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hLqlow : -((f : ℝ) * r / 4) ≤ Real.log Lq := by
    have := neg_abs_le (Real.log Lq)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfL : 1 ≤ (f : ℝ) * L' := by nlinarith
  have hP1 : (n : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hfL hnpos.le]
  have hnL : 0 ≤ (n : ℝ) * L' := by positivity
  have hP2 : (n : ℝ) * L' ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_right hf1 hnL]
  have hP3 : (f : ℝ) * r / 4 ≤ f * n * L' := by
    have hrn : (r : ℝ) / 4 ≤ n * L' := by nlinarith
    linarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0 : ℝ) ≤ f)]
  have hnL2 : (2 : ℝ) ≤ n * L' := by nlinarith [mul_le_mul hn8 hL' (by norm_num) hnpos.le]
  have hP4 : 2 * (f : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hnL2 (by linarith : (0 : ℝ) ≤ f)]
  have hbig : 8 * ((f : ℝ) * n * L') ≤ f * (n : ℝ) ^ 2 * L' := by
    have h0 : 0 ≤ (f : ℝ) * n * L' := by positivity
    linarith [mul_le_mul_of_nonneg_right hn8 h0]
  have hm1 := mul_le_mul_of_nonneg_left hlog2 hnpos.le
  have hm2 := mul_le_mul_of_nonneg_left hlogn hnpos.le
  rw [e1]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiples
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem lattice_hom_finite_image_of_trivial_on_multiples :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  intro g Λ G _ e N hd hspan hadd hN hker
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f : (Module.Free.ChooseBasisIndex ℤ Λ → Fin N) → G :=
    fun a => e (∑ i, ((a i : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ))
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  set x : Λ := ⟨l, hl⟩ with hxdef
  let c : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => b.repr x i
  let q : Λ := ∑ i, (c i / N) • b i
  have hc : ∀ i, 0 ≤ c i % (N : ℤ) := fun i => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  refine ⟨fun i => ⟨(c i % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  · have hl' : l = (N : ℂ) • ((q : Λ) : Fin g → ℂ) +
        ∑ i, (((c i % (N : ℤ)).toNat : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ) := by
      have hx : l = ((∑ i, c i • b i : Λ) : Fin g → ℂ) := by
        rw [b.sum_repr x]
      rw [hx]
      simp only [q, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.toNat_of_nonneg (hc i)]
      have hN' : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
      rw [hN', Int.cast_smul_eq_zsmul, smul_smul, ← add_smul]
      have h2 := Int.mul_ediv_add_emod (c i) (N : ℤ)
      congr 1
      linarith
    refine Eq.trans ?_ (congrArg e hl').symm
    rw [hadd, hker _ q.2, one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeShiftedCutoffSummable
section
noncomputable section

namespace GlobalTheory.LatticeSchwartz

theorem summable_one_add_norm_inv_pow' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ}
    (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem term_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h f : SchwartzMap V ℂ) (k N j m : ℕ) (x l : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ m f (x - l)‖ ≤
      (2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, m)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
      ((1 + ‖l‖)⁻¹) ^ N := by
  have hA := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, j)) le_rfl le_rfl h x
  have hB := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, m)) le_rfl le_rfl f (x - l)
  have hc : 1 + ‖l‖ ≤ (1 + ‖x‖) * (1 + ‖x - l‖) := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    nlinarith [norm_nonneg x, norm_nonneg (x - l)]
  have hc0 : 0 < 1 + ‖l‖ := by positivity
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  set P := ‖iteratedFDeriv ℝ j h x‖
  set Q := ‖iteratedFDeriv ℝ m f (x - l)‖
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖x‖ ^ k * P * Q * (1 + ‖l‖) ^ N
      ≤ (1 + ‖x‖) ^ k * P * Q * ((1 + ‖x‖) * (1 + ‖x - l‖)) ^ N := by gcongr
    _ = ((1 + ‖x‖) ^ (k + N) * P) * ((1 + ‖x - l‖) ^ N * Q) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

theorem summable_seminorm_mul_comp_sub : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  intro V _ _ _ Λ _ _ h f _ u hu k n
  set N := Module.finrank ℤ Λ + 1 with hN
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set D : ℕ → ℝ := fun j => (n.choose j : ℝ) *
      ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by
    have h1 : 0 ≤ (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h := apply_nonneg _ _
    have h2 : 0 ≤ (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := apply_nonneg _ _
    positivity
  set C := ∑ j ∈ Finset.range (n + 1), D j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hD0 j
  refine Summable.of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_) (hw.mul_left C)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) fun x => ?_
  have hul : (u l : V → ℂ) = fun y => h y * f (y - l) := funext (hu l)
  rw [hul]
  have hg : ContDiff ℝ n (fun y : V => f (y - (l : V))) :=
    (f.smooth n).comp (contDiff_id.sub contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (h.smooth n) hg x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_sub] at hL
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h y * f (y - l)) x‖
      ≤ ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖ := by
        gcongr
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by
        refine Finset.sum_le_sum fun j _ => ?_
        have ht := term_le h f k N j (n - j) x l
        have hch : (0 : ℝ) ≤ n.choose j := Nat.cast_nonneg _
        calc (n.choose j : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖)
            ≤ (n.choose j : ℝ) * ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup
                (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
              (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
              ((1 + ‖(l : V)‖)⁻¹) ^ N) := mul_le_mul_of_nonneg_left ht hch
          _ = D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by rw [hD]; ring
    _ = C * ((1 + ‖l‖)⁻¹) ^ N := by rw [hC, Finset.sum_mul]; rfl

end GlobalTheory.LatticeSchwartz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeTranslatesCutoffSummable
section
open SchwartzMap

noncomputable section

namespace GlobalTheory.SchwartzTranslateSum

theorem summable_one_add_norm_inv_pow' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem summable_seminorm_mul_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall (0 : V)
  set N := Module.finrank ℤ Λ + 1 with hNdef
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hSdef
  set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h
    with hAdef
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  clear_value D A S R' N
  refine (hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)
  have hfun : (u l : V → ℂ) = fun y => h (y + l) * f y := funext (hu l)
  rw [hfun]
  have hsh : ContDiff ℝ n (fun y => h (y + (l : V))) :=
    ((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)
  have hsf : ContDiff ℝ n (f : V → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_add_right] at hleib
  by_cases hx : x + (l : V) ∈ tsupport h
  · have hxl : ‖x + (l : V)‖ ≤ R' := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (hR'def ▸ le_max_left _ _)
    have hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖) := by
      have : ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖ := by
        calc ‖(l : V)‖ = ‖(x + (l : V)) - x‖ := by simp
          _ ≤ ‖x + (l : V)‖ + ‖x‖ := norm_sub_le _ _
      have hn' : ‖l‖ = ‖(l : V)‖ := rfl
      nlinarith [norm_nonneg x]
    have hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N := by
      intro m hm
      have h1 := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m)
        le_rfl hm f x
      have h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S := by rw [hSdef]; exact h1
      have hpos : 0 < (1 + ‖l‖) ^ N := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ * (1 + ‖l‖) ^ N
          ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ * ((1 + R') * (1 + ‖x‖)) ^ N := by
            gcongr
            linarith [norm_nonneg x]
        _ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr
        _ = D := by rw [hDdef]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h (x + l)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h (x + l)‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h *
            (D * ((1 + ‖l‖)⁻¹) ^ N) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity))
              (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)
      _ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by
            rw [hAdef, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
  · have hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0 := fun i =>
      Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib
    have : ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0 :=
      le_antisymm hleib (norm_nonneg _)
    rw [this, mul_zero]
    exact mul_nonneg (mul_nonneg hA0 hD0) (by positivity)

end GlobalTheory.SchwartzTranslateSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosLowerBoundOnFinset
section
namespace GlobalTheory.PositiveLowerBoundFinset

theorem pos_lower_bound_on_finset : ∀ {Y : Type} (T : Finset Y) (f : Y → ℝ),
    (∀ (P : Y), (0 : ℝ) < f P) → ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ P ∈ T, r ≤ f P := by
  intro Y T f hf
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, -, hmin⟩ := T.exists_min_image f h
    exact ⟨f x, hf x, hmin⟩

end GlobalTheory.PositiveLowerBoundFinset
end

