module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section
variable {R : Type} [CommRing R] {n : ℕ}

private def kry (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (g ^ (j : ℕ) *ᵥ v) i

private noncomputable def pol (c : Fin n → R) : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)

private theorem kry_mulVec (g : Matrix (Fin n) (Fin n) R) (v c : Fin n → R) :
    kry g v *ᵥ c = aeval g (pol c) *ᵥ v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pol, map_sum, Matrix.sum_mulVec]
  funext i
  rw [Finset.sum_apply]
  simp only [aeval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, kry, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem pol_coeff (p : R[X]) (h : p.degree < n) : pol (fun i : Fin n => p.coeff i) = p := by
  simp only [pol]
  exact sum_fin (fun i a => monomial i a) (by simp) h |>.trans (sum_monomial_eq p)

private theorem aeval_mulVec [Nontrivial R] (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (p : R[X]) :
    aeval g p *ᵥ v = kry g v *ᵥ fun i : Fin n => (p %ₘ g.charpoly).coeff i := by
  rw [kry_mulVec, pol_coeff, ← Matrix.aeval_eq_aeval_mod_charpoly]
  have := degree_modByMonic_lt p g.charpoly_monic
  rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this

private theorem mul_kry [Nontrivial R] (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    g * kry g v = kry g v * Matrix.of fun i j : Fin n => ((X ^ ((j : ℕ) + 1) : R[X]) %ₘ g.charpoly).coeff i := by
  ext i j
  have := congrFun (aeval_mulVec g v (X ^ ((j : ℕ) + 1))) i
  rw [map_pow, aeval_X, pow_succ', ← Matrix.mulVec_mulVec] at this
  exact this

end

section
variable {K : Type} [Field K] {n : ℕ}

end

private theorem exists_kry {R : Type} [CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (h : g.charpoly.Separable) : ∃ v, IsUnit (kry g v).det :=
  _root_.UpperTheory.Reformulated.B.G8.exists_kry g h

end UpperTheory.ConvolutionTheory.D

open UpperTheory.ConvolutionTheory.D in
theorem UpperTheory.ConvolutionTheory.D.conjSep :
    UpperTheory.ConvolutionTheory.D.ConjSep := by
  intro k R _ _ _ _ _ n g h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨fun g' _ => ⟨1, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩,
      fun p => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩⟩
  have := PositivityTheory.UnitarySelfGeneration.free_semilocal k R
  obtain ⟨v, hv⟩ := exists_kry g h
  obtain ⟨P, hP⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv
  refine ⟨fun g' hg => ?_, fun y hy => ?_, fun p => ⟨fun hp => ?_, ?_⟩⟩
  · obtain ⟨v', hv'⟩ := exists_kry g' (hg ▸ h)
    obtain ⟨Q, hQ⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv'
    have h1 := mul_kry g v
    have h2 := mul_kry g' v'
    rw [hg, ← hQ] at h2
    rw [← hP] at h1
    refine ⟨P * Q⁻¹, ?_⟩
    rw [Units.val_mul, ← mul_assoc, h1, mul_assoc, mul_assoc]
    congr 1
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h2, Units.inv_mul_cancel_left]
  · let c := (P⁻¹).val *ᵥ (y *ᵥ v)
    have h1 : aeval g (pol c) *ᵥ v = y *ᵥ v := by
      rw [← kry_mulVec, ← hP, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    refine ⟨pol c, (Units.mul_left_inj P).1 ?_⟩
    rw [hP]
    ext i j
    have c1 : y * g ^ (j : ℕ) = g ^ (j : ℕ) * y := (Commute.pow_right hy j).eq
    have c2 : aeval g (pol c) * g ^ (j : ℕ) = g ^ (j : ℕ) * aeval g (pol c) := by
      rw [← aeval_X_pow (R := R), ← map_mul, ← map_mul, mul_comm]
    change (y *ᵥ (g ^ (j : ℕ) *ᵥ v)) i = (aeval g (pol c) *ᵥ (g ^ (j : ℕ) *ᵥ v)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c1, c2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
  · have h1 := aeval_mulVec g v p
    rw [hp, Matrix.zero_mulVec, ← hP] at h1
    have h2 := congrArg (fun z => (P⁻¹).val *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [← modByMonic_eq_zero_iff_dvd g.charpoly_monic]
    have h3 := degree_modByMonic_lt p g.charpoly_monic
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at h3
    rw [← pol_coeff _ h3, ← h2]
    simp [pol]
  · rintro ⟨q, rfl⟩
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Descent
section
noncomputable section

open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem sum_pow_fix {α M : Type} [Monoid α] [AddCommGroup M] (a : α) (q : ℕ) (h : a ^ q = 1) (f : α → M) :
    ∑ j ∈ Finset.range q, f (a ^ (j + 1)) = ∑ j ∈ Finset.range q, f (a ^ j) := by
  have h1 := Finset.sum_range_succ (fun j => f (a ^ j)) q
  have h2 := Finset.sum_range_succ' (fun j => f (a ^ j)) q
  rw [h1, h, pow_zero] at h2
  exact (add_right_cancel h2).symm

private theorem sep_sum {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ) (hq : 0 < q)
    {t : ℕ} (x y : Fin t → R) (h : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0)
    {M : Type} [AddCommGroup M] [Module R M] (v : ℕ → M) :
    ∑ i, x i • ∑ j ∈ Finset.range q, (σ ^ j) (y i) • v j = v 0 := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]]
  simp [hq]

theorem descent : Descent := by
  intro k R _ _ _ σ q hG M _ _ _ _ s hs hq
  obtain ⟨t, x, y, hxy⟩ := hG.sep
  have hsj : ∀ (j : ℕ) (r : R) (m : M), (s ^ j) (r • m) = (σ ^ j) r • (s ^ j) m := by
    intro j
    induction j with
    | zero => intro r m; simp
    | succ j ih =>
      intro r m
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, AlgEquiv.mul_apply, ih, hs]
  have hfix : ∀ (n : M), s n = n → ∀ j : ℕ, (s ^ j) n = n := by
    intro n hn j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hn]
  have hT : ∀ m : M, (∑ j ∈ Finset.range q, s ^ j) m ∈ LinearMap.eqLocus s LinearMap.id := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.sum_apply, map_sum,
      ← sum_pow_fix s q hq fun a => a m]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', Module.End.mul_apply]
  have htr : ∀ r : R, ∃ c : k, algebraMap k R c = ∑ j ∈ Finset.range q, (σ ^ j) r := by
    intro r
    refine hG.fix _ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← sum_pow_fix σ q hG.pow fun a => a r]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]
  choose c hc using htr
  let T : M →ₗ[k] LinearMap.eqLocus s LinearMap.id := LinearMap.codRestrict _ _ hT
  have hTv : ∀ m, (T m : M) = ∑ j ∈ Finset.range q, (s ^ j) m := fun m => LinearMap.sum_apply _ _ _
  let g : M →ₗ[k] R ⊗[k] LinearMap.eqLocus s LinearMap.id :=
    ∑ i, (TensorProduct.mk k R _ (x i)).comp (T.comp (Algebra.lsmul k k M (y i)))
  have hg : ∀ m, g m = ∑ i, x i ⊗ₜ[k] T (y i • m) := fun m => LinearMap.sum_apply _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨g, fun z => ?_, fun m => ?_⟩
  · induction z with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul r n =>
      have h1 : ∀ i, T (y i • r • (n : M)) = c (y i * r) • n := by
        intro i
        apply Subtype.ext
        rw [hTv, Submodule.coe_smul, ← algebraMap_smul R (c _), hc, Finset.sum_smul, smul_smul]
        exact Finset.sum_congr rfl fun j _ => by rw [hsj, hfix n n.2]
      have h2 : ∑ i, c (y i * r) • x i = r := by
        have := sep_sum σ q hG.pos x y hxy (M := R) fun j => (σ ^ j) r
        simp only [pow_zero, AlgEquiv.one_apply] at this
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
        rw [Algebra.smul_def, hc, smul_eq_mul, mul_comm]
        simp only [map_mul, smul_eq_mul]
      have h3 : TensorProduct.lift ((Algebra.lsmul k k M (A := R)).toLinearMap.compl₂
          (LinearMap.eqLocus s LinearMap.id).subtype) (r ⊗ₜ[k] n) = r • (n : M) := rfl
      rw [h3, hg]
      simp_rw [h1, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, h2]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hg, map_sum]
    have := sep_sum σ q hG.pos x y hxy fun j => (s ^ j) m
    simp only [pow_zero, Module.End.one_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    change x i • (T (y i • m) : M) = _
    rw [hTv]
    simp only [hsj]

end UpperTheory.ConvolutionTheory.D
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
section
noncomputable section

open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {σ : R ≃ₐ[k] R} {q : ℕ}

private theorem sum_fixed (h : IsGal σ q) (r : R) :
    σ (∑ j ∈ Finset.range q, (σ ^ j) r) = ∑ j ∈ Finset.range q, (σ ^ j) r := by
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) r) q
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) r) q
  rw [h1, h.pow, pow_zero] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, add_right_cancel h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem exists_tr (h : IsGal σ q) :
    ∃ t : R →ₗ[k] k, ∀ r, algebraMap k R (t r) = ∑ j ∈ Finset.range q, (σ ^ j) r := by
  choose t ht using fun r => h.fix _ (sum_fixed h r)
  refine ⟨⟨⟨t, fun a b => h.inj ?_⟩, fun c a => h.inj ?_⟩, ht⟩
  · rw [map_add (f := _), ht, ht, ht, ← Finset.sum_add_distrib]
    simp only [map_add (f := _)]
  · simp only [RingHom.id_apply, smul_eq_mul]
    rw [map_mul, ht, ht, Finset.mul_sum]
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]

private theorem dual (h : IsGal σ q) {s : ℕ} {x y : Fin s → R}
    (hxy : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0) {t : R →ₗ[k] k}
    (ht : ∀ r, algebraMap k R (t r) = ∑ j ∈ Finset.range q, (σ ^ j) r) (r : R) :
    ∑ i, t (y i * r) • x i = r := by
  calc ∑ i, t (y i * r) • x i
      = ∑ i, ∑ j ∈ Finset.range q, x i * (σ ^ j) (y i) * (σ ^ j) r := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, ht, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; ring
    _ = ∑ j ∈ Finset.range q, (if j = 0 then 1 else 0) * (σ ^ j) r := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.sum_mul, hxy j (Finset.mem_range.1 hj)]
    _ = r := by
        simp [h.pos]

private theorem pow_tmul (A : Type) [CommRing A] [Algebra k A] (σ : R ≃ₐ[k] R) (j : ℕ) (a : A) (r : R) :
    ((Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) ^ j) (a ⊗ₜ r) =
      a ⊗ₜ (σ ^ j) r := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]
    simp

end

theorem galBase : GalBase := by
  intro k R _ _ _ A _ _ σ q h
  obtain ⟨t, ht⟩ := exists_tr h
  obtain ⟨s, x, y, hxy⟩ := h.sep
  have hd := dual h hxy ht
  have hsplit : (Fintype.linearCombination k x).comp
      (LinearMap.pi fun i => t.comp (LinearMap.mulLeft k (y i))) = LinearMap.id := by
    ext r
    simpa [Fintype.linearCombination_apply] using hd r
  have hfin : Module.Finite k R :=
    Module.Finite.of_surjective (Fintype.linearCombination k x) fun r =>
      ⟨_, LinearMap.congr_fun hsplit r⟩
  have hproj : Module.Projective k R := Module.Projective.of_split _ _ hsplit
  obtain ⟨c, hc⟩ : ∃ c, t c = 1 := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (LinearMap.range t) (⊤ : Submodule k R) Module.Finite.fg_top (by
        intro r _
        rw [← hd r]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem_smul (LinearMap.mem_range_self _ _) Submodule.mem_top)
    have h0 : r = 0 := h.inj (by
      rw [map_zero, Algebra.algebraMap_eq_smul_one]; exact hr0 1 Submodule.mem_top)
    obtain ⟨c, hc⟩ := hr
    exact ⟨-c, by rw [map_neg, hc, h0]; ring⟩
  refine ⟨hfin, hproj, ⟨fun m hm hm' => hm.ne_top ?_⟩, ?_⟩
  · have key : ∀ r ∈ m • (⊤ : Submodule k R), t r ∈ m := by
      intro r hr
      refine Submodule.smul_induction_on hr (fun a ha n _ => ?_) (fun a b ha hb => ?_)
      · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ ha
      · rw [map_add (f := _)]; exact m.add_mem ha hb
    rw [Ideal.eq_top_iff_one, ← hc]
    exact key c (by rw [hm']; exact Submodule.mem_top)
  · set τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl σ with hτ
    have hp : ∀ j a r, (τ ^ j) (a ⊗ₜ r) = a ⊗ₜ (σ ^ j) r := pow_tmul A σ
    let p : A ⊗[k] R →ₗ[k] A :=
      (TensorProduct.rid k A).toLinearMap.comp ((t.comp (LinearMap.mulLeft k c)).lTensor A)
    have hpp : ∀ a r, p (a ⊗ₜ r) = t (c * r) • a := fun a r => by simp [p]
    refine ⟨h.pos, ?_, ?_, ?_, s, fun i => 1 ⊗ₜ x i, fun i => 1 ⊗ₜ y i, fun j hj => ?_⟩
    · refine AlgEquiv.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rw [hp, h.pow]; rfl
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    · refine Function.LeftInverse.injective (g := p) fun a => ?_
      rw [Algebra.TensorProduct.algebraMap_apply, hpp, mul_one, hc, one_smul]
      rfl
    · intro z hz
      have h1 : ∀ z, algebraMap A (A ⊗[k] R) (p z) =
          ∑ j ∈ Finset.range q, (τ ^ j) ((1 ⊗ₜ c) * z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a r =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp]
          rw [← TensorProduct.tmul_sum, ← ht, hpp, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_eq_smul_one (t (c * r)), ← TensorProduct.smul_tmul]
          rfl
        | add a b ha hb =>
          simp only [map_add (f := _), mul_add, ha, hb, Finset.sum_add_distrib]
      have h2 : ∀ j : ℕ, (τ ^ j) z = z := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hz, ih]
      refine ⟨p z, ?_⟩
      rw [h1]
      simp only [map_mul, h2, hp]
      rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ← ht, hc, map_one,
        ← Algebra.TensorProduct.one_def, one_mul]
    · simp only [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum, hxy j hj]
      split_ifs
      · rfl
      · exact TensorProduct.tmul_zero _ _

end UpperTheory.ConvolutionTheory.D
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
section
noncomputable section

namespace UpperTheory.ConvolutionTheory.D

open Classical in
private theorem dual_sum (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (τ : E ≃ₐ[F] E) :
    ∑ i, b i * τ (b.traceDual i) = if τ = 1 then 1 else 0 := by
  have li : LinearIndependent E (fun t : E ≃ₐ[F] E => ((t : E →* E) : E → E)) :=
    (linearIndependent_monoidHom E E).comp (fun t : E ≃ₐ[F] E => (t : E →* E))
      (fun s t h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)
  have key := Fintype.linearIndependent_iff.1 li
    (fun t => (∑ i, b i * t (b.traceDual i)) - if t = 1 then 1 else 0) ?_ τ
  · exact sub_eq_zero.1 key
  funext z
  have hz : z = ∑ i, b i * algebraMap F E (Algebra.trace F E (b.traceDual i * z)) := by
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Algebra.trace F E (b.traceDual i * z) = b.repr z i := by
      conv_lhs => rw [← b.sum_repr z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, Module.Basis.trace_traceDual_mul]
      simp
    rw [this, Algebra.smul_def, mul_comm]
  simp only [trace_eq_sum_automorphisms, Finset.mul_sum, map_mul] at hz
  rw [Finset.sum_comm] at hz
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply, mul_assoc]
  exact sub_eq_zero.2 hz.symm

theorem galField : GalField := by
  classical
  intro F E _ _ _ _ _ σ hσ
  have ho : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  refine ⟨Module.finrank_pos, ho ▸ pow_orderOf_eq_one σ, (algebraMap F E).injective, fun r hr => ?_,
    Module.finrank F E, Module.finBasis F E, (Module.finBasis F E).traceDual, fun j hj => ?_⟩
  · have h : ∀ τ : E ≃ₐ[F] E, τ r = r := fun τ => by
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer (E ≃ₐ[F] E) r :=
        (Subgroup.zpowers_le).2 hr
      exact this (hσ τ)
    exact (IsGalois.mem_range_algebraMap_iff_fixed r).2 h
  · have := dual_sum F E (Module.finBasis F E) (σ ^ j)
    rw [show (if j = 0 then (1 : E) else 0) = if σ ^ j = 1 then 1 else 0 from
      if_congr ⟨fun h => by rw [h, pow_zero], fun h =>
        Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_of_pow_eq_one h) (ho ▸ hj)⟩ rfl rfl]
    convert this

end UpperTheory.ConvolutionTheory.D
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly
section
open Matrix Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (σ : R ≃ₐ[k] R)

private theorem sg_succ (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg (σ ^ m) (sg σ x) := by
  rw [pow_succ]
  rfl

private theorem sg_succ' (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg σ (sg (σ ^ m) x) := by
  rw [pow_succ']
  rfl

private theorem sg_one (x : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) x = x := rfl

private theorem nm_succ (m : ℕ) (δ : GL (Fin n) R) : nm σ (m + 1) δ = nm σ m δ * sg (σ ^ m) δ := by
  simp [nm, List.range_succ]

private theorem nm_conj (m : ℕ) (x δ : GL (Fin n) R) : nm σ m (sgConj σ x δ) = x⁻¹ * nm σ m δ * sg (σ ^ m) x := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, nm_succ, ih, sgConj, map_mul, map_mul, map_inv, sg_succ]
    group

private theorem sg_nm (m : ℕ) (δ : GL (Fin n) R) : sg σ (nm σ m δ) = δ⁻¹ * nm σ m δ * sg (σ ^ m) δ := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, map_mul, ih, ← sg_succ']
    group

end

theorem UpperTheory.ConvolutionTheory.D.nmPoly :
    UpperTheory.ConvolutionTheory.D.NmPoly := by
  intro k R _ _ _ σ q h n δ
  refine ⟨?_, fun x => by rw [nm_conj, h.pow, sg_one]⟩
  have e : (cp (nm σ q δ)).map (σ : R →+* R) = cp (nm σ q δ) := by
    have h1 := sg_nm σ q δ
    rw [h.pow, sg_one] at h1
    have h2 : cp (sg σ (nm σ q δ)) = (cp (nm σ q δ)).map (σ : R →+* R) := Matrix.charpoly_map _ _
    rw [← h2, h1, cp, cp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hl : cp (nm σ q δ) ∈ Polynomial.lifts (algebraMap k R) := (Polynomial.lifts_iff_coeff_lifts _).2 fun i =>
    h.fix _ (by simpa [Polynomial.coeff_map] using congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) e)
  obtain ⟨p, hp⟩ := hl
  exact ⟨p, Polynomial.monic_of_injective h.inj (by rw [show p.map (algebraMap k R) = _ from hp]; exact Matrix.charpoly_monic _), hp.symm⟩
end

