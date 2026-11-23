module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.EventuallyRoot

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CommonZeroEvaluation.EigenLatticeDecomposition
section
open NumberField
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

open scoped TensorProduct in
theorem chars_injective {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {ι : Type} [Fintype ι]
    (emb : ι → (𝓞 E →+* Ω)) (hinj : Function.Injective emb) (hcard : Fintype.card ι = Module.finrank ℚ E)
    (Φ : Ω ⊗[ℤ] 𝓞 E →ₗ[Ω] (ι → Ω)) (hΦ : ∀ a j, Φ (1 ⊗ₜ a) j = emb j a) : Function.Injective Φ := by
  have hli : LinearIndependent Ω (fun j => (emb j : 𝓞 E → Ω)) :=
    (linearIndependent_monoidHom (𝓞 E) Ω).comp (fun j => (emb j : 𝓞 E →* Ω))
      (fun i j h => hinj (RingHom.ext fun a => DFunLike.congr_fun h a))
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hs : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, funext fun j => hΦ a j⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hs
  rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_fintype_fun_eq_card, hcard]

theorem eigen_lattice_decomposition : ∀ (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [CharZero Ω] (F₀ : Subfield Ω) (B A : Subring Ω), (∀ x ∈ F₀, x ∈ B) → B ≤ A → ∀ (ι : Type) [Fintype ι] (emb : ι → (𝓞 E →+* Ω)), Function.Injective emb → Fintype.card ι = Module.finrank ℚ E → (∀ i a, emb i a ∈ F₀) → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (ρ : 𝓞 E →+* Module.End Ω Li) (L : Submodule B Li), (∀ a, ∀ e ∈ L, ρ a e ∈ L) → ∀ (i : ι) (e : Li), e ∈ Submodule.span A (L : Set Li) → e ∈ eigSp ρ (emb i) → e ∈ Submodule.span A ((L ⊓ (eigSp ρ (emb i)).restrictScalars B : Submodule B Li) : Set Li) := by
  intro E _ _ Ω _ _ F₀ B A hFB hBA ι _ emb hinj hcard hF Li _ _ ρ L hL i e he hei
  classical
  have hne : ∀ j, ∃ a, j ≠ i → emb i a ≠ emb j a := fun j => by
    by_contra h
    push Not at h
    exact (h 0).1 (hinj (RingHom.ext fun a => (h a).2.symm))
  choose a ha using hne
  let Φ : TensorProduct ℤ Ω (𝓞 E) →ₐ[Ω] (ι → Ω) :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω _) (RingHom.pi emb).toIntAlgHom fun _ _ => Commute.all _ _
  let Ψ : TensorProduct ℤ Ω (𝓞 E) →ₐ[Ω] Module.End Ω Li :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω _) ρ.toIntAlgHom fun x y => Algebra.commutes x _
  have hΦ : ∀ b j, Φ (1 ⊗ₜ b) j = emb j b := fun b j => by
    have := Algebra.TensorProduct.lift_tmul (Algebra.ofId Ω _) (RingHom.pi emb).toIntAlgHom
      (fun _ _ => Commute.all _ _) 1 b
    rw [map_one, one_mul] at this
    exact congrFun this j
  have hΨ : ∀ b, Ψ (1 ⊗ₜ b) = ρ b := fun b => by
    have := Algebra.TensorProduct.lift_tmul (Algebra.ofId Ω _) ρ.toIntAlgHom
      (fun x y => Algebra.commutes x _) 1 b
    rw [map_one, one_mul] at this
    exact this
  have hΦi : Function.Injective Φ := chars_injective emb hinj hcard Φ.toLinearMap hΦ
  let t : ι → TensorProduct ℤ Ω (𝓞 E) := fun j =>
    (emb i (a j) - emb j (a j))⁻¹ • (1 ⊗ₜ a j - algebraMap Ω _ (emb j (a j)))
  have ht : ∀ j x, Ψ (t j) x = (emb i (a j) - emb j (a j))⁻¹ • (ρ (a j) x - emb j (a j) • x) := fun j x => by
    simp only [t, map_smul, map_sub, hΨ, AlgHom.commutes, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
  let p := ∏ j ∈ Finset.univ.erase i, t j
  have hmem : ∀ x, x ∈ eigSp ρ (emb i) ↔ ∀ b, ρ b x = emb i b • x := fun x => by
    simp [eigSp, sub_eq_zero]
  have h1 : ∀ x ∈ L, Ψ p x ∈ L := by
    refine Finset.prod_induction _ (fun q => ∀ x ∈ L, Ψ q x ∈ L) (fun q r hq hr x hx => ?_) (fun x hx => ?_)
      fun j _ x hx => ?_
    · rw [map_mul]; exact hq _ (hr x hx)
    · rw [map_one]; exact hx
    · rw [ht]
      exact L.smul_mem (⟨_, hFB _ (inv_mem (sub_mem (hF i _) (hF j _)))⟩ : B)
        (sub_mem (hL _ x hx) (L.smul_mem (⟨_, hFB _ (hF j _)⟩ : B) hx))
  have h2 : ∀ x ∈ eigSp ρ (emb i), Ψ p x = x := by
    refine Finset.prod_induction _ (fun q => ∀ x ∈ eigSp ρ (emb i), Ψ q x = x) (fun q r hq hr x hx => ?_)
      (fun x hx => ?_) fun j hj x hx => ?_
    · rw [map_mul, mul_apply_eq_comp, hr x hx, hq x hx]
    · rw [map_one]; rfl
    · rw [ht, (hmem x).1 hx, ← sub_smul, smul_smul,
        inv_mul_cancel₀ (sub_ne_zero.2 (ha j (Finset.ne_of_mem_erase hj))), one_smul]
  have h3 : ∀ x, Ψ p x ∈ eigSp ρ (emb i) := fun x => (hmem _).2 fun b => by
    have hz : (1 ⊗ₜ b - algebraMap Ω _ (emb i b)) * p = 0 := by
      apply hΦi
      rw [map_zero, map_mul]
      funext k
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        rw [map_sub, Pi.sub_apply, hΦ, AlgHom.commutes]
        simp
      · apply mul_eq_zero_of_right
        simp only [p, map_prod, Finset.prod_apply]
        refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) ?_
        simp only [t, map_smul, map_sub, AlgHom.commutes, Pi.smul_apply, Pi.sub_apply, hΦ]
        simp
    have h4 := congrArg (fun q => Ψ q x) hz
    simp only [map_mul, map_sub, hΨ, AlgHom.commutes, map_zero, mul_apply_eq_comp, LinearMap.sub_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply] at h4
    exact sub_eq_zero.1 h4
  rw [← h2 e hei]
  clear hei
  induction he using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨h1 x hx, h3 x⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

end ModelDimension
end
end

-- bundled from Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsAlgebraicStd
section
open Polynomial Filter Topology

namespace ModelDimension.Alg

theorem isAlgebraic_std {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (P : StandardEtalePresentation A B) (g : B) : IsAlgebraic A g := by
  haveI : Algebra.IsStandardEtale A B := ⟨⟨P⟩⟩
  have hx : IsIntegral A P.x := ⟨P.f, P.monic_f, P.hasMap.1⟩
  have hp : ∀ p : A[X], IsAlgebraic A (aeval P.x p) := fun p =>
    (IsIntegral.of_mem_of_fg _ hx.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)).isAlgebraic
  obtain ⟨p, n, h⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x g
  have hu : aeval P.x P.g ^ n ≠ 0 := (P.hasMap.2.pow n).ne_zero
  refine IsAlgebraic.of_mul (y := aeval P.x P.g ^ n) (mem_nonZeroDivisors_of_ne_zero hu) ((hp _).pow n) ?_
  rw [mul_comm, h]
  exact hp p

theorem approx_std {F K : Type} [Field F] [NormedField K] [Algebra F K] (hH : HenselN K) {π : K} (h0 : π ≠ 0)
    (h1 : ‖π‖ < 1) (hD : Dense {x : K | IsAlgebraic F x}) {n : ℕ} {B : Type} [CommRing B] [IsDomain B] [Algebra F B]
    [Algebra (MvPolynomial (Fin n) F) B] [IsScalarTower F (MvPolynomial (Fin n) F) B]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) F) B] (ψ : B →ₐ[F] K) (S : Finset B) (ε : ℝ) (hε : 0 < ε) (g : B)
    (hg : g ≠ 0) : ∃ ψ' : B →ₐ[F] K, (∀ x, IsAlgebraic F (ψ' x)) ∧ (∀ s ∈ S, ‖ψ' s - ψ s‖ < ε) ∧ ψ' g ≠ 0 := by
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := MvPolynomial (Fin n) F) (S := B)
  obtain ⟨c, hc0, hc⟩ := (isAlgebraic_std P g).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hg)
  let ev : (Fin n → K) → (MvPolynomial (Fin n) F →+* K) := fun b => (MvPolynomial.aeval b : _ →ₐ[F] K)
  have hev : ∀ r, Continuous fun b => ev b r := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => simpa [ev] using continuous_const
    | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
    | mul_X p i hp =>
      have : Continuous fun b : Fin n → K => ev b p * b i := hp.mul (continuous_apply i)
      simpa [ev] using this
  let a : Fin n → K := fun i => ψ (algebraMap (MvPolynomial (Fin n) F) B (MvPolynomial.X i))
  have ha : ev a = (ψ : B →+* K).comp (algebraMap (MvPolynomial (Fin n) F) B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => by simp [ev, a])
    have : algebraMap (MvPolynomial (Fin n) F) B (MvPolynomial.C r) = algebraMap F B r :=
      (IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F) B r).symm
    simp [ev, this]
  have hψ : ∀ p : (MvPolynomial (Fin n) F)[X], p.eval₂ (ev a) (ψ P.x) = ψ (aeval P.x p) := by
    intro p
    rw [ha, aeval_def]
    exact (hom_eval₂ p _ (ψ : B →+* K) P.x).symm
  have hc2 : ∀ p : (MvPolynomial (Fin n) F)[X],
      Continuous fun t : (Fin n → K) × K => p.eval₂ (ev t.1) t.2 := by
    intro p
    simp only [eval₂_eq_sum, Polynomial.sum]
    exact continuous_finsetSum _ fun k _ => ((hev _).comp continuous_fst).mul (continuous_snd.pow _)
  choose p m hpm using P.exists_mul_aeval_x_g_pow_eq_aeval_x
  have hg0 : P.g.eval₂ (ev a) (ψ P.x) ≠ 0 := by
    rw [hψ]; exact (P.hasMap.2.map ψ).ne_zero
  have E1 : ∀ᶠ t : (Fin n → K) × K in 𝓝 (a, ψ P.x), P.g.eval₂ (ev t.1) t.2 ≠ 0 :=
    (hc2 P.g).continuousAt.eventually_ne hg0
  have E2 : ∀ᶠ t : (Fin n → K) × K in 𝓝 (a, ψ P.x), ∀ s ∈ S,
      ‖(p s).eval₂ (ev t.1) t.2 / P.g.eval₂ (ev t.1) t.2 ^ m s - ψ s‖ < ε := by
    rw [eventually_all_finset]
    intro s _
    have hca : ContinuousAt (fun t : (Fin n → K) × K =>
        ‖(p s).eval₂ (ev t.1) t.2 / P.g.eval₂ (ev t.1) t.2 ^ m s - ψ s‖) (a, ψ P.x) := by
      have h3 : ContinuousAt (fun t : (Fin n → K) × K => P.g.eval₂ (ev t.1) t.2 ^ m s) (a, ψ P.x) :=
        ((hc2 P.g).pow (m s)).continuousAt
      have h4 := (hc2 (p s)).continuousAt.div h3 (pow_ne_zero (m s) hg0)
      exact (h4.sub continuousAt_const).norm
    refine hca.eventually (gt_mem_nhds ?_)
    show ‖(p s).eval₂ (ev a) (ψ P.x) / P.g.eval₂ (ev a) (ψ P.x) ^ m s - ψ s‖ < ε
    rw [hψ (p s), ← hpm, map_mul, map_pow, ← hψ, mul_div_cancel_right₀ _ (pow_ne_zero _ hg0), sub_self, norm_zero]
    exact hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (E1.and E2)
  have E3 := eventually_root hH h0 h1 ev hev P.f a (ψ P.x) (by rw [hψ, P.hasMap.1, map_zero])
    (by rw [hψ]; exact (P.hasMap.isUnit_derivative_f.map ψ).ne_zero) r hr
  obtain ⟨r', hr', hball'⟩ := Metric.eventually_nhds_iff.1 E3
  have hb : ∃ b : Fin n → K, (∀ i, b i ∈ {x : K | IsAlgebraic F x} ∩ Metric.ball (a i) (min r r')) ∧ ev b c ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hc0
    apply MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
    refine MvPolynomial.funext_set (fun i => {x : K | IsAlgebraic F x} ∩ Metric.ball (a i) (min r r'))
      (fun i => infinite_inter h0 h1 hD _ _ (lt_min hr hr')) fun b hb => ?_
    rw [map_zero, map_zero, MvPolynomial.eval_map]
    exact hne b fun i => hb i trivial
  obtain ⟨b, hb, hbc⟩ := hb
  have hba : dist b a < min r r' := (dist_pi_lt_iff (lt_min hr hr')).2 fun i => (hb i).2
  obtain ⟨x, hx, hfx⟩ := hball' (hba.trans_le (min_le_right _ _))
  obtain ⟨e1, e2⟩ := hball (y := (b, x)) (by
    rw [Prod.dist_eq]
    exact max_lt (hba.trans_le (min_le_left _ _)) (by rwa [dist_eq_norm]))
  let L := algebraicClosure F K
  let φ : MvPolynomial (Fin n) F →ₐ[F] L := MvPolynomial.aeval fun i => ⟨b i, mem_algebraicClosure_iff.2 (hb i).1⟩
  have hφ : (algebraMap L K).comp (φ : _ →+* L) = ev b := by
    refine MvPolynomial.ringHom_ext (fun r => by simp [ev, φ]) (fun i => by simp [ev, φ])
  have hxL : x ∈ L := by
    have : IsIntegral L x := ⟨P.f.map (φ : _ →+* L), P.monic_f.map _, by rw [eval₂_map, hφ, hfx]⟩
    exact mem_algebraicClosure_iff.2 (this.isAlgebraic.restrictScalars F)
  letI : Algebra (MvPolynomial (Fin n) F) L := (φ : _ →+* L).toAlgebra
  haveI : IsScalarTower F (MvPolynomial (Fin n) F) L := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hval : ∀ q : (MvPolynomial (Fin n) F)[X], algebraMap L K (aeval (⟨x, hxL⟩ : L) q) = q.eval₂ (ev b) x := by
    intro q
    rw [aeval_def, hom_eval₂, ← hφ]
    rfl
  have hm : P.HasMap (⟨x, hxL⟩ : L) := by
    refine ⟨(algebraMap L K).injective (by rw [hval, hfx, map_zero]), Ne.isUnit fun h => e1 ?_⟩
    rw [← hval, h, map_zero]
  let χ : B →ₐ[MvPolynomial (Fin n) F] L := (P.lift _ hm).comp P.equivRing.toAlgHom
  have hχ : χ P.x = ⟨x, hxL⟩ := by simp [χ]
  have hχ' : ∀ q : (MvPolynomial (Fin n) F)[X], algebraMap L K (χ (aeval P.x q)) = q.eval₂ (ev b) x := by
    intro q
    rw [← aeval_algHom_apply, hχ, hval]
  refine ⟨L.val.comp (χ.restrictScalars F), fun y => mem_algebraicClosure_iff.1 (χ y).2, fun s hs => ?_, ?_⟩
  · have h2 := e2 s hs
    have h3 := hχ' (p s)
    rw [← hpm, map_mul, map_pow, map_mul, map_pow, hχ'] at h3
    dsimp only at h2 e1
    rw [← h3, mul_div_cancel_right₀ _ (pow_ne_zero _ e1)] at h2
    exact h2
  · intro h
    obtain ⟨u, hu⟩ := hc
    apply hbc
    have h2 : ev b c = algebraMap L K (χ (algebraMap _ B c)) := by
      rw [χ.commutes, ← hφ]; rfl
    have h3 : algebraMap L K (χ g) = 0 := h
    rw [h2, hu, map_mul, map_mul, h3, zero_mul]

theorem approx_smooth {F K : Type} [Field F] [NormedField K] [Algebra F K] (hH : HenselN K) {π : K} (h0 : π ≠ 0)
    (h1 : ‖π‖ < 1) (hD : Dense {x : K | IsAlgebraic F x}) {R : Type} [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.Smooth F R] (ψ : R →ₐ[F] K) (S : Finset R) (ε : ℝ) (hε : 0 < ε) (g : R)
    (hg : g ≠ 0) : ∃ ψ' : R →ₐ[F] K, (∀ x, IsAlgebraic F (ψ' x)) ∧ (∀ s ∈ S, ‖ψ' s - ψ s‖ < ε) ∧ ψ' g ≠ 0 := by
  classical
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  haveI : Algebra.IsSmoothAt F (RingHom.ker ψ) := by
    unfold Algebra.IsSmoothAt
    infer_instance
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := F) (p := RingHom.ker ψ)
  have hψf : ψ f ≠ 0 := hf
  have hf0 : f ≠ 0 := fun h => hψf (by rw [h, map_zero])
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  let ψ₁ : Localization.Away f →ₐ[F] K := IsLocalization.Away.liftAlgHom f (f := ψ) hψf.isUnit
  have hψ₁ : ∀ s, ψ₁ (algebraMap R _ s) = ψ s := fun s => by simp [ψ₁]
  obtain ⟨ψ', ha, hs, hg'⟩ := approx_std (n := n) hH h0 h1 hD ψ₁ (S.image (algebraMap R _)) ε hε (algebraMap R _ g)
    ((map_ne_zero_iff _ hinj).2 hg)
  refine ⟨ψ'.comp (IsScalarTower.toAlgHom F R _), fun x => ha _, fun s h => ?_, hg'⟩
  rw [← hψ₁]
  exact hs _ (Finset.mem_image_of_mem _ h)

end ModelDimension.Alg
end

