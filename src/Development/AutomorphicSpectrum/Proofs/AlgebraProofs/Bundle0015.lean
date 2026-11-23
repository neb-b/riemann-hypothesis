module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjective
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.Induced

theorem isHopfOrder_indOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  obtain ⟨hfin, hproj, hfull, hcomul, hinv⟩ := hA
  unfold prodSpan at hcomul
  have hmemInd : ∀ f : T → R, f ∈ indOrder ι A ↔ ∀ t : T, (fun h => f (t * ι h)) ∈ A := by
    intro f
    unfold indOrder
    exact Iff.rfl
  have hTr : ∀ g ∈ A, ∀ h0 : H, (fun h => g (h * h0)) ∈ A := by
    intro g hg h0
    obtain ⟨E, hE⟩ : ∃ E : (H × H → R) →ₗ[R] (H → R), ∀ φ h, E φ h = φ (h, h0) :=
      ⟨{ toFun := fun φ h => φ (h, h0)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Subalgebra.toSubmodule A).comap E := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have hEab : E (fun z : H × H => a z.1 * b z.2) = b h0 • a := by
        funext h
        rw [hE]
        simp [mul_comm]
      show E _ ∈ Subalgebra.toSubmodule A
      rw [hEab]
      exact A.smul_mem ha _
    have h1 := hle (hcomul g hg)
    have h2 : E (fun z : H × H => g (z.1 * z.2)) = fun h => g (h * h0) := funext fun h => hE _ h
    rw [Submodule.mem_comap, h2] at h1
    simpa using h1
  have hs : Function.Surjective (QuotientGroup.mk : T → T ⧸ ι.range) := QuotientGroup.mk_surjective
  have hQfin : Finite (T ⧸ ι.range) := Finite.of_surjective _ hs
  let _ : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ : ∃ σ : T ⧸ ι.range → T, ∀ c, (σ c : T ⧸ ι.range) = c :=
    ⟨Function.surjInv hs, Function.surjInv_eq hs⟩
  have hmem : ∀ t : T, (σ (t : T ⧸ ι.range))⁻¹ * t ∈ ι.range := fun t => QuotientGroup.eq.mp (hσ _)
  choose δ hδ using fun t : T => MonoidHom.mem_range.mp (hmem t)
  have hdec : ∀ t : T, σ (t : T ⧸ ι.range) * ι (δ t) = t := fun t => by
    rw [hδ, mul_inv_cancel_left]
  have hmk : ∀ (t : T) (h : H), ((t * ι h : T) : T ⧸ ι.range) = (t : T ⧸ ι.range) := by
    intro t h
    apply QuotientGroup.eq.mpr
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have hδmul : ∀ (t : T) (h : H), δ (t * ι h) = δ t * h := by
    intro t h
    apply hι
    rw [hδ, map_mul, hδ, hmk, mul_assoc]
  obtain ⟨e, he⟩ : ∃ e : T ⧸ ι.range → T → R,
      ∀ c t, e c t = if (t : T ⧸ ι.range) = c then 1 else 0 :=
    ⟨fun c t => if (t : T ⧸ ι.range) = c then 1 else 0, fun _ _ => rfl⟩
  have he_self : ∀ t : T, e (t : T ⧸ ι.range) t = 1 := fun t => by rw [he, if_pos rfl]
  have he_ne : ∀ (c : T ⧸ ι.range) (t : T), c ≠ (t : T ⧸ ι.range) → e c t = 0 :=
    fun c t hc => by rw [he, if_neg (fun h => hc h.symm)]
  have he_mk : ∀ (c : T ⧸ ι.range) (t : T) (h : H), e c (t * ι h) = e c t :=
    fun c t h => by rw [he, he, hmk]
  let i : (indOrder ι A) →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (σ c * ι h), (hmemInd _).mp f.2 (σ c)⟩
      map_add' := fun f g => by
        funext c
        apply Subtype.ext
        rfl
      map_smul' := fun r f => by
        funext c
        apply Subtype.ext
        rfl }
  have hp : ∀ a : T ⧸ ι.range → A,
      (fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t)) ∈ indOrder ι A := by
    intro a
    rw [hmemInd]
    intro t
    have heq : (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) =
        fun h => ((a (t : T ⧸ ι.range) : A) : H → R) (h * δ t) := by
      funext h
      rw [hmk, hδmul, mul_comm (δ t) h]
    show (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) ∈ A
    rw [heq]
    exact hTr _ (a _).2 _
  let p : (T ⧸ ι.range → A) →ₗ[R] (indOrder ι A) :=
    { toFun := fun a => ⟨fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t), hp a⟩
      map_add' := fun a b => by
        apply Subtype.ext
        rfl
      map_smul' := fun r a => by
        apply Subtype.ext
        rfl }
  have hpi' : ∀ f, p (i f) = f := by
    intro f
    apply Subtype.ext
    funext t
    show (f : T → R) (σ (t : T ⧸ ι.range) * ι (δ t)) = (f : T → R) t
    rw [hdec]
  have hpi : p.comp i = LinearMap.id := LinearMap.ext hpi'
  have := hfin
  have := hproj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective p (fun f => ⟨i f, hpi' f⟩)
  · have hQM : Module.Projective R (T ⧸ ι.range → A) := by
      obtain ⟨M, _, _, _, i0, s0, hs0⟩ := Module.Projective.iff_split.mp hproj
      refine Module.Projective.of_split
        ({ toFun := fun g c => i0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → A) →ₗ[R] (T ⧸ ι.range → M))
        ({ toFun := fun g c => s0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → M) →ₗ[R] (T ⧸ ι.range → A)) ?_
      apply LinearMap.ext
      intro g
      funext c
      show s0 (i0 (g c)) = g c
      exact LinearMap.congr_fun hs0 (g c)
    exact Module.Projective.of_split i p hpi
  · obtain ⟨d, hd0, hd⟩ := hfull
    exact ⟨d, hd0, fun f => (hmemInd _).mpr fun t => hd (fun h => f (t * ι h))⟩
  · intro f hf
    unfold prodSpan
    have hind : ∀ (c : T ⧸ ι.range), ∀ a ∈ A, (fun t => e c t * a (δ t)) ∈ indOrder ι A := by
      intro c a ha
      rw [hmemInd]
      intro t
      have heq : (fun h => e c (t * ι h) * a (δ (t * ι h))) = fun h => e c t * a (h * δ t) := by
        funext h
        rw [he_mk, hδmul, mul_comm (δ t) h]
      show (fun h => e c (t * ι h) * a (δ (t * ι h))) ∈ A
      rw [heq]
      exact A.smul_mem (hTr a ha (δ t)) (e c t)
    obtain ⟨L, hL⟩ : ∃ L : T ⧸ ι.range → T ⧸ ι.range → (H × H → R) →ₗ[R] (T × T → R),
        ∀ c1 c2 φ z, L c1 c2 φ z = e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2) :=
      ⟨fun c1 c2 =>
        { toFun := fun φ z => e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2)
          map_add' := fun φ ψ => by
            funext z
            simp only [Pi.add_apply]
            ring
          map_smul' := fun r φ => by
            funext z
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            ring },
        fun _ _ _ _ => rfl⟩
    have hsum : (fun z : T × T => f (z.1 * z.2)) =
        ∑ c1 : T ⧸ ι.range, ∑ c2 : T ⧸ ι.range,
          L c1 c2 (fun z : H × H => f (σ c1 * σ c2 * ι (z.1 * z.2))) := by
      funext z
      rw [Finset.sum_apply, Fintype.sum_eq_single (z.1 : T ⧸ ι.range)]
      · rw [Finset.sum_apply, Fintype.sum_eq_single (z.2 : T ⧸ ι.range)]
        · rw [hL]
          try dsimp only
          rw [he_self, he_self, one_mul, one_mul, map_mul, mul_mul_mul_comm, hdec, hdec]
        · intro c2 hc2
          rw [hL, he_ne _ _ hc2, mul_zero, zero_mul]
      · intro c1 hc1
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c2 _
        rw [hL, he_ne _ _ hc1, zero_mul, zero_mul]
    rw [hsum]
    refine sum_mem fun c1 _ => sum_mem fun c2 _ => ?_
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Submodule.span R {g | ∃ a ∈ indOrder ι A, ∃ b ∈ indOrder ι A,
          g = fun z : T × T => a z.1 * b z.2}).comap (L c1 c2) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      show L c1 c2 _ ∈ Submodule.span R _
      apply Submodule.subset_span
      refine ⟨_, hind c1 a ha, _, hind c2 b hb, ?_⟩
      funext z
      rw [hL]
      dsimp only
      ring
    exact hle (hcomul _ ((hmemInd f).mp hf (σ c1 * σ c2)))
  · intro f hf
    rw [hmemInd] at hf ⊢
    intro t
    have heq : (fun h => f ((t * ι h)⁻¹)) = fun h => f (t⁻¹ * ι h⁻¹) := by
      funext h
      rw [map_inv, mul_inv]
    show (fun h => f ((t * ι h)⁻¹)) ∈ A
    rw [heq]
    exact hinv _ (hf t⁻¹)

end GlobalTheory.CompanionTheory.Ar.BT.Induced
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralClosurePlaceRingsData
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_pow_mem_of_integrally_closed {Ω : Type} [Field Ω] (R : Subring Ω)
    (hR : ∀ z : Ω, IsIntegral R z → z ∈ R) {z : Ω} {m : ℕ} (hm : 0 < m) (h : z ^ m ∈ R) :
    z ∈ R := by
  refine hR z ⟨Polynomial.X ^ m - Polynomial.C ⟨z ^ m, h⟩, Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  exact sub_eq_zero.2 rfl

theorem valuation_pow_zpow_eq_of_mul_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {π α : F} {n k : ℤ} {m M : ℕ} (hπ : v.valuation F π = WithZero.exp (-1 : ℤ))
    (hα : v.valuation F α = WithZero.exp (-k)) (h : n * M = m * k) :
    v.valuation F ((π ^ n) ^ M) = v.valuation F (α ^ m) := by
  rw [map_pow, map_zpow₀, hπ, map_pow, hα, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  linear_combination -h

theorem exists_global_generator : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  intro F Ω X _ _ _ φ R s pl r hR hgen hsp
  obtain ⟨M, α, hM, hα0, hval⟩ := exists_pow_principal F r
  refine ⟨M, α, hM, hα0, hval, fun x => ?_⟩
  cases hx : pl x with
  | none =>
    obtain ⟨hφ, hs, -, hsi⟩ := hgen x hx
    have hαi : (φ α)⁻¹ ∈ R x := by
      rw [← map_inv₀]
      exact hφ _
    constructor
    · rw [div_eq_mul_inv]
      exact (R x).mul_mem ((R x).pow_mem hs M) hαi
    · rw [div_eq_mul_inv, ← inv_pow]
      exact (R x).mul_mem (hφ α) ((R x).pow_mem hsi M)
  | some v =>
    obtain ⟨hφ, m, n, π, hm, hn, hπ, hs0, h1, h2⟩ := hsp x v hx
    obtain ⟨k, hk, hαv⟩ := hval v
    have hkey : n * (M : ℤ) = m * k := by
      have : ((n * M : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
        push_cast
        rw [hn, hk]
        ring
      exact_mod_cast this
    have hv := valuation_pow_zpow_eq_of_mul_eq v hπ hαv hkey
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.coe_ne_zero hπ.symm
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    have hφα : φ α ≠ 0 := (map_ne_zero φ).2 hα0
    have hP : φ π ^ n ≠ 0 := zpow_ne_zero _ hφπ
    have hβ : v.valuation F ((π ^ n) ^ M / α ^ m) = 1 := by
      rw [map_div₀, hv, div_self]
      exact (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hα0)
    have hβ1 : φ ((π ^ n) ^ M / α ^ m) ∈ R x := hφ _ hβ.le
    have hβ2 : φ ((π ^ n) ^ M / α ^ m)⁻¹ ∈ R x := hφ _ (by rw [map_inv₀, hβ, inv_one])
    constructor
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (s x ^ M / φ α) ^ m = (s x ^ m / φ π ^ n) ^ M * φ ((π ^ n) ^ M / α ^ m) := by
        simp only [map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, div_mul_div_comm,
          mul_comm (s x ^ (m * M)), mul_div_mul_left _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h1 M) hβ1
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (φ α / s x ^ M) ^ m = (φ π ^ n / s x ^ m) ^ M * φ ((π ^ n) ^ M / α ^ m)⁻¹ := by
        simp only [map_inv₀, map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, inv_div, div_mul_div_comm,
          mul_comm ((φ π ^ n) ^ M), mul_div_mul_right _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h2 M) hβ2

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotient
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.GraphRestrict

theorem main : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) :=
  @PositivityTheory.Xgn.t_graph_restrict_bc

end GlobalTheory.CompanionTheory.Ar.GraphRestrict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeSummand
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem summand_baseChange : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) :=
  @PositivityTheory.Xgn.t_summand_bc

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeSummandCriterion
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem summand_of_locFree_quot : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) :=
  @PositivityTheory.Xgn.summand_iff_locFree_quot

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFree
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv

private theorem valuation_natCast_le_one_algebra {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))

theorem v_intCast_le_one {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℤ) : v (n : K) ≤ 1 := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact valuation_natCast_le_one_algebra v m
  | negSucc m =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_natCast_le_one_algebra v (m + 1)

theorem freeAt_of_basis_lattice (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O]
    [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V)
    (r : ℕ) (i : C.I) (hL : IsBun C L) (hk : ∀ c : k, C.v i (algebraMap k K c) ≤ 1)
    (h : ∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧
      ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧
        y = ∑ q, c q • ρ (b q.2) (x q.1)) :
    FreeAt C k (act k ρ) L r i := by
  obtain ⟨x, hli, hL'⟩ := h
  set e : Fin r × ι → V := fun q => ρ (b q.2) (x q.1) with he
  obtain ⟨b0, hb0⟩ := hL.1 i
  have hb0 : ∀ z : V, z ∈ L i ↔ ∀ q, C.v i (b0.repr z q) ≤ 1 := hb0
  have hmemL : ∀ y : V, y ∈ L i → y ∈ Submodule.span K (Set.range e) := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := (hL' y).1 hy
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [← b0.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine hmemL _ ((hb0 _).2 fun q => ?_)
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact (map_one _).le
    · rw [map_zero]
      exact zero_le_one
  let B : Module.Basis (Fin r × ι) K V := Module.Basis.mk hli hspan
  have hBe : ∀ q, B q = e q := fun q => Module.Basis.mk_apply hli hspan q
  have key : ∀ (c : Fin r × ι → K) (q : Fin r × ι), B.coord q (∑ q', c q' • e q') = c q := by
    intro c q
    have hc : ∑ q', c q' • e q' = B.equivFun.symm c := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBe]
    rw [hc, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have key' : ∀ (c : Fin r × ι → K) (q : Fin r × ι),
      B.coord q (∑ q', c q' • ρ (b q'.2) (x q'.1)) = c q := key
  have hrep : ∀ (o : O) (s' : Fin r), ρ o (x s') =
      ∑ q : Fin r × ι, (if q.1 = s' then ((b.repr o q.2 : ℤ) : K) else 0) • e q := by
    intro o s'
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s' (fun s _ hs => by simp [hs])
      (fun h => absurd (Finset.mem_univ _) h)]
    conv_lhs => rw [← b.sum_repr o]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [if_pos rfl, map_zsmul, Int.cast_smul_eq_zsmul]
    rfl
  refine ⟨x, fun l s => ∑ j, algebraMap k K (l (1 ⊗ₜ[ℤ] b j)) • B.coord (s, j), ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hL']
    refine ⟨fun q => if q.1 = s then ((b.repr 1 q.2 : ℤ) : K) else 0, fun q => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact v_intCast_le_one _ _
      · rw [map_zero]
        exact zero_le_one
    · exact (LinearMap.congr_fun (map_one ρ) (x s)).symm.trans (hrep 1 s)
  · intro l s s' a
    dsimp only
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c o =>
      rw [act_tmul, LinearMap.smul_apply, map_smul, hrep o s']
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_eq_mul]
      split_ifs with hss
      · have h1 : l (c ⊗ₜ[ℤ] o) = c * l ((1 : k) ⊗ₜ[ℤ] o) := by
          rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have h2 : l ((1 : k) ⊗ₜ[ℤ] o) = ∑ j, b.repr o j • l ((1 : k) ⊗ₜ[ℤ] b j) := by
          conv_lhs => rw [← b.sum_repr o]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [TensorProduct.tmul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_smul, map_zsmul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h1, h2, map_mul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, zsmul_eq_mul]
        ring
      · simp [hss]
    | add a a' ha ha' =>
      rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), ha, ha']
      split_ifs <;> simp [map_add (f := _)]
  · intro l s y hy
    obtain ⟨c, hc, rfl⟩ := (hL' y).1 hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, key', smul_eq_mul]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hk _) (hc _)
  · intro y
    have hy : y ∈ Submodule.span K (Set.range e) := hspan Submodule.mem_top
    refine Submodule.span_mono ?_ hy
    rintro _ ⟨q, rfl⟩
    exact ⟨(1 ⊗ₜ[ℤ] b q.2, q.1), by
      show (act k ρ) ((1 : k) ⊗ₜ[ℤ] b q.2) (x q.1) = e q
      rw [act_tmul, map_one, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowSpanLocFreeBaseChange
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem powSpan_locFree_baseChange : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (p : ℕ) (X : AddSubgroup Ω), LocFree R 1 X → LocFree R 1 (powSpan R p X) ∧ powSpan RC p (spanOver RC (algebraMap Ω C '' X)) = spanOver RC (algebraMap Ω C '' powSpan R p X) :=
  @PositivityTheory.Xgn.t_powspan

end GlobalTheory.CompanionTheory.Ar.Num
end

