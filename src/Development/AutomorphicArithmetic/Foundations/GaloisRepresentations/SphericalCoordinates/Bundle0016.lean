module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRhoSig
section
noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

private theorem root_cases (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm < 0) (r z : ℂ) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (starRingEnd ℂ) r ≠ r ∧ (z = r ∨ z = (starRingEnd ℂ) r) := by
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h1 : (t : ℂ) ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by simpa using hr
    have h2 : t ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by exact_mod_cast h1
    have h3 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * t - tr)]
  refine ⟨hne, ?_⟩
  have hr' : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hs : r + (starRingEnd ℂ) r = tr := by
    have h1 : (r - (starRingEnd ℂ) r) * (r + (starRingEnd ℂ) r - tr) = 0 := by
      linear_combination hr - hr'
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact sub_eq_zero.mp h
  have h2 : (z - r) * (z - (starRingEnd ℂ) r) = 0 := by
    rw [← hs] at hz hr
    linear_combination hz - hr
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem sum_mult {F : Type} [Field F] [NumberField F] (n : ℕ) (hn : 1 ≤ n) (t₀ : F →+* ℂ)
    (ε : (F →+* ℂ) → ℕ) (cx : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ)
    (eps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) :
    2 * ∑ τ : F →+* ℂ, typeMult n t₀ ε τ = n * Module.finrank ℚ F := by
  have hinv : ∀ σ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    ComplexEmbedding.involutive_conjugate F
  have hc0 : ComplexEmbedding.conjugate t₀ ≠ t₀ := cx t₀
  have hw : ∀ τ, typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = n := by
    intro τ
    by_cases h1 : τ = t₀
    · subst h1
      simp only [typeMult, ite_true, ite_eq_right hc0]
      omega
    by_cases h2 : τ = ComplexEmbedding.conjugate t₀
    · subst h2
      simp only [typeMult, hinv, ite_eq_right hc0, ite_true]
      omega
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h2 (by rw [← h, hinv])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := fun h =>
      h1 ((ComplexEmbedding.involutive_conjugate F).injective h)
    simp only [typeMult, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    rw [← Nat.mul_add, eps τ h1 h2, Nat.mul_one]
  have hs : ∑ τ : F →+* ℂ, typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = ∑ τ : F →+* ℂ, typeMult n t₀ ε τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate F)) (typeMult n t₀ ε)
  have h2 : ∑ τ : F →+* ℂ, (typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ)) =
      n * Module.finrank ℚ F := by
    simp only [hw, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Embeddings.card F ℂ, mul_comm]
  rw [Finset.sum_add_distrib, hs] at h2
  omega

theorem rhoSig_of : RhoSig := by
  intro p _ D ha hm t₀ ht
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  have hinj : Function.Injective (algebraMap (𝓞 D.F) D.O) := a_inj
  have honto : Function.Surjective (algebraMap (𝓞 D.F) D.O) :=
    a_onto hcomm fun x => D.central x (hcomm x)
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) ⟨hinj, honto⟩
  have he : ∀ c : 𝓞 D.F, e.symm (algebraMap (𝓞 D.F) D.O c) = c := fun c => e.symm_apply_apply c
  have h0 : 0 < D.a := by omega
  have ht0 : t₀ (D.ω : D.F) = D.ρc := by
    rw [← ht ⟨0, h0⟩]
    exact D.tau_ω _
  have hroot : ∀ τ : D.F →+* ℂ, (τ (D.ω : D.F)) ^ 2 - D.tr * τ (D.ω : D.F) + D.nm = 0 := by
    intro τ
    have h1 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.tr_eq
    have h2 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.nm_eq
    simp only [map_add (f := _), map_mul, map_intCast] at h1 h2
    rw [← h1, ← h2]
    ring
  have hcx : ∀ τ : D.F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := by
    intro τ h
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    exact (InfinitePlace.isComplex_mk_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)
  have heps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ →
      epsD D τ + epsD D (ComplexEmbedding.conjugate τ) = 1 := by
    intro τ _ _
    obtain ⟨hne, hcase⟩ := root_cases D.tr D.nm D.disc_neg D.ρc (τ (D.ω : D.F)) D.ρc_root (hroot τ)
    unfold epsD
    rw [ComplexEmbedding.conjugate_coe_eq]
    rcases hcase with h | h
    · rw [h, ite_eq_left rfl, ite_eq_right hne]
    · rw [h, ite_eq_right hne, Complex.conj_conj, ite_eq_left rfl]
  have hsum : ∑ τ : D.F →+* ℂ, typeMult D.n t₀ (epsD D) τ = D.g := by
    have h2 := sum_mult D.n D.n_pos t₀ (epsD D) hcx heps
    unfold Datum.g
    rw [hm, one_mul, ← h2]
    simp
  obtain ⟨E⟩ : Nonempty (Fin D.g ≃ Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) :=
    ⟨(Fintype.equivFinOfCardEq (by simp [hsum])).symm⟩
  let ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ :=
    (Matrix.diagonalRingHom (Fin D.g) ℂ).comp
      ((RingHom.pi fun i => ((E i).1).comp (algebraMap (𝓞 D.F) D.F)).comp (e.symm : D.O →+* 𝓞 D.F))
  have hρ : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Matrix.diagonal fun i => (E i).1 (c : D.F) := by
    intro c
    simp only [ρ, RingHom.comp_apply, RingHom.coe_coe, he]
    rfl
  refine ⟨ρ, ⟨honto, fun c => ⟨D.bar c, ?_, fun τ => ?_⟩, hcx, D.n_pos, heps, fun c => ?_⟩⟩
  · show (D.star (algebraMap (𝓞 D.F) D.O c)).unop = _
    rw [D.star_F]
    rfl
  · rw [D.bar_eq, IsCMField.complexEmbedding_complexConj]
  · rw [hρ, Matrix.trace_diagonal,
      Equiv.sum_comp E (fun s : (Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) => s.1 (c : D.F)),
      Fintype.sum_sigma]
    simp

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSumPts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem finsum_sigma {I : Type} {κ : I → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (Function.support f).Finite) : ∑ᶠ s, f s = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  have hfi : ∀ i, (Function.support (fun k : κ i => f ⟨i, k⟩)).Finite := fun i =>
    hf.preimage (fun a _ b _ h => sigma_mk_injective h)
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp)]
  have hg : Function.support (fun i => ∑ᶠ k, f ⟨i, k⟩) ⊆ ↑(hf.toFinset.image Sigma.fst) := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, f ⟨i, k⟩ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi (finsum_eq_zero_of_forall_eq_zero h)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨i, k⟩, by simpa using hk, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hg]
  have hk : ∀ i, ∑ᶠ k, f ⟨i, k⟩ = ∑ k ∈ (hfi i).toFinset, f ⟨i, k⟩ := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hk]
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨i, k⟩
  simp only [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_sigma, Finset.mem_image]
  constructor
  · intro h
    exact ⟨⟨⟨i, k⟩, h, rfl⟩, h⟩
  · rintro ⟨-, h⟩
    exact h

private noncomputable def tm {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β) : ℂ :=
  ((Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if GlobalTheory.LKCx.FixL G v B.β y b.2.1 then
      (S.indicator (1 : G.GAf → ℂ)) (b.1.1⁻¹ * B.toAf y * b.1.1) *
        (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator (1 : Gr G 1 → ℂ))
          (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0

private theorem tm_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β)
    (hK : ∀ y, Sees B (K : Set G.GAf) b y → y = 1) :
    tm v c K S B b = ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if Sees B S b y then
      c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0 := by
  have hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun s t => ?_⟩, ⟨LKCx.Stab.one G v B.β _ _ _ K _ b⟩⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := s
    obtain ⟨y', hy1', hy2', hy3'⟩ := t
    have e1 : y = 1 := hK y ⟨hy3, hy1, hy2⟩
    have e2 : y' = 1 := hK y' ⟨hy3', hy1', hy2'⟩
    subst e1
    subst e2
    rfl
  unfold tm
  rw [hcard, Nat.cast_one, inv_one, _root_.one_mul]
  apply finsum_congr
  intro y
  unfold Sees
  by_cases hF : GlobalTheory.LKCx.FixL G v B.β y b.2.1
  · by_cases h1 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S
    · by_cases h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · simp [hF, h1, h2]
      · simp [hF, h1, h2]
    · simp [hF, h1]
  · simp [hF]

theorem UpperTheory.Gal.W2.sumPts_of :
    UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.SumPts := by
  intro hE p _ G v c K S hconj hK hS T Φ Fb w hx
  classical
  let g : LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw) → ℂ := fun s => tm v c K S (Quot.out s.1) (Quot.out s.2)
  have key : ∀ x : T, g (Φ x) = if x ∈ Fb then w x else 0 := by
    intro x
    obtain ⟨q, a, hΦ, hFb, hw⟩ := hx x
    obtain ⟨pt, hpt⟩ : ∃ pt : LKCx.Form.Pts v (Quot.out q) K (KHT p G.m G.n 1 G.Fw), Quot.mk _ a = pt := ⟨_, rfl⟩
    rw [hpt] at hΦ
    have hmk : Quot.mk _ a = Quot.mk _ (Quot.out pt) := hpt.trans (Quot.out_eq pt).symm
    obtain ⟨E, -, hE1⟩ := hE p G v c (Quot.out q) K S hconj a (Quot.out pt) hmk
    obtain ⟨E', -, hE2⟩ := hE p G v c (Quot.out q) K S hconj (Quot.out pt) a hmk.symm
    have hg : g (Φ x) = g ⟨q, pt⟩ := by rw [hΦ]
    rw [hg]
    show tm v c K S (Quot.out q) (Quot.out pt) = _
    rw [tm_eq v c K S _ _ (hK _ _)]
    by_cases hxF : x ∈ Fb
    · rw [if_pos hxF]
      obtain ⟨y, hy⟩ := hFb.1 hxF
      have hy' := ((hE1 y).1).1 hy
      rw [finsum_eq_single _ (E y)]
      · rw [if_pos hy', ((hE1 y).2 hy).1, ((hE1 y).2 hy).2, hw y hy]
      · intro y' hne
        rw [if_neg]
        intro hs
        exact hne (hS _ _ _ _ hs hy')
    · rw [if_neg hxF]
      apply finsum_eq_zero_of_forall_eq_zero
      intro y'
      rw [if_neg]
      intro hs
      exact hxF (hFb.2 ⟨E' y', ((hE2 y').1).1 hs⟩)
  have hsupp : Function.support (fun x => g (Φ x)) ⊆ ↑Fb := by
    intro x hx0
    by_contra hn
    exact hx0 (by show g (Φ x) = 0; rw [key x, if_neg (show x ∉ Fb from hn)])
  have hfin : (Function.support g).Finite := by
    apply ((Fb.finite_toSet).image Φ).subset
    intro s hs
    refine ⟨Φ.symm s, hsupp ?_, Φ.apply_symm_apply s⟩
    show g (Φ (Φ.symm s)) ≠ 0
    rw [Φ.apply_symm_apply]
    exact hs
  have h1 : RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw)
      ((↑(KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) = ∑ᶠ s, g s := by
    rw [finsum_sigma g hfin]
    rfl
  rw [h1, ← finsum_comp_equiv Φ, finsum_eq_sum_of_support_subset (fun x => g (Φ x)) hsupp]
  exact Finset.sum_congr rfl (fun x hx => by rw [key, if_pos hx])
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PUnifG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem u_eq_of_marked {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hw : IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w) (hh : ∀ u, P (w u) = h (P' u)) :
    U.u i' P' = U.u i P := by
  obtain rfl := U.distinct i' i w hw
  exact (U.fibre i' P' P hP' hP).2 ⟨w, h, hw, hh⟩

private theorem marked_of_u_eq {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (e : U.u i' P' = U.u i P) :
    ∃ (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w ∧ ∀ u, P (w u) = h (P' u) := by
  obtain rfl := U.disj i' i P' P hP' hP e
  exact (U.fibre i' P' P hP' hP).1 e

private theorem isPeriod_comp {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {D' D'' : PLat O bar} {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ρ P) (w : D''.La ≃ₗ[O] D'.La)
    (hw : IsIsom D'' D' w) : IsPeriod D'' ρ (P.comp w.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hs : Set.range (P.comp w.toLinearMap.toAddMonoidHom) = Set.range P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨w x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, by simp⟩
  have hr : (P.comp w.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    exact Set.ext_iff.1 hs z
  refine ⟨fun a x => ?_, h2.comp w.injective, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · show P (w (a • x)) = _
    rw [map_smul, h1]
    rfl
  · rw [hr]
    exact h3
  · rw [hs]
    exact h4
  · show (hermForm Hm (P (w x)) (P (w y))).im = _
    rw [hEF, hw x y]

private theorem marked_symm {O : Type} [Ring O] {bar : O → O} {Λ : Type} {N : ℕ} {D₁ D₂ : PLat O bar}
    {t₁ : Λ → D₁.La} {t₂ : Λ → D₂.La} {w : D₁.La ≃ₗ[O] D₂.La} (h : IsMarkedIsom N D₁ D₂ t₁ t₂ w) :
    IsMarkedIsom N D₂ D₁ t₂ t₁ w.symm := by
  refine ⟨fun x y => ?_, fun a => ?_⟩
  · have := h.1 (w.symm x) (w.symm y)
    simpa using this.symm
  · obtain ⟨e, he⟩ := h.2 a
    refine ⟨-(w.symm e), ?_⟩
    have h2 := congrArg w.symm he
    rw [LinearEquiv.symm_apply_apply, map_add (f := _), map_nsmul] at h2
    rw [h2, smul_neg]
    abel

theorem UpperTheory.Gal.W2.unifG_of :
    UpperTheory.Gal.W2.CoordEx → UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.CoordIso → UpperTheory.Gal.W2.CoordMove → UpperTheory.Gal.W2.UnifG := by
  intro hEx hOcc hIso hMove p _ D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp F U
  have hch : ∀ x : CxPts F.s (RingHom.id ℂ), ∃ (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ))
      (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β) (j : (U.Di i).La →+ VQ D),
      IsPeriod (U.Di i) ρ P ∧ x.1 = U.u i P ∧ IsCoord L (Quot.out q) (PD _) (RD _) N (U.Di i) (U.t i) P j a := by
    intro x
    obtain ⟨i, P, hP, hu⟩ := U.onto x.1 x.2
    obtain ⟨q, a, j, hc⟩ := hEx p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (U.Di i) (U.t i) P (U.mem i) hP
    exact ⟨i, P, q, a, j, hP, hu.symm, hc⟩
  choose i P q a j hP hu hc using hch
  let Φ₀ : CxPts F.s (RingHom.id ℂ) → GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw) :=
    fun x => ⟨q x, Quot.mk _ (a x)⟩
  have hinj : Function.Injective Φ₀ := by
    intro x x' e
    obtain ⟨w, h, hw, hh⟩ := (hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di (i x)) (U.t (i x)) (P x)
      (U.Di (i x')) (U.t (i x')) (P x') (U.mem _) (U.mem _) (q x) (q x') (a x) (a x') (j x) (j x')
      (hc x) (hc x')).2 e
    apply Subtype.ext
    rw [hu x, hu x']
    exact (u_eq_of_marked U _ _ _ _ (hP x) (hP x') w h hw hh).symm
  have hsurj : Function.Surjective Φ₀ := by
    rintro ⟨q₀, c⟩
    obtain ⟨a₀, rfl⟩ := Quot.exists_rep c
    obtain ⟨D', t, Pd, jd, hCl, hPd, hcd⟩ :=
      hOcc p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (Quot.out q₀) a₀
    obtain ⟨i₀, w, hw⟩ := U.all D' t hCl ⟨Pd, hPd⟩
    have hws := marked_symm hw
    let P₀ := Pd.comp w.symm.toLinearMap.toAddMonoidHom
    have hP₀ : IsPeriod (U.Di i₀) ρ P₀ := isPeriod_comp hPd w.symm hws.1
    let j₀ := jd.comp w.symm.toLinearMap.toAddMonoidHom
    have hc₀ : IsCoord L (Quot.out q₀) (PD _) (RD _) N (U.Di i₀) (U.t i₀) P₀ j₀ a₀ :=
      hMove p D G L v t₀ ρ (Quot.out q₀) (PD _) (RD _) N D' t Pd (U.Di i₀) (U.t i₀) P₀ w.symm hws
        (fun _ => rfl) jd j₀ (fun _ => rfl) a₀ hcd
    let x : CxPts F.s (RingHom.id ℂ) := ⟨U.u i₀ P₀, (U.unif i₀ P₀ hP₀).1⟩
    refine ⟨x, ?_⟩
    obtain ⟨w', h', hw', hh'⟩ := marked_of_u_eq U i₀ (i x) P₀ (P x) hP₀ (hP x) (hu x).symm
    exact ((hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di i₀) (U.t i₀) P₀ (U.Di (i x)) (U.t (i x)) (P x)
      (U.mem _) (U.mem _) q₀ (q x) a₀ (a x) j₀ (j x) hc₀ (hc x)).1 ⟨w', h', hw', hh'⟩).symm
  exact ⟨Equiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, fun x => ⟨q x, a x, i x, P x, j x, rfl, hP x, hu x, hc x⟩⟩
end

