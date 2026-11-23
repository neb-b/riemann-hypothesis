module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfOfIsCompl
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_of_isCompl : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T]
    (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := by
  intro p _ B _ T _ π g hC hB
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hT : (p : T) = 0 := by rw [← map_natCast g p, hB.char, map_zero]
  obtain ⟨FB, hFB⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char 1
  obtain ⟨FT, hFT⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hT 1
  have subB : ∀ x y : B, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FB x y
    simpa only [hFB, pow_one] using h
  have subT : ∀ x y : T, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FT x y
    simpa only [hFT, pow_one] using h
  have surj' : ∀ (M : ℕ) (y : T), ∃ x, g π ^ M ∣ y - g x := fun M y => by
    obtain ⟨x, hx⟩ := hC.surj M y
    exact ⟨x, Ideal.mem_span_singleton.1 hx⟩
  have inj' : ∀ (M : ℕ) (x : B), g π ^ M ∣ g x → π ^ M ∣ x := fun M x h =>
    Ideal.mem_span_singleton.1 (hC.inj M x (Ideal.mem_span_singleton.2 h))
  have root : ∀ (M : ℕ) (b : B), π ^ (p * M) ∣ b ^ p → π ^ M ∣ b := by
    rintro M b ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hB.bij.2 c
    have hd' : d ^ p = c := hd
    refine ⟨d, hB.bij.1 (show b ^ p = (π ^ M * d) ^ p from ?_)⟩
    rw [hc, mul_pow, ← pow_mul, mul_comm M p, hd']
  have haus : ∀ x : T, (∀ n : ℕ, g π ^ n ∣ x) → x = 0 := by
    intro x hx
    refine hC.compl.toIsHausdorff.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hx n
  have dvdp : ∀ (n : ℕ) (x : T), g π ^ n ∣ x → g π ^ n ∣ x ^ p := fun n x h =>
    h.trans (dvd_pow_self x hp0.ne')
  refine ⟨hT, ?_, ?_⟩
  · intro z w hzw
    have hzw' : z ^ p = w ^ p := hzw
    rw [← sub_eq_zero]
    have h0 : (z - w) ^ p = 0 := by rw [subT, hzw', sub_self]
    apply haus
    intro M
    obtain ⟨b, hb⟩ := surj' (p * M) (z - w)
    have h1 : g π ^ (p * M) ∣ g (b ^ p) := by
      have h2 : (z - w - g b) ^ p = (z - w) ^ p - g b ^ p := subT _ _
      rw [h0, zero_sub] at h2
      have h3 : g π ^ (p * M) ∣ (z - w - g b) ^ p := dvdp _ _ hb
      rw [h2, dvd_neg] at h3
      rwa [map_pow]
    have h4 : π ^ M ∣ b := root M b (inj' _ _ h1)
    have h5 : g π ^ M ∣ g b := by
      rw [← map_pow]
      exact map_dvd g h4
    have h6 : g π ^ M ∣ z - w - g b := (pow_dvd_pow _ (Nat.le_mul_of_pos_left M hp0)).trans hb
    have h7 := dvd_add h6 h5
    rwa [sub_add_cancel] at h7
  · intro y
    choose b hb using fun M : ℕ => surj' (p * M) y
    choose e he using fun M : ℕ => hB.bij.2 (b M)
    have he' : ∀ M, e M ^ p = b M := he
    have cauchy : ∀ m n : ℕ, m ≤ n → π ^ m ∣ e m - e n := by
      intro m n hmn
      apply root
      rw [subB, he', he']
      apply inj'
      have h1 : g π ^ (p * m) ∣ y - g (b n) :=
        (pow_dvd_pow _ (Nat.mul_le_mul le_rfl hmn)).trans (hb n)
      have h2 := dvd_sub h1 (hb m)
      rw [map_sub]
      convert h2 using 1
      ring
    obtain ⟨L, hL⟩ := hC.compl.toIsPrecomplete.prec (f := fun n => g (e n)) (fun {m n} hmn => by
      beta_reduce
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← map_sub, ← map_pow]
      exact map_dvd g (cauchy m n hmn))
    refine ⟨L, ?_⟩
    show L ^ p = y
    rw [← sub_eq_zero]
    apply haus
    intro n
    have hn : g π ^ n ∣ g (e n) - L := by
      have h3 := hL n
      rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h3
    have h1 : g π ^ n ∣ (g (e n) - L) ^ p := dvdp _ _ hn
    rw [subT, ← map_pow g (e n) p, he'] at h1
    have h2 : g π ^ n ∣ y - g (b n) :=
      (pow_dvd_pow _ (Nat.le_mul_of_pos_left n hp0)).trans (hb n)
    have h4 := dvd_add h1 h2
    rw [← dvd_neg]
    convert h4 using 1
    ring

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeftEqRTensor
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem prodLeft_eq_rTensor {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] (w : (B₁ × B₂) ⊗[A] K) :
    TensorProduct.prodLeft A A B₁ B₂ K w =
      ((LinearMap.fst A B₁ B₂).rTensor K w, (LinearMap.snd A B₁ B₂).rTensor K w) := by
  induction w with
  | tmul b k =>
    obtain ⟨b₁, b₂⟩ := b
    simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Prod.mk_add_mk]

theorem tensor_prod_ext {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] {w w' : (B₁ × B₂) ⊗[A] K}
    (h₁ : (LinearMap.fst A B₁ B₂).rTensor K w = (LinearMap.fst A B₁ B₂).rTensor K w')
    (h₂ : (LinearMap.snd A B₁ B₂).rTensor K w = (LinearMap.snd A B₁ B₂).rTensor K w') :
    w = w' := by
  apply (TensorProduct.prodLeft A A B₁ B₂ K).injective
  rw [prodLeft_eq_rTensor, prodLeft_eq_rTensor, h₁, h₂]

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := by
  intro p _ A _ B₁ _ _ B₂ _ _ D _ _ r ρ₁ ρ₂ hr hD hsurj hK
  let ρ : (B₁ × B₂) →ₗ[A] D :=
    ρ₁.toLinearMap ∘ₗ LinearMap.fst A B₁ B₂ - ρ₂.toLinearMap ∘ₗ LinearMap.snd A B₁ B₂
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨b₁, b₂, rfl⟩ := hsurj y
    exact ⟨(b₁, b₂), by simp [ρ]⟩
  have h1 : ρ 1 = 0 := by simp [ρ]
  refine mv_cov p A (B₁ × B₂) D r ρ hr hD hρ h1 ?_
  intro K _ _ hPK
  obtain ⟨hinj, hker⟩ := hK K hPK
  have hf : ∀ a : K, (LinearMap.fst A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₁) ⊗ₜ[A] a := by
    intro a; simp
  have hs : ∀ a : K, (LinearMap.snd A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₂) ⊗ₜ[A] a := by
    intro a; simp
  refine ⟨fun a ha => hinj a ?_ ?_, fun w hw => ?_⟩
  · rw [← hf, ha, map_zero]
  · rw [← hs, ha, map_zero]
  · have hcomm : ∀ t : (B₁ × B₂) ⊗[A] K, ρ.rTensor K t =
        Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) ((LinearMap.fst A B₁ B₂).rTensor K t) -
          Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) ((LinearMap.snd A B₁ B₂).rTensor K t) := by
      intro t
      induction t with
      | tmul b k => simp [ρ, TensorProduct.sub_tmul]
      | add x y hx hy =>
        simp only [map_add (f := _), hx, hy]
        abel
    have heq := hcomm w
    rw [hw, eq_comm, sub_eq_zero] at heq
    obtain ⟨a, ha₁, ha₂⟩ := hker _ _ heq
    exact ⟨a, tensor_prod_ext (by rw [ha₁, hf]) (by rw [ha₂, hs])⟩

end GlobalTheory.CompanionTheory.SnakeCov
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeft
section
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedRank

theorem rank_add_rank_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ} {ϖ : O}
    (hϖ : Irreducible ϖ) (d E : Matrix (Fin n) (Fin n) O) (hdE : d * E = ϖ • (1 : Matrix (Fin n) (Fin n) O))
    (hEd : E * d = ϖ • (1 : Matrix (Fin n) (Fin n) O)) :
    (d.map (IsLocalRing.residue O)).rank + (E.map (IsLocalRing.residue O)).rank = n := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  have hzero : d.map (IsLocalRing.residue O) * E.map (IsLocalRing.residue O) = 0 := by
    rw [← Matrix.map_mul, hdE]
    ext i j
    simp [hres]
  have hker : LinearMap.ker (d.map (IsLocalRing.residue O)).mulVecLin =
      LinearMap.range (E.map (IsLocalRing.residue O)).mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : (d.map (IsLocalRing.residue O)) *ᵥ x = 0 := by simpa using hx
      choose x₀ hx₀ using fun i => IsLocalRing.residue_surjective (x i)
      have hxc : (IsLocalRing.residue O) ∘ x₀ = x := funext hx₀
      have hmem : ∀ i, ∃ y : O, y * ϖ = (d *ᵥ x₀) i := by
        intro i
        have h0 : IsLocalRing.residue O ((d *ᵥ x₀) i) = 0 := by
          rw [RingHom.map_mulVec, hxc, hx']
          rfl
        rw [IsLocalRing.residue_eq_zero_iff, hmax] at h0
        exact Ideal.mem_span_singleton'.1 h0
      choose y hy using hmem
      have hdx : d *ᵥ x₀ = ϖ • y := by
        ext i
        simp [← hy i, mul_comm]
      have hEx : ϖ • x₀ = ϖ • (E *ᵥ y) := by
        have h1 : E *ᵥ (d *ᵥ x₀) = ϖ • x₀ := by
          rw [Matrix.mulVec_mulVec, hEd, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [← h1, hdx, Matrix.mulVec_smul]
      have hxE : x₀ = E *ᵥ y := smul_right_injective _ hϖ.ne_zero hEx
      refine ⟨(IsLocalRing.residue O) ∘ y, ?_⟩
      ext i
      simp only [Matrix.mulVecLin_apply]
      rw [← RingHom.map_mulVec, ← hxE]
      exact hx₀ i
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hzero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (d.map (IsLocalRing.residue O)).mulVecLin
  rw [hker] at hrn
  simpa [Matrix.rank] using hrn

theorem low_rows {R : Type} [CommRing R] {n : ℕ} (g : GL (Ix n) R) :
    lowerLeftBlock g * (g⁻¹).1.toBlocks₁₂ + dBlk g * (g⁻¹).1.toBlocks₂₂ = 1 := by
  have h : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul]; simp
  have e : fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ *
      fromBlocks (g⁻¹).1.toBlocks₁₁ (g⁻¹).1.toBlocks₁₂ (g⁻¹).1.toBlocks₂₁ (g⁻¹).1.toBlocks₂₂ = 1 := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, ← fromBlocks_one] at e
  exact (Matrix.fromBlocks_inj.1 e).2.2.2

theorem scM_val {L : Type} [Field L] {n : ℕ} (w : Lˣ) : (scM (n := n) w).1 = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
  ext i j
  simp [scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem low_eq {L : Type} [Field L] {n : ℕ} (x : L) (X Y : Matrix (Ix n) (Ix n) L) (a b d : Matrix (Fin n) (Fin n) L)
    (h : X * fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) = fromBlocks a b 0 d * Y) :
    X.toBlocks₂₁ = d * Y.toBlocks₂₁ ∧ x • X.toBlocks₂₂ = d * Y.toBlocks₂₂ := by
  have e : fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ *
        fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) =
      fromBlocks a b 0 d * fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, fromBlocks_multiply] at e
  obtain ⟨-, -, h3, h4⟩ := Matrix.fromBlocks_inj.1 e
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.zero_mul, Matrix.mul_smul] at h3 h4
  exact ⟨h3, h4⟩

theorem exists_integral {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (hι : Function.Injective ι) {n : ℕ} (ϖ : O)
    (C D C' D' Bi Di Bi' Di' : Matrix (Fin n) (Fin n) O) (h1 : C * Bi + D * Di = 1) (h2 : C' * Bi' + D' * Di' = 1)
    (dL dLi : Matrix (Fin n) (Fin n) L) (hd : dL * dLi = 1) (hd' : dLi * dL = 1)
    (hC : C.map ι = dL * C'.map ι) (hD : ι ϖ • D.map ι = dL * D'.map ι) :
    (C * Bi' + ϖ • (D * Di')) * (ϖ • (C' * Bi) + D' * Di) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    (ϖ • (C' * Bi) + D' * Di) * (C * Bi' + ϖ • (D * Di')) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    C = (C * Bi' + ϖ • (D * Di')) * C' ∧ (ϖ • (C' * Bi) + D' * Di) * D = D' := by
  have hinj : Function.Injective (ι.mapMatrix (m := Fin n)) := fun A B h => by
    ext i j
    exact hι (congrFun (congrFun h i) j)
  have hs : ∀ M : Matrix (Fin n) (Fin n) O, ι.mapMatrix (ϖ • M) = ι ϖ • ι.mapMatrix M := by
    intro M; ext i j; simp
  have hC' : ι.mapMatrix C = dL * ι.mapMatrix C' := hC
  have hD' : ι ϖ • ι.mapMatrix D = dL * ι.mapMatrix D' := hD
  have h1' : ι.mapMatrix C * ι.mapMatrix Bi + ι.mapMatrix D * ι.mapMatrix Di = 1 := by
    rw [← map_mul, ← map_mul, ← map_add (f := _), h1, map_one]
  have h2' : ι.mapMatrix C' * ι.mapMatrix Bi' + ι.mapMatrix D' * ι.mapMatrix Di' = 1 := by
    rw [← map_mul, ← map_mul, ← map_add (f := _), h2, map_one]
  have hCi : ι.mapMatrix C' = dLi * ι.mapMatrix C := by
    rw [hC', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hDi : ι.mapMatrix D' = ι ϖ • (dLi * ι.mapMatrix D) := by
    rw [← Matrix.mul_smul, hD', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hF : ι.mapMatrix (C * Bi' + ϖ • (D * Di')) = dL := by
    rw [map_add (f := _), hs, map_mul, map_mul, hC', ← Matrix.smul_mul, hD', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
      h2', Matrix.mul_one]
  have hG : ι.mapMatrix (ϖ • (C' * Bi) + D' * Di) = ι ϖ • dLi := by
    rw [map_add (f := _), hs, map_mul, map_mul, hCi, hDi, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← smul_add,
      ← Matrix.mul_add, h1', Matrix.mul_one]
  refine ⟨hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · rw [map_mul, hF, hG, hs, map_one, Matrix.mul_smul, hd]
  · rw [map_mul, hF, hG, hs, map_one, Matrix.smul_mul, hd']
  · rw [map_mul, hF, hC']
  · rw [map_mul, hG, Matrix.smul_mul, hDi]

theorem iD_eq_rank : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw κ h hred
  obtain ⟨a, d, b, κ', hEq, rfl⟩ := hred
  have hv := congrArg Units.val hEq
  have hlow := low_eq (w : L) (κ.1.map (algebraMap O L)) (κ'.1.map (algebraMap O L)) a.1 b d.1 (by
    have : (tauM (n := n) w).1 = fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
      simp [tauM, pM, scM_val]
    rw [← this]
    exact hv)
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨e1, e2, e3, e4⟩ := exists_integral (algebraMap O L) (IsFractionRing.injective O L) ϖ
    (lowerLeftBlock κ) (dBlk κ) (lowerLeftBlock κ') (dBlk κ') (κ⁻¹).1.toBlocks₁₂ (κ⁻¹).1.toBlocks₂₂ (κ'⁻¹).1.toBlocks₁₂ (κ'⁻¹).1.toBlocks₂₂
    (low_rows κ) (low_rows κ') d.1 (d⁻¹).1 (by rw [← Units.val_mul]; simp) (by rw [← Units.val_mul]; simp)
    hlow.1 (by rw [← hw]; exact hlow.2)
  have hn := rank_add_rank_eq hϖ _ _ e1 e2
  set R := (IsLocalRing.residue O).mapMatrix (m := Fin n) with hR
  have hsz : ∀ M : Matrix (Fin n) (Fin n) O, R (ϖ • M) = 0 := by
    intro M; ext i j; simp [hR, hres]
  have hd0 : (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) =
      R (lowerLeftBlock κ) * R (κ'⁻¹).1.toBlocks₁₂ := by
    change R _ = _
    rw [map_add (f := _), hsz, add_zero, map_mul]
  have hE0 : (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) =
      R (dBlk κ') * R (κ⁻¹).1.toBlocks₂₂ := by
    change R _ = _
    rw [map_add (f := _), hsz, zero_add, map_mul]
  have r1 : ((lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O)).rank
      = (R (lowerLeftBlock κ)).rank := by
    apply le_antisymm
    · rw [hd0]; exact Matrix.rank_mul_le_left _ _
    · have : R (lowerLeftBlock κ) = (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) *
          R (lowerLeftBlock κ') := by
        conv_lhs => rw [e3]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  have r2 : ((ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O)).rank
      = (R (dBlk κ')).rank := by
    apply le_antisymm
    · rw [hE0]; exact Matrix.rank_mul_le_left _ _
    · have : R (dBlk κ') = (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) *
          R (dBlk κ) := by
        conv_lhs => rw [← e4]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  rw [r1, r2] at hn
  have hc : lowerLeftBlock (resK κ) = R (lowerLeftBlock κ) := rfl
  have hdd : dBlk (resK κ') = R (dBlk κ') := rfl
  unfold iD
  rw [hc, hdd]
  omega

end GlobalTheory.CompanionTheory.Jp.RedRank

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolic
section
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedUnique

theorem exists_pM_of_low_zero {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k)
    (hg : g.1.toBlocks₂₁ = 0) :
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k), g = pM a d b := by
  have hgb : g.1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ 0 g.1.toBlocks₂₂ := by
    rw [← hg, fromBlocks_toBlocks]
  have hdet : g.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [hgb, det_fromBlocks_zero₂₁] at hdet
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), g.1.toBlocks₁₂, ?_⟩
  apply Units.ext
  exact hgb

theorem low_inv_mul_pM {R : Type} [CommRing R] {n : ℕ} (a₁ d₁ a₂ d₂ : GL (Fin n) R)
    (b₁ b₂ : Matrix (Fin n) (Fin n) R) :
    (((pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ : GL (Ix n) R)).1.toBlocks₂₁ = 0 := by
  have h1 : ((pM a₁ d₁ b₁ : GL (Ix n) R)).1 = fromBlocks a₁.1 b₁ 0 d₁.1 := rfl
  have h2 : (((pM a₂ d₂ b₂)⁻¹ : GL (Ix n) R)).1 =
      fromBlocks (a₂⁻¹).1 (-((a₂⁻¹).1 * b₂ * (d₂⁻¹).1)) 0 (d₂⁻¹).1 := rfl
  rw [Units.val_mul, h1, h2, fromBlocks_multiply]
  simp [toBlocks_fromBlocks₂₁]

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  intro O L _ _ _ _ _ _ n w κ h₁ h₂ r₁ r₂
  obtain ⟨a₁, d₁, b₁, κ₁, e₁, rfl⟩ := r₁
  obtain ⟨a₂, d₂, b₂, κ₂, e₂, rfl⟩ := r₂
  obtain ⟨c, hcd⟩ : ∃ c : GL (Ix n) O, c = κ₂ * κ₁⁻¹ := ⟨_, rfl⟩
  have hc : inL (L := L) c = (pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ := by
    have e : pM a₁ d₁ b₁ * inL (L := L) κ₁ = pM a₂ d₂ b₂ * inL (L := L) κ₂ := e₁.symm.trans e₂
    rw [hcd, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e, mul_inv_cancel_right]
  have hlow : (inL (L := L) c).1.toBlocks₂₁ = 0 := by
    rw [hc]; exact low_inv_mul_pM _ _ _ _ _ _
  have hO : ∀ i j, c.1 (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have h0 : algebraMap O L (c.1 (Sum.inr i) (Sum.inl j)) = 0 := congrFun (congrFun hlow i) j
    exact IsFractionRing.injective O L (h0.trans (map_zero _).symm)
  have hk : (resK c).1.toBlocks₂₁ = 0 := by
    ext i j
    change IsLocalRing.residue O (c.1 (Sum.inr i) (Sum.inl j)) = 0
    rw [hO, map_zero]
  obtain ⟨a, d, b, hp⟩ := exists_pM_of_low_zero _ hk
  refine ⟨a, d, b, ?_⟩
  rw [← hp, ← map_mul, hcd, inv_mul_cancel_right]

end GlobalTheory.CompanionTheory.Jp.RedUnique

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem resAlg_of_isUnrQuad : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  intro R _ σ ϖ q ε h
  have hτ : ∀ a : R, barσ σ ϖ h.fix_ϖ 1 (Ideal.Quotient.mk (lev ϖ 1) a) =
      Ideal.Quotient.mk (lev ϖ 1) (σ a) := fun a => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨u, hu, hdec⟩ := h.basis
  refine ⟨?_, ?_, ?_, h.one_lt, h.card, h.eps⟩
  · intro e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [hτ a, hτ (σ a), h.inv]
  · intro e he hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
    rw [hτ] at he
    have hy0 : Ideal.Quotient.mk (lev ϖ 1) y = 0 := by
      have h1 : Ideal.Quotient.mk (lev ϖ 1) (y * (u - σ u)) = 0 := by
        have hxy : y * (u - σ u) = (x + y * u) - σ (x + y * u) := by
          rw [map_add (f := _), map_mul, hx, hy]
          ring
        rw [hxy, map_sub, he, sub_self]
      rw [map_mul] at h1
      exact (IsUnit.mul_left_eq_zero (hu.map (Ideal.Quotient.mk (lev ϖ 1)))).mp h1
    have hxe : Ideal.Quotient.mk (lev ϖ 1) (x + y * u) = Ideal.Quotient.mk (lev ϖ 1) x := by
      rw [map_add (f := _), map_mul, hy0, zero_mul, add_zero]
    rw [hxe] at hne ⊢
    exact (h.fixLocal x hx fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)).map _
  · refine ⟨Ideal.Quotient.mk (lev ϖ 1) u, ?_, ?_⟩
    · have hm := hu.map (Ideal.Quotient.mk (lev ϖ 1))
      rwa [map_sub, ← hτ] at hm
    · intro e
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
      refine ⟨Ideal.Quotient.mk (lev ϖ 1) x, Ideal.Quotient.mk (lev ϖ 1) y, ?_, ?_, ?_⟩
      · rw [hτ, hx]
      · rw [hτ, hy]
      · rw [map_add (f := _), map_mul]

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLtStatement
section
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_weight_square_length_lt : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L : List (ASeg T)) (n : Multiset (ASeg T)), AOrdered s L → InSh s n (wt s L) → n ≠ (L : Multiset (ASeg T)) → sqLen n < sqLen (L : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | exact GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | (intros; apply GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOutStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | exact GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | (intros; apply GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads <;> assumption)
end

