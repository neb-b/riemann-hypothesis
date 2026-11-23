module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocycles
section
open MvPolynomial

namespace GlobalTheory.UniformCocycle

variable {R : Type} [CommRing R] {σ : Type}

noncomputable def proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e)

theorem coeff_proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (proj I e P) m = ((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e := by
  classical
  simp only [proj, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    simp [h]

theorem proj_add (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P + Q) = proj I e P + proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_sub (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P - Q) = proj I e P - proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_X_mul (I : Ideal R) (e : ℕ) (i : σ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i * P) = X i * proj I e P := by
  classical
  ext m
  rw [coeff_proj, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp [coeff_proj]

theorem proj_Xpow_mul (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, proj_X_mul, ih, ← mul_assoc, ← pow_succ']


open Classical in
noncomputable def liftCoeff (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, reesAlgebra.monomial_mem.mpr h⟩ else 0

theorem liftCoeff_zero (I : Ideal R) (e : ℕ) : liftCoeff I e 0 = 0 := by
  unfold liftCoeff
  rw [dite_eq_left (zero_mem _)]
  apply Subtype.ext; simp

noncomputable def liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) :
    MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ F.support, monomial m (liftCoeff I e (AddMonoidAlgebra.coeff F m))

theorem coeff_liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (liftE I e F) m = liftCoeff I e (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [liftE, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, liftCoeff_zero]

theorem proj_liftE {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by
  ext m
  rw [coeff_proj, coeff_liftE, liftCoeff, dite_eq_left (h m)]
  simp only [Polynomial.coeff_monomial]
  by_cases h1 : e' = e
  · subst h1; simp
  · rw [Finsupp.single_eq_of_ne h1, ite_eq_right h1]
    simp

theorem isHomogeneous_liftE {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by
  intro m hm
  apply hF
  intro h0
  apply hm
  rw [coeff_liftE, h0, liftCoeff_zero]

theorem isHomogeneous_proj {I : Ideal R} {e t : ℕ} {P : MvPolynomial σ (reesAlgebra I)}
    (hP : P.IsHomogeneous t) : (proj I e P).IsHomogeneous t := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_proj, h0]
  simp

end GlobalTheory.UniformCocycle

namespace GlobalTheory


open UniformCocycle in
theorem uniformSerre_cocycle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, AddMonoidAlgebra.coeff (F i j) m ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, AddMonoidAlgebra.coeff (G i) m ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  open UniformCocycle in
  intro R _ _ I n J hJ
  obtain ⟨𝔞, h𝔞h, h𝔞⟩ := _root_.GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal R I n J hJ
  obtain ⟨d₀, hd₀⟩ := _root_.GlobalTheory.exists_coboundary_of_cocycle_homogeneous (reesAlgebra I) n 𝔞 h𝔞h
  refine ⟨d₀, fun d hd e N F hFh hFc hcoc => ?_⟩
  have hF'h : ∀ i j, (liftE I e (F i j)).IsHomogeneous (d + 2 * N) :=
    fun i j => isHomogeneous_liftE (hFh i j)
  have hF'p : ∀ e' i j, proj I e' (liftE I e (F i j)) = if e' = e then F i j else 0 :=
    fun e' i j => proj_liftE (hFc i j) e'
  have hcoc' : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l)) ∈ 𝔞 := by
    intro i j l
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hh := ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).mul (isHomogeneous_X _ l)).pow L).mul
      ((((isHomogeneous_X_pow l N).mul (hF'h i j)).add ((isHomogeneous_X_pow i N).mul (hF'h j l))).sub
        ((isHomogeneous_X_pow j N).mul (hF'h i l)))
    rw [h𝔞 _ _ hh]
    intro e' G hG
    have hGe : G = proj I e' (((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l))) := by
      ext m; rw [hG, coeff_proj]
    rw [hGe]
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p]
    by_cases he : e' = e
    · subst he
      simp only [↓reduceIte]
      simpa only [mul_pow, mul_assoc] using hL
    · simp [he]
  obtain ⟨N', G', hG'h, hG'⟩ := hd₀ d hd N (fun i j => liftE I e (F i j)) hF'h hcoc'
  refine ⟨N', fun i => proj I e (G' i), fun i => isHomogeneous_proj (hG'h i), fun i m => ?_, fun i j => ?_⟩
  · rw [coeff_proj]
    exact (mem_reesAlgebra_iff I _).mp (AddMonoidAlgebra.coeff (G' i) m).2 e
  · obtain ⟨L, hL⟩ := hG' i j
    refine ⟨L, ?_⟩
    have h2 : (1 + 1) * N + (N' + (d + N')) = (1 + 1) * N' + (d + 2 * N) := by ring
    have hh := (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow L).mul
      ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N').mul (hF'h i j) |>.sub
        (h2 ▸ (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N).mul
          (((isHomogeneous_X_pow j N').mul (hG'h i)).sub ((isHomogeneous_X_pow i N').mul (hG'h j)))))
    rw [h𝔞 _ _ hh] at hL
    have := hL e (proj I e _) (fun m => coeff_proj I e _ m)
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p, ↓reduceIte] at this
    simpa only [mul_pow, mul_assoc] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalNumberZeroOfHorizontal
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ Finset

noncomputable section

namespace GlobalTheory.EZ.HTot

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = (j : ℕ)
  have : (j : ℕ) < n + 1 := j.isLt
  omega

theorem backc_zero : backc 0 0 0 = 𝟙 _ := by
  ext j
  simp only [backc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min 0 (0 + (j : ℕ)) = (j : ℕ)
  have : (j : ℕ) < 0 + 1 := j.isLt
  omega

theorem bop_id (a b : ℕ) : bop (𝟙 (SimplexCategory.mk a)) (𝟙 (SimplexCategory.mk b)) = 𝟙 (bo a b) := rfl

theorem idO_self (a b : ℕ) : idO a b a b = 𝟙 (bo a b) := by
  rw [idO, if_pos ⟨rfl, rfl⟩, idc_self, idc_self, bop_id]

theorem idO_ne {a b c d : ℕ} (h : ¬ (a = c ∧ b = d)) : idO a b c d = 0 := by
  rw [idO, if_neg h]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl, idc_self, backc_zero, bop_id]

theorem sum_idO_comp {T : BOp} (k a b : ℕ) (h : a + b = k) (g : ∀ p q : ℕ, bo p q ⟶ T) :
    ∑ y ∈ antidiagonal k, idO a b y.1 y.2 ≫ g y.1 y.2 = g a b := by
  rw [Finset.sum_eq_single (a, b)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.zero_comp]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem sum_comp_idO {S : BOp} (k c d : ℕ) (h : c + d = k) (f : ∀ p q : ℕ, S ⟶ bo p q) :
    ∑ x ∈ antidiagonal k, f x.1 x.2 ≫ idO x.1 x.2 c d = f c d := by
  rw [Finset.sum_eq_single (c, d)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.comp_zero]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem dT_comp_dT (a b c d : ℕ) (h : c + d + 2 = a + b) :
    ∑ x ∈ antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 :=
  GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero a b c d h

theorem acyclic (a b k : ℕ) (hk : 1 ≤ k) (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b')
    (hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) :
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d :=
  GlobalTheory.T.bisimplicialOperatorChains_acyclic_positiveDegree a b k hk z hz

theorem exists_fill : ∃ H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'),
    ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  have : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
    intro a b k z
    by_cases hk : 1 ≤ k
    · by_cases hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0
      · obtain ⟨w, hw⟩ := acyclic a b k hk z hz
        exact ⟨w, fun _ _ => hw⟩
      · exact ⟨0, fun _ h => absurd h hz⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose H hH using this
  exact ⟨H, hH⟩

noncomputable def kRec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (n : ℕ) :
    ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b' :=
  Nat.rec (motive := fun _ => ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (fun _ _ _ _ => 0)
    (fun n K a b => H a b (n + 1) (fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ K x.1 x.2 a' b')) n

theorem kRec_zero (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (a b a' b' : ℕ) :
    kRec G H 0 a b a' b' = 0 := rfl

end GlobalTheory.EZ.HTot

namespace GlobalTheory.EZ.HTot

theorem kRec_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hGd : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'))
    (hH : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d) :
    ∀ n a b : ℕ, a + b = n → ∀ a' b' : ℕ, a' + b' = n →
      G a b n ≫ awO n a' b' = idO a b a' b' +
        ∑ x ∈ antidiagonal (n + 1), kRec G H n a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ antidiagonal (n - 1), dT a b x.1 x.2 ≫ kRec G H (n - 1) x.1 x.2 a' b' := by
  intro n
  induction n with
  | zero =>
    intro a b hab a' b' hab'
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    obtain ⟨rfl, rfl⟩ : a' = 0 ∧ b' = 0 := by omega
    simp [kRec_zero, hG0, awO_zero, idO_self]
  | succ n ih =>
    intro a b hab a' b' hab'
    set E : ∀ a' b' : ℕ, bo a b ⟶ bo a' b' := fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 a' b' with hE
    have hcyc : ∀ c d : ℕ, c + d + 1 = n + 1 → ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d = 0 := by
      intro c d hcd
      have h1 : ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d := by
        simp only [Category.assoc, ← Preadditive.comp_sum]
        rw [← GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT n c d (by omega), ← Category.assoc, hGd a b n hab, Preadditive.sum_comp]
        simp only [Category.assoc]
      have h2 : ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d = dT a b c d :=
        sum_idO_comp (n + 1) a b hab (fun p q => dT p q c d)
      have key : ∀ x ∈ antidiagonal n, ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d =
          G x.1 x.2 n ≫ awO n c d - idO x.1 x.2 c d -
            ∑ z ∈ antidiagonal (n - 1), dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d := by
        intro x hx
        rw [ih x.1 x.2 (mem_antidiagonal.1 hx) c d (by omega)]
        abel
      have h4 : ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ idO x.1 x.2 c d = dT a b c d :=
        sum_comp_idO n c d (by omega) (fun p q => dT a b p q)
      have h5 : ∑ x ∈ antidiagonal n, ∑ z ∈ antidiagonal (n - 1),
          dT a b x.1 x.2 ≫ dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d = 0 := by
        rcases n with _ | m
        · simp [kRec_zero]
        · rw [Nat.add_sub_cancel, Finset.sum_comm]
          refine Finset.sum_eq_zero (fun z hz => ?_)
          have hz' := mem_antidiagonal.1 hz
          simp only [← Category.assoc]
          rw [← Preadditive.sum_comp]
          have h0 := dT_comp_dT a b z.1 z.2 (by omega)
          rw [show z.1 + z.2 + 1 = m + 1 by omega] at h0
          rw [h0, Limits.zero_comp]
      have h3 : ∑ y ∈ antidiagonal (n + 1),
          (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d - dT a b c d - 0 := by
        have e1 : ∑ y ∈ antidiagonal (n + 1),
            (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
            ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫
              ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d := by
          simp only [Preadditive.sum_comp, Category.assoc, Preadditive.comp_sum]
          exact Finset.sum_comm
        rw [e1, Finset.sum_congr rfl (fun x hx => by rw [key x hx])]
        simp only [Preadditive.comp_sub, Finset.sum_sub_distrib, Preadditive.comp_sum]
        rw [h4, h5]
      calc ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d
          = ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1),
              (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d := by
            simp only [hE, Preadditive.sub_comp, Finset.sum_sub_distrib]
        _ = 0 := by rw [h1, h2, h3]; abel
    have hk : kRec G H (n + 1) a b = H a b (n + 1) E := rfl
    rw [Nat.add_sub_cancel, hk, hH a b (n + 1) E (by omega) hcyc a' b' hab']
    simp only [hE]
    abel

theorem htot : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b →
      G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  intro G hG0 hGd
  obtain ⟨H, hH⟩ := exists_fill
  refine ⟨fun a b => kRec G H (a + b) a b, ?_⟩
  intro a b a' b' h
  rw [kRec_spec G hG0 hGd H hH (a + b) a b rfl a' b' h]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  show _ = dT a b x.1 x.2 ≫ kRec G H (x.1 + x.2) x.1 x.2 a' b'
  rw [mem_antidiagonal.1 hx]

end GlobalTheory.EZ.HTot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakSolutionOfSmoothSolution
section
noncomputable section

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology

namespace GlobalTheory.HCA

theorem integrable_mul_of_continuousOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hcont : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hgU h)
      have h0 : (fun x => f x * g x) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact continuousAt_const.congr h0.symm
  exact hcont.integrable_of_hasCompactSupport (hgc.mul_left)

theorem dw_hasCompactSupport_tsupport {d : ℕ} (w : List (Fin d)) {f : E d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (dw w f) ∧ tsupport (dw w f) ⊆ tsupport f := by
  induction w with
  | nil => exact ⟨hf, subset_rfl⟩
  | cons j w ih =>
    refine ⟨ih.1.fderiv_apply (𝕜 := ℝ) (ev j), ?_⟩
    exact (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := dw w f) (ev j)).trans ih.2

theorem contDiff_mul_of_contDiffOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {b φ : E d → ℂ} (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : (fun y => b y * φ y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem weakSol_of_smooth :
    ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ),
      (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U →
      (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  intro d m U hU a ha u hu hap i φ hφ hc hs
  show ∫ x, u x * trOp m a φ x = 0
  have hψ : ∀ n w, ContDiff ℝ ∞ (fun y => a n w y * φ y) := fun n w =>
    contDiff_mul_of_contDiffOn_of_tsupport hU (ha n w) hφ hs
  have hψc : ∀ n w, HasCompactSupport (fun y => a n w y * φ y) := fun n w => hc.mul_left
  have hψs : ∀ n w, tsupport (fun y => a n w y * φ y) ⊆ U := fun n w =>
    (tsupport_mul_subset_right).trans hs
  have hI1 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) := by
    intro n w
    have hdc := dw_hasCompactSupport_tsupport (List.ofFn w) (hψc n w)
    have hcont : Continuous (dw (List.ofFn w) (fun y => a n w y * φ y)) := by
      have := (_root_.GlobalTheory.HCA.dw_smooth_local_linear d Set.univ isOpen_univ (List.ofFn w)).1 _ (hψ n w).contDiffOn
      exact (contDiffOn_univ.1 this).continuous
    have := integrable_mul_of_continuousOn_of_tsupport hU hu.continuousOn
      (g := fun x => (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)
      (continuous_const.mul hcont) (hdc.1.mul_left)
      ((tsupport_mul_subset_right).trans (hdc.2.trans (hψs n w)))
    exact this
  have hI2 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => dw (List.ofFn w) u x * (a n w x * φ x)) := by
    intro n w
    exact integrable_mul_of_continuousOn_of_tsupport hU
      ((_root_.GlobalTheory.HCA.dw_smooth_local_linear d U hU (List.ofFn w)).1 u hu).continuousOn (hψ n w).continuous (hψc n w) (hψs n w)
  have hterm : ∀ n (w : Fin n → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n w
    have hibp := _root_.GlobalTheory.HCA.integral_mul_dw_eq_neg_pow d U hU (List.ofFn w) u (fun y => a n w y * φ y) hu (hψ n w) (hψc n w)
      (hψs n w)
    rw [List.length_ofFn] at hibp
    have e1 : (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) =
        fun x => (-1 : ℂ) ^ n * (u x * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
      funext x; ring
    rw [e1, integral_const_mul, hibp, ← mul_assoc, ← mul_pow]
    norm_num
  have hsplit : (fun x => u x * trOp m a φ x) = fun x => ∑ n ∈ Finset.range (m + 1),
      ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
    funext x
    simp only [trOp, Finset.mul_sum]
  rw [hsplit, MeasureTheory.integral_finsetSum _ (fun n _ => MeasureTheory.integrable_finsetSum _ (fun w _ => hI1 n w))]
  have hin : ∀ n ∈ Finset.range (m + 1),
      ∫ x, ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, ∑ w : Fin n → Fin d, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n _
    rw [MeasureTheory.integral_finsetSum _ (fun w _ => hI1 n w), MeasureTheory.integral_finsetSum _ (fun w _ => hI2 n w)]
    exact Finset.sum_congr rfl fun w _ => hterm n w
  rw [Finset.sum_congr rfl hin,
    ← MeasureTheory.integral_finsetSum _ (fun n _ => MeasureTheory.integrable_finsetSum _ (fun w _ => hI2 n w))]
  have hzero : (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      dw (List.ofFn w) u x * (a n w x * φ x)) = fun _ => (0 : ℂ) := by
    funext x
    by_cases hx : x ∈ U
    · have h := hap x hx
      have e : (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          dw (List.ofFn w) u x * (a n w x * φ x)) = apOp m a u x * φ x := by
        simp only [apOp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [e, h, zero_mul]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
      simp [h0]
  rw [hzero, integral_zero]

end GlobalTheory.HCA

end
end

