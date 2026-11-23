module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducible
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mul_entry_mem_subring {ι : Type} [Fintype ι] {R : Type} [CommRing R]
    (S : Subring R) (k l : Matrix ι ι R) (hk : ∀ i j, k i j ∈ S) (hl : ∀ i j, l i j ∈ S) :
    ∀ i j, (k * l) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply]
  exact S.sum_mem fun a _ => S.mul_mem (hk _ _) (hl _ _)

theorem cf_of_ss : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _ Γ R _ _ R₀ hΓ hss hA
  classical
  obtain ⟨m, d, t, hfix, hstab, hcl⟩ := _root_.GlobalTheory.ClassFin.exists_tensor_stabiliser_closed_orbit ι Γ hΓ hss
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.ClassFin.exists_mvPolynomial_ev_eq_act ι m d t
  obtain ⟨-, hmul, hadj, hdet⟩ := _root_.GlobalTheory.ClassFin.pts_group ι Γ hΓ.toIsPre R
  obtain ⟨hrat, hratR⟩ := _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts ι Γ
  obtain ⟨D, hD, hDt⟩ := (adelicPair_elementary R R₀ hA).2.1 (TIdx ι d) (fun k => algebraMap ℚ R (t k))
  obtain ⟨Z, hZ⟩ := _root_.GlobalTheory.ClassFin.finite_integral_classes_closed_orbit ι m d t hcl D hD
  have hone : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S), act d s 1 = s :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).1
  have hact : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S) (y z : Matrix ι ι S),
      act d s (y * z) = act d (act d s y) z :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).2.1
  have hmap : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (s : TIdx ι d → ℚ) (y : Matrix ι ι ℚ),
      act d (fun k => algebraMap ℚ S (s k)) (y.map (algebraMap ℚ S)) = fun k => algebraMap ℚ S (act d s y k) :=
    fun S _ _ s y => ((tpow_act_algebra ι ℚ).2 m d s).2.2.2.2.2 S (algebraMap ℚ S) y

  have hfixR : ∀ x ∈ pts Γ R, act d (fun k => algebraMap ℚ R (t k)) x = fun k => algebraMap ℚ R (t k) := by
    intro x hx
    funext k
    have hv : Φ k - MvPolynomial.C (t k) ∈ vanI Γ := by
      intro g hg
      have h1 := hΦ ℂ g k
      have h2 := congrFun (hfix g hg) k
      simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 ⊢
      rw [h1, sub_eq_zero]
      exact h2
    have h3 := hx _ hv
    have h1 := hΦ R x k
    simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 h3
    rw [← h1]
    exact sub_eq_zero.1 h3
  let P : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R → Prop := fun z p =>
    p.1.det = 1 ∧ p.2.det = 1 ∧ (∀ i j, p.2 i j ∈ R₀) ∧ p.1.map (algebraMap ℚ R) * p.2 ∈ pts Γ R ∧
      act d t p.1 = z
  have key : ∀ x ∈ pts Γ R, ∃ z ∈ Z, ∃ p, P z p ∧ x = p.1.map (algebraMap ℚ R) * p.2 := by
    intro x hx
    obtain ⟨h, k, hh, hk, hkint, rfl⟩ := _root_.GlobalTheory.ClassFin.sl_class_number_one ι R R₀ hA x (hdet x hx)
    have hkk : k * k.adjugate = 1 := by rw [Matrix.mul_adjugate, hk, one_smul]
    have e1 : act d (fun k => algebraMap ℚ R (t k)) k.adjugate = fun k => algebraMap ℚ R (act d t h k) := by
      rw [← hmap]
      conv_lhs => rw [← hfixR _ hx, ← hact, Matrix.mul_assoc, hkk, Matrix.mul_one]
    have e2 : ∀ j, ∃ z : ℤ, (D : ℚ) * act d t h j = z := by
      intro j
      apply hA.int_of_mem
      have h1 := ((tpow_act_algebra ι R).2 m d ((D : R) • fun k => algebraMap ℚ R (t k))).2.2.2.1 R₀
        k.adjugate (fun k => hDt k) (adjugate_entry_mem_subring R₀ k hkint) j
      rw [((tpow_act_algebra ι R).2 m d (fun k => algebraMap ℚ R (t k))).2.2.2.2.1, e1] at h1
      rw [map_mul, map_natCast]
      exact h1
    obtain ⟨γ, hγ, hγZ⟩ := hZ h hh e2
    have hγγ : γ * γ.adjugate = 1 := by rw [Matrix.mul_adjugate, hγ, one_smul]
    have hγR : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * γ.adjugate.map (Int.castRingHom R) = 1 := by
      have : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) = γ.map (Int.castRingHom R) := by
        ext i j; simp
      rw [this, ← Matrix.map_mul, hγγ, Matrix.map_one _ (map_zero _) (map_one _)]
    have e3 : (h * γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * (γ.adjugate.map (Int.castRingHom R) * k)
        = h.map (algebraMap ℚ R) * k := by
      rw [Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ k, hγR, Matrix.one_mul]
    refine ⟨_, hγZ, (h * γ.map (Int.cast : ℤ → ℚ), γ.adjugate.map (Int.castRingHom R) * k),
      ⟨?_, ?_, ?_, ?_, rfl⟩, e3.symm⟩
    · have : (γ.map (Int.cast : ℤ → ℚ)).det = 1 := by
        have h1 := (Int.castRingHom ℚ).map_det γ
        rw [hγ, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hh, this, one_mul]
    · have : (γ.adjugate.map (Int.castRingHom R)).det = 1 := by
        have h1 := (Int.castRingHom R).map_det γ.adjugate
        rw [Matrix.det_adjugate, hγ, one_pow, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hk, this, one_mul]
    · exact mul_entry_mem_subring R₀ _ _ (fun i j => intCast_mem R₀ _) hkint
    · simp only
      rw [e3]; exact hx
  let c : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R := fun z =>
    if hz : ∃ p, P z p then hz.choose else (1, 1)
  have hc : ∀ z, (∃ p, P z p) → P z (c z) := by
    intro z hz
    simp only [c, dif_pos hz]
    exact hz.choose_spec
  refine ⟨(Z.filter fun z => ∃ p, P z p).image fun z => (c z).1.map (algebraMap ℚ R) * (c z).2, ?_, ?_⟩
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hs
    exact (hc z (Finset.mem_filter.1 hz).2).2.2.2.1
  · intro x hx
    obtain ⟨z, hz, ⟨h, k⟩, hp, rfl⟩ := key x hx
    have hz' : z ∈ Z.filter fun z => ∃ p, P z p := Finset.mem_filter.2 ⟨hz, _, hp⟩
    have hq := hc z ⟨_, hp⟩
    have hs := Finset.mem_image_of_mem (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) hz'
    generalize (Z.filter fun z => ∃ p, P z p).image (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) = T at hs ⊢
    generalize c z = q at hq hs
    obtain ⟨h', k'⟩ := q
    obtain ⟨hh, hk, hkint, hxx, hhz⟩ := hp
    obtain ⟨hh', hk', hkint', hxx', hhz'⟩ := hq
    simp only at hh hk hkint hxx hhz hh' hk' hkint' hxx' hhz' hs ⊢
    have a1 : h' * h'.adjugate = 1 := by rw [Matrix.mul_adjugate, hh', one_smul]
    have a2 : h'.adjugate * h' = 1 := by rw [Matrix.adjugate_mul, hh', one_smul]
    have a3 : k' * k'.adjugate = 1 := by rw [Matrix.mul_adjugate, hk', one_smul]
    have g1 : act d t (h * h'.adjugate) = t := by
      rw [hact, hhz, ← hhz', ← hact, a1, hone]
    have g2 : h * h'.adjugate ∈ pts Γ ℚ := by
      apply hrat
      apply hstab
      · have h1 := (algebraMap ℚ ℂ).map_det (h * h'.adjugate)
        rw [Matrix.det_mul, Matrix.det_adjugate, hh, hh', one_pow, one_mul, map_one] at h1
        exact h1.symm
      · have h1 := hmap ℂ t (h * h'.adjugate)
        rw [g1] at h1
        exact h1
    have g3 := hratR R _ g2
    have e : h.map (algebraMap ℚ R) * k = (h * h'.adjugate).map (algebraMap ℚ R) *
        (h'.map (algebraMap ℚ R) * k') * (k'.adjugate * k) := by
      rw [← Matrix.mul_assoc _ _ k', ← Matrix.map_mul, Matrix.mul_assoc h, a2, Matrix.mul_one,
        Matrix.mul_assoc, ← Matrix.mul_assoc k', a3, Matrix.one_mul]
    refine ⟨_, g2, _, hs, k'.adjugate * k, ?_,
      mul_entry_mem_subring R₀ _ _ (adjugate_entry_mem_subring R₀ k' hkint') hkint, e⟩
    have g4 := hmul _ g3 _ hxx'
    have g5 := hmul _ (hadj _ g4) _ hxx
    rw [e, ← Matrix.mul_assoc, Matrix.adjugate_mul, hdet _ g4, one_smul, Matrix.one_mul] at g5
    exact g5

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) *
      Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  let X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1
  have hXbot : X ⊥ = 0 := if_pos rfl
  have hXne : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => if_neg hI
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · simp [X, hI]
    by_cases hJ : J = ⊥
    · simp [X, hJ]
    rw [hXne _ (Ideal.mul_eq_bot.not.mpr (not_or.mpr ⟨hI, hJ⟩)), hXne _ hI, hXne _ hJ, one_mul]
  obtain ⟨Z, hZd, hZ, -⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K ⊤ X (fun _ => 1) top_ne_bot
    hXbot hXmul (fun I hI _ => by rw [hXne I hI, norm_one]) (fun I hI => absurd (sup_top_eq I) hI)
    (fun _ _ => (mul_one 1).symm) (fun _ _ _ => rfl) contDiffOn_const (fun _ _ => norm_one)
    (fun β hβ _ => hXne _ (by simpa using hβ))
  refine ⟨Z, hZd, fun s hs => ?_⟩
  rw [hZ s hs, _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot (hXne ⊤ top_ne_bot) hXmul
    (fun I => by by_cases hI : I = ⊥ <;> simp [X, hI]) s hs]
  have h1 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => hXne _ P.ne_bot
  simp only [h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalMatrixApproxAdeleLinearMap
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix


open GlobalTheory.UnRep.SmallMat in
theorem GlobalTheory.UnRep.exists_rational_approx_after_adele_linear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (φ : Matrix (Fin n) (Fin n) (RA F E) →+ Matrix (Fin n) (Fin n) (RA F E)), (∀ (a : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), φ ((a ⊗ₜ[F] (1 : E) : RA F E) • M) = (a ⊗ₜ[F] (1 : E) : RA F E) • φ M) → ∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), φ (M - fm F M₀) *ᵥ z = D • w := by
  intro F E _ _ _ _ _ n L hL hsp φ hφ M D hD
  obtain ⟨-, hS, -, -, hint⟩ := GlobalTheory.UnRep.idempotent_adeles_small_matrices F E n L hL hsp
  let P : Matrix (Fin n) (Fin n) (RA F E) → Prop := fun M =>
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)),
      ∃ w ∈ hat F (L : Set (Fin n → E)), φ (M - fm F M₀) *ᵥ z = D • w
  have hadd : ∀ A B, P A → P B → P (A + B) := by
    rintro A B ⟨A₀, hA⟩ ⟨B₀, hB⟩
    refine ⟨A₀ + B₀, fun z hz => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hA z hz
    obtain ⟨w, hw, hw'⟩ := hB z hz
    refine ⟨u + w, add_mem hu hw, ?_⟩
    rw [smul_add, ← hu', ← hw', ← Matrix.add_mulVec, fm_add, ← map_add (f := _), add_sub_add_comm]
  have hzero : P 0 := ⟨0, fun z _ => ⟨0, zero_mem _, by simp [fm_zero]⟩⟩
  have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (B : Matrix (Fin n) (Fin n) E),
      P ((a ⊗ₜ[F] (1 : E) : RA F E) • fm F B) := by
    intro a B
    obtain ⟨d, hd, hB⟩ := hS (φ (fm F B))
    obtain ⟨r, a', ha', rfl⟩ := exists_eq_algebraMap_add_nsmul F (D * d) (Nat.mul_pos hD hd) a
    refine ⟨r • B, fun z hz => ⟨_, hint a' ha' _ (hB z hz), ?_⟩⟩
    have h1 : fm F (r • B) =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) r ⊗ₜ[F] (1 : E) : RA F E) • fm F B := by
      ext i j
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, TensorProduct.add_tmul, add_smul, add_sub_cancel_left, hφ, Matrix.smul_mulVec,
      nsmul_tmul_one, smul_assoc, mul_smul, smul_comm d]
  have hsingle : ∀ i j (t : RA F E), P (Matrix.single i j t) := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a y =>
      have := hgen a (Matrix.single i j y)
      convert this using 1
      ext k l
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Matrix.single_apply]
      split_ifs <;> simp
    | add s t hs ht => rw [Matrix.single_add]; exact hadd _ _ hs ht
  change P M
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ P hadd hzero fun i _ =>
    Finset.sum_induction _ P hadd hzero fun j _ => hsingle i j _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemPowsSUnitsChooseT
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_sup_zpowers_chooseT (p : ℕ) {G : Type} [CommGroup G] (Q : Subgroup G) (d : G)
    (hp : p.Prime) (hd : d ^ p ∈ Q) (hn : d ∉ Q) :
    Q.relIndex (Q ⊔ Subgroup.zpowers d) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.relIndex_sup_left]
  have h := Subgroup.relIndex_ker (Subgroup.zpowers d) (QuotientGroup.mk' Q)
  rw [QuotientGroup.ker_mk', MonoidHom.map_zpowers, Nat.card_zpowers] at h
  rw [h]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hd
  · exact fun e => hn ((QuotientGroup.eq_one_iff _).1 e)

theorem mem_pows_sUnits_chooseT (p : ℕ) (hp : p ≠ 0) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (hx : x ∈ sUnits F S) (r : F)
    (hr : r ^ p = (x : F)) : x ∈ pows p (sUnits F S) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hr, zero_pow hp])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_sUnits]
    intro v hv
    have h := (mem_sUnits F S x).1 hx v hv
    rw [← hr, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le hp).1 h
  · ext
    simp [hr]

theorem exists_auxiliary_places_prime : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  classical
  have hQU : pows p (sUnits F S) ≤ sUnits F S := by
    rintro _ ⟨y, hy, rfl⟩
    exact (sUnits F S).pow_mem hy p
  have hdd : δ ^ p ∈ pows p (sUnits F S) := ⟨δ, hδ, rfl⟩
  have hdn : δ ∉ pows p (sUnits F S) := by
    rintro ⟨y, -, hy⟩
    exact hns (y : F) (by rw [← hy]; simp)
  have hHU : pows p (sUnits F S) ⊔ Subgroup.zpowers δ ≤ sUnits F S :=
    sup_le hQU ((Subgroup.zpowers_le).2 hδ)
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = S.card + Fintype.card (InfinitePlace F) :=
    ⟨S.card + Fintype.card (InfinitePlace F) - 1, by omega⟩
  have hidx : (pows p (sUnits F S) ⊔ Subgroup.zpowers δ).relIndex (sUnits F S) = p ^ m := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hHU
    have h2 : (pows p (sUnits F S)).relIndex (sUnits F S) = _ :=
      (pTor_pIdx_sUnits p F ζ S hp hζ).2
    rw [relIndex_sup_zpowers_chooseT p _ _ hp hdd hdn, h2, ← hm, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F),
      Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun v x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hpw : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ),
      x ^ p ∈ powSub p (algebraMap F (v.adicCompletion F)) := fun v x =>
    ⟨algebraMap F (v.adicCompletion F) x, by rw [Units.val_pow_eq_pow_val, map_pow]⟩
  obtain ⟨T, hT, hgood, hA⟩ := exists_indep_prime_index p Fˣ (HeightOneSpectrum (𝓞 F)) (sUnits F S)
    (pows p (sUnits F S) ⊔ Subgroup.zpowers δ)
    (fun v => powSub p (algebraMap F (v.adicCompletion F)))
    (fun v => v ∉ S ∧ ∃ r : v.adicCompletion F,
      r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) m hp hidx
    (by
      rintro v ⟨-, hv⟩
      refine le_trans inf_le_right (sup_le ?_ ((Subgroup.zpowers_le).2 hv))
      rintro _ ⟨y, -, rfl⟩
      exact hpw v y)
    (fun v _ x _ => hpw v x)
    (by
      rintro v ⟨hv, -⟩ x hx hx' y hy
      obtain ⟨k, r, hr⟩ := _root_.GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit p F v (algebraMap F (v.adicCompletion F) x)
        (algebraMap F (v.adicCompletion F) y) hp (hS.2 v hv)
        (by rw [hval]; exact (mem_sUnits F S x).1 hx v hv)
        (by rw [hval]; exact (mem_sUnits F S y).1 hy v hv)
        (fun r hr => hx' ⟨r, hr⟩)
      refine ⟨k, r, ?_⟩
      have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by simp
      rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, map_div₀, map_pow, hr]
      field_simp)
    (by
      intro x hx hxH
      obtain ⟨v, h1, h2, h3⟩ := _root_.GlobalTheory.CNorm.exists_place_pow_and_not_pow p F ζ δ x S hp hζ δ.ne_zero x.ne_zero hns
        (fun k r h => hxH (by
          have h4 : x / δ ^ k ∈ pows p (sUnits F S) := by
            refine mem_pows_sUnits_chooseT p hp.ne_zero F S _
              ((sUnits F S).div_mem hx ((sUnits F S).pow_mem hδ k)) r ?_
            have hδ0 := δ.ne_zero
            rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, h]
            field_simp
          have h5 := Subgroup.mul_mem_sup h4 (Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) k)
          rwa [div_mul_cancel] at h5))
      exact ⟨v, ⟨h1, h2⟩, fun ⟨r, hr⟩ => h3 r hr⟩)
  refine ⟨T, ?_, by rw [hT, hm], fun v hv => (hgood v hv).2, hA⟩
  rw [Finset.disjoint_right]
  exact fun v hv => (hgood v hv).1

end GlobalTheory.CNorm
end

