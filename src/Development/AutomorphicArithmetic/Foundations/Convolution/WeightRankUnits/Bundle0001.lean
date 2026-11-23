module

public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLaplaceFactorisation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.AbsProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem absHalf_eq_sqrt {E : Type} [Field E] [NumberField E] [IsCMField E] (u : HeightOneSpectrum (𝓞 E))
    (x : u.adicCompletion E) (hx : x ≠ 0) : absHalf u x = ((Real.sqrt ‖x‖ : ℝ) : ℂ) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold absHalf
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, Formalism.UG.ordL, dite_eq_right hv, neg_neg]
  simp [Formalism.UG.qV, WithZero.toAdd_unzero_eq_log hv]

theorem UpperTheory.ConvolutionTheory.G2.absProd :
    UpperTheory.ConvolutionTheory.G2.AbsProd := by
  intro E _ _ _ R hR
  have hne : ∀ u : HeightOneSpectrum (𝓞 E), algebraMap E (u.adicCompletion E) R ≠ 0 := fun u =>
    (_root_.map_ne_zero _).2 hR
  have hfun : (fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) R)) =
      fun u : Pl E => ((Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖ : ℝ) : ℂ) :=
    funext fun u => absHalf_eq_sqrt u _ (hne u)
  have hmult : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  have hPF := prod_abs_eq_one hR
  simp only [hmult] at hPF
  have hfp : ∏ᶠ w : FinitePlace E, w R =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) R‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
    rfl
  rw [hfp] at hPF
  have hgfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      ‖algebraMap E (v.adicCompletion E) R‖).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport hR).preimage
      (FinitePlace.equivHeightOneSpectrum (K := E)).symm.injective.injOn).subset fun v hv => ?_
    simp only [Set.mem_preimage, Function.mem_mulSupport, FinitePlace.equivHeightOneSpectrum_symm_apply] at hv ⊢
    exact hv
  have hsub : (Function.mulSupport fun u : Pl E =>
      ((Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖ : ℝ) : ℂ)) ⊆ (hgfin.toFinset : Set (Pl E)) := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    intro h1
    apply hu
    have h1' : ‖algebraMap E (u.adicCompletion E) R‖ = 1 := h1
    simp only [h1', Real.sqrt_one, Complex.ofReal_one]
  rw [hfun]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  rw [finprod_eq_prod _ hgfin] at hPF
  simp only [InfinitePlace.norm_embedding_eq]
  rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_eq_one]
  have hnn : 0 ≤ (∏ u ∈ hgfin.toFinset, Real.sqrt ‖algebraMap E (u.adicCompletion E) R‖) *
      ∏ v : InfinitePlace E, v R :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (Finset.prod_nonneg fun v _ => apply_nonneg v R)
  refine (pow_eq_one_iff_of_nonneg hnn two_ne_zero).1 ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, mul_comm, ← hPF]
  congr 1
  exact Finset.prod_congr rfl fun u _ => Real.sq_sqrt (norm_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MuProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem muAt_unit {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (u : Pl E) (k : Eˣ) :
    UpperTheory.ConvolutionTheory.G2.muAt μ u (k : E) = ((μ.locK u k : ℂˣ) : ℂ) := by
  have h : algebraMap E (u.adicCompletion E) (k : E) ≠ 0 := by
    simpa using k.ne_zero
  rw [UpperTheory.ConvolutionTheory.G2.muAt, dite_eq_left h, HChar.locK, MonoidHom.comp_apply]
  have hu : Units.mk0 (algebraMap E (u.adicCompletion E) (k : E)) h = atFin u k := Units.ext rfl
  rw [hu]

theorem UpperTheory.ConvolutionTheory.G2.muProd :
    UpperTheory.ConvolutionTheory.G2.MuProd := by
  intro E _ _ _ μ e hμ R hR
  obtain ⟨hf, hp⟩ := GlobalTheory.HCharUnit.finprod_locK_mul_inf E μ (Units.mk0 R hR)
  have hfun : (fun u : Pl E => UpperTheory.ConvolutionTheory.G2.muAt μ u R) =
      fun u : Pl E => (Units.coeHom ℂ) (μ.locK u (Units.mk0 R hR)) :=
    funext fun u => muAt_unit μ u (Units.mk0 R hR)
  have hsub : (Function.mulSupport fun u : Pl E => (Units.coeHom ℂ) (μ.locK u (Units.mk0 R hR))) ⊆
      Function.mulSupport fun u : Pl E => μ.locK u (Units.mk0 R hR) := by
    intro u hu h1
    exact hu (by simp only [h1, map_one])
  rw [hfun]
  refine ⟨hf.subset hsub, ?_⟩
  rw [← MonoidHom.map_finprod _ hf]
  have hinf := GlobalTheory.BCT.inf_mu_unit E μ e hμ (Units.mk0 R hR)
  simp only [Units.val_mk0] at hinf
  rw [← hinf]
  have := congrArg (Units.coeHom ℂ) hp
  simpa using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealSigned
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


open GlobalTheory.LaplaceChar ReciprocityTheory.ChartRestriction.TR.Weyl in
theorem UpperTheory.ConvolutionTheory.G2.realSigned : ∀ (a b : ℕ) (lam : DomWeight (a + b)) (e : ℤ), Odd e → ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight b) (ε : ι → ℂ), (∀ j, ε j = 1 ∨ ε j = -1) ∧ (∀ j, (infOfWeight (l₁ j)).map (· + (b : ℂ) * e / 2) + (infOfWeight (l₂ j)).map (· + (a : ℂ) * e / 2) = infOfWeight lam) ∧ ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) → ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt lam (Q₁ * Q₂)) = ∑ j, ε j * (starRingEnd ℂ) (chAt (l₁ j) Q₁) * (starRingEnd ℂ) (chAt (l₂ j) Q₂) := by
  intro a b lam e he
  obtain ⟨m, rfl⟩ := he
  set K : ℤ := m + 1 with hK
  refine ⟨{J : Finset (Fin (a + b)) // J.card = a}, inferInstance,
    fun J => selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K),
    fun J => selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K),
    fun J => (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * ((-1 : ℂ) ^ (a * b)) ^ K, ?_, ?_, ?_⟩
  · intro J
    beta_reduce
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ (by norm_num)]
    rcases Int.even_or_odd (((((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2 : ℕ) : ℤ)) + ((a * b : ℕ) : ℤ) * K) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · intro J
    beta_reduce
    let F : Fin (a + b) → ℂ := fun j => (lam.w j : ℂ) + ((((a + b : ℕ) : ℂ) - 1) / 2 - ((j : ℕ) : ℂ))
    have hL : (infOfWeight (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K))).map
        (· + (b : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1.val.map F := by
      rw [← map_orderEmbOfFin J.1 J.2 F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selL, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    have hR : (infOfWeight (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K))).map
        (· + (a : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1ᶜ.val.map F := by
      rw [← map_orderEmbOfFin J.1ᶜ (k := b) (by rw [Finset.card_compl, J.2]; simp) F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selR, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    rw [hL, hR, ← Multiset.map_add (f := _), val_add_compl]
    rfl
  · intro Q₁ Q₂ h1 h2 hd1 hd2 hsep hroot
    beta_reduce
    have exists_eq_prod_X_sub_C : ∀ (n : ℕ) (Q : ℂ[X]), Q.Monic → Q.natDegree = n →
        ∃ α : Fin n → ℂ, Q = ∏ i, (X - C (α i)) := by
      intro n
      induction n with
      | zero =>
        intro Q hm hd
        exact ⟨Fin.elim0, by rw [Fin.prod_univ_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hm hd⟩
      | succ n ih =>
        intro Q hm hd
        obtain ⟨r, hr⟩ := IsAlgClosed.exists_root Q (by
          rw [degree_eq_natDegree hm.ne_zero, hd]; exact_mod_cast Nat.succ_ne_zero n)
        have hdiv : (X - C r) * (Q /ₘ (X - C r)) = Q := mul_divByMonic_eq_iff_isRoot.mpr hr
        have hm' : (Q /ₘ (X - C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hm)
        have hd' : (Q /ₘ (X - C r)).natDegree = n := by
          rw [natDegree_divByMonic _ (monic_X_sub_C r), hd, natDegree_X_sub_C]; rfl
        obtain ⟨α, hα⟩ := ih _ hm' hd'
        refine ⟨Fin.cons r α, ?_⟩
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [← hα, hdiv]
    obtain ⟨α, rfl⟩ := exists_eq_prod_X_sub_C a Q₁ h1 hd1
    obtain ⟨β, rfl⟩ := exists_eq_prod_X_sub_C b Q₂ h2 hd2
    have hprod : (∏ i, (X - C (α i))) * ∏ j, (X - C (β j)) = ∏ i, (X - C (Fin.addCases α β i)) := by
      rw [Fin.prod_univ_add]; simp
    rw [hprod] at hsep hroot ⊢
    have htinj : Function.Injective (Fin.addCases α β : Fin (a + b) → ℂ) := separable_prod_X_sub_C_iff.mp hsep
    have hmon : (∏ i, (X - C ((Fin.addCases α β : Fin (a + b) → ℂ) i))).Monic :=
      monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
    have htn : ∀ i, ‖(Fin.addCases α β : Fin (a + b) → ℂ) i‖ = 1 := fun i => hroot _ (by
      rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    have ht0 : ∀ i, (Fin.addCases α β : Fin (a + b) → ℂ) i ≠ 0 := fun i h => by simpa [h] using htn i
    have hα : ∀ i, ‖α i‖ = 1 := fun i => by simpa using htn (Fin.castAdd b i)
    have hβ : ∀ j, ‖β j‖ = 1 := fun j => by simpa using htn (Fin.natAdd a j)
    have hα0 : ∀ i, α i ≠ 0 := fun i h => by simpa [h] using hα i
    have hβ0 : ∀ j, β j ≠ 0 := fun j h => by simpa [h] using hβ j
    have hαinj : Function.Injective α := fun i j h =>
      Fin.castAdd_injective _ _ (htinj (by simpa using h))
    have hβinj : Function.Injective β := fun i j h =>
      Fin.natAdd_injective _ _ (htinj (by simpa using h))
    have hne : ∀ i j, α i ≠ β j := fun i j h => by
      have := htinj (show (Fin.addCases α β : Fin (a + b) → ℂ) (Fin.castAdd b i) = Fin.addCases α β (Fin.natAdd a j) by
        simpa using h)
      have := congrArg Fin.val this
      simp at this
      omega
    rw [chAt_prod_eq_gtChar lam _ htinj ht0]
    simp only [chAt_prod_eq_gtChar _ α hαinj hα0, chAt_prod_eq_gtChar _ β hβinj hβ0]
    rw [resultant_prod α β]
    have hph := GlobalTheory.resultant_phase_unit_circle a b α β hα hβ hne K
    simp only at hph
    rw [show (2 * m + 1 : ℤ) = 2 * K - 1 by rw [hK]; ring, hph]
    set R := ∏ i, ∏ j, (α i - β j) with hRdef

    have hW := weylGT ℂ (a + b) lam.w lam.anti _ ht0
    rw [wden_addCases] at hW
    let α' : Fin a → ℂˣ := fun i => Units.mk0 (α i) (hα0 i)
    let β' : Fin b → ℂˣ := fun j => Units.mk0 (β j) (hβ0 j)
    have hLap := GlobalTheory.weylNumerator_laplace a b α' β' (lam.w + delta (a + b))
    have hLHS : alt (a + b) (lam.w + delta (a + b)) (Fin.addCases α β) =
        (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α' β' i : ℂˣ) ^ (lam.w + delta (a + b)) j : ℂˣ) : ℂ)).det := by
      unfold alt
      congr 1
      ext i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [α', β', Units.val_zpow_eq_zpow_val]
    have hA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin a => ((α' i ^ (lam.w + delta (a + b)) (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det =
          wden a α * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α := by
      intro J
      rw [weylGT ℂ a _ (antitone_select lam (selL J) (selL_strictMono J)) α hα0]
      unfold alt
      congr 1
      ext i k
      simp [α', Units.val_zpow_eq_zpow_val, selL]
    have hB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin b => ((β' i ^ (lam.w + delta (a + b))
            (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det =
          wden b β * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      intro J
      rw [weylGT ℂ b _ (antitone_select lam (selR J) (selR_strictMono J)) β hβ0]
      unfold alt
      congr 1
      ext i k
      simp [β', Units.val_zpow_eq_zpow_val, selR]
    rw [hLHS, hLap] at hW
    simp only [hA, hB] at hW
    rw [← hRdef] at hW
    have hwden : ∀ {c : ℕ} (x : Fin c → ℂ), Function.Injective x → wden c x ≠ 0 := by
      intro c x hx
      unfold wden
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
      split_ifs with h
      · exact sub_ne_zero.mpr (hx.ne h.ne)
      · exact one_ne_zero
    have key : R * gtChar (a + b) lam.w (fun i => Fin.addCases α β i) =
        ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) *
          gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α *
          gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      apply mul_left_cancel₀ (mul_ne_zero (hwden α hαinj) (hwden β hβinj))
      rw [← mul_assoc, hW, Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring
    have hc := congrArg (starRingEnd ℂ) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_pow, map_neg, map_one] at hc
    have hsA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar a (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K)).w α =
          (∏ i, α i) ^ (-(b : ℤ) * K) * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α :=
      fun J => sq_gt_shift a _ _ α hα0
    have hsB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar b (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K)).w β =
          (∏ j, β j) ^ (-(a : ℤ) * K) * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β :=
      fun J => sq_gt_shift b _ _ β hβ0
    have hPα : ‖∏ i, α i‖ = 1 := by rw [norm_prod]; simp [hα]
    have hPβ : ‖∏ j, β j‖ = 1 := by rw [norm_prod]; simp [hβ]
    have cA : (starRingEnd ℂ) ((∏ i, α i) ^ (-(b : ℤ) * K)) = ((∏ i, α i) ^ b) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPα, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    have cB : (starRingEnd ℂ) ((∏ j, β j) ^ (-(a : ℤ) * K)) = ((∏ j, β j) ^ a) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPβ, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    simp only [hsA, hsB, map_mul, cA, cB]
    calc (starRingEnd ℂ) R * ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)
        = ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          ((starRingEnd ℂ) R * (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)) := by ring
      _ = _ := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [_root_.mul_zpow, _root_.mul_zpow]
        ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.Regroup
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.regroup :
    UpperTheory.ConvolutionTheory.G2.Regroup := by
  intro E _ _ _ S hS g hg G
  have hG : ∀ w, G w = ∏ u ∈ hg.toFinset with
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)), g u := by
    intro w
    refine finprod_mem_eq_prod_of_inter_mulSupport_eq g ?_
    ext u
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset,
      Function.mem_mulSupport]
    tauto
  have hne : ∀ w, G w ≠ 1 → ∃ u ∈ hg.toFinset,
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    rw [hG w, Finset.filter_false_of_mem hcon, Finset.prod_empty]
  refine ⟨?_, ?_⟩
  · refine ((hg.toFinset.finite_toSet.biUnion
      (fun u _ => GlobalTheory.QNorm.finite_places_over (maximalRealSubfield E) E (u.under (𝓞 (maximalRealSubfield E)))))).subset ?_
    intro w hw
    obtain ⟨u, hu, huw⟩ := hne w hw
    exact Set.mem_biUnion (Finset.mem_coe.mpr hu) huw.symm
  · choose σ hσS hσ using fun w => (hS w).exists
    have huniq : ∀ u w, w ∈ S →
        u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → σ u = w := by
      intro u w hw h
      exact (hS u).unique ⟨hσS u, hσ u⟩ ⟨hw, h.symm⟩
    have hS' : S ∩ Function.mulSupport G =
        ((hg.toFinset.image σ : Finset (Pl E)) : Set (Pl E)) ∩ Function.mulSupport G := by
      ext w
      simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨hw, hw'⟩
        obtain ⟨u, hu, huw⟩ := hne w hw'
        exact ⟨⟨u, hu, huniq u w hw huw⟩, hw'⟩
      · rintro ⟨⟨u, _, rfl⟩, hw'⟩
        exact ⟨hσS u, hw'⟩
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq G hS', finprod_eq_prod g hg,
      ← Finset.prod_fiberwise_of_maps_to (t := hg.toFinset.image σ) (g := σ)
        (fun u hu => Finset.mem_image_of_mem σ hu) g]
    refine Finset.prod_congr rfl fun w hw => ?_
    obtain ⟨u₀, _, rfl⟩ := Finset.mem_image.mp hw
    rw [hG]
    refine Finset.prod_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
    constructor
    · intro h
      exact huniq u _ (hσS u₀) h
    · intro h
      rw [← h, hσ u]
end

