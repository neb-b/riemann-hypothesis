module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
public import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PrismaticFilteredAtOfIntegersAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0497
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomain
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame.GramSchmidt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sum_left (G : Matrix (Fin r) (Fin r) E) (s : Finset (Fin r)) (f : Fin r → E)
    (w : Fin r → Fin r → E) (y : Fin r → E) :
    herm G (∑ j ∈ s, f j • w j) y = ∑ j ∈ s, f j * herm G (w j) y := by
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, ih]

theorem psi_nonempty (X : Data E r) : ∃ τ, τ ∈ X.Ψ := by
  let τ0 : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  by_cases h : τ0 ∈ X.Ψ
  · exact ⟨τ0, h⟩
  · exact ⟨_, not_not.mp (mt (X.cmType τ0).2 h)⟩

theorem dmin_frm_of_lt (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (i : Fin (r + 1))
    (ho : ∀ j k : Fin r, (j : ℕ) < i → (k : ℕ) < i → j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (by rw [Fin.coe_castLE]; exact a.isLt) (by rw [Fin.coe_castLE]; exact b.isLt)
        (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem herm_self_ne (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : ℕ)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (j : Fin r) (hj : (j : ℕ) < m) : herm X.Gm (v j) (v j) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := psi_nonempty X
  have h1 := (hv ⟨τ, hτ⟩).2 j.succ
  have hd : dmin X.Gm (frm X.Ψ v) ⟨τ, hτ⟩ j.succ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [dmin_frm_of_lt X.Ψ X.Gm v j.succ (fun a b ha hb hab => ho a b
    (by simp only [Fin.val_succ] at ha; omega) (by simp only [Fin.val_succ] at hb; omega) hab)] at hd
  have hf := Finset.prod_ne_zero_iff.mp hd ⟨j, by simp⟩ (Finset.mem_univ _)
  have he : (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) ⟨(j : ℕ), by simp⟩ : Fin r) = j := Fin.ext rfl
  rw [he] at hf
  intro h0
  exact hf (by rw [h0, map_zero])

def gsMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Matrix (Fin r) (Fin r) E :=
  fun j a => (if j = a then 1 else 0) -
    (if a = m ∧ j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0)

def gsStep (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Fin r → Fin r → E :=
  fun a k => ∑ j, v j k * gsMat G v m j a

theorem gsStep_ne (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m a : Fin r)
    (h : a ≠ m) : gsStep G v m a = v a := by
  funext k
  simp [gsStep, gsMat, h]

theorem gsStep_self (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    gsStep G v m m = v m - ∑ j, (if j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0) • v j := by
  funext k
  simp only [gsStep, gsMat, true_and, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem frm_gsStep (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : frm Ψ (gsStep G v m) = rmul (frm Ψ v) (fun τ j a => τ.1 (gsMat G v m j a)) := by
  funext τ k a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [frm, rmul, mat, Matrix.mul_apply, gsStep, map_sum, map_mul]

theorem gsB_mem (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) ∈ Bor Ψ r := by
  have hlow : ∀ a c : Fin r, c < a → gsMat G v m a c = 0 := by
    intro a c hca
    have h1 : a ≠ c := fun h => lt_irrefl _ (h ▸ hca)
    have h2 : ¬ (c = m ∧ a < m) := fun h => lt_asymm hca (h.1 ▸ h.2)
    simp [gsMat, h1, h2]
  intro τ
  refine ⟨?_, fun a c hca => by simp [hlow a c hca]⟩
  have ht : (mat (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) τ).BlockTriangular id := by
    intro a c hca
    simp [mat, hlow a c hca]
  rw [Matrix.det_of_upperTriangular ht]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have hn : ¬ (a = m ∧ a < m) := by rintro ⟨rfl, h⟩; exact lt_irrefl _ h
  simp [mat, gsMat, hn]

theorem herm_gsStep_self (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : Fin r)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (k : Fin r) (hk : k < m) : herm X.Gm (gsStep X.Gm v m m) (v k) = 0 := by
  have hkm : (k : ℕ) < m := hk
  have hne := herm_self_ne X v hv m ho k hkm
  rw [gsStep_self, HermitianTraceFormVanishing.herm_sub_left, herm_sum_left,
    Finset.sum_eq_single k (fun i _ hik => ?_) (fun h => absurd (Finset.mem_univ k) h),
    if_pos hk, div_mul_cancel₀ _ hne, sub_self]
  split_ifs with him
  · rw [ho i k him hkm hik, mul_zero]
  · rw [zero_mul]

theorem exists_ortho_lt (X : Data E r) (u : Fin r → Fin r → E) (hu : frm X.Ψ u ∈ X.dom) :
    ∀ m ≤ r, ∃ v : Fin r → Fin r → E, frm X.Ψ v ∈ X.dom ∧
      ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨u, hu, fun j k hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hv, ho⟩ := ih (Nat.le_of_succ_le hm)
    let mf : Fin r := ⟨m, hm⟩
    refine ⟨gsStep X.Gm v mf, ?_, ?_⟩
    · rw [frm_gsStep]
      exact OrthogonalFrameDomain.rmul_mem_dom X hv (gsB_mem X.Ψ X.Gm v mf)
    · intro j k hj hk hjk
      by_cases hjm : j = mf
      · have hkm : k ≠ mf := fun h => hjk (hjm.trans h.symm)
        have hk' : k < mf := by
          rw [Fin.lt_iff_val_lt_val]
          have : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          show (k : ℕ) < m
          omega
        rw [hjm, gsStep_ne X.Gm v mf k hkm]
        exact herm_gsStep_self X v hv mf ho k hk'
      · by_cases hkm : k = mf
        · have hj' : j < mf := by
            rw [Fin.lt_iff_val_lt_val]
            have : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
            show (j : ℕ) < m
            omega
          rw [hkm, gsStep_ne X.Gm v mf j hjm, ← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm,
            herm_gsStep_self X v hv mf ho j hj', HermitianTraceFormVanishing.cc_zero]
        · rw [gsStep_ne X.Gm v mf j hjm, gsStep_ne X.Gm v mf k hkm]
          have hj' : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
          have hk' : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          exact ho j k (by omega) (by omega) hjk

theorem exists_ortho_frm (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E) :
    GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E,
      (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  intro hu
  obtain ⟨v, hv, ho⟩ := exists_ortho_lt X u hu r le_rfl
  exact ⟨v, fun j k hjk => ho j k j.isLt k.isLt hjk, hv⟩

end

end GlobalTheory.OrthoFrame.GramSchmidt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem existsUnique_padic_of_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O,
      WittVector.frobenius a = WittVector.frobenius (xi ε) * a →
        ∃! c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p := by
    simpa [zeta] using hε 1
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain (Ainf p O) := GlobalTheory.Sandwich.Model.isDomain_Ainf hv
  have hμ : Sandwich.mu ε ≠ 0 := GlobalTheory.Sandwich.Model.mu_ne_zero (hε := h1) hv
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.Prism.exists_padic_of_eigen h1 ha
  have hinj : Function.Injective (ofPadic p O) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact ⟨c, hc, fun c' hc' => hinj (mul_right_cancel₀ hμ (hc'.trans hc.symm))⟩

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetPairingNeZero
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_coset_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  intro G Γ _ _ _ _ φ s hp hs X hX Y hY z hz hnd hcos
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, -, -, hfour⟩ := GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic G Γ φ s hgen _ hζ
  obtain ⟨h1, h2⟩ := hfour X Y
  have hvirt : ∀ a : ℕ, (fun x => Y x * (η x : ℂ) ^ a) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    intro a
    obtain ⟨hmul, -, -, -, hlin⟩ := GlobalTheory.BI.virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
    have := hmul Y hY _ (hlin (η ^ a))
    convert this using 1
  have hm : ∀ a : ℕ, ∃ m : ℤ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = m * (Nat.card (G ⋊[φ] Γ) : ℂ) :=
    fun a => GlobalTheory.BI.finsum_mul_star_virt_int _ X _ hX (hvirt a)
  choose m hm using hm
  have hN : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hl : (Nat.card Γ : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [hm, hN, hcos, hz, mul_zero] at h1 h2
  have hsum : ∑ i : Fin (Nat.card Γ), (m i.val : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ i.val = 0 := by
    have h3 : ∑ a ∈ Finset.range (Nat.card Γ), (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a * (↑(m a) * ↑(Nat.card G * Nat.card Γ))
        = (∑ a ∈ Finset.range (Nat.card Γ), (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a) * ((Nat.card G : ℂ) * Nat.card Γ) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; push_cast; ring
    rw [h3] at h2
    rw [← Finset.sum_range (fun a => (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a)]
    have := h2.symm
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (mul_ne_zero hG hl)
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hζ (fun i => m i.val)).1 hsum
  have hconst : ∀ a ∈ Finset.range (Nat.card Γ), m a = m 0 := by
    intro a ha
    exact hall ⟨a, Finset.mem_range.1 ha⟩ ⟨0, hp.pos⟩
  rw [Finset.sum_congr rfl (fun a ha => by rw [hconst a ha])] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hz' : (z : ℂ) = (m 0 * Nat.card Γ : ℤ) := by
    push_cast at h1 ⊢
    have h4 : (Nat.card Γ : ℂ) * (Nat.card G : ℂ) * ((z : ℂ) - m 0 * Nat.card Γ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero hl hG)
    · exact sub_eq_zero.1 h
  exact hnd ⟨m 0, by rw [mul_comm]; exact_mod_cast hz'⟩

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h_zero_pullback_twist_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'), IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' → (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) → ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.h_zero_pull_bijective) | (exact GlobalTheory.EtC.h_zero_pull_bijective) | (intros; apply GlobalTheory.EtC.h_zero_pull_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinShiftedLatticeFourier
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def shearSub {F : Type} [Field F] (x : F) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v 0, v 1 - v 0 * x]
  invFun v := ![v 0, v 1 + v 0 * x]
  map_add' v w := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

theorem shearSub_zero {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 0 = v 0 := rfl

theorem shearSub_one {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 1 = v 1 - v 0 * x := rfl

theorem hasSum_split_shift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (w : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → w ∈ upperHalf F → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * qPow ξ w) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x w hk hc hw
  have hw' : (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) ∈ upperHalf F := by
    intro i
    simpa using hw i
  have hg : gval k (split 𝔞 𝔟 x) w 1 = gval k (split 𝔞 𝔟 0) (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 := by
    have := _root_.GlobalTheory.HilbFam.gval_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 0) (shearSub x) w 1
      (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 1 hk (fun v ↦ by
        change (_ ∧ _) ↔ (_ ∧ _)
        rw [shearSub_zero, shearSub_one, mul_zero, sub_zero]) (fun i ↦ by simp) (fun v i ↦ by
        simp only [coord, shearSub_zero, shearSub_one, Pi.one_apply, map_sub, map_mul]
        push_cast; ring)
    simpa using this
  have h := hc.2.2.2 _ hw'
  rw [hg]
  convert h using 2 with ξ
  rw [mul_assoc]
  congr 1
  unfold eTr qPow
  rw [← Complex.exp_add, ← _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F (ξ * x), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul]; push_cast; ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchangeStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_integral_theta_mellin_interchange : ∀ (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ), (∀ j, ‖a j‖ ≤ C) → ∀ (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, p y ≤ 1) → (∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j))) → Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖) → HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y) (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HeckeMellin.hasSum_integral_theta | exact GlobalTheory.HeckeMellin.hasSum_integral_theta | (intros; apply GlobalTheory.HeckeMellin.hasSum_integral_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSl2IntSmul
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.JetModular

def rowEquiv (F : Type) [Field F] (γ : SL(2, ℤ)) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  LinearEquiv.ofLinear
    (Matrix.vecMulLinear ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (Matrix.vecMulLinear (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)))
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, LinearMap.id_apply]
      rw [← Matrix.map_mul_intCast, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma iterD_const_mul {I : Type} [Fintype I] [DecidableEq I] (u : List I)
    (h : (I → ℂ) → ℂ) (A : ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z ↦ A * h z) z =
      A * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u h z := by
  simpa using _root_.GlobalTheory.HilbFam.iterD_const_mul_reindex I I (Equiv.refl I) u h A z

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma mem_iff_sl2_equiv_mem_mulMat (F : Type) [Field F] [NumberField F] (L : _root_.GlobalTheory.HilbFam.Lat F)
    (γ : SL(2, ℤ)) (x : Fin 2 → F) :
    x ∈ L ↔ _root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x ∈ _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rw [Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [(_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ).injective (a₁ := y) (a₂ := x) hxy] at hy

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma embeddingCoord_sl2_smul_lemma_3 (F : Type) [Field F] [NumberField F] (γ : SL(2, ℤ)) (τ : ℍ)
    (c t : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Fin 2 → F) (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord (fun i ↦ ((γ • τ : ℍ) : ℂ) + z i * (c * ((γ • τ : ℍ) : ℂ) + t)) (fun i ↦ 1 + z i * c) x i =
      (fun _ ↦ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1))⁻¹) i *
      _root_.GlobalTheory.HilbFam.coord
        (fun i ↦ (τ : ℂ) + z i * ((c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) * τ + t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2))
        (fun i ↦ 1 + z i * (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)))
        (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x) i := by
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  simp only [_root_.GlobalTheory.HilbFam.coord, _root_.GlobalTheory.HilbFam.JetModular.rowEquiv, LinearEquiv.ofLinear_apply,
    Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, map_add,
    map_mul, map_intCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
    specialLinearGroup_apply, coe_mk, eq_intCast]
  set j := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj_def
  have hji : j * j⁻¹ = 1 := mul_inv_cancel₀ hj
  rw [div_eq_mul_inv]
  linear_combination (-(((i (x 0) : ℝ) : ℂ) * z i * t + ((i (x 1) : ℝ) : ℂ) * (1 + z i * c))) * hji -
    ((i (x 0) : ℝ) : ℂ) * z i * t * j * j⁻¹ * hdet

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma card_realEmbeddings_eq_finrank (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun φ : F →+* ℝ ↦ Complex.ofRealHom.comp φ) ⟨?_, ?_⟩
  · intro φ ψ h
    ext x
    simpa using congrArg (fun f : F →+* ℂ ↦ f x) h
  · intro ψ
    have hψ : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    exact ⟨hψ.embedding, by ext x; simp [hψ.coe_embedding_apply]⟩


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
theorem _root_.GlobalTheory.HilbFam.JetModular.jet_smul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (τ : ℍ) (c t : ℂ), Even k → _root_.GlobalTheory.HilbFam.jet k L κ ((γ • τ : ℍ) : ℂ) c t = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ (k * Module.finrank ℚ F) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ τ (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) (t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2) := by
  intro F _ _ _ k L κ γ τ c t hk
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← iterD_const_mul]
  congr 1
  funext z
  rw [_root_.GlobalTheory.HilbFam.gval_linear_change F k L (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ))
    (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ) _ _ _ _ (fun _ ↦ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)⁻¹) hk
    (mem_iff_sl2_equiv_mem_mulMat F L γ) (fun _ ↦ inv_ne_zero hj)
    (fun x i ↦ embeddingCoord_sl2_smul_lemma_3 F γ τ c t z x i)]
  rw [Finset.prod_const, Finset.card_univ, card_realEmbeddings_eq_finrank]
  simp only [inv_pow, inv_inv, ← pow_mul, mul_comm (Module.finrank ℚ F) k]
  ring

end GlobalTheory.HilbFam.JetModular
end
end

