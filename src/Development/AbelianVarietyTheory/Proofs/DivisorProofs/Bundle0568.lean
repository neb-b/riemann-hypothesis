module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import GroundTheory.Brauer.BaseChangeCSA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyEqOfAevalOfLinearIndependent
section
open scoped TensorProduct
open Polynomial

namespace GlobalTheory.SkNoFactor

theorem minpoly_eq_of_aeval_of_linearIndependent {L A : Type} [Field L] [Ring A] [Algebra L A]
    (p : L[X]) (y : A) (hm : p.Monic) (hy : aeval y p = 0)
    (hind : ∀ c : Fin p.natDegree → L, ∑ j, c j • y ^ (j : ℕ) = 0 → c = 0) : minpoly L y = p := by
  have hi : IsIntegral L y := ⟨p, hm, by rwa [← aeval_def]⟩
  have hdvd : minpoly L y ∣ p := minpoly.dvd L y hy
  have hle : p.natDegree ≤ (minpoly L y).natDegree := by
    by_contra hlt
    push_neg at hlt
    have hsum := aeval_eq_sum_range' hlt y
    rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly L y).coeff i • y ^ i)] at hsum
    have hc := hind (fun i => (minpoly L y).coeff i) hsum.symm
    apply minpoly.ne_zero hi
    ext i
    rw [coeff_zero]
    by_cases h : i < p.natDegree
    · exact congrFun hc ⟨i, h⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hdvd hle
  rw [this, hm.leadingCoeff, C_1, one_mul]

theorem minpoly_one_tmul {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

theorem exists_unit_conj_baseChange : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B]
    [FiniteDimensional F B] (n : ℕ), Module.finrank F B = n ^ 2 → ∀ (x₀ : B) (x : S ⊗[ℚ] B),
    (minpoly F x₀).Separable → (minpoly F x₀).natDegree = n →
    (∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * x ^ i = 0) →
    (∀ c : Fin n → S ⊗[ℚ] F, ∑ j, Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) (c j) *
      x ^ (j : ℕ) = 0 → c = 0) →
    ∃ g : (S ⊗[ℚ] B)ˣ, (g : S ⊗[ℚ] B) * ((1 : S) ⊗ₜ[ℚ] x₀) = x * g := by
  intro S F B _ _ _ _ _ _ _ _ _ _ _ _ n hn x₀ x hsep hdeg hP hind
  classical
  obtain ⟨ι, _, L, _, _, _, Φ, ψ, hΦ1, hΦ2⟩ := GlobalTheory.T.tensor_rat_algebra_decomp_factorwise S F B
  have hcomp : ∀ i, ∃ u : (L i ⊗[F] B)ˣ, (u : L i ⊗[F] B) * ((1 : L i) ⊗ₜ[F] x₀) = Φ x i * u := by
    intro i
    haveI : Infinite (L i) := Infinite.of_injective (Nat.cast : ℕ → L i) Nat.cast_injective
    have hn' : Module.finrank (L i) (L i ⊗[F] B) = n ^ 2 := by rw [Module.finrank_baseChange, hn]
    have h0 : minpoly (L i) ((1 : L i) ⊗ₜ[F] x₀) = (minpoly F x₀).map (algebraMap F (L i)) :=
      minpoly_one_tmul (L i) x₀
    have hmonic : ((minpoly F x₀).map (algebraMap F (L i))).Monic :=
      (minpoly.monic (IsIntegral.of_finite F x₀)).map _
    have hdegm : ((minpoly F x₀).map (algebraMap F (L i))).natDegree = n := by rw [natDegree_map, hdeg]
    have hcoef : ∀ c : F, Φ ((1 : S) ⊗ₜ[ℚ] algebraMap F B c) i =
        algebraMap (L i) (L i ⊗[F] B) (algebraMap F (L i) c) := by
      intro c
      rw [hΦ1]
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.TensorProduct.one_def]
    have hy : aeval (Φ x i) ((minpoly F x₀).map (algebraMap F (L i))) = 0 := by
      have := congrArg (fun w => Φ w i) hP
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_pow, map_zero, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply,
        Pi.zero_apply, hcoef] at this
      rw [aeval_eq_sum_range' (n := n + 1) (by rw [hdegm]; omega), ← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_map, Algebra.smul_def]
    have hli : ∀ c : Fin ((minpoly F x₀).map (algebraMap F (L i))).natDegree → L i,
        ∑ j, c j • Φ x i ^ (j : ℕ) = 0 → c = 0 := by
      rw [hdegm]
      intro c hc
      have hz := hind (fun j => ψ.symm (Pi.single i (c j))) (by
        apply Φ.injective
        rw [map_zero]
        funext k
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, map_pow, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hΦ2,
          RingEquiv.apply_symm_apply, Pi.zero_apply]
        by_cases hk : k = i
        · subst hk
          simpa [Pi.single_eq_same, Algebra.smul_def] using hc
        · simp [Pi.single_eq_of_ne hk])
      funext j
      have := congrArg (fun w => ψ (w j) i) hz
      simpa using this
    have hmin : minpoly (L i) (Φ x i) = minpoly (L i) ((1 : L i) ⊗ₜ[F] x₀) := by
      rw [h0]; exact minpoly_eq_of_aeval_of_linearIndependent _ _ hmonic hy hli
    exact GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq (L i) (L i ⊗[F] B) n hn' _ _
      (by rw [h0]; exact hsep.map) (by rw [h0, hdegm]) hmin
  choose u hu using hcomp
  let v : ((i : ι) → L i ⊗[F] B)ˣ := MulEquiv.piUnits.symm u
  refine ⟨Units.map Φ.symm.toMonoidHom v, ?_⟩
  apply Φ.injective
  rw [map_mul, map_mul]
  funext i
  simp [v, hΦ1, hu i]

end GlobalTheory.SkNoFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultSharpOfPlaceBound
section
noncomputable section

namespace GlobalTheory.FinGL.MultSharpPf

open GlobalTheory.FinGL Formalism.L2.DIV Module NumberField GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

def PlaceBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ →
    ∀ ρ k : ℕ, 1 ≤ k → ρ + k + 1 ≤ r → r ≤ Fintype.card F →
      (Fintype.card F : ℝ) ^ k * (1 - 1 / (Fintype.card F : ℝ)) ≤ (nPos ψ (parInd b σ) ρ k : ℝ) ∧
      (nPos ψ (parInd b σ) ρ k : ℝ) ≤ (Fintype.card F : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Fintype.card F : ℝ))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem card_mul_finrank_eig {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (P : Subgroup G) [Fintype P] (ψ : G → ℂ) (h1 : ψ 1 = 1)
    (hm : ∀ x ∈ P, ∀ y ∈ P, ψ (x * y) = ψ x * ψ y) :
    (Fintype.card P : ℂ) * (finrank ℂ (eig τ (P : Set G) ψ) : ℂ) =
      ∑ h : P, LinearMap.trace ℂ V (τ h) * (ψ h)⁻¹ := by
  have hc : (Fintype.card P : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h0 : ∀ x ∈ P, ψ x ≠ 0 := fun x hx e => by
    have := hm x hx x⁻¹ (P.inv_mem hx)
    rw [mul_inv_cancel, h1, e, zero_mul] at this
    exact one_ne_zero this
  set e : V →ₗ[ℂ] V := (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (ψ h)⁻¹ • (τ h : V →ₗ[ℂ] V) with he
  have hp : LinearMap.IsProj (eig τ (P : Set G) ψ) e := by
    constructor
    · intro v
      rw [mem_eig]
      intro g hg
      have hg' : g ∈ P := hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul, map_sum]
      rw [smul_comm (ψ g)]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg'⟩ : P)) _ _ fun x => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hm g hg' x x.2, smul_smul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (h0 g hg'), one_mul]
    · intro v hv
      rw [mem_eig] at hv
      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl (g := fun _ => v) fun x _ => by
        rw [hv x x.2, smul_smul, inv_mul_cancel₀ (h0 x x.2), one_smul]]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hp.trace, he, map_smul, map_sum, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

variable {E : Type} [Field E] [NumberField E]

def piEquiv {Pg : Finset (Pl E)} {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) :
    (Subgroup.pi Set.univ Hl : Subgroup (G0 Pg r)) ≃ ∀ PP : ↥Pg, Hl PP where
  toFun x PP := LevelP.prj Hl PP x
  invFun y := ⟨fun PP => y PP, fun PP _ => (y PP).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem levelMult_ofLocal {K : Type} [Field K] (s : K →+* ℂ) {Pg : Finset (Pl E)} {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) [∀ PP, Fintype (Hl PP)] (cl : ∀ PP : ↥Pg, Hl PP →* Kˣ)
    (χ : G0 Pg r → K) (θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ) (hχ : ∀ x, s (χ x) = ∏ PP : ↥Pg, θ PP (x PP))
    (n : ↥Pg → ℕ)
    (hn : ∀ PP, (Fintype.card (Hl PP) : ℂ) * (n PP : ℂ) = ∑ h : Hl PP, θ PP h * (s (cl PP h : K))⁻¹) :
    levelMult (LevelP.ofLocal Hl cl) χ = ((∏ PP, n PP : ℕ) : K) := by
  classical
  apply s.injective
  unfold levelMult
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_inv₀, map_natCast, map_natCast, map_sum]
  have hcard : Nat.card (LevelP.ofLocal Hl cl).H = ∏ PP, Fintype.card (Hl PP) := by
    rw [← Fintype.card_pi, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (piEquiv Hl)
  have hne : (∏ PP, (Fintype.card (Hl PP) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun PP _ => by exact_mod_cast Fintype.card_ne_zero
  rw [hcard, Nat.cast_prod, Nat.cast_prod, inv_mul_eq_iff_eq_mul₀ hne, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun PP _ => hn PP, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine @Fintype.sum_equiv _ _ _ (_) _ _ (piEquiv Hl) _ _ fun x => ?_
  rw [map_mul, hχ, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, map_inv₀]
  congr 2
  show s ((((∏ PP : ↥Pg, (cl PP).comp (LevelP.prj Hl PP)) x : Kˣ)) : K) = _
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, map_prod]
  rfl

theorem edgeSum_sup_eq {κ : Type} [CommRing κ] {r k : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unipCol κ r 0 k) :
    edgeSum supEdge g = edgeSum (symEdge 0 k) g := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : supEdge i j <;> by_cases h2 : symEdge 0 k i j
  · rw [if_pos h1, if_pos h2]
  · rw [if_pos h1, if_neg h2]
    unfold supEdge at h1
    unfold symEdge at h2
    exact hg.2 i j (Nat.zero_le _) (by omega) (by omega)
  · unfold supEdge at h1
    unfold symEdge at h2
    omega
  · rw [if_neg h1, if_neg h2]

theorem addCharHom_sym {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r ρ k : ℕ} (ψ : AddChar κ K) (h : unipSym κ r ρ k) :
    (addCharHom ψ (symHom κ r ρ k) h : K) = ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ)) := rfl

theorem addCharHom_first {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r k : ℕ} (ψ : AddChar κ K) (h : unipCol κ r 0 k) :
    ((addCharHom ψ (supHom κ r)).comp (Subgroup.inclusion (unipCol_le r 0 k)) h : K) =
      ψ (edgeSum (symEdge 0 k) (h : GL (Fin r) κ)) := by
  rw [← edgeSum_sup_eq h.2]
  rfl

theorem place (H : PlaceBound) {κ : Type} [Field κ] [Finite κ] {K : Type} [Field K] (s : K →+* ℂ) (ψ : AddChar κ K)
    (hψ : ψ ≠ 1) {r ρ k : ℕ} (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hq : r ≤ Nat.card κ) (θ : GL (Fin r) κ → ℂ)
    (hθ : IsCuspProdChar θ) [Fintype (unipSym κ r ρ k)] :
    ∃ n : ℕ, (Fintype.card (unipSym κ r ρ k) : ℂ) * (n : ℂ) =
        ∑ h : unipSym κ r ρ k, θ h * (s (ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ))))⁻¹ ∧
      (Nat.card κ : ℝ) ^ k * (1 - 1 / (Nat.card κ : ℝ)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (Nat.card κ : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Nat.card κ : ℝ)) := by
  obtain ⟨d, b, σ, hσ, hθ⟩ := hθ
  letI : Fintype κ := Fintype.ofFinite κ
  set φ : AddChar κ ℂ := s.toMonoidHom.compAddChar ψ with hφ
  have hφa : ∀ x, φ x = s (ψ x) := fun _ => rfl
  have hφ1 : φ ≠ 1 := fun e => hψ (by
    ext x
    apply s.injective
    rw [← hφa, e]; simp)
  rw [Nat.card_eq_fintype_card] at hq ⊢
  refine ⟨nPos φ (parInd b σ) ρ k, ?_, H κ φ hφ1 r _ b σ hσ ρ k hk hr hq⟩
  unfold nPos
  rw [card_mul_finrank_eig (parInd b σ) (unipSym κ r ρ k) (fun g => φ (edgeSum (symEdge ρ k) g))]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [hθ]; rfl
  · have := (symHom κ r ρ k).map_one
    have h2 : edgeSum (symEdge ρ k) (1 : GL (Fin r) κ) = 0 := this
    simp only [h2, AddChar.map_zero_eq_one]
  · intro x hx y hy
    have := (symHom κ r ρ k).map_mul ⟨x, hx⟩ ⟨y, hy⟩
    have h2 : edgeSum (symEdge ρ k) (x * y) = edgeSum (symEdge ρ k) x + edgeSum (symEdge ρ k) y := this
    simp only [h2, AddChar.map_add_eq_mul]

theorem places (H : PlaceBound) {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (f g r ρ k c : ℕ) (hc : c = ρ + k)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (hf : Pg.card = 2 * f) (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hg : 0 < g)
    (hfg : 4 * f * r ≤ g) (hq : ∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) (hψ : IsGenericPsi Pg ψ)
    (cl : ∀ PP : ↥Pg, unipCol (kP PP.1) r ρ c →* Kˣ)
    (hcl : ∀ PP h, (cl PP h : K) = ψ PP.1 (edgeSum (symEdge ρ k) (h : GL (Fin r) (kP PP.1))))
    (χ : G0 Pg r → K) (hχ : IsProdCuspChar s Pg r χ) :
    MultNear (LevelP.ofLocal (fun PP => unipCol (kP PP.1) r ρ c) cl) χ (nbar Pg k) (8 * f * r / g) := by
  subst hc
  obtain ⟨θ, hθ, hχ⟩ := hχ
  have hfin : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => finite_kP PP.1
  letI : ∀ PP : ↥Pg, Fintype (unipCol (kP PP.1) r ρ (ρ + k)) := fun PP => Fintype.ofFinite _
  have hrq : ∀ PP : ↥Pg, r ≤ Nat.card (kP PP.1) := fun PP => by
    have h1 : 0 < Pg.card := Finset.card_pos.2 ⟨PP.1, PP.2⟩
    have h2 : 1 ≤ 4 * f := by omega
    exact le_trans (le_trans (Nat.le_mul_of_pos_left r h2) hfg) (hq PP.1 PP.2)
  have hloc := fun PP : ↥Pg => @place H (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) (hfin PP) K _ s (ψ PP.1)
    (hψ PP.1 PP.2) r ρ k hk hr (hrq PP) (θ PP) (hθ PP) (this PP)
  choose n hn hb using hloc
  refine ⟨∏ PP, n PP, levelMult_ofLocal s _ cl χ θ hχ n fun PP => ?_, ?_⟩
  · simp only [hcl]
    exact hn PP
  · have := Formalism.BranchingDeterminantCap.multiplicity_product ↥Pg (fun PP => (Nat.card (kP PP.1) : ℝ)) (fun PP => (n PP : ℝ)) k f r g
      (by rw [Fintype.card_coe, hf]; push_cast; rfl) (by exact_mod_cast (by omega : 1 ≤ r)) (by exact_mod_cast hg)
      (fun PP => by exact_mod_cast hq PP.1 PP.2) (by exact_mod_cast hfg) hb
    have e : (nbar Pg k : ℝ) = ∏ PP : ↥Pg, (Nat.card (kP PP.1) : ℝ) ^ k := by
      unfold nbar
      rw [← Finset.prod_coe_sort Pg]; push_cast; rfl
    rw [e, Nat.cast_prod, abs_le]
    constructor <;> linarith [this.1, this.2]

theorem multSharp_of_placeBound (H : PlaceBound) : MultSharp := by
  intro E _ _ K _ _ s Pg f g r ρ k ψ hf hk hr hg hfg hq hψ χ hχ
  constructor
  · unfold PsharpSym
    exact places H s Pg f g r ρ k (ρ + k) rfl ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) r ρ k)) (fun PP h => addCharHom_sym _ h) χ hχ
  · unfold Psharp
    exact places H s Pg f g r 0 k k (Nat.zero_add k).symm ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (Subgroup.inclusion (unipCol_le r 0 k)))
      (fun PP h => addCharHom_first _ h) χ hχ

end GlobalTheory.FinGL.MultSharpPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.RedRules

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (σ : Type)

theorem inj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
  IsFractionRing.injective _ _

theorem coeff_smul' (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (α : σ →₀ ℕ) :
    coeff α (r • f) = algebraMap _ (Fr p k) r * coeff α f := by
  change r • coeff α f = _
  rw [Algebra.smul_def]

theorem intBy_one_iff (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨fun α => WittVector.constantCoeff (w α), fun α => ⟨w α, ?_, rfl⟩⟩
    rw [hw α, one_mul]
  · rintro ⟨g, hg⟩ α
    obtain ⟨w, hw, -⟩ := hg α
    exact ⟨w, by rw [one_mul, hw]⟩

theorem red_unique (f : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f g') : g = g' := by
  ext α
  obtain ⟨w, hw, hg⟩ := h α
  obtain ⟨w', hw', hg'⟩ := h' α
  have : w = w' := inj p k (hw.symm.trans hw')
  rw [← hg, ← hg', this]

theorem red_lift (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := fun α =>
  ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

theorem red_add_sub (f f' : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f' g') : Red p (f + f') (g + g') ∧ Red p (f - f') (g - g') := by
  constructor
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w + w', by rw [map_add (f := _), map_add (f := _), hw, hw'], by rw [map_add (f := _), map_add (f := _), hg, hg']⟩
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w - w', by rw [map_sub, map_sub, hw, hw'], by rw [map_sub, map_sub, hg, hg']⟩

theorem red_smul (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (g : MvPowerSeries σ k)
    (h : Red p f g) : Red p (r • f) (WittVector.constantCoeff r • g) := by
  intro α
  obtain ⟨w, hw, hg⟩ := h α
  refine ⟨r * w, ?_, ?_⟩
  · rw [coeff_smul', hw, map_mul]
  · rw [map_mul, hg, MvPowerSeries.coeff_smul]

theorem constantCoeff_p_mul (v : WittVector p k) :
    WittVector.constantCoeff ((p : WittVector p k) * v) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem exists_p_mul [PerfectRing k p] (w : WittVector p k) (hw : WittVector.constantCoeff w = 0) :
    ∃ v, w = (p : WittVector p k) * v := by
  by_cases h0 : w = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  cases m with
  | zero =>
    rw [pow_zero, one_mul, WittVector.constantCoeff_apply] at hw
    exact absurd hw hb
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [pow_succ, mul_comm _ (p : WittVector p k), mul_assoc]⟩

theorem intBy_p_iff [PerfectRing k p] (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ p ↔ Red p f 0 := by
  constructor
  · intro hf α
    obtain ⟨v, hv⟩ := hf α
    exact ⟨_, hv, by rw [constantCoeff_p_mul, map_zero]⟩
  · intro hf α
    obtain ⟨w, hw, h0⟩ := hf α
    rw [map_zero] at h0
    obtain ⟨v, rfl⟩ := exists_p_mul p k w h0
    exact ⟨v, hw⟩

theorem intBy_iff (c : WittVector p k) (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨(fun α => algebraMap _ (Fr p k) (w α) : MvPowerSeries σ (Fr p k)), fun α => ⟨w α, by rw [one_mul]; rfl⟩, ?_⟩
    ext α
    rw [hw α, map_mul]
    exact (coeff_smul' p k σ c (fun α => algebraMap _ (Fr p k) (w α)) α).symm
  · rintro ⟨g, hg, rfl⟩ α
    obtain ⟨w, hw⟩ := hg α
    exact ⟨w, by rw [coeff_smul', hw, one_mul, map_mul]⟩

end GlobalTheory.Katz.RedRules

open GlobalTheory.Katz.RedRules in
theorem GlobalTheory.Katz.red_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  intro p _ k _ _ _ σ
  exact ⟨intBy_one_iff p k σ, red_unique p k σ, red_lift p k σ, red_add_sub p k σ, red_smul p k σ,
    intBy_p_iff p k σ, intBy_iff p k σ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosets
section
namespace GlobalTheory.LFun

theorem norm_le_card_of_heckeVec_eq_smul :
    ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) →
      (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) →
      {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x →
      ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  intro G _ K V _ _ ρ Bf hsym hpos hinv h x c hh hfin hx hc
  classical
  have hnn : ∀ y, 0 ≤ (Bf y y).re := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by rw [hsym x y]; simp
      re_inner_nonneg := hnn
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have cs : ∀ y, ‖Bf x y‖ * ‖Bf y x‖ ≤ (Bf x x).re * (Bf y y).re :=
    fun y => @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ core x y
  have hr : 0 < (Bf x x).re := hpos x hx
  have hb : ∀ g, ‖Bf x (ρ g x)‖ ≤ (Bf x x).re := by
    intro g
    have h1 := cs (ρ g x)
    rw [hinv, hsym x (ρ g x), RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (Bf x (ρ g x))]
  have hxx : ‖Bf x x‖ = (Bf x x).re := by
    have e : (starRingEnd ℂ) (Bf x x) = Bf x x := (hsym x x).symm
    rw [RCLike.conj_eq_iff_re] at e
    rw [← e]
    simp [abs_of_pos hr]
  set S := hfin.toFinset
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ S := by
    intro q hq
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ S, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  have key : c * Bf x x = ∑ q ∈ S, h q.out * Bf x (ρ q.out x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← smul_eq_mul, ← map_smul, ← hc, hsum, map_sum]
    simp
  have hcard : Nat.card {q : G ⧸ K // h q.out ≠ 0} = S.card :=
    Nat.card_eq_card_finite_toFinset hfin
  have hle : ‖c‖ * (Bf x x).re ≤ (S.card : ℝ) * (Bf x x).re := by
    calc ‖c‖ * (Bf x x).re = ‖c * Bf x x‖ := by rw [norm_mul, hxx]
      _ = ‖∑ q ∈ S, h q.out * Bf x (ρ q.out x)‖ := by rw [key]
      _ ≤ ∑ q ∈ S, ‖h q.out * Bf x (ρ q.out x)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S, (Bf x x).re := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        calc ‖h q.out‖ * ‖Bf x (ρ q.out x)‖ ≤ 1 * (Bf x x).re :=
              mul_le_mul (hh _) (hb _) (norm_nonneg _) zero_le_one
          _ = (Bf x x).re := one_mul _
      _ = (S.card : ℝ) * (Bf x x).re := by simp
  rw [hcard]
  exact le_of_mul_le_mul_right hle hr

end GlobalTheory.LFun
end

