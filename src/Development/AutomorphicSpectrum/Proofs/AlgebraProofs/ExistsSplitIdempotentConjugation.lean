module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0038
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem exists_addChar_ne_one (C F : Type) [Field C] [IsAlgClosed C] [CharZero C] [Field F]
    [Finite F] : ∃ ψ : AddChar F C, ψ ≠ 1 := by
  have hch : ringChar C ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  let P := AddChar.FiniteField.primitiveChar F C hch
  haveI : NeZero (P.n : ℕ) := ⟨P.n.ne_zero⟩
  haveI : Algebra.IsIntegral C (CyclotomicField P.n C) :=
    IsCyclotomicExtension.integral {(P.n : ℕ)} C _
  let j : CyclotomicField P.n C →ₐ[C] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ψ : AddChar F C :=
    { toFun := fun a => j (P.char a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp [AddChar.map_add_eq_mul] }
  refine ⟨ψ, fun h => ?_⟩
  refine P.prim one_ne_zero ?_
  ext a
  have h1 : j (P.char a) = 1 := by
    have := congrArg (fun χ : AddChar F C => χ a) h
    simpa [ψ] using this
  have h2 : P.char a = 1 := j.toRingHom.injective (by simpa using h1)
  simpa [AddChar.mulShift_apply] using h2

theorem exists_shift_equiv {C F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F C) (hψ : ψ ≠ 1) :
    ∃ e : F ≃ AddChar F C, (∀ h h', e (h + h') = e h * e h') ∧ ∀ h a, e h a = ψ (h * a) :=
  _root_.UpperTheory.Reformulated.B.AddCharacterCount.main ψ hψ

open PositivityTheory.HtPt.Ri in
theorem rank_one_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∃ AD : HopfOrder (C := C) R F, FStable (F := F) AD.carrier ∧ (∀ cN cD, HasColen R v AA.carrier cN → HasColen R v AD.carrier cD → (cN * cD) ^ 2 = v (p : C) ^ (f * p ^ f)) ∧ ∀ τ : MulChar F R, IsFund p τ → ∀ c cD : R, xIdeal AA.carrier τ = Ideal.span {c} → xIdeal AD.carrier τ = Ideal.span {cD} → (v (algebraMap R C c) * v (algebraMap R C cD)) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hcard AA hFS
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one C F
  obtain ⟨e, he, heψ⟩ := exists_shift_equiv ψ hψ
  obtain ⟨AD, hAD, -, hcol⟩ := h1 C R v hv F F e he rfl AA
  have hfun : (fun (h a : F) => e h a) = fun (h a : F) => ψ (h * a) := by
    funext h a; exact heψ h a
  rw [hfun] at hAD
  have hGauss : FStable (F := F) AD.carrier ∧
      ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R,
        xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} →
        v (algebraMap R C c) * v (algebraMap R C cD) =
          v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) := by
    have wsum_one (χ : MulChar F R) {g : F → C} (hg : g ∈ AA.carrier)
        (h0 : wsum χ g 0 = 0) : ∃ r ∈ xIdeal AA.carrier χ, algebraMap R C r = wsum χ g 1 := by
      have hsum : wsum χ g = ∑ a : F, χ⁻¹ a • fun x => g (a • x) := by
        funext x
        simp [wsum, Finset.sum_apply, Algebra.smul_def]
      have hm : wsum χ g ∈ AA.carrier := by
        rw [hsum]
        exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hFS a g hg)
      obtain ⟨r, hr⟩ := AA.le_int hm 1
      refine ⟨r, (mem_xIdeal _ _ _).2 ?_, hr⟩
      convert hm using 1
      funext a
      rw [wsum_eq χ g h0 a, hr, mul_comm]
    refine ⟨?_, ?_⟩
    · intro b g hg
      rw [hAD] at hg ⊢
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
      refine Submodule.mem_map.mpr ⟨fun y => ∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a, ?_, ?_⟩
      · intro f' hf'
        obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * f' (b • a) := hu _ (hFS b f' hf')
        refine ⟨r, ?_⟩
        show _ = ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * f' y
        rw [hr, push_sum]
        rfl
      · funext h
        show ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * ψ (h * y) = ∑ a, u a * ψ ((b • h) * a)
        rw [push_sum b u (fun y => ψ (h * y))]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_eq_mul]
        ring_nf
    · intro χ hχ c cD hc hcD
      set G : C := ∑ a, algebraMap R C (χ⁻¹ a) * ψ a with hG
      have hW : ∀ h : F, ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) = algebraMap R C (χ h) * G := by
        intro h
        have e := wsum_eq χ (fun a => ψ a) (wsum_zero_of_ne hv hχ _) h
        simpa [wsum, G] using e
      have hFt : ∀ t : C, fourier (R := R) (fun h a : F => ψ (h * a)) (fun a => t * algebraMap R C (χ⁻¹ a)) = fun h => t * G * algebraMap R C (χ h) := by
        intro t
        funext h
        show ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = _
        calc ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = t * ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [mul_comm h a]
              ring
          _ = _ := by rw [hW h]; ring
      have hq : v ((Fintype.card F : C) - 1) = 1 := v_card_sub_one p hv hvp
      have hcm : (fun a => algebraMap R C c * algebraMap R C (χ a)) ∈ AA.carrier :=
        (mem_xIdeal _ _ _).mp (by rw [hc]; exact Ideal.mem_span_singleton_self c)
      have hDm : (fun a => algebraMap R C cD * algebraMap R C (χ a)) ∈ AD.carrier :=
        (mem_xIdeal _ _ _).mp (by rw [hcD]; exact Ideal.mem_span_singleton_self cD)
      have key : ∀ t : C, (∃ s : R, algebraMap R C s = t * algebraMap R C c) →
          v t * v G ≤ v (algebraMap R C cD) := by
        intro t ⟨s, hs⟩
        have hu : (fun a => t * algebraMap R C (χ⁻¹ a)) ∈ dualLat AA.carrier := by
          intro g hg
          obtain ⟨r, hr, hr1⟩ := wsum_one χ hg (wsum_zero_of_ne hv hχ g)
          rw [hc] at hr
          obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
          refine ⟨k * s, ?_⟩
          have e : ∑ a, t * algebraMap R C (χ⁻¹ a) * g a = t * wsum χ g 1 := by
            simp only [wsum, mul_one, Finset.mul_sum, mul_assoc]
          show _ = ∑ a, t * algebraMap R C (χ⁻¹ a) * g a
          rw [e, ← hr1, map_mul, map_mul, hs]
          ring
        have hm : (fun h => t * G * algebraMap R C (χ h)) ∈ AD.carrier := by
          rw [hAD, ← hFt]
          exact Submodule.mem_map_of_mem hu
        obtain ⟨s', hs'⟩ : ∃ s' : R, algebraMap R C s' = t * G * algebraMap R C (χ 1) := AD.le_int hm 1
        rw [map_one, map_one, mul_one] at hs'
        have hx : s' ∈ xIdeal AD.carrier χ := by
          rw [mem_xIdeal, hs']
          exact hm
        rw [hcD] at hx
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        rw [← map_mul, ← hs', map_mul, map_mul]
        calc v (algebraMap R C k) * v (algebraMap R C cD) ≤ 1 * v (algebraMap R C cD) := by
              gcongr
              exact hv.map_le_one k
          _ = _ := one_mul _
      rw [hAD] at hDm
      obtain ⟨u, hu, hFu⟩ := Submodule.mem_map.mp hDm
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) := hu _ hcm
      have hinv : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
          G * ∑ a, u a * algebraMap R C (χ a) := by
        have e1 : ∀ h, fourier (R := R) (fun h a : F => ψ (h * a)) u h = ∑ a, u a * ψ (h * a) := fun h => rfl
        simp_rw [e1, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        calc ∑ h, algebraMap R C (χ⁻¹ h) * (u a * ψ (h * a)) = u a * ∑ h, algebraMap R C (χ⁻¹ h) * ψ (h * a) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun h _ => ?_
              ring
          _ = _ := by rw [hW a]; ring
      have hL : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
          algebraMap R C cD * ((Fintype.card F : C) - 1) := by
        rw [hFu, ← sum_inv_mul (C := C) χ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        ring
      have e2 : ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) = algebraMap R C c * ∑ a, u a * algebraMap R C (χ a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [e2] at hr
      have hmain : G * algebraMap R C r = algebraMap R C c * algebraMap R C cD * ((Fintype.card F : C) - 1) := by
        linear_combination G * hr - algebraMap R C c * hinv + algebraMap R C c * hL
      have hup : v (algebraMap R C c) * v (algebraMap R C cD) ≤ v G := by
        have h2 := congrArg v hmain
        rw [map_mul, map_mul, map_mul, hq, mul_one] at h2
        rw [← h2]
        calc v G * v (algebraMap R C r) ≤ v G * 1 := by
              gcongr
              exact hv.map_le_one r
          _ = v G := mul_one _
      refine le_antisymm hup ?_
      by_cases hc0 : algebraMap R C c = 0
      · have hG0 : G = 0 := by
          by_contra hG0
          have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
          have h3 := key ((p : C) * G)⁻¹ ⟨0, by rw [hc0, mul_zero, map_zero]⟩
          have e3 : ((p : C) * G)⁻¹ * G = (p : C)⁻¹ := by field_simp
          rw [← map_mul, e3, map_inv₀] at h3
          have h4 := h3.trans (hv.map_le_one cD)
          have hvp0 : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).mpr hp0
          rw [inv_le_one₀ (pos_iff_ne_zero.mpr hvp0)] at h4
          exact absurd hvp (not_lt.mpr h4)
        rw [hG0, hc0]
        simp
      · have h3 := key (algebraMap R C c)⁻¹ ⟨1, by rw [map_one, inv_mul_cancel₀ hc0]⟩
        rw [map_inv₀] at h3
        have hvc : 0 < v (algebraMap R C c) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hc0)
        rwa [inv_mul_le_iff₀ hvc] at h3
  obtain ⟨hFD, hdual⟩ := hGauss
  refine ⟨AD, hFD, ?_, ?_⟩
  · intro cN cD hN hD
    rw [hcol cN cD hN hD, hcard, Nat.cast_pow, map_pow, ← pow_mul]
  · intro τ hτ c cD hc hcD
    have hord := (_root_.GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hcard τ hτ).1
    by_cases h2 : Fintype.card F = 2
    · have hpf : p ^ f = 2 := hcard.symm.trans h2
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hpf
      have ht : τ = 1 := orderOf_eq_one_iff.1 (by rw [hord]; norm_num)
      subst τ
      let points : Fin 2 → F := ![0, 1]
      have points_injective : Function.Injective points := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [points]
      let indices : Fin 2 ≃ F := Equiv.ofBijective points
        (points_injective.bijective_of_nat_card_le (by simp [Nat.card_eq_fintype_card, h2]))
      have indices_zero : indices 0 = 0 := rfl
      have indices_one : indices 1 = 1 := rfl
      have point_cases (x : F) : x = 0 ∨ x = 1 := by
        obtain ⟨i, rfl⟩ := indices.surjective x
        fin_cases i
        · exact Or.inl indices_zero
        · exact Or.inr indices_one
      have hasColen_of_span (A : HopfOrder (C := C) R F) (d : R)
          (hd : xIdeal A.carrier (1 : MulChar F R) = Ideal.span {d}) :
          HasColen R v A.carrier (v (algebraMap R C d)) := by
        let charVec (s : R) (x : F) := algebraMap R C s * algebraMap R C ((1 : MulChar F R) x)
        have charVec_zero (s : R) : charVec s 0 = 0 := by
          simp [charVec, MulChar.map_nonunit (1 : MulChar F R) not_isUnit_zero]
        have charVec_one (s : R) : charVec s 1 = algebraMap R C s := by
          simp [charVec]
        let M : Matrix (Fin 2) (Fin 2) C := !![1, 0; 1, algebraMap R C d]
        let B := M.submatrix indices.symm indices.symm
        have col_zero : (fun x => B x (indices 0)) = (1 : F → C) := by
          funext x
          obtain ⟨i, rfl⟩ := indices.surjective x
          fin_cases i <;> simp [B, M]
        have col_one : (fun x => B x (indices 1)) = charVec d := by
          funext x
          obtain ⟨i, rfl⟩ := indices.surjective x
          fin_cases i
          · change B (indices 0) (indices 1) = charVec d (indices 0)
            simp only [B, Matrix.submatrix_apply, Equiv.symm_apply_apply]
            simp [M, indices_zero, charVec_zero]
          · change B (indices 1) (indices 1) = charVec d (indices 1)
            simp only [B, Matrix.submatrix_apply, Equiv.symm_apply_apply]
            simp [M, indices_one, charVec_one]
        have one_mem := A.one_mem
        have vec_mem : charVec d ∈ A.carrier := (mem_xIdeal _ _ _).mp
          (hd.symm ▸ Ideal.mem_span_singleton_self d)
        refine ⟨B, le_antisymm ?_ ?_, ?_⟩
        · intro g hg
          obtain ⟨r, hr⟩ := A.le_int hg 0
          obtain ⟨s, hs⟩ := A.le_int hg 1
          have g_sub : g - r • (1 : F → C) = charVec (s - r) := by
            funext x
            rcases point_cases x with rfl | rfl
            · simp [charVec_zero, Algebra.smul_def, hr]
            · simp [charVec_one, Algebra.smul_def, hs, map_sub]
          have hs_mem : s - r ∈ xIdeal A.carrier (1 : MulChar F R) := by
            apply (mem_xIdeal _ _ _).mpr
            change charVec (s - r) ∈ A.carrier
            rw [← g_sub]
            exact A.carrier.sub_mem hg (A.carrier.smul_mem r one_mem)
          rw [hd] at hs_mem
          obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hs_mem
          have g_eq : g = r • (1 : F → C) + k • charVec d := by
            have hvec : charVec (s - r) = k • charVec d := by
              rw [← hk]
              funext x
              simp [charVec, map_mul, Algebra.smul_def, mul_assoc]
            rw [hvec] at g_sub
            rw [add_comm, ← g_sub, sub_add_cancel]
          rw [g_eq]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨indices 0, col_zero⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨indices 1, col_one⟩))
        · rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          obtain ⟨i, rfl⟩ := indices.surjective j
          fin_cases i
          · change (fun x => B x (indices 0)) ∈ A.carrier
            rw [col_zero]
            exact one_mem
          · change (fun x => B x (indices 1)) ∈ A.carrier
            rw [col_one]
            exact vec_mem
        · rw [show B = _ from rfl, Matrix.det_submatrix_equiv_self]
          simp [M, Matrix.det_fin_two]
      have hN := hasColen_of_span AA c hc
      have hD := hasColen_of_span AD cD hcD
      have key := hcol _ _ hN hD
      rw [h2] at key
      have := (pow_left_inj₀ zero_le zero_le two_ne_zero).1 key
      simpa using this
    · have hne : τ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hord
        apply h2
        rw [hcard]
        have : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        omega
      rw [hdual τ hne c cD hc hcD]
      exact _root_.GlobalTheory.CompanionTheory.Ar.GR.gauss_value p C v R hv hvp F f hcard h2 τ hτ ψ hψ

end GlobalTheory.CompanionTheory.Ar.GR
