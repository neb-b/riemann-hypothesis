module

public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclosedeq_weight_sum {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) :
    ∑ s : Fin n, Finsupp.weight (colW r n) m s = Finsupp.weight (1 : Fin r × Fin n → ℕ) m := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [colW, Pi.single_apply]

theorem lclosedeq_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by
  classical
  have hS : Set.Finite {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin r × Fin n => ν v.2))).subset ?_
    intro d hd
    have hd' : Finsupp.weight (colW r n) d = ν := hd
    show d ≤ _
    rw [Finsupp.le_def]
    intro v
    have h1 : d v ≤ Finsupp.weight (colW r n) d v.2 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      by_cases hv : v ∈ d.support
      · refine le_trans ?_ (Finset.single_le_sum
          (f := fun u => (d u • colW r n u) v.2) (fun _ _ => Nat.zero_le _) hv)
        simp [colW]
      · have : d v = 0 := by
          by_contra h
          exact hv (Finsupp.mem_support_iff.mpr h)
        rw [this]
        exact Nat.zero_le _
    rw [hd'] at h1
    simpa using h1
  haveI := hS.to_subtype
  haveI hfd : FiniteDimensional ℚ (weightedHomogeneousSubmodule ℚ (colW r n) ν) := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp
      {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν}).symm
  exact Submodule.finiteDimensional_of_le (fun f hf => (Submodule.mem_inf.mp hf).1)

def lclosedeq_B {σ : Type} (h2 : FockQPos) (h3 : FockQBilin) :
    LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => (h3 σ f f' g 1).1)
    (fun c f g => by rw [(h3 σ f f g c).2, smul_eq_mul])
    (fun f g g' => by rw [(h2 σ f _).1, (h3 σ g g' f 1).1, (h2 σ g f).1, (h2 σ g' f).1])
    (fun c f g => by rw [(h2 σ f _).1, (h3 σ g g f c).2, (h2 σ g f).1, smul_eq_mul])

theorem closedEqNabla_of (h1 : HWInClosed) (h2 : FockQPos) (h3 : FockQBilin) (h4 : FockQRowDivAdj) :
    ClosedEqNabla := by
  intro r n hn ν hν M hMV hMc hhw
  have hfdV : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := lclosedeq_fd r n ν
  have hfdM : FiniteDimensional ℚ M := Submodule.finiteDimensional_of_le hMV
  let B := lclosedeq_B (σ := Fin r × Fin n) h2 h3
  have hB : ∀ f g, B f g = fockQ f g := fun _ _ => rfl
  let N : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ) :=
    { carrier := {x | x ∈ dualWeyl ℚ r n ν ∧ ∀ g ∈ M, fockQ x g = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Submodule.add_mem _ hx hy, fun g hg => ?_⟩
        rw [← hB, map_add (f := _), LinearMap.add_apply, hB, hB, hx' g hg, hy' g hg, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun g _ => by rw [← hB, map_zero, LinearMap.zero_apply]⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨Submodule.smul_mem _ c hx, fun g hg => ?_⟩
        rw [← hB, map_smul, LinearMap.smul_apply, hB, hx' g hg, smul_zero] }
  have hNV : N ≤ dualWeyl ℚ r n ν := fun x hx => hx.1
  have hNc : RowDivClosed N := by
    intro a b k f hf
    obtain ⟨hf1, hf2⟩ := hf
    refine ⟨rowDivStable ℚ r n ν a b k f hf1, fun g hg => ?_⟩
    rw [h4, hf2 _ (hMc b a k g hg)]
  have hN : N = ⊥ := by
    by_contra hne
    have hmem := h1 r n hn ν hν N hNV hNc hne
    have h0 := hmem.2 _ hhw
    have hpos := (h2 _ (hw ℚ hn ν) 0).2 (hwNe ℚ r n hn ν)
    linarith
  let BM := B.restrict M
  have hBM : ∀ x y : M, BM x y = fockQ (x : MvPolynomial (Fin r × Fin n) ℚ) y := fun _ _ => rfl
  have key : ∀ x : M, (∀ y : M, BM x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    have hx0 : (x : MvPolynomial (Fin r × Fin n) ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := (h2 _ (x : MvPolynomial (Fin r × Fin n) ℚ) 0).2 hx0
    have h0 := hx x
    rw [hBM] at h0
    linarith
  have hnd : BM.Nondegenerate := by
    refine ⟨key, fun y hy => key y fun x => ?_⟩
    rw [hBM, (h2 _ _ _).1, ← hBM]
    exact hy x
  apply le_antisymm hMV
  intro f hf
  let φ : Module.Dual ℚ M := (B f).domRestrict M
  let p : M := (BM.toDual hnd).symm φ
  have hp : ∀ g : M, fockQ (p : MvPolynomial (Fin r × Fin n) ℚ) g = fockQ f g := by
    intro g
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ g
    exact this
  have hd : f - p ∈ N := by
    refine ⟨Submodule.sub_mem _ hf (hMV p.2), fun g hg => ?_⟩
    rw [← hB, map_sub, LinearMap.sub_apply, hB, hB, ← hp ⟨g, hg⟩, sub_self]
  rw [hN] at hd
  have hfp : f = p := sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp hd)
  rw [hfp]
  exact p.2

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLine
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line : HWLine := by
  intro K _ _ r n hn ν hν f hf hraise
  have hfP := (dualWeylPoint K r n ν f).mp hf
  have hhP := (dualWeylPoint K r n ν (hw K hn ν)).mp (hwMem K r n hn ν hν)
  have hid : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idPoint K r n (a, j) = 0 := by
    intro a j h
    simp [idPoint, h]
  have hP1 : ∏ v, idPoint K r n v ^ (lhwline_mnu hn ν) v = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨a, j⟩ := v
    rw [lhwline_mnu_apply]
    by_cases h : a.val = j.val <;> simp [idPoint, h]
  have hcf : eval (idPoint K r n) f = AddMonoidAlgebra.coeff f (lhwline_mnu hn ν) := by
    rw [lhwline_diag hn ν f hfP.1 _ hid, hP1, mul_one]
  have hch : AddMonoidAlgebra.coeff (hw K hn ν) (lhwline_mnu hn ν) = 1 := by
    have h1 := lhwline_diag hn ν (hw K hn ν) hhP.1 _ hid
    rw [hP1, mul_one] at h1
    rw [← h1]
    simp [hw, eval_idPoint_lpMinor]
  set c := eval (idPoint K r n) f with hc
  refine ⟨c, ?_⟩
  have hgw : IsWeightedHomogeneous (colW r n) (f - c • hw K hn ν) ν := by
    have h1 : f ∈ weightedHomogeneousSubmodule K (colW r n) ν :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP.1
    have h2 : hw K hn ν ∈ weightedHomogeneousSubmodule K (colW r n) ν :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hhP.1
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (Submodule.sub_mem _ h1 (Submodule.smul_mem _ c h2))
  have hg0 : f - c • hw K hn ν = 0 := by
    apply lhwline_vanish
    · intro a b hab
      rw [map_sub, map_smul, lhwline_rowGen_eq a b f (hraise a b hab),
        lhwline_rowGen_eq a b (hw K hn ν) (fun k hk => hwRaise K r n hn ν a b k hab hk)]
      simp [Polynomial.smul_C]
    · intro l j hlj c'
      rw [map_sub, map_smul, hfP.2 l j hlj c', hhP.2 l j hlj c']
    · intro D hD
      rw [lhwline_diag hn ν _ hgw D hD, coeff_sub, coeff_smul, hch, ← hcf]
      simp
  exact sub_eq_zero.mp hg0

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLineTall
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line_tall : HWLineTall := by
  intro K _ _ r n ν ⟨s, hs, hνs⟩ f hf hdiv
  obtain ⟨hhom, hcol⟩ := (dualWeylPoint K r n ν f).mp hf
  refine lhwline_vanish f (fun a b hab => lhwline_rowGen_eq a b f (hdiv a b hab)) hcol ?_
  intro D hD
  exact lhwline_diag_tall ν s hs hνs f hhom D hD

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRationalOf
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem rowGen_map_intCast {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    rowGen ℚ a b (map (Int.castRingHom ℚ) f) =
      Polynomial.map (map (Int.castRingHom ℚ)) (rowGen ℤ a b f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [rowGen]
  next p q hp hq =>
    rw [_root_.map_add (f := _), _root_.map_add (f := _), _root_.map_add (f := _), hp, hq, Polynomial.map_add (f := _)]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, Polynomial.map_mul, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

private theorem rowDiv_map_intCast {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    rowDiv ℚ a b k (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) := by
  unfold rowDiv
  rw [rowGen_map_intCast, Polynomial.coeff_map]

private theorem map_intCast_applyWord {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (applyWord ℤ w f) = applyWord ℚ w (map (Int.castRingHom ℚ) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show map (Int.castRingHom ℚ) (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w f)) =
      rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w (map (Int.castRingHom ℚ) f))
    rw [← rowDiv_map_intCast, ih]

private theorem map_intCast_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom ℚ) (hw ℤ hn ν) = hw ℚ hn ν := by
  unfold hw
  rw [_root_.map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [_root_.map_pow]
  congr 1
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem lclosedeq_weyl_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) ℚ) (hF : F ∈ weyl ℚ r n hn ν) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ u ∈ weyl ℤ r n hn ν, map (Int.castRingHom ℚ) u = (c : ℚ) • F := by
  unfold weyl at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [map_intCast_applyWord, map_intCast_hw]
    simp
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, u, hu, hu'⟩ := hx
    obtain ⟨d, hd, v, hv, hv'⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, d • u + c • v,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩
    rw [_root_.map_add (f := _), MvPolynomial.smul_eq_C_mul u d, MvPolynomial.smul_eq_C_mul v c,
      _root_.map_mul, _root_.map_mul, map_C, map_C, hu', hv']
    simp only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, MvPolynomial.C_mul]
    ring
  | smul q x _ hx =>
    obtain ⟨c, hc, u, hu, hu'⟩ := hx
    refine ⟨(q.den : ℤ) * c, mul_ne_zero (by exact_mod_cast q.den_nz) hc, q.num • u,
      Submodule.smul_mem _ _ hu, ?_⟩
    rw [MvPolynomial.smul_eq_C_mul u q.num, _root_.map_mul, map_C, hu']
    have hq : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
    simp only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, Int.cast_natCast,
      MvPolynomial.C_mul, ← hq]
    ring

private theorem colAddGen_map_intCast {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    colAddGen ℚ (r := r) l j (map (Int.castRingHom ℚ) f) =
      map (Int.castRingHom ℚ) (colAddGen ℤ (r := r) l j f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [colAddGen]
  next p q hp hq =>
    rw [_root_.map_add (f := _), _root_.map_add (f := _), _root_.map_add (f := _), hp, hq, _root_.map_add (f := _)]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, _root_.map_mul, hp]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

private theorem map_intCast_mem_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ)
    (hf : f ∈ dualWeyl ℤ r n ν) : map (Int.castRingHom ℚ) f ∈ dualWeyl ℚ r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero,
    mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, _root_.map_zero]
  · intro l j hlj
    rw [colAddGen_map_intCast, h2 l j hlj, map_rename]

theorem weyl_module_rational : WeylRationalOf := by
  unfold WeylRationalOf WeylRational
  intro h r n hn ν hν f hf
  have hfQ : map (Int.castRingHom ℚ) f ∈ weyl ℚ r n hn ν := by
    rw [h r n hn ν hν]
    exact map_intCast_mem_dualWeyl ν f hf
  obtain ⟨c, hc, u, hu, hmap⟩ := lclosedeq_weyl_denom hn ν _ hfQ
  refine ⟨c, hc, ?_⟩
  have huf : u = c • f := by
    apply MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
    rw [hmap, _root_.map_zsmul]
    exact Int.cast_smul_eq_zsmul ℚ c _
  rw [← huf]
  exact hu

end Formalism.GradedWeylDivisibility
end
end

