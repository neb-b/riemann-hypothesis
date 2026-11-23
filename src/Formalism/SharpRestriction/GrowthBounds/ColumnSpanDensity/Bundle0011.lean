module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.FinalO

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

theorem P_rev (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w))) :
    (algebraMap O Kf w ^ (-(((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) *
      lam (Fin.last m)))) • F ∈ nablaLTw O Kf m lam g := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set ν : Fin (m + 1) → ℕ := fun t => (lam t - lam (Fin.last m)).toNat with hν
  set e : ℤ := lam (Fin.last m) with he
  obtain ⟨b, hb, -⟩ := lb_basis O (m + 1) (m + 1) ν
  set t : Fin (m + 1) → Kf := fun a => if a.val < r then c⁻¹ else 1 with ht
  have ht0 : ∀ a, t a ≠ 0 := by
    intro a
    simp only [ht]
    split_ifs
    · exact inv_ne_zero hw
    · exact one_ne_zero
  have hB := (nablaLBasis O Kf hinj (m + 1) (m + 1) ν b _ hb g hg).2
  have hD := (nablaLDiag O Kf hinj (m + 1) (m + 1) ν b _ hb g t hg ht0).2
  have hle : nablaL O Kf (m + 1) (m + 1) ν (g * Matrix.diagonal t) ≤ nablaL O Kf (m + 1) (m + 1) ν g := by
    rw [← hD, ← hB, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    set Fi := rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hFi
    set π' : ℕ := ∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a with hπ
    have h2 : ∏ a, t a ^ rowWt i.1 a = (c⁻¹) ^ π' := by
      rw [hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      simp only [ht]
      split_ifs <;> simp
    have h6 : ((c⁻¹) ^ π')⁻¹ = c ^ π' := by rw [inv_pow, inv_inv]
    show (∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi ∈ _
    rw [h2, h6, hc, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨F0, hF0, rfl⟩ := hF
  refine ⟨F0, hle hF0, ?_⟩
  set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
  show g.det ^ (-e) • F0 = c ^ (-((ρ : ℤ) * e)) • ((g * lb_D (m + 1) r c).det ^ (-e) • F0)
  have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
    rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
    rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
  rw [smul_smul, h1, mul_zpow, h5, mul_comm (g.det ^ (-e)), ← mul_assoc, ← zpow_add₀ hw, neg_add_cancel, zpow_zero,
    one_mul]

theorem zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ H0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w)))) :
    (algebraMap O Kf w ^ (-(((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) *
      lam (Fin.last m)))) • F ∈ H0 O m lam (colSpan O g) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold H0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  have h1 : F ∈ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) :=
    (iInf₂_le _ ⟨hgD, rfl⟩ : _ ≤ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w))) hF
  have h2 := P_rev O Kf hinj m r lam w hw g hg F h1
  exact (le_iInf₂ fun h hh => lb_indep O Kf hinj m lam _ h hg hh.1 hh.2 : nablaLTw O Kf m lam g ≤ _) h2

section RSLat

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem extO_RS (s : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) R.Qq) :
    extO R.O R.ι R.σ s (colSpan R.W g) = colSpan R.O (la_tw R.ι R.σ s g) :=
  la_extO R.ι R.σ R.jO (fun x => by obtain ⟨y, hy⟩ := R.std.1.frob x; exact ⟨_, hy⟩) R.std.1.ι_comp s g

theorem tw_p (s : ℕ) {k : ℕ} (x : Fin k → R.Qq) (i : Fin k) :
    twistVec R.ι R.σ s ((p : R.W) • x) i = (p : R.Kf) * R.ι ((R.σ ^ s) (x i)) := by
  show R.ι ((R.σ ^ s) ((p : R.W) • x i)) = _
  rw [Algebra.smul_def, map_natCast, map_mul, map_mul, map_natCast, map_natCast]

theorem edgeLat_RS (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ gs : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, (∀ s, IsUnit (gs s).det) ∧
      (∀ s, extO R.O R.ι R.σ s e.src = colSpan R.O (gs s)) ∧
      (∀ s, LeAt p R.ι R.σ R.w s e = colSpan R.O (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w))) ∧
      (∀ s, extO R.O R.ι R.σ s e.tgt =
        colSpan R.O (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w) * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w))) := by
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  unfold lb_D
  set c : R.Kf := algebraMap R.O R.Kf R.w with hc
  have hw : c ≠ 0 := R.w_ne
  have hpK : (p : R.Kf) = c ^ 2 := R.p_eq
  have hpK0 : (p : R.Kf) ≠ 0 := by rw [hpK]; exact pow_ne_zero _ hw
  have hpQ0 : (p : R.Qq) ≠ 0 := by
    intro h0
    apply hpK0
    have := congrArg R.ι h0
    simpa using this
  set dK : Fin (m + 1) → R.Kf := fun a => if a.val < 1 then c⁻¹ else 1 with hdK
  set dQ : Fin (m + 1) → R.Qq := fun a => if a.val < 1 then ((p : R.Qq))⁻¹ else 1 with hdQ
  have hDD : ∀ s, la_tw R.ι R.σ s (g * Matrix.diagonal dQ) =
      la_tw R.ι R.σ s g * Matrix.diagonal dK * Matrix.diagonal dK := by
    intro s
    ext i j
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, lb_tw_apply, lb_tw_apply,
      Matrix.mul_diagonal, map_mul, map_mul]
    congr 1
    simp only [hdQ, hdK]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast, hpK, pow_two, mul_inv]
    · simp
  have e1 : ∀ s, extO R.O R.ι R.σ s e.src = colSpan R.O (la_tw R.ι R.σ s g) :=
    fun s => by rw [hsrc]; exact extO_RS R s g
  have e3 : ∀ s, extO R.O R.ι R.σ s e.tgt =
      colSpan R.O (la_tw R.ι R.σ s g * Matrix.diagonal dK * Matrix.diagonal dK) :=
    fun s => by rw [htgt, extO_RS R, hDD]
  refine ⟨fun s => la_tw R.ι R.σ s g, fun s => la_tw_det _ _ s g hg, e1, ?_, e3⟩
  intro s
  set gK := la_tw R.ι R.σ s g with hgK
  apply le_antisymm
  · unfold LeAt
    refine sup_le ?_ ?_
    · rw [e1]
      intro x hx
      have h1 : gK = gK * Matrix.diagonal dK *
          Matrix.diagonal (fun a : Fin (m + 1) => if a.val < 1 then c else 1) := by
        rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
        have h2 : (fun a : Fin (m + 1) => dK a * (if a.val < 1 then c else 1)) = fun _ => 1 := by
          funext a
          simp only [hdK]
          split_ifs
          · exact inv_mul_cancel₀ hw
          · simp
        rw [h2, Matrix.diagonal_one, Matrix.mul_one]
      have hx' : x ∈ colSpan R.O gK := hx
      rw [h1] at hx'
      have h3 := lb_col (gK * Matrix.diagonal dK) _
        (fun a : Fin (m + 1) => if a.val < 1 then R.w else 1) 1
        (by intro j; split_ifs <;> simp [hc]) x hx'
      rw [one_smul] at h3
      exact h3
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : c⁻¹ • twistVec R.ι R.σ s ((p : R.W) • x) =
          R.w • twistVec R.ι R.σ s x := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, tw_p R, smul_eq_mul, Algebra.smul_def, ← hc, hpK]
        show c⁻¹ * (c ^ 2 * _) = c * R.ι ((R.σ ^ s) (x i))
        field_simp
      have h2 : twistVec R.ι R.σ s x ∈
          colSpan R.O (gK * Matrix.diagonal dK * Matrix.diagonal dK) := by
        rw [← e3]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      show c⁻¹ • twistVec R.ι R.σ s ((p : R.W) • x) ∈ _
      rw [h1]
      exact lb_col (gK * Matrix.diagonal dK) dK
        (fun a : Fin (m + 1) => if a.val < 1 then 1 else R.w) R.w
        (by
          intro j
          simp only [hdK]
          split_ifs
          · rw [← hc, mul_inv_cancel₀ hw, map_one]
          · rw [mul_one]) _ h2
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold LeAt
    by_cases hj : j.val < 1
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      refine ⟨fun i => (g * Matrix.diagonal dQ) i j, ?_, ?_⟩
      · rw [htgt]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        show c⁻¹ • twistVec R.ι R.σ s
          ((p : R.W) • fun i => (g * Matrix.diagonal dQ) i j) i = (gK * Matrix.diagonal dK) i j
        rw [tw_p R, Matrix.mul_diagonal, Matrix.mul_diagonal, smul_eq_mul, hgK, lb_tw_apply]
        simp only [hdQ, hdK, hj, if_true, map_mul, map_inv₀, map_natCast]
        field_simp
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨fun i => g i j, ?_, ?_⟩
      · rw [hsrc]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        simp only [twistVec, Matrix.mul_diagonal, hdK, hj, if_false, mul_one, lb_tw_apply]

end RSLat

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NLeDAll
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

theorem nLeD_all {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hDc : 2 * D < c)
    (hfac : ∀ e, IsEdge p n' 1 e →
      FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    (n : ℝ) ≤ dL R lam0 := by
  classical
  have hcnt := restEdgeCountSrc
  have hdnn := dL_nonneg R lam0
  by_cases hn0 : n = 0
  · subst hn0; simpa using hdnn
  have hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq)) := ⟨1, by simp, rfl⟩
  obtain ⟨Ne, es, hinj, hes, hNe⟩ := hcnt p n' R (m + 1) (by omega) _ hL
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) < c := by linarith
    exact_mod_cast this
  have hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0)
      (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧
      (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ Re' p R.ι R.σ R.w 1 lam0 (es i)) ∧
      z' * z = R.w ^ (c - 1) ∧
      ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then algebraMap R.O R.Kf z else 0 := by
    intro i
    rcases hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩
    · exact absurd h0 hn0
    · obtain ⟨z', hz'⟩ := dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv
      refine ⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx,
        fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩
      rw [be_sum]
      exact hM a b
  choose x y z z' hz0 hx hy hzz hxy using hdata
  have hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧
      be p 1 lam0 (x i.1 i.2) (y l.1 l.2) =
        algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1) := by
    rintro ⟨i, a⟩ ⟨l, b⟩
    by_cases hil : i = l
    · subst hil
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only
      rw [hxy, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · have : ((i, a) : Fin Ne × Fin n) ≠ (i, b) := fun h => hab (Prod.mk.inj h).2
        rw [if_neg hab, if_neg this]; simp
    · have hne : es l ≠ es i := fun h => hil (hinj h).symm
      have hXs := CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)
      obtain ⟨b', hb⟩ := be_scale_Re R lam0 (es l) c hXs (hy l b)
      have h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b) := fun h => hil (Prod.mk.inj h).1
      refine ⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩
      simp only
      rw [hb, Matrix.one_apply_ne h2, zero_add]
      congr 1
      have h3 : R.w ^ c = R.w * R.w ^ (c - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3, ← hzz l]
      ring
  choose β hβm hβe using hβ
  let P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O := Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l
  have hP : IsUnit P.det := by
    apply isUnit_det_of_one_add'
    intro i l
    simpa [P] using hβm i l
  have hinjK : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    have : P.det = 0 := hinjK (by rw [h0, map_zero])
    rw [this] at hP
    exact not_isUnit_zero hP
  have hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0 := by
      intro l
      have h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0 := by
        rw [hg]; simp [be]
      rw [be_sum_left] at h2
      have h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0 := by
        rw [← h2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hβe i l, map_mul, mul_assoc]
        rfl
      have hz : algebraMap R.O R.Kf (z l.1) ≠ 0 := fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))
      exact (mul_eq_zero.1 h3).resolve_right hz
    have h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0 := by
      funext l
      simpa [Matrix.vecMul, dotProduct] using h1 l
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero hPK h4
    intro i
    rw [h5]; rfl
  have hpos : 0 < dimV R.Kf lam0 := Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom
  have hfin : Module.Finite R.Kf (Vsp R.Kf lam0) := Module.finite_of_finrank_pos hpos
  have hcard : Ne * n ≤ dimV R.Kf lam0 := by
    have := hli.fintype_card_le_finrank
    simpa [dimV] using this
  have hNpos := gaussianNumber_prime_pow_pos R (m + 1) (by omega)
  unfold dL
  rw [le_div_iff₀ hNpos]
  have h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ) := by exact_mod_cast hcard
  have h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne := mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)
  push_cast at h6
  linarith

theorem nEdge {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (e e' : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (he' : IsEdge p n' 1 e')
    (hfac : FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e') (Re' p R.ι R.σ R.w 1 lam0 e') n D := by
  classical
  have hFun := restFunct
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  obtain ⟨g', hg', hsrc', htgt'⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e' he'
  have hug : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 hg
  have hug' : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 hg'
  let γ : GL (Fin (m + 1)) R.Qq := hug'.unit * hug.unit⁻¹
  have hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g' := by
    have : γ * hug.unit = hug'.unit := by simp [γ]
    have h2 := congrArg Units.val this
    simpa using h2
  have hee : e' = mapE γ e := by
    cases e with
    | mk s tg =>
      cases e' with
      | mk s' tg' =>
        simp only at hsrc htgt hsrc' htgt'
        simp only [mapE]
        rw [hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]
  obtain ⟨T, hT1, hT2⟩ := hFun p n' R m lam0 hDom γ
  have hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'') :=
    fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h
  have hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact scale_alt T _ (hT1 e.src he.1) hx.1.1
    · exact scale_alt T _ (hT2 e he) hx.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').src = e.src := by
        show e''.src.map (nt_phi R.W γ⁻¹) = e.src
        rw [h2]
        exact nt_map_inv γ e.src
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx
      have h7 := apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  rw [hee]
  rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h0
  · refine Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i),
      fun l => comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) (hy l), z, M, hz, hv, fun i j => ?_⟩
    rw [← hM i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    unfold be
    rw [LinearMap.comp_apply, ← map_smul]
    simp

theorem nLeD {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hDc : 2 * D < c) (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e)
    (hfac : FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    (n : ℝ) ≤ dL R lam0 :=
  nLeD_all R lam0 hDom t c n D hD0 hDc fun e' he' => nEdge R lam0 hDom t c n D e e' he he' hfac

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestOIso
section
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem restOIso : RestOIso := fun p n' R₁ R₂ φW =>
  QuadraticBasis.oIso p n' R₁.std.1.prime (by have := R₁.std.1.two_le; omega) R₁.W R₂.W R₁.O R₂.O R₁.jO R₂.jO R₁.w R₂.w
    R₁.std.1.p_unif R₂.std.1.p_unif R₁.std.1.res_card R₂.std.1.res_card R₁.std.1.eq_sum_herm_smul_frame_of_inW R₂.std.1.eq_sum_herm_smul_frame_of_inW
    R₁.std.1.finite R₂.std.1.finite R₁.std.1.complete_O R₂.std.1.complete_O R₁.std.1.w_sq R₂.std.1.w_sq
    R₁.std.2.1 R₂.std.2.1 R₁.std.2.2.1 R₂.std.2.2.1 φW

end Formalism.MainNotions.flipOneThree.Pf
end

