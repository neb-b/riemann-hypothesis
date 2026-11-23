module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.JpSubstExpand
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnGePProdRat
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem en_p_mem : (p : Y.Kc) ∈ Y.Oc := by
  exact natCast_mem Y.Oc p

theorem en_ppow_mem (N : ℤ) (hN : 0 ≤ N) : (p : Y.Kc) ^ N ∈ Y.Oc := by
  lift N to ℕ using hN
  rw [zpow_natCast]
  exact Y.Oc.pow_mem (en_p_mem Y) _

theorem en_root (z : Y.Kc) (M : ℕ) (hM : 0 < M) (h : z ^ M ∈ Y.Oc) : z ∈ Y.Oc := by
  rcases Y.Oc_val z with hz | hz
  · exact hz
  · by_cases h0 : z = 0
    · rw [h0]
      exact Y.Oc.zero_mem
    · have e : z = z ^ M * (z⁻¹) ^ (M - 1) := by
        rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ h0), ← pow_succ']
        congr 1
        omega
      rw [e]
      exact Y.Oc.mul_mem h (Y.Oc.pow_mem hz _)

theorem en_geC_one : Y.geC 1 0 := by
  intro a b hb hab
  rw [one_pow, one_mul]
  have h' : (a : ℝ) ≤ 0 := by linarith
  have h'' : a ≤ 0 := by exact_mod_cast h'
  exact en_ppow_mem Y (-a) (by omega)

theorem en_geC_mul_rat {x y : Y.Kc} (q1 q2 : ℚ) (hx : Y.geC x q1) (hy : Y.geC y q2) :
    Y.geC (x * y) ((q1 + q2 : ℚ) : ℝ) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hM0 : 0 < q1.den * q2.den := Nat.mul_pos q1.den_pos q2.den_pos
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℤ, (a1 : ℝ) = (q1 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q1.num * q2.den * b, ?_⟩
    have hd : (q1.den : ℝ) ≠ 0 := by exact_mod_cast q1.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℤ, (a2 : ℝ) = (q2 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q2.num * q1.den * b, ?_⟩
    have hd : (q2.den : ℝ) ≠ 0 := by exact_mod_cast q2.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hx' := hx a1 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha1.le
  have hy' := hy a2 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha2.le
  have hle : a * ((q1.den * q2.den : ℕ) : ℤ) ≤ a1 + a2 := by
    have h' : ((a * ((q1.den * q2.den : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((a1 + a2 : ℤ) : ℝ) := by
      push_cast
      rw [ha1, ha2]
      push_cast at hab ⊢
      have hM' : (0 : ℝ) ≤ (q1.den : ℝ) * q2.den := by positivity
      nlinarith
    exact_mod_cast h'
  have key : ((x * y) ^ b * (p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
      (x ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a1)) * (y ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a2)) *
        (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
    have h1 : ((p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
        (p : Y.Kc) ^ (-a1) * (p : Y.Kc) ^ (-a2) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp, ← zpow_add₀ hp]
      congr 1
      push_cast
      ring
    rw [mul_pow, h1]
    ring
  apply en_root Y _ (q1.den * q2.den) hM0
  rw [key]
  exact Y.Oc.mul_mem (Y.Oc.mul_mem hx' hy') (en_ppow_mem Y _ (by omega))

theorem en_geC_sum {α : Type} (s : Finset α) (f : α → Y.Kc) (g : ℝ) (h : ∀ i ∈ s, Y.geC (f i) g) :
    Y.geC (∑ i ∈ s, f i) g := by
  exact Finset.sum_induction f (fun x => Y.geC x g) (fun _ _ ha hb => geC_add Y ha hb) (geC_zero Y g) h

def geP {τ : Type} (a : MvPolynomial τ Y.Kc) (g : ℝ) : Prop := ∀ n, Y.geC (AddMonoidAlgebra.coeff a n) g

theorem valuation_coeff_one_nonneg {τ : Type} : geP Y (1 : MvPolynomial τ Y.Kc) 0 := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact en_geC_one Y
  · exact geC_zero Y 0

theorem valuation_coeff_ge_mul_rat {τ : Type} {a b : MvPolynomial τ Y.Kc} (q1 q2 : ℚ) (ha : geP Y a q1) (hb : geP Y b q2) :
    geP Y (a * b) ((q1 + q2 : ℚ) : ℝ) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact en_geC_sum Y _ _ _ fun x _ => en_geC_mul_rat Y q1 q2 (ha x.1) (hb x.2)

theorem valuation_coeff_ge_prod_rat {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (q : α → ℚ)
    (h : ∀ i ∈ s, geP Y (a i) (q i)) : geP Y (∏ i ∈ s, a i) ((∑ i ∈ s, q i : ℚ) : ℝ) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using valuation_coeff_one_nonneg Y (τ := τ)
  · intro i t hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact valuation_coeff_ge_mul_rat Y _ _ (h i (Finset.mem_insert_self i t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem valuation_coeff_ge_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (g : ℝ) (h : ∀ i ∈ s, geP Y (a i) g) :
    geP Y (∑ i ∈ s, a i) g := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact en_geC_sum Y _ _ _ fun i hi => h i hi n

theorem valuation_coeff_ge_smul {τ : Type} {a : MvPolynomial τ Y.Kc} {g : ℝ} {c : Y.Kc} (hc : c ∈ Y.Oc) (h : geP Y a g) :
    geP Y (c • a) g := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact geC_mul_Oc Y (h n) hc

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EntryAOneParity
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : φ.comp (Int.castRingHom K) = Int.castRingHom K' := RingHom.ext_int _ _
  have e2 : φ (∏ x ∈ n.support, ((n x).factorial : K)) = ∏ x ∈ n.support, ((n x).factorial : K') := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => map_natCast φ _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, e, MvPowerSeries.coeff_map, map_mul φ, e2]

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IsLatticeBetween
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

open Formalism.MainNotions.G

section Gen

variable {R : Type*} [CommRing R] {M M1 M2 : Type*} [AddCommGroup M] [AddCommGroup M1] [AddCommGroup M2]
  [Module R M] [Module R M1] [Module R M2]

theorem card_eq_of_ker_eq (f1 : M →ₗ[R] M1) (f2 : M →ₗ[R] M2) (h1 : Function.Surjective f1)
    (h2 : Function.Surjective f2) (hk : LinearMap.ker f1 = LinearMap.ker f2) : Nat.card M1 = Nat.card M2 := by
  have e1 := (f1.quotKerEquivOfSurjective h1).toEquiv
  have e2 := (f2.quotKerEquivOfSurjective h2).toEquiv
  have e3 := (Submodule.quotEquivOfEq _ _ hk).toEquiv
  exact Nat.card_congr (e1.symm.trans (e3.trans e2))

theorem card_quot (T S : Submodule R M1) (φ : M →ₗ[R] M1) (hφ : LinearMap.range φ = T) (f2 : M →ₗ[R] M2)
    (h2 : Function.Surjective f2) (hk : ∀ m, φ m ∈ S ↔ f2 m = 0) :
    Nat.card (↥T ⧸ Submodule.comap T.subtype S) = Nat.card M2 := by
  have hmem : ∀ m, φ m ∈ T := fun m => hφ ▸ LinearMap.mem_range_self φ m
  let f1 : M →ₗ[R] (↥T ⧸ Submodule.comap T.subtype S) :=
    (Submodule.comap T.subtype S).mkQ.comp (φ.codRestrict T hmem)
  apply card_eq_of_ker_eq f1 f2 _ h2
  · ext m
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hk m]
    show (Submodule.comap T.subtype S).mkQ (φ.codRestrict T hmem m) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  · intro y
    obtain ⟨⟨t, ht⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hφ] at ht
    obtain ⟨m, rfl⟩ := ht
    exact ⟨m, rfl⟩

end Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {n : ℕ}

def psi (g : Matrix (Fin n) (Fin n) Qq) : (Fin n → W) →ₗ[W] (Fin n → Qq) :=
  ((Matrix.mulVecLin g).restrictScalars W).comp ((Algebra.linearMap W Qq).compLeft (Fin n))

theorem psi_apply (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    psi g w = g.mulVec (fun c => algebraMap W Qq (w c)) := rfl

theorem mem_colSpan (G : Matrix (Fin n) (Fin n) Qq) (x : Fin n → Qq) :
    x ∈ colSpan W G ↔ ∃ y : Fin n → W, x = G.mulVec (fun c => algebraMap W Qq (y c)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem range_psi (g : Matrix (Fin n) (Fin n) Qq) : LinearMap.range (psi (W := W) g) = colSpan W g := by
  ext x
  rw [LinearMap.mem_range, mem_colSpan]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩

theorem mulVec_cancel (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) {u v : Fin n → Qq}
    (h : g.mulVec u = g.mulVec v) : u = v := by
  have := congrArg (g⁻¹).mulVec h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg] using this

theorem psi_inj (hinj : Function.Injective (algebraMap W Qq)) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) :
    Function.Injective (psi (W := W) g) := by
  intro a b h
  have := mulVec_cancel g hg h
  funext c
  exact hinj (congrFun this c)

theorem psi_smul_mat (c : Qq) (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    psi (c • g) w = c • psi g w := by
  rw [psi_apply, psi_apply, Matrix.smul_mulVec]

theorem isLattice_between [IsDomain W] [IsPrincipalIdealRing W] [IsFractionRing W Qq] (π : W) (hπ : π ≠ 0)
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (S : Submodule W (Fin n → Qq))
    (h1 : S ≤ colSpan W g) (h2 : ∀ y ∈ colSpan W g, π • y ∈ S) : IsLattice W S := by
  classical
  have hinj := psi_inj (IsFractionRing.injective W Qq) g hg
  set Sb : Submodule W (Fin n → W) := S.comap (psi g) with hSb
  obtain ⟨m, ⟨bS⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun W (Fin n)) Sb
  have hfin : Module.Finite W Sb := Module.Finite.of_basis bS
  have hfr : Module.finrank W Sb = m := by rw [Module.finrank_eq_card_basis bS, Fintype.card_fin]
  let c : Fin m → (Fin n → Qq) := fun i => psi g (bS i : Fin n → W)
  have hliW : LinearIndependent W c := by
    have := bS.linearIndependent.map' ((psi g).comp Sb.subtype)
      (by rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot, Submodule.ker_subtype])
    exact this
  have hliQ : LinearIndependent Qq c := (LinearIndependent.iff_fractionRing W Qq).1 hliW
  have hmn : m ≤ n := by
    have := hliQ.fintype_card_le_finrank
    simpa using this
  have hnm : n ≤ m := by
    have hmem : ∀ i : Fin n, π • (Pi.basisFun W (Fin n) i) ∈ Sb := by
      intro i
      show psi g (π • (Pi.basisFun W (Fin n) i)) ∈ S
      rw [map_smul]
      exact h2 _ (by rw [← range_psi]; exact LinearMap.mem_range_self _ _)
    have hli : LinearIndependent W (fun i : Fin n => (⟨π • (Pi.basisFun W (Fin n) i), hmem i⟩ : Sb)) := by
      apply LinearIndependent.of_comp Sb.subtype
      have := (Pi.basisFun W (Fin n)).linearIndependent.map' (π • (LinearMap.id : (Fin n → W) →ₗ[W] (Fin n → W)))
        (by
          rw [LinearMap.ker_eq_bot]
          intro a b hab
          exact smul_right_injective _ hπ hab)
      exact this
    have := hli.fintype_card_le_finrank
    rw [hfr] at this
    simpa using this
  obtain rfl : m = n := le_antisymm hmn hnm
  refine ⟨Matrix.of fun a b => c b a, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hliQ
  · unfold colSpan
    have e1 : (Set.range fun b : Fin m => fun a => (Matrix.of fun a b => c b a) a b) =
        (psi g).comp Sb.subtype '' Set.range bS := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, bS.span_eq, Submodule.map_comp, Submodule.map_subtype_top, hSb,
      Submodule.map_comap_eq, range_psi, inf_eq_right.2 h1]

end Formalism.MainNotions.FormalGroupSystem.Pf.Cnt
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelExpansionOfRestrictions
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def RestSExp (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (Ph : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)),
    Simeq p Ph (∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      ThZ B K' vp (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestSInt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' r0 r1 : ℕ) (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U))

def RestSExpA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (j : ℕ) (Ph : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)),
    Simeq p Ph (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

def RestSIntA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ (j : ℕ) (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)))

section Formal

variable {p : ℕ} [hp : Fact p.Prime]

theorem sSer_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (e : Fin n') (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (sSer p K' e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : Zidx n' r0 r1 →₀ ℕ).degree + 1),
    if (0 : Zidx n' r0 r1 →₀ ℕ) = Finsupp.single (posSub e (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhS_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (u : Fin n' → K') :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p K' u) = 0 := by
  unfold hhS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sSer_const, mul_zero, Finset.sum_const_zero]

theorem coordZ_const {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordZ, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZ_mul {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (f g : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K') :
    ThZ B K' vp (f * g) = ThZ B K' vp f * ThZ B K' vp g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZ_const B K' vp)) f g

theorem map_map_tower {ι : Type} (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (f : MvPowerSeries ι (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) f) =
      MvPowerSeries.map (algebraMap (K0 p) K') f := by
  rw [IsScalarTower.algebraMap_eq (K0 p) K1 K', MvPowerSeries.map_comp]
  rfl

theorem atPi_mul {σ R : Type} [CommRing R] (vp : R) (f g : MvPowerSeries σ R) :
    atPi vp (f * g) = atPi vp f * atPi vp g := by
  classical
  ext n
  show vp ^ n.degree * MvPowerSeries.coeff n (f * g) = MvPowerSeries.coeff n (atPi vp f * atPi vp g)
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  show _ = (vp ^ x.1.degree * MvPowerSeries.coeff x.1 f) * (vp ^ x.2.degree * MvPowerSeries.coeff x.2 g)
  rw [← hx', map_add (f := _), pow_add]
  ring

theorem exp_change {ι : Type} (K' : Type) [Field K'] [Algebra (K0 p) K'] (c : K') (hh hh' G : MvPowerSeries ι K')
    (h0 : MvPowerSeries.constantCoeff hh = 0) (h0' : MvPowerSeries.constantCoeff hh' = 0)
    (hE : hh' = hh + MvPowerSeries.C (p : K') * G) :
    expK (-(MvPowerSeries.C (c / (p : K')) * hh)) =
      expK (-(MvPowerSeries.C (c / (p : K')) * hh')) * expK (MvPowerSeries.C c * G) := by
  have := charZero_K' p K'
  have hp0 := pK'_ne p K'
  have hG : MvPowerSeries.constantCoeff G = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hE
    rw [map_add (f := _), map_mul, h0, h0', zero_add, MvPowerSeries.constantCoeff_C] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hp0
    · exact h
  rw [← expK_add (by rw [map_neg, map_mul, h0', mul_zero, neg_zero]) (by rw [map_mul, hG, mul_zero])]
  congr 1
  have e : (MvPowerSeries.C (c / (p : K')) : MvPowerSeries ι K') * MvPowerSeries.C (p : K') = MvPowerSeries.C c := by
    rw [← map_mul, div_mul_cancel₀ _ hp0]
  rw [hE, mul_add, ← mul_assoc, e]
  ring

end Formal

theorem SConcl_of {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (hD : DworkLemma p) (hE : RestSExp p) (hI : RestSInt p)
    {n' r0 r1 : ℕ} (h2 : 2 ≤ n') (hev : Even n') (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1]
    (R1 : Subring K1) (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1)
    (hK : ExtensionLocalCondition p K1 R1 be Th) : SConcl B K1 R1 Th := by
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hK
  intro K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨u, hu, V, hV, hEq⟩ := hE h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' vp hvp
  refine ⟨u, fun s => hRp (hu s), fun hh' h0' hG => ?_⟩
  obtain ⟨G, hG, hhE⟩ := hG
  have hW := hI n' r0 r1 B K1 R1 U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') Th) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hh')) *
        (expK (MvPowerSeries.C (vp ^ (p + 1)) * G) * V * ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U)) := by
    rw [hTh, map_mul, map_map_tower, ThZ_mul, hEq,
      exp_change K' (vp ^ (p + 1)) (hhS p K' u) hh' G (hhS_const K' u) h0' hhE]
    ring
  rw [e1]
  exact inClass_of_exp (pK'_ne p K') hc hh' h0' (IntR_mul (IntR_mul (IntR_expK hc hG) (IntR_mono hRp hV)) hW)

theorem kernel_expansion_of_restrictions (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExp p) (hI : RestSInt p) : Conclusion1 D X Y := by
  intro v j hj La La' h1 h2 φ
  exact SConcl_of (X.std v).five_le (hA.1 p) hE hI (X.std v).two_le (X.std v).even (X.om v) Y.Kc Y.Oc Y.be _
    (hA.2.1 v j hj La La' h1 h2 φ)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

