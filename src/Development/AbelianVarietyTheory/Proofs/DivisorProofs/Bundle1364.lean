module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEqMapNormOneTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTerm
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem absHalf_mul : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x y : w.adicCompletion E), x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y := by
  intro E _ _ w x y hx hy
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  have ho : Formalism.UG.ordL (x * y) = Formalism.UG.ordL x + Formalism.UG.ordL y := by
    unfold Formalism.UG.ordL
    have h1 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h2 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h3 : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
    rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
    have : WithZero.unzero h3 = WithZero.unzero h1 * WithZero.unzero h2 := by
      apply WithZero.coe_injective
      simp [map_mul]
    rw [this, toAdd_mul]
    ring
  unfold absHalf
  rw [ho, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_pos hq _).le]
  push_cast
  ring

theorem isClosed_parP : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E), IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  intro E _ _ a n w
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

theorem blk_mem_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), blk h w m X ∈ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m X
  unfold blk
  simp only []
  split_ifs with hM
  · change (hM.unit : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular _
    rw [IsUnit.unit_spec]
    intro i j hij
    have hj : (j : ℕ) < a := by
      by_contra hc
      push_neg at hc
      simp only [hc, decide_true] at hij
      exact (by decide : ∀ c : Bool, ¬ (true < c)) _ hij
    have hi : a ≤ (i : ℕ) := by
      by_contra hc
      push_neg at hc
      simp only [not_le.2 hc, decide_false] at hij
      exact (by decide : ∀ c : Bool, ¬ (c < false)) _ hij
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases hi' : (finSumFinEquiv.trans (finCongr h)).symm i with i' | i'
    · exfalso
      have := congrArg (finSumFinEquiv.trans (finCongr h)) hi'
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp at hv
      omega
    · rcases hj' : (finSumFinEquiv.trans (finCongr h)).symm j with j' | j'
      · simp
      · exfalso
        have := congrArg (finSumFinEquiv.trans (finCongr h)) hj'
        rw [Equiv.apply_symm_apply] at this
        have hv := congrArg Fin.val this
        simp at hv
        omega
  · exact (parP a n w).one_mem

theorem avg_const_mul {H : Type} [Group H] (u : H → ℂ) {c : ℂ} (hc : c ≠ 0) :
    avg (fun x => c * u x) = c * avg u := by
  have hs : rStab (fun x => c * u x) = rStab u := by
    ext k
    change (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
    exact ⟨fun h x => mul_left_cancel₀ hc (h x), fun h x => by rw [h x]⟩
  unfold avg
  rw [hs, ← mul_finsum]
  ring

theorem absHalf_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) : absHalf w x ≠ 0 := by
  unfold absHalf
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  exact_mod_cast (Real.sqrt_pos.2 (zpow_pos hq _)).ne'

theorem ct_eq_mul_orbN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ct (Nat.add_sub_cancel' ha) w f m = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f m := by
  intro E _ _ _ n a ha w f hf m hsep
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m
  have hR := _root_.GlobalTheory.resultant_ne_zero_of_separable_mul (w.adicCompletion E) _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hsep
  have hD := _root_.GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow (w.adicCompletion E) a (n - a) m.1 m.2.val
  have hd1 : m.1.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).ne_zero
  have hd2 : m.2.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit).ne_zero
  have hL : LinearMap.det (adL m.1 m.2.val) ≠ 0 := by
    intro h0
    rw [h0] at hD
    apply hR
    have : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 = 0 := by rw [← hD]; ring
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hJ := _root_.GlobalTheory.LeviDesc.hint_comp_linear E w a (n - a) (adL m.1 m.2.val)
    (fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk (Nat.add_sub_cancel' ha) w m X)) hL hU hcs
  have hI : orbN (Nat.add_sub_cancel' ha) w f m = hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk (Nat.add_sub_cancel' ha) w m (adL m.1 m.2.val (Multiplicative.toAdd X)))) := by
    unfold orbN
    simp only [_root_.GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk]
  rw [hI, hJ]
  change absHalf w (m.1.val.det ^ (n - a) / m.2.val.det ^ a) * hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk (Nat.add_sub_cancel' ha) w m (Multiplicative.toAdd X))) = _
  have hq : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a) =
      LinearMap.det (adL m.1 m.2.val) * (LinearMap.det (adL m.1 m.2.val) * (m.1.val.det ^ (n - a) / m.2.val.det ^ a)) := by
    rw [← hD]
    field_simp
    ring
  have hq0 : m.1.val.det ^ (n - a) / m.2.val.det ^ a ≠ 0 := div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  rw [hq, absHalf_mul E w _ _ hL (mul_ne_zero hL hq0), absHalf_mul E w _ _ hL hq0]
  have h0 := absHalf_ne_zero' w (LinearMap.det (adL m.1 m.2.val))
  field_simp

theorem conjP_charpoly {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.charpoly = m.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g m.val

theorem conjP_det {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.det = m.val.det := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj' g m.val

theorem orbInt_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w (n := n)) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w (n := n)) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  intro E _ _ _ n a ha w f hf m hsep
  have hf' : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f := by
    rcases hf with h | h
    · exact ⟨_, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, h⟩
    · exact h
  have hc0 := absHalf_ne_zero' w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a))
  have h1 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) =
      twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 2
    funext k
    have e1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.charpoly = m.1.val.charpoly :=
      fun g => conjP_charpoly g.1 m.1
    have e2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.charpoly = m.2.val.charpoly :=
      fun g => conjP_charpoly g.2 m.2
    have d1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.det = m.1.val.det :=
      fun g => conjP_det g.1 m.1
    have d2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.det = m.2.val.det :=
      fun g => conjP_det g.2 m.2
    set g := Quotient.out q * (k : GLw a w × GLw (n - a) w)
    rw [ct_eq_mul_orbN E n a ha w f hf' _ (by rw [e1, e2]; exact hsep), e1, e2, d1, d2]
  have h2 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') =
      absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
        twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (orbN (Nat.add_sub_cancel' ha) w f) := by
    unfold twOrb
    rw [mul_finsum]
    refine finsum_congr fun q => ?_
    rw [avg_const_mul _ hc0]
    ring
  have hγ := blk_mem_parP E n a (n - a) (Nat.add_sub_cancel' ha) w m 0
  have hKG := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [h1, h2, ← GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi E n a ha w f hf' m hsep hγ,
    ← _root_.GlobalTheory.IwRed.twOrb_sub (GLw n w) (GlobalTheory.LFun.KGL w (n := n)) (parP a n w) hKG.1 hKG.2 (isClosed_parP E a n w) (GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL E a n w) _ hγ
      (_root_.GlobalTheory.LeviDesc.twCent_blk_le_parP E n a (n - a) _ w m hsep) f hf']

end GlobalTheory.LeviDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma

variable {K : UQ} {B : InvAlg K}

theorem mulLat_mem_iff (t : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (t : B.A) L ↔ ((t⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 h
    simpa [← mul_assoc] using hx
  · intro h
    exact Submodule.mem_map.2 ⟨_, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff (t : B.Aˣ) (L : Submodule K.O B.A) :
    t ∈ stabLat K.O L ↔ mulLat K.O (t : B.A) L = L := by
  constructor
  · intro h
    ext y
    rw [mulLat_mem_iff, h (((t⁻¹ : B.Aˣ) : B.A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    conv_rhs => rw [← h]
    rw [mulLat_mem_iff, ← mul_assoc, Units.inv_mul, one_mul]

theorem stabLat_mulLat (t : B.Aˣ) (L : Submodule K.O B.A) :
    stabLat K.O (mulLat K.O (t : B.A) L) = stabLat K.O L := by
  ext s
  change (∀ y, y ∈ mulLat K.O (t : B.A) L ↔ (s : B.A) * y ∈ mulLat K.O (t : B.A) L) ↔ ∀ y, y ∈ L ↔ (s : B.A) * y ∈ L
  simp only [mulLat_mem_iff]
  constructor
  · intro h y
    have := h ((t : B.A) * y)
    have e1 : ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * y) = y := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have e2 : ((t⁻¹ : B.Aˣ) : B.A) * ((s : B.A) * ((t : B.A) * y)) = s * y := by rw [mul_left_comm, e1]
    rwa [e1, e2] at this
  · intro h y
    rw [h (((t⁻¹ : B.Aˣ) : B.A) * y), mul_left_comm]

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  have h1 : ∀ x : H ⧸ (⊤ : Subgroup H), x = 1 := fun x =>
    QuotientGroup.induction_on x fun g => (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_top g)
  rw [hR, Subgroup.index_top, finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (h1 x) hx)]
  simp

theorem cast_finsum {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact (Rat.castHom ℂ).toAddMonoidHom.map_finsum h
  · have h' : ¬ (Function.support fun i => (f i : ℂ)).Finite := by
      have : (Function.support fun i => (f i : ℂ)) = Function.support f := by ext i; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma GlobalTheory.TwOrbLat in
theorem GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) δ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he hO a B hP β ε hε hβ b δ hδ
  set θ := thL a w with hθ
  set Kg := GlobalTheory.LFun.KGL w (n := a) with hKg
  set ι := mulGL e b with hι
  set T' := twCent θ δ with hT'
  have hCent : T' = B.T.map ι := _root_.GlobalTheory.TwOrbCent.twCent_eq_map E w hw K e he a B hP β ε hε hβ b δ hδ
  have hinj : Function.Injective ι := mulGL_injective e b
  have hθK : ∀ k ∈ Kg, θ k ∈ Kg := GlobalTheory.BCT.ThBasic.thL_mem_KGL hU a w

  have hstab : ∀ (t : B.Aˣ) (q : GLw a w), ι t ∈ Kg.map (MulAut.conj q).toMonoidHom ↔
      t ∈ stabLat K.O (GlobalTheory.TwLat.lat e b q) := by
    intro t q
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_stabLat_iff,
      ← latOf_mul e b t q, eq_comm, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b, mul_assoc]
  have hcpt : cptPart T' = (intUnits K.O B.A ⊓ B.T).map ι := by
    rw [hCent]
    unfold cptPart
    have hS : {x | x ∈ B.T.map ι ∧ IsCompact (closure (Subgroup.zpowers x : Set (GLw a w)))} =
        ι '' ((intUnits K.O B.A ⊓ B.T : Subgroup B.Aˣ) : Set B.Aˣ) := by
      ext x
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hc⟩
        exact ⟨t, ⟨(GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).1 hc, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hi, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).2 hi⟩
    rw [hS, ← MonoidHom.map_closure, Subgroup.closure_eq]
  have hRel : ∀ y : GLw a w, (T' ⊓ Kg.map (MulAut.conj y).toMonoidHom).relIndex (cptPart T') =
      (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro y
    have h1 : T' ⊓ Kg.map (MulAut.conj y).toMonoidHom = (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).map ι := by
      ext x
      rw [Subgroup.mem_inf, hCent]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hx⟩
        exact ⟨t, ⟨(hstab t y).1 hx, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hs, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (hstab t y).2 hs⟩
    rw [h1, hcpt, Subgroup.relIndex_map_map_of_injective _ _ hinj]

  set P : GLw a w → Prop := fun y => y⁻¹ * δ * θ y ∈ Kg with hP_def
  have hPinv : ∀ (y t k : GLw a w), t ∈ T' → k ∈ Kg → (P (t * y * k) ↔ P y) := by
    intro y t k ht hk
    have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (GlobalTheory.TwOrbConj.mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have e1 : (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
      calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [hd]
    simp only [hP_def]
    rw [e1]
    constructor
    · intro h
      have := Kg.mul_mem (Kg.mul_mem hk h) (Kg.inv_mem (hθK k hk))
      simpa [mul_assoc] using this
    · intro h
      exact Kg.mul_mem (Kg.mul_mem (Kg.inv_mem hk) h) (hθK k hk)

  have hsum : ∀ y : GLw a w, GlobalTheory.TwOrbConj.summand θ Kg δ ((Kg : Set (GLw a w)).indicator 1) y =
      if P y then ((((stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0 := by
    intro y
    have hconst : (fun k : Kg => (Kg : Set (GLw a w)).indicator 1 ((y * k)⁻¹ * δ * θ (y * k))) =
        fun _ => (if P y then (1 : ℂ) else 0) := by
      funext k
      have := hPinv y 1 k (T'.one_mem) k.2
      rw [one_mul] at this
      simp only [Set.indicator_apply, SetLike.mem_coe, Pi.one_apply]
      by_cases h : P y
      · rw [if_pos h, if_pos ((this.2 h))]
      · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
    unfold GlobalTheory.TwOrbConj.summand
    rw [hconst, avg_const, hRel]
    split_ifs <;> simp

  set X : Set (Submodule K.O B.A) := {L : Submodule K.O B.A | IsLat K.O K.E L ∧
    ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} with hX
  have hUni : ∀ y : GLw a w, P y ↔ GlobalTheory.TwLat.lat e b y ∈ X := by
    intro y
    simp only [hP_def, hX, Set.mem_setOf_eq]
    rw [GlobalTheory.T.twistedConj_integral_iff_lattice_unimodular E w hw K e he hO a B β b δ hδ y]
    exact ⟨fun h => ⟨latOf_isLat e b y, h⟩, fun h => h.2⟩
  let r : X → X → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ?_⟩, fun {L M} ⟨t, ht, h⟩ => ⟨t⁻¹, B.T.inv_mem ht, ?_⟩,
      fun {L M N} ⟨t, ht, h⟩ ⟨s, hs, h'⟩ => ⟨s * t, B.T.mul_mem hs ht, ?_⟩⟩
    · ext y; rw [mulLat_mem_iff]; simp
    · ext y; rw [mulLat_mem_iff, h, mulLat_mem_iff]; simp
    · ext y; rw [h', mulLat_mem_iff, h, mulLat_mem_iff, mulLat_mem_iff, ← mul_assoc]; simp [mul_comm]

  let φ : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)} →
      Orb K.O B.T X := fun q => Quot.mk _ ⟨GlobalTheory.TwLat.lat e b (Quotient.out q.1), (hUni _).1 q.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      obtain ⟨t, ht, h1⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
      simp only at h1
      rw [← latOf_mul e b t, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b] at h1
      apply Subtype.ext
      simp only
      rw [← DoubleCoset.out_eq' (H := T') (K := Kg) q, ← DoubleCoset.out_eq' (H := T') (K := Kg) q', DoubleCoset.eq]
      refine ⟨ι t, by rw [hCent]; exact ⟨t, ht, rfl⟩, _, Kg.inv_mem h1, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    · intro o
      induction o using Quot.ind with
      | mk L =>
        obtain ⟨q0, hq0⟩ := _root_.GlobalTheory.TwOrbLat.exists_lat_eq E w K e a B b L.1 L.2.1
        obtain ⟨t', ht', k, hk, he'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
          (DoubleCoset.out_eq' (H := T') (K := Kg) (DoubleCoset.mk T' Kg q0)).symm
        have hP0 : P q0 := (hUni q0).2 (hq0 ▸ L.2)
        refine ⟨⟨DoubleCoset.mk _ _ q0, by rw [he']; exact (hPinv q0 t' k ht' hk).2 hP0⟩, ?_⟩
        apply Quot.sound
        rw [hCent] at ht'
        obtain ⟨t, ht, rfl⟩ := ht'
        refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
        show L.1 = _
        simp only
        rw [he', mul_assoc, latOf_mul e b t,
          ← (GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b q0 (q0 * k)).2 (by simpa using hk), hq0]
        ext y; rw [mulLat_mem_iff, mulLat_mem_iff]; simp

  rw [GlobalTheory.TwOrbConj.twOrb_eq, orbSum, cast_finsum]
  simp_rw [hsum]
  rw [show (∑ᶠ q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)), if P (Quotient.out q) then
      ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0) =
      ∑ᶠ q : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)},
        ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) by
    exact (finsum_congr fun q => finsum_eq_if.symm).trans (finsum_subtype_eq_finsum_cond
      (fun q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) => P (Quotient.out q))
      (f := fun q => ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex
        (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)))).symm]
  refine finsum_eq_of_bijective φ hφ fun q => ?_
  obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (φ q)))
  have hs2 : GlobalTheory.TwLat.lat e b (Quotient.out q.1) = mulLat K.O (s : B.A) (Quot.out (φ q)).1 := hs'
  rw [hs2, stabLat_mulLat]
  push_cast
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem om_real_fock_eq : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  intro D cc δ t0 Q P X hX hB g hg T
  set G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.A g) with hG
  have hmt : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B (1 : GA D X.B)) = 1 := fun τ => by
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one]
  have hmove := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * G τ) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 * 1) g 1
    (fun τ => by simp) (fun τ => by simp) (fun τ => by simp [hG]) (fun τ => by rw [hmt])
    X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))).2
  have hsub := GlobalTheory.FockBaseChange.pureTensorO_subst D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) G
    (fun _ => 1) (fun _ => 1) X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  have hdet : ∀ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * ((G τ)⁻¹).det = 1 := fun τ => by
    have e := GlobalTheory.WeilVacMove.compAt_mt_mul_inv X.θ τ X.A g
    have hu : IsUnit (G τ) := IsUnit.of_mul_eq_one _ e
    rw [← Matrix.det_mul]
    rw [show compAt X.θ τ (Formalism.L2.Theta.mt X.A g) = G τ from rfl,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.det_one]
  change X.om (g, 1) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))) = pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))
  rw [hmove, _root_.GlobalTheory.NormDict.vacuum_smul_realA P X hX hB g hg, GlobalTheory.FiniteFock.pureTensorO_smul, hsub, _root_.GlobalTheory.NormDict.substF_invT_minorPol P X T G, map_smul, smul_smul,
    ← Finset.prod_mul_distrib]
  simp only [← mul_pow, hdet, one_pow, Finset.prod_const_one, one_smul]

end GlobalTheory.NormDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTwistBase
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdThCore

theorem weil_twist_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → R.ωP i t (1, k) f = ((R.xi t x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t k x hx f hf
  have h := GlobalTheory.TwistFactorProof.frame_ratio R (_root_.GlobalTheory.WeilUniq.weilDatum_unique D) (GlobalTheory.WeilChange.exists_weilDatum_twist D) hR.thP.ωP i A.μ0 t hx hf
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, Circle.coe_one, one_smul] at h
  exact h

end GlobalTheory.AdThCore
end

