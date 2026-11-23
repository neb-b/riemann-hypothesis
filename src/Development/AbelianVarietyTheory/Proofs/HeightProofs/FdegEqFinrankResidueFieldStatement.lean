module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FdegEqFinrankResidueField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

open IsLocalRing GlobalTheory.ResDegPlace in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fdeg_eq_finrank_residueField_alt : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif (A := A) ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by
  intro R R' F _ _ _ _ _ _ _ _ _ _ _ hRR L _ _ _ _ A _ _ ϖ h ζ _ w hw S _ u Ψ ι hΨ hcomp hι hord
    hres
  let := resAlg (F := F) w
  have ord_pos_iff (a : As R' A) : 0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
    rw [ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]
    change 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
    generalize vL ζ a = v
    cases v with
    | top => simp
    | coe n =>
      rw [ENat.map_natCast, WithTop.coe_pos]
      simp [Nat.pos_iff_ne_zero]
  have exists_approx (x : A) (hx : 0 ≤ ord ϖ ζ x) :
      ∃ a : As R' A, 0 < ord ϖ ζ ((a : A) - x) := by
    obtain ⟨n, hn⟩ := h.denom x
    have h1 := hx
    rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
      IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
    have h2 : algebraMap (As R' A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As R' A)) =
        algebraMap (As R' A) (Loc ζ) (algebraMap R' (As R' A) ϖ ^ n * b) := by
      rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
    have h3 : (algebraMap R' A ϖ) ^ n * ((((t : As R' A) : A) * ((s : As R' A) : A)) * x) =
        (algebraMap R' A ϖ) ^ n * (((t : As R' A) : A) * (b : A)) := by
      have := congrArg Subtype.val ht
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
      have e : ((algebraMap R' (As R' A) ϖ : As R' A) : A) = algebraMap R' A ϖ := rfl
      rw [e] at this
      linear_combination this
    have h4 := (h.isUnit.pow n).mul_right_inj.1 h3
    obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
    refine ⟨d * (t * b), ?_⟩
    have h5 : ((d * (t * b) : As R' A) : A) - x = ((-i : As R' A) : A) * x := by
      have := congrArg Subtype.val hdi
      simp only [AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
        NegMemClass.coe_neg] at this ⊢
      linear_combination x * this - (d : A) * h4
    rw [h5, ord_mul ζ h]
    exact add_pos_of_pos_of_nonneg ((ord_pos_iff _).2 (ζ.asIdeal.neg_mem hi)) hx
  let T : Subring (As R' A × vRing w) :=
    { carrier := {z | 0 < u (Ψ (z.1 : A) - ι (z.2 : L))}
      mul_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2))
        have e : Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2) =
            (Ψ (z'.1 : A) - ι (z'.2 : L)) * Ψ z.1 + (Ψ (z.1 : A) - ι (z.2 : L)) * ι z'.2 := by
          rw [map_mul, map_mul]; ring
        rw [e]
        refine u.map_lt_add ?_ ?_
        · rw [u.map_mul, ← hord]
          exact add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ h z.1.2)
        · rw [u.map_mul, hι]
          exact add_pos_of_pos_of_nonneg hz z'.2.2
      one_mem' := by
        change 0 < u (Ψ 1 - ι 1)
        simp
      add_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) + z'.1) - ι ((z.2 : L) + z'.2))
        rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
        exact u.map_lt_add hz hz'
      zero_mem' := by
        change 0 < u (Ψ 0 - ι 0)
        simp
      neg_mem' := by
        intro z hz
        change 0 < u (Ψ (-(z.1 : A)) - ι (-(z.2 : L)))
        rw [map_neg, map_neg, ← neg_sub', u.map_neg]
        exact hz }
  have hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - ι (z.1.2 : L)) := fun z => z.2
  let jw : R →+* vRing w := (algebraMap R L).codRestrict (vRing w) (fun r => (hw.2 r).1)
  let j : R →+* T := (((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T
    (fun r => by
      change 0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - ι (algebraMap R L r))
      rw [hcomp, sub_self]; simp)
  have hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (hw.2 a).1
  let φ : R →+* (vRing w).comap (algebraMap F L) := (algebraMap R F).codRestrict _ hOw
  let p : T →+* ResidueField (Loc ζ) := ((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp
    ((RingHom.fst _ _).comp T.subtype)
  let q : T →+* ResidueField (vRing w) := (residue (vRing w)).comp
    ((RingHom.snd _ _).comp T.subtype)
  refine finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y
    obtain ⟨y, rfl⟩ := hRR y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨r, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := exists_eq_of_nonneg hw (x : F) x.2
    exact ⟨a, congrArg (residue _) (Subtype.ext ha)⟩
  · intro y
    have := ζ.isMaximal
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective ζ.asIdeal y
    obtain ⟨g, hg, hag⟩ := hres (Ψ a) (by rw [← hord]; exact ord_nonneg ζ h a.2)
    exact ⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩
  · intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    obtain ⟨x, hx⟩ := hΨ (ι g)
    obtain ⟨a, ha⟩ := exists_approx x (by rw [hord, hx, hι]; exact g.2)
    rw [hord, map_sub, hx] at ha
    exact ⟨⟨(a, g), ha⟩, rfl⟩
  · intro z
    change residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff, hord, ← hι]
    refine ⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩
    rw [← neg_sub, u.map_neg]
    exact hT z
  · intro r
    rfl
  · intro r
    change residue (vRing w) (comapIncl (vRing w) (algebraMap F L) (φ r)) = residue (vRing w) (jw r)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply R F L r).symm
