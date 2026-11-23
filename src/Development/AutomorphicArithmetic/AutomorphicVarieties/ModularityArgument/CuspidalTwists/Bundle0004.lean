module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutOf4Of
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Cu.AutomorphyOfRankFourLift

theorem irr_cover {H H' K : Type} [Group H] [Group H'] [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (r : H →* Matrix n n K) (r' : H' →* Matrix n n K) (h : ∀ x, ∃ y, ∃ u : K, r x = u • r' y) (hr : Irr r) :
    Irr r' := by
  unfold Irr at hr ⊢
  rw [eq_top_iff, ← hr, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, u, e⟩ := h x
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem q_apply (d : Dat Ω l) (T : Tower d.D) (g : G T.F Ω) :
    ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r g =
      ((toB d.δ (resQ T.F g) : (Qbar l)ˣ) : Qbar l) •
        mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ) (resQ T.F g) := by
  ext i j
  simp only [PD.map_r, Matrix.map_apply, Dat.Q, MonoidHom.comp_apply, mapRep_apply, Matrix.smul_apply, smul_eq_mul,
    rep4, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, Units.val_one, one_smul, map_mul]
  rfl

end UpperTheory.V.Cu.AutomorphyOfRankFourLift

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
theorem UpperTheory.V.Cu.autOf4_of (hne : AlNe) : AutOf4 := by
  intro Ω _ _ _ l _ d T hT hok hirr
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  obtain ⟨π, hreg, hatt⟩ := d.aut T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  refine ⟨π, hreg, ?_⟩
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjDec
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section Alg

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem tn_map (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

private theorem flg_map (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem adj_flg (x s : R) : adj (flg x s) = nA (-s) * tn (low (-x)) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev] <;> ring

private theorem conj_flg (a x y s s' : R) (g t : M2 R) :
    adj (flg y s') * (a • tn g t) * flg x s = a • (nA (-s') * tn (low (-y) * g * low x) t * nA s) := by
  have e : tn (low (-y) * g * low x) t = tn (low (-y)) 1 * tn g t * tn (low x) 1 := by
    rw [← tn_mul, ← tn_mul, one_mul, mul_one]
  rw [adj_flg, e, flg]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

private theorem isUp_mid (a : R) {m t : M2 R} {s s' : R} (hm01 : m 0 1 = 0) (hm10 : m 1 0 = 0) (ht01 : t 0 1 = 0)
    (ht10 : t 1 0 = 0) (hs1 : t 1 1 * s = t 0 0 * s') (hs2 : t 1 1 * s' = t 0 0 * s) :
    IsUp (a • (nA (-s') * tn m t * nA s)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [nA, tn, Matrix.mul_apply, Fin.sum_univ_succ, hm01, hm10, ht01, ht10] at hij ⊢ <;>
    first
    | linear_combination (a * m 0 0) * hs1
    | linear_combination (-(a * m 0 0)) * hs1
    | linear_combination (a * m 1 1) * hs2

end Alg

private theorem conj_dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A A' : ValuationSubring Ω} {g s : G ℚ Ω}
    (hA : ∀ x, g x ∈ A' ↔ x ∈ A) (hs : s ∈ Dec (F := ℚ) A') : g⁻¹ * s * g ∈ Dec (F := ℚ) A :=
  UpperTheory.V.conjGal_mem_Dec (τ := RingEquiv.refl ℚ) (σ := g.toRingEquiv) (fun x => g.commutes x) hA hs

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy

private theorem phi_ne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (h : D.Good) (pr : Bool) (k : ℕ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Dec (F := ℚ) A, Raw.bar (Phi D pr k) s ≠ 1 := by
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  obtain ⟨u, hu, -⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l _ A hl.out (h.pl_over l hl.out) hA
  have hc : chiO ℚ Ω l c.O (D.sg l) = 1 := by simp [chiO, h.sg_cyc]
  have e : Phi D pr k (u⁻¹ * D.sg l * u) = (D.ξ * D.Psi ^ (if pr then (-1 : ℤ) else 1)) (D.sg l) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    cases pr <;> simp [Phi, phi, Raw.Psi, Chr.Psi, hc]
  exact ⟨_, hu _ (h.sg_frob l hT).1, fun h' => h.condD l hT _
    ((congrArg (fun z : c.Oˣ => residue c.O (z : c.O)) e).symm.trans h')⟩

theorem overOf4 : OverOf4 := by
  intro Ω _ _ _ l _ d T hT R _ f hf
  refine ⟨rfl, fun v' => ?_⟩
  obtain ⟨v, g, hg⟩ := (d.T₀.cover (T.pl v') (T.ovl v')).exists
  refine ⟨v, g, hg, ?_⟩
  obtain ⟨s, hs, hne⟩ := phi_ne d.D d.ctx.1 d.T₀.pr d.k (T.pl v') (T.ovl v')
  have ht : (resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g ∈ Dec (F := ℚ) (d.T₀.pl v) := conj_dec hg hs
  have h1 : ∀ t, ((d.ρ₁ t).map f) 1 1 = 1 ∧ ((d.ρ₁ t).map f) 0 1 = 0 := fun t =>
    ⟨by simpa [sub_eq_zero] using hf _ (d.mod.red t).2.1, hf _ (d.mod.red t).2.2⟩
  have h0 : ∀ t, ((d.ρ₁ t).map f) 0 0 = f (inc d.h (Phi d.D d.T₀.pr d.k t)) := fun t => by
    simpa [sub_eq_zero] using hf _ (d.mod.red t).1
  have hk := key (g := (d.ρ₁ (resQ d.T₀.F g)).map f) (s := (d.ρ₁ s).map f)
    (t := (d.ρ₁ ((resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g)).map f) (x := f (d.x (d.T₀.pl v))) (y := f (d.x (T.pl v')))
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul]; congr 2; group)
    (by rw [h0]; exact (((Phi d.D d.T₀.pr d.k _).isUnit.map (inc d.h)).map f).ne_zero) (h1 _) (h1 _) (h1 _)
    (fun h => by
      rw [h0] at h
      have hn : ¬ IsUnit ((Phi d.D d.T₀.pr d.k s : d.c.O) - 1) := fun hu => by
        have := ((hu.map (inc d.h)).map f).ne_zero
        rw [map_sub, map_sub, map_one, map_one, h, sub_self] at this
        exact this rfl
      refine hne ?_
      show residue d.c.O (Phi d.D d.T₀.pr d.k s : d.c.O) = 1
      rw [← map_one (residue d.c.O)]
      exact Ideal.Quotient.eq.2 hn)
    (by simpa using congrArg f (d.mod.flag _ (d.T₀.ovl v) _ ht))
    (by simpa using congrArg f (d.mod.flag _ (T.ovl v') _ hs))
  have z01 : f (d.τ (resQ d.T₀.F g) 0 1) = 0 := hf _ (d.tau.red _).2
  have hsg := d.tau.mov (d.T₀.pl v) (T.pl v') (resQ d.T₀.F g) (d.T₀.ovl v) hg
  have hτ : ((d.τ (resQ d.T₀.F g)).map f) 1 0 = 0 ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (d.T₀.pl v)) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (T.pl v')) ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (T.pl v')) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (d.T₀.pl v)) := by
    simp only [Matrix.map_apply]
    by_cases hK : resQ d.T₀.F g ∈ d.K'.fixingSubgroup
    · obtain ⟨e1, e2⟩ := d.tau.on _ hK
      rw [e1, e2, hsg.1 hK, z01]
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨e1, e2⟩ := d.tau.off _ hK
      rw [e1, e2, hsg.2 hK, map_neg, map_neg, map_neg, z01]
      exact ⟨neg_zero, by ring, by ring⟩
  have e : ((d.Q d.T₀).map f).r g =
      f (toC d.h d.δ (resQ d.T₀.F g)) • tn ((d.ρ₁ (resQ d.T₀.F g)).map f) ((d.τ (resQ d.T₀.F g)).map f) := by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have e1 : ((d.Q d.T₀).map f).n v = flg (f (d.x (d.T₀.pl v))) (f (d.s (d.T₀.pl v))) := by
    rw [← flg_map]; rfl
  have e2 : ((d.Q T).map f).n v' = flg (f (d.x (T.pl v'))) (f (d.s (T.pl v'))) := by
    rw [← flg_map]; rfl
  rw [e, e1, e2, conj_flg]
  refine isUp_mid _ ?_ ?_ (by simpa using z01) hτ.1 hτ.2.1 hτ.2.2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (h1 (resQ d.T₀.F g)).2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination hk

end UpperTheory.V.Cu

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjDiag
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourResidualFlag

section Alg

variable {R : Type} [CommRing R]

def mat (P b e : R) : M4 R := !![P, 0, 0, 0; 0, P * e, 0, 0; 0, -(b * e), e, 0; b, 0, 0, 1]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem flg_map {R' : Type} [CommRing R'] (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  rw [flg_eq, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem flg_10 (x s : R) : flg x s 1 0 = s := by
  rw [flg_eq]
  simp

theorem conj_diag (x s dl P b e : R) (i : Fin 4) :
    (adj (flg x s) * (dl • mat P b e) * flg x s) i i = (dl • mat P b e) i i := by
  rw [flg_eq]
  fin_cases i <;> simp [adj_apply, mat, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev]

theorem mat_supp {S : Finset (ℤ × ℤ)} (h1 : wt 2 1 ∈ S) (h2 : wt 3 0 ∈ S) (dl P b e : R) : SuppM S (dl • mat P b e) := by
  intro i j hij hw
  fin_cases i <;> fin_cases j <;> first | (simp [mat]; done) | exact absurd h1 hw | exact absurd h2 hw | exact absurd rfl hij

theorem tn_map {R' : Type} [CommRing R'] (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

theorem tn_eq (g t : M2 R) (hg : g 0 1 = 0) (ht1 : t 0 1 = 0) (ht2 : t 1 0 = 0) (ht0 : t 0 0 = 1)
    (hg1 : g 1 1 = 1) : tn g t = mat (g 0 0) (g 1 0) (t 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, mat, hg, ht1, ht2, ht0, hg1]

theorem res_mul {O : Type} [CommRing O] [IsLocalRing O] (u v : Oˣ) {t : ResidueField O}
    (h : residue O ((u * v⁻¹ : Oˣ) : O) = t) : residue O (u : O) = t * residue O (v : O) := by
  have e : (u : O) = ((u * v⁻¹ : Oˣ) : O) * (v : O) := by simp
  rw [e, map_mul, h]

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem chi_mul {c : Coef l} (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * chi D pr 3 g = chi D pr 1 g * chi D pr 2 g := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]

private theorem inc_mem {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  have hint : (inc h).IsIntegral := by
    intro y
    obtain ⟨p, hp, e⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact e
  haveI : IsLocalHom (inc h) := hint.isLocalHom (Subalgebra.inclusion_injective h)
  exact map_nonunit (inc h) x hx

theorem eq_of_res {c c' : Coef l} (h : c.O ≤ c'.O) {R : Type} [CommRing R]
    (f : c'.O →+* R) (hf : ∀ y ∈ maximalIdeal c'.O, f y = 0) {x y : c.O} (e : residue c.O x = residue c.O y) :
    f (inc h x) = f (inc h y) := by
  have h1 : x - y ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, e, sub_self]
  have h2 := hf _ (inc_mem h h1)
  rwa [map_sub, map_sub, sub_eq_zero] at h2

end UpperTheory.V.Cu.RankFourResidualFlag

open UpperTheory.V.Cu.RankFourResidualFlag in
theorem UpperTheory.V.Cu.resOf4 : UpperTheory.V.Cu.ResOf4 := by
  intro Ω _ _ _ l _ d T hT W R _ f hf
  have hpr : T.pr = d.T₀.pr := hT.pr

  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (Phi d.D d.T₀.pr d.k g : d.c.O)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have h01 : ∀ g, f (d.ρ₁ g 0 1) = 0 := fun g => hf _ (d.mod.red g).2.2
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t01 : ∀ g, f (d.τ g 0 1) = 0 := fun g => hf _ (d.tau.red g).2
  have hne : ∀ u : d.c.Oˣ, f (inc d.h (u : d.c.O)) ≠ 0 := fun u => by
    have : IsUnit (f (inc d.h (u : d.c.O))) := (u.isUnit.map (inc d.h)).map f
    exact this.ne_zero

  have sgnK : ∀ g : G T.F Ω, ∃ e : R, (e = 1 ∨ e = -1) ∧ f (d.τ (resQ T.F g) 1 1) = e ∧ f (d.τ (resQ T.F g) 1 0) = 0 ∧
      f (inc d.h (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * e ∧
      f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 3 (resQ T.F g) : d.c.O)) * e := by
    intro g
    have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
    have hrb : ∀ t : ResidueField d.c.O, d.T₀.rb wAl (resLe hT.le g) = t →
        residue d.c.O (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O) =
          t * residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) := fun t ht => by
      apply res_mul
      simp only [Tower.rb, Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, wAl, zpow_one,
        zpow_zero, mul_one, hres] at ht
      exact ht
    have hprod := congrArg (fun u : d.c.Oˣ => f (inc d.h (u : d.c.O))) (chi_mul d.D d.T₀.pr (resQ T.F g))
    simp only [Units.val_mul, map_mul] at hprod
    have h0 := hne (chi d.D d.T₀.pr 0 (resQ T.F g))
    by_cases hK : resQ T.F g ∈ d.K'.fixingSubgroup
    · have e1 := hrb 1 (d.quad.on _ (by rwa [hres]))
      rw [one_mul] at e1
      have e2 := eq_of_res d.h f hf e1.symm
      obtain ⟨a1, a2⟩ := d.tau.on _ hK
      refine ⟨1, Or.inl rfl, by rw [a1, t00], by rw [a2, t01], by rw [e2, mul_one], ?_⟩
      rw [e2] at hprod
      rw [mul_one]
      exact (mul_left_cancel₀ h0 hprod).symm
    · have e1 := hrb (-1) (d.quad.off _ (by rwa [hres]))
      have e1' : residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) =
          residue d.c.O (-(chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) := by
        rw [map_neg, e1]
        ring
      have e2 := eq_of_res d.h f hf e1'
      rw [map_neg, map_neg] at e2
      obtain ⟨a1, a2⟩ := d.tau.off _ hK
      refine ⟨-1, Or.inr rfl, by rw [a1, map_neg, t00], by rw [a2, map_neg, t01, neg_zero], by rw [e2]; ring, ?_⟩
      rw [e2] at hprod
      have := mul_left_cancel₀ h0 (hprod.trans (by ring) : _ = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) *
        (-f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O))))
      rw [this]
      ring

  have hr : ∀ g, ((d.Q T).map f).r g = f (inc d.h (d.δ (resQ T.F g) : d.c.O)) •
      tn ((d.ρ₁ (resQ T.F g)).map f) ((d.τ (resQ T.F g)).map f) := fun g => by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have key : ∀ g : G T.F Ω, ∃ e P b dl : R, ((d.Q T).map f).r g = dl • mat P b e ∧
      (f.comp (inc d.h)) ((T.fr W).χ 0 g : d.c.O) = dl * P ∧ (f.comp (inc d.h)) ((T.fr W).χ 1 g : d.c.O) = dl * (P * e) ∧
      (f.comp (inc d.h)) ((T.fr W).χ 2 g : d.c.O) = dl * e ∧ (f.comp (inc d.h)) ((T.fr W).χ 3 g : d.c.O) = dl := by
    intro g
    obtain ⟨e, -, he, he10, e1, e2⟩ := sgnK g
    have hrg := hr g
    have hχ : ∀ i, (f.comp (inc d.h)) ((T.fr W).χ i g : d.c.O) =
        f (inc d.h (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O)) := fun i => by
      rw [← hpr]
      rfl
    generalize resQ T.F g = g' at he he10 e1 e2 hrg hχ
    have r0 : f (inc d.h (chi d.D d.T₀.pr 0 g' : d.c.O)) =
        f (inc d.h (d.δ g' : d.c.O)) * f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)) := by
      rw [← map_mul, ← map_mul]
      apply eq_of_res d.h f hf
      rw [map_mul]
      exact d.tw.red0 g'
    have r3 := eq_of_res d.h f hf (d.tw.red3 g')
    refine ⟨e, f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)), f (d.ρ₁ g' 1 0), f (inc d.h (d.δ g' : d.c.O)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrg, tn_eq _ _ (by rw [Matrix.map_apply]; exact h01 _) (by rw [Matrix.map_apply]; exact t01 _)
        (by rw [Matrix.map_apply]; exact he10) (by rw [Matrix.map_apply]; exact t00 _) (by rw [Matrix.map_apply]; exact h11 _)]
      simp only [Matrix.map_apply]
      rw [h00, he]
    · rw [hχ 0]
      exact r0
    · rw [hχ 1, e1, r0]
      ring
    · rw [hχ 2, e2, r3]
    · rw [hχ 3]
      exact r3
  have hn : ∀ v, ((d.Q T).map f).n v = flg (f (d.x (T.pl v))) (f (d.s (T.pl v))) := fun v => flg_map f _ _
  have hs : ∀ S : Finset (ℤ × ℤ), wt 2 1 ∈ S → wt 3 0 ∈ S → Supp S ((d.Q T).map f).r := fun S h1 h2 g => by
    obtain ⟨e, P, b, dl, h, -⟩ := key g
    rw [h]
    exact mat_supp h1 h2 dl P b e
  have hsM : Supp nM ((d.Q T).map f).r := hs nM (by decide) (by decide)
  refine ⟨⟨fun g i => ?_, fun (v : T.ι) s _ i => ?_, Or.inr hsM⟩, hsM, ⟨hs aA (by decide) (by decide), fun v => ?_⟩, fun g => ?_⟩
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key g
    rw [h]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key s
    show (adj (((d.Q T).map f).n v) * ((d.Q T).map f).r s * ((d.Q T).map f).n v) i i = _
    rw [hn v, h, conj_diag]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · rw [hn, flg_10]
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> simp
  · rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h01]
    ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ContOf4
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section
variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_map {S : Type} [CommRing S] {J : Ideal S} (φ : R →+* S) (h : I ≤ J.comap φ) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := fun N =>
  (hf N).comp (Ideal.quotientMap (J ^ N) φ ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow φ N)))

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x :=
  fun N => (hf N).mul (hg N)

private theorem ac_neg {f : Γ → R} (hf : AdicCont I f) : AdicCont I fun x => -f x :=
  fun N => (hf N).neg

private theorem ac_tn {f t : Γ → M2 R} (hf : ∀ i j, AdicCont I fun g => f g i j)
    (ht : ∀ i j, AdicCont I fun g => t g i j) (i j : Fin 4) : AdicCont I fun g => tn (f g) (t g) i j := by
  fin_cases i <;> fin_cases j <;> simp [tn] <;>
    first
    | exact ac_mul (hf _ _) (ht _ _)
    | exact ac_neg (ac_mul (hf _ _) (ht _ _))

end

theorem contOf4 : ContOf4 := by
  intro Ω _ _ _ l _ d T
  have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
  have hm : maximalIdeal d.c.O ≤ (maximalIdeal d.c₁.O).comap (inc d.h) := fun x hx =>
    (UpperTheory.V.Fr.sc_norm l d.c₁ (inc d.h x)).2.2 ((UpperTheory.V.Fr.sc_norm l d.c x).2.1 hx)
  have h1 : (d.Q T).Cont (maximalIdeal d.c₁.O) := fun i j N =>
    (ac_mul (ac_map (inc d.h) hm d.tw.cont) (ac_tn d.mod.cont d.tau.cont i j) N).comp_continuous hc
  exact ⟨h1, fun R _ f hf i j => ac_map (J := ⊥) f (fun y hy => Ideal.mem_comap.2 (Ideal.mem_bot.2 (hf y hy))) (h1 i j)⟩

end UpperTheory.V.Cu

end
end

