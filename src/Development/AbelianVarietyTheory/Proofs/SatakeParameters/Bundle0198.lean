module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConjDet

open ValuativeRel

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det_mul_sub_one_lt {r t : ℕ} {h : GL (Fin (r + t)) k} (hh : h ∈ blockGrp k r t) :
    valuation k (((h⁻¹ : GL (Fin (r + t)) k).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
  obtain ⟨g, hg⟩ := hh.1
  have hi := ((blockGrp k r t).inv_mem hh).2
  have hinv : (h⁻¹ : GL (Fin (r + t)) k) = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g⁻¹ := by
    rw [← hg, map_inv]
  have hC : ∀ (i : Fin t) (j : Fin r),
      (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j) ∈ 𝓂[k] := by
    intro i j
    have := hi (Fin.natAdd r i) j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    rw [hinv, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    change valuation k (algebraMap 𝒪[k] k ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j))) < 1 at this
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr this)
  have hres : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    ext i j
    have e1 : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val * g.val) (Fin.natAdd r i) (Fin.natAdd r j) =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have hm : ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
        g.val (Fin.castAdd t x) (Fin.natAdd r j) ∈ 𝓂[k] :=
      Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (hC i x)
    have e2 : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
        (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))) i j =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) -
          ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
            g.val (Fin.castAdd t x) (Fin.natAdd r j) := by
      simp only [Matrix.mul_apply, Matrix.submatrix_apply]; rw [← e1]; ring
    rw [Matrix.map_apply, e2, map_sub, (IsLocalRing.residue_eq_zero_iff _).2 hm, sub_zero]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have hm : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply,
      hres, Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ∀ G : GL (Fin (r + t)) 𝒪[k],
      ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) G).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
        (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    intro G
    rw [show (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) =
      algebraMap 𝒪[k] k (G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  rw [hinv, ← hg, e, e]
  simpa only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] using hv

end

end GlobalTheory.BlockConjDet

namespace GlobalTheory.BlockConjDet

theorem blockChar_eq_inv_detDD : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → ∃ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (d * b * d⁻¹) ∧ ∀ μ : (s.w.adicCompletion L)ˣ →* ℂˣ, IsTame μ → blockChar μ (Matrix.GeneralLinearGroup.map c.toRingHom a) = (((μ (Units.map c.toMonoidHom u))⁻¹ : ℂˣ) : ℂ) := by
  intro L _ _ _ s r t c _ a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact (WithZero.exp_ne_zero hϖ.symm).elim
  have hdinv : (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val =
      Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) := by
    have h1 : d.val * Matrix.diagonal (fun i : Fin (r + t) =>
        if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; ext i; split_ifs <;> simp [hϖ0]
    calc (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val
        = (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val * (d.val * Matrix.diagonal (fun i : Fin (r + t) =>
          if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hDD : NG.detDD s r (d * b * d⁻¹) =
      ((a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    let e : Fin t ≃ {x : Fin (r + t) // r ≤ x.val} :=
      { toFun := fun i => ⟨Fin.natAdd r i, by simp⟩
        invFun := fun x => ⟨x.1.val - r, by omega⟩
        left_inv := fun i => by ext; simp
        right_inv := fun x => by ext; simp; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
    congr 1
    ext i j
    have hn : ∀ x : Fin t, ¬ ((Fin.natAdd r x : Fin (r + t)) : ℕ) < r := by intro x; simp
    simp only [e, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.coe_fn_mk, Units.val_mul,
      hdinv, hd, Matrix.mul_diagonal, Matrix.diagonal_mul, hb]
    rw [if_neg (hn _), if_neg (hn _), mul_comm ϖ, mul_inv_cancel_right₀ hϖ0]
  have hc : c (NG.detDD s r (d * b * d⁻¹)) =
      (((Matrix.GeneralLinearGroup.map c.toRingHom a)⁻¹ : GL (Fin (r + t)) (s.w.adicCompletion L)).val.submatrix
        (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [hDD, ← map_inv]
    exact RingHom.map_det c.toRingHom _
  have hv := val_det_mul_sub_one_lt ha
  have hne : ∀ x y : s.w.adicCompletion L, ValuativeRel.valuation _ (x * y - 1) < 1 → x ≠ 0 ∧ y ≠ 0 := by
    intro x y h
    constructor <;> rintro rfl <;> simp at h
  obtain ⟨h1, h2⟩ := hne _ _ hv
  have hF : NG.detDD s r (d * b * d⁻¹) ≠ 0 := fun h0 => h1 (by rw [← hc, h0, map_zero])
  refine ⟨Units.mk0 _ hF, rfl, fun μ hμ => ?_⟩
  rw [blockChar_eq μ _ (Units.mk0 _ h2) rfl]
  have ht := hμ (Units.map c.toMonoidHom (Units.mk0 _ hF) * Units.mk0 _ h2) (by
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0]
    rw [show (c.toMonoidHom : _ →* _) (NG.detDD s r (d * b * d⁻¹)) = c (NG.detDD s r (d * b * d⁻¹)) from rfl, hc]
    exact hv)
  rw [map_mul] at ht
  rw [eq_inv_of_mul_eq_one_right ht]

end GlobalTheory.BlockConjDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Val

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem val_lt_one_of_norm_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have h2 : Filter.Tendsto (fun n : ℕ => e z ^ n) Filter.atTop (nhds 0) := by
    have := ((he.tendsto 0).comp h1)
    simpa [Function.comp_def, map_pow] using this
  have h3 : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (h2.eventually h3).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation F (e z ^ n) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hn (not_lt.2 this)

theorem val_natCast_le_one (c : ℕ) : valuation F (c : F) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact (valuation F).map_add_le ih (by simp)

theorem val_le_one_of_norm_le_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ ≤ 1) :
    valuation F (e z) ≤ 1 := by
  let zi : ℤ_[g] := ⟨z, hz⟩
  have hm := PadicInt.sub_zmodRepr_mem zi
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hm
  have hm' : ‖z - (zi.zmodRepr : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hm
    exact hm
  have h1 := val_lt_one_of_norm_lt_one e he hm'
  have hz' : e z = e (z - (zi.zmodRepr : ℚ_[g])) + (zi.zmodRepr : F) := by
    rw [map_sub, map_natCast]; ring
  rw [hz']
  exact (valuation F).map_add_le h1.le (val_natCast_le_one _)

theorem norm_lt_one_of_val_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {y : ℚ_[g]}
    (hy : valuation F (e y) < 1) : ‖y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hy0 : y ≠ 0 := by rintro rfl; simp at hc; exact absurd hc (by norm_num)
  have h1 : ‖y⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := val_le_one_of_norm_le_one e he h1
  have h3 : valuation F (e y) * valuation F (e y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  have h4 : valuation F (e y) * valuation F (e y⁻¹) ≤ valuation F (e y) * 1 := by gcongr
  rw [h3, mul_one] at h4
  exact absurd hy (not_lt.2 h4)

theorem entry_of_val (e : ℚ_[g] ≃+* F) (he : Continuous e) (x : F) (c : ℕ) (hx : valuation F (x - c) < 1) :
    ∃ hA : ‖e.symm x‖ ≤ 1, PadicInt.toZMod (⟨e.symm x, hA⟩ : ℤ_[g]) = c := by
  have h1 : ‖e.symm x - c‖ < 1 :=
    norm_lt_one_of_val_lt_one e he (by rwa [map_sub, map_natCast, e.apply_symm_apply])
  have hc : ‖(c : ℚ_[g])‖ ≤ 1 := by
    have := PadicInt.norm_le_one (c : ℤ_[g])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  have hA : ‖e.symm x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (e.symm x - c) (c : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1.le hc)
  refine ⟨hA, ?_⟩
  let zi : ℤ_[g] := ⟨e.symm x, hA⟩
  have hm : zi - (c : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def]
    simpa using h1
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at hm
  exact hm

end Val

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Mat

variable {g : ℕ} [Fact g.Prime]

def bm (r t : ℕ) (h : Gn g r) : Mt g (r + t) := fun i j =>
  if (i : ℕ) < r ∧ (j : ℕ) < r then entN (h : Mt g r) i j
  else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then entN ((1 : Gn g t) : Mt g t) (i - r) (j - r) else 0

theorem bm_isUnit (r t : ℕ) (h : Gn g r) : IsUnit (bm r t h) := by
  set M := bm r t h with hM
  have h0 : InPar r M := fun i j hj hi => by
    rw [hM]; show bm r t h i j = 0; unfold bm; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = h := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, entN, hM, bm, hi, hj]
  have h2 : br r t M = 1 := by
    ext i j
    simp [br, entN, hM, bm]
  have hd := LabelDet.det_inPar r t M h0
  rw [h1, h2, Matrix.det_one, mul_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det, hd]
  exact Matrix.isUnits_det_units h

theorem blk_val (r t : ℕ) (h : Gn g r) : ((blk r t (r + t) h 1 : Gn g (r + t)) : Mt g (r + t)) = bm r t h := by
  show ((toG (bm r t h) : Gn g (r + t)) : Mt g (r + t)) = bm r t h
  unfold toG
  rw [dif_pos (bm_isUnit r t h)]
  exact IsUnit.unit_spec _

theorem bm_apply (r t : ℕ) (h : Gn g r) (a b : Fin (r + t)) : bm r t h a b =
    if hab : (a : ℕ) < r ∧ (b : ℕ) < r then (h : Mt g r) ⟨a, hab.1⟩ ⟨b, hab.2⟩ else if a = b then 1 else 0 := by
  unfold bm
  by_cases hab : (a : ℕ) < r ∧ (b : ℕ) < r
  · rw [if_pos hab, dif_pos hab]; simp [entN, hab]
  · rw [if_neg hab, dite_eq_right hab]
    by_cases h2 : r ≤ (a : ℕ) ∧ r ≤ (b : ℕ)
    · rw [if_pos h2]
      have ha : (a : ℕ) - r < t := by omega
      have hb : (b : ℕ) - r < t := by omega
      simp only [entN, dif_pos (And.intro ha hb), Units.val_one, Matrix.one_apply, Fin.ext_iff]
      congr 1
      apply propext
      omega
    · rw [if_neg h2, if_neg]
      intro e; subst e; omega

end Mat

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

theorem blockLift_act (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (r t : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V)
    (hu : u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) (h : GL (Fin r) (ZMod g))
    (h' : GL (Fin (r + t)) F) (hl : GlobalTheory.PendOf.IsLiftN h h') :
    ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  classical
  have hent : ∀ a b : Fin (r + t), ∃ hA : ‖e.symm (h'.val a b)‖ ≤ 1,
      PadicInt.toZMod (⟨e.symm (h'.val a b), hA⟩ : ℤ_[g]) = bm r t h a b := by
    intro a b
    have hab := hl a b
    rw [bm_apply]
    by_cases hc : (a : ℕ) < r ∧ (b : ℕ) < r
    · rw [dif_pos hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he _ _ hab
      exact ⟨hA, by rw [hA', ZMod.natCast_zmod_val]⟩
    · rw [dite_eq_right hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he (h'.val a b) (if a = b then 1 else 0)
        (by rw [hab]; split_ifs <;> simp)
      exact ⟨hA, by rw [hA']; split_ifs <;> simp⟩
  choose hA hA' using hent
  let A : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g] := fun a b => ⟨e.symm (h'.val a b), hA a b⟩
  have hmap : (PadicInt.toZMod (p := g)).mapMatrix A = bm r t h := by
    ext a b
    exact hA' a b
  have hdet : IsUnit A.det := by
    by_contra hn
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hmap] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bm_isUnit r t h)).ne_zero h1
  let A' : GL (Fin (r + t)) ℤ_[g] := Matrix.GeneralLinearGroup.mk'' A hdet
  have hred : red g (r + t) A' = blk r t (r + t) h 1 := by
    ext a b
    rw [blk_val]
    exact hA' a b
  have hh' : Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) A') = h' := by
    ext a b
    show e (algebraMap ℤ_[g] ℚ_[g] (A a b)) = h'.val a b
    rw [PadicInt.algebraMap_apply]
    exact e.apply_symm_apply _
  have hx0 : red g (r + t) (Function.invFun (red g (r + t)) (blk r t (r + t) h 1)) = blk r t (r + t) h 1 :=
    Function.invFun_eq ⟨A', hred⟩
  have hk : red g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A') = 1 := by
    rw [map_mul, map_inv, hx0, hred, inv_mul_cancel]
  have hfix := (Submodule.mem_iInf _).1 hu ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfix
  have hsplit : h' = Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1)) *
      Matrix.GeneralLinearGroup.map e.toRingHom
        (inc g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A')) := by
    rw [← hh', lift, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hsplit, map_mul, Module.End.mul_apply]
  congr 1

end GlobalTheory.SerSys.BlockLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacSuppCount


open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel in
theorem eq_mul_unrChar_of_eq_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ ω : kˣ →* ℂˣ), (∀ u : kˣ, ValuativeRel.valuation k (u : k) = 1 → ω u = χ u) → ∃ α : ℂˣ, ω = χ * GlobalTheory.SmGL.unrChar k α := by
  intro k _ _ _ _ χ ω h
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hu : IsUnram (χ⁻¹ * ω) := fun u hu => by
    simp [h u hu]
  refine ⟨(χ⁻¹ * ω) ϖ, ?_⟩
  rw [← eq_unrChar hu hϖ]
  ext u
  simp


open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.ProdSupport Matrix ValuativeRel TensorProduct in
theorem scalar_mem_KO_of_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : Type) [Fintype m] [DecidableEq m] {z : kˣ} (hz : ValuativeRel.valuation k (z : k) = 1) :
    GeneralLinearGroup.scalar m z ∈ KO k m := by
  have hz' : ValuativeRel.valuation k ((z⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hz, inv_one]
  have h1 : (z : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hz.le
  have h2 : ((z⁻¹ : kˣ) : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hz'.le
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · by_cases h : i = j
    · subst h; simpa [GeneralLinearGroup.scalar] using h1
    · simp [GeneralLinearGroup.scalar, h, zero_mem]
  · rw [← map_inv]
    by_cases h : i = j
    · subst h; simpa [GeneralLinearGroup.scalar] using h2
    · simp [GeneralLinearGroup.scalar, h, zero_mem]


open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.ProdSupport Matrix ValuativeRel TensorProduct in
theorem card_le_ncard_unrTwist : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s s' : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (d' : Fin s' → ℕ) (e : (Σ j, Fin (d' j)) ≃ Fin n) (A : Finset (Fin s')) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) → (∀ j ∈ A, d' j = 1) → x ≠ 0 → (∀ j ∈ A, ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (d' j)), GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → A.card ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro _ hG k _ _ _ _ n s s' χ π d σ d' e A x hχ hcs hA hx hact
  obtain ⟨-, hσ, e₀, hsub⟩ := hcs
  obtain ⟨Y, _, _, τ, y, hτ, hτs, hy, hτy⟩ := _root_.GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero _ _ (jac e π.π) x hx
  have hτP : IsSubquotient τ (jac e (multiProd e₀ fun a => (σ a).π)) :=
    hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _) hsub)
  obtain ⟨b, f, g, t, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e₀ e
    (fun a => (σ a).smooth) (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ hτP

  have hcolj : ∀ j ∈ A, ∃ i, b.1 i j = 1 ∧ ∀ i', i' ≠ i → b.1 i' j = 0 := by
    intro j hj
    have hsum : ∑ i, b.1 i j = 1 := by simpa [hA j hj] using b.2.2 j
    obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => b.1 i j) (Finset.mem_univ i)
    have h0 : ∑ i' ∈ Finset.univ.erase i, b.1 i' j = 0 := by simp only at hsplit; omega
    refine ⟨i, by simp only at hsplit; omega, fun i' hi' => ?_⟩
    exact Finset.sum_eq_zero_iff.1 h0 i' (Finset.mem_erase.2 ⟨hi', Finset.mem_univ i'⟩)
  rcases A.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  haveI : Nonempty (Fin s) := ⟨(hcolj j₀ hj₀).choose⟩
  choose! ι hι1 hι0 using hcolj

  have hrow1 : ∀ i j j', 0 < b.1 i j → 0 < b.1 i j' → j = j' := fun i =>
    _root_.GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k (d i) _ (σ i).π s' (b.1 i) (f i) _ (fun j => (t i j).ρ) (hσ i).2.2
      (fun j => Model.nontrivial_of_isIrreducible (t i j).irr) (hrow i)

  have hd1 : ∀ j ∈ A, d (ι j) = 1 := by
    intro j hj
    have h := b.2.1 (ι j)
    rw [Fintype.card_fin, Finset.sum_eq_single j (fun j' _ hj' => by
      by_contra hne
      exact hj' (hrow1 _ _ _ (Nat.pos_of_ne_zero hne) (by rw [hι1 j hj]; exact one_pos)))
      (by simp), hι1 j hj] at h
    exact h.symm
  have hinj : Set.InjOn ι (A : Set (Fin s')) := by
    intro j hj j' hj' h
    refine hrow1 (ι j) j j' (by rw [hι1 j hj]; exact one_pos) ?_
    rw [h, hι1 j' hj']; exact one_pos

  have hmem : ∀ j ∈ A, ι j ∈ {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv
      (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
    intro j hj
    set i := ι j with hi
    obtain ⟨ω, -, hω⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar (σ i).smooth (σ i).irr

    have hT : ∀ (z : kˣ) (v : ⨂[ℂ] j', (t i j').V),
        piTensor (fun j' => (t i j').ρ) (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b.1 i j)) z)) v =
          (ω z : ℂ) • v := fun z v =>
      Model.scalar_of_isSubquotient (hrow i) (_root_.GlobalTheory.JacGL1.jac_mulSingle_scalar k (d i) _ (σ i).π ω s' (b.1 i) (f i) j (hd1 j hj)
        (hι1 j hj) hω z) v
    have hωt : HasCentralChar (t i j).ρ ω := by
      obtain ⟨ω', -, hω'⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar (t i j).smooth (t i j).irr
      have := nontrivial_piTensor _ fun j' => Model.nontrivial_of_isIrreducible (t i j').irr
      obtain ⟨v, hv⟩ := exists_ne (0 : ⨂[ℂ] j', (t i j').V)
      have : ω' = ω := MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv
        ((piTensor_mulSingle (fun j' => (t i j').ρ) j _ _ (hω' z) v).symm.trans (hT z v)))
      exact this ▸ hω'
    have hz : ∀ i', i' ≠ i → IsEmpty (Fin (b.1 i' j)) := fun i' h' => by
      rw [hι0 j hj i' h']; infer_instance
    have hcen := hasCentralChar_multiProd (g j) (fun i' => (t i' j).ρ) i hz hωt
    have hωχ : ∀ u : kˣ, ValuativeRel.valuation k (u : k) = 1 → ω u = χ u := by
      intro u hu
      have h1 := Model.scalar_of_isSubquotient hcol
        (piTensor_mulSingle (fun j => multiProd (g j) fun i => (t i j).ρ) j _ _ (hcen u)) y
      have h2 := hτy _ _ (hact j hj _ (scalar_mem_KO_of_val (Fin (d' j)) hu))
      rw [det_scalar_one (hA j hj)] at h2
      exact Units.ext (smul_left_injective ℂ hy (h1.symm.trans h2))
    obtain ⟨α, hα⟩ := eq_mul_unrChar_of_eq_on_units k χ ω hωχ
    exact ⟨hd1 j hj, α, hα ▸ _root_.GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible k (d i) _ (σ i).π ω (hd1 j hj) (σ i).irr hω⟩
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn ι hmem hinj (Set.toFinite _)

end GlobalTheory.JacSuppCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  first | exact @GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | exact GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | (intros; apply GlobalTheory.DeRhamRead.isdRW_iff_isdRAt <;> assumption)
end

