module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0007
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelSecond
section
noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.lowerTriangularModel

open Formalism.FourierDecayAlt.P.Dx2.Rad (low low_apply low_coord)

variable {m : ℕ} (w : Equiv.Perm (Fin m))

def ht (q : Formalism.FourierDecayAlt.C2.Lstidx w) : ℕ := q.1.1.val - q.1.2.val

theorem low_upper (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (h : i < j) :
    low w y i j = 0 := by
  rw [low_apply, Matrix.one_apply_ne (ne_of_lt h), zero_add, dite_eq_right]
  rintro ⟨h1, -⟩
  exact absurd (lt_trans h1 h) (lt_irrefl _)

theorem low_diag (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i : Fin m) : low w y i i = 1 := by
  rw [low_apply, Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1), add_zero]

theorem low_bt (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) :
    (low w y).BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact low_upper w y i j hij

theorem low_det (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : (low w y).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (low_bt w y)]
  exact Finset.prod_eq_one fun i _ => low_diag w y i

abbrev M (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ := (low w y)⁻¹

theorem isUnit_low (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : IsUnit (low w y).det := by
  rw [low_det]
  exact isUnit_one

theorem M_upper (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (h : i < j) : M w y i j = 0 := by
  haveI := Matrix.invertibleOfIsUnitDet (low w y) (isUnit_low w y)
  exact Matrix.blockTriangular_inv_of_blockTriangular (low_bt w y) h

theorem mul_M (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : low w y * M w y = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_low w y)

theorem sum_split (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) :
    ∑ c, low w y i c * M w y c j =
      ∑ c ∈ Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i), low w y i c * M w y c j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · rcases not_and_or.1 h with h1 | h1
    · rw [M_upper w y c j (not_le.1 h1), mul_zero]
    · rw [low_upper w y i c (not_le.1 h1), zero_mul]

theorem M_diag (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i : Fin m) : M w y i i = 1 := by
  have h := congrFun (congrFun (mul_M w y) i) i
  rw [Matrix.mul_apply, sum_split, Matrix.one_apply_eq] at h
  have e : Finset.univ.filter (fun c => i ≤ c ∧ c ≤ i) = {i} := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  rw [e, Finset.sum_singleton, low_diag, one_mul] at h
  exact h

theorem M_rec (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (hji : j < i) :
    M w y i j + low w y i j =
      -∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), low w y i c * M w y c j := by
  have h := congrFun (congrFun (mul_M w y) i) j
  rw [Matrix.mul_apply, sum_split, Matrix.one_apply_ne (ne_of_gt hji)] at h
  have e : Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i) =
      insert i (insert j (Finset.univ.filter (fun c => j < c ∧ c < i))) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h2 | h2
      · rcases h1.lt_or_eq with h1 | h1
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
        · exact Or.inr (Or.inl h1.symm)
      · exact Or.inl h2
    · rintro (h | h | h)
      · exact ⟨h ▸ hji.le, h ▸ le_rfl⟩
      · exact ⟨h ▸ le_rfl, h ▸ hji.le⟩
      · exact ⟨h.1.le, h.2.le⟩
  have hi : i ∉ insert j (Finset.univ.filter (fun c => j < c ∧ c < i)) := by
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    exact ⟨ne_of_gt hji, fun h => lt_irrefl _ h.2⟩
  have hj : j ∉ Finset.univ.filter (fun c => j < c ∧ c < i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => lt_irrefl _ h.1
  rw [e, Finset.sum_insert hi, Finset.sum_insert hj, low_diag, one_mul, M_diag, mul_one] at h
  linear_combination h

theorem M_dep (n : ℕ) : ∀ (y y' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q, ht w q ≤ n → y q = y' q) →
    ∀ i j : Fin m, i.val - j.val ≤ n → M w y i j = M w y' i j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y y' hy i j hij
  rcases lt_trichotomy i j with h | h | h
  · rw [M_upper w y i j h, M_upper w y' i j h]
  · subst h; rw [M_diag, M_diag]
  · have hL : ∀ a b : Fin m, a.val - b.val ≤ n → low w y a b = low w y' a b := by
      intro a b hab
      rw [low_apply, low_apply]
      congr 1
      split_ifs with hq
      · exact hy _ hab
      · rfl
    have e1 := M_rec w y i j h
    have e2 := M_rec w y' i j h
    have hsum : ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), low w y i c * M w y c j =
        ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), low w y' i c * M w y' c j := by
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hc1 := Fin.lt_def.1 hc.1
      have hc2 := Fin.lt_def.1 hc.2
      rw [hL i c (by omega)]
      congr 1
      exact ih (c.val - j.val) (by omega) y y' (fun q hq => hy q (by omega)) c j le_rfl
    have := hL i j hij
    linear_combination e1 - e2 - this - hsum

def linv (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ := fun q => M w y q.1.1 q.1.2

theorem low_cont : Continuous (low w) := by
  have e : low w = fun y => Matrix.of fun i j =>
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : j < i ∧ w.symm i < w.symm j then y ⟨(i, j), h⟩ else 0 := by
    funext y; ext i j; exact low_apply w y i j
  rw [e]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_const.add (continuous_apply _)
  · exact continuous_const

theorem M_cont : Continuous (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) := by
  have e : (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) = fun y => (low w y).adjugate := by
    funext y
    show (low w y)⁻¹ = _
    rw [Matrix.inv_def, low_det, Ring.inverse_one, one_smul]
  rw [e]
  exact (low_cont w).matrix_adjugate

theorem linv_mp : MeasurePreserving (linv w) volume volume := by
  set τ : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx w, (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) → ℂ := fun q y => -(M w y q.1.1 q.1.2 + y q) with hτ
  have hmeas : ∀ q, Measurable (τ q) := fun q => by
    refine Measurable.neg (Measurable.add ?_ (measurable_pi_apply q))
    exact ((continuous_apply q.1.2).comp ((continuous_apply q.1.1).comp (M_cont w))).measurable
  have hdep : ∀ q (x x' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q', ht w q' < ht w q → x q' = x' q') → τ q x = τ q x' := by
    intro q x x' hx
    have hq := q.2.1
    have hq' := Fin.lt_def.1 hq
    simp only [hτ]
    congr 1
    have e1 := M_rec w x q.1.1 q.1.2 hq
    have e2 := M_rec w x' q.1.1 q.1.2 hq
    have hLq : ∀ y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ, low w y q.1.1 q.1.2 = y q :=
      fun y => low_coord w y q
    rw [hLq] at e1 e2
    rw [e1, e2]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hc1 := Fin.lt_def.1 hc.1
    have hc2 := Fin.lt_def.1 hc.2
    have hL : low w x q.1.1 c = low w x' q.1.1 c := by
      rw [low_apply, low_apply]
      congr 1
      split_ifs with h
      · exact hx _ (by simp only [ht]; omega)
      · rfl
    rw [hL]
    congr 1
    exact M_dep w (c.val - q.1.2.val) x x' (fun q' hq'' => hx q' (by simp only [ht] at hq'' ⊢; omega)) c q.1.2 le_rfl
  have hS := Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp _ (Formalism.FourierDecayAlt.C2.Lstidx w) rfl (fun _ => ℂ) (fun _ => volume) (ht w) τ hmeas hdep
  have hN := Measure.measurePreserving_neg (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ))
  have e : linv w = Neg.neg ∘ (fun g p => g p + τ p g) := by
    funext y q
    simp only [Function.comp_apply, Pi.neg_apply, hτ, linv]
    ring
  rw [e]
  exact hN.comp hS

end Formalism.L2.SG.lowerTriangularModel

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Rescale
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix

namespace Formalism.L2.SG.Pf.Rescale

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hE_swap (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, AlgHom.coe_toRingHom, map_sum, map_mul, hσ]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hJ.1]
  ring

theorem standard_gram_nondegenerate : Formalism.L2.SG.Pf.RescaleCore.GramStdND := by
  intro F E _ _ _ σ n J r P T hσ hJ hS
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := hS
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet

  have tE : ∀ a : Fin r, tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
    intro a; simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]
  have tZ : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
    simp [tupH, F0, Fin.append_left, Fin.snoc_last]
  have tF : ∀ a : Fin r, tupH P (Fin.natAdd (r + 1) a) = P.f a := by
    intro a; simp [tupH, Fin.append_right]
  have hsum : ∀ i, (gramE σ J (tupH P) *ᵥ v) i =
      (∑ b : Fin r, hE σ J (tupH P i) (P.e b) * v (Fin.castAdd r (Fin.castSucc b))) +
        hE σ J (tupH P i) P.z * v (Fin.castAdd r (Fin.last r)) +
        ∑ b : Fin r, hE σ J (tupH P i) (P.f b) * v (Fin.natAdd (r + 1) b) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, gramE]
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
    simp only [tE, tZ, tF]
  have hrow : ∀ i, (gramE σ J (tupH P) *ᵥ v) i = 0 := fun i => congrFun hv i
  have vF : ∀ a : Fin r, v (Fin.natAdd (r + 1) a) = 0 := by
    intro a
    have h := hrow (Fin.castAdd r (Fin.castSucc a))
    rw [hsum, tE] at h
    simp only [hee, zero_mul, Finset.sum_const_zero, zero_add, hez, hef, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  have hze : ∀ b, hE σ J P.z (P.e b) = 0 := fun b => by rw [hE_swap σ J hσ hJ, hez, map_zero]
  have hzf : ∀ b, hE σ J P.z (P.f b) = 0 := fun b => by rw [hE_swap σ J hσ hJ, hfz, map_zero]
  have hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if b = a then 1 else 0 := fun a b => by
    rw [hE_swap σ J hσ hJ, hef]; split_ifs <;> simp
  have hfz' : ∀ a, hE σ J (P.f a) P.z = 0 := hfz
  have vZ : v (Fin.castAdd r (Fin.last r)) = 0 := by
    have h := hrow (Fin.castAdd r (Fin.last r))
    rw [hsum, tZ] at h
    simp only [hze, hzf, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at h
    have hne : hE σ J P.z P.z ≠ 0 := by
      rw [hzz]
      intro h0
      exact hT (neg_eq_zero.1 ((algebraMap F E).injective (by rw [h0, map_zero])))
    exact (mul_eq_zero.1 h).resolve_left hne
  have vE : ∀ a : Fin r, v (Fin.castAdd r (Fin.castSucc a)) = 0 := by
    intro a
    have h := hrow (Fin.natAdd (r + 1) a)
    rw [hsum, tF] at h
    simp only [hfe, hfz', hff, zero_mul, Finset.sum_const_zero, add_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  apply hv0
  funext i
  refine Fin.addCases (fun j => ?_) (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun a => ?_) j
    · exact vZ
    · exact vE a
  · exact vF a

end Gram

end Formalism.L2.SG.Pf.Rescale

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

namespace Formalism.L2.SG.Pf.Rescale

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hform_crdX (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hE_crdX (X : HidaSetting D) (v w : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) = X.ιE.symm ((VS D).hT v w) := by
  show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J _ _ = _
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frame_stdX (X : HidaSetting D) (u : D.what₂.Word) :
    (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_, ?_⟩
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.eX b)) = 0
    rw [hE_crdX, X.ee, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.fY b)) = 0
    rw [hE_crdX, X.ff, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b)) = _
    rw [hE_crdX, X.ef]
    split_ifs <;> simp
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0
    rw [hE_crdX, (X.zu_orth u a).1, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0
    rw [hE_crdX, (X.zu_orth u a).2, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.zu u)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = _
    rw [hE_crdX, X.zu_norm]
    simp
  · exact Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero


end Formalism.L2.SG.Pf.Rescale
end
end

