module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0068
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0035

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AbsNormSmallFinite
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem absNorm_small_finite (D : Formalism.BasicNotions.D7) :
    {p : PlF D | (Ideal.absNorm p.asIdeal : ℝ) < 3}.Finite := by
  have h : {I : Ideal (𝓞 D.host.F) | Ideal.absNorm I < 3}.Finite := by
    have : {I : Ideal (𝓞 D.host.F) | Ideal.absNorm I < 3} =
        ⋃ n ∈ Finset.range 3, {I : Ideal (𝓞 D.host.F) | Ideal.absNorm I = n} := by
      ext I; simp [Finset.mem_range]
    rw [this]
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => Ideal.finite_setOf_absNorm_eq n)
  refine (h.preimage (fun p _ q _ hpq => IsDedekindDomain.HeightOneSpectrum.ext hpq)).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  exact_mod_cast hp

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CMeasSbox
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Phi

variable {ι : Type} [Fintype ι] {r k : ℕ}

def Φc (x : ∀ p : CBlk r, CSpc ι k p) (i : ι × LsNc5.CIdx r k) : ℝ :=
  match i with
  | (v, Sum.inl (Sum.inl (p, t))) => LsNc5.reim ((x (Sum.inl (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inl (Sum.inr (b, t))) => LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.last k)) t
  | (v, Sum.inr (Sum.inl (b, j, t))) =>
      LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.castSucc j)) t
  | (v, Sum.inr (Sum.inr (Sum.inl (p, t)))) => LsNc5.reim ((x (Sum.inr (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inr (Sum.inr (Sum.inr a))) => (x (Sum.inr (Sum.inr a)) : ι → ℝ) v

theorem measurable_Φc : Measurable (Φc (ι := ι) (r := r) (k := k)) := by
  refine Measurable.of_eval fun i => ?_
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inl p) : CBlk r)))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.last k)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.castSucc j)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inr (Sum.inl p) : CBlk r)))
  · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inr (Sum.inr a) : CBlk r))

def Ψc (y : ι × LsNc5.CIdx r k → ℝ) : ∀ p : CBlk r, CSpc ι k p
  | Sum.inl (Sum.inl p) => fun v => (⟨y (v, Sum.inl (Sum.inl (p, false))), y (v, Sum.inl (Sum.inl (p, true)))⟩ : ℂ)
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ)
  | Sum.inr (Sum.inl p) => fun v =>
      (⟨y (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), y (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩ : ℂ)
  | Sum.inr (Sum.inr a) => fun v => y (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_Ψc (y : ι × LsNc5.CIdx r k → ℝ) : Φc (Ψc y) = y := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · cases t <;> rfl
  · have hj : ¬ (Fin.last k).val < k := by simp
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · have hj : (Fin.castSucc j).val < k := j.isLt
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · cases t <;> rfl
  · rfl

theorem Ψc_Φc (x : ∀ p : CBlk r, CSpc ι k p) : Ψc (Φc x) = x := by
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v; apply Complex.ext <;> rfl
  · funext v j
    show (if h : j.val < k then _ else _) = _
    split_ifs with h
    · apply Complex.ext
      · show LsNc5.reim (_ : ℂ) false = _
        simp only [LsNc5.reim, Bool.false_eq_true, if_false]
        congr 2
      · show LsNc5.reim (_ : ℂ) true = _
        simp only [LsNc5.reim, if_true]
        congr 2
    · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hj
      apply Complex.ext <;> rfl
  · funext v; apply Complex.ext <;> rfl
  · rfl

theorem measurable_Ψc : Measurable (Ψc (ι := ι) (r := r) (k := k)) := by
  have hC : ∀ f g : (ι × LsNc5.CIdx r k → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun y => (⟨f y, g y⟩ : ℂ) := fun f g hf hg =>
    Complex.measurableEquivRealProd.symm.measurable.comp (hf.prodMk hg)
  refine Measurable.of_eval fun p => ?_
  rcases p with ((p | b) | (p | a))
  · exact Measurable.of_eval fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · refine Measurable.of_eval fun v => Measurable.of_eval fun j => ?_
    show Measurable fun y : ι × LsNc5.CIdx r k → ℝ => (if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ))
    split_ifs with h
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact Measurable.of_eval fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact Measurable.of_eval fun v => measurable_pi_apply _

end Phi

section Box

variable {ι : Type} [Fintype ι] {r k : ℕ}

def cRow (b : Fin r) (j : Fin (k + 1)) (t : Bool) : LsNc5.CIdx r k :=
  if h : j.val < k then Sum.inr (Sum.inl (b, ⟨j.val, h⟩, t)) else Sum.inl (Sum.inr (b, t))

def Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) : ∀ p : CBlk r, Set (CSpc ι k p)
  | Sum.inl (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inl (Sum.inl (p, false))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inl (Sum.inl (p, true)))}
  | Sum.inl (Sum.inr b) => Set.univ.pi fun v => Set.univ.pi fun j : Fin (k + 1) =>
      {z : ℂ | LsNc5.reim z false ∈ s (v, cRow b j false) ∧ LsNc5.reim z true ∈ s (v, cRow b j true)}
  | Sum.inr (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, false)))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, true))))}
  | Sum.inr (Sum.inr a) => Set.univ.pi fun v => s (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_row (x : ∀ p : CBlk r, CSpc ι k p) (v : ι) (b : Fin r) (j : Fin (k + 1)) (t : Bool) :
    Φc x (v, cRow b j t) = LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j) t := by
  unfold cRow
  split_ifs with h
  · rfl
  · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    subst hj; rfl

theorem pre_box (s : ι × LsNc5.CIdx r k → Set ℝ) :
    Φc ⁻¹' Set.univ.pi s = Set.univ.pi (Sbox (ι := ι) (k := k) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h p
    rcases p with ((p | b) | (p | a))
    · intro v _; exact ⟨h (v, Sum.inl (Sum.inl (p, false))), h (v, Sum.inl (Sum.inl (p, true)))⟩
    · intro v _ j _
      refine ⟨?_, ?_⟩
      · have := h (v, cRow b j false); rwa [Φc_row] at this
      · have := h (v, cRow b j true); rwa [Φc_row] at this
    · intro v _; exact ⟨h (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), h (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩
    · intro v _; exact h (v, Sum.inr (Sum.inr (Sum.inr a)))
  · intro h i
    rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
    · have := h (Sum.inl (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.last k) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun t => by simp [cRow]
      have h2 := Φc_row x v b (Fin.last k) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.castSucc j) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) := fun t => by
        simp [cRow]
      have h2 := Φc_row x v b (Fin.castSucc j) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inr (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · exact h (Sum.inr (Sum.inr a)) v (Set.mem_univ v)

theorem cMeas_Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (p : CBlk r) :
    cMeas ι k p (Sbox s p) =
      match p with
      | Sum.inl (Sum.inl p) => ∏ v, volume (s (v, Sum.inl (Sum.inl (p, false)))) * volume (s (v, Sum.inl (Sum.inl (p, true))))
      | Sum.inl (Sum.inr b) => ∏ v, ∏ j : Fin (k + 1), volume (s (v, cRow b j false)) * volume (s (v, cRow b j true))
      | Sum.inr (Sum.inl p) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, false))))) *
          volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, true)))))
      | Sum.inr (Sum.inr a) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inr a)))) := by
  rcases p with ((p | b) | (p | a))
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → Fin (k + 1) → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun j _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℝ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]

theorem map_Φc : (Measure.pi (cMeas ι k (r := r))).map Φc = volume := by
  refine (Measure.pi_eq (μ := fun _ : ι × LsNc5.CIdx r k => (volume : Measure ℝ))
    (μ' := (Measure.pi (cMeas ι k (r := r))).map Φc) fun s hs => ?_).symm
  rw [Measure.map_apply measurable_Φc (MeasurableSet.univ_pi hs), pre_box, Measure.pi_pi]
  simp_rw [cMeas_Sbox s hs]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool, Fin.prod_univ_castSucc,
    Finset.prod_mul_distrib]
  have e1 : ∀ (b : Fin r) (t : Bool), cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun b t => by
    simp [cRow]
  have e2 : ∀ (b : Fin r) (j : Fin k) (t : Bool), cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) :=
    fun b j t => by simp [cRow]
  simp only [e1, e2]
  have swap : ∀ {β : Type} [Fintype β] (f : ι → β → ℝ≥0∞), ∏ v, ∏ b, f v b = ∏ b, ∏ v, f v b :=
    fun f => Finset.prod_comm
  simp only [swap]
  ring

end Box

theorem kap_eq_Φc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) :
    LsNc5.kap X u s = Φc (blk X u s) := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · rfl
  · show LsNc5.reim (LsNc5.yVec X u v s b) t = LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.last D.R.k)) t
    simp [blk]
  · show LsNc5.reim (LsNc5.phiMat X u v s b j) t =
      LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.castSucc j)) t
    simp [blk]
  · rfl
  · rfl

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowBlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS),
    Countable (cLat X u (Sum.inl (Sum.inr b))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inr b)))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualFormInverse
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions Formalism.L2.SG.Pf.GluedFormOrthogonality
  Formalism.L2.SG.Pf.DualFormInverse

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  have hTop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => form_orth_U hs (hbU i) (hwW j)
  have hq0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  have hqS : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := (isLocUnif (K := K) hK hF h𝔭 hu).mem
    rwa [jι_eq'] at this
  have hA0 : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)
  have hC0 : ∀ j, algebraMap F K (c j) ≠ 0 := fun j => (map_ne_zero _).2 (hwn j).2
  have hGr : ∀ j, glueFam K 𝔭 b a π w τ (Sum.inr j) = w j := fun j => rfl
  have hGl : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hGl0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) =
      algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) := by
    intro i
    simp only [map_add (f := _), LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring

  have hgg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ ^ 2 *
          (algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i))) := by
    intro i hi
    rw [hGl i hi, form_smul_smul, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), key_ii]
    ring
  have hgw : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_left, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), map_add (f := _),
      LinearMap.add_apply, hbw, hwn1, zero_add]
  have hwg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_right, inv_pow (algebraMap F K (π : F)), map_add (f := _), hwb, hwn1, zero_add]
  have hww : ∀ j, h (glueFam K 𝔭 b a π w τ (Sum.inr j)) (glueFam K 𝔭 b a π w τ (Sum.inr j)) =
      algebraMap F K (c j) := fun j => by rw [hGr, hwn1]
  have hdiag0 : ∀ i, vF 𝔭 (a i) = 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        algebraMap F K ((a i : 𝓞 F) : F) := fun i hi => by rw [hGl0 i hi, hbn]

  have hoff0 : ∀ i, vF 𝔭 (a i) = 0 → ∀ s, s ≠ Sum.inl i →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 := by
    intro i hi s hs'
    rcases s with i' | j
    · exact glue_inl_inl hs hbU hbo hwW hwo hτ (fun e => hs' (congrArg Sum.inl e))
    · exact hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun h1 => absurd hi h1))
  have hoff : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ s, s ≠ Sum.inl i → s ≠ Sum.inr (τ i) →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 ∧
        h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) = 0 := by
    intro i hi s h1 h2
    rcases s with i' | j
    · have hii : i' ≠ i := fun e => h1 (congrArg Sum.inl e)
      exact ⟨glue_inl_inl hs hbU hbo hwW hwo hτ hii,
        glue_inl_w hbU hwW hwo (fun h3 e => hii (hτ i' i h3 hi e))⟩
    · have hj : j ≠ τ i := fun e => h2 (congrArg Sum.inr e)
      exact ⟨hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun _ e => hj e.symm)), hwo j (τ i) hj⟩
  have hoffw : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → ∀ s, s ≠ Sum.inr j →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr j)) = 0 := by
    intro j hj s hs'
    rcases s with i | j'
    · exact glue_inl_w hbU hwW hwo (fun h3 => hj i h3)
    · exact hwo j' j (fun e => hs' (congrArg Sum.inr e))

  have hpair : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ X Y : K, X ∈ SP K 𝔭 → Y ∈ SP K 𝔭 →
      ∃ κ : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → K, (∀ t, κ t ∈ SP K 𝔭) ∧
        ∀ s, ∑ t, κ t * h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t) =
          if s = Sum.inl i then X else if s = Sum.inr (τ i) then Y else 0 := by
    intro i hi X Y hX hY
    obtain ⟨r, hr, hre⟩ := (mem_noncompactPart_iff hu _ _).1 (hcong i hi)
    rw [jι_eq', map_add (f := _)] at hre
    have hre' : algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i)) ^ 2 * r := by
      rw [hre]; ring
    have hc := unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    obtain ⟨e1, e2⟩ := pair_solve (X := X) (Y := Y) (pow_ne_zero (vF 𝔭 (a i)) hq0) (hA0 i) hc.1 hre'
    obtain ⟨m1, m2⟩ := pair_coeffs_mem (𝔭 := 𝔭) (X := X) (Y := Y) ((SP K 𝔭).pow_mem hqS _)
      (unit_part hK hF h𝔭 hu (ha0 i)) hc.2 hr hX hY
    obtain ⟨κ, hκS, hκ⟩ := exists_two (Sum.inl_ne_inr (a := i) (b := τ i)) m1 m2
      (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
    refine ⟨κ, hκS, fun s => ?_⟩
    rw [hκ s]
    by_cases h1 : s = Sum.inl i
    · subst h1
      rw [if_pos rfl, hgg i hi, hgw i hi]
      linear_combination e1
    · by_cases h2 : s = Sum.inr (τ i)
      · subst h2
        rw [if_neg h1, if_pos rfl, hwg i hi, hww]
        linear_combination e2
      · rw [if_neg h1, if_neg h2, (hoff i hi s h1 h2).1, (hoff i hi s h1 h2).2]
        ring
  refine dualF_le_of_inv hs hnd _ hTop ?_
  intro u
  rcases u with i | j
  · by_cases hi : vF 𝔭 (a i) = 0
    · have hAi : (algebraMap F K ((a i : 𝓞 F) : F))⁻¹ ∈ SP K 𝔭 := by
        have := unit_part hK hF h𝔭 hu (ha0 i)
        rwa [hi, pow_zero, mul_one] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inl i) hAi
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i
      · subst h1
        rw [if_pos rfl, hdiag0 i hi, inv_mul_cancel₀ (hA0 i)]
      · rw [if_neg h1, hoff0 i hi s h1, mul_zero]
    · obtain ⟨κ, hκS, hκ⟩ := hpair i hi 1 0 (SP K 𝔭).one_mem (SP K 𝔭).zero_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
  · by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨κ, hκS, hκ⟩ := hpair i hi 0 1 (SP K 𝔭).zero_mem (SP K 𝔭).one_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
    · simp only [not_exists, not_and] at hj
      have hCj : (algebraMap F K (c j))⁻¹ ∈ SP K 𝔭 := by
        have := (hunit j hj).2
        rwa [map_inv₀] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inr j) hCj
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inr j
      · subst h1
        rw [if_pos rfl, hww, inv_mul_cancel₀ (hC0 j)]
      · rw [if_neg h1, hoffw j hj s h1, mul_zero]

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameRow : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ L : (LsNc5.CIdx D.R.rS D.R.k → ℝ) →ₗ[ℝ] (LsNc5.CIdx D.R.rS D.R.k → ℝ),
      (∀ s : X.B.I.Ginf, (fun i => LsNc5.kapV X w v s i) = L (fun i => LsNc5.kapV X u v s i)) ∧
      |LinearMap.det L| = (Tw w / Tw u) ^ D.R.rS

end Formalism.L2.SG.Pf.NcReal.JX
end
end

