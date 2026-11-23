module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalVectorMemFixedRight

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.BlkOneMem
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private def eIdx (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

private def bm (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
  Matrix.reindex (eIdx h) (eIdx h) (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)

private theorem bm_isUnit (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : IsUnit (bm h w m X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  unfold bm
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)

private theorem blk_val (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : (GlobalTheory.BCT.blk h w m X).val = bm h w m X := by
  show (if hM : IsUnit (bm h w m X) then hM.unit else 1).val = _
  rw [dite_eq_left (bm_isUnit h w m X)]
  rfl

private theorem blk_add (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GlobalTheory.BCT.blk h w m (X + Y) = GlobalTheory.BCT.blk h w m X * GlobalTheory.BCT.blk h w 1 Y := by
  apply Units.ext
  rw [Units.val_mul, blk_val, blk_val, blk_val]
  unfold bm
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_add, add_comm]

private theorem blk_one_mem (h : a + b = n) (w : Pl E) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (hY : ∀ i j, Valued.v (Y i j) ≤ 1) : GlobalTheory.BCT.blk h w 1 Y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let Y' : Matrix (Fin a) (Fin b) (Ov E w) := fun i j => ⟨Y i j, hY i j⟩
  let N : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.reindex (eIdx h) (eIdx h) (Matrix.fromBlocks 1 Y' 0 1)
  have hN : IsUnit N := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp [N, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  refine ⟨hN.unit, Units.ext ?_⟩
  rw [blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (eIdx h).surjective i
  obtain ⟨j, rfl⟩ := (eIdx h).surjective j
  change (Ov E w).subtype (N _ _) = bm h w 1 Y _ _
  rcases i with i | i <;> rcases j with j | j <;> simp [N, bm, Y', Matrix.one_apply]
  · change (((1 : Matrix (Fin a) (Fin a) (Ov E w)) i j : Ov E w) : w.adicCompletion E) = _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hij]
      simp [hij]
  · rfl
  · rfl
  · change (((1 : Matrix (Fin b) (Fin b) (Ov E w)) i j : Ov E w) : w.adicCompletion E) = _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hij]
      simp [hij]

private theorem intMat_le (w : Pl E) (Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))
    (hY : Y ∈ intMat a b w) : ∀ i j, Valued.v (Multiplicative.toAdd Y i j) ≤ 1 := by
  unfold intMat at hY
  induction hY using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro i j; simp
  | mul x y _ _ hx hy =>
    intro i j
    simp only [toAdd_mul, Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx i j) (hy i j))
  | inv x _ hx =>
    intro i j
    simpa using hx i j

private theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (Subsingleton.elim _ _) hx)]
  simp

private theorem supp_fin (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (hf : HasCompactSupport f)
    (m : GLw a w × GLw b w) :
    (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
      f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out))).Finite := by
  let ψ : GLw n w → Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun g =>
    (m.1⁻¹).val * Matrix.of fun i j => g.val (eIdx h (Sum.inl i)) (eIdx h (Sum.inr j))
  have hψ : Continuous ψ := by
    refine continuous_const.matrix_mul ?_
    refine continuous_matrix fun i j => ?_
    exact Units.continuous_val.matrix_elem _ _
  have hψb : ∀ X, ψ (GlobalTheory.BCT.blk h w m X) = X := by
    intro X
    have hb : (Matrix.of fun i j => (GlobalTheory.BCT.blk h w m X).val (eIdx h (Sum.inl i)) (eIdx h (Sum.inr j))) =
        m.1.val * X := by
      ext i j
      rw [blk_val]
      simp [bm]
    simp only [ψ]
    rw [hb, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hC : IsCompact (ψ '' tsupport f) := hf.isCompact.image hψ
  have hU : ∀ X ∈ ψ '' tsupport f, {Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) |
      ∀ i j, Valued.v ((Y - X) i j) ≤ 1} ∈ 𝓝 X := by
    intro X _
    have h0 : {x : w.adicCompletion E | Valued.v x ≤ 1} ∈ 𝓝 (0 : w.adicCompletion E) :=
      (Valued.mem_nhds_zero).2 ⟨1, fun x hx => show Valued.v x ≤ 1 from le_of_lt (by simpa using hx)⟩
    have : ∀ i j, ∀ᶠ Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) in 𝓝 X, Valued.v ((Y - X) i j) ≤ 1 := by
      intro i j
      have hc : Continuous fun Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (Y - X) i j :=
        (continuous_id.sub continuous_const).matrix_elem i j
      have ht : Tendsto (fun Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (Y - X) i j) (𝓝 X) (𝓝 0) := by
        have := hc.tendsto X
        simpa using this
      exact ht h0
    exact eventually_all.2 fun i => eventually_all.2 fun j => this i j
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image fun X => (QuotientGroup.mk (Multiplicative.ofAdd X) :
    Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w)).subset ?_
  intro q hq
  have hmem : Multiplicative.toAdd q.out ∈ ψ '' tsupport f :=
    ⟨_, subset_tsupport f hq, hψb _⟩
  obtain ⟨X, hX, hXY⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨X, hX, ?_⟩
  rw [← QuotientGroup.out_eq' q]
  refine QuotientGroup.eq.2 (Subgroup.subset_closure ?_)
  intro i j
  have := hXY i j
  simpa [sub_eq_neg_add] using this

end SlopeTestRemainingChoices

theorem ctSph : CtSph := by
  intro E _ _ _ w n a b h f hf m
  refine ⟨?_, supp_fin h w f hf.1 m⟩
  have hinv := hf.2
  have havg : ∀ y : GLw n w, (avg fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * y * k)) = f y := by
    intro y
    have : (fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * y * k)) = fun _ => f y := by
      funext k
      rw [(hinv k k.2 _).2, (hinv _ (inv_mem k.2) y).1]
    rw [this, avg_const]
  unfold ct
  simp only [havg]
  rw [hintSph _ (intMat a b w) (fun X => f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd X)))]
  intro k hk x
  show f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd x + Multiplicative.toAdd k)) = _
  rw [blk_add, (hinv _ (blk_one_mem h w _ (intMat_le w k hk)) _).2]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.BCT
open scoped Pointwise

private theorem cv_eq_sum {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ)
    (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x) (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x) (y : G) :
    cv K f g y = ∑ᶠ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) := by
  refine hintSph G K (fun z => f z * g (z⁻¹ * y)) ?_
  intro k hk x
  have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
  simp only [e, hf k hk x, hg k⁻¹ (K.inv_mem hk)]

theorem cvHecke : CvHecke := by
  intro G _ _ _ K _ _ f g hf hg
  have hfl : ∀ k ∈ K, ∀ x, f (k * x) = f x := fun k hk x => (hf.2 k hk x).1
  have hfr : ∀ k ∈ K, ∀ x, f (x * k) = f x := fun k hk x => (hf.2 k hk x).2
  have hgl : ∀ k ∈ K, ∀ x, g (k * x) = g x := fun k hk x => (hg.2 k hk x).1
  have hgr : ∀ k ∈ K, ∀ x, g (x * k) = g x := fun k hk x => (hg.2 k hk x).2
  have hcv := cv_eq_sum K f g hfr hgl
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · have hS : IsCompact (tsupport f * tsupport g) := hf.1.isCompact.mul hg.1.isCompact
    refine hS.closure_of_subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyS
    apply hy
    rw [hcv]
    have h0 : ∀ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) = 0 := by
      intro q
      by_contra h
      have h1 : f q.out ≠ 0 := left_ne_zero_of_mul h
      have h2 : g (q.out⁻¹ * y) ≠ 0 := right_ne_zero_of_mul h
      exact hyS ⟨q.out, subset_tsupport _ h1, q.out⁻¹ * y, subset_tsupport _ h2, by group⟩
    simp [h0]
  · rw [hcv, hcv]
    have hF : ∀ z : G, f (z : G ⧸ K).out * g ((z : G ⧸ K).out⁻¹ * x) = f z * g (z⁻¹ * x) := by
      intro z
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K z
      have e : (z * (h : G))⁻¹ * x = (h : G)⁻¹ * (z⁻¹ * x) := by group
      rw [hh, hfr _ h.2, e, hgl _ (K.inv_mem h.2)]
    have hterm : ∀ q : G ⧸ K, f q.out * g (q.out⁻¹ * (k * x)) =
        (fun p : G ⧸ K => f p.out * g (p.out⁻¹ * x)) (MulAction.toPerm (k⁻¹ : G) q) := by
      intro q
      have e1 : MulAction.toPerm (k⁻¹ : G) q = ((k⁻¹ * q.out : G) : G ⧸ K) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have e2 : (k⁻¹ * q.out)⁻¹ * x = q.out⁻¹ * (k * x) := by group
      simp only [e1]
      rw [hF, hfl _ (K.inv_mem hk), e2]
    rw [finsum_congr hterm]
    exact finsum_comp_equiv (f := fun p : G ⧸ K => f p.out * g (p.out⁻¹ * x))
      (MulAction.toPerm (k⁻¹ : G) : Equiv.Perm (G ⧸ K))
  · rw [hcv, hcv]
    refine finsum_congr fun q => ?_
    rw [← mul_assoc, hgr k hk]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintMulEqConv
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.BCT GlobalTheory.LFun
open Formalism.UG (Hecke IsCommensurated Tj Ov qV IsUnifV dosetInd)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G : Type} [Group G]

private theorem hint_mul_eq_conv (K : Subgroup G) {f g : G → ℂ} (hf : f ∈ Hecke ℂ K) (hg : g ∈ Hecke ℂ K) :
    (fun y => hint K fun z => f z * g (z⁻¹ * y)) = Formalism.UG.conv K f g := by
  funext y
  refine (hintSph G K _ fun k hk x => ?_).trans rfl
  have h1 : f (x * k) = f x := by simpa using hf.1 1 ⟨k, hk⟩ x
  have h2 : g (k⁻¹ * (x⁻¹ * y)) = g (x⁻¹ * y) := by
    simpa using hg.1 ⟨k⁻¹, K.inv_mem hk⟩ 1 (x⁻¹ * y)
  have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
  show f (x * k) * g ((x * k)⁻¹ * y) = f x * g (x⁻¹ * y)
  rw [h1, e, h2]

private theorem ind_eq_dosetInd (K : Subgroup G) : (K : Set G).indicator (1 : G → ℂ) = dosetInd ℂ K 1 := by
  funext x
  by_cases hx : x ∈ K
  · rw [Formalism.UG.P.dosetInd_of_mem ℂ K 1 x ((Formalism.UG.P.mem_dc_one K x).2 hx)]
    simp [Set.indicator_apply, hx]
  · rw [Formalism.UG.P.dosetInd_of_not_mem ℂ K 1 x fun h => hx ((Formalism.UG.P.mem_dc_one K x).1 h)]
    simp [Set.indicator_apply, hx]

private theorem fn_mem {ι : Type} (K : Subgroup G) (hK : IsCommensurated K) (g : ι → G → ℂ)
    (hg : ∀ i, g i ∈ Hecke ℂ K) (e : Ex ι) : e.fn K g ∈ Hecke ℂ K := by
  induction e with
  | one =>
    show (K : Set G).indicator 1 ∈ Hecke ℂ K
    rw [ind_eq_dosetInd]
    exact Formalism.UG.Final.DosetIndMem G K ℂ 1
  | gen i => exact hg i
  | smul c a ih => exact (Hecke ℂ K).smul_mem c ih
  | add a b iha ihb => exact (Hecke ℂ K).add_mem iha ihb
  | mul a b iha ihb =>
    show (fun y => hint K fun z => a.fn K g z * b.fn K g (z⁻¹ * y)) ∈ Hecke ℂ K
    rw [hint_mul_eq_conv K iha ihb]
    exact Formalism.UG.Final.HeckeConvMem G K ℂ hK _ iha _ ihb

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem heckeVec_ind (K : Subgroup G) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K ((K : Set G).indicator 1) x = x := by
  rw [ind_eq_dosetInd, heckeVec_dosetInd hx (a := 1) (R := {1})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact (Formalism.UG.P.mem_dc_one K 1).2 K.one_mem
  · intro g hg
    refine ⟨1, ⟨Finset.mem_singleton_self _, by simpa using (Formalism.UG.P.mem_dc_one K g).1 hg⟩, ?_⟩
    exact fun γ hγ => Finset.mem_singleton.1 hγ.1

private theorem heckeVec_fn {ι : Type} (K : Subgroup G) (hK : IsCommensurated K) (g : ι → G → ℂ)
    (hg : ∀ i, g i ∈ Hecke ℂ K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K) (c : ι → ℂ)
    (hc : ∀ i, heckeVec ρ K (g i) x = c i • x) (e : Ex ι) :
    heckeVec ρ K (e.fn K g) x = e.ev c • x := by
  induction e with
  | one =>
    show heckeVec ρ K ((K : Set G).indicator 1) x = (1 : ℂ) • x
    rw [heckeVec_ind K ρ hx, one_smul]
  | gen i => exact hc i
  | smul z a ih =>
    show heckeVec ρ K (z • a.fn K g) x = (z * a.ev c) • x
    rw [GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_smul, ih, mul_smul]
  | add a b iha ihb =>
    show heckeVec ρ K (a.fn K g + b.fn K g) x = (a.ev c + b.ev c) • x
    rw [GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_add hK (fn_mem K hK g hg a) (fn_mem K hK g hg b), iha, ihb, add_smul]
  | mul a b iha ihb =>
    show heckeVec ρ K (fun y => hint K fun z => a.fn K g z * b.fn K g (z⁻¹ * y)) x = (a.ev c * b.ev c) • x
    rw [hint_mul_eq_conv K (fn_mem K hK g hg a) (fn_mem K hK g hg b),
      GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_conv hK (fn_mem K hK g hg a) (fn_mem K hK g hg b) ρ hx, ihb,
      GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_smul_vec, iha, smul_smul, mul_comm]

private theorem isHecke_of_mem [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hc : IsCompact (K : Set G)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : IsHecke K f := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · have hcomp : IsCompact (⋃ s ∈ (S : Set G), (fun p : G × G => p.1 * s * p.2) '' ((K : Set G) ×ˢ (K : Set G))) :=
      S.finite_toSet.isCompact_biUnion fun s _ => (hc.prod hc).image (by fun_prop)
    refine HasCompactSupport.intro hcomp fun x hx => ?_
    by_contra h0
    obtain ⟨s, hs, a, b, e⟩ := hS x h0
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨(a, b), ⟨a.2, b.2⟩, e.symm⟩)
  · simpa using hb ⟨k, hk⟩ 1 x
  · simpa using hb 1 ⟨k, hk⟩ x

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exAct :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExAct := by
  intro E _ _ _ n w e
  have hu : IsUnifV E w (unif w) := Classical.epsilon_spec (exists_isUnifV w)
  have hK : IsCommensurated (KGL w (n := n)) := Formalism.UG.Final.GLintComm E w n
  have hT : ∀ j : Fin (n + 1), Tj ℂ n (Ov E w) (unif w) j ∈ Formalism.UG.Hecke ℂ (KGL w (n := n)) :=
    fun j => Tj_mem_hecke hu j
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hmem : fn1 n w e ∈ Formalism.UG.Hecke ℂ (KGL w (n := n)) := fn_mem _ hK _ hT e
  have hH : IsHecke (KGL w (n := n)) (fn1 n w e) := isHecke_of_mem hc hmem
  refine ⟨hH, fun V _ _ ρ x B hx => ?_⟩
  have hfix : x ∈ fixed ρ (KGL w (n := n)) := hx.2.1
  rw [(cvOp _ _ ho hc V ρ _ _ hH hH x hfix).2.2]
  exact heckeVec_fn _ hK _ hT ρ hfix _ (fun j => hx.2.2.2 (unif w) hu j (Nat.lt_succ_iff.1 j.2)) e
end
end

