module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.DetDiagJ
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem prod_lt {R : Type} [CommMonoid R] (p : R) (j : ℕ) :
    ∀ n, ∏ k ∈ Finset.range n, (if k < j then p else 1) = p ^ (min n j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : n < j
    · rw [if_pos h, min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h), pow_succ]
    · rw [if_neg h, mul_one, min_eq_right (not_lt.1 h), min_eq_right (by omega)]

private theorem det_diagJ {L : Type} [Field L] (n : ℕ) (p : L) {i : ℕ} (hi : i ≤ n) : (diagJ n p i).det = p ^ i := by
  rw [diagJ, det_diagonal, Fin.prod_univ_eq_prod_range (fun k => if k < i then p else 1) n, prod_lt, min_eq_right hi]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem v_le (w : Pl E) (n : ℕ) : ∀ k ∈ GLint (Fin n) (Ov E w),
    Valued.v ((GeneralLinearGroup.det k : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
  rintro _ ⟨x, rfl⟩
  exact (congrArg (fun y => Valued.v y ≤ 1) (det_map (Ov E w).subtype x)).mpr (GeneralLinearGroup.det x).1.2

private theorem v_eq (w : Pl E) (n : ℕ) {k : GLw n w} (hk : k ∈ GLint (Fin n) (Ov E w)) :
    Valued.v ((GeneralLinearGroup.det k : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h3 := v_le w n _ (inv_mem hk)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 (Units.ne_zero _)))] at h3
  exact le_antisymm (v_le w n k hk) h3

private theorem unifV (w : Pl E) : IsUnifV E w (unif w) :=
  Classical.epsilon_spec (exists_isUnifV w)

private theorem unif_ne (w : Pl E) : unif w ≠ 0 := by
  intro e
  have h := unifV w
  rw [IsUnifV, e, map_zero] at h
  exact WithZero.coe_ne_zero h.symm

private theorem loc_unif (w : Pl E) (μ : HChar E) (hμ : μ.UnrAt w) :
    μ.loc w (Units.mk0 (unif w) (unif_ne w)) = μ.val w := by
  have h : μ.loc w (Units.mk0 (unif w) (unif_ne w) * (atFin w (Formalism.L2.Host.unif w))⁻¹) = 1 := by
    refine hμ _ ?_
    have h1 : Valued.v ((atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-1 : ℤ) :=
      Formalism.L2.Host.unif_spec w
    have h2 : Valued.v (unif w) = WithZero.exp (-1 : ℤ) := unifV w
    rw [IsUnitAt, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, Units.val_mk0, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

private theorem loc_det (w : Pl E) (μ : HChar E) (hμ : μ.UnrAt w) {n i : ℕ} (hi : i ≤ n) (g : GLw n w)
    (h : Tj ℂ n (Ov E w) (unif w) i g ≠ 0) : μ.loc w (GeneralLinearGroup.det g) = μ.val w ^ i := by
  have hm : g ∈ {g : GLw n w | ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n (unif w) i * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E))} := by
    by_contra hn
    exact h (Set.indicator_of_notMem hn _)
  obtain ⟨x, hx, y, hy, e⟩ := hm
  have hd : GeneralLinearGroup.det g = GeneralLinearGroup.det x * Units.mk0 (unif w) (unif_ne w) ^ i * GeneralLinearGroup.det y := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, GeneralLinearGroup.val_det_apply]
    rw [e, det_mul, det_mul, det_diagJ _ _ hi]
  rw [hd, map_mul, map_mul, map_pow, hμ _ (v_eq w n hx), hμ _ (v_eq w n hy), loc_unif w μ hμ, one_mul, mul_one]

private theorem chi_eq (w : Pl E) (μ : HChar E) (hμ : μ.UnrAt w) (a b : ℕ) (m : GLw a w × GLw b w) :
    chi μ a b w m = ((μ.loc w (GeneralLinearGroup.det m.1) ^ b * μ.loc w (GeneralLinearGroup.det m.2) ^ a : ℂˣ) : ℂ) := by
  have h1 : μ.loc w (-1) = 1 := hμ _ (by simp [IsUnitAt])
  rw [chi, map_mul, map_mul, map_pow, map_pow, map_pow, h1, one_pow, one_mul]

theorem muTw : MuTw := by
  intro E _ _ _ w μ hμ a b
  refine ⟨fun m hm => ?_, fun m m' => ?_, fun i j m hi hj h => ?_⟩
  · rw [chi_eq w μ hμ, hμ _ (v_eq w a hm.1), hμ _ (v_eq w b hm.2)]
    simp
  · rw [chi_eq w μ hμ, chi_eq w μ hμ, chi_eq w μ hμ, ← Units.val_mul]
    congr 1
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    exact mul_mul_mul_comm _ _ _ _
  · rw [chi_eq w μ hμ, loc_det w μ hμ hi m.1 (left_ne_zero_of_mul h), loc_det w μ hμ hj m.2 (right_ne_zero_of_mul h)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplit
section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem finprodSplit : FinprodSplit := by
  intro α S Z T F hZ hT hd h1
  classical
  have key : ∏ᶠ w ∈ S, F w = ∏ w ∈ T ∪ Z, F w := by
    apply finprod_mem_eq_prod_of_inter_mulSupport_eq
    ext w
    simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_union, Set.mem_union,
      Finset.mem_coe]
    constructor
    · rintro ⟨hS, hF⟩
      refine ⟨?_, hF⟩
      by_contra hn
      exact hF (h1 w hS (fun h => hn (Or.inr h)) (fun h => hn (Or.inl h)))
    · rintro ⟨hw | hw, hF⟩
      · exact ⟨hT w hw, hF⟩
      · exact ⟨hZ w hw, hF⟩
  rw [key, Finset.prod_union hd, mul_comm]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintConstMul
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private def lin {κ : Type} (c : κ → ℂ) : List κ → Ex κ
  | [] => Ex.smul 0 Ex.one
  | p :: L => Ex.add (Ex.smul (c p) (Ex.gen p)) (lin c L)

private theorem ev_lin {κ : Type} (c x : κ → ℂ) (L : List κ) :
    (lin c L).ev x = (L.map fun p => c p * x p).sum := by
  induction L with
  | nil => simp [lin, Ex.ev]
  | cons p L ih => simp [lin, Ex.ev, ih]

private theorem fn_lin {κ : Type} {G : Type} [Group G] (K : Subgroup G) (g : κ → G → ℂ) (c : κ → ℂ)
    (L : List κ) (y : G) : (lin c L).fn K g y = (L.map fun p => c p * g p y).sum := by
  induction L with
  | nil => simp [lin, Ex.fn]
  | cons p L ih => simp [lin, Ex.fn, ih]

private theorem ev_bind {ι κ : Type} (x : κ → ℂ) (τ : ι → Ex κ) (e : Ex ι) :
    (e.bind τ).ev x = e.ev fun i => (τ i).ev x := by
  induction e with
  | one => rfl
  | gen i => rfl
  | smul c a ih => simp [Ex.bind, Ex.ev, ih]
  | add a b iha ihb => simp [Ex.bind, Ex.ev, iha, ihb]
  | mul a b iha ihb => simp [Ex.bind, Ex.ev, iha, ihb]

private theorem hint_const_mul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    hint K (fun z => c * u z) = c * hint K u := by
  have hs : rStab (fun z => c * u z) = rStab u := by
    ext g
    simp [rStab, hc]
  unfold hint
  rw [hs]
  have := smul_finsum (M := ℂ) c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)
  simp only [smul_eq_mul] at this
  rw [← mul_assoc, mul_comm c, mul_assoc, this]

private def tco (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ) (p : Fin (a + 1) × Fin (b + 1)) : ℂ :=
  cf q a b j p * (c₁ : ℂ) ^ (p.1 : ℕ) * (c₂ : ℂ) ^ (p.2 : ℕ)

private def tEx (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ) : Ex (Fin (a + 1) × Fin (b + 1)) :=
  lin (tco q a b c₁ c₂ j) Finset.univ.toList

private theorem ev_tEx (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ) (x : Fin (a + 1) × Fin (b + 1) → ℂ) :
    (tEx q a b c₁ c₂ j).ev x = ∑ p, tco q a b c₁ c₂ j p * x p := by
  rw [tEx, ev_lin]
  exact Finset.sum_map_toList _ _

private theorem fn_tEx {G : Type} [Group G] (K : Subgroup G) (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ)
    (g : Fin (a + 1) × Fin (b + 1) → G → ℂ) (y : G) :
    (tEx q a b c₁ c₂ j).fn K g y = ∑ p, tco q a b c₁ c₂ j p * g p y := by
  rw [tEx, fn_lin]
  exact Finset.sum_map_toList _ _

theorem rCtEx : RCtEx := by
  intro hEx hLin hUnit hT hMul hSat hMu _ E _ _ _ w hs μ hμ n a b h
  subst h
  have hq : qV E w ≠ 0 := by
    unfold qV
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  obtain ⟨hK, hmul, hval⟩ := hMu E w μ hμ a b
  have hy : ∀ y : GLw (a + b) w, ((toSub (UL (a + b) w) y : UL (a + b) w) : GLw (a + b) w) = y := by
    intro y
    have hm : y ∈ UL (a + b) w := by simp [UL, hs]
    simp [toSub, hm]
  have hne : ∀ m, chi μ a b w m ≠ 0 := fun m => Units.ne_zero _
  let t : Fin (a + b + 1) → Ex (Fin (a + 1) × Fin (b + 1)) :=
    fun j => tEx (qV E w) a b (μ.val w ^ b) (μ.val w ^ a) j
  have key : ∀ e : Ex (Fin (a + b + 1)),
      (fun m => chi μ a b w m * ct rfl w (fn1 (a + b) w e) m) = fn2 a b w (e.bind t) := by
    intro e
    induction e with
    | one =>
      funext m
      show chi μ a b w m * ct rfl w ((KGL w (n := (a + b)) : Set _).indicator 1) m = (K2 a b w : Set _).indicator 1 m
      rw [hUnit E w (a + b) a b rfl]
      by_cases hm : m ∈ K2 a b w
      · simp [Set.indicator, hm, hK m hm]
      · simp [Set.indicator, hm]
    | gen j =>
      funext m
      show chi μ a b w m * ct rfl w (Tj ℂ (a + b) (Ov E w) (unif w) j) m =
        (t j).fn (K2 a b w) (fun p y => Tj ℂ a (Ov E w) (unif w) p.1 y.1 * Tj ℂ b (Ov E w) (unif w) p.2 y.2) m
      rw [hT E w (a + b) a b rfl j m, fn_tEx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h0 : Tj ℂ a (Ov E w) (unif w) p.1 m.1 * Tj ℂ b (Ov E w) (unif w) p.2 m.2 = 0
      · simp [h0]
      · rw [hval p.1 p.2 m (Nat.lt_succ_iff.mp p.1.2) (Nat.lt_succ_iff.mp p.2.2) h0]
        simp only [tco]
        ring
    | smul c e ih =>
      have h1 : fn1 (a + b) w (Ex.smul c e) = fun y => c * fn1 (a + b) w e y := rfl
      have hH := (hEx E (a + b) w e).1
      have h2 := (hLin E w (a + b) a b rfl _ _ c hH hH).2
      show _ = fun y => c * fn2 a b w (e.bind t) y
      rw [h1, h2, ← ih]
      funext m
      ring
    | add e₁ e₂ ih₁ ih₂ =>
      have h1 : fn1 (a + b) w (Ex.add e₁ e₂) = fun y => fn1 (a + b) w e₁ y + fn1 (a + b) w e₂ y := rfl
      have h2 := (hLin E w (a + b) a b rfl _ _ 1 (hEx E (a + b) w e₁).1 (hEx E (a + b) w e₂).1).1
      show _ = fun y => fn2 a b w (e₁.bind t) y + fn2 a b w (e₂.bind t) y
      rw [h1, h2, ← ih₁, ← ih₂]
      funext m
      ring
    | mul e₁ e₂ ih₁ ih₂ =>
      have h1 : fn1 (a + b) w (Ex.mul e₁ e₂) =
          cv (KGL w (n := (a + b))) (fn1 (a + b) w e₁) (fn1 (a + b) w e₂) := rfl
      show _ = fun y => hint (K2 a b w) fun z => fn2 a b w (e₁.bind t) z * fn2 a b w (e₂.bind t) (z⁻¹ * y)
      rw [h1, hMul E w (a + b) a b rfl _ _ (hEx E (a + b) w e₁).1 (hEx E (a + b) w e₂).1, ← ih₁, ← ih₂]
      funext m
      show chi μ a b w m * hint (K2 a b w) (fun z => ct rfl w (fn1 (a + b) w e₁) z *
          ct rfl w (fn1 (a + b) w e₂) (z⁻¹ * m)) = _
      rw [← hint_const_mul _ _ (hne m)]
      congr 1
      funext z
      have hc : chi μ a b w m = chi μ a b w z * chi μ a b w (z⁻¹ * m) := by
        rw [← hmul, mul_inv_cancel_left]
      rw [hc]
      ring
  refine ⟨t, ?_, ?_⟩
  · intro e
    rw [← key e]
    funext m
    have hf : (fun y : GLw (a + b) w => (fun x : UL (a + b) w => fn1 (a + b) w e x.1) (toSub _ y)) =
        fn1 (a + b) w e := by
      funext y
      show fn1 (a + b) w e (toSub (UL (a + b) w) y : UL (a + b) w).1 = _
      rw [hy]
    unfold ctMu
    rw [hf]
    rfl
  · intro e B₁ B₂ h₁ h₂
    unfold ev2 ev1
    rw [ev_bind]
    congr 1
    funext j
    show (tEx (qV E w) a b (μ.val w ^ b) (μ.val w ^ a) j).ev _ = satEig (qV E w) (a + b) (un μ a b w B₁ B₂) j
    rw [ev_tEx]
    have := hSat (qV E w) a b hq B₁ B₂ (μ.val w ^ b) (μ.val w ^ a) h₁ h₂ j
    rw [show un μ a b w B₁ B₂ = B₁.map (· * μ.val w ^ b) + B₂.map (· * μ.val w ^ a) from rfl, this]
    rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph
section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.BCT

theorem hintSph : HintSph := by
  intro G _ K u hu
  have hK : rStab u ⊓ K = K := inf_eq_right.mpr fun k hk x => hu k hk x
  unfold hint
  rw [hK, Subgroup.relIndex_self]
  simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Imports
section
open GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.adm :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted := by
  intro E _ _ _ n w τ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n τ.V τ.ρ τ.smooth τ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hsmall : FiniteDimensional ℂ (fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed τ.ρ U ≤ fixed τ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelU
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem UL_top {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hw : IsSplitAt w) : UL n w = ⊤ := by
  simp [UL, hw]

private theorem val_closed {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hw : IsSplitAt w) : IsClosedEmbedding (Subtype.val : UL n w → GLw n w) := by
  apply IsClosed.isClosedEmbedding_subtypeVal
  rw [UL_top n w hw]
  exact isClosed_univ

private theorem hecke_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hw : IsSplitAt w) (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ) (h : IsHecke K' f) :
    IsHecke (K'.subgroupOf (UL n w)) fun x : UL n w => f x.1 := by
  refine ⟨h.1.comp_isClosedEmbedding (val_closed n w hw), fun k hk x => ?_⟩
  have hk' : (k : GLw n w) ∈ K' := Subgroup.mem_subgroupOf.mp hk
  exact ⟨(h.2 _ hk' _).1, (h.2 _ hk' _).2⟩

theorem levelU : LevelU := by
  intro E _ _ _ n w hw
  refine ⟨?_, fun f hf => ?_⟩
  · rintro f ⟨K', hop, hle, hH⟩
    refine ⟨K'.subgroupOf (UL n w), ?_, ?_, hecke_restrict n w hw K' f hH⟩
    · exact hop.preimage continuous_subtype_val
    · intro x hx
      unfold KL
      exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))
  · exact hecke_restrict n w hw _ f hf

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.TrLevel
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trLevel :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel := by
  intro G _ _ _ K _ hK V _ _ ρ f K₁ K₂ h₂ hle h₁K hf hfd
  have h₁ : IsOpen (K₁ : Set G) := Subgroup.isOpen_mono hle h₂
  haveI : Finite (K₁ ⧸ K₂.subgroupOf K₁) := GlobalTheory.TwTrLevel.finite_quot K K₁ K₂ hK h₁ h₂ h₁K
  have hf₂ : IsHecke K₂ f := ⟨hf.1, fun k hk x => hf.2 k (hle hk) x⟩
  have stable : ∀ (H : Subgroup G), IsOpen (H : Set G) → IsHecke H f →
      ∀ v ∈ fixed ρ H, levOp ρ K H f LinearMap.id v ∈ fixed ρ H := fun H hH hfH v hv =>
    GlobalTheory.TwTrLevel.levOp_mem_fixed ρ (MonoidHom.id G) (fun _ => rfl) LinearMap.id (fun _ => rfl) K H hH
      (fun _ hk => hk) f hfH v hv
  have c₁ := stable K₁ h₁ hf
  have c₂ := stable K₂ h₂ hf₂
  have hW : fixed ρ K₁ ≤ fixed ρ K₂ := fun v hv => by
    rw [GlobalTheory.TwTrLevel.mem_fixed_iff] at hv ⊢
    exact fun k hk => hv k (hle hk)
  haveI : FiniteDimensional ℂ (fixed ρ K₂) := hfd
  haveI : FiniteDimensional ℂ (fixed ρ K₁) := Submodule.finiteDimensional_of_le hW
  let incl : fixed ρ K₁ →ₗ[ℂ] fixed ρ K₂ := Submodule.inclusion hW
  let T : fixed ρ K₂ →ₗ[ℂ] fixed ρ K₁ :=
    ((levOp ρ K K₁ f LinearMap.id).restrict c₁) ∘ₗ
      ((GlobalTheory.TwTrLevel.avgOp ρ K₁ K₂).restrict fun u hu => GlobalTheory.TwTrLevel.avgOp_mem ρ K₁ K₂ u hu)
  have e₂ : (levOp ρ K K₂ f LinearMap.id).restrict c₂ = incl ∘ₗ T := by
    ext v
    simp only [LinearMap.restrict_coe_apply, LinearMap.coe_comp, Function.comp_apply, incl, T,
      Submodule.coe_inclusion]
    exact GlobalTheory.TwTrLevel.levOp_le ρ K K₁ K₂ hle h₁K h₁ h₂ f hf _ v.2
  have e₁ : (levOp ρ K K₁ f LinearMap.id).restrict c₁ = T ∘ₗ incl := by
    ext w
    simp only [LinearMap.restrict_coe_apply, LinearMap.coe_comp, Function.comp_apply, incl, T,
      Submodule.coe_inclusion]
    rw [GlobalTheory.TwTrLevel.avgOp_fix ρ K₁ K₂ _ w.2]
  unfold twTr
  rw [dite_eq_left c₂, dite_eq_left c₁, e₂, e₁, LinearMap.trace_comp_comm']
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.TrSph
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem trSph : TrSph := by
  intro hEx hSL E _ _ _ n w τ B hB e
  have hne : fixed τ.ρ (KGL w (n := n)) ≠ ⊥ := hB.1
  have hfr : Module.finrank ℂ (fixed τ.ρ (KGL w (n := n))) = 1 := (hSL E n w τ hne).1
  have hact : ∀ x ∈ fixed τ.ρ (KGL w (n := n)),
      levOp τ.ρ (KGL w (n := n)) (KGL w (n := n)) (fn1 n w e) LinearMap.id x = ev1 n w e B • x := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · exact (hEx E n w e).2 _ τ.ρ x B (hB.2 x hx h0)
  have hmaps : ∀ v ∈ fixed τ.ρ (KGL w (n := n)),
      levOp τ.ρ (KGL w (n := n)) (KGL w (n := n)) (fn1 n w e) LinearMap.id v ∈ fixed τ.ρ (KGL w (n := n)) := fun v hv => by
    rw [hact v hv]
    exact Submodule.smul_mem _ _ hv
  have hres : (levOp τ.ρ (KGL w (n := n)) (KGL w (n := n)) (fn1 n w e) LinearMap.id).restrict hmaps =
      ev1 n w e B • LinearMap.id := by
    ext ⟨x, hx⟩
    simp [LinearMap.restrict_apply, hact x hx]
  haveI : Module.Finite ℂ (fixed τ.ρ (KGL w (n := n))) := Module.finite_of_finrank_pos (by omega)
  unfold twTr
  rw [dite_eq_left hmaps, hres, map_smul, LinearMap.trace_id, hfr]
  simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnramOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unramOf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.UnramOf := by
  intro E _ _ _ n S π K' hlev w hw hK
  obtain ⟨φ, hφ, h0, hfix⟩ := hlev
  refine ⟨φ, hφ, h0, fun x hx hk => hfix w hw x hx ?_⟩
  have hmem : cLoc w x ∈ UL n w := by
    by_cases hs : IsSplitAt w
    · unfold UL
      rw [if_pos hs]
      trivial
    · exact GlobalTheory.LocInj.cLoc_mem_UL hs x
  refine ⟨⟨cLoc w x, hmem⟩, ?_, rfl⟩
  rw [hK]
  exact Subgroup.mem_subgroupOf.2 hk
end
end

