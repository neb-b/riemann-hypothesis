module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTorusAtOfIsTorusOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OrthoPeriodTorus

section

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) (x : FD.Frame X.Ψ r)

theorem perFr_add (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.Pj.perFr X x (v + w) τ i = Formalism.L2.Pj.perFr X x v τ i + Formalism.L2.Pj.perFr X x w τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := by
    intro ρ
    funext a
    simp [Data.emb]
  unfold Formalism.L2.Pj.perFr
  rw [he, he]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  · simp
  · simp

theorem perFr_smul (α : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.Pj.perFr X x (α • v) τ i = τ α * Formalism.L2.Pj.perFr X x v τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (α • v) = ρ α • Data.emb ρ v := by
    intro ρ
    funext a
    simp [Data.emb]
  have hc : (starRingEnd ℂ) ((conjEmb τ) α) = τ α := by
    simp [conjEmb]
  unfold Formalism.L2.Pj.perFr
  rw [he, he]
  split_ifs
  · simp [Matrix.mulVec_smul]
  · simp
  · simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · simp
  · simp

theorem norm_sq_eq_Hf {J : Type} [Fintype J] (v : EuclideanSpace ℂ J) : ‖v‖ ^ 2 = (I2.Hf v v).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [I2.Hf, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end

theorem isTorusAt_of_isTorusOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W) (T : I2.PT E) (ψ : (Fin W.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → IsTorusOf (W.F.Di (W.ik k)) (fun j => relab c σ (W.e j).1) W.Pm Wu.Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ ∀ th, T.ph th = I2.phiFD (U.X k) th x.1 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu T ψ hg hu ho ht
  classical
  have hU := hu
  unfold Formalism.L2.Pj.IsUnf at hU
  obtain ⟨hr, hPsi, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := hPsi k
  obtain ⟨hbij0, hrt0, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hg
  have hrel : Formalism.L2.PjFree.relab c σ = relab c σ := funext fun τ => rfl
  have hbij : Function.Bijective (relab c σ) := by
    rw [← hrel]
    exact hbij0
  have hrt : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    rw [← hrel]
    exact hrt0 τ
  unfold GlobalTheory.EtaAn.IsTorusOf at ht
  obtain ⟨hTr, -, hHf, hL, hact, -⟩ := ht
  have hsig := W.F.sig (W.ik k)
  have hle := (U.X k).p0_le
  have hcc : ∀ ρ : E →+* ℂ, NumberField.ComplexEmbedding.conjugate (conjEmb ρ) = ρ := by
    intro ρ
    ext y
    simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hcc2 : ∀ ρ : E →+* ℂ, conjEmb (conjEmb ρ) = ρ := by
    intro ρ
    ext y
    simp [conjEmb]
  have hconjMem : ∀ ρ : E →+* ℂ, ρ ∉ (U.X k).Ψ → conjEmb ρ ∈ (U.X k).Ψ := by
    intro ρ hρ
    rw [(U.X k).cmType, hcc]
    exact hρ
  have hmultP : ∀ τ' : E →+* ℂ, relab c σ τ' ∈ (U.X k).Ψ → Dw.mult τ' = Dw.p := by
    intro τ' h
    have h' : τ' (H.rt : E) = H.rt0 := (hrt τ').1 ((hΨ _).1 h)
    simp [Datum.mult, h']
  have hmultN : ∀ τ' : E →+* ℂ, relab c σ τ' ∉ (U.X k).Ψ → Dw.mult τ' = Dw.q := by
    intro τ' h
    have h' : ¬ τ' (H.rt : E) = H.rt0 := fun h'' => h ((hΨ _).2 ((hrt τ').2 h''))
    simp [Datum.mult, h']
  let fwd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (U.X k).Ψ × Fin r := fun s =>
    if h : relab c σ s.1 ∈ (U.X k).Ψ then
      (⟨relab c σ s.1, h⟩, ⟨(U.X k).p0 + s.2, by have := s.2.isLt; have := hmultP _ h; omega⟩)
    else
      (⟨conjEmb (relab c σ s.1), hconjMem _ h⟩,
        ⟨(U.X k).p0 - 1 - s.2, by have := s.2.isLt; have := hmultN _ h; omega⟩)
  have hfwd : Function.Bijective fwd := by
    constructor
    · rintro ⟨τ1, i1⟩ ⟨τ2, i2⟩ heq
      have hi1 := i1.isLt
      have hi2 := i2.isLt
      by_cases h1 : relab c σ τ1 ∈ (U.X k).Ψ <;> by_cases h2 : relab c σ τ2 ∈ (U.X k).Ψ
      · simp only [fwd, dif_pos h1, dif_pos h2, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at heq
        obtain ⟨he1, he2⟩ := heq
        obtain rfl := hbij.1 he1
        obtain rfl : i1 = i2 := Fin.ext (by omega)
        rfl
      · simp only [fwd, dif_pos h1, dif_neg h2, Prod.mk.injEq, Fin.mk.injEq] at heq
        have := hmultN _ h2
        omega
      · simp only [fwd, dif_neg h1, dif_pos h2, Prod.mk.injEq, Fin.mk.injEq] at heq
        have := hmultN _ h1
        omega
      · simp only [fwd, dif_neg h1, dif_neg h2, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at heq
        obtain ⟨he1, he2⟩ := heq
        have hρ : relab c σ τ1 = relab c σ τ2 := by
          have h3 := congrArg conjEmb he1
          rwa [hcc2, hcc2] at h3
        obtain rfl := hbij.1 hρ
        have := hmultN _ h1
        obtain rfl : i1 = i2 := Fin.ext (by omega)
        rfl
    · rintro ⟨⟨ρ, hρ⟩, t⟩
      obtain ⟨τ', rfl⟩ := hbij.2 ρ
      by_cases ht0 : (U.X k).p0 ≤ (t : ℕ)
      · refine ⟨⟨τ', ⟨t - (U.X k).p0, by have := hmultP _ hρ; have := t.isLt; omega⟩⟩, ?_⟩
        simp only [fwd, dif_pos hρ]
        refine Prod.ext (Subtype.ext rfl) (Fin.ext ?_)
        show (U.X k).p0 + ((t : ℕ) - (U.X k).p0) = t
        omega
      · obtain ⟨τ'', hτ''⟩ := hbij.2 (conjEmb (relab c σ τ'))
        have hn : relab c σ τ'' ∉ (U.X k).Ψ := by
          rw [hτ'']
          intro hm
          rw [(U.X k).cmType, hcc] at hm
          exact hm hρ
        refine ⟨⟨τ'', ⟨(U.X k).p0 - 1 - t, by have := hmultN _ hn; omega⟩⟩, ?_⟩
        simp only [fwd, dif_neg hn]
        refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · show conjEmb (relab c σ τ'') = relab c σ τ'
          rw [hτ'', hcc2]
        · show (U.X k).p0 - 1 - ((U.X k).p0 - 1 - (t : ℕ)) = t
          omega
  let idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans (Equiv.ofBijective fwd hfwd)
  have hP : ∀ a j, W.Pm a j = GlobalTheory.RiemMaj.pc (U.X k) x.1 (W.φ k a : Fin r → E) (idx j) := by
    intro a j
    rw [W.pm_eq a j]
    show _ = GlobalTheory.RiemMaj.pc (U.X k) x.1 _ (fwd (W.e j))
    generalize W.e j = s
    obtain ⟨τ', i⟩ := s
    have hi := i.isLt
    by_cases h : relab c σ τ' ∈ (U.X k).Ψ
    · have := hmultP _ h
      have hlt : (U.X k).p0 + (i : ℕ) < r := by omega
      have hnlt : ¬ (U.X k).p0 + (i : ℕ) < (U.X k).p0 := by omega
      simp only [fwd, dif_pos h]
      unfold Formalism.L2.Pj.perFr GlobalTheory.RiemMaj.pc
      simp only [dif_pos h, dif_pos hlt, hnlt, if_false]
    · have := hmultN _ h
      have hc := hconjMem _ h
      have hlt : (U.X k).p0 - 1 - (i : ℕ) < r := by omega
      have hlt' : (U.X k).p0 - 1 - (i : ℕ) < (U.X k).p0 := by omega
      simp only [fwd, dif_neg h]
      unfold Formalism.L2.Pj.perFr GlobalTheory.RiemMaj.pc
      simp only [dif_neg h, dif_pos hc, dif_pos hlt, hlt', if_true]
  have him : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im =
      ((Algebra.trace ℚ E (-(U.X k).ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (W.φ k a : Fin r → E) (W.φ k b)) : ℚ) : ℝ) := by
    intro a b
    rw [Wu.c1 a b]
    exact_mod_cast W.isom k a b
  have hcore := GlobalTheory.RiemMaj.core (U.X k) x.2 idx (fun a => (W.φ k a : Fin r → E)) W.Pm hP
    W.per.2.2.2.1 Wu.Hm Wu.pos him
  let per : (Fin r → E) → Fin W.g → ℂ := fun v j =>
    Formalism.L2.Pj.perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2
  have per_add : ∀ v w, per (v + w) = per v + per w := fun v w =>
    funext fun j => perFr_add (U.X k) x.1 v w _ _
  let φ : (Fin r → E) →+ I2.Vsp T.dim := AddMonoidHom.mk' (fun v => ψ (per v)) (by
    intro v w
    show ψ (per (v + w)) = ψ (per v) + ψ (per w)
    rw [per_add, map_add (f := _)])
  have hφa : ∀ a, φ (W.φ k a : Fin r → E) = ψ (W.Pm a) := by
    intro a
    show ψ (per _) = _
    congr 1
    funext j
    exact (W.pm_eq a j).symm
  have hmem : ∀ v ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(W.φ k).symm ⟨v, hv⟩, by simp⟩
  have hTA : I2.IsTorusAt (U.X k) x.1 T := by
    refine ⟨φ, -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [hL y]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, (W.φ k a).2, hφa a⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨a, rfl⟩ := hmem v hv
        exact ⟨a, (hφa a).symm⟩
    · intro α v
      show ψ (per _) = I2.act α (ψ (per v))
      rw [← hact α (per v)]
      congr 1
      funext j
      exact perFr_smul (U.X k) x.1 (α : E) v _ _
    · intro v hv
      obtain ⟨a, rfl⟩ := hmem v hv
      rw [hφa, norm_sq_eq_Hf, hHf]
      exact hcore.1 a
    · intro u hu' v hv
      obtain ⟨a, rfl⟩ := hmem u hu'
      obtain ⟨b, rfl⟩ := hmem v hv
      rw [hφa, hφa, hHf, him a b, neg_mul, map_neg]
      push_cast
      ring
  refine ⟨hTA, ?_, fun th => (ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf.torusAtLa1_holds E r (U.X k) x.1 x.2 T hTA).2 th⟩
  rw [hTr, hsig.1, hsig.2]
  exact hr.symm

end GlobalTheory.OrthoPeriodTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivLevelSqEqAlpha
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaChain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem polyDeriv_comp_clm {J V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Q : MvPolynomial J ℂ) (u : J → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (g : V →L[ℂ] V) (c : J → ℂ) (hg : ∀ l, g (u l) = c l • u l) (κ : ℂ)
    (hκ : ∀ m ∈ Q.support, (m.prod fun l k => c l ^ k) = κ) :
    I2.polyDeriv Q u (G ∘ g) 0 = κ * I2.polyDeriv Q u G 0 := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right g hG 0
    (i := Multiset.card (Finsupp.toMultiset m)) le_top
  rw [h, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hg]
  rw [ContinuousMultilinearMap.map_smul_univ, ← hκ m hm, smul_eq_mul]
  have : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      m.prod fun l k => c l ^ k := by
    have e1 : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      ∏ k : Fin (Finsupp.toMultiset m).toList.length, c ((Finsupp.toMultiset m).toList.get k) :=
      Fintype.prod_equiv (finCongr (Multiset.length_toList _).symm) _ _ (fun _ => rfl)
    rw [e1, ← List.prod_ofFn]
    have e2 : (List.ofFn fun k => c ((Finsupp.toMultiset m).toList.get k)) = (Finsupp.toMultiset m).toList.map c := by
      rw [List.ofFn_comp' , List.ofFn_get]
    rw [e2, Multiset.prod_map_toList]
    classical
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
  rw [this]; ring

theorem hf_act_act {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (M : ℂ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M) (v w : I2.Vsp dim) :
    I2.Hf (I2.act β v) (I2.act β w) = M * I2.Hf v w := by
  unfold I2.Hf I2.act
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  rw [← h i.1]; ring

theorem translate_eq_comp {E : Type} [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M)
    (h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M) (s : (Fin 1 → I2.Vsp X.dim) → ℂ)
    (a v : Fin n → I2.Vsp X.dim) :
    X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) v =
      X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s) (fun b => I2.act β (v b)) := by
  unfold I2.PT.U I2.HC I2.s0
  simp only [hf_act_act β M h, ← Finset.mul_sum]
  congr 1
  · congr 1; push_cast; ring
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext _
    ext i
    simp [PullbackSections.vspActL, I2.act]
    rw [← h' i.1]; ring

def colMap {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (n : ℕ) :
    (Fin n → I2.Vsp dim) →L[ℂ] (Fin n → I2.Vsp dim) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun b => (vspActL β).comp (LinearMap.proj b))

theorem differentiable_translate {E : Type} [Field E] [NumberField E] (X : I2.PT E) (q n : ℕ)
    (p : I2.Vsp X.dim →ₗ[ℂ] I2.Vsp X.dim) (s : (Fin 1 → I2.Vsp X.dim) → ℂ) (hs : Differentiable ℂ s)
    (a : Fin n → I2.Vsp X.dim) : Differentiable ℂ (X.U q a (I2.s0 X p s)) := by
  have hp : Differentiable ℂ p := (LinearMap.toContinuousLinearMap p).differentiable
  have h1 : Differentiable ℂ (I2.s0 X (n := n) p s) := by
    unfold I2.s0
    have hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => p (v k) := fun k =>
      hs.comp (differentiable_pi.2 fun _ => hp.comp (differentiable_apply k))
    exact fun v => (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (hk k v).hasFDerivAt).differentiableAt
  have h2 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v a := by
    unfold I2.HC I2.Hf
    refine Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun i _ => Differentiable.mul_const ?_ _
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp (differentiable_apply k)
  unfold I2.PT.U
  exact (((h2.const_mul _).sub_const _).cexp).mul (h1.comp (differentiable_id.sub_const a))

theorem polyDeriv_levelSq_eq_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ), (β : E) = IsCMField.complexConj E (α : E) → α * β = (M : 𝓞 E) → ∀ s : (Fin 1 → I2.Vsp X.dim) → ℂ, Differentiable ℂ s → ∀ (a : Fin n → I2.Vsp X.dim) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → I2.Vsp X.dim) (sc : Io → ℂ) (κ : ℂ), (∀ ℓ b, I2.act β (u ℓ b) = sc ℓ • u ℓ b) → (∀ m ∈ P.support, (m.prod fun ℓ e => sc ℓ ^ e) = κ) → I2.polyDeriv P u (X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s)) 0 = κ * I2.polyDeriv P u (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) 0 := by
  intro E _ _ _ X α β M n hβ hα s hs a Io P u sc κ hu hκ
  have hbar : ∀ τ : E →+* ℂ, τ (β : E) = (starRingEnd ℂ) (τ (α : E)) := fun τ => by
    rw [hβ, IsCMField.complexEmbedding_complexConj]
  have h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M := by
    intro τ
    have := congrArg (fun a : 𝓞 E => τ (a : E)) hα
    simpa using this
  have h'' : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M := by
    intro τ
    rw [← h' τ, hbar, Complex.conj_conj, mul_comm]
  have hfun : X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) =
      (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) ∘ colMap β n := by
    funext v
    rw [translate_eq_comp X α β M n h'' h']
    rfl
  rw [hfun]
  refine polyDeriv_comp_clm P u _ ?_ (colMap β n) sc (fun l => funext fun b => hu l b) κ hκ
  exact GlobalTheory.SCV.contDiff_of_differentiable (differentiable_translate X M n (vspActL α) s hs _) ⊤

end GlobalTheory.AlphaChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdFockEqTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem polyDeriv_comp_linear_equiv {σ V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (e : V ≃L[ℂ] W) (P : MvPolynomial σ ℂ) (u : σ → V)
    (G : W → ℂ) (x : V) :
    I2.polyDeriv P u (fun z => G (e z)) x = I2.polyDeriv P (fun ℓ => e (u ℓ)) G (e x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := e.iteratedFDerivWithin_comp_right G (s := Set.univ) uniqueDiffOn_univ (x := x)
    (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have h' : (fun z => G (e z)) = G ∘ e := rfl
  rw [h', h]
  rfl

theorem lintor_hf_neg_right {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf v (-w) = -I2.Hf v w := by
  simp [I2.Hf]

theorem lintor_hf_neg_left {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf (-v) w = -I2.Hf v w := by
  simp [I2.Hf]

theorem polyDeriv_prod_fock_eq_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (g : ℕ) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp X.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ), (∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) → Differentiable ℂ θ → ∀ (n N : ℕ) (a : Fin n → Fin g → ℂ) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → Fin g → ℂ), I2.polyDeriv P u (fun z => ∏ b, fock Hm ((N : ℤ) ^ 2) (a b) (fun w => θ ((N : ℂ) • w)) (z b)) 0 = I2.polyDeriv P (fun ℓ b => ψ (u ℓ b)) (X.U (N ^ 2) (fun b => -ψ (a b)) (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0 := by
  intro E _ _ _ X g ψ Hm θ hH _ n N a Io P u
  let e : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp X.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  have he : ∀ z, e z = fun b => ψ (z b) := fun _ => rfl
  have key := polyDeriv_comp_linear_equiv e P u (X.U (N ^ 2) (fun b => -ψ (a b))
    (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0
  rw [map_zero] at key
  refine Eq.trans ?_ key
  congr 1
  funext z
  rw [he]
  simp only [fock, I2.PT.U, I2.s0, I2.HC, lintor_hf_neg_right, lintor_hf_neg_left, hH, neg_neg,
    Finset.prod_mul_distrib, ← Complex.exp_sum, Pi.sub_apply, sub_neg_eq_add,
    LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul, LinearEquiv.symm_apply_apply]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, mul_neg]
  push_cast
  rfl

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValAtBc
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

theorem shortExpr_bc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F)
    (β : c.F) (a b N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) {J : Type} [Fintype J] (k : ℤ)
    (F : (Fin n → LevQ Dw l) → J → Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    algebraMap c'.F S ((incF c c' hle β)⁻¹ * ((a : c'.F))⁻¹ * ((b : c'.F))⁻¹ *
        ((N : c'.F) ^ (MvPolynomial.map (incF c c' hle) P).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c'.F S (incF c c' hle (w q)) *
        ∑ i, ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support,
          algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) *
          ∏ j, nabBC hle nab y k (F q i j) (colOf m j) =
    algebraMap c.F S (β⁻¹ * ((a : c.F))⁻¹ * ((b : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ j, nab (y.res hle h) k (F q i j) (colOf m j) := by
  have h' : ∀ x : c.F, algebraMap c'.F S (incF c c' hle x) = algebraMap c.F S x := h
  have hd : (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree := by
    simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective P (incF c c' hle).injective]
  congr 1
  · rw [hd, ← h']
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  · refine finsum_congr fun q => ?_
    rw [h']
    congr 1
    exact Finset.sum_congr rfl fun i _ => (_root_.GlobalTheory.FieldBC.polyNab_fieldBC E H Dw l Xo c c' hle nab n P S h y k (F q i)).2

theorem shortValAt_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (v : S), ShortValAt Xo c' (nabBC hle nab) (fun q => incF c c' hle (w q)) Λ (incF c c' hle β) N (MvPolynomial.map (incF c c' hle) P) y v ↔ ShortValAt Xo c nab w Λ β N P (y.res hle h) v := by
  intro E _ _ _ H Dw l Xo c c' hle nab n w Λ β N P S _ _ _ h y v
  constructor
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, hff, hfr, hz, hg, htp, hF, hv⟩
    letI i3 : Algebra c.F S' := resAlg hle S'
    have h' : AlgOver c c' hle S' := fun _ => rfl
    let φ₀ : S →ₐ[c.F] S' := { φ.toRingHom with commutes' := fun x => (congrArg φ (h x).symm).trans (φ.commutes _) }
    exact ⟨S', i1, i3, φ₀, y'.res hle h', z, tp, F, hff, hfr, hz, hg, htp, hF,
      hv.trans (shortExpr_bc hle nab w β _ _ N P h' y' _ F)⟩
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, hff, hfr, hz, hg, htp, hF, hv⟩
    letI i3 : Algebra c'.F S' := (φ.toRingHom.comp (algebraMap c'.F S)).toAlgebra
    have h' : AlgOver c c' hle S' := fun x => (congrArg φ (h x)).trans (φ.commutes x)
    let φ₀ : S →ₐ[c'.F] S' := { φ.toRingHom with commutes' := fun _ => rfl }
    exact ⟨S', i1, i3, φ₀, y'.ext hle h', z, tp, F, hff, hfr, hz, hg, htp, hF,
      hv.trans (shortExpr_bc hle nab w β _ _ N P h' (y'.ext hle h') _ F).symm⟩

end GlobalTheory.FieldBC
end

