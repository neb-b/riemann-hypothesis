module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqMulIInfHeightLeCard
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogThetaSumInvariantSmooth
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyTorusAt
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaWeight

theorem nonempty_torusAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (w0 : 𝓞 E) (hw : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) :
    ∀ x ∈ X.dom, Nonempty (TorusAt X.toData x) := by
  intro x hx
  obtain ⟨A, -⟩ := GlobalTheory.torusAtExists E r X.toData (fun φ => by
    obtain ⟨u, hu, h⟩ := X.EF_perf (-φ)
    refine ⟨u, hu, fun v => ?_⟩
    have h1 := h v
    rw [EFf, neg_mul, map_neg, AddMonoidHom.neg_apply, Int.cast_neg] at h1
    exact neg_injective h1) w0 hw x hx
  exact ⟨A⟩

theorem exists_weight : TStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → ((∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) ∧ (PT.f E : ℝ) ≤ PT.rd E ∧ (PT.f E : ℝ) ^ 2 ≤ PT.rd E ∧ 16 ≤ PT.rd E ∧ ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ PT.f E ∧ (X.p0 ≤ m ∨ r - X.p0 ≤ m)) → ∃ ps : Frame X.Ψ r → ℝ, IsInvFn X.toData ps ∧ (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom}) ∧ (∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ) ∧ cfwM X.toData ps (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card))) := by
  intro hT E _ _ _ r X hiso ⟨hw, hf1, hf2, hrd, hm⟩
  obtain ⟨ps, hps⟩ : ∃ ps : Frame X.Ψ r → ℝ, ∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) := by
    obtain ⟨w0, hw0⟩ := hw
    have h : ∀ x : Frame X.Ψ r, ∃ t : ℝ, x ∈ X.dom → ∃ A : TorusAt X.toData x, t = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) := by
      intro x
      by_cases hx : x ∈ X.dom
      · obtain ⟨A⟩ := nonempty_torusAt X w0 hw0 x hx
        exact ⟨_, fun _ => ⟨A, rfl⟩⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose ps hps using h
    exact ⟨ps, hps⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth E r X hiso hw ps hps
  refine ⟨ps, h1, h2, _root_.GlobalTheory.ThetaSumLevi.levi_log_theta_sum E r X hiso hw ps hps, ?_⟩
  obtain ⟨C, A', -, hC⟩ := GlobalTheory.ThetaSumBound.growth_decay hT E r X hiso hf1 hf2 hrd hm
  refine ⟨⟨C, A', fun x hx => ?_⟩, fun η hη _ => ⟨C, A', fun x hx ξ hξ ht => ?_⟩⟩
  · obtain ⟨A, hA⟩ := hps x hx
    rw [hA]
    exact (hC x hx A (GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A)).1
  · obtain ⟨A, hA⟩ := hps x hx
    rw [hA]
    refine ((hC x hx A (GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A)).2 ξ hξ).trans ?_
    have ht0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => zero_le_one.trans (ht τ)
    have ha : 0 ≤ 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)) := by
      positivity
    generalize 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)) = a at ha ⊢
    generalize ⨅ τ, X.tt ξ x τ = t at ht0 ⊢
    have := mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hη.le) ha) ht0
    linarith

end GlobalTheory.ThetaWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMove
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValMove

open GlobalTheory.TranslMove GlobalTheory.VVRank

section Sections

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left}
  {T : Over S'} {T₀ : Over S} {L₀ : LB G.left} {L₁ : LB A.left}
  {w : LB.Iso L₁ (L₀.pull φ)} {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left}

theorem secRel_of_charts (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    (s₀ : LB.Sec (LPow G L₀ 1 T₀)) (s : LB.Sec (LPow A L₁ 1 T))
    (H : ∀ (i : L₀.ι) (j : L₁.ι) (W : (T ⊗ A).left.Opens),
      W = (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) →
      ∀ (h₀ : W ≤ (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)))
      (h₁ : W ≤ Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i)) (h₂ : W ≤ (LPow A L₁ 1 T).U (fun _ => j)),
      (Ψ.appLE ((LPow G L₀ 1 T₀).U (fun _ => i)) W h₁).hom (s₀.f (fun _ => i)) =
        ((snd T A).left.appLE ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) W h₀).hom
          (Units.val (w.s ((fun _ => i), j))) *
        ((T ⊗ A).left.presheaf.map (homOfLE h₂).op).hom (s.f (fun _ => j))) : SecRel w Ψ s₀ s := by
  refine (secRel_iff hL₀ hL₁ h₂ 1 Nat.cast_one.symm s₀ s).2 fun i j W k₀ k₁ k₂ => fn_ext fun x hx => ?_
  have m₁ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i) := fun p hp => Set.mem_iInter.2 fun _ => by
    have h : ((snd T A).left ≫ φ) p ∈ L₀.U i := mem_pull.1 hp.1
    rw [← h₂] at h
    exact h
  have m₂ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      (LPow A L₁ 1 T).U (fun _ => j) := fun p hp => Set.mem_iInter.2 fun _ => hp.2
  have e := congrArg (gs (𝟙 _) x _) (H i j _ rfl le_rfl m₁ m₂)
  have hx' : (𝟙 (T ⊗ A).left : _ ⟶ _) x ∈ W := hx
  have hx₀ := k₀ hx'
  rw [gs_mul _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀,
    gs_res _ _ _ hx₀] at e
  rw [pow_one, gs_mul _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx',
    gs_res _ _ _ hx']
  exact e

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sv_pull {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')}
    (ha : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
      (pm.appLE _ _ h).hom (s.f i) = s'.f i)
    {Z : Scheme.{0}} (r : Z ⟶ Gx x') (z : Z) {J} (hJ : Good Xo.univ.t.PP.L z J) :
    sv Xo.univ.t.G s (r ≫ pm) z J = sv Xo.univ.t.G s' r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd (Over.mk x') Xo.univ.t.G).left) r
  refine (sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x') Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hs])).trans ?_
  refine (TranslMove.gs_appLE r pm z _ _ (FramedBaseChange.chart_le pm hs _) hm _).symm.trans ?_
  exact congrArg (gs r z _) (ha _ _)

theorem exists_ptEquiv {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {x x' : Sp S ⟶ Xo.X} (hx : x' = x ≫ ρ) :
    ∃ e : (ptO Xo x ⟶ Xo.univ.t.G) ≃* (ptO Xo x' ⟶ Xo.univ.t.G), ∀ p, (e p).left = p.left ≫ ν.φ := by
  subst hx
  refine ⟨MulEquiv.ofBijective (pushHom ν.cart (ptO Xo x)) ⟨fun p q h => ?_, fun q => ?_⟩, fun p => rfl⟩
  · exact Over.OverMorphism.ext (ν.cart.1.hom_ext (congrArg (fun t => t.left) h)
      ((Over.w p).trans (Over.w q).symm))
  · exact ⟨Over.homMk (ν.cart.1.lift q.left x (Over.w q)) (ν.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (ν.cart.1.lift_fst _ _ _)⟩

theorem exists_move_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} (hm : FrMove ρ ν y y')
    {φ : S →ₐ[c.F] T} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y' z') :
    z'.x = z.x ≫ ρ ∧ (∀ τ i, z'.u τ i = z.u τ i ≫ ν.φ) ∧
    ∃ (pm : Gx z.x ⟶ Gx z'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
      pm ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ ∧
      CubIso ν w ∧ SecRel (T := Over.mk z.x) (T₀ := Over.mk z'.x) w pm z'.s z.s := by
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := hm
  obtain ⟨gx, gu, p, ps, pf, pa⟩ := h
  obtain ⟨gx', gu', p', ps', pf', pa'⟩ := h'
  have hL := Xo.univ.t.PP.isLB
  have ex : z'.x = z.x ≫ ρ := by rw [gx', gx, hx, Category.assoc]
  have sq : (fst (Over.mk z.x) Xo.univ.t.G).left ≫ z'.x =
      ((snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, ν.cart.1.w, ex, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ ρ) ((Over.w (fst (Over.mk z.x) Xo.univ.t.G)).trans
      (Over.w (snd (Over.mk z.x) Xo.univ.t.G)).symm)
  let q : Gx z.x ⟶ Gx z'.x := pullback.lift (f := z'.x) (g := Xo.univ.t.G.hom) _ _ sq
  have qf : q ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left :=
    pullback.lift_fst _ _ _
  have qs : q ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ :=
    pullback.lift_snd _ _ _
  have comm : q ≫ p' = p ≫ pm := FramedBaseChange.pulledGroup_hom_ext _ _
    (by rw [Category.assoc, ps', qs, Category.assoc, hs, ← Category.assoc, ps])
    (by rw [Category.assoc, pf', ← Category.assoc, qf, Category.assoc, hf, pf])
  have R := secRel_of_charts (T := Over.mk y.x) (T₀ := Over.mk y'.x) hL hL hs y'.s y.s hc
  refine ⟨ex, fun τ i => by rw [gu', gu, hu, Category.assoc], q, w, qf, qs, hw, fun Z r t J₀ J hJ₀ hJ => ?_⟩
  have a₁ := sv_pull p' ps' pa' (r ≫ q) t hJ₀
  have a₂ := sv_pull p ps pa r t hJ
  have a₃ := R Z (r ≫ p) t J₀ J hJ₀ hJ
  rw [Category.assoc, comm, ← Category.assoc] at a₁
  rw [Category.assoc r p (snd (Over.mk y.x) Xo.univ.t.G).left, ps] at a₃
  exact a₁.symm.trans (a₃.trans (congrArg _ a₂))

theorem eta_congr {a b : Dw.La}
    (h : (Submodule.Quotient.mk a : LevQ Dw l) = Submodule.Quotient.mk b) : Xo.univ.eta a = Xo.univ.eta b := by
  have h2 := Xo.univ.eta_add (a - b) b
  rwa [sub_add_cancel, Xo.univ.eta_ker _ ((Submodule.Quotient.eq _).1 h), _root_.one_mul] at h2

theorem mk_levRep (q : LevQ Dw l) : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem shortValAt_move : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c S), IsLevMove ρ ν gM gA → FrMove ρ ν y y' → ∀ σq : LevQ Dw l ≃ LevQ Dw l, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (gM a)) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y' v → ShortValAt Xo c nab (fun q => w (fun b => σq.symm (q b))) Λ β N P y v := by
  intro hLaw hCI E _ _ _ H Dw l Xo c _ nab hnab S _ _ ρ ν gM gA y y' hlev hmv σq hσ n a P hP w Λ β N v hv
  obtain ⟨S', _, _, φ, y₁', z', tp', F', hff, hfr, hZ, hG, htp, hUU, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : LevQ Dw l, e (levPt Xo y₁.x (levRep q)) = levPt Xo y₁'.x (levRep (σq.symm q)) := fun q => by
    have h1 : Xo.univ.eta (levRep q) = Xo.univ.eta (gM (levRep (σq.symm q))) :=
      eta_congr (by rw [← hσ, mk_levRep, mk_levRep, σq.apply_symm_apply])
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, h1, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun (q : Fin n → LevQ Dw l) i b =>
    isUUOver_move hLaw E H Dw l Xo c S' ρ ν y₁ y₁' pm ω hx hf hs hω
      ((secRel_iff hL hL hs 1 Nat.cast_one.symm y₁'.s y₁.s).1 hR) N (e.symm (z' i b))
      (e.symm (tp' (fun b => σq.symm (q b)) b)) (z' i b) (tp' (fun b => σq.symm (q b)) b) (he' _) (he' _)
      (F' (fun b => σq.symm (q b)) i b) (hUU _ i b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, fun i b => e.symm (z' i b),
    fun q b => e.symm (tp' (fun b => σq.symm (q b)) b), F, hff, hy₁, fun i => ⟨fun b => ?_, ?_⟩, ?_,
    fun q b => ⟨?_, ?_⟩, hF, ?_⟩
  · rw [← map_pow, (hZ i).1 b, map_one]
  · intro mu hmu cm hcm k
    have h := congrArg e.symm ((hZ i).2 mu hmu cm hcm k)
    rw [map_list_prod, List.map_ofFn, map_one] at h
    simp only [hact']
    exact h
  · intro k _ ψ g hg i j hij
    refine hG k ψ (Over.homMk (spMap ψ) rfl) rfl (funext fun b => Over.OverMorphism.ext ?_)
    have h := congrArg (fun t => t.left ≫ ν.φ) (congrFun hij b)
    simp only [Over.comp_left, hg, Category.assoc, ← he'] at h
    exact h
  · rw [← map_pow, (htp _ b).1, ← hlv, e.symm_apply_apply]
  · obtain ⟨j, hj⟩ := (htp (fun b => σq.symm (q b)) b).2
    exact ⟨j, fun t ht => by rw [hact', hj t ht, map_one]⟩
  · rw [hval]
    congr 1
    refine (finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => σq.symm)).symm.trans
      (finsum_congr fun q => ?_)
    refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    exact _root_.GlobalTheory.ChartPush.nab_harmonic_invariant hLaw hCI E H Dw l Xo c nab hnab S' ρ ν y₁ y₁' pm ω hx hf hs hω hu n a P hP N
      (F q i) (F' (fun b => σq.symm (q b)) i) (hFF q i)

end GlobalTheory.ShortValMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnesses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (hm : FrMap ψ y z) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    (hF : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x (x b)) (F b)) :
    ∃ F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (F' b)) ∧
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab z P F' := by
  obtain ⟨hx, -⟩ := id hm
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx.symm
  have hh : h.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm h hh
  have hH : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    unfold harmA HaO at hP
    exact hP.1
  choose F' hF' using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L
    ((l.M : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b)
  refine ⟨F', fun b => ?_, ?_⟩
  · have hv := (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) (ptO Xo y.x)
      (ptO Xo z.x) h y.s z.s hs (F b) (F' b) (hF' b)).1 _ (hF b)
    have e : h ≫ levPt Xo y.x (x b) = levPt Xo z.x (x b) := by
      unfold levPt
      rw [← Category.assoc]
      congr 1
      exact CartesianMonoidalCategory.toUnit_unique _ _
    rwa [e] at hv
  · have hv := _root_.GlobalTheory.harmonicValue_baseChange hC E H Dw l Xo c nab hnab S T ψ y z hm h hh a n P hH l.M F F' hF'
    unfold thExpr
    rw [map_mul, AlgHom.commutes, hv]

theorem thExpr_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s (levPt Xo y1.x (x b)) (F1 b)) → FrMap φ2 y y2 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s (levPt Xo y2.x (x b)) (F2 b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ψ1 (thExpr Xo c nab y1 P F1) = ψ2 (thExpr Xo c nab y2 P F2) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP S1 _ _ φ1 y1 F1 S2 _ _ φ2 y2 F2 hm1 hF1 hm2 hF2 T _ _ ψ1 ψ2 hψ
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S T (ψ1.comp φ1) y
  have hw1 : FrMap ψ1 y1 w := GlobalTheory.FramedBaseChange.cancel φ1 ψ1 hm1 hw
  have hw2 : FrMap ψ2 y2 w := GlobalTheory.FramedBaseChange.cancel φ2 ψ2 hm2 (hψ ▸ hw)
  obtain ⟨G1, hG1, e1⟩ := exists_pull hC nab hnab ψ1 y1 w hw1 a n x P hP F1 hF1
  obtain ⟨G2, hG2, e2⟩ := exists_pull hC nab hnab ψ2 y2 w hw2 a n x P hP F2 hF2
  rw [e1, e2]
  have hG : G1 = G2 := funext fun b => vtUniq_obj hL.globalFns Xo.univ (hG1 b) (hG2 b)
  rw [hG]

end GlobalTheory.ThetaCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace RootShift

open ThetaAct CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

theorem exists_lin_iff (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ f : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ s s', IsActOf A L k θ s s' ↔
      f (SecM.ofSec A s) = SecM.ofSec A s' := by
  obtain ⟨f, hf⟩ := exists_lin hL θ
  refine ⟨f, fun s s' => ?_⟩
  rw [isActOf_iff hL]
  exact ⟨fun H => sv_ext hL fun y J hJ => (hf _ _ _ _ _ hJ).trans (H y J hJ).symm,
    fun H y J hJ => H ▸ hf _ _ _ _ _ hJ⟩

theorem exists_isActOf (hL : L.IsLB) (θ : ThetaGrp A L k T) (s : LB.Sec (LPow A L k T)) :
    ∃ s', IsActOf A L k θ s s' := by
  obtain ⟨f, hf⟩ := exists_lin_iff hL θ
  exact ⟨SecM.toSec A (f (SecM.ofSec A s)), (hf _ _).2 rfl⟩

theorem act_smul (hL : L.IsLB) (θ : ThetaGrp A L k T) (c : Γ(T.left, ⊤))
    {a b a' b' : LB.Sec (LPow A L k T)} (h : ∀ j, b.f j = liftFun A _ c * a.f j)
    (ha : IsActOf A L k θ a a') (hb : IsActOf A L k θ b b') :
    ∀ j, b'.f j = liftFun A _ c * a'.f j := by
  obtain ⟨f, hf⟩ := exists_lin_iff hL θ
  have e : SecM.ofSec A b = c • SecM.ofSec A a := Subtype.ext (funext h)
  have e' : SecM.ofSec A b' = c • SecM.ofSec A a' := by
    rw [← (hf _ _).1 ha, ← (hf _ _).1 hb, e, map_smul]
  exact fun j => congrFun (congrArg Subtype.val e') j

theorem liftFun_one (W : (T ⊗ A).left.Opens) : liftFun A W (1 : Γ(T.left, ⊤)) = 1 := by
  unfold liftFun
  rw [map_one, map_one]

theorem toΓ_bijective (B : Type) [CommRing B] : Function.Bijective (toΓ B) :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv.bijective

end RootShift


open RootShift in
theorem isUUOver_shift : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0))) (t u z : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), t ^ (N ^ 2) = 1 → u ^ (N ^ 2) = 1 → z ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) t u 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) u z e → ∀ F F', IsUUOver Xo.univ.t.G Xo.univ.t.PP N s z (t * u) F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (u * z) t F' → ∃ r : B, (toΓ B r) ^ 2 = (e : Γ((ptO Xo x0).left, ⊤)) ∧ r ^ (N ^ 2) = 1 ∧ ∀ j, F.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x0) (toΓ B r) * F'.f j := by
  intro hLaw E _ _ _ H Dw l Xo B _ x0 N hN s t u z e ht hu hz wtu wuz F F' hF hF'
  have hL := Xo.univ.t.PP.isLB
  have htu : (t * u) ^ (N ^ 2) = 1 := by rw [mul_pow, ht, hu, _root_.one_mul]
  obtain ⟨α₀, α, s₁, s₂, Uuz, Ut, g₀, n₀, cα, tw, hUuz, a₁, hUt, a₂⟩ := hF'
  obtain ⟨Uz, Utu, hUz, hUtu⟩ : ∃ Uz Utu,
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) z Uz ∧
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (t * u) Utu := by
    obtain ⟨-, -, -, -, Uz, Utu, -, -, -, -, h₁, -, h₂, -⟩ := hF
    exact ⟨Uz, Utu, h₁, h₂⟩
  obtain ⟨⟨Uu, hUu⟩, -⟩ := _root_.GlobalTheory.moduli_univ_symLift_global hLaw E H Dw l Xo N hN _ u hu
  obtain ⟨p, hp⟩ := exists_isActOf hL Uz s₁
  obtain ⟨q, hq⟩ := exists_isActOf hL Uu p
  obtain ⟨w, hw⟩ := exists_isActOf hL Ut q
  obtain ⟨G, hG⟩ := exists_isActOf hL Utu p
  obtain rfl : G = F :=
    ((exists_isVtOver_and_existsUnique_isUUOver hLaw E H Dw l Xo N hN _ s).2 z (t * u) hz htu).unique
      ⟨α₀, α, s₁, p, Uz, Utu, g₀, n₀, cα, tw, hUz, hp, hUtu, hG⟩ hF
  obtain ⟨r₀, r₀2, r₀N, h₀⟩ := _root_.GlobalTheory.moduli_univ_symLift_mul hLaw E H Dw l Xo N hN _ t u Ut Uu Utu 1 hUt hUu hUtu wtu
  obtain ⟨r, r2, rN, h₁⟩ := _root_.GlobalTheory.moduli_univ_symLift_mul hLaw E H Dw l Xo N hN _ u z Uu Uz Uuz e hUu hUz hUuz wuz
  obtain rfl : r₀ = 1 := by
    obtain ⟨m, hm⟩ : Odd (N ^ 2) := hN.pow
    rwa [hm, pow_succ, pow_mul, r₀2, one_pow, _root_.one_mul] at r₀N
  obtain ⟨ρ, hρ⟩ := (toΓ_bijective B).2 (r : Γ((ptO Xo x0).left, ⊤))
  refine ⟨ρ, ?_, (toΓ_bijective B).1 ?_, fun j => ?_⟩
  · rw [hρ]
    exact congrArg Units.val r2
  · rw [map_pow, map_one, hρ]
    exact congrArg Units.val rN
  · have e₀ := h₀ p q w G hq hw hG j
    rw [Units.val_one, liftFun_one, _root_.one_mul] at e₀
    rw [hρ, ← e₀]
    exact act_smul hL Ut _ (h₁ s₁ p q s₂ hp hq a₁) a₂ hw j

end GlobalTheory
end

