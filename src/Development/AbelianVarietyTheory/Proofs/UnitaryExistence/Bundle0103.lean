module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsUnfEx

theorem exists_xi {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ ξ₀ : E, cc ξ₀ = -ξ₀ ∧ ξ₀ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
    have him : z.im ≠ 0 := by
      intro h
      rw [h] at h1
      nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ₀ := key (τ₀ (H.rt : E)) (by rw [← map_pow, hsq]; simp)
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    apply τ₀.injective
    unfold cc
    rw [IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hτ₀.1]
  have hne : (H.rt : E) ≠ 0 := by
    intro h
    apply hτ₀.2
    rw [h]; simp
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩
    · unfold cc at hcc ⊢
      rw [map_neg, hcc]
    · rw [map_neg, hτ, Complex.neg_im]; linarith

theorem exists_isUnf : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → ∃ U : Unf Xo c σ (Dw.p + Dw.q), IsUnf U := by
  intro h1 h2 h3 h4 E _ _ _ H Dw l Xo c σ hpq hσ
  obtain ⟨ξ₀, hcc, hne, him⟩ := exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨U, hU, -⟩ :=
    GlobalTheory.T.exists_frameUniformisation_prescribedSpace h1 h2 h3 h4 E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hpq hσ hcc him hφ
  exact ⟨U, hU⟩

end GlobalTheory.IsUnfEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsIndicatingComp
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRead

theorem exists_idempotents_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : U.Comp → Rul Xo c, (∀ k, χ k ∈ sec Xo c 0 0) ∧ (∀ k, χ k * χ k = χ k) ∧ (∀ k k', k ≠ k' → χ k * χ k' = 0) ∧ ∑ k, χ k = 1 ∧ ∀ k k' x, x ∈ (U.X k').dom → (k' = k → rdU U (χ k) k' x = 1) ∧ (k' ≠ k → rdU U (χ k) k' x = 0) := by
  intro E _ _ _ H Dw l Xo c σ r U hr hσ hU hF
  obtain ⟨g, e, F, ik, φ, hφ, hP⟩ := hU.2.2.2.2.2
  have hb : Function.Bijective ik := by
    refine _root_.GlobalTheory.CompBij.ik_bijective E H Dw l Xo c σ r U hr hσ hU g e F ik φ hφ (fun k x => ?_)
    obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hP k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  obtain ⟨χ, h0, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces E H Dw l Xo c σ g _ F hF
  refine ⟨fun k => χ (ik k), fun k => h0 _, fun k => h1 _, fun k k' h => h2 _ _ (fun h' => h (hb.1 h')), ?_, ?_⟩
  · rw [← h3]
    exact hb.sum_comp χ
  · intro k k' x hx
    obtain ⟨Pm, -, hp, hu, -⟩ := hP k' ⟨x, hx⟩
    have hv := h4 (U.un k' ⟨x, hx⟩) (ik k) (ik k') Pm hp hu
    have hr : rdU U (χ (ik k)) k' x = toC (evR Xo c (χ (ik k)) (U.un k' ⟨x, hx⟩)) := dif_pos hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hr, hv, if_pos (congrArg ik h)]
    · rw [hr, hv, if_neg (fun h' => h (hb.1 h'))]

end GlobalTheory.CompRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRatFinCongOfMarks
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRead

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}


set_option maxHeartbeats 800000 in
theorem exists_rat_finCong_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (t : Dw.La → La)
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : La ≃ₗ[𝓞 D.host.E] Λ) (φ' : La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (t a) : Fin V.rank → D.host.E) - (finHom V g).1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (t a) : Fin V.rank → D.host.E) - (finHom V g').1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hΛ hΛ'
  obtain ⟨r1, -, r3, -, r5⟩ := _root_.GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_unitary_of_trace_eq _ _ (_root_.GlobalTheory.Member.latG_lattice_and_completion D V g).2.1 (_root_.GlobalTheory.Member.latG_lattice_and_completion D V g').2.1
    φ φ' _ ξ hξ htr
  obtain ⟨γ, hγ⟩ := r3 δ hδ3
  obtain ⟨m1, m2⟩ := (_root_.GlobalTheory.Member.latG_move D V).1 γ δ g hγ
  have hlat : latG V (γ * g) = latG V g' := by
    ext v
    have hv : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have a1 := m1 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    have a2 := hδ2 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    rw [hv] at a1 a2
    exact a1.symm.trans a2
  have hc : FinCong V l.M ((γ * g)⁻¹ * g') := by
    refine finCong_of_marks l V io hio _ _ hlat (fun a => finVec V (φ' (t a) : Fin V.rank → D.host.E)) ?_ hM'
    intro a ha
    obtain ⟨w, hw, e⟩ := hM a ha
    refine ⟨_, (m2 w).1 hw, ?_⟩
    have e2 := congrArg (fun z => (finHom V γ).1 *ᵥ z) e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
    rw [(r5 _ δ hγ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hδ1] at e2
    exact e2
  have hu : gLat V ((γ * g)⁻¹ * g') = latHat V := by
    refine gLat_eq_of_finCong V _ ((_root_.GlobalTheory.Member.latG_move D V).2.2.2 _ _ hlat) ?_
    have e0 : ((γ * g)⁻¹ * g')⁻¹ = g'⁻¹ * (γ * g) := by group
    rw [e0]
    exact (_root_.GlobalTheory.Member.latG_move D V).2.2.2 _ _ hlat.symm
  exact ⟨γ, (r1 γ).2 ⟨δ, hγ⟩, _, hu, hc, (mul_inv_cancel_left _ _).symm⟩

theorem exists_rat_finCong_of_index {l : Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {n : ℕ}
    {ty : Fin n → D.host.E →+* ℂ}
    (F : FamilyUnif Xo s ty) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (i i' : Fin F.n) (hi : i = i')
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] Λ) (φ' : (F.Di i').La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)))
    (htr' : ∀ a b, (((F.Di i').EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (F.t i a) : Fin V.rank → D.host.E) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (F.t i' a) : Fin V.rank → D.host.E) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hi
  exact exists_rat_finCong_of_marks l V io hio (F.t i) g g' Λ Λ' hΛ hΛ' φ φ' ξ hξ
    (fun a b => (htr a b).symm.trans (htr' a b)) hM hM'


end GlobalTheory.CompRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingAtConjugateSplitPointTransportedTwisted
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem marking_conj_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∀ s, C.ActsBy τ io l.M' s → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ (∀ v : D.La, ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.A • e) ∧ ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty F h1 h2 h3 τ hτ C io hio i P hP i' P' hP' hs hu s hact
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := _root_.GlobalTheory.CompRat.exists_isometry_of_conj_split_anyLevel E H D l Xo σ g ty F h1 h2 h3 τ hτ C io hio i P hP i' P' hP' hs hu
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hA : 0 < l.A := l.A_pos
  have hL : 0 < l.M' := Nat.lcm_pos hM hA
  have hdiv : ∀ m : ℕ, m ∣ l.M' → C.ActsBy τ io m s :=
    ((GlobalTheory.CompRat.Acts.main E H C τ hτ io hio l.M' hL).2 s hact).2
  refine ⟨Φ, hΦ1, hΦ2, hΦ3, fun v a ha b hb hab => ?_, fun v hv a ha b hb hab => ?_⟩
  · have key := hΦ4 l.A s hA (hdiv _ (Nat.dvd_lcm_right _ _)) a ha b hb
    have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ Xo.univ.etaA v).left = y ≫ (Xo.univ.etaA v).left := by
      intro y
      rw [Over.comp_left]
      congr 1
    have h0 : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA.ne'
    rw [← hab, ← F.ex_etaA i P hP v, tu, ← Category.assoc, hu, ← tu, F.ex_etaA i' P' hP' v] at key
    set w := Φ (wE H s • a + H.bar (wE H s) • b) with hw
    have e : F.ex i' P' ((l.A : ℂ)⁻¹ • P' (F.t i' v)) = F.ex i' P' ((l.A : ℂ)⁻¹ • P' w) :=
      Over.OverMorphism.ext key
    have e' := F.ex_add i' P' hP' ((l.A : ℂ)⁻¹ • P' (F.t i' v - w)) ((l.A : ℂ)⁻¹ • P' w)
    rw [← smul_add, ← map_add (f := _), sub_add_cancel, e] at e'
    obtain ⟨x, hx⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
    refine ⟨x, ?_⟩
    rw [← sub_eq_iff_eq_add']
    apply hP'.2.1
    rw [map_nsmul, hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · have key := hΦ4 l.M s hM (hdiv _ (Nat.dvd_lcm_left _ _)) a ha b hb
    have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ Xo.univ.eta v).left = y ≫ (Xo.univ.eta v).left := by
      intro y
      rw [Over.comp_left]
      congr 1
    have h0 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    rw [← hab, ← F.ex_eta i P hP v hv, tu, ← Category.assoc, hu, ← tu, F.ex_eta i' P' hP' v hv] at key
    set w := Φ (wE H s • a + H.bar (wE H s) • b) with hw
    have e : F.ex i' P' ((l.M : ℂ)⁻¹ • P' (F.t i' v)) = F.ex i' P' ((l.M : ℂ)⁻¹ • P' w) :=
      Over.OverMorphism.ext key
    have e' := F.ex_add i' P' hP' ((l.M : ℂ)⁻¹ • P' (F.t i' v - w)) ((l.M : ℂ)⁻¹ • P' w)
    rw [← smul_add, ← map_add (f := _), sub_add_cancel, e] at e'
    obtain ⟨x, hx⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
    refine ⟨x, ?_⟩
    rw [← sub_eq_iff_eq_add']
    apply hP'.2.1
    rw [map_nsmul, hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ h0, one_smul]

end GlobalTheory.CompRat
end

