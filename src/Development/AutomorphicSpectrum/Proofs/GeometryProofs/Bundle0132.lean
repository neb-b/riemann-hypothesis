module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TransitionMatrixPeriodFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.ChgGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tau_conj (τ : E →+* ℂ) (a : E) : τ (IsCMField.complexConj E a) = ComplexEmbedding.conjugate τ a := by
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  rfl

theorem transition_unique (D : Datum H) {I : Type} [Fintype I] [DecidableEq I] (x e : I → D.La) (T T' : Matrix I I E)
    (hg : (gramE D e).det ≠ 0) (h : IsTransition D x e T) (h' : IsTransition D x e T') : T = T' := by
  have hmul : T * gramE D e = T' * gramE D e := by
    ext m j
    simp only [Matrix.mul_apply, gramE, Matrix.of_apply]
    rw [← h m (e j), ← h' m (e j)]
  have hu : IsUnit (gramE D e).det := isUnit_iff_ne_zero.mpr hg
  calc T = T * gramE D e * (gramE D e)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = T' * gramE D e * (gramE D e)⁻¹ := by rw [hmul]
    _ = T' := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.Ar.Fl.ChgGen

namespace GlobalTheory.CompanionTheory.Ar.Fl


open ChgGen in
theorem constMul_change_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (ρ : ℂ), LinearIndependent (𝓞 E) e → IsTransition (FU.Di i) x e T → T.det ≠ 0 → IsConstMul U τ φ FU i e ρ → IsConstMul U τ φ FU i x (ρ / τ T.det) := by
  intro E _ _ _ H D l Xo c g ty FU i U τ φ e x T ρ he hT hdet hC
  unfold IsConstMul at hC ⊢
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]
  obtain ⟨T₀, hT₀, hgram, -, n, S, hn, hS, hST⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists E H (FU.Di i) _ x e hcard he
  have hg : (gramE (FU.Di i) e).det ≠ 0 := (_root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hTT : T₀ = T := transition_unique (FU.Di i) x e T₀ T hg hT₀ hT
  rw [hTT] at hgram hST
  have hconj : (⇑τ ∘ ⇑(IsCMField.complexConj E)) = ⇑(ComplexEmbedding.conjugate τ) :=
    funext fun a => tau_conj τ a
  have hlin : ∀ (σ : E →+* ℂ) (a : Fin D.p ⊕ Fin D.q → ℂ) (z : Fin D.p ⊕ Fin D.q → Fin g → ℂ),
      tyPart ty σ (∑ j, a j • z j) = ∑ j, a j • tyPart ty σ (z j) := by
    intro σ a z
    funext k
    simp only [tyPart, Finset.sum_apply, Pi.smul_apply, _root_.smul_eq_mul]
    by_cases hk : ty k = σ
    · simp only [if_pos hk]
    · simp only [if_neg hk, MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hinj : ∀ (M : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ), M.det ≠ 0 →
      ∀ u : Fin D.p ⊕ Fin D.q → Fin g → ℂ, (∀ m, ∑ l, M m l • u l = 0) → u = 0 := by
    intro M hM u hu
    funext l k
    have hv : M *ᵥ (fun l => u l k) = 0 := by
      funext m
      have := congrFun (hu m) k
      simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using this
    have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h2 := congrArg (fun v => M⁻¹ *ᵥ v) hv
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h2
    exact congrFun h2 l
  have hcomb : ∀ (Bm : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ)
      (M : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ) (W : Fin D.q → Fin g → ℂ) (m : Fin D.p ⊕ Fin D.q),
      ∑ j, (Bm * Mᵀ) j m • W j = ∑ l, M m l • ∑ j, Bm j l • W j := by
    intro Bm M W m
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, _root_.smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]
  intro P y v w V W C Fm B hPer hu hfr hV hW hCa hB hF
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP : ∀ m k, P (x m) k = ∑ b, ty k (T m b) * P (e b) k := by
    intro m k
    have h1 : (n : ℂ) * P (x m) k = ∑ b, ty k (T m b) * P (e b) k * n := by
      have := congrArg (fun z => z k) (congrArg P (hS m))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [_root_.map_nsmul, _root_.map_sum, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul] at this
      rw [this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hPer.1 (S m b) (e b) k, hST m b, _root_.map_mul, _root_.map_natCast]
      ring
    rw [← Finset.sum_mul, _root_.mul_comm (n : ℂ)] at h1
    exact mul_right_cancel₀ hn' h1
  have hPσ : ∀ (σ : E →+* ℂ) m, tyPart ty σ (P (x m)) = ∑ b, σ (T m b) • tyPart ty σ (P (e b)) := by
    intro σ m
    funext k
    simp only [tyPart, Finset.sum_apply, Pi.smul_apply, _root_.smul_eq_mul]
    by_cases hk : ty k = σ
    · simp only [if_pos hk]
      rw [hP m k, hk]
    · simp only [if_neg hk, MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hBmat : B = Fm * T.map τ * (gramE (FU.Di i) e).map τ * (T.map (ComplexEmbedding.conjugate τ))ᵀ := by
    have h1 : B = Fm * (gramE (FU.Di i) x).map τ := by
      ext j m
      rw [← hF j m, Matrix.mul_apply]
      simp only [Matrix.map_apply, gramE, Matrix.of_apply]
    rw [h1, hgram, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hconj]
    simp only [Matrix.mul_assoc]
  have hTc : (T.map (ComplexEmbedding.conjugate τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (_root_.map_ne_zero _).mpr hdet
  have ha' : ∀ a, tyPart ty τ (∑ m, (C * T.map τ) a m • P (e m)) = V a := by
    intro a
    rw [← hCa a, hlin, hlin]
    simp only [hPσ τ, Matrix.mul_apply, Matrix.map_apply, Finset.smul_sum, Finset.sum_smul, _root_.smul_smul]
    exact Finset.sum_comm
  have hb' : ∀ m, tyPart ty (ComplexEmbedding.conjugate τ) (P (e m)) =
      ∑ j, (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j m • W j := by
    have key := hinj (T.map (ComplexEmbedding.conjugate τ)) hTc
      (fun l => tyPart ty (ComplexEmbedding.conjugate τ) (P (e l)) -
        ∑ j, (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j l • W j) (by
        intro m
        simp only [smul_sub, Finset.sum_sub_distrib, Matrix.map_apply]
        rw [← hPσ (ComplexEmbedding.conjugate τ) m, hB m, hBmat, sub_eq_zero]
        exact hcomb _ _ W m)
    intro m
    exact sub_eq_zero.mp (congrFun key m)
  have hc' : ∀ j m, ∑ r, (Fm * T.map τ) j r * τ (sesq (FU.Di i) (e r) (e m)) =
      (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j m := by
    intro j m
    rw [Matrix.mul_apply (M := Fm * T.map τ)]
    simp only [Matrix.map_apply, gramE, Matrix.of_apply]
  have key := hC P y v w V W (C * T.map τ) (Fm * T.map τ) (Fm * T.map τ * (gramE (FU.Di i) e).map τ)
    hPer hu hfr hV hW ha' hb' hc'
  rw [← Matrix.fromRows_mul, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at key
  have hτ : τ T.det ≠ 0 := (_root_.map_ne_zero τ).mpr hdet
  rw [eq_div_iff hτ, ← key]
  ring

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anSolve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), LinearIndependent (𝓞 E) e → IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → ∃! x : (Fin D.p → Fin g → ℂ) × (Fin D.q → Fin g → ℂ) × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × ℂ, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.1 a) (v a).left) ∧ (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.2.1 j) (w j).left) ∧ (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, x.2.2.2.1 j n • x.2.1 j) ∧ (∀ j n, ∑ m, x.2.2.1 j m * τ' (sesq (FU.Di i) (e m) (e n)) = x.2.2.2.1 j n) ∧ x.2.2.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, ∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) ∧ ∀ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) → (Matrix.fromRows C x.2.2.1).det = x.2.2.2.2 := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU _ _ hτ i e P y v w he hP hy hfr
  obtain ⟨-, -, hv, hw⟩ := hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V, hVd, hVl, hVs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W, hWd, hWl, hWs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hS : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))).det ≠ 0 := by
    have := hd 0 _ e hcard he
    have h2 : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) = (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  have hlin : IsLinearMap ℂ (tyPart ty τ') := by
    constructor
    · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
    · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp
  obtain ⟨⟨Fm, B, d⟩, ⟨h1, h2, h3, h4, h5⟩, hu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra D.p D.q g (tyPart ty τ') (tyPart ty (ComplexEmbedding.conjugate τ')) V W (fun m => P (e m)) _ Hm hlin hHh hHp hS hVl hWl (fun n => hVs _) (fun n => hWs _) (fun m n => hs τ' _ _)
  refine ⟨⟨V, W, Fm, B, d⟩, ⟨fun a => (hVd a _).2 rfl, fun j => (hWd j _).2 rfl, h1, h2, h3, h4, h5⟩, ?_⟩
  rintro ⟨V', W', Fm', B', d'⟩ ⟨k1, k2, k3, k4, k5, k6, k7⟩
  have eV : V' = V := funext fun a => (hVd a _).1 (k1 a)
  have eW : W' = W := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW
  have := hu ⟨Fm', B', d'⟩ ⟨k3, k4, k5, k6, k7⟩
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnipotentEntriesFieldDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower

theorem adjoin_lower_eq_top : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (S : Type) (r : S → ℕ)
    (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω),
    (∀ σ k, u σ k k = 1) → (∀ σ l k, l < k → u σ l k = 0) →
    Module.finrank (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω = 1 →
    IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) = ⊤ := by
  intro Ω₀ Ω _ _ _ S r u hdiag hup hfin
  rw [IntermediateField.finrank_eq_one_iff_eq_top] at hfin
  rw [← hfin]
  apply le_antisymm
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨⟨σ, ⟨l, k⟩, _⟩, rfl⟩
    exact ⟨⟨σ, l, k⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨σ, l, k⟩, rfl⟩
    rcases lt_trichotomy l k with h | h | h
    · simp only [hup σ l k h]
      exact zero_mem _
    · subst h
      simp only [hdiag σ l]
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨l, k⟩, h⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower
end

