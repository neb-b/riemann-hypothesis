module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveBis

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameIndependent
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat.Ratio

open Matrix

theorem hf_sum_left {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, c i • V i) w = ∑ i, c i * hermForm Hm (V i) w := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, sum_dotProduct, smul_dotProduct]

theorem hf_sum_right {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ i, c i • V i) = ∑ i, star (c i) * hermForm Hm z (V i) := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum,
    Matrix.mulVec_smul, dotProduct_smul]

theorem exists_row {R M I : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype I]
    (e : I → M) (he : LinearIndependent R e) (hc : Fintype.card I = Module.finrank R M) (x : M) :
    ∃ (n : R) (c : I → R), n ≠ 0 ∧ n • x = ∑ m, c m • e m := by
  classical
  have hnot : ¬ LinearIndependent R (fun o : Option I => o.elim x e) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, hc] at this
    omega
  obtain ⟨c, hsum, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hnot
  rw [Fintype.sum_option] at hsum
  simp only [Option.elim] at hsum
  have hn : c none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hsum
    have := Fintype.linearIndependent_iff.1 he (fun m => c (some m)) hsum
    cases o with
    | none => exact ho h0
    | some m => exact ho (this m)
  refine ⟨c none, fun m => - c (some m), hn, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hsum

theorem lifts_change {p q g : ℕ} (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (π π₀ : Fin p ⊕ Fin q → Fin g → ℂ) (S S₀ Tm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hT : IsLinearMap ℂ T) (hH : Hm.IsHermitian)
    (hHp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (hS : S.det ≠ 0) (hS₀ : S₀.det ≠ 0)
    (hV : LinearIndependent ℂ V) (hW : LinearIndependent ℂ W)
    (hVs : ∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) (hWs : ∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W))
    (hVs₀ : ∀ n, T (π₀ n) ∈ Submodule.span ℂ (Set.range V)) (hWs₀ : ∀ n, T' (π₀ n) ∈ Submodule.span ℂ (Set.range W))
    (hF : ∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n)
    (hF₀ : ∀ m n, hermForm Hm (T (π₀ m)) (T (π₀ n)) - star (hermForm Hm (T' (π₀ m)) (T' (π₀ n))) = 2 * Complex.I * S₀ m n)
    (hc : ∀ m, T (π m) = ∑ k, Tm m k • T (π₀ k)) (hc' : ∀ m, T' (π m) = ∑ k, star (Tm m k) • T' (π₀ k)) :
    Tm.det ≠ 0 ∧ ∃ (C C₀ : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B Fm₀ B₀ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a, T (∑ m, C a m • π m) = V a) ∧ (∀ n, T' (π n) = ∑ j, B j n • W j) ∧ (∀ j n, ∑ m, Fm j m * S m n = B j n) ∧
      (∀ a, T (∑ m, C₀ a m • π₀ m) = V a) ∧ (∀ n, T' (π₀ n) = ∑ j, B₀ j n • W j) ∧
      (∀ j n, ∑ m, Fm₀ j m * S₀ m n = B₀ j n) ∧ (Matrix.fromRows C Fm).det ≠ 0 ∧
      (Matrix.fromRows C₀ Fm₀).det = (Matrix.fromRows C Fm).det * Tm.det := by
  obtain ⟨⟨Fm, B, d⟩, ⟨h1, h2, h3, ⟨C, hC⟩, h5⟩, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra p q g T T' V W π S Hm hT hH hHp hS hV hW hVs hWs hF
  obtain ⟨⟨Fm₀, B₀, d₀⟩, ⟨k1, k2, k3, -, k5⟩, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra p q g T T' V W π₀ S₀ Hm hT hH hHp hS₀ hV hW hVs₀ hWs₀ hF₀
  simp only at h1 h2 h3 hC h5 k1 k2 k3 k5
  have lin : ∀ (c : Fin p ⊕ Fin q → ℂ) (x : Fin p ⊕ Fin q → Fin g → ℂ), T (∑ m, c m • x m) = ∑ m, c m • T (x m) := by
    intro c x
    have := map_sum (hT.mk' T) (fun m => c m • x m) Finset.univ
    simpa using this

  have hmat : S = Tm * S₀ * Tmᴴ := by
    ext m n
    have e0 := hF m n
    rw [hc m, hc n, hc' m, hc' n] at e0
    simp only [hf_sum_left, hf_sum_right, star_sum, star_mul', star_star, Finset.mul_sum] at e0
    have e1 : (2 * Complex.I) * (Tm * S₀ * Tmᴴ) m n = 2 * Complex.I * S m n := by
      rw [← e0, ← Finset.sum_sub_distrib]
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hF₀ j i
      linear_combination (- (Tm m j * star (Tm n i))) * this
    have h2I : (2 * Complex.I) ≠ 0 := by simp
    exact (mul_left_cancel₀ h2I e1).symm
  have hdetH : Tmᴴ.det = star Tm.det := Matrix.det_conjTranspose Tm
  have hTdet : Tm.det ≠ 0 := by
    intro h0
    apply hS
    rw [hmat, Matrix.det_mul, Matrix.det_mul, h0]
    simp
  have hTH : Tmᴴ.det ≠ 0 := by
    rw [hdetH]; simpa using hTdet
  have hBm : B = B₀ * Tmᴴ := by
    ext j n
    have e0 : ∑ j, (B j n - (B₀ * Tmᴴ) j n) • W j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1 n, hc' n, sub_eq_zero]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [k1 k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hW _ e0 j)
  have hFS : Fm * S = B := by
    ext j n
    simpa [Matrix.mul_apply] using h2 j n
  have hFS₀ : Fm₀ * S₀ = B₀ := by
    ext j n
    simpa [Matrix.mul_apply] using k2 j n
  have hFm : Fm * Tm = Fm₀ := by
    have a1 : (Fm * Tm * S₀) * Tmᴴ = (Fm₀ * S₀) * Tmᴴ := by
      rw [hFS₀, ← hBm, ← hFS, hmat]
      simp only [Matrix.mul_assoc]
    have iTH : IsUnit Tmᴴ.det := isUnit_iff_ne_zero.2 hTH
    have iS : IsUnit S₀.det := isUnit_iff_ne_zero.2 hS₀
    have a2 : Fm * Tm * S₀ = Fm₀ * S₀ := by
      have := congrArg (· * Tmᴴ⁻¹) a1
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ iTH] using this
    have := congrArg (· * S₀⁻¹) a2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ iS] using this
  have hC₀ : ∀ a, T (∑ m, (C * Tm) a m • π₀ m) = V a := by
    intro a
    rw [← hC a, lin, lin]
    simp only [hc, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  have hd : d ≠ 0 := h3
  have hd' : (Matrix.fromRows C Fm).det = d := h5 C hC
  refine ⟨hTdet, C, C * Tm, Fm, B, Fm₀, B₀, hC, h1, h2, hC₀, k1, k2, by rw [hd']; exact hd, ?_⟩
  rw [← hFm, ← Matrix.fromRows_mul, Matrix.det_mul]

end GlobalTheory.CompanionTheory.Ar.Flat.Ratio

namespace GlobalTheory.CompanionTheory.Ar.Flat.Ratio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tyPart_add {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty σ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem tyPart_row {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (σ : E →+* ℂ) {I : Type} [Fintype I] (e : I → D.La) (x : D.La) (n : 𝓞 E) (c : I → 𝓞 E) (hn : n ≠ 0)
    (h : n • x = ∑ m, c m • e m) :
    tyPart ty σ (P x) = ∑ m, (σ (c m : E) / σ (n : E)) • tyPart ty σ (P (e m)) := by
  have hσ : σ (n : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hn
  funext k
  simp only [tyPart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hk
  · have e1 := congrFun (congrArg P h) k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP.1, map_sum, Finset.sum_apply] at e1
    simp only [hP.1, hk] at e1
    rw [eq_comm, ← mul_right_inj' hσ, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  · simp

end GlobalTheory.CompanionTheory.Ar.Flat.Ratio


open GlobalTheory.CompanionTheory.Ar.Flat.Ratio in
theorem GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : ℂ, ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i _ h1 h2 hU
  obtain ⟨e, ρ, he, hc⟩ := h1.flat
  obtain ⟨e₀, ρ₀, he₀, hc₀⟩ := h2.flat
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hcard' : Fintype.card (Fin D.p ⊕ Fin D.q) = Module.finrank (𝓞 E) (FU.Di i).La := by
    rw [hcard, (FU.Di i).rank]
  haveI := (FU.Di i).fin
  choose n cf hn hrow using fun m => exists_row e₀ he₀ hcard' (e m)
  set Tm : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m k => τ (cf m k : E) / τ (n m : E) with hTm
  refine ⟨ρ * Tm.det / ρ₀, fun y v w hfr => ?_⟩
  obtain ⟨P, hP, hy⟩ := hU y hfr.1 hfr.2.1
  have hfv := hfr.2.2.1
  have hfw := hfr.2.2.2
  obtain ⟨V, hVd, hVl, hVs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ τ D.p v hP hy (fun a => rfl) hfv
  obtain ⟨W, hWd, hWl, hWs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ) D.q w hP hy
    (fun a => rfl) hfw
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
  have hSdet : ∀ e' : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e' →
      (Matrix.of fun m n => τ (sesq (FU.Di i) (e' m) (e' n))).det ≠ 0 := by
    intro e' he'
    have := hd 0 _ e' hcard he'
    have h2 : (Matrix.of fun m n => τ (sesq (FU.Di i) (e' m) (e' n))) =
        (Matrix.of fun m n => sesq (FU.Di i) (e' m) (e' n)).map τ := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 this
  obtain ⟨hTdet, C, C₀, Fm, B, Fm₀, B₀, a1, a2, a3, b1, b2, b3, hdet, hrel⟩ :=
    lifts_change (tyPart ty τ) (tyPart ty (ComplexEmbedding.conjugate τ)) V W (fun m => P (e m)) (fun m => P (e₀ m)) _ _ Tm Hm
      (tyPart_add ty τ) hHh hHp (hSdet e he) (hSdet e₀ he₀) hVl hWl (fun _ => hVs _) (fun _ => hWs _) (fun _ => hVs _)
      (fun _ => hWs _) (fun m n => hs τ _ _) (fun m n => hs τ _ _)
      (fun m => tyPart_row hP τ e₀ (e m) (n m) (cf m) (hn m) (hrow m))
      (fun m => by
        rw [tyPart_row hP (ComplexEmbedding.conjugate τ) e₀ (e m) (n m) (cf m) (hn m) (hrow m)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hTm, ComplexEmbedding.conjugate_coe_eq])
  have c1 := hc P y v w V W C Fm B hP hy hfr (fun a => (hVd a _).2 rfl) (fun j => (hWd j _).2 rfl) a1 a2 a3
  have c2 := hc₀ P y v w V W C₀ Fm₀ B₀ hP hy hfr (fun a => (hVd a _).2 rfl) (fun j => (hWd j _).2 rfl) b1 b2 b3
  have hφ₀ : φ₀ ℂ y v w ≠ 0 := h2.line.ne ℂ _ y v w hfr
  have hρ₀ : ρ₀ ≠ 0 := by
    rw [← c2, hrel]
    exact mul_ne_zero hφ₀ (mul_ne_zero hdet hTdet)
  rw [← c1, ← c2, hrel]
  field_simp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagUnderEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.Transport

theorem flagStep_equiv {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (Φ : F ≃ₗ[Ω] F') {r : ℕ} (b : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (b k)) i = (flagStep Ω b i).map Φ.toLinearMap := by
  rw [flagStep, flagStep, Submodule.map_span, Set.image_image]
  rfl

theorem isGenericFlag_transport : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  intro Ω₀ Ω _ _ _ E₀ E F F' _ _ _ _ _ _ _ _ a j Φ S r V V₀ b d hV hG
  obtain ⟨c, u, hc, hjlin, hjc, hb, hu1, hu0, hflag, halg, hd, hrank⟩ := hG
  refine ⟨fun σ k => a.symm (c σ k), u, fun σ => ⟨?_, ?_⟩, ?_, fun σ => ?_, fun σ => ?_, hu1, hu0,
    fun σ i => ?_, halg, hd, hrank⟩
  · exact (hc σ).1.map' a.symm.toLinearMap a.symm.ker
  · have h1 : Submodule.span Ω₀ (Set.range fun k => a.symm (c σ k)) =
        (Submodule.span Ω₀ (Set.range (c σ))).map a.symm.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, (hc σ).2]
    ext e
    rw [hV σ e, Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  · intro x e
    show Φ (j (a (x • e))) = algebraMap Ω₀ Ω x • Φ (j (a e))
    rw [map_smul, hjlin, map_smul]
  · have hfe : (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom)
        (a.symm (c σ k))) = ⇑Φ.toLinearMap ∘ fun k => j (c σ k) := by
      funext k
      show Φ (j (a (a.symm (c σ k)))) = Φ (j (c σ k))
      rw [LinearEquiv.apply_symm_apply]
    have h3 : LinearIndependent Ω (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp
        a.toLinearMap.toAddMonoidHom) (a.symm (c σ k))) := by
      rw [hfe]
      exact (hjc σ).map' Φ.toLinearMap Φ.ker
    exact h3
  · exact (hb σ).map' Φ.toLinearMap Φ.ker
  · have hfun : (fun k => ∑ l, u σ l k •
        ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) =
        fun k => Φ (∑ l, u σ l k • j (c σ l)) := by
      funext k
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      show u σ l k • Φ (j (a (a.symm (c σ l)))) = u σ l k • Φ (j (c σ l))
      rw [LinearEquiv.apply_symm_apply]
    calc flagStep Ω (fun k => Φ (b σ k)) i = (flagStep Ω (b σ) i).map Φ.toLinearMap := flagStep_equiv Φ (b σ) i
      _ = (flagStep Ω (fun k => ∑ l, u σ l k • j (c σ l)) i).map Φ.toLinearMap := by rw [hflag σ i]
      _ = flagStep Ω (fun k => Φ (∑ l, u σ l k • j (c σ l))) i := (flagStep_equiv Φ _ i).symm
      _ = flagStep Ω (fun k => ∑ l, u σ l k •
          ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) i := by
        rw [hfun]

end GlobalTheory.CompanionTheory.Ar.FlagStep.Transport
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagRead

open GlobalTheory.CompanionTheory.Ar.FlagPull

theorem fieldRange_finite {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    FiniteDimensional i.fieldRange Ω ∧
      Module.finrank i.fieldRange Ω = (letI := i.toAlgebra; Module.finrank Ω₁ Ω) := by
  letI := i.toAlgebra
  haveI := hfin
  let e : Ω₁ ≃+* i.fieldRange := RingEquiv.ofBijective i.rangeRestrictField
    ⟨fun x y h => i.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have he : (algebraMap i.fieldRange Ω).comp (e : Ω₁ →+* i.fieldRange) =
      ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω).comp (algebraMap Ω₁ Ω) := by
    ext x
    rfl
  exact ⟨Module.Finite.of_equiv_equiv e (RingEquiv.refl Ω) he,
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω) he).symm⟩

theorem span_eq_of_indep {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b' : Fin r → V}
    {W : Submodule Ω V} (hb : LinearIndependent Ω b) (hle : ∀ k, b k ∈ W) (hb' : LinearIndependent Ω b')
    (hs : Submodule.span Ω (Set.range b') = W) : Submodule.span Ω (Set.range b) = W := by
  subst hs
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b')) :=
    FiniteDimensional.span_of_finite Ω (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hle k
  · rw [finrank_span_eq_card hb, finrank_span_eq_card hb']

theorem generic_read : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hfin hd hf hcst hj hpt hρ
  obtain ⟨hfd, hfr⟩ := fieldRange_finite i hfin
  haveI := hfd
  have hgen : genPt A.ξ₀ = genPt B.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt B.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso A.gen₀ B.gen₀ hgen
  have hfn : B.fn.comp ψ.toRingHom = i.comp A.fn := by
    haveI := mono_of_isCptGen A.gen₀
    have e1 : spMap B.fn ≫ B.ξ₀ = B.ξ ≫ B.f := B.fn_over.symm
    have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
    have e3 : B.ξ ≫ h = spMap i ≫ A.ξ := hd
    have e4 : spMap (B.fn.comp ψ.toRingHom) = spMap (i.comp A.fn) := by
      refine (cancel_mono A.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, FlagPull.spMap_comp, Category.assoc, Category.assoc, hψ, e1, e2, hf, ← Category.assoc, e3,
        Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  letI mod' : Module B.Ω₀ Fl.Li₀ := Module.compHom _ ψ.symm.toRingHom
  have hs : ∀ (a : A.Ω₀) (e : Fl.Li₀), ψ a • e = a • e := fun a e => by
    show ψ.symm (ψ a) • e = a • e
    rw [ψ.symm_apply_apply]
  have hemb : ∀ s, B.emb s = i.comp (A.emb s) := fun s => by
    simp only [HodgeCpt.emb]
    rw [hcst]
    rfl
  have hVgen : ∀ s w, jA w ∈ B.Vgen s ↔ w ∈ A.Vgen s := fun s w => by
    show jA w ∈ eigSp B.ρ (B.emb s) ↔ w ∈ eigSp A.ρ (A.emb s)
    rw [hemb]
    exact mem_eigSp_iff hj _ _ _ hρ w
  let V₀' : CMType H ⊕ CMType H → Submodule B.Ω₀ Fl.Li₀ := fun s =>
    { carrier := (Fl.V₀ s : Set Fl.Li₀)
      add_mem' := fun ha hb => (Fl.V₀ s).add_mem ha hb
      zero_mem' := (Fl.V₀ s).zero_mem
      smul_mem' := fun c x hx => (Fl.V₀ s).smul_mem (ψ.symm c) hx }
  have hsq : spMap (dualMap i) ≫ spMap (dualMap A.fn) = spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    rw [← FlagPull.spMap_comp, ← FlagPull.spMap_comp, ← dualMap_comp, ← dualMap_comp, hfn]
  have hspan : ∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s := by
    intro s
    letI := A.fn.toAlgebra
    obtain ⟨cc, u, hcV, -, -, hb, -, -, hfl, -⟩ := Fl.generic
    have hmemc : ∀ k, Fl.j (cc s k) ∈ A.Vgen s := fun k => (Fl.V₀_mem s _).1 (by
      rw [← (hcV s).2]
      exact Submodule.subset_span ⟨k, rfl⟩)
    have hbk : ∀ a, Fl.b s a ∈ A.Vgen s := by
      intro a
      have h1 : Fl.b s a ∈ flagStep Ω₁ (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨a, a.2, rfl⟩
      rw [hfl s] at h1
      refine (Submodule.span_le (p := A.Vgen s).2 ?_) h1
      rintro _ ⟨k, -, rfl⟩
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmemc l)
    obtain ⟨U, hU, b', hb', hfr'⟩ := B.vb s ⟨genPt B.ξ, specializes_rfl⟩ (Set.mem_univ _)
    exact span_eq_of_indep (hj.2 _ _ (hb s)) (fun k => (hVgen s _).2 (hbk k))
      (hfr' _ (Set.mem_univ _) hU).1 hb'
  refine ⟨Fl.Li₀, Fl.acg, mod', transport ψ hψ hs Fl.M₀, jA.comp Fl.j, V₀', hspan, fun e => ?_,
    fun s e => (Fl.V₀_mem s e).trans (hVgen s _).symm, ?_⟩
  · show (B.M.pt (jA (Fl.j e))).left ≫ B.m.φ =
      spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left
    rw [hpt, Fl.j_pt, ← Category.assoc, hsq, Category.assoc]
  · have := genericFlag_pull A.fn B.fn ψ i hfn hs Fl.j jA hj Fl.V₀ V₀' (fun _ _ => Iff.rfl) Fl.b Fl.deg Fl.generic
    rw [hfr] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.FlagRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeSpan
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.LieSpan

theorem span_range_pullback : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  intro S G _ _ R R' _ _ c x E E' _ _ _ _ M M' j hj
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' :=
    ⟨fun r r' e => by
      show (c r * r') • e = c r • (r' • e)
      exact mul_smul _ _ _⟩
  let h : GlobalTheory.CompanionTheory.Ar.epsAt (Spec.map (CommRingCat.ofHom c) ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c))) (by
      show Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
        Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
          Spec.map (CommRingCat.ofHom c) ≫ x
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom])
  have hl : h.left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) := rfl
  have hpt : ∀ e, M'.pt (j e) = h ≫ M.pt e := fun e =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hl]; exact hj e)
  have hadd : ∀ a b, j (a + b) = j a + j b := by
    intro a b
    apply M'.inj
    rw [M'.add, hpt, hpt, hpt, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) (e : E), j (r • e) = c r • j e := by
    intro r e
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [M'.smul, hpt, hpt, Over.comp_left, Over.comp_left, M.smul, hl,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a <;>
      simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom]
  let β : E →ₗ[R] E' :=
    { toFun := j, map_add' := hadd, map_smul' := fun r e => hsmul r e }
  obtain ⟨-, -, hbc⟩ := GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M
  have hb : IsBaseChange R' β := hbc R' E' M' β (fun e => hj e)
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    rw [hb.equiv_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb' =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.LieSpan
end

