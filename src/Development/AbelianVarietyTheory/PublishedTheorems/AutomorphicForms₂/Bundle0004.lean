module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters GlobalTheory.RealPar Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.Published.CoverSeries

variable {p q n : ℕ}

def pull {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : URep T where
  H := H
  π := { toFun := fun x => σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))
         map_one' := by simpa using hσ.1.1
         map_mul' := fun x y => by
           rw [ContinuousLinearMap.mul_def, ← hσ.1.2 _ (h.cov_mem T x) _ (h.cov_mem T y)]
           simp [Matrix.submatrix_mul_equiv] }
  isom x v := hσ.2.1 _ (h.cov_mem T x) v
  cont v := (hσ.2.2 v).comp_continuous
    ((Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)).matrix_reindex e e) (h.cov_mem T)

theorem exists_of_isDSPar (T : GrpData p q)
    (hM : ∀ U : URep T, Formalism.MainNotions.SchurIrreducible.IrrU U → ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io)
    (P : SignedPar n) {e : Ix p q ≃ Fin n} (h : BlockOrd e P.sgn) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDSPar P σ) :
    ∃ R : DSRep T, HasParam R (blockPar P e) := by
  haveI : CompleteSpace H := hσ.1
  have hU := hσ.2.2.1
  have hirr : Formalism.MainNotions.SchurIrreducible.IrrU (pull h T hU) := ⟨hσ.2.1, fun S hS hst => hσ.2.2.2.1 S hS fun g hg v hv => by
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    exact hst x v hv⟩
  obtain ⟨M, io, m1, m2, m3⟩ := hM _ hirr
  haveI := SqInt.isHaarMeasure_map_covU h T
  have hμ := Measure.isMulLeftInvariant_eq_smul (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn)
  obtain ⟨d, hd, hI⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n P.sgn P.lam H σ hσ _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn))
  refine ⟨⟨pull h T hU, hirr.1, hirr.2, d, hd, fun x y => ?_, M, io, m1, m2, m3⟩, ?_⟩
  · change H at x y
    obtain ⟨i1, i2⟩ := hI x y x y
    rw [← ENNReal.smul_def, ← hμ] at i1 i2
    have hf : (fun g => coefOn (ε := P.sgn) σ x y g * star (coefOn (ε := P.sgn) σ x y g)) =
        fun g => ((‖coefOn (ε := P.sgn) σ x y g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hf] at i1 i2
    have hm := (SqInt.continuous_covU h T).measurable.aemeasurable (μ := T.haar)
    rw [integral_map hm i1.aestronglyMeasurable] at i2
    have i3 := (integrable_map_measure i1.aestronglyMeasurable hm).1 i1
    refine ⟨i3.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at i2
    have i4 : ((∫ g, ‖coefOn (ε := P.sgn) σ x y (SqInt.covU h T g)‖ ^ 2 ∂T.haar : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      push_cast
      exact i2
    exact_mod_cast i4
  · exact (hasParam_iff_isDSPar _ P h (σ := σ) fun _ => rfl).2 hσ

theorem of_upq (hE : DiscreteSeriesUpqExists)
    (hM : ∀ p q : ℕ, 1 ≤ p + q → ∀ (T : GrpData p q) (U : URep T), Formalism.MainNotions.SchurIrreducible.IrrU U →
      ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io) :
    DiscreteSeriesCoverExists := by
  intro p q T lam hl
  rcases Nat.eq_zero_or_pos (p + q) with h0 | h0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.1 h0
    exact ⟨Cover.trivZero T, GlobalTheory.SignedParTest.hasParam_zero _ _⟩
  have key : ∀ lam : Ix p q → ℚ, IsParam lam → (∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m) →
      ∃ R : DSRep T, HasParam R lam := by
    intro lam hl hi
    obtain ⟨P, e, -, h, rfl⟩ := exists_blockPar hl hi
    obtain ⟨H, _, _, σ, hσ⟩ := hE _ P.sgn P.lam P.hc
    exact exists_of_isDSPar T (hM p q h0 T) P h hσ
  obtain ⟨P, e, -, h, rfl | rfl⟩ := isParam_cases hl
  · exact key _ hl fun a => ⟨(P.hc.2 (e a)).choose, by simp [blockPar, ratEntry]⟩
  · obtain ⟨R, hR⟩ := key (fun a => blockPar P e a + 1 / 2 + 1 / 2)
      ⟨fun x y e => hl.1 (add_left_injective _ e), fun x y e => by simpa using hl.2.1 x y e,
        fun x => by
          obtain ⟨k, hk⟩ := hl.2.2.1 x
          exact ⟨k + 1, by push_cast; linarith⟩,
        fun x y => by simpa using hl.2.2.2 x y⟩
      fun a => ⟨(P.hc.2 (e a)).choose + 1, by simp only [blockPar, ratEntry]; push_cast; ring⟩
    exact ⟨Cover.twist R, (Cover.hasParam_twist R _).2 hR⟩

end GlobalTheory.Published.CoverSeries

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.Published

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace AutFin

def coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ {f | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun k => ℓ (ρ k w)}

def IsContRep {K W : Type} [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) : Prop :=
  ∀ (ℓ : Module.Dual ℂ W) (w : W), Continuous fun k => ℓ (ρ k w)

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def IsFrameFam (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, IsUnit (fr τ) ∧ (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

def kAt (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : Formalism.REAL.KG e) :
    GA D V :=
  atTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P)

def HasTypeAt (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ : GA D V → ℂ) : Prop :=
  ∀ x : GA D V, (fun k => φ (x * kAt θ V τ e P k)) ∈ coeffSpan ρ

def forms (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)]
    [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) :
    Set (GA D V → ℂ) :=
  {φ | IsAutFunSm θ V φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ ∀ τ k, gelf θ V τ k φ = c τ k • φ}

end AutFin


open AutFin in
def HarishChandraFinite : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) →
  ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsFrameFam V ε fr →
  ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) →
  ∀ c : D.what₂.Tau → ℕ → ℂ,
    FiniteDimensional ℂ (Submodule.span ℂ (forms θ V U ε fr ρ c))

namespace AutFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem conj_mem_UH {n : ℕ} {e : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm e * P = G) (k : Formalism.REAL.KG e) :
    P⁻¹ * Formalism.REAL.toMK k * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : (Formalism.REAL.toMK k)ᴴ * Formalism.REAL.Jm e * Formalism.REAL.toMK k = Formalism.REAL.Jm e := (k : Formalism.REAL.UJ e).2
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  change (P⁻¹ * Formalism.REAL.toMK k * P)ᴴ * G * (P⁻¹ * Formalism.REAL.toMK k * P) = G
  calc (P⁻¹ * Formalism.REAL.toMK k * P)ᴴ * G * (P⁻¹ * Formalism.REAL.toMK k * P)
      = Pᴴ * ((Formalism.REAL.toMK k)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm e * (P * P⁻¹) * Formalism.REAL.toMK k) * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]


open Classical in
theorem isAtTau_kAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k : Formalism.REAL.KG e) : IsAtTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P) (kAt θ V τ e P k) := by
  obtain ⟨g, hg, h1⟩ := ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.1
    (Function.update (fun _ => 1) τ (P⁻¹ * Formalism.REAL.toMK k * P)) (fun τ' => by
      by_cases c : τ' = τ
      · subst c; rw [Function.update_self]; exact conj_mem_UH hP h k
      · rw [Function.update_of_ne c]
        change (1 : Matrix _ _ ℂ)ᴴ * _ * 1 = _
        rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  have hex : ∃ x, IsAtTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P) x :=
    ⟨g, hg, by rw [h1, Function.update_self], fun τ' c => by rw [h1, Function.update_of_ne c]⟩
  rw [kAt, atTau, dite_eq_left hex]
  exact hex.choose_spec

theorem hasTypeAt_of_map (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (T : W →ₗ[ℂ] (GA D V → ℂ))
    (hT : ∀ k w, T (ρ k w) = rTr V (kAt θ V τ e P k) (T w)) (w : W) : HasTypeAt θ V τ e P ρ (T w) := fun x =>
  Submodule.subset_span ⟨(LinearMap.proj x).comp T, w, funext fun k => (congrFun (hT k w) x).symm⟩

theorem exists_isFrameFam (hV : V.SigOK) : ∃ ε fr, IsFrameFam V ε fr := by
  have key : ∀ τ, ∃ (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsUnit P ∧ Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ := by
    intro τ
    obtain ⟨hpq, ⟨A, hA⟩, hB⟩ := GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D τ))
    obtain ⟨B, hAB, -⟩ := hB A hA
    let s := (finSumFinEquiv.trans (finCongr hpq)).symm
    have hJ : Formalism.REAL.Jm (fun i => (s i).isLeft) = (Formalism.UG.Jpq _ _).submatrix s s := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Formalism.REAL.Jm, diagonal_apply_eq, submatrix_apply]
        rcases s i with a | a <;> simp [Formalism.UG.Jpq]
      · have hs : s i ≠ s j := fun h => hij (s.injective h)
        rw [Formalism.REAL.Jm, diagonal_apply_ne _ hij, submatrix_apply]
        revert hs
        rcases s i with a | a <;> rcases s j with b | b <;> simp +contextual [Formalism.UG.Jpq, Matrix.one_apply]
    refine ⟨fun i => (s i).isLeft, A.submatrix s id, ?_, ?_⟩
    · refine IsUnit.of_mul_eq_one (B.submatrix id s) ?_
      rw [← submatrix_mul A B s id s Function.bijective_id, hAB, submatrix_one_equiv]
    · rw [hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA]
      rfl
  choose ε fr h using key
  exact ⟨ε, fr, h⟩

end AutFin

end GlobalTheory.Published

end
end

