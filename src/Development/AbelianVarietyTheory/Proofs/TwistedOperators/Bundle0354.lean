module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

def complId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (AE D) :=
  AddSubgroup.closure {s | ∃ α ∈ intAf D.host.F, ∃ a ∈ 𝔠, s = pairA D.host.F 0 α ⊗ₜ[D.host.F] a}

theorem tmul_mem_complId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {a : D.host.E} (ha : a ∈ 𝔠) : pairA D.host.F 0 α ⊗ₜ[D.host.F] a ∈ complId 𝔠 :=
  AddSubgroup.subset_closure ⟨α, hα, a, ha, rfl⟩

end GlobalTheory.XCharBF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransformIntegral
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

section Lin

open Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

theorem baseChange_mem {K K' M : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup M] [Module K M]
    (φ : M →ₗ[K] M) (V : Submodule K M) (h : ∀ x ∈ V, φ x ∈ V) : ∀ x ∈ V.baseChange K', φ.baseChange K' x ∈ V.baseChange K' := by
  intro x hx
  rw [Submodule.baseChange_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ v, h v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem span_mem {K' M : Type} [Field K'] [AddCommGroup M] [Module K' M] (O : ValuationSubring K')
    (φ : M →ₗ[K'] M) (S : Set M) (h : ∀ x ∈ S, φ x ∈ S) : ∀ x ∈ Submodule.span O S, φ x ∈ Submodule.span O S := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : φ (a • x) = a • φ x := φ.map_smul (a : K') x
    rw [this]; exact Submodule.smul_mem _ _ hx

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

theorem keeps_of (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK)
    (hs : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1)
    (hr : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL) : Keeps Φ la hL hW := by
  have he : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL := fun eC => by
    ext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FormsL.eOp, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun g _ => congrArg _ (LinearMap.congr_fun (hr g) x)
  have ht : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam := fun J lam x hx p => by
    have h1 : Φ.ρ p (hL x) = hL (Φ.ρ p x) := (LinearMap.congr_fun (hr p) x).symm
    rw [h1, hx p, map_smul]
  have hg : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC := by
    rintro eC _ ⟨x, rfl⟩
    exact ⟨hL x, (LinearMap.congr_fun (he eC) x).symm⟩
  have hw : ∀ (J : Subgroup G) (lam : J →* LLˣ) (eC : G → LL), ∀ x ∈ Φ.Wgood J lam eC, hL x ∈ Φ.Wgood J lam eC :=
    fun J lam eC x hx => ⟨ht J lam x hx.1, hg eC x hx.2⟩
  refine ⟨hs, hr, he, ht, hg, fun K' _ _ O _ => ?_, fun K' _ _ _ _ O _ => ?_⟩
  · have h1 : ∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O := by
      refine span_mem O _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨hL f, hW f f.2⟩, hs f hf, rfl⟩
    have h2 : ∀ V : Submodule LL WL, (∀ x ∈ V, hL x ∈ V) →
        ∀ x ∈ latKIn Φ la O V, (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O V := fun V hV x hx =>
      ⟨h1 x hx.1, baseChange_mem (resW Φ hL hW) _ (fun y hy => hV _ hy) x hx.2⟩
    exact ⟨h1, fun J lam => ⟨h2 _ (ht J lam), fun eC => h2 _ (hw J lam eC)⟩⟩
  · have h1 : ∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O := by
      refine span_mem O _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨hL f, hW f f.2⟩, hs f hf, rfl⟩
    have h2 : ∀ V : Submodule LL WL, (∀ x ∈ V, hL x ∈ V) →
        ∀ x ∈ latLIn Φ la O V, hL.baseChange K' x ∈ latLIn Φ la O V := fun V hV x hx =>
      ⟨h1 x hx.1, baseChange_mem hL _ hV x hx.2⟩
    exact ⟨h1, fun J lam => ⟨h2 _ (ht J lam), fun eC => h2 _ (hw J lam eC)⟩⟩

end Lin

section Grp

open Formalism.IndefR.Bridge GlobalTheory.HeckeModel

theorem exists_local_isDC {G : Type} [Group G] {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC J x A) : ∃ A₀, IsDC K x A₀ := by
  classical
  have hex : ∀ a : G, ∃ b : G, a ∈ A → (∃ k ∈ K, b = k * x) ∧ b⁻¹ * a ∈ J := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
      refine ⟨a₁ * x, fun _ => ⟨⟨a₁, ha₁, rfl⟩, ?_⟩⟩
      have : (a₁ * x)⁻¹ * ((k₁ : G) * x * k₂) = b₁ * k₂ := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem hb₁ k₂.2
    · exact ⟨1, fun h => absurd h ha⟩
  choose f hf using hex
  refine ⟨A.image f, fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, hk, e⟩ := (hf a ha).1
    exact ⟨⟨k, hk⟩, 1, by simp [e]⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, hag⟩, hu⟩ := hA.2 ((k₁ : G) * x * k₂) ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
    refine ⟨f a, ⟨Finset.mem_image_of_mem f ha, ?_⟩, ?_⟩
    · obtain ⟨k, hk, e⟩ := (hf a ha).1
      refine (hs.mem _ ?_).1 ?_
      · rw [e]
        exact L.mul_mem (L.inv_mem (L.mul_mem (hs.le hk) hx)) (L.mul_mem (L.mul_mem (hs.le k₁.2) hx) (hs.le k₂.2))
      · have := J.mul_mem (hf a ha).2 hag
        simpa [mul_assoc] using this
    · rintro b ⟨hb, hbg⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hb
      rw [hu a' ⟨ha', ?_⟩]
      have := J.mul_mem (J.inv_mem (hf a' ha').2) (hs.le' hbg)
      simpa [mul_assoc] using this

end Grp

section Geo

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem nval_nonneg_of_int {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] (e : ℕ) (a : V) : 0 ≤ nval V e (algebraMap V K' a) := by
  by_cases h0 : algebraMap V K' a = 0
  · rw [h0, nval_zero]; exact le_top
  rw [nval_of_ne h0]
  have hne : valV V (algebraMap V K' a) ≠ 0 := valV_ne_zero h0
  have hle : valV V (algebraMap V K' a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
  have hlog : WithZero.log (valV V (algebraMap V K' a)) ≤ 0 := by
    have := (WithZero.log_le_log hne one_ne_zero).2 hle
    simpa using this
  have hv : (0 : ℝ) ≤ (vV V (algebraMap V K' a) : ℝ) := by
    have : (0 : ℤ) ≤ vV V (algebraMap V K' a) := by simp only [vV]; omega
    exact_mod_cast this
  exact EReal.coe_nonneg.2 (div_nonneg hv (Nat.cast_nonneg e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transform_integral (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeValueInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c))
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {P : Ideal (𝓞 E)} {p i : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p) (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i)
    {la : HeightOneSpectrum (𝓞 c.F)} (hp : (p : 𝓞 c.F) ∉ la.asIdeal) {s : c.F} (hs : la.valuation c.F s ≤ 1)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c a n) (hg : g ∈ sec Xo c a n)
    (hr : HkRel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) s f g)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v g := by
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  show 0 ≤ nval T.V e (evI y g)
  letI := io.toAlgebra
  let Ω := AlgebraicClosure T.Fr
  letI : Algebra c.F Ω := ((algebraMap T.Fr Ω).comp io).toAlgebra
  let k : T.Fr →ₐ[c.F] Ω := ⟨algebraMap T.Fr Ω, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ k y.1
  have e1 : evR Xo c g z = k (evI y g) := evR_frMap hWD g hg.1 k y.1 y.2.1 z hz
  have e2 := hr Ω z
  haveI := hF Ω z
  set x := hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) f z with hx
  have halg : (letI := k.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr Ω) := by
    have hA : k.toRingHom.toAlgebra = (inferInstance : Algebra T.Fr Ω) := Algebra.algebra_ext _ _ fun _ => rfl
    rw [hA]
    exact AlgebraicClosure.isAlgebraic T.Fr
  have hint : IsIntegral T.V x := by
    rw [hx, hkVal]
    refine finsum_induction (IsIntegral T.V) isIntegral_zero (fun _ _ => IsIntegral.add) fun C => ?_
    unfold hkTerm
    split_ifs with h
    · exact (hI la P p i hP hp T io e ho y hy trivial Ω k halg z hz C _ h.choose_spec).2
        a n f hf h0
    · exact isIntegral_zero
  by_cases hs0 : s = 0
  · have : evI y g = 0 := by
      apply k.toRingHom.injective
      show k _ = k _
      rw [← e1, map_zero]
      refine e2.trans ?_
      rw [hs0, map_zero, zero_mul]
    rw [this, nval_zero]; exact le_top
  have e3 : algebraMap T.Fr Ω ((io s)⁻¹ * evI y g) = x := by
    rw [map_mul, map_inv₀]
    show (algebraMap c.F Ω s)⁻¹ * k _ = x
    rw [← e1]
    have : evR Xo c g z = algebraMap c.F Ω s * x := e2
    rw [this, inv_mul_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [← e3, isIntegral_algebraMap_iff ] at hint
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have e4 : evI y g = io s * algebraMap T.V T.Fr w := by
    rw [hw, mul_inv_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [e4, nval_smul ho hs0]
  refine add_nonneg ?_ (nval_nonneg_of_int e w)
  have h5 := (WithZero.log_le_log ((la.valuation c.F).ne_zero_iff.2 hs0) one_ne_zero).2 hs
  rw [WithZero.log_one] at h5
  have : (0 : ℤ) ≤ vLa la s := by unfold vLa; omega
  exact_mod_cast this

end Geo

end GlobalTheory.HeckeSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedMatrixCoefficientInAdaptedFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

lemma inUJ_mul' {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) : a * b ∈ Formalism.MainNotions.S.UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem mco_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  intro D V S M τ B g v₀ hB hBg hg
  set F := M.fr τ with hFdef
  set J := Formalism.REAL.Jm (M.ε τ) with hJdef
  set G := gramAt D V τ with hGdef
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp (M.fr_unit τ)
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hFg : Fᴴ * J * F = G := M.fr_gram τ
  have hg' : gᴴ * J * g = J := hg
  have hBH : (B⁻¹)ᴴ * Bᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv B hBd, conjTranspose_one]
  have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv F hFd, conjTranspose_one]
  have hBinv : (B⁻¹)ᴴ * G * B⁻¹ = J := by
    rw [← hBg]
    calc (B⁻¹)ᴴ * (Bᴴ * J * B) * B⁻¹ = ((B⁻¹)ᴴ * Bᴴ) * J * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hBH, Matrix.mul_nonsing_inv B hBd]; simp
  have hFinv : (F⁻¹)ᴴ * G * F⁻¹ = J := by
    rw [← hFg]
    calc (F⁻¹)ᴴ * (Fᴴ * J * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * J * (F * F⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hFH, Matrix.mul_nonsing_inv F hFd]; simp
  refine ⟨?_, ?_⟩
  · show (B⁻¹ * g * F)ᴴ * G * (B⁻¹ * g * F) = G
    rw [conjTranspose_mul, conjTranspose_mul]
    calc Fᴴ * (gᴴ * (B⁻¹)ᴴ) * G * (B⁻¹ * g * F) = Fᴴ * (gᴴ * ((B⁻¹)ᴴ * G * B⁻¹) * g) * F := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hBinv, hg', hFg]
  · intro x hx
    have hx' : xᴴ * G * x = G := hx
    obtain ⟨⟨_, hmul⟩, hiso, _⟩ := (M.ds τ).2.2.1
    have hk : F * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * B⁻¹)ᴴ * J * (F * B⁻¹) = J
      rw [conjTranspose_mul]
      calc (B⁻¹)ᴴ * Fᴴ * J * (F * B⁻¹) = (B⁻¹)ᴴ * (Fᴴ * J * F) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hBinv]
    have hy : B * x * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (B * x * B⁻¹)ᴴ * J * (B * x * B⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (B⁻¹)ᴴ * (xᴴ * Bᴴ) * J * (B * x * B⁻¹) = (B⁻¹)ᴴ * (xᴴ * (Bᴴ * J * B) * x) * B⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hBg, hx', hBinv]
    have hz : F * x * F⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * x * F⁻¹)ᴴ * J * (F * x * F⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (F⁻¹)ᴴ * (xᴴ * Fᴴ) * J * (F * x * F⁻¹) = (F⁻¹)ᴴ * (xᴴ * (Fᴴ * J * F) * x) * F⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hx', hFinv]
    have e1 : F * (B⁻¹ * g * F) * F⁻¹ = F * B⁻¹ * g := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFd, Matrix.mul_one]
    have e2 : F * x * F⁻¹ * (F * B⁻¹ * g) = F * B⁻¹ * (B * x * B⁻¹ * g) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left F _ hFd,
        Matrix.nonsing_inv_mul_cancel_left B _ hBd]
    have hkg := inUJ_mul' hk hg
    have hyg := inUJ_mul' hy hg
    unfold mco DSModel.rep
    rw [← hFdef, e1, ← ContinuousLinearMap.comp_apply, ← hmul _ hz _ hkg, e2,
      hmul _ hk _ hyg, hmul _ hk _ hg, hmul _ hy _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    let L : M.H τ →ₗᵢ[ℂ] M.H τ := ⟨(M.σ τ (F * B⁻¹)).toLinearMap, hiso _ hk⟩
    exact L.inner_map_map _ _

end GlobalTheory.PackLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransversalCoefficientDecayAtRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

theorem farClause : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ B c₁ lam q Cb k hB hBJ hBz hk hmco hint hInt hc₁ hlam hCb hb g hg
  set z : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hz
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hg' : B * g * B⁻¹ ∈ Formalism.MainNotions.S.UJset (MP.ε τ) := by
    have hg0 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    show (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹) = Formalism.REAL.Jm (MP.ε τ)
    have hBi : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBinv', Matrix.conjTranspose_one]
    calc (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹)
        = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * g) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * B⁻¹ := by rw [hBJ, hg0]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm (MP.ε τ) * (B * B⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (MP.ε τ) := by rw [hBi, hBinv']; simp
  obtain ⟨hbI, hbB⟩ := hb _ hg'
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ :=
    fun x => ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ with hF
  have hfun : (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      = fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := funext (hmco g hg)
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint F).mpr hbI
  ·
    have hcol : B *ᵥ (g *ᵥ z) = fun a => (B * g * B⁻¹) a (e none) := by
      funext a
      have : (B * g * B⁻¹) *ᵥ (B *ᵥ z) = B *ᵥ (g *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (B * g), hBinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      rw [← this, hBz]
      simp [Matrix.mulVec_single]
    set L := eu (B *ᵥ (g *ᵥ z)) with hL
    have hLdef : L = Real.sqrt (∑ a, ‖(B * g * B⁻¹) a (e none)‖ ^ 2) := by
      rw [hL, hcol]; rfl
    have hI : (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)))
        = lam * ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) := by
      have := hInt (fun x => ‖F x‖)
      rw [smul_eq_mul] at this
      rw [← this]
      congr 1
      funext u
      rw [hmco g hg u]
    have hL0 : 0 ≤ L := Real.sqrt_nonneg _
    have hexp : 2 * V.rank + 5 = 2 * k + 7 := by omega
    have hnorm : ‖((lam * c₁ : ℝ) : ℂ)‖ = lam * c₁ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    rw [hI, hnorm, hexp]
    have hInn : 0 ≤ ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) :=
      integral_nonneg (fun _ => norm_nonneg _)
    rcases hL0.lt_or_eq with hLp | hLz
    · have hbB' : ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))
          ≤ c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7)) := by rw [hLdef]; exact hbB
      have hpow : L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7) = 1 := by
        rw [Real.rpow_neg hL0, ← Real.rpow_natCast]
        push_cast
        exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hLp _).ne'
      have hLn : 0 ≤ L ^ (2 * k + 7) := pow_nonneg hL0 _
      calc lam * (∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) * L ^ (2 * k + 7)
          ≤ lam * (c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7))) * L ^ (2 * k + 7) := by
            gcongr
        _ = lam * c₁ * Cb * (L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7)) := by ring
        _ = lam * c₁ * Cb := by rw [hpow, mul_one]
        _ ≤ lam * c₁ * Real.exp q := by
            exact mul_le_mul_of_nonneg_left hCb (mul_pos hlam hc₁).le
        _ = Real.exp q * (lam * c₁) := by ring
    · rw [← hLz, zero_pow (by omega), mul_zero]
      exact mul_nonneg (Real.exp_pos q).le (mul_pos hlam hc₁).le

end GlobalTheory.PackLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLeftIntertwinesHeisenbergDerivativeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (g : UA σ X.J) (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) → ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1 (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left <;> assumption)
end

