module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay

variable {D : D7}

def quotHeight (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : NNReal :=
  ⨅ γ : GQ V, height θ V ((γ : GA D V) * g)

def IsRapidDecay (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g : GA D V, ‖φ g‖ * (quotHeight θ V g : ℝ) ^ N ≤ C

end GlobalTheory.CuspDecay

namespace GlobalTheory.Published

def CuspRapidDecay : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (e : LieInf V → GA D V), IsExpFam θ V e →
      ∀ φ : GA D V → ℂ, IsAutFun V φ → IsSmoothInf V e φ → IsUnifModerate θ V e φ → IsCuspFun V φ →
        GlobalTheory.CuspDecay.IsRapidDecay θ V φ

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_le (g : GA D V) {γ : GA D V} (hγ : γ ∈ GQ V) : quotHeight θ V g ≤ height θ V (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : GQ V)

theorem one_le_quotHeight (g : GA D V) : 1 ≤ quotHeight θ V g :=
  le_ciInf fun _ => one_le_height θ V _

theorem exists_height_le (g : GA D V) : ∃ γ ∈ GQ V, height θ V (γ * g) ≤ 2 * quotHeight θ V g := by
  have h : quotHeight θ V g < 2 * quotHeight θ V g :=
    lt_mul_of_one_lt_left (zero_lt_one.trans_le (one_le_quotHeight g)) one_lt_two
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h
  exact ⟨γ, γ.2, hγ.le⟩

theorem IsRapidDecay.bounded {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem IsRapidDecay.mul_bounded {φ ψ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hψ : ∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) {N : ℕ} {C : ℝ} (hC : ∀ g, ‖ψ g‖ ≤ C * (height θ V g : ℝ) ^ N) :
    ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨C', hC'⟩ := h N
  refine ⟨|C| * 2 ^ N * C', fun g => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖ψ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N := by
    rw [← hψ γ hγ g]
    exact (hC _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))
  calc ‖ψ g‖ * ‖φ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N * ‖φ g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖φ g‖ * (quotHeight θ V g : ℝ) ^ N) := by rw [mul_pow]; ring
    _ ≤ |C| * 2 ^ N * C' := mul_le_mul_of_nonneg_left (hC' g) (by positivity)

theorem exists_norm_le_height_pow (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ g‖ ≤ C * (height θ V g : ℝ) ^ N := by
  obtain ⟨-, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨-, -, N, hN⟩ := h2 e he
  obtain ⟨C, hC⟩ := hN []
  exact ⟨N, C, hC⟩

theorem isRapidDecay_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : IsRapidDecay θ V φ := by
  obtain ⟨ha, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨hs, -, hg⟩ := h2 e he
  exact hP D θ hθ V e he φ ha hs hg hc

theorem bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C :=
  (isRapidDecay_of_cuspForm hP hθ h hc).bounded

theorem mul_bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {ψ φ : GA D V → ℂ}
    (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨N, C, hC⟩ := exists_norm_le_height_pow hθ hψ
  exact (isRapidDecay_of_cuspForm hP hθ h hc).mul_bounded hψ.left hC

theorem measure_lt_top (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  exact hV D.host.F D.host.E D.sp.cm.sig h1 V.rank V.gram (h2 V) μ hμ 𝓕 h𝓕

theorem integrableOn_star_mul (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hθ : IsInfFam θ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {ψ φ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IntegrableOn (fun g => star (ψ g) * φ g) 𝓕 μ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := mul_bounded_of_cuspForm hP hθ hψ h hc
  refine Measure.integrableOn_of_bounded (M := B) (measure_lt_top hV V μ 𝓕 hμ h𝓕).ne
    ((hψ.cont.star.mul h.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hB g

end GlobalTheory.CuspDecay

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

abbrev cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : IrrRep (GL (Fin n) k)) : IrrGL (k := k) := ⟨n, π.cl⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def sumList (l : List (WD h)) : WD h := l.foldr WD.lpSum (WD.lpZero (h := h))

def IsIrrWD (x : WD h) : Prop := ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧ a.ρ.IsIrreducible

def IsTameWD (x : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧
    ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1

structure Laws (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop where

  bij : Function.Bijective rc

  dim : ∀ x, (rc x).lpDim = x.1

  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (τ : IrrRep (GL (Fin m) (w.adicCompletion E))),
      IsCuspidal π.ρ → HasPairEps ψ π.ρ τ.ρ (ε E w h ψ ((rc (cls π)).lpChar (rc (cls τ))))

  twist : ∀ x χ hχ, rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))

  central : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π'.ρ.Equiv (contra π.ρ)) →
    rc (cls π') = (rc (cls π)).lpDual

  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)

  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep →
    rc x = sumList (l.map fun Δ =>
      ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))

  det : ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) =
    sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j))

  prod : ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E)))
    (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) →
    rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ))

  supp : ∀ (x : IrrGL (k := w.adicCompletion E)) s, HasSupport x.rep s →
    ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod

  sph : ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr

  sat : ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹)

  depth : ∀ x : IrrGL (k := w.adicCompletion E),
    fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x)

variable (h) in
def IsRec (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A), IsDeligneEps ε ∧ Laws a ha ε rc

def FieldCompatible {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h') : Prop :=
  ∀ (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
    (∀ z, φ z ∈ A' ↔ z ∈ A) → (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → Continuous i →
    (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) →
    ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (π' : IrrRep (GL (Fin n) (w'.adicCompletion E')))
      (e : π.V ≃ₗ[ℂ] π'.V), (∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) →
      ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = rc (cls π) ∧ WD.mk b' = rc' (cls π') ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ'

end GlobalTheory.LocLanglands

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalLanglandsGL : Prop :=
  (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃! rc : IrrGL (k := w.adicCompletion E) → WD h, IsRec h rc) ∧
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h'),
    IsRec h rc → IsRec h' rc' → FieldCompatible rc rc'

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpOfChar (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) :
    x.lpChar (WD.lpOfChar h ξ hξ) = x.lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpOfChar, WD.lpChar_mk, WD.lpTwist_mk]
  refine WD.sound ⟨(TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ _), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp [smul_smul, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp [WDRep.twist]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]


variable (w) in
theorem resCard_eq_normV : resCard (w.adicCompletion E) = normV w := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : resCard (w.adicCompletion E) = Formalism.UG.qV E w := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  simpa only [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq

variable {a : Weil h →* (w.adicCompletion E)ˣ}

theorem IsLocalArtin.unrChar_comp (ha : IsLocalArtin h a) (c : ℂˣ) :
    (SmGL.unrChar (w.adicCompletion E) c).comp a = WeilDeligne.unrChar h c⁻¹ := by
  refine MonoidHom.ext fun σ => ?_
  rw [MonoidHom.comp_apply, SmGL.unrChar_apply, ha.ord_eq, WeilDeligne.unrChar_apply, _root_.zpow_neg, _root_.inv_zpow]

theorem IsLocalArtin.absPow_comp (ha : IsLocalArtin h a) (s : ℝ) :
    (absPow (w.adicCompletion E) s).comp a = WeilDeligne.unrChar h (qPow w s) := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [MonoidHom.comp_apply, val_absPow_ofReal, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV,
    WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, coe_qPow, ← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm,
    Real.rpow_mul hq, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_cpow hq, Complex.ofReal_natCast]

variable {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem Laws.tw_eq (H : Laws a ha ε rc) (x : IrrGL (k := w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  rw [H.twist, H.one, lpChar_lpOfChar]

theorem Laws.nu_eq (H : Laws a ha ε rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.tw_eq, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem Laws.eq_iff (H : Laws a ha ε rc) {n : ℕ} (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))) :
    rc (cls π) = rc (cls π') ↔ Nonempty (π.ρ.Equiv π'.ρ) :=
  H.bij.1.eq_iff.trans (IrrGL.of_eq_of (π := π.ρ) (σ := π'.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π'.smooth)
    (hi' := π'.irr))

end GlobalTheory.LocLanglands
end
end

