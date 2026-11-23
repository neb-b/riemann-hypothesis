module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

section FrLev

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem frDiv_mem_GLint (p p' : DecoF E n ST SG Q) (hN : p.deco.1.N = p'.deco.1.N) (P : Q) :
    (p.fr P)⁻¹ * p'.fr P ∈ GLint E n P.1 := by
  intro v
  have h1 := p.2 P (((p.fr P)⁻¹ * p'.fr P) v)
  have h2 := p'.2 P v
  have e : p.1.2 P (((p.fr P)⁻¹ * p'.fr P) v) = p'.fr P v := by
    show p.fr P ((p.fr P).symm (p'.fr P v)) = p'.fr P v
    exact LinearEquiv.apply_symm_apply _ _
  rw [e] at h1
  rw [← h1, ← h2]
  show p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N ↔ p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p'.deco.1.N
  rw [hN]

theorem rhoP_eq_fr {g : GL (Fin n) (AfE F E)} {q : DecoF E n ST SG Q} (hq : IsPtOf hc g q) (P : Q) :
    rhoP F P.1 g = bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (q.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (q.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [hq.fr P i j, qsp_toGLm_apply]

end FrLev

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TopCh

theorem mem_topU_iff : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ U k t y x p p' hk hkP ht hU hp hp'
  set g := y * (k * t) with hg
  set z := (k * t)⁻¹ * x * (k * t) with hz
  have hgz : y * x * (k * t) = g * z := by rw [hg, hz]; group
  rw [hgz] at hp'
  have step := fun h : GLG (E := E) (n := n) (SG := SG) => ((GlobalTheory.T.isPtOf_mul_J0_decoration F E hc n ST SG Q g z p p' h).1 hp hp')
  have htU : t ∈ UAd hc n := principal_le_adelic_unitary hc n ST SG ht
  have hktU : k * t ∈ UAd hc n := mul_mem hk htU
  have hgU : g ∈ UAd hc n := hp.uni
  have hgzU : g * z ∈ UAd hc n := hp'.uni
  have hyU : y ∈ UAd hc n := by
    have e : y = g * (k * t)⁻¹ := by rw [hg]; group
    rw [e]; exact mul_mem hgU (inv_mem hktU)
  have hxU : x ∈ UAd hc n := by
    have e : x = y⁻¹ * (g * z) * (k * t)⁻¹ := by rw [hg, hz]; group
    rw [e]; exact mul_mem (mul_mem (inv_mem hyU) hgzU) (inv_mem hktU)
  have hU' : x ∈ U ↔ z ∈ levU hc n ST SG Λ.grp := by
    rw [hU x hxU]
    have e : k⁻¹ * x * k = t * z * t⁻¹ := by rw [hz]; group
    rw [e]
    have htL : t ∈ levU hc n ST SG Λ.grp := kOne_le_unipotentLevel hc n ST SG _ ht
    constructor
    · intro h
      have h2 := mul_mem (mul_mem (inv_mem htL) h) htL
      have e2 : t⁻¹ * (t * z * t⁻¹) * t = z := by group
      rwa [e2] at h2
    · intro h
      exact mul_mem (mul_mem htL h) (inv_mem htL)
  have hT : ∀ P : Q, rhoT F P.1 t x = rhoP F P.1 z := by
    intro P
    show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 z
    rw [hz]
    simp only [map_mul, map_inv, hkP P, one_mul, inv_inv, _root_.mul_inv_rev, inv_one, mul_one]
  have hZ : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoP F P.1 z = iotaP P.1 ⟨_, frDiv_mem_GLint p p' hN P⟩ := by
    intro hN P
    have e : rhoP F P.1 z = (rhoP F P.1 g)⁻¹ * rhoP F P.1 (g * z) := by
      rw [← map_inv, ← map_mul, inv_mul_cancel_left]
    rw [e, rhoP_eq_fr hp P, rhoP_eq_fr hp' P, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hL : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) ↔ (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := by
    intro hN P
    rw [hT P, hZ hN P]
    exact qbU_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P)
      (hΘ P) _
  have hNs : ∀ h : GLG (E := E) (n := n) (SG := SG), p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco → p.deco.1.N = p'.deco.1.N := by
    intro h e
    rw [e]
    show p.deco.1.N = Formalism.HermitianLatticesTheory.gmap (1 : Sp E n ≃ₗ[E] Sp E n) p.deco.1.N
    exact (Formalism.L2.Col.gmap_one _).symm
  constructor
  · intro hx
    obtain ⟨hz0, hzr⟩ := (mem_levU hc n ST SG _).1 (hU'.1 hx.1)
    let h : Λ.grp := ⟨(redG hc n ST SG ⟨z, hz0⟩)⁻¹, inv_mem hzr⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco := (step h.1).1 ⟨hz0, (inv_inv _).symm⟩
    have hN := hNs h.1 hdeco
    have hc' : ∀ P : Q, (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := fun P =>
      (hL hN P).1 (rhoT_mem hx P)
    let θ : Θ.grp := ⟨fun P => (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1))⁻¹, fun P _ => inv_mem (hc' P)⟩
    refine ⟨h, θ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hdeco.symm
    · funext P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) = p'.fr P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((p.fr P)⁻¹ * p'.fr P) = p'.fr P
      rw [one_mul, mul_inv_cancel_left]
  · rintro ⟨h, θ, hθ⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco := by rw [← hθ]; rfl
    obtain ⟨hz0, hzr⟩ := (step h.1).2 hdeco
    have hN := hNs h.1 hdeco
    refine ⟨hU'.2 ((mem_levU hc n ST SG _).2 ⟨hz0, by rw [hzr]; exact inv_mem h.2⟩), ?_⟩
    refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_comap.2 ((hL hN P).2 ?_)
    have hfr : p'.fr P = p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) := by
      rw [← hθ]
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * _ = _
      rw [one_mul]
    have e : (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) = (θ.1 P)⁻¹ := by
      apply Subtype.ext
      show (p.fr P)⁻¹ * p'.fr P = _
      rw [hfr, inv_mul_cancel_left]
    rw [e]
    exact inv_mem (θ.2 P (Set.mem_univ _))

end GlobalTheory.Mem.Col2.TopCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

theorem mem_of_inclE_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E),
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w →
      α ∈ w.asIdeal := by
  intro D X w α hα
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE with he
  set Wx : Ideal (𝓞 X.B.I.E) := w.asIdeal.comap (e : 𝓞 X.B.I.E →+* 𝓞 D.host.E) with hWx
  have hWx0 : Wx ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    rw [eq_bot_iff]
    intro b hb
    have : e.symm b ∈ Wx := by
      show e (e.symm b) ∈ w.asIdeal
      simpa using hb
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    simpa using congrArg e this

  have key : ∀ c ∈ GlobalTheory.Mem.SymChar.wInt X w,
      ∃ h : c ∈ Formalism.L2.Herm.intAf X.B.I.F X.B.I.E,
        (⟨c, h⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) ∈ Formalism.L2.DIV.idS X.B.I.F Wx := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
      refine ⟨(Formalism.L2.DIV.oToS X.B.I.F X.B.I.E a).2, ?_⟩
      have ha : a ∈ Wx := by
        show e a ∈ w.asIdeal
        have : e a = b := Subtype.ext hab
        rw [this]; exact hb
      exact Ideal.mem_map_of_mem _ ha
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨add_mem hx1 hy1, add_mem hx2 hy2⟩
    | smul r x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨mul_mem r.2 hx1, ?_⟩
      have : (⟨r • x, mul_mem r.2 hx1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = ⟨r.1, r.2⟩ * ⟨x, hx1⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ hx2
  obtain ⟨h1, h2⟩ := key _ hα
  set c : 𝓞 X.B.I.E := e.symm α with hc
  have hoc : (⟨_, h1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c := rfl
  rw [hoc] at h2
  have hz : Formalism.L2.DIV.cmpS X.B.I.F Wx (Ideal.Quotient.mk Wx c) = Formalism.L2.DIV.cmpS X.B.I.F Wx 0 := by
    rw [map_zero]
    show Ideal.Quotient.mk _ (Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  have hcW : c ∈ Wx := Ideal.Quotient.eq_zero_iff_mem.1 (Formalism.L2.DIV.cmpS_inj Wx hWx0 hz)
  have : e c = α := by rw [hc]; exact e.apply_symm_apply α
  rw [← this]
  exact hcW

end GlobalTheory.Mem.SymChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

theorem om_sizes_le_poR (f r L lE lh lN lhs lG lr ld rk ldeg : ℝ) (hf : 8 ≤ f) (hr : 62 ≤ r) (hL : 4 ≤ L)
    (hlf : Real.log f ≤ L) (hE0 : 0 ≤ lE) (hE : lE ≤ 2 * L)
    (hh : lh ≤ f * lE + 2 * f * Real.log (1 + f * lE)) (hN : lN ≤ 20 * L + 2) (hs0 : 0 ≤ lhs)
    (hs : lhs ≤ lh + 2 * f * lN) (hG : lG ≤ f * r ^ 2 * (18 * L + 2)) (hr' : lr ≤ lG + 24)
    (hd : ld ≤ 4 * L) (hk : rk ≤ 2 * f) (hdeg : ldeg ≤ 1 + L) :
    (ld + 20) + (ldeg + lhs) + lr + (ldeg + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L ∧
    (3 * ld + 20) + (lE + lN + lhs) + lr + (lE + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : Real.log (1 + f * lE) ≤ Real.log (f * (3 * L)) := Real.log_le_log (by linarith) (by nlinarith)
  have h2 : Real.log (f * (3 * L)) = Real.log f + Real.log (3 * L) := Real.log_mul hf0.ne' (by positivity)
  have h3 : Real.log (3 * L) ≤ 3 * L - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * Real.log (1 + f * lE) ≤ 2 * f * (4 * L) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : 2 * f * lN ≤ 2 * f * (20 * L + 2) := mul_le_mul_of_nonneg_left hN (by positivity)
  have h8 : 4 * f ≤ f * L := by nlinarith
  have h9 : lhs ≤ 51 * (f * L) := by nlinarith
  have h10 : (rk + 2) * lhs ≤ (2 * f + 2) * (51 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) hs0 |>.trans (mul_le_mul_of_nonneg_left h9 (by linarith))
  have h11 : f * r ^ 2 * 2 ≤ f * r ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h12 : 8 * (f * L) ≤ f * (f * L) := mul_le_mul_of_nonneg_right hf (by positivity)
  have h13 : f * (f * L) = f ^ 2 * L := by ring
  constructor <;> nlinarith

theorem sz_Om_poR : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  intro hR P δ L hL
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  obtain ⟨K, _, _, hK2, hKd, -, hKE, -, hdeg⟩ := exists_hostK P.R P.host
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
  have hrd : lE ≤ 2 * L := hlE' ▸ hL.rd

  have hd : Real.log (P.host.d : ℝ) ≤ 4 * L := by
    obtain ⟨_, -, h⟩ := sz_mono_and_of_le.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2, hKd] at h'
    push_cast at h'
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h'
    linarith

  have hM' := _root_.GlobalTheory.Mem.Fld.TorsionSize.sz_discField hR P δ
  obtain ⟨hdeg_le, hray⟩ := _root_.GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz P.host.E P.host.φ₀ (modulus P) δ.ray δ.isRay (modulus_ne_zero P)
  have hcyc : Sz (cycField (rootOrder P)) (Real.log (rootOrder P)) (Real.log (rootOrder P)) :=
    sz_adjoin_rootOfUnity _ (Nat.pos_of_ne_zero (rootOrder_ne_zero P))
  have hV : Sz δ.V _ _ := _root_.GlobalTheory.FieldSize.sz_kummerField P.host.E P.host.φ₀ δ.hstar δ.hstar_pos
  have hall := sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ hM' hray) hcyc) hV
  change Sz (δ.M' ⊔ δ.ray ⊔ cycField (rootOrder P) ⊔ δ.V) _ _

  obtain ⟨hG, -, hf8, -⟩ := roots_sizes P L hL
  have hf0 : (0 : ℝ) < P.R.f := by have : 8 ≤ P.R.f := hf8; exact_mod_cast (by omega : 0 < P.R.f)
  have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
  rw [← hlE'] at hcl
  have hh0 : 0 < classNumber P.host.E := classNumber_pos _

  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := P.host.pde_prime.pos
  have hp' := P.host.pde'_prime.pos
  have hN : Real.log (modulus P : ℝ) ≤ 20 * L + 2 := by
    have e : Real.log (modulus P : ℝ) = Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log P.host.pde +
        Real.log P.host.pde' := by
      simp only [modulus]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    have := hL.g 0
    have := hL.g 1
    have := hL.p
    rw [e]; linarith [this.1, this.2]

  have hs0 : 0 ≤ Real.log (δ.hstar : ℝ) := Real.log_natCast_nonneg _
  have hs : Real.log (δ.hstar : ℝ) ≤ Real.log (classNumber P.host.E) + 2 * P.R.f * Real.log (modulus P : ℝ) := by
    have h1 : (δ.hstar : ℝ) ≤ (classNumber P.host.E : ℝ) * (modulus P : ℝ) ^ Module.finrank ℚ P.host.E := by
      exact_mod_cast hdeg_le
    have h2 := Real.log_le_log (by exact_mod_cast δ.hstar_pos) h1
    rw [Real.log_mul (by positivity) (pow_ne_zero _ (by exact_mod_cast modulus_ne_zero P)), Real.log_pow, hdeg] at h2
    push_cast at h2
    linarith

  have hr : Real.log (rootOrder P : ℝ) ≤ Real.log P.restRowsFiniteGroupCard + 24 := by
    have hc := P.restRowsFiniteGroupCard_pos
    have h1 : (rootOrder P : ℝ) ≤ (P.restRowsFiniteGroupCard : ℝ) * ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)
    have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (rootOrder_ne_zero P)) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    have e : Real.log ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = 4 * Real.log 3 + 4 * Real.log 5 := by
      rw [show ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = (3 : ℝ) ^ 4 * (5 : ℝ) ^ 4 by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith

  have hk : (NumberField.Units.rank P.host.E : ℝ) ≤ 2 * P.R.f := by
    have : NumberField.Units.rank P.host.E ≤ Module.finrank ℚ P.host.E := by
      rw [NumberField.Units.rank, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
    rw [hdeg] at this
    exact_mod_cast this
  have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
    rw [hdeg]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have := hL.deg
    linarith
  have hnum := om_sizes_le_poR P.R.f P.R.r L lE (Real.log (classNumber P.host.E)) (Real.log (modulus P : ℝ))
    (Real.log (δ.hstar : ℝ)) (Real.log P.restRowsFiniteGroupCard) (Real.log (rootOrder P : ℝ)) (Real.log (P.host.d : ℝ))
    (NumberField.Units.rank P.host.E) (Real.log (Module.finrank ℚ P.host.E)) (by exact_mod_cast hf8)
    (by exact_mod_cast hL.rank) hL.len hL.deg hlE0 hrd hcl hN hs0 hs hG hr hd hk d1
  refine sz_mono_and_of_le.1 _ _ _ _ _ hall ?_ ?_
  · unfold poR; exact hnum.1
  · unfold poR; exact hnum.2

end GlobalTheory.FieldSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.Resid

open GlobalTheory.Mem.SymFrame

variable {D : D7}

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def posE (D : D7) (a : Fin D.R.rS) : Fin D.R.r := ⟨a.1, by have := rank_eq D; omega⟩

def posB (D : D7) (i : Fin D.R.k) : Fin D.R.r := ⟨D.R.rS + i.1, by have := rank_eq D; omega⟩

def posN (D : D7) (a : Fin D.R.rS) : Fin D.R.r :=
  ⟨if a.1 + 1 < D.R.rS then a.1 + 1 else D.R.rS + D.R.k, by have := rank_eq D; split_ifs <;> omega⟩

theorem symVec_posN (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) :
    symVec X w (posN D a) = nxt X.e0 X.z0 a := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posN nxt
  by_cases h : a.1 + 1 < D.R.rS
  · simp [h]
  · have h2 : ¬ (D.R.rS + D.R.k < D.R.rS) := by omega
    simp [h]

theorem symVec_posB (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : EwAt X w) (i : Fin D.R.k) :
    symVec X w (posB D i) = X.bw i := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posB epsW
  have h1 : ¬ (D.R.rS + i.1 < D.R.rS) := by omega
  have h2 : D.R.rS + i.1 < D.R.rS + D.R.k := by omega
  simp [h1, h2, hw]

theorem dual_row (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i₀ : Fin D.R.r)
    (hd : ∀ j, hA X.B.I y (u j) - (if j = i₀ then 1 else 0) ∈ wInt X w) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) - (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈
      wInt X w := by
  have h := hA_isMatIn X w hN hy i
  have hs : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) ∈ wInt X w := by
    refine Submodule.sum_mem _ fun j _ => ?_
    exact (wInt X w).smul_mem
      (⟨_, natCast_mem _ (N j i).val⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hd j)
  have e : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) =
      (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j)) -
        (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e] at hs
  have := add_mem h hs
  convert this using 1
  abel

theorem natCast_g_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
  · simp
  · simp

theorem one_sub_ew_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (hw : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hA_mem_wInt X w hz (hw X.z0 hz)
  rw [hA_smul_right'] at h1
  have h2 := wInt_of_zmod X k hg X.formsAtZero.1
  have hint : 1 - X.ew ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := sub_mem (one_mem _) X.ew_int
  have h3 : (1 - X.ew) * (hA X.B.I X.z0 X.z0 + 1) ∈ wInt X w :=
    (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) h2
  have := sub_mem h3 h1
  convert this using 1
  ring

end GlobalTheory.Mem.SymChar.Resid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowPartFormsAndNonzeroVectorsEveryPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RowsLift

theorem rows_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH hM hg p hp i
  have hA := _root_.GlobalTheory.RowsAtBase.exists_base_row_of_pins D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp
  have hB : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ := by
    intro h0
    apply hA
    rw [← Submodule.finrank_eq_zero, ← hH.prim.dimParts i p, h0, finrank_bot]
  refine ⟨?_, fun v hv => ?_⟩
  · intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    have : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ R.Wp3 i p := hw.1
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).2 this
  · obtain ⟨x, hx, hx0⟩ := _root_.GlobalTheory.RatLift.exists_rat_lift_mem_part D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp i hB
    exact ⟨x, hx, _root_.GlobalTheory.Mem.R3.framesBase_majAt_ne_zero D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg i v hv x hx0⟩

end GlobalTheory.RowsLift
end

