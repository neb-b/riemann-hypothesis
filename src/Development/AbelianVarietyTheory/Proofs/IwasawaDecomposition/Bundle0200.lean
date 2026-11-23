module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef

variable {D : D7} {S T : HSp D} {r g : ℕ}

def IsSet (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hr : T.rank = r) (X : Data D.host.E r)
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ S.gram = 1 ∧ Even S.rank ∧ ModelW T hr X ∧ X.κ0 = -(2 * D.host.xi0) ∧
    (∀ ρ, (eT ρ).1 = tauE D ρ) ∧ IsSympl X bas

abbrev Fam (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

def negM (T : HSp D) (q : ℕ) : Matrix (Fin T.rank) (Fin T.rank) ℂ :=
  Matrix.diagonal fun a : Fin T.rank => ((-(sgn q (a : ℕ)) : ℝ) : ℂ)

def IsONeg (T : HSp D) (q : ℕ) (Z : Fam T) : Prop := ∀ ρ, (Z ρ)ᴴ * gramAt D T ρ * Z ρ = negM T q

def cartZ (T : HSp D) (q : ℕ) (Z : Fam T) : Fam T := fun ρ => Z ρ * negM T q * (Z ρ)⁻¹

def mvZ (θ : InfFam D) (h : GA D T) (Z : Fam T) : Fam T := fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * Z ρ

def frOf (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (Z : Fam T) : Frame X.Ψ r :=
  fun τ a b => Z (eT.symm τ) (Fin.cast hr.symm a) (Fin.cast hr.symm b)

def rePt (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (w : WO S T) :
    Ker.WR X S.rank :=
  fun τ k a => compAt θ (eT.symm τ) w (Fin.cast hr.symm a) k

def Zak (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r}
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (φ : TF S.rank g) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w, Ker.IsRealPt w → f w = Ker.thR X bas idx φ x (rePt θ hr eT w)

def finR (S : HSp D) (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) : WO S T :=
  Ker.finW S T (y.submatrix id (Fin.cast hr))

def latW (hr : T.rank = r) (L : Lt D.host.E r) : Lt D.host.E T.rank :=
  L.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr.symm))

def toP (S : HSp D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ X.Ψ q0 X.p0 (Fin S.rank) :=
  MvPolynomial.aeval fun v => MvPolynomial.C (((2 / fockScale D v.1 : ℝ) : ℂ)) *
    MvPolynomial.X (eT v.1, (rowIdx hq).symm (Fin.cast hr v.2.1), v.2.2)

def fv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (q : ℕ) (Z : Fam T) (f : WO S T → ℂ)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO ψ θ S T (fun _ => 1) (cartZ T q Z) (fun _ => 1) Z f Q

def ctxOf {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hn : Even S.rank)
    (X' : Data D.host.E T.rank) (m : Ker.Match S T X') {q : ℕ} (hq : X'.p0 + q = T.rank)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') : Ker.Ctx S T :=
  ⟨ψ, hψ, θ, hθ, X', m, g, q, hq, bas', idx', hs, hn⟩

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

def MarkAd (hr : T.rank = r) (l : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) (h : GA D T)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat T h,
    finVec T (mk a ∘ Fin.cast hr) - (finHom T h).1.mulVec (finVec T (ι a)) = (l.M : ℕ) • w

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Matched (c : Coeff l) (σ : c.F →+* ℂ) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

abbrev ptC (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) : @FrPt D.host.E _ _ _ H Dw l Xo c ℂ _ σ.toAlgebra :=
  unC (Formalism.L2.PjFree.Unf.ofPj U) k x

def FrConst (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f₀ : WO S T → ℂ) (U : Unf Xo c σ r)
    (dict : GA D T → Σ k, Frame (U.X k).Ψ r) (mu : GA D T → ℂ) (Z₀ : Fam T) (cc : U.Comp → ℂ) : Prop :=
  ∀ (h γ : GA D T), γ ∈ GQ T → ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw),
    IsSet ψ θ S T hr (U.X (dict h).1) eT bas → Matched c σ (U.X (dict h).1) idx e →
    (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom),
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩))
      (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U (dict h).1 ⟨(dict h).2, hx⟩).s th →
      ∀ w : WO S T, Ker.IsRealPt w →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          (Ker.gaussR (U.X (dict h).1) bas idx (dict h).2 (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w)) *
            ∏ b, th (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w) b))

section Field

variable {c' : Coeff l} {hle : c.F ≤ c'.F} [Algebra c.F ℂ] [Algebra c'.F ℂ] (hA : AlgOver c c' hle ℂ) {X : Data D.host.E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt D.host.E r} {y : FrPt Xo c ℂ}

def fibExt (A : AnFib X bas idx e x L y) : AnFib X bas idx e x L (y.ext hle hA) :=
  ⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker, A.ex_lin, A.hol, A.der, A.fr, A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm,
    A.fr_per⟩

end Field

end Geo

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseZ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Fam (Wc D i) := x0Mat (R.MW i (sg0 D A))

end Rec

end GlobalTheory.OneMapRef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions IsDedekindDomain
open Formalism.MainNotions.S (FlagG XS ddS FrameOK)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS XLam IsFixedConv FixedHyp)
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm.Conv

section Ideals

variable {E : Type} [Field E] [NumberField E]

theorem exists_local_gen {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) :
    ∃ c : E, c ≠ 0 ∧ c ∈ I ∧ ∀ x ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  have int {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹) : ∃ o : 𝓞 E, (o : E) = a * b := by
    have := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  obtain ⟨a, ha, b, hb, s, hs, e⟩ : ∃ a ∈ I, ∃ b ∈ I⁻¹, ∃ s : 𝓞 E, s ∉ P ∧ (s : E) = a * b := by
    by_contra h
    have h1 : (1 : E) ∈ I * I⁻¹ := by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
    obtain ⟨s, hs, e⟩ := FractionalIdeal.mul_induction_on (C := fun x => ∃ s ∈ P, (s : E) = x) h1
      (fun a ha b hb => by
        obtain ⟨o, e⟩ := int ha hb
        exact ⟨o, by_contra fun k => h ⟨a, ha, b, hb, o, k, e⟩, e⟩)
      (fun _ _ ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨s + t, add_mem hs ht, by rw [← e, ← f]; simp⟩)
    obtain rfl : s = 1 := RingOfIntegers.ext e
    exact hP ((Ideal.eq_top_iff_one _).2 hs)
  refine ⟨a, fun h => hs ?_, ha, fun x hx => ⟨s, hs, ?_⟩⟩
  · obtain rfl : s = 0 := RingOfIntegers.ext (by rw [e, h, zero_mul]; rfl)
    exact zero_mem _
  · obtain ⟨o, f⟩ := int hx hb
    exact ⟨o, by rw [e, f]; ring⟩

theorem exists_gen_dInv (j : ℕ) (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    ∃ c : E, c ≠ 0 ∧ c ∈ dInv E j ∧ (¬ P ∣ differentIdeal ℤ (𝓞 E) → c = 1) ∧
      ∀ x ∈ dInv E j, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  by_cases h : P ∣ differentIdeal ℤ (𝓞 E)
  · obtain ⟨c, h1, h2, h3⟩ := exists_local_gen (I := dInv E j)
      (fun e => by simpa [e] using Iota.one_mem_dInv (E := E) j) hP.ne_top
    exact ⟨c, h1, h2, fun k => absurd h k, h3⟩
  · obtain ⟨s, hs, hn⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.dvd_iff_le.2 h)
    refine ⟨1, one_ne_zero, Iota.one_mem_dInv j, fun _ => rfl, fun x hx =>
      ⟨s ^ j, fun k => hn (hP.mem_of_pow_mem j k), ?_⟩⟩
    have h0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
    have := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E) (Ideal.pow_mem_pow hs j)) hx
    rw [FractionalIdeal.coeIdeal_pow, dInv, ← mul_pow, mul_inv_cancel₀ h0, one_pow] at this
    obtain ⟨o, e⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨o, by rw [mul_one]; exact e.symm⟩

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P) : ¬ P ∣ differentIdeal ℤ (𝓞 E) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have e : HeightOneSpectrum.asIdeal '' placesOver E p = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := v.isPrime
      exact ⟨v.isPrime, (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa [placesOver] using hv)⟩
    · rintro ⟨h1, h2⟩
      have k : (p : 𝓞 E) ∈ Q := by simpa using (Ideal.liesOver_span_iff h1.ne_top hp').1 h2
      exact ⟨⟨Q, h1, fun e => hp.ne_zero (by simpa [e] using k)⟩, k, rfl⟩
  have hd := GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp E (by
    rw [← e, Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw, h])
  exact not_dvd_differentIdeal_iff.2 ((not_dvd_discr_iff_forall_mem E (𝓞 E) hp').1 hd P hP (by simpa using hm))

end Ideals

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) (Fin S.rank → E)} {F : LFlag S r T}

variable (h : IntFrame (starRingEnd E) S.gram T Λ (coMat S (Formalism.MainNotions.S.Lat.frame F)))
include h

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddS_eq : ddS D = (differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) := by
  rw [ddS, differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.F) (𝓞 D.host.E),
    GlobalTheory.CMDiscrSq.differentIdeal_eq_top D.sp.cm, Ideal.top_mul]

theorem level_not_dvd (P : HeightOneSpectrum (𝓞 D.host.E)) (h : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.E) := by
  have := P.isPrime
  rw [gS, Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact not_dvd_different (D.host.g_prime 0) (D.nd.g_split 0) _ h
  · exact not_dvd_different (D.host.g_prime 1) (D.nd.g_split 1) _ h

variable {D}

end Record

end GlobalTheory.IntTerm.Conv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm


open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in
theorem weights_of_minors : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  intro D i σ hσ M _
  subst hσ
  have hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s := by
    obtain ⟨a, ha⟩ := Formalism.L2.NTheta.odd_r D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    exact ⟨a + b + 1, by omega⟩
  obtain ⟨s, hs⟩ := hnr
  have hsq : (D.R.r : ℚ) + D.R.t = 2 * s := by exact_mod_cast hs
  choose e he using fun τ : D.what₂.Tau => (D.hc τ).e_int i
  choose d hd using fun τ : D.what₂.Tau => (_root_.GlobalTheory.PairWeightArith.arithAt D i τ).d_int
  refine ⟨fun τ => -e τ + s, fun τ => -e τ - s, fun τ => -d τ, fun τ => ?_⟩
  have A := _root_.GlobalTheory.PairWeightArith.arithAt D i τ
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = 2 * s := by rw [hV, hs]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hVq]; push_cast; ring
  · rw [he, hVq]; push_cast; ring
  · have := hd τ
    unfold dShift at this
    push_cast
    rw [← this]
    ring
  · have hen := M.enum τ
    rw [GlobalTheory.ThetaFiresProbe.parAt_fixed] at hen
    obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq) hen
    intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [hx x]
    congr 1
    rcases x with c | c
    · have h1 := A.kap_plus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e τ + s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) =
            (((aP D i τ c : ℤ) + (-e τ + s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_pos (by simp)]
      simp
    · have h1 := A.kap_minus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
          -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) =
            ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_neg (by simp)]
      have h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) =
          qS D i τ - 1 - c := by
        simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
        rw [← hn]
        simp only [qS]
        omega
      rw [h3]
  · intro j
    have h1 := A.coef_eq j
    rw [hd] at h1
    have h2 : (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d τ := by
      exact_mod_cast h1
    rw [h2]
    have hj := j.2
    unfold wtU thetaWt
    simp only [pS, qS] at hpq ⊢
    by_cases c1 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
    · have ht := D.R.three_m_lt_t
      rw [if_pos c1, if_pos c1, if_neg (by omega)]
      ring
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1 + D.R.t
      · rw [if_pos c2, if_neg (by omega)]
        ring
      · rw [if_neg c2, if_pos (by omega)]
        have h3 : (Vc D i).rank - 1 - (j : ℕ) = ((Wc D i).sig (tauE D τ)).2 - 1 - (j - (((Wc D i).sig (tauE D τ)).1 + D.R.t)) := by
          omega
        rw [h3]
        ring

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

namespace SerreCriterion

variable {X : Scheme.{0}}

theorem exists_germ_eq_of_support_subset {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    (hF : support F ⊆ {y}) (t : (F.presheaf.stalk y :)) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t := by
  classical
  by_cases h : y ∈ support F
  · obtain ⟨s, hs⟩ := (germ_support_bijective (F := F) ((Set.finite_singleton y).subset hF)
      fun x hx => by rw [show x = y from hF hx]; exact hy).2
      (Function.update (fun _ => 0) ⟨y, h⟩ t)
    refine ⟨s, (congrFun hs ⟨y, h⟩).trans ?_⟩
    simp
  · exact ⟨0, (notMem_support_iff.1 h).elim _ _⟩

theorem support_pushforward_subscheme_subset (Y : X.IdealSheafData) :
    support ((Scheme.Modules.pushforward Y.subschemeι).obj (structureModule Y.subscheme)) ⊆
      Y.support := by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t => ?_) hx
  obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem (U := Y.support.compl) h t
  have e : Y.subschemeι ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun z hz => (hV hz (Y.range_subschemeι.le ⟨z, rfl⟩)).elim
  have : Subsingleton Γ(Y.subscheme, Y.subschemeι ⁻¹ᵁ V) := by
    rw [e]
    infer_instance
  have hs : s = 0 := this.elim s 0
  rw [hs, map_zero]

theorem not_isUnit_of_toSubscheme_eq_zero (Y : X.IdealSheafData) {y : X} (hy : y ∈ Y.support)
    (g : ((structureModule X).presheaf.stalk y :)) (hg : stalkLinear (toSubscheme Y) y g = 0) :
    ¬ IsUnit (structureModuleStalkEquiv y g) := by
  have hex := (exact_iff_stalkLinear (ShortComplex.mk (kernel.ι (toSubscheme Y)) (toSubscheme Y)
    (kernel.condition _))).1 (ShortComplex.exact_kernel _) y
  obtain ⟨u, rfl⟩ := (hex g).1 hg
  obtain ⟨V, hV, u, rfl⟩ := (idealModule Y).presheaf.exists_germ_eq u
  intro hu
  refine notMem_support_of_mem_basicOpen Y u ((X.mem_basicOpen _ y hV).2 ?_) hy
  rw [← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
  exact hu

theorem exists_mem_nonzeroLocus {M : LB X} (hM : M.IsLB) {J : X.Modules}
    (j : J ⟶ structureModule X) (Y : X.IdealSheafData) {y : X} (hY : (Y.support : Set X) = {y})
    (h : Subsingleton (coh (twist (kernel (j ≫ toSubscheme Y)) M) 1))
    {U : X.Opens} (hU : y ∈ U) (t : Γ(J, U))
    (ht : structureModuleSectionsEquiv U (j.app U t) = 1) :
    ∃ a : Γ(twist J M, ⊤), y ∈ nonzeroLocus (secOfTwist j a) := by
  set φ := j ≫ toSubscheme Y with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor M)).ShortExact := Twist.shortExact_map hM hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hyc : IsClosed ({y} : Set X) := hY ▸ Y.support.isClosed
  have hQ : support (twist S.X₃ M) ⊆ {y} := by
    rw [support_twist hM, ← hY]
    refine fun x hx => support_pushforward_subscheme_subset Y ?_
    have := mem_support_iff.1 hx
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) x).nontrivial
  obtain ⟨c, hc⟩ := exists_chart hM y
  obtain ⟨b, hb⟩ := exists_germ_eq_of_support_subset hyc hQ
    ((stalkEquiv S.X₃ hM c hc).symm (stalkLinear S.g y (J.presheaf.germ U y hU t)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨a, basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ y hc).2 ?_)⟩
  have hm : y ∈ ⊤ ⊓ M.U c := ⟨trivial, hc⟩
  replace hb := (stalkEquiv_germ hM c hc (V := ⊤) trivial _).symm.trans
    ((LinearEquiv.eq_symm_apply _).1 hb)
  have h₁ : stalkLinear S.g y (J.presheaf.germ _ y hm (coord (F := J) a c)) =
      stalkLinear S.g y (J.presheaf.germ U y hU t) :=
    (stalkLinear_germ S.g y hm _).trans hb
  have h₂ : stalkLinear φ y (J.presheaf.germ U y hU t -
      J.presheaf.germ _ y hm (coord (F := J) a c)) = 0 := by
    rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
    exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
  rw [hφ, stalkLinear_comp, LinearMap.comp_apply] at h₂
  have h₃ := not_isUnit_of_toSubscheme_eq_zero Y (y := y) (hY.ge rfl) _ h₂
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, structureModuleStalkEquiv_germ,
    structureModuleStalkEquiv_germ, ht, map_one] at h₃
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
  exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hc _)).mpr hu

end SerreCriterion


open SerreCriterion in
theorem isAmpleLB_of_subsingleton_coh_one (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (L : LB X) (hL : L.IsLB)
    (h : ∀ F : X.Modules, IsFiniteQC F →
      ∃ n : ℕ, 1 ≤ n ∧ Subsingleton (coh (twist F (lbPow L n)) 1)) : IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨y, hxy, hy⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  obtain ⟨W, hW, hyW⟩ := exists_affine_mem y
  let I := Scheme.IdealSheafData.vanishingIdeal W.compl
  have hI : ∀ z, z ∉ I.support ↔ z ∈ W := fun z => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact not_not
  let Y := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨{y}, hy⟩
  have hY : (Y.support : Set X) = {y} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨n, hn, hz⟩ := h (kernel (idealModuleι I ≫ toSubscheme Y)) (.of_mono (kernel.ι _))
  obtain ⟨t, ht⟩ := exists_idealModuleι_app_eq_one I fun z => (hI z).2
  have hM := isLB_lbPow hL n
  obtain ⟨a, ha⟩ := exists_mem_nonzeroLocus hM _ Y hY hz hyW t ht
  have hle : nonzeroLocus (secOfTwist (idealModuleι I) a) ≤ W := iSup_le fun c z hz => (hI z).1 <| by
    rw [secOfTwist_f] at hz
    exact notMem_support_of_mem_basicOpen I _ ((X.basicOpen_res _ (homOfLE _).op).le hz).2
  refine ⟨n, hn, _, (specializes_iff_mem_closure.2 hxy).mem_open (Opens.isOpen _) ha, ?_⟩
  exact inf_eq_left.2 hle ▸ isAffineOpen_nonzeroLocus_inf hM _ hW

end GlobalTheory
end
end

