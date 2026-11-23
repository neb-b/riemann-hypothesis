module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConnectionOnDividedPowerBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapMemExt
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDAcyc

variable {B : Type} [CommRing B] {J : Ideal B}

theorem le_fil_one (δ : DividedPowers J) : J ≤ fil δ 1 := by
  intro j hj
  refine Ideal.subset_span ⟨[(1, j)], by simpa using hj, by simp, by simp [δ.dpow_one hj]⟩

theorem algebraMap_mem_ext (Q : PDPoly B) {j : B} (hj : j ∈ J) :
    algebraMap B Q.P j ∈ Q.ext J :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj)

theorem e_one_mem_ext (Q : PDPoly B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem map_e {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {μ q : B} (hμ : μ ∈ J) (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P μ + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) = ∑ j ∈ Finset.range (k + 1), (δ.dpow j μ * q ^ (k - j)) • Q.e (k - j) := by
  have he1 : Q.e 1 ∈ Q.ext J := e_one_mem_ext Q
  have hm : algebraMap B Q.P μ ∈ Q.ext J := algebraMap_mem_ext Q hμ
  have hq : algebraMap B Q.P q * Q.e 1 ∈ Q.ext J := Ideal.mul_mem_left _ _ he1
  have h0 : g (Q.e k) = η.dpow k (g (Q.e 1)) := by
    rw [hgd.dpow_comp _ he1, hS.var]
  rw [h0, h1, η.dpow_add hm hq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ η.dpow a (algebraMap B Q.P μ) * η.dpow b (algebraMap B Q.P q * Q.e 1))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [η.dpow_mul he1, hS.var, hS.dp.dpow_comp _ hμ, Algebra.smul_def, map_mul, map_pow]
  ring

noncomputable def qDer (Q : PDPoly B) (q : B) (ν : ℕ → B) : Q.P →ₗ[B] Q.P :=
  Q.e.constr B fun k ↦ (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
    ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1))

theorem qDer_e (Q : PDPoly B) (q : B) (ν : ℕ → B) (k : ℕ) :
    qDer Q q ν (Q.e k) = (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1)) := by
  simp only [qDer, Module.Basis.constr_basis]

theorem map_e_sub {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) - Q.e k = (q - 1) • qDer Q q ν (Q.e k) := by
  rw [map_e hS hμ g hgd h1, qDer_e, Finset.sum_range_succ', δ.dpow_zero hμ, smul_add,
    smul_smul, mul_geom_sum, Finset.smul_sum]
  simp only [hν, smul_smul, mul_assoc, Nat.sub_zero, one_mul, sub_smul, one_smul]
  abel

theorem map_sub_self {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgB : g.comp (algebraMap B Q.P) = algebraMap B Q.P)
    (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (z : Q.P) :
    g z - z = (q - 1) • qDer Q q ν z := by
  have hsm : ∀ (b : B) (w : Q.P), g (b • w) = b • g w := fun b w ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * g w) (RingHom.congr_fun hgB b)
  let gl : Q.P →ₗ[B] Q.P :=
    { toFun := g, map_add' := map_add g, map_smul' := fun b w ↦ by simpa using hsm b w }
  have key : gl - LinearMap.id = (q - 1) • qDer Q q ν :=
    Q.e.ext fun k ↦ by simpa [gl] using map_e_sub hS hμ hν g hgd h1 k
  simpa [gl] using LinearMap.congr_fun key z

theorem main : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B)
    (η : DividedPowers (Q.ext J)), Q.IsStd δ η → ∀ (p : ℕ), p.Prime → IsNilpotent (p : B) →
    ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → ∀ g : Q.P →+* Q.P,
    g.comp (algebraMap B Q.P) = algebraMap B Q.P → IsDPMorphism η η g →
    g (1 + Q.e 1) = algebraMap B Q.P (x ^ p) * (1 + Q.e 1) →
    Function.Injective (algebraMap B Q.P) ∧
    (∀ r, ∀ z ∈ fil η r, g z = z → ∃ m ∈ fil δ (r + 1),
      algebraMap B Q.P m = algebraMap B Q.P (x ^ p - 1) * z) ∧
    ∀ r, ∀ z ∈ fil η r, ∃ y ∈ fil η (r + 1), g y - y = algebraMap B Q.P (x ^ p - 1) * z := by
  intro B _ J δ Q η hS p hp hpn x hx g hgB hgd hg1
  have hrepr : ∀ b : B, Q.e.repr (algebraMap B Q.P b) 0 = b := fun b ↦ by
    rw [Algebra.algebraMap_eq_smul_one, ← Q.e_zero, map_smul]
    simp
  have hμ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hx
  obtain ⟨hqn, ν, hν1, hνd, hνf, hνn, hνz⟩ := _root_.GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one δ p hp hpn x hx
  obtain ⟨hfm, hfa, -, hfr⟩ := _root_.GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ Q η hS
  have h1 : g (Q.e 1) = algebraMap B Q.P (x ^ p - 1) + algebraMap B Q.P (x ^ p) * Q.e 1 := by
    have := hg1
    rw [map_add (f := _), map_one, mul_add, mul_one, add_comm (1 : Q.P)] at this
    rw [_root_.map_sub, map_one (algebraMap B Q.P)]
    linear_combination this
  have hg := map_sub_self hS hμ hνd g hgB hgd h1
  obtain ⟨hker, hsurj⟩ := _root_.GlobalTheory.CompanionTheory.QDerivative.ker_and_surjective Q.e (fil δ) p (x ^ p) ν (qDer Q (x ^ p) ν) hp.ne_zero hpn
    hqn hfm hfa hν1 hνf hνn hνz (qDer_e Q (x ^ p) ν)
  refine ⟨fun a b hab ↦ by rw [← hrepr a, hab, hrepr], ?_, ?_⟩
  · intro r z hz hgz
    have hD : qDer Q (x ^ p) ν ((x ^ p - 1) • z) = 0 := by
      rw [map_smul, ← hg, hgz, sub_self]
    obtain ⟨c, hc⟩ := hker _ hD
    have hc' : algebraMap B Q.P c = algebraMap B Q.P (x ^ p - 1) * z := by
      rw [← Algebra.smul_def, hc, Q.e_zero, Algebra.algebraMap_eq_smul_one]
    refine ⟨c, ?_, hc'⟩
    have hc0 : c = (x ^ p - 1) * Q.e.repr z 0 := by
      have := hrepr c
      rw [hc', ← Algebra.smul_def, map_smul] at this
      simpa using this.symm
    rw [hc0, add_comm]
    have hz0 : Q.e.repr z 0 ∈ fil δ r := by simpa using (hfr r z).1 hz 0
    exact hfm 1 r (Ideal.mul_mem_mul (le_fil_one δ hμ) hz0)
  · intro r z hz
    obtain ⟨y, hy, hDy⟩ := hsurj r z ((hfr r z).1 hz)
    refine ⟨y, (hfr (r + 1) y).2 hy, ?_⟩
    rw [hg, hDy, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDAcyc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartMaps

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem nil_J (T : Thick (nlFun γ p X q κ)) : ∀ x ∈ T.J, IsNilpotent x := by
  intro x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

theorem isDP {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) : IsDPMorphism c.D.δ T.δ f := by
  have e : f.comp c.D.i = T.i := RingHom.ext hf
  refine IsDPMorphism.of_comp γ c.D.δ T.δ c.D.i f c.J_eq c.D.compat ?_
  rw [e]
  exact T.compat

theorem exists_unique_lift {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d)
    (T : Thick (nlFun γ p X q κ)) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : ∀ r, g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r))
    (y : Fin d → T.B) (hy : ∀ k, Ideal.Quotient.mk T.J (y k) = g (Ideal.Quotient.mk _ (c.t k))) :
    ∃! f : c.D.B →+* T.B, (∀ r, f (c.D.i r) = T.i r) ∧ (∀ k, f (c.t k) = y k) ∧
      (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J) := by
  have hL := _root_.GlobalTheory.CompanionTheory.EtNil.etLift_of_nil T.J (nil_J T)
  have hc : (g.comp (Ideal.Quotient.mk c.D.J)).comp
      (MvPolynomial.eval₂Hom c.D.i c.t : MvPolynomial (Fin d) R →+* c.D.B) =
      (Ideal.Quotient.mk T.J).comp (MvPolynomial.eval₂Hom T.i y : MvPolynomial (Fin d) R →+* T.B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simpa using hg r
    · simpa using (hy k).symm
  obtain ⟨f, ⟨h1, h2⟩, hu⟩ := hL (MvPolynomial (Fin d) R) c.D.B _ c.etale
    (MvPolynomial.eval₂Hom T.i y) (g.comp (Ideal.Quotient.mk c.D.J)) hc
  refine ⟨f, ⟨fun r => ?_, fun k => ?_, h2⟩, ?_⟩
  · simpa using RingHom.congr_fun h1 (MvPolynomial.C r)
  · simpa using RingHom.congr_fun h1 (MvPolynomial.X k)
  · rintro f' ⟨a1, a2, a3⟩
    refine hu f' ⟨MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_), a3⟩
    · simpa using a1 r
    · simpa using a2 k

theorem inU_of_hom {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)}
    (σ : c.D ⟶ T) : InU V T := by
  have e : pt T = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) ≫ pt c.D := by
    unfold pt
    rw [← σ.pt]
    rfl
  unfold InU
  rw [e]
  intro x _
  exact c.inV (show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle))) x ∈ ⊤ from trivial)

theorem quot_comm {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) (r : R) :
    g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r) := by
  have e := congrArg (fun z : PtOver X q κ (T.B ⧸ T.J) => z.1.1 (Ideal.Quotient.mk _ r)) hg
  have w1 := c.D.w r
  have w2 := T.w r
  calc g (Ideal.Quotient.mk _ (c.D.i r))
      = g ((nlFun γ p X q κ).str c.D.y (Ideal.Quotient.mk _ r)) := by rw [w1]
    _ = (nlFun γ p X q κ).str T.y (Ideal.Quotient.mk _ r) := e
    _ = Ideal.Quotient.mk _ (T.i r) := w2

def homOf {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hq : (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J))
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) : c.D ⟶ T :=
  have hdp := isDP c T f hf
  have hle : c.D.J ≤ T.J.comap f := fun _ hx => hdp.1 (Ideal.mem_map_of_mem f hx)
  mkH f hf hdp hle (by
    have e : Ideal.quotientMap T.J f hle = g :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun x => RingHom.congr_fun hq x)
    rw [e]
    exact hg)

theorem good {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) : c.Good := by
  refine ⟨fun T hT => ?_, fun T σ y hy => ?_⟩
  · obtain ⟨g, hg, -⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
    have hg' : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y := hg
    choose y hy using fun k => Ideal.Quotient.mk_surjective (g (Ideal.Quotient.mk _ (c.t k)))
    obtain ⟨f, ⟨h1, -, h3⟩, -⟩ := exists_unique_lift c T g (quot_comm c T g hg') y hy
    exact ⟨homOf c T f h1 g h3 hg'⟩
  · have hg : (nlFun γ p X q κ).Pt.map
        (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) c.D.y = T.y := σ.pt
    have hs : ∀ k, Ideal.Quotient.mk T.J (σ.φ (c.t k) + y k) =
        Ideal.quotientMap T.J σ.φ σ.hle (Ideal.Quotient.mk _ (c.t k)) := fun k => by
      rw [Ideal.quotientMap_mk, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (hy k), add_zero]
    obtain ⟨f, ⟨h1, h2, h3⟩, hu⟩ := exists_unique_lift c T (Ideal.quotientMap T.J σ.φ σ.hle)
      (quot_comm c T _ hg) (fun k => σ.φ (c.t k) + y k) hs
    refine ⟨homOf c T f h1 _ h3 hg, fun i => ?_, fun τ hτ => hom_ext ?_⟩
    · change f (c.t i) - σ.φ (c.t i) = y i
      rw [h2 i]
      ring
    · obtain ⟨g₀, -, hu₀⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y (inU_of_hom c σ)
      have e : Ideal.quotientMap T.J τ.φ τ.hle = Ideal.quotientMap T.J σ.φ σ.hle :=
        (hu₀ _ τ.pt).trans (hu₀ _ σ.pt).symm
      refine hu τ.φ ⟨τ.comm, fun k => ?_, ?_⟩
      · have := hτ k
        rw [← this]
        ring
      · rw [← e]
        rfl

end GlobalTheory.CompanionTheory.ChartMaps
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfIsAutFormTotallyComplex
section
open NumberField

namespace GlobalTheory.CompanionTheory.ContAutForm

open GlobalTheory.CuspRep

theorem continuous_of_isAutForm_totallyComplex (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (φ : Sm E N) (h : IsAutForm φ) : Continuous φ.1 :=
  h.continuous

end GlobalTheory.CompanionTheory.ContAutForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowersOnFiltration
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.RedInEx

section Abstract

variable {A : Type} [CommRing A] {I : Ideal A} {γ : DividedPowers I} {l s : ℕ}

theorem one_eq (γ : DividedPowers I) : pdP γ 1 = I := by
  refine le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le γ) fun x hx => ?_
  have h := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ 1 hx
  rwa [γ.dpow_one hx] at h

theorem mem_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x ∈ I) : x ∈ I := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf 1 ((l : A) ^ N * x) (by
      rw [one_eq]
      rwa [pow_succ', mul_assoc] at h)
    rwa [one_eq] at this

theorem eq_zero_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x = 0) : x = 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf s ((l : A) ^ N * x) (by
      rw [hb.nil]
      rw [pow_succ', mul_assoc] at h
      exact h)
    rw [hb.nil] at this
    exact this

theorem mem_of_fact_mul (hb : TFBase γ l s) (k : ℕ) (x : A) (h : (k.factorial : A) * x ∈ I) : x ∈ I := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  refine mem_of_pow_mul hb N x ?_
  rw [← hu, mul_comm _ u, mul_assoc]
  exact Ideal.mul_mem_left _ _ h

theorem eq_of_fact_mul (hb : TFBase γ l s) (k : ℕ) {x y : A} (h : (k.factorial : A) * x = (k.factorial : A) * y) :
    x = y := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul hb N _ ?_
  rw [← hu, mul_comm _ u, mul_assoc, mul_sub, h, sub_self, mul_zero]

theorem dpow_congr (hb : TFBase γ l s) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (h : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) x = Ideal.Quotient.mk _ y) (k : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) (γ.dpow k x) = Ideal.Quotient.mk _ (γ.dpow k y) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have haI : a ∈ I := mem_of_pow_mul hb n a (by rw [mul_comm, ha]; exact sub_mem hx hy)
  have hc : (l : A) ^ n * a ∈ I := Ideal.mul_mem_left _ _ haI
  have e : x = y + (l : A) ^ n * a := by rw [mul_comm, ha]; ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, γ.dpow_add hy hc, map_sum, Finset.sum_eq_single (k, 0)]
  · rw [γ.dpow_zero hc, mul_one]
  · rintro ⟨i, j⟩ hij hne
    have hj : j ≠ 0 := by
      rintro rfl
      have : i = k := by simpa using hij
      exact hne (by rw [this])
    change Ideal.Quotient.mk _ (γ.dpow i y * γ.dpow j ((l : A) ^ n * a)) = 0
    rw [γ.dpow_mul haI, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (by
      rw [pow_succ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · intro h0
    exact absurd (by simp) h0

end Abstract

section Concrete

open PAlg

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A]

def e0 (l : ℕ) [Fact l.Prime] : Acris0 l ≃+* (base l).Acr0 :=
  RingEquiv.ofBijective (base l).cris0 (RL.base_acr (base l) isBase_base).1.1

def lam0 (lam : Acris l →+* A) : (base l).Acr0 →+* A :=
  (lam.comp (algebraMap (Acris0 l) (Acris l))).comp (e0 l).symm.toRingHom

theorem lam0_cris0_eq_lam_of (lam : Acris l →+* A) (y : Acris0 l) :
    lam0 lam ((base l).cris0 y) = lam (AdicCompletion.of _ _ y) := by
  have h : (e0 l).symm ((base l).cris0 y) = y := (e0 l).symm_apply_apply y
  change lam (algebraMap (Acris0 l) (Acris l) ((e0 l).symm ((base l).cris0 y))) = _
  rw [h]
  rfl

theorem lam0_algebraMap_sW_eq_lam_algebraMap (lam : Acris l →+* A) (w : Ainf l) :
    lam0 lam (algebraMap (base l).W (base l).Acr0 ((base l).sW w)) = lam (algebraMap (Ainf l) (Acris l) w) := by
  have h : algebraMap (base l).W (base l).Acr0 ((base l).sW w) = (base l).cris0 (algebraMap (Ainf l) (Acris0 l) w) :=
    Subtype.ext (awayW_algebraMap (base l).s w).symm
  rw [h, lam0_cris0_eq_lam_of, AdicCompletion.algebraMap_apply]

def rho (lam : Acris l →+* A) (n : ℕ) : (base l).Acr n →+* A ⧸ Ideal.span {(l : A) ^ n} :=
  ((base l).cris n).liftOfSurjective ((RL.base_acr (base l) isBase_base).2 n).1
    ⟨(Ideal.Quotient.mk _).comp lam, fun x hx => by
      rw [((RL.base_acr (base l) isBase_base).2 n).2] at hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have hz : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) ((l : A) ^ n) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_mul, map_pow, map_natCast, hz, mul_zero]⟩

theorem rho_cris (lam : Acris l →+* A) (n : ℕ) (c : Acris l) :
    rho lam n ((base l).cris n c) = Ideal.Quotient.mk _ (lam c) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ c

theorem rho_mk (lam : Acris l →+* A) (n : ℕ) (y : (base l).Acr0) :
    rho lam n ((base l).mkAcr n y) = Ideal.Quotient.mk _ (lam0 lam y) := by
  obtain ⟨y, rfl⟩ := (e0 l).surjective y
  change rho lam n ((base l).mkAcr n ((base l).cris0 y)) = Ideal.Quotient.mk _ (lam0 lam ((base l).cris0 y))
  rw [← cris_of, rho_cris, lam0_cris0_eq_lam_of]

variable {I : Ideal A} {γ : DividedPowers I} {s : ℕ}

theorem lam0_mem_of_mem_fil0_one (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) :
    lam0 lam x ∈ I := by
  have : (base l).Fil0 1 ≤ I.comap (lam0 lam) := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_of_fact_mul hb k _ ?_
    rw [← map_natCast (lam0 lam), ← map_mul, (RL.filtration_multiplicative (base l)).2.2.1 k, map_pow]
    refine Ideal.pow_mem_of_mem _ ?_ _ hk
    rw [show (base l).xi = (base l).sW (xi0 l) from rfl, lam0_algebraMap_sW_eq_lam_algebraMap]
    exact hξ
  exact this hx

theorem lam0_dpow (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x z : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) (k : ℕ)
    (hz : (k.factorial : (base l).Acr0) * z = x ^ k) : lam0 lam z = γ.dpow k (lam0 lam x) := by
  refine eq_of_fact_mul hb k ?_
  rw [γ.factorial_mul_dpow_eq_pow (lam0_mem_of_mem_fil0_one hb lam hξ hx), ← map_natCast (lam0 lam), ← map_mul, hz, map_pow]

theorem exists_unit_one_add_generator (x : (base l).Acr0) (hx : x ∈ (base l).Fil0 1) (k : ℕ) :
    ∃ z : (base l).Acr0, (k.factorial : (base l).Acr0) * z = x ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨1, by simp⟩
  · obtain ⟨z, -, hz⟩ := (RL.pdi (base l)).1 x hx k hk
    exact ⟨z, hz⟩

end Concrete

theorem redIn_ex : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {A : Type} [CommRing A] [Algebra (OK l K) A]
    {I : Ideal A} (γ : DividedPowers I) (s : ℕ) (lam : Acris l →+* A), TFBase γ l s →
    lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I →
    (∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w) ∈ I) →
    ∀ n : ℕ, ∃ d : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) γ l n,
      ∀ c, d.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (lam c) := by
  intro l _ K A _ _ I γ s lam hb hξ hO n
  have hfil : ∀ x ∈ (PAlg.base l).Fil n 1, ∃ x₀ ∈ (PAlg.base l).Fil0 1, (PAlg.base l).mkAcr n x₀ = x := by
    intro x hx
    rw [((PAlg.base l).isPd_pdFil n).1] at hx
    exact (Ideal.mem_map_iff_of_surjective _ ((PAlg.base l).mkAcr_surjective n)).1 hx
  refine ⟨{ hl := (Fact.out : l.Prime).ne_zero, ρ := rho lam n, mem := ?_, dp := ?_, hκ := ?_ }, rho_cris lam n⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    exact ⟨lam0 lam x₀, lam0_mem_of_mem_fil0_one hb lam hξ hx₀, rho_mk lam n x₀⟩
  · intro k x hx y hy e
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    obtain ⟨z, hz⟩ := exists_unit_one_add_generator x₀ hx₀ k
    have e1 : (B.DD false (PAlg.base l) n).dpow k ((PAlg.base l).mkAcr n x₀) = (PAlg.base l).mkAcr n z :=
      ((PAlg.base l).isPd_pdFil n).2 k x₀ z hx₀ hz
    rw [e1, rho_mk, lam0_dpow hb lam hξ hx₀ k hz]
    rw [rho_mk] at e
    exact dpow_congr hb (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) hy e k
  · intro a r h
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (okToOC l K a)
    have h1 : B.κb (okToOC l K) false n a = Ideal.Quotient.mk _ ((PAlg.base l).toAcr n ((PAlg.base l).sW w)) := by
      change B.uJ false (PAlg.base l) n ((PAlg.base l).oC (okToOC l K a)) = _
      rw [← hw, PAlg.oC_theta0, B.uJ_th]
    rw [h1] at h
    have h2 : r - (PAlg.base l).toAcr n ((PAlg.base l).sW w) ∈ (PAlg.base l).Fil n 1 :=
      Ideal.Quotient.eq.1 h.symm
    obtain ⟨x₀, hx₀, e⟩ := hfil _ h2
    have h3 : rho lam n r = Ideal.Quotient.mk _ (lam (algebraMap (Ainf l) (Acris l) w) + lam0 lam x₀) := by
      rw [map_add (f := _), ← rho_mk, e, ← PAlg.cris_algebraMap, ← rho_cris, PAlg.cris_algebraMap, map_sub, add_sub_cancel]
    refine ⟨lam0 lam x₀ - (algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w)),
      sub_mem (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) (hO a w hw), ?_⟩
    rw [h3]
    congr 1
    ring

end GlobalTheory.CompanionTheory.RedInEx
end
end

