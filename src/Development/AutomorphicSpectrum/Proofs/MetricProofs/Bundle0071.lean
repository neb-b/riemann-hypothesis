module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecond
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem sameOrbit_basePart {M : FlagModel y Ψ N j} {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) (x : R.X) {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x x) :
    SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) := by
  obtain ⟨hbm, hcov, -, hall⟩ := hS
  obtain ⟨z₁, -, h1, h2⟩ := hall x
  have e : basePart M.blk z = basePart M.blk z₁ := by
    funext q
    obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨q.1.1, q.2⟩ (hcov _ (Or.inl q.1.2))
    have h3 : z (v r) = z₁ (v r) := congrFun (hz.trans h1.symm) r
    rw [hr] at h3
    exact h3
  rw [e]
  exact h2

theorem exists_base_const {L : Type} {μ : L → Type} {b₁ b₂ b : (Σ k, μ k) → ℂ} (h₁ : SameOrbit b₁ b)
    (h₂ : SameOrbit b₂ b) : ∃ c : L → ℂ, (∀ k, c k ≠ 0) ∧ ∀ q, b₁ q = c q.1 * b₂ q := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  refine ⟨fun k => c₁ k / c₂ k, fun k => div_ne_zero (hc₁ k) (hc₂ k), fun q => ?_⟩
  have := hc₂ q.1
  field_simp

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hbm : IsBlockMap κ v) (k : Kk) (i : ι (κ k)) :
    ∃ m : ιk k, v ⟨k, m⟩ = ⟨κ k, i⟩ := by
  obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ r.1 = κ k := by rw [← hbm.2.2.1 r, hr]
  have h2 : r.1 = k := hbm.1 h1
  obtain ⟨r1, m⟩ := r
  obtain rfl : r1 = k := h2
  exact ⟨m, hr⟩

theorem stepGap_eq {M : FlagModel y Ψ N j} [Fintype Ψ] [DecidableEq Ψ] {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) {x x' : R.X} (hpr : pr x = pr x') (hb : pr x ∉ bdry BM.s)
    (hblk : ∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k,
      R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩)
    {z z' : (Σ k, ι k) → ℂ} (hzm : z ∈ mcPts (mCoordIdeal y)) (hz'm : z' ∈ mcPts (mCoordIdeal y))
    (hz : z ∘ v = R.lift x x) (hz' : z' ∘ v = R.lift x' x') :
    stepGap M BM p z = stepGap M BM p z' := by
  have so := sameOrbit_basePart hS x hz
  have so' := sameOrbit_basePart hS x' hz'
  rw [← hpr] at so'
  obtain ⟨cb, hcb, hcbq⟩ := exists_base_const so so'
  obtain ⟨hbm, hcov, -, -⟩ := hS
  have e1 : ∀ r, z (v r) = R.lift x x r := congrFun hz
  have e2 : ∀ r, z' (v r) = R.lift x' x' r := congrFun hz'
  have ha : ∃ a : ℂ, a ≠ 0 ∧ ∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩ := by
    rcases hp : M.blk p with _ | k₀
    · exact ⟨1, one_ne_zero, fun k hk => by simp at hk⟩
    · obtain ⟨k', rfl⟩ := hcov k₀ (Or.inr hp)
      obtain ⟨i, hi⟩ := hzm.1 (κ k')
      obtain ⟨m, hm⟩ := exists_coord hbm k' i
      obtain ⟨a, ha⟩ := hblk k' m hp
      refine ⟨a, fun h0 => hi ?_, fun k hk m' => ?_⟩
      · rw [← hm, e1, ha, h0, zero_mul]
      · obtain rfl : κ k' = k := Option.some.inj hk
        obtain ⟨m'', hm''⟩ := exists_coord hbm k' m'
        rw [← hm'', e1, e2, ha]
  obtain ⟨a, ha0, ha⟩ := ha
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then cb ⟨k, h⟩ else if M.blk p = some k then a else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    simp only [c]
    split_ifs
    · exact hcb _
    · exact ha0
    · exact one_ne_zero
  have hT := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z' c hc
  have h1 : stepGap M BM p (fun q => c q.1 * z' q) = stepGap M BM p z' :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus K ι Φ y Ψ N j M n BM p z' c hc hz'm.1
  rw [← h1]
  refine _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block K ι Φ y Ψ N j M n BM p (pr x) z _ hb hzm (hT.2 hz'm).1 so ?_ ?_
  · funext q
    have : c q.1.1 = cb q.1 := dif_pos q.1.2
    show basePart M.blk z q = c q.1.1 * z' ⟨q.1.1, q.2⟩
    rw [this, hcbq]
    rfl
  · intro k hk m
    have : c k = a := (dif_neg fun h => h p hk).trans (if_pos hk)
    show z ⟨k, m⟩ = c k * z' ⟨k, m⟩
    rw [this, ha k hk]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hS x x' hpr hblk
  by_cases hb : pr x ∈ bdry BM.s
  · have hb' : pr x' ∈ bdry BM.s := hpr ▸ hb
    rw [stepPh, stepPh, dif_neg fun h => h.1 hb, dif_neg fun h => h.1 hb']
  · have hb' : pr x' ∉ bdry BM.s := hpr ▸ hb
    obtain ⟨z₁, hz₁, hv₁, -⟩ := hS.2.2.2 x
    obtain ⟨z₂, hz₂, hv₂, -⟩ := hS.2.2.2 x'
    have h1 : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x := ⟨hb, z₁, hz₁, hv₁⟩
    have h2 : pr x' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x' x' := ⟨hb', z₂, hz₂, hv₂⟩
    rw [stepPh, stepPh, dif_pos h1, dif_pos h2]
    exact stepGap_eq hS hpr hb hblk h1.2.choose_spec.1 h2.2.choose_spec.1 h1.2.choose_spec.2 h2.2.choose_spec.2

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section GenU

variable (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S)

theorem genU_self (a : Fin (r s)) : genU Ω r s a a = 1 := by
  simp [genU]

theorem genU_of_lt {a b : Fin (r s)} (h : a < b) : genU Ω r s a b = 0 := by
  simp [genU, not_lt.2 h.le, h.ne]

theorem genU_of_gt {l k : Fin (r s)} (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) :=
  dif_pos h

end GenU

variable {Ψ : Type} {p q : ℕ} (Ω : Type) [Field Ω]

theorem symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
  rw [← blockEquiv_inl, Equiv.symm_apply_apply]

theorem symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
  rw [← blockEquiv_inr, Equiv.symm_apply_apply]

theorem gMat_apply (τ : Ψ) (i j : Fin (p + q)) :
    gMat p q Ω τ i j = (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ) : Matrix (Fin q) (Fin q) _) 0 0
      (genU Ω (rk Ψ p q) (.inl τ) : Matrix (Fin p) (Fin p) _)) ((blockEquiv p q).symm i) ((blockEquiv p q).symm j) :=
  rfl

theorem gMat_om (τ : Ψ) (a b : Fin q) :
    gMat p q Ω τ (omEmb p q a) (omEmb p q b) = genU Ω (rk Ψ p q) (.inr τ) a b := by
  rw [gMat_apply, symm_omEmb, symm_omEmb]
  rfl

theorem gMat_w (τ : Ψ) (a b : Fin p) :
    gMat p q Ω τ (wEmb p q a) (wEmb p q b) = genU Ω (rk Ψ p q) (.inl τ) a b := by
  rw [gMat_apply, symm_wEmb, symm_wEmb]
  rfl

theorem gMat_om_w (τ : Ψ) (a : Fin q) (b : Fin p) : gMat p q Ω τ (omEmb p q a) (wEmb p q b) = 0 := by
  rw [gMat_apply, symm_omEmb, symm_wEmb]
  rfl

theorem gMat_lowerUni (τ : Ψ) : IsLowerUni (gMat p q Ω τ) := by
  constructor
  · intro a
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    rcases x with x | x
    · rw [blockEquiv_inl, gMat_om]
      exact genU_self Ω (rk Ψ p q) (.inr τ) x
    · rw [blockEquiv_inr, gMat_w]
      exact genU_self Ω (rk Ψ p q) (.inl τ) x
  · intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    rcases x with x | x <;> rcases y with y | y
    · rw [blockEquiv_inl, blockEquiv_inl] at hab ⊢
      rw [gMat_om]
      exact genU_of_lt Ω (rk Ψ p q) (.inr τ) ((omEmb_strictMono p q).lt_iff_lt.1 hab)
    · rw [blockEquiv_inl, blockEquiv_inr, gMat_om_w]
    · rw [blockEquiv_inr, blockEquiv_inl] at hab
      have h : q + (x : ℕ) < (y : ℕ) := hab
      have := y.2
      omega
    · rw [blockEquiv_inr, blockEquiv_inr] at hab ⊢
      rw [gMat_w]
      exact genU_of_lt Ω (rk Ψ p q) (.inl τ) ((wEmb_strictMono p q).lt_iff_lt.1 hab)

def loc (t : GenIx (rk Ψ p q)) : Ψ × Fin (p + q) × Fin (p + q) :=
  match t with
  | ⟨.inl τ, lk⟩ => (τ, wEmb p q lk.1.1, wEmb p q lk.1.2)
  | ⟨.inr τ, lk⟩ => (τ, omEmb p q lk.1.1, omEmb p q lk.1.2)

theorem exists_var (x : LowIdx Ψ (p + q) p) :
    ∃ t : GenIx (rk Ψ p q), loc t = x.1 ∧ gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 =
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) := by
  obtain ⟨⟨τ, a, b⟩, hlt, hiff⟩ := x
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rcases a with a | a <;> rcases b with b | b
  · simp only [blockEquiv_inl] at hlt hiff ⊢
    have h : b < a := (omEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inr τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_om]; exact genU_of_gt Ω (rk Ψ p q) (.inr τ) h⟩
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hlt
    have h : q + (b : ℕ) < (a : ℕ) := hlt
    have := a.2
    omega
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hiff
    have h : (q + (a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p) := hiff
    have := b.2
    omega
  · simp only [blockEquiv_inr] at hlt hiff ⊢
    have h : b < a := (wEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inl τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_w]; exact genU_of_gt Ω (rk Ψ p q) (.inl τ) h⟩

theorem gMat_indep :
    AlgebraicIndependent Ω fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 := by
  choose e he₁ he₂ using exists_var (Ψ := Ψ) (p := p) (q := q) Ω
  have hinj : Function.Injective e := fun x y h => Subtype.ext (by rw [← he₁ x, ← he₁ y, h])
  have hX : AlgebraicIndependent Ω fun t : GenIx (rk Ψ p q) =>
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) :=
    (MvPolynomial.algebraicIndependent_X (GenIx (rk Ψ p q)) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)))
      (IsFractionRing.injective _ _)
  have e' : (fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2) =
      (fun t : GenIx (rk Ψ p q) =>
        algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t)) ∘ e :=
    funext he₂
  rw [e']
  exact hX.comp e hinj

theorem gMat_isGenericFlag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω],
    GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := fun _ _ _ _ Ω _ =>
  IsGenericFlag.of_lowerUni (fun τ => gMat_lowerUni Ω τ) (gMat_indep Ω)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTerm
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def segIxEquiv : ((k : K₀ ⊕ StepIx Ψ p q) → idx (p := p) (q := q) J₀ n k) ≃
    FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q) :=
  Equiv.sumPiEquivProdPi (idx (p := p) (q := q) J₀ n)

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  classical
  obtain ⟨hL, hc, hφ, hB⟩ := hF
  set r := rk (CMType H) D.p D.q with hr
  set x : ((k : K₀) → J₀ k) → Ω := seg x₀ with hxdef
  set cF := cc 𝔐 bW bO with hcF
  have hx : CoordTie ℤ 𝔐.ξ x := 𝔐.tie
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt 𝔐.ξ, specializes_refl _⟩
  have hB' : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (cF s l)) = 1 := hB
  obtain ⟨J₁, hJ₁, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω (EE 𝔐) (CMType H ⊕ CMType H) r n ((k : K₀) → J₀ k) x φ cF c₀ hc₀.1
    (GlobalTheory.T.function_field_ratio_generators 𝔐.X Ω 𝔐.ξ _ x c₀ hx hc₀.1) hB'
  have : Finite (FlagIx ((k : K₀) → J₀ k) n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.exists_cl_scheme (GenField Ω r) ℤ (FlagIx ((k : K₀) → J₀ k) n r) (flagCoord _ x φ cF) J₁ hJ₁ hfrac
  obtain ⟨f, hdom, hch⟩ := _root_.GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map 𝔐.X Ω 𝔐.ξ ℤ _ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simp [intCast_mem (regAt ξ' p') z]) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord _ x φ cF (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsm := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ x (CMType H ⊕ CMType H) r (VV 𝔐) (LL 𝔐) m n φ cF X' ξ' f hx 𝔐.all hL hφ hc
    hx' hirr' hdom hch
  have hseg : seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) =
      flagCoord ((k : K₀) → J₀ k) x φ cF ∘ segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀) := by
    funext c'
    show ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, c' k⟩ =
      algebraMap Ω (GenField Ω r) (∏ k, x₀ ⟨k, c' (.inl k)⟩) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (c' (.inr q)) (Fin.castLE q.2.2)).det
    rw [Fintype.prod_sum_type, map_prod]
    rfl
  refine ⟨X', ξ', f, ?_, hirr', hdom, hsm⟩
  rw [hseg]
  convert coordTie_comp_equiv hx' (segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀)) using 1 <;> exact Subsingleton.elim _ _
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBound
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar GlobalTheory.CompanionTheory.Ar.TieArith ReciprocityTheory.ChartRestriction.G.AI.I4

section Comparison₂

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {K : Type} [Fintype K] {J : K → Type}

theorem exists_chart (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) :
    ∃ c : ∀ k, J k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  obtain ⟨c, hchart⟩ := h.cover (genCpt ξ)
  exact ⟨c, fun k ↦ (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)⟩

theorem ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ratioField y c = ⊤ := by
  have hne : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, u, hu, -, rfl⟩ := FracChart.exists_eq_div_adjoin X Ω ξ _ (seg y) c h hne a
  exact div_mem (adjoin_le_ratioField y c hg) (adjoin_le_ratioField y c hu)

theorem trdeg_eq_of_ringKrullDim [∀ k, Fintype (J k)] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hdim : ringKrullDim (MRing J ⧸ mCoordIdeal y) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    Algebra.trdeg ℤ Ω = d := by
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = Algebra.trdeg ℤ Ω := by
    rw [hb]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  have h2 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat =
      ((d + Fintype.card K : ℕ) : ℕ∞) := by
    generalize (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat = e at h1
    cases e using ENat.recTopCoe with
    | top => exact absurd h1 (by rw [top_add]; exact (ENat.natCast_ne_top _).symm)
    | coe e =>
      have h3 : e + 1 = d + 1 + Fintype.card K := by exact_mod_cast h1
      have h4 : e = d + Fintype.card K := by omega
      rw [h4]
  have h5 : Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal) = ((d + Fintype.card K : ℕ) : Cardinal) :=
    Cardinal.toENat_eq_natCast.mp h2
  rw [Nat.cast_add] at h5
  exact (Cardinal.add_nat_inj _).mp h5

end Comparison₂

theorem isArithVar_xb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d _ hT hA
  obtain ⟨c₀, hc₀⟩ := exists_chart 𝔐.ξ x₀ 𝔐.tie
  obtain ⟨cb, hcb⟩ := exists_chart 𝔐.ξ _ hT
  have hd : Algebra.trdeg ℤ Ω = d :=
    trdeg_eq_of_ringKrullDim x₀ c₀ hc₀ (ratioField_eq_top 𝔐.ξ x₀ 𝔐.tie c₀ hc₀) d hA.2.2.2
  obtain ⟨k₀⟩ := hA.1
  have hK : Nonempty (NonPluckerBlocks (blkF (CMType H) D.p D.q K₀)) := by
    refine ⟨⟨.inl k₀, fun r ↦ ?_⟩⟩
    unfold blkF
    split <;> simp
  exact isArithVar_of_ratioField_eq_top _ cb hcb (ratioField_eq_top 𝔐.ξ _ hT cb hcb) d hd

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRank
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.FlagBun

section Map

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem isFrameAt_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {b : Fin r → E} {p : Cpt ξ} (h : L.IsFrameAt b p) : (L.map f).IsFrameAt (fun a => f (b a)) p := by
  refine ⟨h.1.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  show (L p).map (f.restrictScalars (regAt ξ p)) = _
  rw [h.2, Submodule.map_span, ← Set.range_comp]
  rfl

theorem isVB_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {V : Submodule Ω E} (h : L.IsVB r V) : (L.map f).IsVB r (V.map f) := by
  intro p hp
  obtain ⟨U, hU, b, hb, hq⟩ := h p hp
  refine ⟨U, hU, fun a => f (b a), ?_, fun q hqT hqU => isFrameAt_map_of_injective hf (hq q hqT hqU)⟩
  rw [← hb, Submodule.map_span, ← Set.range_comp]
  rfl

end Map

section Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

theorem inW_injective (A : HodgeCpt Y S x) : Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective (A : HodgeCpt Y S x) (τ : CMType H) : Function.Injective (inO A τ) := by
  intro a b h
  have e := congrFun (congrArg Prod.snd h) τ
  simpa [inO] using e

end Bundles

theorem LL_isVB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)
    (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 s
  rcases s with τ | τ
  · exact isVB_map_of_injective (inW_injective 𝔐) (𝔐.vb (.inl τ))
  · exact isVB_map_of_injective (inO_injective 𝔐 τ) (omBundle_isVB 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end
end

