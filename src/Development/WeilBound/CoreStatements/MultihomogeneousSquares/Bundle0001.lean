module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsMultiHomogRenameBaseInc
section
noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} (blk : σ → Option K)

def baseInc : (Σ k, baseIdx ι blk k) → Σ k, ι k := fun q => ⟨q.1.1, q.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem baseInc_injective : Function.Injective (baseInc (ι := ι) blk) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [baseInc, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl


open Classical in
def extDeg (b : NonPluckerBlocks blk → ℕ) : K → ℕ := fun k => if h : ∀ p, blk p ≠ some k then b ⟨k, h⟩ else 0

theorem isMultiHomog_rename_baseInc {β : MRing (baseIdx ι blk)} {b : NonPluckerBlocks blk → ℕ} (hβ : IsMultiHomog β b) :
    IsMultiHomog (rename (baseInc (ι := ι) blk) β) (extDeg blk b) := by
  classical
  intro m hm k
  rw [support_rename_of_injective (baseInc_injective blk)] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.1 hm
  by_cases h : ∀ p, blk p ≠ some k
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = m₀ ⟨⟨k, h⟩, i⟩ := fun i =>
      Finsupp.mapDomain_apply_of_injective (baseInc_injective blk) m₀ (⟨⟨k, h⟩, i⟩ : Σ k, baseIdx ι blk k)
    simp only [e, extDeg, dif_pos h]
    exact hβ m₀ hm₀ ⟨k, h⟩
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_of_notMem_range _ _ (by
        rintro ⟨q, hq⟩
        have : q.1.1 = k := congrArg Sigma.fst hq
        exact h (this ▸ q.1.2))
    simp only [e, extDeg, dif_neg h, Finset.sum_const_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem evC_rename_baseInc (z : (Σ k, ι k) → ℂ) (β : MRing (baseIdx ι blk)) :
    Cmp.evC z (rename (baseInc blk) β) = Cmp.evC (basePart blk z) β := by
  simp only [Cmp.evC, map_rename, eval_rename]
  rfl

end SlopeTestRemainingChoices

theorem alg_of : StEmb → StForm → StAlg := by
  intro hE hF E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie n d BM FA hH
  obtain ⟨β, b, hβ, hβn, hβz⟩ := hF E H D l Xo c Y S M.Ω (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐
  have hβ' := isMultiHomog_rename_baseInc M.blk hβ
  refine hE K ι (mCoordIdeal y) (d + 1) _ (FA.S.comap some) (FA.Re.comap some) (rename (baseInc M.blk) β)
    (extDeg M.blk b) FA.J_top FA.deg_one FA.br_empty hβ' ?_ ?_
  · rw [form_mem_mCoordIdeal_iff y hβ', aeval_rename]
    have e : y ∘ baseInc M.blk = algebraMap M.Ω Φ ∘ M.x := funext fun q => M.y_base q
    rw [e, aeval_algebraMap_apply]
    intro h0
    apply hβn
    rw [form_mem_mCoordIdeal_iff M.x hβ]
    exact (algebraMap M.Ω Φ).injective (by rw [h0, map_zero])
  · intro x hx
    have hx' : FA.pr (FA.Re.π x) ∈ ReciprocityTheory.AnForm.P.bdry BM.s := by
      have : FA.S.s (FA.Re.π x) (FA.Re.π x) = 0 := hx
      rw [FA.s_eq] at this
      exact this
    set xb := FA.pr (FA.Re.π x)
    have hmem : BM.Rb.lift xb xb ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem xb xb (BM.Rb.mem_U xb)
    obtain ⟨z, -, hz⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 hmem
    have hnot : ¬ 𝔐.Interior z := fun hI => ((hH.interior xb z hz).2 hI) hx'
    have h0 : Cmp.evC (BM.Rb.lift xb xb) β = 0 := hβz z _ hz hnot
    obtain ⟨c₀, -, hc⟩ := FA.pr_eq x
    show Cmp.evC (FA.Re.R.lift x x) (rename (baseInc M.blk) β) = 0
    rw [evC_rename_baseInc, hc]
    unfold Cmp.evC at h0 ⊢
    rw [eval_smul_homog β b hβ c₀, h0, mul_zero]

end SquareStatements
end
end

-- bundled from Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
section
noncomputable section

namespace SquareStatements.Sing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt)
open scoped ComplexOrder

def col (p q : ℕ) (m : Fin (p + q)) : Fin (p + q) :=
  if h : (m : ℕ) < p then wEmb p q ⟨m, h⟩ else omEmb p q ⟨m - p, by have := m.2; omega⟩

def revDual {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ := (Aᵀ⁻¹).submatrix Fin.rev Fin.rev

def grN {r : ℕ} (Γ : Matrix (Fin r) (Fin r) ℂ) (k : ℕ) : ℝ := Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k)

def mu (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (m : Fin (p + q)) : ℝ :=
  if (m : ℕ) < p then grN (wBlock Γ) m else (grN (revDual (omBlock Γ)) (p + q - 1 - m))⁻¹

def C4 : Prop :=
  ∀ (p q : ℕ) (G h : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), IsBlockDiag p G → G.PosDef → IsBlockDiag p h → h.det ≠ 0 →
    (∀ m, 0 < mu p q (hᴴ * G * h) m) ∧ ∀ i : Fin (p + q), detFac p i h ≠ 0 ∧
      ∑ m ∈ Finset.Iic i, Real.log (mu p q (hᴴ * G * h) m) = blockPot p i G h + Real.log ‖detFac p i h‖

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

def Tot (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) : Prop :=
  HodgeOver 𝔐' 𝔐 pr (algebraMap M.Ω Φ) j ∧ (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) ∧
    (∀ τ (k : Fin D.p), Fl.b (.inl τ) k = colFrame (fun a => j (tie.eW τ a)) (wBlock (M.g τ)) k) ∧
    ∀ τ (v : Fin D.q → 𝔐.Vgen (.inr τ)), (∀ a b, tie.eO τ a (v b) = if a = b then 1 else 0) →
      ∀ k : Fin D.q, Fl.b (.inr τ) k = colFrame (fun a => j (v a)) (omBlock (M.g τ))ᵀ⁻¹ k.rev

def inFrame (M : FlagModel y (CMType H) (D.p + D.q) D.p) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk)
    (τ : CMType H) (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ :=
  ((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ * B

def Adapted (𝔐' : HodgeCpt Y S y) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X) (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ)
    (h : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) : Prop :=
  IsBlockDiag D.p B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsBlockDiag D.p h ∧ h.det ≠ 0 ∧
    ∀ a b, ValAt 𝔐'.ξ z (inFrame M F τ B a b) (h a b)

end

def C0 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (𝔐' : HodgeCpt Y S y)
    (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X) (w : (Σ k, ι k) → ℂ),
    HodgeOver 𝔐' 𝔐 pr (algebraMap M.Ω Φ) j → CoordsAt 𝔐'.ξ y z w →
    CoordsAt 𝔐.ξ M.x (z ≫ pr) (basePart M.blk w) ∧ (𝔐'.Interior z ↔ 𝔐.Interior (z ≫ pr)) ∧
      (∀ a r, ValAt 𝔐.ξ (z ≫ pr) a r → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ a) r) ∧
      ∀ s, RegAt M.x (mCoordIdeal (basePart M.blk w)) s →
        ValAt 𝔐'.ξ z (algebraMap M.Ω Φ s) (valAt M.x s (basePart M.blk w))

def C1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y)
    (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H),
    Tot tie 𝔐' Fl pr j → M.IsFrame F → (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ →
    (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ → ∃ B h, Adapted 𝔐' F τ z B h

def C2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐' : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (wb : (Σ k, baseIdx ι M.blk k) → ℂ) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) (h : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
    M.IsFrame F → M.GoodAt F (mCoordIdeal wb) →
    (∀ s, RegAt M.x (mCoordIdeal wb) s → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ s) (valAt M.x s wb)) →
    (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → Adapted 𝔐' F τ z B h → ∀ i : Fin (D.p + D.q),
    (∀ k, M.blk (τ, i) = some k → ∀ m : ι k,
      ValAt 𝔐'.ξ z ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) * y ⟨k, m⟩ *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k'))
        (detFac D.p i h * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I (stepCols (D.p + D.q) D.p i))) ∧
    (M.blk (τ, i) = none → valAt M.x (F.υ (τ, i)) wb ≠ 0 ∧
      ValAt 𝔐'.ξ z ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) *
          algebraMap M.Ω Φ (M.lam (τ, i)) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k'))
        (detFac D.p i h * valAt M.x (F.υ (τ, i)) wb))

def C5 : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type)
    (N j : ℕ) (M : FlagModel y Ψ N j) (wb : (Σ k, baseIdx ι M.blk k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk)
    (h : Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), wb ∈ mcPts (mCoordIdeal M.x) →
    M.IsFrame F → M.GoodAt F (mCoordIdeal wb) → IsBlockDiag j h → h.det ≠ 0 → M.blk p = some k →
    ∃ m : ι k, ∑ I, valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I (stepCols N j p.2) ≠ 0

def GradedLineNormsW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y)
    (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) (h G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
    Tot tie 𝔐' Fl pr j → M.IsFrame F → (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ →
    Adapted 𝔐' F τ z B h → IsBlockDiag D.p G → G.PosDef → 𝔐'.Interior z →
    𝔐.M.GramAt 𝔐.t.PP.L (z ≫ pr) (tie.wFrame F τ) (wBlock G) → ∀ k : Fin D.p,
      𝔐'.M.IsGrNorm 𝔐'.t.PP.L (𝔐'.V (.inl τ)) (Fl.b (.inl τ)) k z (B (wEmb D.p D.q k) (wEmb D.p D.q k))
        (grN (wBlock (hᴴ * G * h)) k)

def GradedLineNormsDualOmega : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y)
    (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) (h G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
    Tot tie 𝔐' Fl pr j → M.IsFrame F → (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ →
    Adapted 𝔐' F τ z B h → IsBlockDiag D.p G → G.PosDef → 𝔐'.Interior z →
    DualGramAt 𝔐.M 𝔐.t.PP.L (z ≫ pr) (𝔐.Vgen (.inr τ)) (tie.omFrame F τ) (omBlock G) → ∀ k : Fin D.q,
      𝔐'.M.IsGrNorm 𝔐'.t.PP.L (𝔐'.V (.inr τ)) (Fl.b (.inr τ)) k z (B (omEmb D.p D.q k.rev) (omEmb D.p D.q k.rev))⁻¹
        (grN (revDual (omBlock (hᴴ * G * h))) k)

end SquareStatements.Sing
end
end

-- bundled from Development.WeilBound.CoreStatements.MultihomogeneousSquares.SmoothComb
section
noncomputable section

namespace SquareStatements

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem smooth_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (Top.combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  refine contDiffOn_prod fun j _ => ?_
  rcases n j with m | m
  · simpa using (h j).pow m
  · simp only [zpow_negSucc]
    exact ((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'

theorem stXB : StX := by
  intro Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc
  classical
  let cl : ℝ → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀
  have hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀ := fun t => by
    by_cases h : 0 < t ∧ t ≤ S.t₀
    · simp only [cl, if_pos h]; exact h
    · simp only [cl, if_neg h]; exact ⟨h0, le_rfl⟩
  refine ⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_,
    fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩
  · funext k
    have h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k := fun a => by
      rw [Re.line_deg, hd]
      show (∑ r, _ • (sing r).a) k = _
      rw [RootFieldNumerics.Sq.sum_fundOnRoot]
      simp [Finset.sum_apply]
    have h2 := RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)
    show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, h1, smul_eq_mul]
    simp only [zsmul_eq_mul] at h2
    exact_mod_cast h2
  · show ∏ a, _ = ∏ a, _
    exact Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]
  · filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _
    have : cl t = t := if_pos ⟨ht.1, ht.2.le⟩
    rw [this]

end SquareStatements
end
end

