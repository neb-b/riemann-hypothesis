module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewAdjointCasimirSpectral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev Bk (n : Fin (m + 1) → ℕ) : Fin (m + 1) → Type := fun c => Fin (n c + 1)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev prB (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) : MP ℤ m n ⟶ PSpace ℤ (n k) := pr ℤ m n k

abbrev blockChart (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) (i : Bk n k) : (MP ℤ m n).Opens :=
  prB n k ⁻¹ᵁ chart ℤ (n k) i

def mchart (c : ∀ k, Bk n k) : (MP ℤ m n).Opens :=
  ⟨⋂ k, (blockChart n k (c k) : Set (MP ℤ m n)),
    isOpen_iInter_of_finite fun k => (blockChart n k (c k)).isOpen⟩

theorem mchart_le (c : ∀ k, Bk n k) (k : Fin (m + 1)) : mchart c ≤ blockChart n k (c k) :=
  fun _ hx => Set.mem_iInter.1 hx k

def blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) : Γ(MP ℤ m n, W)ˣ :=
  res h (pullU (prB n k) _ (ratioUnit _ i j inf_le_left inf_le_right))

def ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : Bk n k :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose

theorem mem_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : x ∈ blockChart n k (ptChart x k) :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose_spec

def ptCoord (x : MP ℤ m n) (p : Σ k, Bk n k) : (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (blockChart n p.1 (ptChart x p.1)) x (mem_ptChart x p.1)).hom
    (pullRatio (prB n p.1) _ (ptChart x p.1) le_rfl p.2)

def ptIdeal (x : MP ℤ m n) : Ideal (Geo.MRing (Bk n)) := Geo.mCoordIdeal (ptCoord x)

def IsUnder (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) : Prop :=
  ∀ (k : Fin (m + 1)) (i : Bk n k), (y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0) ∧
    ∀ j : Bk n k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) →
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y = z ⟨k, j⟩ / z ⟨k, i⟩

def IsHermRep (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) : Prop :=
  ∃ u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) ∧
    ∀ (i : M.B.ι) (c : ∀ k, Bk n k) (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder y z →
      y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) →
      A.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) *
        ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
          Real.exp ((M.φ σ₀).φ i y / 2)

abbrev consN (n' : ℕ) (n : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ := Fin.cons n' n

def sv (n' : ℕ) (n : Fin (m + 1) → ℕ) : (Σ k, Bk n k) → Σ k', Bk (consN n' n) k' :=
  fun p => ⟨p.1.succ, p.2⟩

theorem isBlockMap_sv (n' : ℕ) (n : Fin (m + 1) → ℕ) :
    IsBlockMap (ι := Bk n) (ι' := Bk (consN n' n)) Fin.succ (sv n' n) := by
  refine ⟨Fin.succ_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', j⟩ h
    have hk : k.succ = k'.succ := congrArg Sigma.fst h
    obtain rfl : k = k' := Fin.succ_injective _ hk
    have h' : (⟨k.succ, i⟩ : Σ k', Bk (consN n' n) k') = ⟨k.succ, j⟩ := h
    have hij : i = j := sigma_mk_injective (β := Bk (consN n' n)) (i := k.succ) h'
    rw [hij]
  · rintro ⟨k', j⟩ ⟨k, rfl⟩
    exact ⟨⟨k, j⟩, rfl⟩

def pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) : Geo.HermLine (Bk (consN n' n)) where
  a := pullDeg Fin.succ A.a
  h z := A.h fun p => z (sv n' n p)
  pos z hz := A.pos _ fun k => hz k.succ
  smul c z hc := by
    have e := A.smul (fun k => c k.succ) (fun p => z (sv n' n p)) fun k => hc k.succ
    refine e.trans ?_
    have h0 : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a 0 = 0 := by
      unfold pullDeg
      rw [Function.extend_apply']
      · rfl
      · rintro ⟨k, hk⟩
        exact Fin.succ_ne_zero k hk
    have hs (k : Fin (m + 1)) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a k.succ = A.a k :=
      (Fin.succ_injective _).extend_apply _ _ _
    rw [Fin.prod_univ_succ (fun k' => ‖c k'‖ ^ pullDeg Fin.succ A.a k'), h0, zpow_zero, one_mul]
    simp only [hs]

theorem isPullHerm_pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) :
    IsPullHerm Fin.succ (sv n' n) A (pullLine n' A) :=
  ⟨rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAll
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Grams

theorem sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n d b T hT
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (b k)
  have hJ' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (J i j)
  have hT' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ a c, inclR (F := F) (Fv F v) (T a c) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun c => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (T a c)
  have htr : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (Algebra.trace F E (b k))
  filter_upwards [Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (F := F) (1 / 2), hb, hJ', hT', htr,
    Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_crd_oev (E := E) b] with v hh hbv hJv hTv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ a i, X a i ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a i
    rw [hrepr (X a i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Formalism.L2.SG.Pf.NcS.IntWittPf.oev_smul' v (hX a i k) (hbv k)
  have hG : ∀ a c, hR (Fv F v) σ J (X a) (X c) ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    show ∑ i, ∑ j, sigR (Fv F v) σ (X a i) * JR (Fv F v) J i j * X c j ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (Formalism.L2.SG.Pf.NcS.IntWittPf.oev_sigR v σ (hx a i)) (hJv i j)) (hx c j)
  have hS : ∀ a c, ((hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X :
      HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    exact sub_mem (hTv a c) (hG a c)
  have htrace : ∀ z ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
    intro z hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrepr z, map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hz k) (htrv k)
  exact ⟨fun i => mul_mem hh (htrace _ (hS i i)), fun i j _ k => hc _ (hS i j) k⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.Grams
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Period

variable {D : D7}

theorem rat_sub' {m n : ℕ} (p p₀ : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (p - p₀) : Mx D m n) = rat p - rat p₀ := by
  ext i j
  simp [rat]

theorem psi_inner_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    ψ (trA (Matrix.trace (inner V (rat q) (rat q₀)))) = 1 := by
  have h : (inner V (rat q) (rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀)) := by
    change (adj (rat q) ⬝ (gA V ⬝ rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀))
    rw [rat_mul, rat_mul, rat_conjTranspose, gA]
  have ht : ∀ M : Matrix (Fin s) (Fin s) D.host.E,
      Matrix.trace (rat M : Mx D s s) = incA D (Matrix.trace M) := fun M => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [h, ht, GlobalTheory.CompanionTheory.ThetaInv.trA_incA]
  exact hψ.2.2.1 _

theorem inner_add_right' (V : HSp D) {s : ℕ} (x y z : Mx D V.rank s) :
    (inner V x (y + z) : Mx D s s) = inner V x y + inner V x z := by
  change (adj x ⬝ (gA V ⬝ (y + z)) : Mx D s s) = adj x ⬝ (gA V ⬝ y) + adj x ⬝ (gA V ⬝ z)
  simp [Matrix.mul_add]

theorem trA_add' (x y : AE D) : trA (x + y) = trA x + trA y := by
  simp [trA]

theorem term_shift {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ)
    (p p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    cellTerm ψ V b a Φ p q (y₁ + rat p₀) (y₂ + rat q₀) = cellTerm ψ V b a Φ (p - p₀) q y₁ y₂ := by
  have e₁ : y₁ + rat p₀ - rat p = y₁ - rat (p - p₀) := by rw [rat_sub']; abel
  have e₂ : rat p - (y₁ + rat p₀) = rat (p - p₀) - y₁ := by rw [rat_sub']; abel
  have e₃ : ψ (trA (Matrix.trace (inner V (rat q) (y₂ + rat q₀)))) =
      ψ (trA (Matrix.trace (inner V (rat q) y₂))) := by
    rw [inner_add_right', Matrix.trace_add, trA_add', AddChar.map_add_eq_mul, psi_inner_rat hψ, mul_one]
  unfold cellTerm
  rw [e₁, e₂, e₃]

theorem tsum_cellTerm_add_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  intro D ψ hψ V r s b a Φ p₀ q₀ y₁ y₂
  simp only [term_shift hψ]
  exact (Equiv.prodCongr (Equiv.subRight p₀) (Equiv.refl _)).tsum_eq
    (fun pq => cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂)

end GlobalTheory.CompanionTheory.EisUnfold.Period

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiePowerL2FactorialBound
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.AnalyticBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Restricts (W : Submodule ℂ (Sm E a)) (T' : Module.End ℂ W) (T : Module.End ℂ (Sm E a)) : Prop :=
  ∀ v : W, ((T' v : W) : Sm E a) = T v

namespace Restricts

variable {W : Submodule ℂ (Sm E a)} {A' B' : Module.End ℂ W} {A B : Module.End ℂ (Sm E a)}

theorem mul (hA : Restricts W A' A) (hB : Restricts W B' B) : Restricts W (A' * B') (A * B) := fun v => by
  simp only [Module.End.mul_apply]
  rw [hA, hB]

theorem sub (hA : Restricts W A' A) (hB : Restricts W B' B) : Restricts W (A' - B') (A - B) := fun v => by
  simp only [LinearMap.sub_apply, Submodule.coe_sub]
  rw [hA, hB]

theorem smul (c : ℂ) (hA : Restricts W A' A) : Restricts W (c • A') (c • A) := fun v => by
  simp only [LinearMap.smul_apply, Submodule.coe_smul]
  rw [hA]

theorem one : Restricts W (1 : Module.End ℂ W) (1 : Module.End ℂ (Sm E a)) := fun _ => rfl

theorem pow (hA : Restricts W A' A) (k : ℕ) : Restricts W (A' ^ k) (A ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hA

theorem sum {ι : Type} (s : Finset ι) {f' : ι → Module.End ℂ W} {f : ι → Module.End ℂ (Sm E a)}
    (h : ∀ i, Restricts W (f' i) (f i)) : Restricts W (∑ i ∈ s, f' i) (∑ i ∈ s, f i) := fun v => by
  simp only [LinearMap.sum_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun i _ => h i v

theorem ext_of_eq (hA : Restricts W A' A) (hB : Restricts W B' B) (e : A = B) : A' = B' :=
  LinearMap.ext fun v => Subtype.ext (by rw [hA, hB, e])

end Restricts

theorem real_smul_end (r : ℝ) (T : Module.End ℂ (Sm E a)) : r • T = (r : ℂ) • T := by
  ext φ g
  simp [Complex.real_smul]

theorem lie_sum {ι : Type} [Fintype ι] (Z : ι → GlobalTheory.CuspRep.Lie E a) (r : ι → ℝ) :
    lie E a (∑ l, r l • Z l) = ∑ l, (r l : ℂ) • lie E a (Z l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_smul, real_smul_end]

theorem exists_coords {W Y : Submodule ℂ (Sm E a)} (hYW : Y ≤ W) {m : ℕ} (b : Module.Basis (Fin m) ℂ Y)
    {T' : Module.End ℂ W} {T : Module.End ℂ (Sm E a)} (hI : Restricts W T' T) (hT : ∀ u ∈ Y, T u ∈ Y) :
    ∃ d : Fin m → Fin m → ℂ, ∀ e, T' ⟨(b e).1, hYW (b e).2⟩ = ∑ f, d e f • (⟨(b f).1, hYW (b f).2⟩ : W) := by
  refine ⟨fun e f => b.repr ⟨T (b e).1, hT _ (b e).2⟩ f, fun e => Subtype.ext ?_⟩
  rw [hI]
  have h := congrArg (Subtype.val) (b.sum_repr ⟨T (b e).1, hT _ (b e).2⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h ⊢
  exact h.symm

theorem mem_span_basis {W Y : Submodule ℂ (Sm E a)} (hYW : Y ≤ W) {m : ℕ} (b : Module.Basis (Fin m) ℂ Y)
    {φ : Sm E a} (hφ : φ ∈ Y) :
    (⟨φ, hYW hφ⟩ : W) ∈ Submodule.span ℂ (Set.range fun e => (⟨(b e).1, hYW (b e).2⟩ : W)) := by
  have h := congrArg (Subtype.val) (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  have e : (⟨φ, hYW hφ⟩ : W) = ∑ f, b.repr ⟨φ, hφ⟩ f • (⟨(b f).1, hYW (b f).2⟩ : W) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact h.symm
  rw [e]
  exact Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)

theorem factorial_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E a)), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) → ∀ φ ∈ W, ∀ X : GlobalTheory.CuspRep.Lie E a, ∃ M C : ℝ, ∀ (k : ℕ) (h : MemL2Quotient (latticeGL E a) μ (((lie E a X) ^ k) φ).1), ‖h.toL2‖ ≤ M * C ^ k * (k.factorial : ℝ) := by
  intro E _ _ _ a μ _ _ W hW hA φ hφ X
  obtain ⟨ι, _, _, Z, K, hspan, hskewK, hΩ⟩ := _root_.GlobalTheory.CompanionTheory.CasFamily.exists_family E a
  have hL : ∀ (X : GlobalTheory.CuspRep.Lie E a), ∀ ψ ∈ W, lie E a X ψ ∈ W := fun X ψ h => hW (.lie X) ψ h
  have hm : ∀ ψ ∈ W, MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ h => (hA ψ h).2
  have hc : ∀ ψ ∈ W, Continuous ψ.1 := fun ψ h =>
    ContAut.continuous_of_isOpen_stab E a ψ (hA ψ h).1.level
  have hreal : ∀ X : GlobalTheory.CuspRep.Lie E a, ∃ r : ι → ℝ, ∑ l, r l • Z l = X := fun X => by
    have hX : X ∈ Submodule.span ℝ (Set.range Z) := by rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  let Zop : ι → Module.End ℂ W := fun i => (lie E a (Z i)).restrict (hL (Z i))
  have hZ : ∀ i, Restricts W (Zop i) (lie E a (Z i)) := fun i v => rfl
  let j := toL2ₗ μ W hm
  have hskew : ∀ i v w, inner ℂ (j (Zop i v)) (j w) = - inner ℂ (j v) (j (Zop i w)) := fun i v w =>
    _root_.GlobalTheory.CompanionTheory.LieSkew.lie_skew E a μ (Z i) v.1 w.1 (hm _ v.2) (hm _ w.2) (hm _ (hL _ _ v.2)) (hm _ (hL _ _ w.2))
      (hc _ v.2) (hc _ w.2) (hc _ (hL _ _ v.2)) (hc _ (hL _ _ w.2))
  choose r hr using fun (p : ι × ι) => hreal (toL (of (Z p.1) * of (Z p.2)) - toL (of (Z p.2) * of (Z p.1)))
  have hcomm : ∀ κ i, Zop κ * Zop i - Zop i * Zop κ = ∑ l, ((r (κ, i) l : ℝ) : ℂ) • Zop l := fun κ i => by
    refine Restricts.ext_of_eq (((hZ κ).mul (hZ i)).sub ((hZ i).mul (hZ κ)))
      (Restricts.sum _ fun l => (hZ l).smul _) ?_
    rw [lie_comm, ← map_sub, ← hr (κ, i), lie_sum]
  set Ω₀ : Module.End ℂ (Sm E a) :=
    ∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ) with hΩ₀
  set S₀ : Module.End ℂ (Sm E a) := ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ) with hS₀
  have hSI : Restricts W (∑ κ ∈ K, Zop κ * Zop κ) S₀ := Restricts.sum _ fun κ => (hZ κ).mul (hZ κ)
  have hΩI : Restricts W (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) Ω₀ :=
    (Restricts.sum _ fun κ => (hZ κ).mul (hZ κ)).sub hSI
  have hcentral : ∀ i, (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) * Zop i
      = Zop i * (∑ i ∈ Kᶜ, Zop i * Zop i - ∑ κ ∈ K, Zop κ * Zop κ) := fun i =>
    Restricts.ext_of_eq (hΩI.mul (hZ i)) ((hZ i).mul hΩI) (_root_.GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie E a Ω₀ hΩ (Z i))
  obtain ⟨Y, hfd, hYW, hφY, hZY, hKY⟩ := _root_.GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable E a W hW (fun ψ h => (hA ψ h).1) φ hφ
  let b := Module.finBasis ℂ Y
  have hSY : ∀ u ∈ Y, S₀ u ∈ Y := fun u hu => by
    rw [hS₀, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun κ hκ => hKY _ (hskewK κ hκ) _ (hKY _ (hskewK κ hκ) _ hu)
  have hΩY : ∀ u ∈ Y, Ω₀ u ∈ Y := fun u hu => hZY _ hΩ _ hu
  obtain ⟨d, hd⟩ := exists_coords hYW b hSI hSY
  obtain ⟨o, ho⟩ := exists_coords hYW b hΩI hΩY
  obtain ⟨x, hx⟩ := hreal X
  have hT : Restricts W (∑ i, ((x i : ℝ) : ℂ) • Zop i) (lie E a X) := by
    rw [← hx, lie_sum]
    exact Restricts.sum _ fun l => (hZ l).smul _
  obtain ⟨M, C, hMC⟩ := _root_.GlobalTheory.CompanionTheory.AnalyticWord.analytic_bound W (L2 (latticeGL E a) μ) j ι Zop K _
    (fun e => (⟨(b e).1, hYW (b e).2⟩ : W)) d o (fun κ i l => ((r (κ, i) l : ℝ) : ℂ))
    hskew hcomm hcentral hd ho (fun i => (x i : ℂ)) ⟨φ, hφ⟩ (mem_span_basis hYW b hφY)
  refine ⟨M, C, fun k h => ?_⟩
  have key : ∀ (w : W) (f : Sm E a) (_ : w.1 = f) (h : MemL2Quotient (latticeGL E a) μ f.1), j w = h.toL2 := by
    rintro ⟨w, hw⟩ f rfl h
    rfl
  rw [← key _ _ ((hT.pow k) ⟨φ, hφ⟩) h]
  exact hMC k

end GlobalTheory.CompanionTheory.AnalyticBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDependentSetNull
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree

theorem linearIndependent_of_isUnit_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [Field R] [Algebra F R] (X : Fin 1 → Fin M → R ⊗[F] E)
    (hu : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : LinearIndependent (R ⊗[F] E) X := by
  classical
  have hfix : HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0) :=
    GlobalTheory.CompanionTheory.SW.FibreRatio.sigR_hR_self R hσ hJ (X 0)
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.SW.FibreRatio.fixed_tmul R hσ _ hfix
  have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = r := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR
    rw [hr]
    exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul R hσ r
  have hr0 : r ≠ 0 := by
    rw [← hq]
    exact hu.ne_zero
  have hunit : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0)) := by
    rw [hr]
    exact GlobalTheory.CompanionTheory.SW.FibreRatio.isUnit_tmul R hr0
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  set a := g 0 with ha_def
  have ha' : a • X 0 = 0 := by simpa [Fin.sum_univ_one] using hg
  have hlin : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (a • X 0) =
      a * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0) := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hzero : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (0 : Fin M → R ⊗[F] E) = 0 := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [ha', hzero] at hlin
  exact (hunit.mul_left_eq_zero).1 hlin.symm

theorem null_nonfree : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → coordW (Fv F v) b lam 1 M {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hh := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  have h0 := (NullV.null_nonunits F E σ hσ M J hJ hM v (coordW (Fv F v) b lam 1 M) lam (hh.2.1 1 M) hlam.1).2
  refine measure_mono_null ?_ h0
  intro X hX hu
  exact hX (linearIndependent_of_isUnit_qR hσ hJ (Fv F v) X hu)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightEx
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.WeightExist

theorem weightEx : PositivityTheory.Rg.BcB.F.WeightEx :=
  fun E _ _ _ n π hπ τ => (_root_.GlobalTheory.DefU.AU.existsUnique_hasWt E n (GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.CompanionTheory.WeightExist
end

