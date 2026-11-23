module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrExtract
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.FixedLevelIsolate

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

end GlobalTheory.FixedLevelIsolate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiFlatMapSupportFiniteCells
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.LocFlat.CellSupport

theorem det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, colE, upU, Matrix.det_fromBlocks_zero₂₁]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_inv_of_det_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL b k) (hg : Matrix.GeneralLinearGroup.det g = 1) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) g⁻¹ Ψ = fun z => Ψ (g.val * z) := by
  funext z
  simp only [om, map_inv, hg, inv_one, map_one, nabs_one, inv_inv, Real.one_rpow, Units.val_one, Complex.ofReal_one,
    one_mul, Matrix.mul_one]

theorem om_eq_mul_om_triv {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) h Ψ = fun z => (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * om 1 (1 : GL a k) h Ψ z := by
  funext z
  simp only [om, map_one, MonoidHom.one_apply, inv_one, Units.val_one]
  ring

theorem opE_const_mul [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (s : ℂ)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => s * Ψ z) x₀ = s * opE ψ ν p Ψ x₀ := by
  unfold opE
  rw [← integral_const_mul]
  simp only [mul_assoc]

end GlobalTheory.LocFlat.CellSupport

namespace GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CellSupport

theorem flCol_support_finite_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p →
    p ≤ c → ∀ (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (a : GL (n' ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n ⊕ Fin c) k), ∀ x : GL (n ⊕ Fin c) k, GlobalTheory.LocFlat.flCol ψ ν p (om μ a x Φ.1) ≠ 0 →
      ∃ β : n → k, ∃ r ∈ R k n c p, ∃ t ∈ T, ∃ j ∈ J, x = colE c p β * r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ ν hν n n' _ _ _ _ c p hp1 hpc μ J hJ Φ a
  obtain ⟨T, -, hT⟩ := GlobalTheory.PosOne.covers_opE_finite k n n' c p hp1 hpc ψ hψc hψ ν 1
    (by rw [MonoidHom.ker_one]; exact isOpen_univ) J hJ ⟨om μ a 1 Φ.1, om_mem_SB μ a 1 Φ.2⟩
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨X, hX⟩ := Function.ne_iff.1 hx
  rw [flCol_eq_opE_colE k ψ ν hψc hν n n' c p hp1 hpc _ (om_mem_SB μ a x Φ.2) X] at hX
  set β : n → k := fun r => X r (Sum.inr ()) with hβ
  replace hX : opE ψ ν p (om μ 1 (colE c p β)⁻¹ (om μ a x Φ.1)) X.toCols₁ ≠ 0 := by
    rw [om_inv_of_det_one μ _ (det_colE c p β)]
    exact hX
  rw [← om_mul] at hX
  have e : om μ (1 * a) ((colE c p β)⁻¹ * x) Φ.1 = om μ 1 ((colE c p β)⁻¹ * x) (om μ a 1 Φ.1) := by
    rw [← om_mul, mul_one]
  rw [e, om_eq_mul_om_triv, opE_const_mul] at hX
  obtain ⟨t, ht, hd⟩ := hT ((colE c p β)⁻¹ * x) (Function.ne_iff.2 ⟨X.toCols₁, right_ne_zero_of_mul hX⟩)
  obtain ⟨r, hr, j, hj, hx'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hd.symm
  refine ⟨β, r, hr, t, ht, j, hj, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_assoc r, ← hx', mul_inv_cancel_left]

end GlobalTheory.LocFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GeneratorMemSplitPrimeLevelPrimeMemPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.GenOver


open GlobalTheory.AdForm.PlacesDistinct in
theorem mem_place_of_mem_prime {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w)
    (x : 𝓞 D.host.F) (y : 𝓞 D.host.E) (hxy : (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F))
    (hy : y ∈ w.asIdeal) : x ∈ p.v.asIdeal := by
  by_contra hxv
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ p.v.asIdeal.zero_mem)
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    have : algebraMap D.host.F D.host.E (x : D.host.F) = 0 := by rw [← hxy, h]; rfl
    rw [map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective] at this
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  apply (hI.2 y hy0).1 hy
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.e = p.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hsum, mul_add, p.split.1, p.split.2.1, add_zero]
  set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) ((x : D.host.F)⁻¹) with hc
  have hinc : incA D ((y : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) c := by
    rw [hxy, ← map_inv₀, hc]
    show Algebra.TensorProduct.includeRight _ = _
    exact (Algebra.TensorProduct.includeRight.commutes _).trans (IsScalarTower.algebraMap_apply _ _ _ _)
  have h2 : finPart D (algebraMap (AF D.host.F) (AE D) (ε * c)) ∈ intAE D := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hf : finPart D ((ε * c) ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F (ε * c) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hf]
    refine AddSubgroup.subset_closure ⟨sndA D.host.F (ε * c), ?_, 1, by simp⟩
    intro v'
    obtain ⟨α, rfl, h1, h0⟩ := hε
    have hs : sndA D.host.F (pairA D.host.F 0 α * c) = α * algebraMap D.host.F (Af D.host.F) ((x : D.host.F)⁻¹) := by
      rw [map_mul, hc, AlgHom.commutes]; rfl
    rw [hs, map_mul, AlgHom.commutes]
    by_cases hv : v' = p.v
    · subst hv
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
      have hv1 : Valued.v (algebraMap D.host.F (Fv D.host.F p.v) (x : D.host.F)) = 1 := by
        have := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.F) p.v x
        refine this.trans ?_
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hxv
      rw [hv1, inv_one]
    · rw [h0 v' hv, zero_mul]
      exact zero_mem _
  rw [hinc, he, mul_assoc, ← map_mul, map_mul]
  exact FrameLat.mul_mem_intAE (finPart_idem_int hI) h2

theorem natCast_mem_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w) (n : ℕ)
    (hn : (n : 𝓞 D.host.E) ∈ w.asIdeal) : (n : 𝓞 D.host.F) ∈ p.v.asIdeal :=
  mem_place_of_mem_prime p hI (n : 𝓞 D.host.F) (n : 𝓞 D.host.E) (by simp) hn

end GlobalTheory.AdForm.GenOver


open GlobalTheory.AdForm.GenOver in
theorem GlobalTheory.AdForm.piT_mem_and_T_mem_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k) (P : (B.primes X).vT u), Formalism.L2.NTheta.IsIdemAt p.e P.1 → X.piT u ∈ P.1.asIdeal ∧ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal := by
  intro B X I _ l Z u k _ _ _ _ p P hI
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h1 : X.piT u ∈ P.1.asIdeal := (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).1 P.2
  have hT : ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ P.1.asIdeal := by
    have : X.piT u * B.fields.conjO (X.piT u) = ((B.T u : ℕ) : 𝓞 B.fields.E) := hPr.piT_norm u
    rw [← this]
    exact Ideal.mul_mem_right _ _ h1
  exact ⟨h1, natCast_mem_place p hI (B.T u) hT⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientNeOneCompletelySplitPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotVal

theorem val_quot_ne_one : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∀ p : ℕ,
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    w.under (𝓞 D.host.F) ∉ c.S → GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w ≠ 1 := by
  intro D c hc i j hi hij hj p hp w hw hS h1
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  have hoff : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hS
  refine GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity D (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹)
    (GlobalTheory.Chain.isHeckeChar_div (QuotL.isHecke hc (by omega) (by omega)) (QuotL.isHecke hc (by omega) hj))
    (fun τ => ⟨_, ?_, GlobalTheory.Chain.hasInfExp_div (hc.exp ⟨i', by omega⟩ τ) (hc.exp ⟨j', by omega⟩ τ)⟩) p hp w hw
    ((hc.unr ⟨i', by omega⟩ w hoff).mul (hc.unr ⟨j', by omega⟩ w hoff).inv) ?_
  · have := QuotL.e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
      Fin.mk_lt_mk.2 (by omega))
    intro h0
    linarith
  · rw [h1]
    exact IsOfFinOrder.one

end GlobalTheory.ChainOnto.QuotVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorFinitePartRestActsBySemicharac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HalfARest

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem natsmul_mem_twO' (L : Submodule (𝓞 E) W) (c : ℕ) (e e' : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e' Q ≤ e Q + 1)
    {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ L c e) : (c : 𝓞 E) • x ∈ Formalism.L2.Ker.twist₂ L c e' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e Q + 1 - e' Q := ⟨(e Q + 1 - e' Q).toNat, Int.toNat_of_nonneg (by linarith [he Q])⟩
  have key : ((c : E) ^ e' Q)⁻¹ • ((c : 𝓞 E) • x) = ((c : 𝓞 E) ^ n) • (((c : E) ^ e Q)⁻¹ • x) := by
    rw [← IsScalarTower.algebraMap_smul E ((c : 𝓞 E) ^ n), ← IsScalarTower.algebraMap_smul E (c : 𝓞 E) x, smul_smul, smul_smul]
    congr 1
    simp only [map_pow, map_natCast]
    rw [← _root_.zpow_neg, ← _root_.zpow_neg, ← zpow_natCast, hn, ← zpow_add_one₀ hcE, ← zpow_add₀ hcE]
    congr 1; ring
  rw [key]
  exact Submodule.smul_mem _ _ (hx Q)

theorem mem_twO_zero' (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) : x ∈ Formalism.L2.Ker.twist₂ M c (fun _ => 0) ↔ x ∈ M := by
  rw [Formalism.L2.Ker.mem_twO]
  simp only [zpow_zero, inv_one, one_smul]
  exact ⟨fun h => Formalism.L2.Ker.mem_of_forall_locP M h, fun h Q => Formalism.L2.Ker.le_locP' M Q h⟩

end Tw


open GlobalTheory.LatVac in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heisO_rest_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) f₀ = alV D.host.d sc (embH (tauE D) δ x') • f₀ := by
  intro D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd c hc hcP f₀ hV x' hx
  set X := LinearMap.toMatrix' x' with hXdef
  set Y := GlobalTheory.VacUnique.finRat S T X with hY
  set Λ := latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hvac : IsLatVac (heisO ψ S T) Λ f₀ := hV.2.lat
  have hstab : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ :=
    fun w hw u hu => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ w hw u hu
  have hsmM : ∀ (r : D.host.E) (Z : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      GlobalTheory.VacUnique.finRat S T (r • Z) = incA D r • GlobalTheory.VacUnique.finRat S T Z := by
    intro r Z
    ext i j
    change (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (r * Z i j) = incA D r * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] Z i j)
    rw [show incA D r = (1 : AF D.host.F) ⊗ₜ[D.host.F] r from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hnat : ∀ (n : ℕ) (u : WO S T), n • u = incA D (n : D.host.E) • u := by
    intro n u; rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'

  have hcx : (c : 𝓞 D.host.E) • x' ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    (mem_twO_zero' _ c _).1 (natsmul_mem_twO' _ c _ _ (fun Q => by
      rcases Formalism.L2.Ker.expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hx)
  have ha : c • Y ∈ Λ := by
    rw [hnat, ← hsmM]
    have e1 : (c : D.host.E) • X = LinearMap.toMatrix' ((c : 𝓞 D.host.E) • x') := by
      rw [Nat.cast_smul_eq_nsmul (𝓞 D.host.E), ← Nat.cast_smul_eq_nsmul D.host.E, LinearEquiv.map_smul]
    rw [e1, GlobalTheory.LatVacSign.finRat_eq]
    exact finTens_mem_latO (one_mem_intAf _) (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hP.cc hSd hcx)

  have h0 : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hXt : X.map (fun r => e * incA D r) = e • Y := by
    ext i j
    change e * incA D (X i j) = e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] X i j)
    rw [show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] X i j = ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (X i j) by
      rw [show incA D (X i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] X i j from rfl, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul], ← mul_assoc, GlobalTheory.PlaceDatum.mul_pair_one h0]
  set R := (1 - e) • Y with hRdef
  have hYR : Y - e • Y = R := by rw [hRdef, sub_smul, one_smul]
  have hR : R ∈ Λ := by
    have h := _root_.GlobalTheory.HalfAComp.zmem D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd c hc hcP x' hx
    rw [← hXdef, ← hY, hXt, hYR] at h
    exact h
  have he2 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE

  have hbil : ∀ (x y : WO S T) (k : ℕ), symplOH S T (k • x) (k • y) = (k * k) • symplOH S T x y := by
    intro x y k
    have h1 : symplO S T (k • x) (k • y) = (k * k) • symplO S T x y := by
      rw [← symplHom_apply, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, symplHom_apply, smul_smul]
    rw [symplOH, symplOH, h1]
    simp only [nsmul_eq_mul]
    ring
  have hcc : c • c • Y ∈ Λ := nsmul_mem ha c
  obtain ⟨k, hk, hsign⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T N N' hV.1 hSd hTd f₀ hvac
    (-(((c : D.host.E) ^ 2) • X)) (by
      rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat]; exact hcc)
  rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat] at hsign
  set X1 := e • (c • c • Y) with hX1
  have hY1 : e • Y + R = Y := by rw [hRdef, ← add_smul, add_sub_cancel, one_smul]
  have hdec : c • c • Y = X1 + c • c • R := by
    calc c • c • Y = c • c • (e • Y + R) := by rw [hY1]
      _ = X1 + c • c • R := by rw [hX1, smul_add, smul_add, smul_comm e c, smul_comm e c]
  have hfixXn : heisO ψ S T (-X1) f₀ = f₀ := by
    have h := (GlobalTheory.IdemSumVac.heisO_idemSum_fix D ψ S T Λ f₀ hvac hstab e SS hE _ (neg_mem hcc)).1
    rwa [smul_neg] at h
  have hzero : symplOH S T (-X1) X1 = 0 := by
    have h0' : hO S T (-X1) X1 = 0 := by
      rw [hX1, ← smul_neg, GlobalTheory.LatVacSign.hO_smul_smul, hE.2, zero_mul]
    rw [symplOH, symplO, h0', mul_zero, map_zero, mul_zero]
  have hinv : ∀ g, heisO ψ S T (-X1) (heisO ψ S T X1 g) = g := by
    intro g
    rw [GlobalTheory.LatVac.heisO_heisO, hzero, AddChar.map_zero_eq_one, one_smul, neg_add_cancel, GlobalTheory.LatVac.heisO_zero]
  have hcR : c • c • R ∈ Λ := nsmul_mem (nsmul_mem hR c) c
  have hcoc4 : ψ (symplOH S T X1 (c • c • R)) = 1 := by
    have h := _root_.GlobalTheory.HalfCocycle.char_symplOH_idem_conj D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd _ hcc _ hcR
    have e1 : symplOH S T X1 (c • c • R) = symplOH S T (e • (c • c • Y)) (cA D e • (c • c • R)) := by
      rw [hX1, symplOH, symplOH, ← GlobalTheory.SplitScalar.symplO_smul, smul_smul e e, he2]
    rw [e1]; exact h
  obtain ⟨m, hm⟩ := id hcP
  have hR2eq : c • c • R = R + 2 • ((2 * m * m + 2 * m) • R) := by
    have h1 : R + 2 • ((2 * m * m + 2 * m) • R) = (1 + 2 * (2 * m * m + 2 * m)) • R := by
      rw [add_smul 1 (2 * (2 * m * m + 2 * m)) R, one_smul, mul_smul]
    rw [h1, smul_smul]
    congr 1; subst hm; ring
  have hRR : heisO ψ S T (c • c • R) f₀ = heisO ψ S T R f₀ := by
    have hmR : (2 * m * m + 2 * m) • R ∈ Λ := nsmul_mem hR _
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ R (2 • ((2 * m * m + 2 * m) • R)) f₀
    have hs : symplOH S T R (2 • ((2 * m * m + 2 * m) • R)) = symplO S T R ((2 * m * m + 2 * m) • R) := by
      rw [symplOH, ← symplHom_apply, map_nsmul, symplHom_apply, nsmul_eq_mul, ← mul_assoc]
      have h12 : algebraMap D.host.F (AF D.host.F) (1 / 2) * ((2 : ℕ) : AF D.host.F) = 1 := by
        rw [← map_natCast (algebraMap D.host.F (AF D.host.F)), ← map_mul]; norm_num
      rw [h12, one_mul]
    rw [hvac.1 _ hmR, hs, GlobalTheory.LatVac.char_sympl_eq_one hV.1 hSd hTd hR hmR, one_smul, ← hR2eq] at h1
    exact h1.symm
  have hRk : heisO ψ S T R f₀ = ((-1 : ℂ) ^ k) • f₀ := by
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ X1 (c • c • R) f₀
    rw [hcoc4, one_smul, ← hdec, hsign, hRR] at h1
    have h2' := congrArg (heisO ψ S T (-X1)) h1
    rw [hinv, GlobalTheory.LatVac.heisO_smul, hfixXn] at h2'
    exact h2'

  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, (k₀ : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      GlobalTheory.LatVac.hRat S T X X) :=
    _root_.GlobalTheory.TraceInt.trace_int D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd c hc hcP x' hx
  have hα : alV D.host.d sc (embH (tauE D) δ x') = (-1 : ℂ) ^ k₀ := by
    have h := GlobalTheory.SemiTrace.alV_embH_eq_neg_one_zpow D ψ θ S T S.rank T.rank rfl rfl δ sc hP x' k₀ (by simpa using hk₀)
    exact h
  have hkk : k = (c : ℤ) ^ 4 * k₀ := by
    have e1 : GlobalTheory.LatVac.hRat S T (-(((c : D.host.E) ^ 2) • X)) (-(((c : D.host.E) ^ 2) • X)) =
        ((c : ℚ) ^ 4 : ℚ) • GlobalTheory.LatVac.hRat S T X X := by
      rw [← neg_smul, GlobalTheory.LatVacSign.hRat_smul_smul, star_neg, star_pow, star_natCast, Algebra.smul_def]
      push_cast; ring
    have e2 : (k : ℚ) = (c : ℚ) ^ 4 * k₀ := by
      rw [hk, e1, mul_smul_comm, map_smul, hk₀, smul_eq_mul]
    exact_mod_cast e2
  have hodd : Odd ((c : ℤ) ^ 4) := by
    obtain ⟨m', hm'⟩ := id hcP
    exact (show Odd (c : ℤ) from ⟨m', by exact_mod_cast hm'⟩).pow
  have hsgn : ((-1 : ℂ) ^ k) = alV D.host.d sc (embH (tauE D) δ x') := by
    rw [hα, hkk, _root_.zpow_mul, hodd.neg_one_zpow]
  rw [hXt, hYR, hRk, hsgn]

end GlobalTheory.HalfARest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIndSB

theorem indicator_latO_mem_SB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  intro D ψ S T M M' hM hM' P
  classical
  have hset : {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} =
      (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k)) := by
    obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem P.q
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε P.q.split.1 heε h).1
    have hh : (ofSplit P.q).up P.FS P.FT x ∈ GlobalTheory.PlaceModel.half S T P.q.e :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.LocMod.Witness.up_half (ofSplit P.q) P.FS P.FT x)
    have h3 : P.q.e • (ofSplit P.q).up P.FS P.FT x = (ofSplit P.q).up P.FS P.FT x := (GlobalTheory.PlaceModel.mem_half S T).1 hh
    change P.q.e • (ofSplit P.q).up P.FS P.FT x ∈ (latO S T (M : Set _) (M' : Set _) fun w => w = P.q.v) at h2
    rw [h3] at h2
    exact h2
  rw [hset]
  have ho := GlobalTheory.LocMod.Witness.lat_open (ofSplit P.q) P.FS P.FT hM hM'
  have hc := GlobalTheory.LocMod.Witness.lat_compact (ofSplit P.q) P.FS P.FT hM hM'
  have hcl := AddSubgroup.isClosed_of_isOpen _ ho
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap
        (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k))
    · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LatIndSB

end
end

