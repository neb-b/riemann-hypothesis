module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0552
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelHeightFinitePlaceDoublingEmbeddingLeOne
section
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.Core.Rk.HgtFin

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_le_one_of_absFin_le_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E), absFin F v x ≤ 1 → ‖Algebra.norm (Fv F v) x‖₊ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ v x hx
  have hN := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x
  have e1 : absFin F v (algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) x)) =
      ‖Algebra.norm (Fv F v) x‖₊ := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact absFin_tmul_one F v _
  have hs : absFin F v (sigR (Fv F v) σ x) ≤ absFin F v x := by
    refine (absFin_le_iff F v).2 fun τ => ?_
    have e2 : ∀ w, finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v ((τ : E →ₐ[F] FvBar F v).comp σ) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    rw [e2]
    exact le_absFin F v _ x
  rw [← e1, hN]
  calc _ ≤ absFin F v x * absFin F v (sigR (Fv F v) σ x) := absFin_mul_le F v _ _
    _ ≤ 1 * 1 := mul_le_mul' hx (hs.trans hx)
    _ = 1 := one_mul 1

theorem absFin_tmul_one_mul (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (y : Fv F v ⊗[F] E) :
    absFin F v (c ⊗ₜ[F] (1 : E) * y) = ‖c‖₊ * absFin F v y := by
  simp only [absFin, map_mul, finEmb_tmul, map_one, mul_one, absBar_mul, absBar_algebraMap]
  rw [NNReal.mul_finset_sup]

theorem absFin_le_one_of_pow_le {v : HeightOneSpectrum (𝓞 F)} {x : Fv F v ⊗[F] E} {C : ℝ≥0}
    (h : ∀ k : ℕ, absFin F v (x ^ k) ≤ C) : absFin F v x ≤ 1 := by
  refine (absFin_le_iff F v).2 fun τ => ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
  have := (le_absFin F v τ (x ^ k)).trans (h k)
  have hpw : ∀ (z : FvBar F v) (m : ℕ), absBar F v (z ^ m) = absBar F v z ^ m := by
    intro z m
    induction m with
    | zero => simpa using absBar_algebraMap F v 1
    | succ m ih => rw [pow_succ, absBar_mul, ih, pow_succ]
  rw [map_pow, hpw] at this
  exact absurd this (not_le.2 hk)

theorem absFin_det_le (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    absFin F v M.det ≤ normFin F v M ^ n := by
  rw [Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun s _ => ?_
  have hp : absFin F v (∏ i, M (s i) i) ≤ normFin F v M ^ n :=
    calc absFin F v (∏ i, M (s i) i) ≤ ∏ i, absFin F v (M (s i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, normFin F v M := Finset.prod_le_prod' fun i _ => absFin_le_normFin F v M _ _
      _ = normFin F v M ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hp

theorem normDet_le_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hM : ∀ x ∈ latLoc F L v, M *ᵥ x ∈ latLoc F L v) : ‖Algebra.norm (Fv F v) M.det‖₊ ≤ 1 := by
  obtain ⟨c, hc, hcL⟩ := _root_.GlobalTheory.AdelicU.exists_single_mem_latLoc L v
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.absFin_latLoc_le L v
  have hpow : ∀ k : ℕ, ∀ x ∈ latLoc F L v, (M ^ k) *ᵥ x ∈ latLoc F L v := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hM _ hx)
  have hent : ∀ k i j, absFin F v ((M ^ k) i j) ≤ C / ‖c‖₊ := by
    intro k i j
    have h1 := hC _ (hpow k _ (hcL j)) i
    rw [Matrix.mulVec_single] at h1
    change absFin F v ((M ^ k) i j * c ⊗ₜ[F] (1 : E)) ≤ C at h1
    rw [mul_comm, absFin_tmul_one_mul] at h1
    rw [le_div_iff₀ (nnnorm_pos.2 hc), mul_comm]
    exact h1
  have hdet : ∀ k : ℕ, absFin F v (M.det ^ k) ≤ (C / ‖c‖₊) ^ n := fun k => by
    rw [← Matrix.det_pow]
    exact (absFin_det_le v _).trans (pow_le_pow_left' ((normFin_le_iff F v).2 (hent k)) n)
  exact absNorm_le_one_of_absFin_le_one hσ v _ (absFin_le_one_of_pow_le hdet)

theorem levi_mulVec_mem (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GLoc σ J v) (p : siegelH (Fv F v) σ Q) {k : GLoc σ Q v} (hk : k ∈ KFin σ Q L v)
    (e : ioH _ σ hQ (y, 1) = p * k) {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc F L v) :
    leviMat finSumFinEquiv (matHom _ σ Q p).1 *ᵥ x ∈ latLoc F L v := by
  have hp : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := matHom (Fv F v) σ Q)).1 p.2
  have hk' := inv_mem hk
  have ek : k⁻¹ = ioH _ σ hQ (y⁻¹, 1) * p := by
    have : k = (p : GLoc σ Q v)⁻¹ * ioH _ σ hQ (y, 1) := by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this, mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hk' _).1 h1
  have e3 : (matHom _ σ Q (ioH _ σ hQ (y⁻¹, 1))).1 =
      blkMat finSumFinEquiv (matHom _ σ J y⁻¹).1 (matHom _ σ J 1).1 := rfl
  rw [ek, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hp.mulVec_diag, e3, blkMat_mulVec, latLoc_sumLat,
    pairVec_mem_sumLat] at h2
  simpa using h2.2

theorem hgtFin_ioH_le_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)) (y : GLoc σ J v) :
    hgtFin σ Q L v (ioH _ σ hQ (y, 1)) ≤ 1 := by
  by_cases h : ∃ p : siegelH (Fv F v) σ Q, ∃ k ∈ KFin σ Q L v, ioH _ σ hQ (y, 1) = p * k
  · obtain ⟨p, k, hk, e⟩ := h
    rw [e, hgtFin_mul p hk, absEv_apply]
    exact normDet_le_one hσ L v _ fun x hx => levi_mulVec_mem σ hQ L v y p hk e hx
  · show iwAbs _ _ _ ≤ 1
    rw [iwAbs, dite_eq_right h]

end GlobalTheory.Core.Rk.HgtFin

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Rk.IP

theorem hgtFin_ioAt_le_one : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (y : Gv A v), hgtFin D.sp.cm.sig (dblSp A).gram L v (ioAt A v y) ≤ 1 := by
  intro D A L hL v y
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  exact GlobalTheory.Core.Rk.HgtFin.hgtFin_ioH_le_one (isCMExt_host D) (gram_hdbl A) L v y

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairsExistAtLevelPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace StdExProof

theorem qt_facts (T : ℕ) [Fact T.Prime] : Nat.card 𝓀[ℚ_[T]] = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := _root_.GlobalTheory.TAdicInt.card_residueField_and_irreducible T

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (T : ℕ) (hT : T.Prime) (hs : GlobalTheory.St.G.SplitsIn E T)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (T : 𝓞 E) ∈ w.asIdeal) : ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} :=
  _root_.GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn E T hT hs w hw

theorem places_over (D : D7) (π π' : 𝓞 D.host.E) (T : ℕ) (hπ' : (π' : D.host.E) = star (π : D.host.E))
    (hT : π * π' = (T : 𝓞 D.host.E)) (hne : π ≠ 0) (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x :=
  GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd D π π' T hπ' hT hne x

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int (p : SplitPt D k) (x : 𝓞 D.host.E) : p.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (p.pr (incA D (x : D.host.E))) := (x.2).map ((p.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (p.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem val_pr_eq_one (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    (y : 𝓞 D.host.E) (hy : y ∉ w.asIdeal) : valuation k (p.pr (incA D (y : D.host.E))) = 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ w.asIdeal.zero_mem)
  have hyE : (y : D.host.E) ≠ 0 := by exact_mod_cast hy0
  have hI : finPart D (p.e * incA D ((y : D.host.E))⁻¹) ∈ intAE D := not_not.1 (mt (hw.2 y hy0).2 hy)
  have h1 : p.pr (incA D ((y : D.host.E))⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact hI
  have h2 := pr_int p y
  have hmul : p.pr (incA D (y : D.host.E)) * p.pr (incA D ((y : D.host.E))⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hyE, map_one, map_one]
  have e1 : valuation k (p.pr (incA D (y : D.host.E))) ≤ 1 := h2
  have e2 : valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) ≤ 1 := h1
  have e3 := congrArg (valuation k) hmul
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  by_contra hlt
  push_neg at hlt
  have : valuation k (p.pr (incA D (y : D.host.E))) * valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt e2
  rw [e3] at this
  exact lt_irrefl _ this

theorem isLat_std (p : SplitPt D k) (S : HSp D) (β : Frame p S (Fin S.rank)) (hb : β.b = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D _) : β.IsLat L (stdLat k (Fin S.rank)) := by
  intro x
  have hL' : ∀ z : Fin S.rank → D.host.E, z ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = z i := fun z => by
    rw [hL z]
    exact ⟨fun h i => ⟨⟨z i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  rw [hb, Matrix.one_mulVec, GlobalTheory.FinPl.Model.mem_latV_std S L hL' p.v, mem_stdLat]
  refine forall_congr' fun i => ?_
  rw [p.int_iff]
  exact ⟨fun h => ⟨GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _, h⟩, fun h => h.2⟩

def scPair (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) : Pair k n where
  lat := stdLat k n
  isLat := inferInstance
  fn := c • (stdPair k i).fn
  fn_ne h := (stdPair k i).fn_ne (LinearMap.ext fun x => (hc.smul_eq_zero).1 (LinearMap.congr_fun h x))

theorem scPair_hasVal (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) (x : n → k) (hx : ∀ j, x j ∈ 𝒪[k]) :
    (scPair c hc i).HasVal x (residue 𝒪[k] (c * ⟨x i, hx i⟩)) :=
  ⟨mem_stdLat.2 hx, by
    show c • residue 𝒪[k] ⟨x i, _⟩ = _
    rw [map_mul, Algebra.smul_def]; rfl⟩

end StdExProof
end GlobalTheory.AdForm

namespace GlobalTheory.AdForm.StdExProof
open GlobalTheory.AdForm

theorem stdEx' : StdEx' := by
  intro B X I hI _hP l Z u ψ hψ L hL
  haveI hTf : Fact (B.T u).Prime := ⟨l.pr.T_prime u⟩
  obtain ⟨hcard, hirr⟩ := qt_facts (B.T u)
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : ∀ i : (B.primes X).vT u, X.piT u ∈ i.1.asIdeal := fun i => (Formalism.L2.Col.mem_divs hne _).1 i.2
  have hconj : ∀ i : (B.primes X).vT u, B.fields.conjO (X.piT u) ∉ i.1.asIdeal := by
    intro i hc
    obtain ⟨a, b, hab⟩ := hcop
    exact i.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ i.1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i)) (Ideal.mul_mem_left _ b hc)))
  have hcP : ∀ i : (B.primes X).vT u, GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1 ≠ i.1 := by
    intro i h
    apply hconj i
    have h1 : X.piT u ∈ (GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1).asIdeal := by rw [h]; exact hmem i
    have h2 := (GlobalTheory.IdemSupport.mem_cP (D := I.rec7 l Z) i.1 (X.piT u)).1 h1
    have h3 : B.fields.conjO (X.piT u) = GlobalTheory.IdemSupport.cO (I.rec7 l Z) (X.piT u) := RingOfIntegers.ext rfl
    rw [h3]; exact h2
  choose e he using fun i : (B.primes X).vT u => GlobalTheory.StdFrames.exists_isIdemAt (hcP i)
  have hsplitT := (GlobalTheory.St.G.record_facts (I.rec7 l Z) u).1
  have hsp : ∀ i : (B.primes X).vT u, ∃ p : SplitPt (I.rec7 l Z) ℚ_[B.T u], p.e = e i := fun i =>
    (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).1 ℚ_[B.T u] (B.T u) hTf.out hcard hirr i.1 (e i) (he i) (he i).1
      (l.pr.vT_norm u _ i.2) (not_sq_dvd _ (B.T u) hTf.out hsplitT i.1 (by
        have h := Ideal.mul_mem_right (B.fields.conjO (X.piT u)) _ (hmem i)
        rw [l.pr.piT_norm u] at h
        exact h))
  choose p hpe using hsp
  have hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e i.1 := fun i => (hpe i).symm ▸ he i
  let wE : (B.primes X).vT u → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) := fun i => i.1
  have hv : ∀ i : (B.primes X).vT u, HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (wE i) = (p i).v := by
    intro i
    obtain ⟨ε, h1, h2⟩ := (p i).above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (hidem i) h1 h2
  have hover := fun x => places_over (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl (l.pr.piT_norm u) hne x
  have hTv : ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := fun i =>
    (hover (p i).v).2 ⟨wE i, i.2, hv i⟩
  have hunit : ∀ i, (p i).UnitAA := fun i => GlobalTheory.FinPl.UnitAt.unitAA_level I l Z u (p i) (hTv i)
  have hpart2 := fun i => (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).2 ℚ_[B.T u] (p i)
  choose χ hχ using fun i => (hpart2 i).2 ψ hψ
  choose β hβ using fun j i => (hpart2 i).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1 (mul_one 1) (mul_one 1)
  have hβ' : ∀ j i, (β j i).b' = 1 := fun j i => by
    have := (β j i).bb'
    rwa [hβ j i, one_mul] at this
  have hrank : ∀ j, 0 < ((I.rec7 l Z).sp.X j).rank := by
    intro j
    obtain ⟨hs, h1, -⟩ := hI.spaces
    rw [show (I.rec7 l Z).sp.X j = B.sp.X j from rfl, h1 j]
    show 0 < B.R.k + j * (B.R.t + 1)
    have := B.R.m_add_three_le_k
    omega
  let c : (B.primes X).vT u → 𝒪[ℚ_[B.T u]] := fun i =>
    ⟨(p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)), pr_int (p i) (B.fields.conjO (X.piT u))⟩
  have hcv : ∀ i, valuation ℚ_[B.T u] ((p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E))) = 1 :=
    fun i => val_pr_eq_one (p i) (hidem i) (B.fields.conjO (X.piT u)) (hconj i)
  have hc : ∀ i, IsUnit (c i) := fun i =>
    (Valuation.integer.integers (valuation ℚ_[B.T u])).isUnit_iff_valuation_eq_one.2 (hcv i)
  let last : ∀ j, Fin ((I.rec7 l Z).sp.X j).rank := fun j => ⟨((I.rec7 l Z).sp.X j).rank - 1, by have := hrank j; omega⟩
  let Q : ∀ j, (B.primes X).vT u → Pair ℚ_[B.T u] (Fin ((I.rec7 l Z).sp.X j).rank) := fun j i => scPair (c i) (hc i) (last j)
  have hStd : StdT I l Z u p β Q L := by
    refine ⟨⟨Equiv.refl _, fun i => hidem i⟩, fun j hj => ⟨hL j hj, fun i => ⟨isLat_std (p i) _ (β j i) (hβ j i) (L j) (hL j hj), ?_⟩⟩⟩
    intro z hz r hr
    have hz' : ∀ r', IsIntegral ℤ (z r') := (hL j hj z).1 hz
    have hx : ∀ r', (p i).pr (incA (I.rec7 l Z) (z r')) ∈ 𝒪[ℚ_[B.T u]] := fun r' => pr_int (p i) ⟨z r', hz' r'⟩
    change r.1 + 1 = ((I.rec7 l Z).sp.X j).rank at hr
    have hrl : r = last j := Fin.ext (by show r.1 = _ - 1; omega)
    subst hrl
    refine ⟨c i * ⟨_, hx (last j)⟩, ?_, ?_⟩
    · show (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (z (last j))) = _
      rw [← map_mul]
      exact congrArg _ (map_mul _ _ _).symm
    · rw [hβ' j i, Matrix.one_mulVec]
      exact scPair_hasVal (c i) (hc i) (last j) _ hx
  refine ⟨ℚ_[B.T u], inferInstance, inferInstance, inferInstance, inferInstance, (B.primes X).vT u, p, Finset.univ.toList,
    ⟨(B.T u : 𝒪[ℚ_[B.T u]]), hirr⟩, χ, β, Q, ⟨Finset.nodup_toList _, fun i => Finset.mem_toList.2 (Finset.mem_univ _),
    GlobalTheory.AdForm.StdT.places_injective I hI _hP l Z u p β Q L hStd, fun x => Iff.rfl, hunit⟩,
    fun i => ⟨(hχ i).2.2.2 (hunit i), (hχ i).1⟩, hcard, fun i => ⟨?_, hcv i⟩, fun x => ?_, hβ, hStd⟩
  · have hm : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
        (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) = (B.T u : ℚ_[B.T u]) := by
      have : ((X.piT u : B.fields.E) * (B.fields.conjO (X.piT u) : B.fields.E)) = ((B.T u : ℕ) : B.fields.E) := by
        exact_mod_cast congrArg (fun x : 𝓞 B.fields.E => (x : B.fields.E)) (l.pr.piT_norm u)
      have h2 : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
          (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) =
          (p i).pr (incA (I.rec7 l Z) (((B.T u : ℕ) : B.fields.E))) := by
        rw [← map_mul, ← this]
        exact congrArg _ (map_mul _ _ _).symm
      rw [h2]
      exact map_natCast ((p i).pr.comp (incA (I.rec7 l Z))) (B.T u)
    have hv2 := congrArg (valuation ℚ_[B.T u]) hm
    rw [map_mul, hcv i, mul_one] at hv2
    rw [hv2]
    rfl
  · rw [hover x]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wE i, i.2, hv i⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, hv ⟨w, hw⟩⟩

end GlobalTheory.AdForm.StdExProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValue
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AFormL

theorem aFormL : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → ∀ SF, GlobalTheory.Hk3.IsSF R SF → AForm R SF := by
  intro hDS hHC hCusp hWS hSE hUD hBZ D G _ _ Pl0 T A Ks _ _ _ R F hG hc SF hSF
  have hHM := GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hPM := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.LiftScalarL.aForm R F
    (_root_.GlobalTheory.SourceLaw.sourceLevelLaw GlobalTheory.SingleBlock.localIntegralSingleBlock R F hPM)
    (_root_.GlobalTheory.innerProductFormula_of_hypotheses hCusp hWS hSE R F hG.params)
    (_root_.GlobalTheory.FockCoeffImage.fockCoefficientC hHM R F hPM)
    (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUD R F)
    (_root_.GlobalTheory.LevelIndex.levelIndexNormC GlobalTheory.SingleBlock.localIntegralSingleBlock R F hPM)
    (GlobalTheory.RealCoefSq.lowestKType_coefficients_sq_integrable R F hG.core)
    hG hc SF hSF

end GlobalTheory.AFormL

end
end

