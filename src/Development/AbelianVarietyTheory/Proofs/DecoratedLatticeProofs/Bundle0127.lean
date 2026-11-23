module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainFlagUnipotentCoords
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetSB

theorem cosetInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  intro k _ _ _ _ n _ _ q L _ f
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  by_cases hex : ∃ F : n → k, Lifts L F f
  · obtain ⟨F, hF⟩ := hex
    have e : cosetInd q L f = fun η => dualInd L (η - q.inv • F) := by
      funext η
      rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]
    rw [e]
    exact GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F)
      (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _
  · have e : cosetInd q L f = 0 := by
      classical
      funext η
      unfold cosetInd
      rw [ite_eq_right fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]
      rfl
    rw [e]
    exact (SB (n → k)).zero_mem

end GlobalTheory.FinPl.CosetSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthogonalAllThetaFunctions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaOrthTotal

theorem eq_zero_of_orthogonal_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 q hq hquasi horth
  obtain ⟨f₀, hne, h₀⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact _root_.GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x
  have hq' : ∀ γ ∈ ratL T S, ∀ w, q (γ + w) = ψ (-(symplOH S T γ w)) * q w := by
    intro γ hγ w
    obtain ⟨γ', rfl⟩ := hγ
    exact hquasi γ' w
  have horth' : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (q x) ∂μ = 0 := by
    intro w
    have h := horth _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ h₀)
    have e : (fun x => heisO ψ S T w f₀ x * star (q x)) = fun x => (starRingEnd ℂ) (q x * star (heisO ψ S T w f₀ x)) := by
      funext x
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [e, integral_conj, h, map_zero]
  exact GlobalTheory.HeisTotal.eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann
    f₀ q h₀.cont hq (GlobalTheory.HeisTotal.quasi_of_mem h₀) hq' hne μ 𝓕 hμ h𝓕 horth'

end GlobalTheory.ThetaOrthTotal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCongruenceModulusIdelicCharacterTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeckeSplitAll

theorem char_trivial_modSet : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  intro D ν hν
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  have hNr : (N : Af D.host.F ⊗[D.host.F] D.host.E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPart D (x : AE D) ∈ intAE D := by
    have : finPart D (x : AE D) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaFlag

variable {D : D7} {v : Pl D}

def intGrpAt (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  zero_mem' := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mul_mem_intAt {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) : a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem exists_nat_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_isIntegral_fin {ι : Type} [Fintype ι] (z : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l, IsIntegral ℤ ((d : D.host.E) * z l) := by
  classical
  choose c hc hi using fun p : ι => exists_nat_isIntegral (z p)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ l), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi l)
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem mul_incA_mem {ε : AE D} (hεI : ε ∈ intAt D (· = v)) {o : D.host.E} (ho : IsIntegral ℤ o) :
    ε * incA D o ∈ intAt D (· = v) := by
  have h : finPart D (incA D o) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩
  exact ⟨Ideal.mul_mem_right _ _ hεI.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE hεI.2 h⟩

theorem princ_intGrpAt {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v))
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (ht : Tame D v) : Princ ε (intGrpAt D v) := by
  rintro J h1 h2 ⟨m, hm, h3⟩ ⟨N, hN, h4⟩
  obtain ⟨β, β', g1, g2, g3, g4, g5⟩ := GlobalTheory.IwaPlace.FreeAt.exists_basis D 1 v ε (J.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => AE D) 0))
    ht hεε hεc hεI hε
    (fun y hy i => by rw [Subsingleton.elim i 0]; exact (hε _).2 (h1 _ hy))
    (fun a ha y hy => h2 a ha _ hy)
    ⟨m, hm, fun y hy => by
      have := h2 _ (hy 0) _ h3
      rw [mul_left_comm, mul_comm (y 0), (hε _).1 (hy 0).1] at this
      exact this⟩
    ⟨N, hN, fun y hy i => by rw [Subsingleton.elim i 0]; exact h4 _ hy⟩
  have e3 : β 0 0 * β' 0 0 = ε := by
    have := congrFun (congrFun g3 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  have ev : ∀ (a : AE D) (i : Fin 1), (β' *ᵥ fun _ => a) i = β' 0 0 * a := fun a i => by
    rw [Subsingleton.elim i 0, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  refine ⟨β 0 0, (g5 (fun _ => β 0 0) fun _ => g1 0 0).2 fun i => ?_, β' 0 0, (hε _).1 (g2 0 0), e3, fun a ha => ?_⟩
  · rw [ev, mul_comm, e3]; exact hεI
  · have := (g5 (fun _ => a) fun _ => (hε _).2 (h1 a ha)).1 ha 0
    rw [ev] at this
    exact this

theorem exists_flag_basis : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2) (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol : ∀ z : Fin S.rank → D.host.E, (∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) →
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := fun z hz => by
    have e : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [e]
    exact hmul _ fun l => mul_incA_mem hεI (hz l)
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := exists_flag_dual_matrix (c := cA D) (O := intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1) (fun a ha b hb => mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]), (FrameLat.cA_int_iff a).2 ha.2⟩)
    (princ_intGrpAt hεε hεc hεI hε ht) (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩

end GlobalTheory.IwaFlag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.StdPos

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix

section Pure

variable {R : Type} [CommRing R] (s : R →+* R) {n r m : ℕ} (J : Matrix (Fin n) (Fin n) R)

end Pure

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n r m : ℕ}
  (J : Matrix (Fin n) (Fin n) E)







end Lattice

end GlobalTheory.RegSch.StdPos

namespace GlobalTheory.RegSch

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix StdPos

theorem exists_good_frameLat (D : D7) (V : HSp D) : ∃ a, Lvl.Good (⟨frameLat V, a⟩ : Lvl V) :=
  (exists_isMaj V).imp fun _ h => ⟨isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, h⟩

end GlobalTheory.RegSch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.SDBound

variable {D : D7}

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_mul_isIntegral_fin {n : ℕ} (z : Fin n → Fin n → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l k, IsIntegral ℤ ((d : D.host.E) * z l k) := by
  classical
  choose c hc hi using fun p : Fin n × Fin n => exists_nat_mul_isIntegral (z p.1 p.2)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l k => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ (l, k)), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi (l, k))
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem finPart_incA_mem {o : D.host.E} (ho : IsIntegral ℤ o) : finPart D (incA D o) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩

theorem hermAt_single (S : HSp D) (y : Fin S.rank → AE D) (k : Fin S.rank) (a : AE D) :
    hermAt S y (Pi.single k a) = cA D a * (gA S *ᵥ y) k := by
  unfold hermAt
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, RingHom.map_zero]
    simp only [zero_mul, Finset.sum_const_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem exists_mul_mem_intAt : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v) := by
  intro D S v Λ ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  obtain ⟨d, hd, hint⟩ := exists_nat_mul_isIntegral_fin (fun l k => (S.gram)⁻¹ l k)
  refine ⟨d * m, Nat.mul_pos hd hm, fun y hy l => ⟨Ideal.mul_mem_left _ _ (hsupp y hy l), ?_⟩⟩
  have key : ∀ k, finPart D ((m : AE D) * (gA S *ᵥ y) k) ∈ intAE D := fun k => by
    have hx : (m : AE D) • (Pi.single k ε : Fin S.rank → AE D) ∈ Λ := by
      refine hmul _ fun i => ?_
      by_cases hi : i = k
      · rw [hi, Pi.single_eq_same]; exact hε
      · rw [Pi.single_eq_of_ne hi]; exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    have h1 := (((hdual y (hsupp y hy)).1 hy) _ hx).2
    rwa [← Pi.single_smul', smul_eq_mul, hermAt_single, RingHom.map_mul (cA D), map_natCast, hc, mul_assoc,
      hact _ (mulVec_mem_idAt _ (hsupp y hy) k)] at h1
  have e1 : y l = ∑ k, incA D ((S.gram)⁻¹ l k) * (gA S *ᵥ y) k := by
    have : giA S *ᵥ (gA S *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, giA_mul_gA, Matrix.one_mulVec]
    exact (congrFun this l).symm
  have e2 : ((d * m : ℕ) : AE D) * y l =
      ∑ k, incA D ((d : D.host.E) * (S.gram)⁻¹ l k) * ((m : AE D) * (gA S *ᵥ y) k) := by
    rw [e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, map_natCast, Nat.cast_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sum]
  refine sum_mem fun k _ => ?_
  rw [RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (finPart_incA_mem (hint l k)) (key k)

end GlobalTheory.IwaPlace.SDBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentHaarEqMapCoordinates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoordsUnit

theorem eq_of_rightInvariant_of_fundamentalDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] (ν m : Measure G) (𝓝 𝓕 : Set G)
    (h1 : ν.IsHaarMeasure) (h2 : IsFundamentalDomain Γ 𝓝 ν) (h3 : ν 𝓝 = 1) (k0 : SigmaFinite m) (k1 : m.IsMulRightInvariant)
    (k2 : IsFundamentalDomain Γ 𝓕 m) (k3 : m 𝓕 = 1) : m = ν := by
  open scoped Pointwise in
  haveI : ν.IsMulRightInvariant := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain Γ ν h2
    (by rw [h3]; exact one_ne_zero) (by rw [h3]; exact ENNReal.one_ne_top)
  have hinv : ν.inv 𝓝⁻¹ = 1 := by rw [Measure.inv_apply, inv_inv, h3]
  have e1 := measure_eq_div_smul m.inv ν.inv (s := 𝓝⁻¹) (by rw [hinv]; exact one_ne_zero) (by rw [hinv]; exact ENNReal.one_ne_top)
  rw [hinv, div_one, Measure.inv_apply, inv_inv] at e1
  set κ := m 𝓝 with hκ
  have e2 : m = κ • ν := by
    ext s -
    have := congrArg (fun μ : Measure G => μ s⁻¹) e1
    simpa only [Measure.inv_apply, inv_inv, Measure.smul_apply] using this
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e2
    rw [e2] at k3
    simp at k3
  haveI : m.IsMulLeftInvariant := by rw [e2]; infer_instance
  have h2' : IsFundamentalDomain Γ 𝓝 m := h2.mono (by rw [e2]; exact Measure.smul_absolutelyContinuous)
  have h4 : m 𝓝 = 1 := (h2'.measure_eq k2).trans k3
  have hk1 : κ = 1 := by rw [hκ]; exact h4
  rw [e2, hk1, one_smul]

theorem volN_eq_map_coords : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → lC 𝓒 = 1 → vN.ν = (lC.prod (vb.μ.prod vU.ν)).map e := by
  intro D V V₀ ρ d vN vb vU e he lC 𝓒 hC hCs hCF hC1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hU, 𝓤, hU𝓤, hU1⟩ := vU.unit
  obtain ⟨hb, hbF, hb1⟩ := vb.covol
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨-, n2, n3, n4, -⟩ := lattice_Mx D ρ ρ
  haveI := vN.unit.1
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite lC := inferInstance
  haveI : SigmaFinite vb.μ := inferInstance
  haveI : SigmaFinite vU.ν := inferInstance
  haveI hm : SigmaFinite ((lC.prod (vb.μ.prod vU.ν)).map e) := e.sigmaFinite_map
  have hR := _root_.GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord D V V₀ ρ d vb vU e he lC hC hCs
  have hF := _root_.GlobalTheory.ThreeLayers.fundDomain_coords D V V₀ ρ d vb vU e he lC 𝓒 𝓤 hC hCs hCF hU𝓤
  have h1 : (lC.prod (vb.μ.prod vU.ν)).map e (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ 𝓤))) = 1 := by
    rw [MeasurableEquiv.map_apply, e.preimage_image, Measure.prod_prod, Measure.prod_prod, hC1, hb1, hU1, one_mul, one_mul]
  exact (eq_of_rightInvariant_of_fundamentalDomain (NFlagQ V d.e) vN.ν _ vN.𝓝 _ vN.unit.1 vN.unit.2.1 vN.unit.2.2 hm hR hF h1).symm

end GlobalTheory.HaarCoordsUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem handFBLaw : ∀ D : D7, HandFBLaw D := by
  intro D
  unfold HandFBLaw
  intro ψ σ J B s vL Y Ξ hY hΞ

  obtain ⟨hc, hl, hr⟩ := _root_.GlobalTheory.PairKer.pairKer_law D ψ σ J B s vL Y Ξ hY hΞ
  refine ⟨fun γ hγ g => ?_, ?_⟩
  ·
    simp only [handFB, hr γ hγ]
  ·
    exact (_root_.GlobalTheory.CocompactParam.continuous_integral_param D J.W₀ J.cpt J.v0 (GA D B.A) (pairKer s vL Y Ξ) hc hl).2.1

end GlobalTheory
end

