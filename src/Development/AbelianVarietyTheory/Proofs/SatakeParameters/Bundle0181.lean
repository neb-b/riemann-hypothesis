module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0177
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInert
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem norm_hK_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hb w a b₀ i
  obtain ⟨h2, hq, -⟩ := GlobalTheory.InertCompare.ne_of_inert D p hcl
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl w
  set τ := tauPl D w with hτ
  have hρK : rhoK D lam w = fun y => ρ y := funext fun y => (hρ y).1
  have hρC : ∀ y, ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = GlobalTheory.KerStd.UnitaryMat.rho D lam τ y := fun y => by
    rw [(hρ y).2, GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]
  have hPW : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L (P τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP.1 τ
  have hP'W : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L' (P' τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP'.1 τ
  have hdet : IsUnit (P' τ).det := isUnit_iff_ne_zero.2 hP'W.1
  have hQ : (P' τ)⁻¹ * P' τ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hinv : ((P' τ).map (fun y => ρ y))⁻¹ = ((P' τ)⁻¹).map (fun y => ρ y) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [show ((P' τ)⁻¹).map (fun y => ρ y) = ((P' τ)⁻¹).map ρ from rfl,
      show (P' τ).map (fun y => ρ y) = (P' τ).map ρ from rfl, ← Matrix.map_mul, hQ,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [GlobalTheory.PadicPlaceBound.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hint := GlobalTheory.KerStd.UnitaryMat.intIn_of_locBasis hp1
    (fun x hx => GlobalTheory.EigenGenerator.norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent D h2 hq _ hx) hQ hPW hP'W hb i b₀ a
  have e : hK D lam P P' b w a b₀ i = ρ (((P' τ)⁻¹ * b i * P τ) b₀ a) := by
    unfold hK
    rw [← hτ, hρK, hinv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  show ‖((hK D lam P P' b w a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1
  rw [e, hρC]
  exact hint

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasisCoordinatesDual
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord.Pair

theorem sum_bilin {R : Type*} [CommRing R] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (F : κ → R) (G : μ → R) (X : ι → κ → R) (Y : ι → μ → R) :
    ∑ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * ∑ i, X i k * Y i m := by
  have h1 : ∀ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * (X i k * Y i m) := fun i => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end GlobalTheory.KerStd.HypCoord.Pair


open GlobalTheory.KerStd.HypCoord.Pair in
theorem GlobalTheory.KerStd.HypCoord.hK_gK_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ w z a b₀ a₁ b₁, ∑ i, hK D lam P P' b w a b₀ i * gK D lam P P' b z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b₀ = b₁ then 1 else 0 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hL w z a b₀ a₁ b₁

  have hunit : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E) (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      StdBases D lam L₀ Q → ∀ v, IsUnit ((Q (tauPl D v)).map (rhoK D lam v)).det := by
    intro n Q L₀ hQ v
    obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl v
    have hf : rhoK D lam v = ⇑ρ := funext fun y => (hρ y).1
    have h1 := hQ.2.1 hcl v
    have hdet : IsUnit (Q (tauPl D v)).det :=
      Matrix.isUnit_det_of_left_inverse h1
    rw [hf, show ((Q (tauPl D v)).map ⇑ρ).det = ρ (Q (tauPl D v)).det from (RingHom.map_det ρ _).symm]
    exact hdet.map ρ

  have hker : ∀ (k m : Fin N' × Fin N), ∑ i, rhoK D lam w (b i k.1 k.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) =
      if (tauPl D w, k.1, k.2) = (tauPl D z, m.1, m.2) then 1 else 0 := by
    intro k m
    have e := hL (tauPl D w, k.1, k.2) (tauPl D z, m.1, m.2)
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl]
    convert e using 1 <;> first | rfl | (split_ifs <;> simp)
  set A := ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ with hA
  set B := ((P (tauPl D z)).map (rhoK D lam z))⁻¹ with hB
  have eh : ∀ i, hK D lam P P' b w a b₀ i =
      ∑ k : Fin N' × Fin N, (A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a)) * rhoK D lam w (b i k.1 k.2) := fun i => by
    rw [hK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have eg : ∀ i, gK D lam P P' b z a₁ b₁ i =
      ∑ m : Fin N' × Fin N, (rhoK D lam z (P' (tauPl D z) m.1 b₁) * B a₁ m.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) := fun i => by
    rw [gK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [eh, eg]
  rw [sum_bilin]
  simp only [hker]
  by_cases hwz : w = z
  · subst hwz
    have hsimp : ∀ k m : Fin N' × Fin N, ((tauPl D w, k.1, k.2) = (tauPl D w, m.1, m.2)) ↔ k = m := by
      intro k m
      simp [Prod.ext_iff]
    simp only [hsimp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ k : Fin N' × Fin N, A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a) *
        (rhoK D lam w (P' (tauPl D w) k.1 b₁) * B a₁ k.2) =
        (A * (P' (tauPl D w)).map (rhoK D lam w)) b₀ b₁ * (B * (P (tauPl D w)).map (rhoK D lam w)) a₁ a := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [Matrix.map_apply]; ring
    rw [e1, hA, hB, Matrix.nonsing_inv_mul _ (hunit P' L' hP' w), Matrix.nonsing_inv_mul _ (hunit P L hP w),
      Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : b₀ = b₁ <;> by_cases h2 : a = a₁ <;> simp [h1, h2, eq_comm]
  · have hne : tauPl D w ≠ tauPl D z := fun h => hwz ((tauPl_bij D).1 h)
    rw [if_neg (fun h => hwz h.1)]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg (fun h => hne (congrArg Prod.fst h)), mul_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem intOff_finset_prod {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IntOff.one : IntOff S 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem xiCpl1_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ al p₀ p Yb x
  have hm : t.m2 < D.R.m := by have := (t.idx_ok μ).hm; omega
  unfold XiCpl1
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · rw [map_one]; exact IntOff.one
    · rw [map_zero]; exact IntOff.zero
  · unfold PsiAt
    first
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeries
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem mvPowerSeries_subst_linearForm {σ τ : Type} [Fintype σ] {K : Type} [Field K] {a : σ → MvPowerSeries τ K}
    (ha : MvPowerSeries.HasSubst a) (α : σ → K) :
    MvPowerSeries.subst a (∑ j, MvPowerSeries.C (α j) * MvPowerSeries.X j : MvPowerSeries σ K) =
      ∑ j, MvPowerSeries.C (α j) * a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_C]

theorem stdSer_scaled_eq_thOrth : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  intro D p _ lam N N' r P P' b hz hz0 hlin c G
  have hs1 : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hs2 : MvPowerSeries.HasSubst hz := MvPowerSeries.hasSubst_of_constantCoeff_zero hz0
  have e : ∀ x : ℂ_[p], algebraMap ℂ_[p] (MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) x = MvPowerSeries.C x := fun x => rfl
  rw [stdSer, atLin, thOrth, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs1,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs2]
  congr 1
  funext k
  simp only [e, one_mul]
  rw [mvPowerSeries_subst_linearForm hs1, mvPowerSeries_subst_linearForm hs2]
  have h1 : (∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hz i :
      MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) =
      MvPowerSeries.C c * ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
    rfl
  rw [h1, hlin k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLength
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.TrDualExpand

variable {K : Type} [Field K]

theorem iter_mul (σ : K →+* K) (n : ℕ) (a b : K) : σ^[n] (a * b) = σ^[n] a * σ^[n] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem sum_zmod_val {d : ℕ} [NeZero d] (F : ℕ → K) :
    ∑ s : ZMod d, F s.val = ∑ n ∈ Finset.range d, F n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_bijective (fun s : ZMod d => (⟨s.val, ZMod.val_lt s⟩ : Fin d))
    ⟨fun a b h => ZMod.val_injective d (by simpa using congrArg Fin.val h),
     fun i => ⟨(i.val : ZMod d), by ext; simp [ZMod.val_natCast_of_lt i.2]⟩⟩ _ _ (fun _ => rfl)

theorem sum_range_even (m : ℕ) (G : ℕ → K) :
    ∑ n ∈ Finset.range (2 * m), (if n % 2 = 0 then G n else 0) = ∑ i ∈ Finset.range m, G (2 * i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, if_pos (by omega), if_neg (by omega), add_zero]

theorem even_case {m d : ℕ} [NeZero d] (hd : 2 * m = d) (σ : K →+* K) (om oms : Fin m → K)
    (h : ∀ r r' : Fin m, (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r * oms r') else 0) =
      if r = r' then 1 else 0) (i j : Fin m) :
    ∑ k, σ^[2 * i.val] (om k) * σ^[2 * j.val] (oms k) = if i = j then 1 else 0 := by
  let M : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (om k)
  let Q : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (oms k)
  have hMQ : M.transpose * Q = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h r r',
      sum_zmod_val (fun n => if n % 2 = 0 then σ^[n] (om r * oms r') else 0), ← hd, sum_range_even,
      ← Fin.sum_univ_eq_sum_range (fun i => σ^[2 * i] (om r * oms r'))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [iter_mul]
    rfl
  have hMQ' : M * Q.transpose = 1 := by
    have := congrArg Matrix.transpose (mul_eq_one_comm.1 hMQ)
    simpa [Matrix.transpose_mul] using this
  have := congrFun (congrFun hMQ' i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem sum_eq_ite {d : ℕ} [NeZero d] (σ : K →+* K) (om oms : Fin (d / 2) → K)
    (hT : TrDual d σ om oms) (s t : ZMod d) (hst : s.val % 2 = t.val % 2) :
    ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 := by
  obtain ⟨hc, h⟩ := hT
  rw [Fintype.card_fin] at hc
  have hs := ZMod.val_lt s
  have ht := ZMod.val_lt t
  let i : Fin (d / 2) := ⟨s.val / 2, by omega⟩
  let j : Fin (d / 2) := ⟨t.val / 2, by omega⟩
  have E := even_case hc σ om oms h i j
  have hij : (i = j) ↔ (s = t) := by
    rw [Fin.ext_iff, ← (ZMod.val_injective d).eq_iff]
    simp only [i, j]
    omega
  rcases Nat.mod_two_eq_zero_or_one s.val with h0 | h1
  · have e1 : s.val = 2 * i.val := by simp only [i]; omega
    have e2 : t.val = 2 * j.val := by simp only [j]; omega
    rw [e1, e2, E]
    exact if_congr hij rfl rfl
  · have e1 : s.val = 2 * i.val + 1 := by simp only [i]; omega
    have e2 : t.val = 2 * j.val + 1 := by simp only [j]; omega
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [e1, e2, Function.iterate_succ_apply', ← map_mul, ← map_sum, E]
    split_ifs with h3 h4 h4
    · exact map_one σ
    · exact absurd (hij.1 h3) h4
    · exact absurd (hij.2 h4) h3
    · exact map_zero σ

end GlobalTheory.TrDualExpand

namespace GlobalTheory.KerStd.HypCoord

theorem trDual_expand : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p),
    TrDual (nP D p) σ om oms → ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 :=
  fun _ _ _ σ om oms hT s t hst => GlobalTheory.TrDualExpand.sum_eq_ite σ om oms hT s t hst

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.TwoSidedInert

theorem dualC_dualC (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by

  have h : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  unfold dualC
  rw [← Finsupp.mapDomain_comp, h, Finsupp.mapDomain_id]

theorem exists_down {C : Type} (Q : ℕ → C → C → Prop) (h : ∀ k c', ∃ c, Q k c c') (n : ℕ) :
    ∀ c, ∃ cs : ℕ → C, cs n = c ∧ ∀ k, k < n → Q k (cs k) (cs (k + 1)) := by
  induction n with
  | zero => exact fun c => ⟨fun _ => c, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    intro c
    obtain ⟨c₁, hc₁⟩ := h n c
    obtain ⟨cs, hcs, hQ⟩ := ih c₁

    refine ⟨fun k => if k ≤ n then cs k else c, by simp, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · simp only [if_pos hk.le, if_pos (Nat.succ_le_of_lt hk)]
      exact hQ k hk
    · simpa [hcs] using hc₁

theorem exists_up {C : Type} (Q : ℕ → C → C → Prop) (h : ∀ k c, ∃ c', Q k c c') (c0 : C) :
    ∃ cs : ℕ → C, cs 0 = c0 ∧ ∀ k, Q k (cs k) (cs (k + 1)) := by
  choose f hf using h
  exact ⟨fun k => Nat.rec (motive := fun _ => C) c0 (fun k c => f k c) k, rfl, fun k => hf k _⟩

theorem twoSided_of_inert : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → conjPl P = P → FixAll R t P → TwoSided R t P := by
  intro hHowe D G _ _ Pl0 T A Ks _ _ _ R F hLift hCore hSchur t P hGood hconj hFix

  have hY : ∀ k, k + 1 < D.R.m → SphCorr R.ψ (R.ωY t k) P := fun k hk =>
    _root_.GlobalTheory.Hk3.CorrInert.sphCorr_of_inert hHowe R.ψ _ _ _ _ (R.ωY t k) P (hCore.chain.ωY t k hk) hconj (hFix.1 k hk)
  have hX : SphCorr R.ψ (R.ωX t) P :=
    _root_.GlobalTheory.Hk3.CorrInert.sphCorr_of_inert hHowe R.ψ _ _ _ _ (R.ωX t) P (hCore.chain.ωX t) hconj hFix.2.1
  have hP : ∀ i, SphCorr R.ψ (R.ωP i t) P := fun i =>
    _root_.GlobalTheory.Hk3.CorrInert.sphCorr_of_inert hHowe R.ψ _ _ _ _ (R.ωP i t) P (hCore.thP.ωP i t) hconj (hFix.2.2 i)
  refine ⟨⟨fun cX => ?_, fun c0 => ?_⟩, fun i => ⟨fun cV => ?_, fun cW => ?_⟩⟩
  ·
    obtain ⟨cm, hcm⟩ := hX.2.1 (dualC cX)
    obtain ⟨cs, hcs, hQ⟩ := exists_down
      (fun k c c' => k + 1 < D.R.m → Match R.ψ (R.ωY t k) P c (dualC c'))
      (fun k c' => by
        by_cases hk : k + 1 < D.R.m
        · exact ((hY k hk).2.1 (dualC c')).imp fun c hc _ => hc
        · exact ⟨c', fun h => absurd h hk⟩) (D.R.m - 1) cm
    refine ⟨cs 0, _root_.GlobalTheory.Hk3.ChainE.matchE_of_chain R F hLift hCore hSchur t P hGood hFix cX cs ?_ fun k hk => ?_⟩
    · rw [hcs]; exact hcm
    · exact hQ k (by omega) hk
  ·
    obtain ⟨cs, hcs0, hQ⟩ := exists_up
      (fun k c c' => k + 1 < D.R.m → Match R.ψ (R.ωY t k) P c (dualC c'))
      (fun k c => by
        by_cases hk : k + 1 < D.R.m
        · obtain ⟨cT, hcT⟩ := (hY k hk).2.2 c
          exact ⟨dualC cT, fun _ => by rw [dualC_dualC]; exact hcT⟩
        · exact ⟨c, fun h => absurd h hk⟩) c0
    obtain ⟨cT, hcT⟩ := hX.2.2 (cs (D.R.m - 1))
    refine ⟨dualC cT, ?_⟩
    rw [← hcs0]
    refine _root_.GlobalTheory.Hk3.ChainE.matchE_of_chain R F hLift hCore hSchur t P hGood hFix (dualC cT) cs ?_ fun k hk => hQ k hk
    rw [dualC_dualC]; exact hcT
  · obtain ⟨cW, hcW⟩ := (hP i).2.2 (dualC cV)
    exact ⟨cW, _root_.GlobalTheory.DefLiftHecke.matchW_of_match R F hCore hSchur i t P hGood (hFix.2.2 i) cV cW hcW⟩
  · obtain ⟨cS, hcS⟩ := (hP i).2.1 cW
    refine ⟨dualC cS, _root_.GlobalTheory.DefLiftHecke.matchW_of_match R F hCore hSchur i t P hGood (hFix.2.2 i) (dualC cS) cW ?_⟩
    rw [dualC_dualC]; exact hcS

end GlobalTheory.Hk3.TwoSidedInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbit
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordBase_of_jumpIn : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i w hw C hG r ρ π ε κ hR hA h2 hq hd hI
  have hU : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) :=
    _root_.GlobalTheory.bridge_field_le_unramified D.nbr i w hw h2 hq hd
  have hF : Formalism.MainNotions.LocalSituation.fontCore ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) := hA _ _
  obtain ⟨g, hg, hread⟩ := _root_.GlobalTheory.HTW.Rec.reads_orbit_invFrob D (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ h2 hq hd
    (D.nbr i w hw).j_dense hU
  refine ⟨g, hg, _root_.GlobalTheory.bridge_degW D.nbr i w hw, ?_, _root_.GlobalTheory.HTW.Rec.recWord_wordNum L C₀ (liftIdx D i) ε g _ hR hg⟩
  exact
    { unram := hU
      split := fun ft => GlobalTheory.splits_of_conjugates_mem _ _ _
        (GlobalTheory.good_conjugates_mem _ _ _ 1 hG) ft
      t1 := _root_.GlobalTheory.HTW.Rec.fits_of_isSubOfSums L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hI hread
      t2 := _root_.GlobalTheory.HTW.Rec.fits_lowCount_of_matRep L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hU hI hread }

end GlobalTheory.HTW.Rec
end

