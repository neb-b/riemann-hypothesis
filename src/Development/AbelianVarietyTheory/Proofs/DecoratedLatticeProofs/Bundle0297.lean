module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section
open IsDedekindDomain NumberField
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaFixed

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

def intIn (D : D7) (v : Pl D) : v.adicCompletionIntegers D.host.F →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)).comp (algebraMap _ (Fv D.host.F v))

theorem integral_compFin (v : Pl D) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (intIn D v).IsIntegralElem (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    have e : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        intIn D v ⟨evalV D.host.F v a, ha v⟩ *
          (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E) (o : D.host.E) := by
      show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        (evalV D.host.F v a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (o : D.host.E))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [e]
    refine RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) ?_
    obtain ⟨p, hp, hpo⟩ : IsIntegral ℤ (o : D.host.E) := o.2
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom hpo
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [RingHom.ext_int ((intIn D v).comp (Int.castRingHom _)) ((Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom.comp (algebraMap ℤ D.host.E))]
    exact h
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ h h'
  | neg z _ h => rw [map_neg]; exact RingHom.IsIntegralElem.neg _ h

theorem mem_int_of_integral (v : Pl D) (a : Fv D.host.F v)
    (h : (intIn D v).IsIntegralElem (a ⊗ₜ[D.host.F] (1 : D.host.E))) : a ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hp, hpa⟩ := h
  have hinj : Function.Injective (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :=
    RingHom.injective _
  have hi : IsIntegral (v.adicCompletionIntegers D.host.F) a := by
    refine ⟨p, hp, hinj ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact hpa
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

theorem exists_inv (v : Pl D) {x : AE D} (hx : x ∈ idAt D (· = v)) (u : (v.adicCompletionIntegers D.host.F)ˣ)
    (hu : compAt D v x = ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E)) :
    ∃ y ∈ intAt D (· = v), x * y = idem D (· = v) := by
  classical
  obtain ⟨c, hci, hc⟩ : ∃ c : Fv D.host.F v, c ∈ v.adicCompletionIntegers D.host.F ∧ (u.val.1 : Fv D.host.F v) * c = 1 :=
    ⟨u.inv.1, u.inv.2, congrArg Subtype.val u.val_inv⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · exact pair_mem_idAt _ _ (fun w hw => evalV_single_ne _ v c hw) _
  · rw [finPart_pair]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v c, fun w => ?_, 1, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same]; exact hci
    · rw [evalV_single_ne _ v c hw]; exact zero_mem _
  · rw [← sub_eq_zero]
    apply eq_zero_of_comp
    · rw [map_sub, map_mul, infPart_of_idAt hx, infPart_of_idAt (idem_mem_idAt _), zero_mul, sub_zero]
    · intro w
      rw [map_sub, map_mul, compAt_idem]
      by_cases hw : w = v
      · subst hw
        rw [hu, compAt_pair, evalV_single_same, if_pos rfl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc,
          ← Algebra.TensorProduct.one_def, sub_self]
      · rw [compAt_of_idAt hx hw, if_neg hw, zero_mul, sub_zero]

theorem fixed_unit_or : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x →
    (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  intro D v ε _ _ _ hε hid x hx hfix
  classical
  have hεe : ε = idem D (· = v) := by
    have h1 := (hid _).1 (idem_mem_idAt (· = v))
    have h2 := (mem_idAt_iff (· = v) ε).1 hε.1
    rw [← h2, mul_comm, h1]
  subst hεe
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_mem D x hfix
  have hcomp : compAt D v x = evalV D.host.F v (sndA D.host.F b) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [← hb]
    show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (b ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  have hint : evalV D.host.F v (sndA D.host.F b) ∈ v.adicCompletionIntegers D.host.F := by
    apply mem_int_of_integral
    rw [← hcomp]
    exact integral_compFin v hx.2
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨_, hint⟩ : v.adicCompletionIntegers D.host.F) with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    refine exists_inv v hx.1 u ?_
    rw [hu, hcomp]
  · right
    refine exists_inv v (sub_mem (idem_mem_idAt _) hx.1) u ?_
    rw [hu, map_sub, compAt_idem, if_pos rfl, hcomp, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    rfl

end GlobalTheory.IwaFixed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPNotMemOfIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerLift

theorem conjP_notMem_of_isIdemSum {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro P hP hP'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have horth := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_conj_orth hes hsum hc P hP (Formalism.L2.Col.conjPrime₂ P) hP'
  have h1 : Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.Col.conjPrime₂ P))) P := by
    refine GlobalTheory.MovedIdem.isIdemAt_conj (hes _ hP') fun x => ?_
    show x ∈ P.asIdeal ↔ Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) ∈ P.asIdeal
    have : Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) = x := by
      apply RingOfIntegers.ext
      simp [Formalism.L2.Col.cO]
    rw [this]
  have heq : cA D (es (Formalism.L2.Col.conjPrime₂ P)) = es P :=
    (GlobalTheory.ExportSeries.idemAt_eq h1).symm.trans (GlobalTheory.ExportSeries.idemAt_eq (hes P hP))
  rw [heq, (hes P hP).1.1] at horth
  have hI := hes P hP
  rw [horth] at hI
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := (hI.2 x hx0).1 hxP
  rw [zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem natCast_smul_inv_smul {E : Type} [Field E] [NumberField E] {a b : ℕ} (c : ℕ) (hc : 0 < c)
    (y : Formalism.L2.Col.HomE E a b) : ((c : 𝓞 E)) • ((c : E)⁻¹ • y) = y := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc0, one_smul]


set_option maxHeartbeats 800000 in
theorem exists_rep_add_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ (SX : Finset (VV D.what₂.Tau S.rank T.rank)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → ∀ (px : VV D.what₂.Tau S.rank T.rank → Formalism.L2.Col.HomE D.host.E S.rank T.rank), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → ∀ g : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (∀ P ∈ SS, (c : D.host.E) • g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) → ∃ x ∈ SX, ∀ P ∈ SS, g + px x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS he N N' hN hN' c hc SX hSX px hpx g hg
  have hSS := conjP_notMem_of_isIdemSum he
  have hAA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.leading_constant_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  have hspan : ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, ∃ n : ℕ, 0 < n ∧ (n : D.host.E) • x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    by
      have hfull : Submodule.span D.host.E (N' : Set (Fin T.rank → D.host.E)) = ⊤ := by
        obtain ⟨n, s, s', hs, hd⟩ := _root_.GlobalTheory.LatVacDual.dualFamily D T N' hN'
        apply top_unique
        intro v _
        have hv : v = ∑ i, (∑ j, (∑ k, star (s' i k) * T.gram k j) * v j) • s i := by
          ext a
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          calc
            v a = ∑ j : Fin T.rank, (if a = j then 1 else 0) * v j := by simp
            _ = ∑ j, (∑ i, s i a * (∑ k, star (s' i k) * T.gram k j)) * v j := by simp_rw [hd]
            _ = ∑ i, (∑ j, (∑ k, star (s' i k) * T.gram k j) * v j) * s i a := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              ring
        rw [hv]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i).1)
      exact Formalism.L2.Ker.lf_span _ hAA N N' hN.1.fg hfull
  have hneg : ∀ P ∈ SS, (c : D.host.E) • (-g) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := fun P hP' => by
    rw [smul_neg]; exact neg_mem (hg P hP')
  have hL := Formalism.L2.Ker.lift_exists_alt D.host.E S.rank T.rank SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c hc hSS hspan (-g) hneg
  obtain ⟨hsA, hsP⟩ := hL
  generalize Formalism.L2.Ker.liftS SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c (-g) = s at hsA hsP
  have hmem : embH (tauE D) δ s ∈ AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c :=
    ⟨s, hsA, rfl⟩
  obtain ⟨x, hxS, hxL⟩ := hSX.2.2 _ hmem
  obtain ⟨β, hβ, hβe⟩ := hxL
  have hne : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hβs : β = s - px x := by
    apply Formalism.L2.Ker.embH_inj (tauE D) hP.ne
    rw [map_sub, (hpx x hxS).2]
    exact hβe
  refine ⟨x, hxS, fun P hPS => ?_⟩
  have h1 : s + g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    have h2 := hsP P hPS
    rw [sub_neg_eq_add] at h2
    have h3 : ((c : 𝓞 D.host.E)) • ((c : D.host.E)⁻¹ • (s + g)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      Submodule.smul_mem _ _ h2
    have e3 := natCast_smul_inv_smul c hc (s + g)
    rwa [e3] at h3
  have h4 : β ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hβ⟩
  have e5 : g + px x = (s + g) - β := by rw [hβs]; abel
  rw [e5]
  exact sub_mem h1 h4

end GlobalTheory.PerLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

open scoped Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContractionLocal

section Tens
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

def colTens (φ : SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n' ⊕ Unit)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁)
      (r := fun x r => x r (Sum.inr ())) (s := fun z => Matrix.fromCols z.1 (Matrix.of fun r _ => z.2 r))
      (by unfold Matrix.toCols₁; fun_prop) (continuous_pi fun r => by fun_prop) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases j with j | j
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply i).comp continuous_snd
    · intro x
      ext i (j | j)
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem colTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (colTens φ Ξ).1 x = Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())) := rfl

def rowTens (φ : SB (n → k)) : SB (Matrix n'' n k) →ₗ[ℂ] SB (Matrix (n'' ⊕ Unit) n k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n'' ⊕ Unit) (n' := n)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix (n'' ⊕ Unit) n k => x.toRows₁)
      (r := fun x => x (Sum.inr ())) (s := fun z => Matrix.fromRows z.1 (Matrix.of fun _ => z.2))
      (by unfold Matrix.toRows₁; fun_prop) (continuous_pi fun j => continuous_id.matrix_elem _ j) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases i with i | i
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply j).comp continuous_snd
    · intro x
      ext (i | i) j
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem rowTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n'' n k)) (x : Matrix (n'' ⊕ Unit) n k) :
    (rowTens φ Ξ).1 x = Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())) := rfl

end Tens

section Bil
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_contr (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {Ξ₁ : WO B.V₀ S → ℂ} {Ξ₂ : WO S B'.V₀ → ℂ}
    (h₁ : IsThetaFunO ψ B.V₀ S Ξ₁) (h₂ : IsThetaFunO ψ S B'.V₀ Ξ₂) (u : WO B.A S) (v : WO S B'.A) :
    Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := by
  haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ h₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ h₂
  have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
    (h₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))).mul
      (h₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (continuous_kappa l S))))
  refine (integrable_const (C₂ * C₁)).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC₂ _) (hC₁ _) (norm_nonneg _) ((norm_nonneg _).trans (hC₂ 0))

def contrBil (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] (WO B.A S → WO S B'.A → ℂ) :=
  LinearMap.mk₂ ℂ (fun Ψ₁ Ψ₂ => GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂))
    (fun a a' b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add (f := _), Pi.add_apply, mul_add]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a') (h₂ b) u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)
    (fun a b b' => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add (f := _), Pi.add_apply, add_mul]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a) (h₂ b') u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)

@[simp] theorem contrBil_apply (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) (Ψ₁ : M₁) (Ψ₂ : M₂) :
    contrBil hψ l S vL T₁ T₂ h₁ h₂ Ψ₁ Ψ₂ = GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂) := rfl

end Bil

end GlobalTheory.ContractionLocal

namespace GlobalTheory.ContractionLocal

theorem exists_normPair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψk)
    (hν : ν.IsAddHaarMeasure) (n : Type) [Fintype n] [DecidableEq n] :
    ∃ φ₀ φ₀' : SB (n → k), ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) = 1 := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := hν
  haveI := GlobalTheory.SplitWeil.secondCountable k
  let L := GlobalTheory.LatPair.stdLat k n
  have hc := GlobalTheory.FinPl.Comm.fpair_ne_zero ψk hψ (-1) (Or.inr rfl) (Measure.pi fun _ => ν) L
  set c := GlobalTheory.FinPl.Comm.fpair ψk (-1) (Measure.pi fun _ => ν) (GlobalTheory.FinPl.vecInd L) (GlobalTheory.FinPl.dualInd L)
  refine ⟨⟨_, GlobalTheory.FinPl.Comm.vecInd_mem L⟩, c⁻¹ • ⟨_, GlobalTheory.FinPl.Comm.dualInd_mem L⟩, ?_⟩
  have e : c = ∫ u, (GlobalTheory.FinPl.dualInd L u) * GlobalTheory.StepData.hat ψk ν (-1) (GlobalTheory.FinPl.vecInd L) u
      ∂(Measure.pi fun _ => ν) := by
    simp only [c, GlobalTheory.FinPl.Comm.fpair, GlobalTheory.StepData.hat]
    congr 1; funext u; ring
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, ← e, inv_mul_cancel₀ hc]

theorem contr_tens {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k)
    {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (φ₀ φ₀' : SB (n → k)) (Ξ₁ : SB (Matrix n n' k)) (Ξ₂ : SB (Matrix n'' n k)) (q : Matrix n n' k × Matrix n'' n k) :
    GlobalTheory.LocFlat.contr ψk ν (colTens φ₀ Ξ₁).1 (rowTens φ₀' Ξ₂).1 q =
      Ξ₁.1 q.1 * Ξ₂.1 q.2 * ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) := by
  simp only [GlobalTheory.LocFlat.contr, colTens_apply, rowTens_apply, Matrix.toCols₁_fromCols, Matrix.toRows₁_fromRows,
    GlobalTheory.StepData.hat]
  rw [← integral_const_mul]
  congr 1; funext u
  have h1 : (Matrix.fromRows q.2 (Matrix.of fun _ : Unit => u)) (Sum.inr ()) = u := rfl
  have h2 : ∀ y : n → k, (fun r => Matrix.fromCols q.1 (Matrix.of fun r (_ : Unit) => y r) r (Sum.inr ())) = y :=
    fun y => rfl
  simp only [h1, h2]
  rw [show (∫ y, Ξ₁.1 q.1 * φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν)) =
      Ξ₁.1 q.1 * ∫ y, φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν) by
    rw [← integral_const_mul]; congr 1; funext y; ring]
  ring
end GlobalTheory.ContractionLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffDen

theorem exists_den_avoid : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  intro E _ _ a b M G c hc x hcx hloc
  classical
  have hsm : ∀ d : 𝓞 E, (d : E) • x = d • x := fun d => by
    rw [← algebraMap_smul E d x]
  set J : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) _ x) with hJ
  have memJ : ∀ d : 𝓞 E, d ∈ J ↔ d • x ∈ M := fun d => by simp [hJ]
  have hc0 : (c : 𝓞 E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcx' : (c : 𝓞 E) • x ∈ M := by
    have hcE : ((c : 𝓞 E) : E) = (c : E) := by simp
    rw [← hsm, hcE]; exact hcx
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | (c : 𝓞 E) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(c : 𝓞 E)}) (by simpa using hc0)).subset ?_
    intro Q hQ
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hQ)
  set S : Set (HeightOneSpectrum (𝓞 E)) := {Q | (c : 𝓞 E) ∈ Q.asIdeal ∧ ¬ G Q} with hS
  have hSfin : S.Finite := hfin.subset fun Q hQ => hQ.1
  have hnot : ¬ ((J : Set (𝓞 E)) ⊆ ⋃ Q ∈ S, (Q.asIdeal : Set (𝓞 E))) := by
    intro hsub
    rcases S.eq_empty_or_nonempty with h0 | ⟨Q₀, _⟩
    · have hm := hsub ((memJ _).2 hcx')
      simp [h0] at hm
    obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime_finite hSfin (f := fun Q => Q.asIdeal) Q₀ Q₀
      (fun Q _ _ _ => Q.isPrime)).1 hsub
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ.2
    exact hs (hle ((memJ s).2 hsx))
  obtain ⟨d, hdJ, hdS⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hdS
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q :=
    fun Q hcQ hdQ => by_contra fun hG => hdS Q ⟨hcQ, hG⟩ hdQ
  by_cases hd0 : d = 0
  · refine ⟨c, hc0, ?_, fun Q hcQ _ => key Q hcQ (hd0 ▸ Q.asIdeal.zero_mem)⟩
    rw [hsm]; exact hcx'
  · exact ⟨d, hd0, by rw [hsm]; exact (memJ d).1 hdJ, key⟩

end GlobalTheory.OffDen
end

