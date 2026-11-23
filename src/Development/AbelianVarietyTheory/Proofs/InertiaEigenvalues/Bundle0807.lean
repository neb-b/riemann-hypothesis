module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseDataTypeCharacterEqLocalComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeCharUnits

open Formalism.L2.JoinChr GlobalTheory.ConjTwist Formalism.IndefR.Datum

theorem isLocUnit_locU {D : D7} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (a : 𝓞 D.host.E)
    (ha0 : (a : D.host.E) ≠ 0) (u : (kP PP)ˣ) (ha : (u : kP PP) = Ideal.Quotient.mk PP.asIdeal a) :
    IsLocUnit PP u (locU h.1.1 (Units.mk0 (a : D.host.E) ha0)) := by
  have haP : a ∉ PP.asIdeal := fun h0 => u.ne_zero (ha ▸ Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha1 : a ≠ 0 := fun h0 => haP (h0 ▸ zero_mem _)
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using h, by simp⟩, h.1.2.1⟩
  have hai : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra k
    exact haP ((h.2 a ha1).2 k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP h
  have he : idemAt PP * idemAt PP = idemAt PP := h.1.1
  have hb : toEAf D (incA D (a : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  have hxv : ((locU h.1.1 (Units.mk0 (a : D.host.E) ha0) : (AE D)ˣ) : AE D) =
      1 + idemAt PP * (incA D (a : D.host.E) - 1) := locU_val _ _
  have hxi : (((locU h.1.1 (Units.mk0 (a : D.host.E) ha0))⁻¹ : (AE D)ˣ) : AE D) =
      1 + idemAt PP * (incA D ((a : D.host.E)⁻¹) - 1) := by
    rw [GlobalTheory.HeckeDetChar.locU_inv, Units.val_inv_eq_inv_val, Units.val_mk0]
    rfl
  generalize locU h.1.1 (Units.mk0 (a : D.host.E) ha0) = x at hxv hxi
  generalize incA D (a : D.host.E) = b at hb hxv
  generalize incA D ((a : D.host.E)⁻¹) = b' at hai hxi
  have hv : toEAf D (x : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hxv, map_loc, hb]
    rfl
  have hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  refine ⟨?_, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx, ?_, hx, ?_⟩
  · rw [hxv]
    linear_combination (1 - b) * he
  · rw [hxv, map_loc, hinf, zero_mul, add_zero]
  · rw [hxi]
    have e1 : finPart D (1 + idemAt PP * (b' - 1)) = finPart D (1 - idemAt PP) + finPart D (idemAt PP * b') := by
      rw [← RingHom.map_add (f := _)]
      congr 1
      ring
    rw [e1]
    refine add_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D _ ?_) hai
    rw [← RingHom.map_mul]
    congr 1
    linear_combination he
  · have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F PP) e2).trans ?_
    rw [map_loc, h1, resS_oToS, ha]
    ring

theorem muC_eq_locK : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ χ : HChar D.host.E, ChrEq B.mu0 χ → ∀ PP ∈ B.G.Pg, ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0) (z : (kP PP)ˣ), (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.G.muC PP z : ℂˣ) : ℂ) = ((χ.locK PP (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro D S T B hB χ hχ PP hg u hu z hz
  obtain ⟨P, h1, h2, hP⟩ := hB.places.split
  have hI := hP.isIdemAt (h1 hg)
  have hx := isLocUnit_locU hI u hu z hz
  have e1 := hx.eq (hB.tame PP hg)
  have e2 := hx.eq_one hB.de.unram hP h2 (h1 hg) (Finset.disjoint_left.1 hB.places.disj hg)
  have e3 := hχ.2 PP _ (GlobalTheory.HeckeDetChar.isPlIdem hI) _ _ (locU_val hI.1.1 (Units.mk0 (u : D.host.E) hu))
  rw [Base.mu, MonoidHom.mul_apply, e2, mul_one] at e1
  rw [← e3, e1]
  rfl

end GlobalTheory.TypeCharUnits

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponentsStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  first | exact @GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip | exact GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip | (intros; apply GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BasePairChar

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem unrAt_of_unramAt {c : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hc : GlobalTheory.WeilParts.UnramAt ε c) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.LFun.UnrAt c w := by
  subst hw
  have key : ∀ y, Formalism.L2.Host.IsUnitAt w y → finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).2 fun P => by
      rw [show GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ)) =
        Neutral.B1.finiteSingle _ w y from GlobalTheory.LFun.finTens_locIdele w y]
      by_cases e : P = w
      · subst e; rw [GlobalTheory.LFun.finSingle_self]; exact hy.le
      · rw [GlobalTheory.LFun.finSingle_ne e, map_one]
  obtain ⟨α, rfl, h1, -⟩ := hε
  intro y hy
  have hs : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * ((GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1) =
      (GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1 := by
    refine GlobalTheory.LFun.tens_ext ?_ ?_
    · simp only [map_mul, map_sub, map_one, GlobalTheory.LFun.infTens_locIdele, sub_self, mul_zero]
    · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      have e2 := GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y
      refine FiniteAdeleRing.ext _ fun P => ?_
      simp only [map_mul, map_sub, map_one, e2]
      have hA : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E
          (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) =
          GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) := rfl
      rw [hA]
      change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) P *
          (Neutral.B1.finiteSingle D.host.E w y P - 1) = Neutral.B1.finiteSingle D.host.E w y P - 1
      rw [GlobalTheory.LFun.finAdEquiv_tmul, map_one, mul_one]
      by_cases hP : P = w
      · subst hP
        rw [GlobalTheory.LFun.finSingle_self]
        have : α (P.under (𝓞 D.host.F)) = 1 := h1
        rw [this, map_one, one_mul]
      · rw [GlobalTheory.LFun.finSingle_ne hP, sub_self, mul_zero]
  have h := hc _ hs (key y hy) (by
    rw [← map_inv]
    refine key _ ?_
    unfold Formalism.L2.Host.IsUnitAt at hy ⊢
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  exact (congrArg Circle.toUnits h).trans (map_one _)


end GlobalTheory.BasePairChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily : ∀ (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n), (∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) → F = 0 := by
  first | exact @GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | exact GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | (intros; apply GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongOneOfSuppAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SuppIntCong


set_option maxHeartbeats 2000000 in
theorem cong_one_of_suppAt : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (hQ : GA D V) (a : ℕ), 0 < a → SplitSet Q → SuppAt (idem Q) V hQ → ∃ c : ℕ, ∀ i j, (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) ∧ (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ)⁻¹.val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) := by
  intro D V Q hQ a ha hQs hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ P : HeightOneSpectrum (𝓞 D.host.E), AE D →+* P.adicCompletion D.host.E,
      ∀ P z, ev P z = ι (finPart D z) P :=
    ⟨fun P => ((GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  obtain ⟨evf, hevf⟩ : ∃ evf : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (Af D.host.F ⊗[D.host.F] D.host.E) →+* P.adicCompletion D.host.E, ∀ P y, evf P y = ι y P :=
    ⟨fun P => (GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom, fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQs.isIdemSum
  have e2 : ∀ P, P ∉ Q → ev P (idem Q) = 0 := fun P hP => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 P fun hh => hP (hh ▸ h')
  have hA1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ) = 1 := fun P hP hP' => by
    have hc := hcj (idem Q) (GlobalTheory.IdemSupport.cP P)
    rw [e2 _ hP', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at hc
    have hu : ev P (idem Q + cA D (idem Q)) = 0 := by rw [map_add (f := _), e2 P hP, hc, add_zero]
    have : (ev P).mapMatrix (mt V hQ - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev P ((mt V hQ - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ P, (ev P).mapMatrix (mt V hQ) * (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P => by
    rw [← map_mul, show mt V hQ * mt V hQ⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P hP hP' => by
    have := hinv P
    rwa [hA1 P hP hP', one_mul] at this
  set S := Q ∪ Q.image GlobalTheory.IdemSupport.cP with hS
  have hout : ∀ P, P ∉ S → P ∉ Q ∧ GlobalTheory.IdemSupport.cP P ∉ Q := fun P hP =>
    ⟨fun h' => hP (Finset.mem_union_left _ h'), fun h' => hP (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP P⟩))⟩

  have hN : ∀ P ∈ S, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have key : ∀ P' ∈ Q, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := fun P' hP' => by
      show ((∏ v ∈ Q, Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm v.asIdeal) hP'
      rw [hr, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact key P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact key P' hP'
  have hvN : ∀ P ∈ S, ∀ c : ℕ, Valued.v (evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E)) ≤
      WithZero.exp (-(c : ℤ)) := by
    intro P hP c
    have he : evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) = algebraMap D.host.E (P.adicCompletion D.host.E)
        (algebraMap (𝓞 D.host.E) D.host.E (((normProd Q : ℕ) : 𝓞 D.host.E) ^ c)) := by
      simp only [map_natCast, map_pow, Nat.cast_pow]
    rw [he, GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow (hN P hP) c)
  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  have ha0 : (a : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'

  have hgen : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E, (∀ P, P ∉ S → evf P y = 0) → ∃ c0 : ℕ, ∀ c, c0 ≤ c →
      ∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    intro y hy
    set u : Af D.host.F ⊗[D.host.F] D.host.E :=
      Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E) ((a : D.host.E)⁻¹ ^ 2) with hu
    have hau : ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * u = 1 := by
      rw [hu, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)),
        ← map_mul, Nat.cast_pow, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, map_one]
    let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => fn (Valued.v (evf P u)) + fn (Valued.v (evf P y))
    refine ⟨S.sup f, fun c hc => ⟨u * ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y, ?_, ?_⟩⟩
    · refine (h2 _).2 fun P => ?_
      rw [← hevf, map_mul, map_mul, map_mul, map_mul]
      by_cases hP : P ∈ S
      · have hle : f P ≤ c := (Finset.le_sup hP).trans hc
        calc _ ≤ WithZero.exp (fn (Valued.v (evf P u)) : ℤ) * WithZero.exp (-(c : ℤ)) *
              WithZero.exp (fn (Valued.v (evf P y)) : ℤ) :=
              mul_le_mul' (mul_le_mul' (hfn _) (hvN P hP c)) (hfn _)
          _ = WithZero.exp ((fn (Valued.v (evf P u)) : ℤ) + -(c : ℤ) + fn (Valued.v (evf P y))) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero]
              exact WithZero.exp_le_exp.2 (by simp only [f] at hle; omega)
      · rw [hy P hP, map_zero, mul_zero]; exact zero_le'
    · rw [← mul_assoc, ← mul_assoc, hau, one_mul]
  have hone : ∀ P i j, evf P ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) i j := fun P i j => by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have hy1 : ∀ i j P, P ∉ S → evf P ((finHom V hQ).val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hA1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ).val i j = finPart D (mt V hQ i j) := rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  have hy2 : ∀ i j P, P ∉ S → evf P ((finHom V hQ)⁻¹.val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hB1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ)⁻¹.val i j = finPart D (mt V hQ⁻¹ i j) := by rw [← map_inv]; rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  choose c1 hc1 using fun i j => hgen _ (hy1 i j)
  choose c2 hc2 using fun i j => hgen _ (hy2 i j)
  let g : Fin V.rank × Fin V.rank → ℕ := fun p => c1 p.1 p.2 + c2 p.1 p.2
  refine ⟨Finset.univ.sup g, fun i j => ⟨hc1 i j _ ?_, hc2 i j _ ?_⟩⟩
  · exact le_trans (Nat.le_add_right _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))
  · exact le_trans (Nat.le_add_left _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))

end GlobalTheory.SuppIntCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSums
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem exists_basisOf_of_classSum :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S :=
  fun D E h i hi j hj b =>
    GlobalTheory.TwistChoice.exists_basisOf D.nexp i j b _ (GlobalTheory.TwistChoice.th_fg D.nexp E h i hi j hj b)

end GlobalTheory.TwInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentMapNonzeroOfSmallFieldForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.NX

noncomputable section

namespace GlobalTheory

theorem exists_desc_of_isKsForm : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), (S.A j).IsKsForm → ∀ (i : D.ntw.Tw) (b : Bool) (x : S.WL j), x ≠ 0 →
    ∃ Φ : S.WL j →+ Fm S i j b, Φ x ≠ 0 ∧
      (∀ (c : ↥D.LL0) (w : S.WL j), Φ (((c : ↥D.LL0) : D.what₂.LL) • w) = readLL0 S i b c • Φ w) ∧
      ∀ (T : Module.End D.what₂.LL (S.WL j)) (hT : ∀ w ∈ (S.A j).WK, T w ∈ (S.A j).WK) (w : S.WL j),
        Φ (T w) = Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
          ((T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT) (Φ w) := by
  intro D S j hK i b x hx
  classical
  obtain ⟨n, v, hvK, hliK, hspK, hliL, hspL⟩ := hK
  let bL : Module.Basis (Fin n) D.what₂.LL (S.WL j) := Module.Basis.mk hliL (by rw [hspL])
  let bK0 : Module.Basis (Fin n) S.Ks (Submodule.span S.Ks (Set.range v)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) S.Ks (FmK S j) := bK0.map (LinearEquiv.ofEq _ _ hspK)
  let ι : FmK S j →ₗ[S.Ks] S.WL j := (S.A j).WK.subtype
  have hbK : ∀ r, ι (bK r) = v r := by
    intro r
    show ((bK0 r : Submodule.span S.Ks (Set.range v)) : S.WL j) = v r
    exact congrArg Subtype.val (Module.Basis.span_apply hliK r)
  have hbL : ∀ r, bL r = v r := by intro r; simp [bL]
  let bF : Module.Basis (Fin n) (KB S i b) (Fm S i j b) := Algebra.TensorProduct.basis (KB S i b) bK
  obtain ⟨r0, ha⟩ : ∃ r0, bL.repr x r0 ≠ 0 := by
    by_contra h; push_neg at h; exact hx (bL.ext_elem fun r => by simpa using h r)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ↥D.LL0 D.what₂.LL, g (bL.repr x r0) ≠ 0 := by
    by_contra h; push_neg at h; exact ha ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)
  let f : D.what₂.LL →ₗ[↥D.LL0] ↥D.LL0 := (g (bL.repr x r0))⁻¹ • g
  have hfa : f (bL.repr x r0) = 1 := by simp [f, hg]
  have hfc : ∀ (c : ↥D.LL0) (y : D.what₂.LL), f ((c : D.what₂.LL) * y) = c * f y := by
    intro c y
    rw [show (c : D.what₂.LL) * y = c • y from (Algebra.smul_def c y).symm, map_smul, smul_eq_mul]
  let φ : (Fin n → D.what₂.LL) →+ (Fin n → KB S i b) :=
    AddMonoidHom.compLeft ((readLL0 S i b).toAddMonoidHom.comp f.toAddMonoidHom) (Fin n)
  let Φ : S.WL j →+ Fm S i j b :=
    (bF.equivFun.symm.toLinearMap.toAddMonoidHom).comp (φ.comp bL.equivFun.toLinearMap.toAddMonoidHom)
  have hΦ : ∀ w, bF.equivFun (Φ w) = fun r => readLL0 S i b (f (bL.repr w r)) := by
    intro w
    show bF.equivFun (bF.equivFun.symm (φ (bL.equivFun w))) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun (hΦ x) r0
    rw [h0, map_zero, hfa, map_one] at this
    exact zero_ne_one this
  · intro c w
    apply bF.equivFun.injective
    rw [hΦ, bF.equivFun.map_smul, hΦ, bL.repr.map_smul]
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, map_smul, Finsupp.smul_apply]
    rw [hfc, map_mul]
  · intro T hT w
    let T' : Module.End S.Ks (FmK S j) := (T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT
    let t := LinearMap.toMatrix bK bK T'
    have hTm : LinearMap.toMatrix bL bL T = t.map (algebraMap S.Ks D.what₂.LL) := by
      ext r q
      simp only [t, LinearMap.toMatrix_apply, Matrix.map_apply]
      have e1 : T (bL q) = ι (T' (bK q)) := by
        rw [hbL, ← hbK]; rfl
      have e2 : T (bL q) = ∑ s, (algebraMap S.Ks D.what₂.LL (bK.repr (T' (bK q)) s)) • bL s := by
        rw [e1]; conv_lhs => rw [← bK.sum_repr (T' (bK q))]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul, hbK, hbL, algebraMap_smul]
      rw [e2, Module.Basis.repr_sum_self]
    apply bF.equivFun.injective
    have hbc : Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' = LinearMap.baseChange (KB S i b) T' := rfl
    change bF.equivFun (Φ (T w)) = bF.equivFun (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' (Φ w))
    rw [hbc]
    have hMF : LinearMap.toMatrix bF bF (LinearMap.baseChange (KB S i b) T') = t.map (algebraMap S.Ks (KB S i b)) :=
      LinearMap.toMatrix_baseChange _ _ _ _
    have hL : ∀ r, bL.repr (T w) r = ∑ q, algebraMap S.Ks D.what₂.LL (t r q) * bL.repr w q := by
      intro r
      rw [← LinearMap.toMatrix_mulVec_repr bL bL T w, hTm]; rfl
    have hKB : ∀ r, bF.equivFun (LinearMap.baseChange (KB S i b) T' (Φ w)) r =
        ∑ q, algebraMap S.Ks (KB S i b) (t r q) * bF.equivFun (Φ w) q := by
      intro r
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr bF bF (LinearMap.baseChange (KB S i b) T') (Φ w)) r
      rw [hMF] at h1
      exact h1.symm
    funext r
    rw [hΦ, hKB, hΦ]
    simp only []
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hL, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← S.kKs_spec, hfc, map_mul]; rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E), FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) = (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ConjFix.fixBase_split_conj | exact GlobalTheory.ConjFix.fixBase_split_conj | (intros; apply GlobalTheory.ConjFix.fixBase_split_conj <;> assumption)
end

