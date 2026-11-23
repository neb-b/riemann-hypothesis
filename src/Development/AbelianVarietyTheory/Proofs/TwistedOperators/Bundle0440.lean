module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumFinAdele

theorem exists_finAdele_of_idemSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  intro D P e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, hz⟩ := he
  have hex : ∀ PP ∈ P, ∃ α : Af D.host.F,
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = es PP + cA D (es PP) ∧
      evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) α = 1 ∧
      ∀ v', v' ≠ HeightOneSpectrum.under (𝓞 D.host.F) PP → evalV D.host.F v' α = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v ε (hes PP hPP) hε a3
    obtain ⟨α, rfl, h1, h2⟩ := hε
    exact ⟨α, a3.symm, hv ▸ h1, hv ▸ h2⟩
  choose! α hα using hex
  have hsum : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (∑ PP ∈ P, α PP)) =
      ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) := by
    have hp : pairA D.host.F 0 (∑ PP ∈ P, α PP) = ∑ PP ∈ P, pairA D.host.F 0 (α PP) := by
      have hadd : ∀ a b : Af D.host.F, pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
        fun a b => Prod.ext (add_zero 0).symm rfl
      exact map_sum (AddMonoidHom.mk' (pairA D.host.F 0) hadd) α P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sum, map_sum (cA D), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun PP hPP => (hα PP hPP).1
  refine ⟨∑ PP ∈ P, α PP, hsum, ?_, ?_⟩
  · intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun PP hPP => (hα PP hPP).2.2 w (hw PP hPP).symm
  · intro PP hPP
    have h1 := GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one P _ he' PP hPP
    rw [← hsum] at h1
    have h2 : (evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) (∑ PP ∈ P, α PP)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Fv D.host.F _ ⊗[D.host.F] D.host.E) := h1
    haveI : Module.Free D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Flat D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) := Module.Flat.of_free
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
      (A := Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply, h2]
    rfl

end GlobalTheory.IdemSumFinAdele

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidue
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDet

theorem toEAf_detAt_mem {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) :
    toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hg
  have hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he]))
  have hd := GlobalTheory.VecInv.isDetAt_detAt e he V g
  unfold IsDetAt at hd
  rw [hd, map_add (f := _), map_mul, map_sub, map_one, ← ha]
  exact add_mem (mul_mem hE a.2) (sub_mem (one_mem _) hE)

theorem toEAf_detAt {D : D7} (V : HSp D) (g : GA D V) (e : AE D) (he : e * e = e) :
    toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D) =
      toEAf D e * toEAf D (Formalism.L2.Theta.mt V g).det + (1 - toEAf D e) := by
  have hd := GlobalTheory.VecInv.isDetAt_detAt e he V g
  unfold IsDetAt at hd
  rw [hd, map_add (f := _), map_mul, map_sub, map_one]

theorem map_eq_of_idem {R K : Type} [Ring R] [Ring K] (S : Subring R) (f : S →+* K) (x ε a : S) (h1 : f ε = 1)
    (hx : (x : R) = (ε : R) * (a : R) + (1 - (ε : R))) : f a = f x := by
  have hx' : x = ε * a + (1 - ε) := Subtype.ext (by push_cast; exact hx)
  rw [hx', map_add (f := _), map_mul, map_sub, map_one, h1]
  simp

theorem toEAf_detAt_inv_mem {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) :
    toEAf D (((GlobalTheory.VecInv.detAt e he V g)⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv (GlobalTheory.VecInv.detAt e he V) g]
  exact toEAf_detAt_mem (by rw [map_inv]; exact inv_mem hg) e he

theorem res_detAt {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) (PP : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt e PP) :
    ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
      resS D.host.F PP ⟨toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D), toEAf_detAt_mem hg e he⟩ := by
  obtain ⟨a, ha, hred⟩ := GlobalTheory.VecInv.exists_det_int hg
  obtain ⟨hE, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP hP
  rw [hred PP]
  refine map_eq_of_idem _ (resS D.host.F PP) _ ⟨toEAf D e, hE⟩ a h1 ?_
  show toEAf D _ = toEAf D e * (a : Lev.EAf D) + (1 - toEAf D e)
  rw [toEAf_detAt V g e he, ha]

theorem exists_detAt_int : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V), finE V g ∈ St β → ∀ e : AE D, e * e = e → ∃ x : (AE D)ˣ, IsDetAt e V g x ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP : Pl D.host.E, Formalism.L2.NTheta.IsIdemAt e PP → ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ := by
  intro D V β g hg e he
  exact ⟨GlobalTheory.VecInv.detAt e he V g, GlobalTheory.VecInv.isDetAt_detAt e he V g,
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (toEAf_detAt_mem hg e he),
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (toEAf_detAt_inv_mem hg e he),
    toEAf_detAt_mem hg e he, fun PP hP => res_detAt hg e he PP hP⟩

end GlobalTheory.StabDet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrOffShift

theorem algebraMap_mem_conjI {D : D7} (I : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.F)
    (h : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ I) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ conjI I := by
  apply Ideal.subset_span
  refine ⟨_, h, ?_⟩
  have h2 := GlobalTheory.Ker.MovLev.bar_algebraMap (D := D) s
  have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) h2
  simp only [Lev.bar] at h3
  have h4 := IsCMField.coe_ringOfIntegersComplexConj D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s)
  exact h3.symm.trans h4

theorem shift_mult : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  intro D r Pg Q L w hne u hu
  classical
  have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
    intro PP hPP
    by_contra hcon
    push_neg at hcon
    apply hne PP hPP
    have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := by
      intro s hs
      exact hcon s hs
    exact HeightOneSpectrum.ext
      ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
  choose! tf htf1 htf2 using hex
  refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
  · have : ∏ PP ∈ Pg ∪ Q, tf PP ∈ w.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun c hc => htf2 c hc)
    exact this
  · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP)
        ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
      rw [map_prod]
      exact Ideal.prod_mem_prod (fun PP hPP => algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP))
    have h1 := hu _ (algebraMap_mem_conjI (D := D) _ _ hmem)
    exact Submodule.smul_le_right h1

end GlobalTheory.TrOffShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierStandardLatticeOfMoverTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.MoverStd

theorem exists_mul_std : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  intro D S k₀ Λ' σ w hσ hk hm v hv
  obtain ⟨hfg, -, -⟩ := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    congr 2
    funext i
    exact (Pi.basisFun_apply D.host.E (Fin S.rank) i).symm
  have ht : ∀ u, MovLev.lf (MovLev.idem w.asIdeal) • (fmtC S k₀⁻¹ *ᵥ u) = MovLev.lf (MovLev.idem w.asIdeal) • u :=
    fun u => MovLev.smul_mulVec_eq _ _ (fun v' => by
      by_cases hv' : w.asIdeal ≤ v'.asIdeal
      · have e : v' = w := (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v'.isPrime.ne_top hv')).symm
        subst e
        refine Or.inr fun ε hε i j => ?_
        obtain ⟨α, rfl, -, hα0⟩ := hε
        have hασ : α * σ = 0 := by
          refine FiniteAdeleRing.ext D.host.F fun u => ?_
          change α u * σ u = 0
          by_cases hu : u = v'
          · subst hu
            rw [show σ u = 0 from hσ, mul_zero]
          · rw [show α u = 0 from hα0 u hu, zero_mul]
        have hmul : pairA D.host.F 0 α * (1 - pairA D.host.F 0 σ) = pairA D.host.F 0 α := by
          refine Prod.ext ?_ ?_
          · change (0 : Ainf D.host.F) * (1 - 0) = 0
            rw [zero_mul]
          · change α * (1 - σ) = α
            rw [mul_sub, mul_one, hασ, sub_zero]
        have h0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt S k₀⁻¹ - 1) i j = 0 := by
          rw [← hmul, map_mul, mul_assoc, map_sub, map_one, hk i j, mul_zero]
        have := congrArg (cA D) h0
        rw [map_mul, map_zero, Matrix.sub_apply, map_sub] at this
        have e1 : cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
            algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
          change (pairA D.host.F 0 α) ⊗ₜ D.sp.cm.sig 1 = (pairA D.host.F 0 α) ⊗ₜ 1
          rw [map_one]
        have e' : cA D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
            (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
          rw [Matrix.one_apply]
          split_ifs
          exacts [map_one _, map_zero _]
        rw [e1, e'] at this
        exact this
      · exact Or.inl (if_neg hv')) u
  obtain ⟨t, htw, H⟩ := MovLev.exists_mul (E := D.host.E) w.asIdeal.primeCompl w.asIdeal (fun v' hv' => by
      have h1 : ¬ v'.asIdeal ≤ w.asIdeal := fun h => hv' ((v'.isMaximal.eq_of_le w.isPrime.ne_top h) ▸ le_rfl)
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
      exact ⟨a, ha', ha⟩)
    (L := Submodule.span (𝓞 D.host.E) {v}) (Λ := stdL D.host.E S.rank) (Submodule.fg_span_singleton v) hfg hs
    (fun z hz => by
      have hz' : z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin S.rank → D.host.E)) := AddSubgroup.closure_mono (by
        rintro y ⟨a, ha, x, hx, e⟩
        exact ⟨a, ha, x, (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)) hx, e⟩) hz
      change MovLev.lf (MovLev.idem w.asIdeal) • z ∈ _
      rw [← ht z]
      exact MovLev.hat_int (MovLev.idem_int _) ((hm _).2 ⟨z, hz', rfl⟩))
  exact ⟨t, htw, H v (Submodule.mem_span_singleton_self v)⟩

end GlobalTheory.Ker.MoverStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def InK (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)

structure IsGKSub (A : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ τ g, InK M τ g → ∀ f ∈ A, rTr V (atTau θ V τ g) f ∈ A
  lie : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f ∈ A, Rder θ V τ X f ∈ A

def IsIrrGKSub (A : Submodule ℂ (GA D V → ℂ)) : Prop :=
  IsGKSub θ M A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ (GA D V → ℂ), B ≤ A → IsGKSub θ M B → B = ⊥ ∨ B = A

def gkGen (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {A | ψ ∈ A ∧ IsGKSub θ M A}

theorem mem_gkGen (ψ : GA D V → ℂ) : ψ ∈ gkGen θ M ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isGKSub_gkGen (ψ : GA D V → ℂ) : IsGKSub θ M (gkGen θ M ψ) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => hA.2.k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => hA.2.lie τ X hX f (Submodule.mem_sInf.1 hf A hA)

theorem gkGen_le {ψ : GA D V → ℂ} {A : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ A) (hA : IsGKSub θ M A) :
    gkGen θ M ψ ≤ A :=
  sInf_le ⟨hψ, hA⟩

structure IsGKMult
    (F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ)) : Prop where
  aut : ∀ u, IsAutFunSm θ V (F u)
  cusp : ∀ u, IsCuspFun V (F u)
  equivK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
    ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)
  equivLie : ∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
      (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
      F (Function.update u τ w) = Rder θ V τ X (F u)

def multSpan : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {f | ∃ (F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
    (GA D V → ℂ)) (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), IsGKMult θ M F ∧ f = F u}

def IsKFinCuspOfType (f : GA D V → ℂ) : Prop :=
  IsAutFunSm θ V f ∧ IsCuspFun V f ∧ (∀ τ, IsTypeAt θ V τ (S τ) f) ∧
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ f ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W

theorem IsGKMult.smul {F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
    (GA D V → ℂ)} (h : IsGKMult θ M F) (c : ℂ) : IsGKMult θ M (c • F) := by
  constructor
  · intro u
    exact Formalism.IndefR.Mult.isAutFunSm_smul θ V (h.aut u) c
  · intro u
    exact Formalism.IndefR.Mult.isCuspFun_smul V (h.cusp u) c
  · intro τ g hg hk u w hw
    rw [smul_apply, smul_apply, h.equivK τ g hg hk u w hw]
    rfl
  · intro τ X hX u w hw
    rw [smul_apply, smul_apply, h.equivLie τ X hX u w hw,
      Formalism.IndefR.Mult.rder_smul]

theorem exists_sum_of_mem_multSpan {ψ : GA D V → ℂ} (hψ : ψ ∈ multSpan θ M) :
    ∃ (n : ℕ) (F : Fin n → MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
      (GA D V → ℂ)) (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, IsGKMult θ M (F l)) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  obtain ⟨n, c, f, hf⟩ := Submodule.mem_span_set'.1 hψ
  choose F u hF hFu using fun i => (f i).2
  refine ⟨n, fun l => c l • F l, u, fun l => (hF l).smul θ M (c l), fun g => ?_⟩
  rw [← hf, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hFu l]
  rfl

end GlobalTheory.CuspGK

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

def frS (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pS p).rank) D.host.E
  | .chi i j => N.fr (.grid (i + 1) j)
  | .mu _ i j => N.fr (.grid i j)
  | .core i => N.fr (.core (i + 1))
  | .top _ j => N.fr (.top j)

def frT (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pT p).rank) D.host.E
  | .chi i j => N.fr (.grid i j)
  | .mu _ i j => N.fr (.grid i (j + 1))
  | .core i => N.fr (.core i)
  | .top _ j => N.fr (.top (j + 1))

def inV {n : ℕ} (B : GL (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  (B : Matrix (Fin n) (Fin n) D.host.E).mulVec '' (Λ : Set (Fin n → D.host.E))

end GlobalTheory.MovedDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParOfSigOK
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.NodePar

theorem goodPar_of_sigOK {D : D7} (N : GlobalTheory.Grid.Node D) (h : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  have hm := GlobalTheory.TowerSplit.hasSignature_of_model N.M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ)] at hm
  have hs : Formalism.UG.HasSignature (gramAt D N.V τ) (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 := h (tauE D τ)
  obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ hm hs
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), e1, e2⟩

end GlobalTheory.NodePar
end
end

