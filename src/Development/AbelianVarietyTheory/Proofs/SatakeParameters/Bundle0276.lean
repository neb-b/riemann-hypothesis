module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNormStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  first | exact @GlobalTheory.FramesDet.det_frame_mul_congAt | exact GlobalTheory.FramesDet.det_frame_mul_congAt | (intros; apply GlobalTheory.FramesDet.det_frame_mul_congAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartPointFramesMovedByLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_point_frames_moved_by_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2)))
    (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    ∃ (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (κP : GLQ t.X.E (D.R.N t.m2) (rowSG t.Pr t.sel (t.tup μ)))
      (c : rowSG t.Pr t.sel (t.tup μ) → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * ((κP P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) (c P)) ∧
      q.deco.1.N = p.deco.1.N ∧ q.deco.1.f = p.deco.1.f ∧
      (∀ P, ((c P : t.X.Kˣ) : t.X.K) * z P = 1) ∧
      (∀ P, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det ((κP P)⁻¹).1 : t.X.Eˣ) : t.X.E) =
        rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) ∧
      ∀ P, InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 ((κP P)⁻¹).1) := by
  first | exact @GlobalTheory.LevSrcPt.exists_pt_lev | exact GlobalTheory.LevSrcPt.exists_pt_lev | (intros; apply GlobalTheory.LevSrcPt.exists_pt_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodChartLastStepAllTuples
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue


set_option maxHeartbeats 1000000 in
theorem chart_last_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a B.R.m).Cl → Ch) (Kc : Fam I l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a B.R.m le_rfl chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨K1, hR, -, -, hfin, -⟩ := GlobalTheory.T.chart_lastStep_twistBasePoint I hI hP l Z u a Q (F.cls B.R.m le_rfl (Or.inr rfl)) hQ
    (hF.ends B.R.m le_rfl (Or.inr rfl))
  obtain ⟨k, hk, -⟩ := hR
  obtain ⟨Kc, h1, h2⟩ := _root_.GlobalTheory.TwU.AtTrue.charts_funKilled_one I hI hP l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) Unit (fun _ => ()) K1 ⟨k, hk⟩
    (fun β => by cases β; exact hfin)
  exact ⟨Unit, inferInstance, fun _ => (), Kc, h1, h2⟩

end GlobalTheory.TwU.AtTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

namespace GlobalTheory.OtherSplitPlace

theorem exists_isSplitAt_under_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧
      w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  intro E _ _ _ w₀
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩

  have hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w₀.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w₀.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hp₀
  · simpa using hN

end GlobalTheory.OtherSplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderHeckeCharGalois
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.HeckeToGal

theorem exists_galChar_of_finite_order : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (η : HChar K) (n : ℕ), 0 < n → η ^ n = 1 → ∃ χ : G K Ω →* ℂˣ,
      IsOpen (χ.ker : Set (G K Ω)) ∧ (χ = 1 → η = 1) ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
        IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v := by
  intro Ω _ K _ _ _ _ η n hn hη
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have hηn : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar K => ξ.1 x) hη
  have hopen : IsOpen (η.1.ker : Set (Ideles K)) := isOpen_ker_of_pow η.1 η.2.1 hn hηn
  have hinf : infConn K ≤ η.1.ker := by
    rintro _ ⟨y, hy, rfl⟩
    let φ : (InfiniteAdeleRing K)ˣ →* ℂˣ :=
      η.1.comp (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))
    have hc : Continuous fun z : InfiniteAdeleRing K => (z, (1 : FiniteAdeleRing (𝓞 K) K)) :=
      continuous_id.prodMk continuous_const
    have hφ : Continuous φ := η.2.1.comp (Continuous.units_map _ hc)
    have hop : IsOpen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := isOpen_ker_of_pow φ hφ hn (fun x => hηn _)
    have hcl : IsClopen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
    exact hcl.connectedComponent_subset (one_mem φ.ker) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (Subgroup.isClosed_of_isOpen _ hopen)
    rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (η.2.2 k)
  have hs : Function.Surjective art := ha.quot.surjective
  let ηb : Gab K Ω →* ℂˣ :=
    art.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩
  have hηb : ∀ x, ηb (art x) = η.1 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply art (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩ x
  have hηbc : Continuous ηb := by
    refine ha.quot.isQuotientMap.continuous_iff.mpr ?_
    have e : (ηb ∘ art) = η.1 := funext hηb
    rw [e]
    exact η.2.1
  let χ : G K Ω →* ℂˣ := (ηb.comp (toAb K Ω))⁻¹
  have hχ : ∀ σ, χ σ = (ηb (toAb K Ω σ))⁻¹ := fun σ => rfl
  have hχc : Continuous χ := by
    have ht : Continuous (toAb K Ω) := (QuotientGroup.isQuotientMap_mk _).continuous
    exact (hηbc.comp ht).inv
  have hχn : ∀ σ, χ σ ^ n = 1 := fun σ => by
    obtain ⟨x, hx⟩ := hs (toAb K Ω σ)
    rw [hχ, ← hx, hηb, inv_pow, hηn, inv_one]
  refine ⟨χ, isOpen_ker_of_pow χ hχc hn hχn, fun h1 => ?_, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
    have e := DFunLike.congr_fun h1 σ
    rw [hχ, hσ, hηb, MonoidHom.one_apply, inv_eq_one] at e
    exact e
  · filter_upwards [(GlobalTheory.Mem.UnrAe.unr_ae_and_level K η).1.compl_mem_cofinite] with v hv
    have hv : η.UnrAt v := by simpa using hv
    intro A σ hA hσ
    obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
    rw [hχ, ← map_inv, ← map_inv, ← e, hηb, ← η.val_eq hv x hx]
    rfl

end GlobalTheory.HeckeToGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplRat

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}


open Classical in
theorem exists_pass_rat (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) :
    ∃ κ : GLQ X.E (R.N j) (rowSG Pr sel mu),
      (∀ P, frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) ∧
      (∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL (R.N j) P.1 (κ P) = 1) ∧ (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1) := by
  have h : ∀ P : rowSG Pr sel mu, ∃ k : GLint X.E (R.N j) P.1,
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * (k⁻¹).1) ∧ GlobalTheory.TopStep.redGL (R.N j) P.1 k = 1 ∧ (P.1 ∉ Pr.vGs → k = 1) := by
    intro P
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨κ0, h1, h2⟩ := liftFr_smul p.deco ((g, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)) ⟨P.1, hP⟩
      have hr : GlobalTheory.TopStep.redGL (R.N j) P.1 κ0 = 1 := GlobalTheory.TopStep.redGL_eq κ0 fun x hx => by
        rw [h2 x hx]
        simp
      refine ⟨κ0⁻¹, ?_, by rw [map_inv, hr, inv_one], fun h => absurd hP h⟩
      unfold frsF
      rw [dite_eq_left hP, dite_eq_left hP, inv_inv]
      exact h1.trans (mul_assoc _ _ _)
    · refine ⟨1, ?_, map_one _, fun _ => rfl⟩
      unfold frsF
      rw [dite_eq_right hP, dite_eq_right hP]
      show g.1 * _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
      simp [mul_assoc]
      rfl
  choose κ hκ using h
  exact ⟨κ, fun P => (hκ P).1, fun P => (hκ P).2.1, fun P => (hκ P).2.2⟩

theorem levAt_one {n : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (P : rowSG Pr sel mu)
    (k : GLint X.E n P.1) (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) : GlobalTheory.TopLaw.LevAt Λ Θ P k 1 := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · have hm : GlobalTheory.TopStep.redGL n P.1 k ∈ (Λ ⟨P.1, hP⟩).H := by rw [hr]; exact one_mem _
    refine ⟨hm, ?_⟩
    rw [show (⟨_, hm⟩ : (Λ ⟨P.1, hP⟩).H) = 1 from Subtype.ext hr, map_one]
  · obtain rfl := h1 hP
    exact ⟨one_mem _, (map_one _).symm⟩

end Gen

section Cos

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}


open Classical in
theorem sameCoset_pass (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (P : rowSG Pr sel mu) (k : GLint X.E n P.1)
    (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) (y0 : Sp X.E n)
    (hy0 : P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 l)) (v : Sp X.E n) :
    SameCoset sel mu cst P (k.1 v) y0 ↔ SameCoset sel mu cst P v y0 := by
  by_cases hP : P.1 ∈ Pr.vGs
  · unfold SameCoset
    simp only [if_pos hP]
    have hk : k⁻¹ ∈ GlobalTheory.TopStep.prinCong n P.1 1 :=
      GlobalTheory.CplCosetPt.mem_prinCong_one_of_redGL (GlobalTheory.TopStep.qOf_notMem_sq hX hPr hP) _ (by rw [map_inv, hr, inv_one])
    exact GlobalTheory.CplCosetPt.sameCoset_loc P.1 0 1 1 k.1 1 k⁻¹ k.2 (one_mem _) hk (by simp) (by omega) y0 (hy0 hP)
      (fun l => by simpa using GlobalTheory.TopStep.intAt_zero) v
  · obtain rfl := h1 hP
    exact Iff.rfl


open Classical in
theorem coset_image (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (fp fq : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (κ : GLQ X.E n (rowSG Pr sel mu)) (hκ : ∀ P, fq P = g * (fp P * ((κ P)⁻¹).1))
    (hr : ∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL n P.1 (κ P) = 1) (h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1)
    (y0 : rowSG Pr sel mu → Sp X.E n) (hy0 : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((fq P).symm y) (y0 P)} =
      (fun v => g v) '' {y | ∀ P, SameCoset sel mu cst P ((fp P).symm y) (y0 P)} := by
  have e : ∀ P y, (fq P).symm y = (κ P).1 ((fp P).symm (g.symm y)) := by
    intro P y
    apply (fq P).injective
    rw [LinearEquiv.apply_symm_apply, hκ P]
    show y = g (fp P (((κ P)⁻¹).1 ((κ P).1 ((fp P).symm (g.symm y)))))
    rw [Subgroup.coe_inv]
    show y = g (fp P ((κ P).1.symm ((κ P).1 ((fp P).symm (g.symm y)))))
    simp
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, e]
  constructor
  · intro h
    refine ⟨g.symm y, fun P => (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).1 (h P), by simp⟩
  · rintro ⟨z, hz, rfl⟩ P
    rw [LinearEquiv.symm_apply_apply]
    exact (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).2 (hz P)


open Classical in
theorem coset_mem_ybSet (p : ChPt (R := R) sel mu u j) (y0 : rowSG Pr sel mu → Sp X.E (R.N j))
    (hy0 : ∀ (P : rowSG Pr sel mu) l, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((frsF sel mu p P).symm y) (y0 P)} ∈ ybSet sel mu cst p.deco.1.N := by
  obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (frsF sel mu p) y0
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      exact_mod_cast this
    have hqI : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 X.E)
    rw [← (frsF sel mu p P).apply_symm_apply (_ • y), GlobalTheory.TwV.Model.frsF_mem, GlobalTheory.TopStep.mem_stdAt]
    intro l
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have hs := hy P l
    have h0 := hy0 P l
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [if_pos hP, pow_zero, inv_one, one_mul, pow_one] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_one, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) * (frsF sel mu p P).symm y l =
          ((qOf P.1 : ℕ) : X.E) * ((frsF sel mu p P).symm y - y0 P) l + ((qOf P.1 : ℕ) : X.E) * y0 P l := by
        simp only [Pi.sub_apply]; ring
      rw [e]
      exact (hqI.mul hs).add h0
    · simp only [if_neg hP] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_natCast, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) ^ cst.M * (frsF sel mu p P).symm y l =
          (((qOf P.1 : ℕ) : X.E) ^ cst.M * ((qOf P.1 : ℕ) : X.E) ^ cst.M) *
            ((((qOf P.1 : ℕ) : X.E) ^ cst.M)⁻¹ * ((frsF sel mu p P).symm y - y0 P) l) + ((qOf P.1 : ℕ) : X.E) ^ cst.M * y0 P l := by
        simp only [Pi.sub_apply]
        field_simp
        ring
      rw [e]
      exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul hs).add h0
  · ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_locLat]
    refine forall_congr' fun P => ?_
    rw [← GlobalTheory.TwV.Model.sameCoset_iff sel mu cst p P z y]
    exact ⟨fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (GlobalTheory.TwV.Model.sameCoset_symm _ _ _ (hy P)),
      fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (hy P)⟩

end Cos

section Main

theorem unitV_det_one {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k : GLint E n P) (hr : GlobalTheory.TopStep.redGL n P k = 1) :
    LocE.unitV χ ((LinearEquiv.det k.1 : Eˣ) : E) = 1 := by
  rw [GlobalTheory.TopStep.unitV_congr χ (b := 1) ?_, GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one]
  rw [(GlobalTheory.TopStep.det_glint k).2, GlobalTheory.TopStep.reduction_one₂, ← GlobalTheory.TopStep.redGL_val, hr]
  simp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiPt_cpl_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i = t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi hm β β' x x' p p' _ _ g g' w
  classical
  subst hm
  have hX : t.X.Ok := hPins.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  obtain ⟨κ, hκ, hr, h1⟩ := exists_pass_rat (R := D.R) p g
  obtain ⟨κ', hκ', hr', h1'⟩ := exists_pass_rat (R := D.R) p' g'
  have hy0 : ∀ (P : SB t μ) l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      y0At A (t.m2 + 1) hi β' P l) := by
    intro P l
    have e : y0At A (t.m2 + 1) hi β' P = A.y0 β' P := by
      unfold y0At
      rw [dite_eq_left rfl]
    rw [e]
    exact GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie β' P l
  have hY : cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ) p'.deco.1.N := coset_mem_ybSet p' _ hy0
  have hC : cosetOf A (t.m2 + 1) hi β' (((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG (E := t.X.E) (n := D.R.N (t.m2 + 1)) (SG := t.Pr.vGs) ×
      GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p') =
      (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' :=
    coset_image hX hPr _ _ g'.1 κ' hκ' hr' h1' _ (fun P hP l => by simpa [hP] using hy0 P l)
  have hY2 : (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ)
      ((((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG (E := t.X.E) (n := D.R.N (t.m2 + 1)) (SG := t.Pr.vGs) ×
        GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p').deco.1.N) :=
    (ybSet_gmap t.sel (t.tup μ) (t.cst μ) _ g'.1 _).2 hY
  have law := GlobalTheory.CoupledLaw.xiCpl1_law (Ch := t.Ch) (L := t.idx μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') hX hPr hL hY hY2 hκ hκ' (a := fun _ => 1) (a' := fun _ => 1)
    (fun P => levAt_one _ _ P _ (hr P) (h1 P)) (fun P => levAt_one _ _ P _ (hr' P) (h1' P)) w
    (Formalism.L2.Ker.phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w)
  have hprod : ∀ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ⁻¹ P).1 : t.X.Eˣ) : t.X.E) *
      rhoT t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : t.X.Eˣ) : t.X.E) = 1 := by
    intro P
    unfold rhoS rhoT
    rw [Pi.inv_apply, Pi.inv_apply, unitV_det_one _ _ (by rw [map_inv, hr P, inv_one]),
      unitV_det_one _ _ (by rw [map_inv, hr' P, inv_one]), mul_one]
  rw [Finset.prod_eq_one fun P _ => hprod P, mul_one] at law
  simp only [Finset.prod_const_one, inv_one, mul_one, Units.val_one, one_mul] at law
  unfold xiPt
  rw [dite_eq_right (lt_irrefl _), if_pos rfl, dite_eq_right (lt_irrefl _), if_pos rfl, hC]
  exact law

end Main

end GlobalTheory.CplRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramesOfRightTranslatePointPrincipalCongruenceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_of_right_translate_point_principal_congruence : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  first | exact @GlobalTheory.LevFrames.frames_lev | exact GlobalTheory.LevFrames.frames_lev | (intros; apply GlobalTheory.LevFrames.frames_lev <;> assumption)
end

