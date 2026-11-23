module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjType

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

noncomputable def rt (P : HeightOneSpectrum (𝓞 E)) : ℝ := (Real.sqrt ((Ideal.absNorm P.asIdeal : ℕ) : ℝ))⁻¹

theorem rt_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < rt P :=
  inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot))))

theorem rt_sq (P : HeightOneSpectrum (𝓞 E)) : rt P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [rt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem mk_eq (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : FinitePlace.mk P (k : E) = (rt P ^ ordF P k) ^ 2 := by
  obtain ⟨u, hu, hk⟩ := GlobalTheory.EtaConjChar.exists_unit_part P k
  generalize ordF P k = n at hk ⊢
  rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, GlobalTheory.EtaConjLocal.mk_unit P hu,
    GlobalTheory.EtaConjLocal.mk_unif, mul_one, ← rt_sq, sq, sq, mul_zpow]

theorem prod_rt [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) : (∏ i, ‖φ i k‖) * ∏ P ∈ S, rt P ^ ordF P k = 1 := by
  have h := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    finprod_eq_prod_of_mulSupport_subset (s := S)] at h
  · rw [← sq_eq_sq₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun P _ => (zpow_pos (rt_pos P) _).le)) zero_le_one, one_pow, mul_pow, ← Finset.prod_pow,
      ← Finset.prod_pow, ← h]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
    · exact Finset.prod_congr rfl fun P _ => (mk_eq P k).symm
  · intro P hP
    refine hS P fun h0 => hP ?_
    exact (mk_eq P k).trans (by rw [h0]; simp)

theorem prod_val (χ : HChar E) (hu : ∀ P, χ.UnrAt P) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) :
    ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ S, (((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF P k =
      ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) := by
  have h := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at h
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => hS P fun h0 => hP (by simp [h0]))] at h
  have h' := congrArg (Units.val : ℂˣ → ℂ) h
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at h'
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, h', one_mul]
  push_cast
  rfl

theorem unrAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1) : χ.UnrAt P := by
  intro x
  have hc : IsClopen {x : (P.adicCompletion E)ˣ | IsUnitAt P x} := by
    have := (Valued.isClopen_sphere (P.adicCompletion E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := P.adicCompletion E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on (p := fun x => IsUnitAt P x → χ.loc P x = 1) x ?_
    fun k hk => h k ((P.valuedAdicCompletion_eq_valuation' _).symm.trans hk)
  exact isClosed_imp hc.2 (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)

variable {L : Type} [Field L] (ι σ : L →+* ℂ) {χ χ' : HChar E} (hu : ∀ P, χ.UnrAt P) (hu' : ∀ P, χ'.UnrAt P)
  (y : HeightOneSpectrum (𝓞 E) → L) (hy : ∀ P, ι (y P) = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ))
  (hy' : ∀ P, σ (y P) = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ))

include hu hu' hy hy'

theorem inf_eq [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (hi : χ.HasInf φ fun _ => 1)
    (ht : ∀ k : E, ∃ t : L, ι t = ∏ i, φ i k ∧ σ t = ∏ i, φ i k) (k : Eˣ) : χ'.inf k = χ.inf k := by
  obtain ⟨t, ht1, ht2⟩ := ht k
  let S := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
  have hS : ∀ P, ordF P k ≠ 0 → P ∈ S := fun P hP => (Set.Finite.mem_toFinset _).2 hP
  have h1 := prod_val χ hu k S hS
  have h2 := prod_val χ' hu' k S hS
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) (prod_rt φ hφ k S hS)
  have h4 : ((χ.inf k : ℂˣ) : ℂ) * ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = ∏ i, φ i k := by
    rw [hi k, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_one, div_mul_cancel₀ _ (by simp)]
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h2
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h3
  generalize ∏ P ∈ S, y P ^ ordF P k = Y at h1 h2
  generalize ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) = r at h1 h2 h3
  generalize ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = s at h3 h4
  have h5 : Y * t = 1 := ι.injective (by
    rw [map_mul, map_one, ht1, ← h4, ← h3, ← h1]
    ring)
  have h6 : σ Y * (∏ i, φ i k) = 1 := by rw [← ht2, ← map_mul, h5, map_one]
  refine Units.ext ?_
  calc ((χ'.inf k : ℂˣ) : ℂ) = (χ'.inf k : ℂˣ) * (σ Y * (((χ.inf k : ℂˣ) : ℂ) * s)) := by rw [h4, h6, mul_one]
    _ = (χ.inf k : ℂˣ) * (s * (((χ'.inf k : ℂˣ) : ℂ) * σ Y)) := by ring
    _ = _ := by rw [h2, h3, mul_one]

theorem resFin_eq {F : Type} [Field F] [NumberField F] [Algebra F E] (h2 : Module.finrank F E = 2)
    (hF : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal) (hr : χ.ResEta F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ'.resFin v k = χ.resFin v k := by
  have key : ∀ (ψ : HChar E), (∀ P, ψ.UnrAt P) →
      ∏ P ∈ aboveF (L := E) F v, (((ψ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF v k =
        ((ψ.resFin v k : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ ^ ordF v k := by
    intro ψ hψ
    have h1 : ∏ P ∈ aboveF (L := E) F v, rt P = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
      rw [← sq_eq_sq₀ (Finset.prod_nonneg fun P _ => (rt_pos P).le) (by positivity), ← Finset.prod_pow]
      simp only [rt_sq]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, GlobalTheory.ToricDistribution.prod_absNorm hF, h2, Nat.cast_pow, inv_pow]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    · rw [HChar.resFin_apply, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [GlobalTheory.HeckeProduct.locK_unr ψ (hψ P), GlobalTheory.ToricDistribution.ordF_up hF, GlobalTheory.ToricDistribution.mem_aboveF.1 hP,
        Units.val_zpow_eq_zpow_val]
    · rw [Finset.prod_zpow, ← Complex.ofReal_prod, h1]
      simp
  have h1 := key χ hu
  have h3 := key χ' hu'
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h3
  obtain ⟨z, hz⟩ : ∃ z : L, ∀ f : L →+* ℂ, f z = ((χ.resFin v k : ℂˣ) : ℂ) := by
    rw [hr.1, etaFin]
    split_ifs
    · exact ⟨(-1) ^ ordF v k, fun f => by simp⟩
    · exact ⟨1, fun f => by simp⟩
  have h4 : ∏ P ∈ aboveF (L := E) F v, y P ^ ordF v k = z * ((Ideal.absNorm v.asIdeal : ℕ) : L)⁻¹ ^ ordF v k :=
    ι.injective (by rw [h1, map_mul, hz, map_zpow₀, map_inv₀, map_natCast])
  rw [h4, map_mul, hz, map_zpow₀, map_inv₀, map_natCast] at h3
  refine Units.ext (mul_right_cancel₀ (zpow_ne_zero _ (inv_ne_zero ?_)) h3.symm)
  exact Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

end General

theorem isEtaT_of_conj {D : D7} {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {η η' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E}
    (hc : ChrEq η χ) (hc' : ChrEq η' χ') (hχ : IsEtaT D.host χ) (hη : IsEtaConj σ η η') : IsEtaT D.host χ' := by
  have hu' : ∀ P, χ'.UnrAt P := fun P => unrAt_of_locK χ' P (GlobalTheory.EtaConjChar.locK_eq_one hc' hη.2.1 P)
  have hy : ∀ P, ∃ y : D.what₂.LL, D.what₂.embLL y = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ) ∧
      σ y = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ) := by
    intro P
    obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
    obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
    rw [hc.2 P e he _ (locU he.1 (unif P)) rfl] at hy1
    rw [hc'.2 P e he _ (locU he.1 (unif P)) rfl] at hy2
    refine ⟨y, ?_, ?_⟩
    · simpa only [HChar.val, rt, Ideal.absNorm_eq_natCard] using hy1
    · simpa only [HChar.val, rt, Ideal.absNorm_eq_natCard] using hy2
  choose y hy hy' using hy
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  haveI := hcm.cplx
  obtain ⟨hb, hl⟩ := (labels_overK σ).1 hσ
  have hinf : ∀ k, (χ' * χ⁻¹).inf k = 1 := fun k => by
    rw [HChar.inf_mul, HChar.inf_inv, mul_inv_eq_one]
    refine inf_eq D.what₂.embLL σ hχ.unr hu' y hy hy' (embPsi D.host) hcm.bij hχ.inf (fun a => ?_) k
    refine ⟨∏ τ, labLL D τ a, ?_, ?_⟩
    · rw [map_prod, ← D.eTau.prod_comp]
      exact Finset.prod_congr rfl fun τ _ => embLL_embE D _
    · rw [map_prod, ← D.eTau.prod_comp, ← hb.prod_comp]
      exact Finset.prod_congr rfl fun ρ _ => RingHom.congr_fun (hl ρ) a
  obtain ⟨n, hn, ho⟩ := GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one _ _ hinf
  have hp : ∀ x, (χ' * χ⁻¹).1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) ho
  have hξ : IsClsF D.host (χ' * χ⁻¹) := by
    refine ⟨HChar.isUnitary_of_order hn ho, fun P => (hu' P).mul (hχ.unr P).inv, hinf, fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, HChar.resFin_inv, mul_inv_eq_one]
      exact resFin_eq D.what₂.embLL σ hχ.unr hu' y hy hy' hcm.rank
        (GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm) hχ.res v k
    · rw [HChar.resInf_apply]
      exact Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hn.ne' hp w' _
  have := hχ.mul_cls hξ
  rwa [mul_comm χ', mul_inv_cancel_left] at this

end GlobalTheory.EtaConjType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowPartsFullSphericalAlgebraStableFiniteGroup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowPartStable

variable {D : D7}

theorem sphericalOperator_commute_levelFiniteGroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (P : Pl D.host.E) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) {d : List ℤ} {B : Finset (GA D V)}
    (hS : GlobalTheory.Hk3.SphOp V P d B) (g0 : G0 L.Pg L.r) (Φ : GA D V → ℂ) (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    actG0 V β L g0 (heckeLin V B Φ) = heckeLin V B (actG0 V β L g0 Φ) := by
  obtain ⟨e, f, hP⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  unfold actG0
  split_ifs with hex
  · have hl := hex.choose_spec
    generalize hex.choose = κ at hl ⊢
    have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
    have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
      (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
    rw [e1, LinearMap.map_smul]
    funext h
    rw [GlobalTheory.LevOp.heckeLin_translate hP hJ' hS hΦ hk₁ s₁ s₂]
    rfl
  · rw [LinearMap.map_zero]

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) (v : M.Vec) (k : GA D V) (hk : k ∈ J) (g : GA D V) : U v (g * k) = χ k * U v g := by
  induction hU using Submodule.span_induction with
  | mem U hU => exact hU.lev v k hk g
  | zero => simp
  | add U U' _ _ h h' => simp [h, h', mul_add]
  | smul a U _ h => simp [h, mul_left_comm]

theorem map_gE_le : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ SF, IsSF R SF → ∀ c g, (EEc R SF c).map (R.gE g) ≤ EEc R SF c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hC SF hSF c g
  rintro _ ⟨x, hx, rfl⟩
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have h : R.HE.e y ∈ R.EEat R.triv := hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y
    exact goodPart_le _ _ _ _ _ h
  have hx' := ((mem_partFull R.θ (R.MY 0) _ _ SF _ _).1 hx).2
  refine (mem_partFull R.θ (R.MY 0) _ _ SF _ _).2 ⟨hmem _, fun P d B hB v => ?_⟩
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hO : OffS D SF P := by
    obtain ⟨e, f, ϖ, α, h, -⟩ := hB
    exact h
  have hG : Good R A.μ0 P := (hoff SF hSF P).1 hO
  obtain ⟨n, hn⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hN : (((D.host.g 0 * D.host.g 1) ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_pow]
    exact fun h => (hgood _ P hG).1 (P.isPrime.mem_of_pow_mem n h)
  have hPP : ∀ PP, PP ∈ (R.dat0 R.triv).Pg ∨ PP ∈ (R.dat0 R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact hG PP (Or.inl hPP)
    · exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP
  have hS := ((h2 SF d B).1 hB).2
  have hfix : ∀ y, ∀ k ∈ GlobalTheory.Hk3.hyp (Yc D 0) P, ∀ h, R.HE.e y v (h * k) = R.HE.e y v h := by
    intro y k hk h
    rw [mult_lev _ _ _ _ (hmem y) v k (h1 k hk).1 h, (h1 k hk).2, one_mul]
  have hact : R.HE.e (R.gE g x) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e x v) := by
    rw [hC.models.gE g x]; rfl
  have hcomm := sphericalOperator_commute_levelFiniteGroup (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP hS (R.eG g) (R.HE.e x v) (hfix x)
  rw [hx' P d B hB v] at hcomm
  rw [hact]
  exact hcomm.symm.trans ((actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)).map_smul _ _)

end GlobalTheory.RowPartStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProduStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ SB (κ → Af F),
    g ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)} := by
  first | exact @GlobalTheory.SBSpan.mem_span_restrictedProd | exact GlobalTheory.SBSpan.mem_span_restrictedProd | (intros; apply GlobalTheory.SBSpan.mem_span_restrictedProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HtSelfInter

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem isClosed_of_ne_genericPoint [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem charZero_residueField_genericPoint [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Z.Opens) (Opens.mem_top _))
  let f : Z.functionField →+* Z.residueField (genericPoint Z) := (Z.residue _).hom
  exact charZero_of_injective_ringHom f.injective

theorem eq_genericPoint [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) {z : Z}
    (hz : CharZero (Z.residueField z)) : z = genericPoint Z := by
  by_contra h
  have := hZ.finite_residueField (isClosed_of_ne_genericPoint hZ.dim_eq h)
  exact not_finite (Z.residueField z)

theorem finite_ringHom [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Finite (Z.residueField (genericPoint Z) →+* ℂ) := by
  have hc := charZero_residueField_genericPoint hZ.charZero
  obtain ⟨N, j, _, hj⟩ := hZ.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hZ.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  have h₁ : t.QuasiFiniteAt (genericPoint Z) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have h0 : CharZero ((Sp ℤ).residueField (t (genericPoint Z))) :=
      (t.residueFieldMap (genericPoint Z)).hom.charZero
    have hs (w : t.fiber (t (genericPoint Z))) : t.fiberι _ w = genericPoint Z := by
      have e : t (t.fiberι _ w) = t (genericPoint Z) :=
        (t.range_fiberι (t (genericPoint Z))).le ⟨w, rfl⟩
      rw [← e] at h0
      exact eq_genericPoint hZ (charZero_of_injective_ringHom (t.residueFieldMap _).hom.injective)
    have : Subsingleton (t.fiber (t (genericPoint Z))) := ⟨fun a b =>
      (t.fiberι _).isEmbedding.injective ((hs a).trans (hs b).symm)⟩
    exact isOpen_discrete _
  have h₂ := Scheme.Hom.quasiFiniteAt_iff.1 h₁
  have h₃ : LocallyQuasiFinite (Z.fromSpecResidueField (genericPoint Z) ≫ t) := by
    rw [Scheme.fromSpecResidueField, Category.assoc]
    infer_instance
  rw [← Spec.map_preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t),
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite),
    RingHom.ext_int (Spec.preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t)).hom
      ((algebraMap ℚ (Z.residueField (genericPoint Z))).comp (Int.castRingHom ℚ))] at h₃
  have h₄ := RingHom.quasiFinite_algebraMap.1 (RingHom.QuasiFinite.of_comp h₃)
  have : Module.Finite ℚ (Z.residueField (genericPoint Z)) := .of_quasiFinite
  exact .of_equiv _ (RingHom.equivRatAlgHom _ ℂ).symm

theorem nonempty_equiv [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Nonempty ((Σ σ : k →+* ℂ, CxPts q σ) ≃ (Z.residueField (genericPoint Z) →+* ℂ)) := by
  have h₁ : Function.Bijective fun y : (Σ σ : k →+* ℂ, CxPts q σ) => y.2.1 := by
    refine ⟨?_, fun y => ⟨⟨(Spec.preimage (y ≫ q)).hom, y, (Spec.map_preimage _).symm⟩, rfl⟩⟩
    rintro ⟨σ, y, hy⟩ ⟨σ', y', hy'⟩ (rfl : y = y')
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans hy'))
    rfl
  have h₂ : Function.Bijective fun φ : Z.residueField (genericPoint Z) →+* ℂ =>
      (Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecResidueField (genericPoint Z) : Sp ℂ ⟶ Z) := by
    refine ⟨fun φ ψ h => congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h)),
      fun y => ?_⟩
    obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Z).symm.surjective y
    obtain rfl := eq_genericPoint hZ (z := z) φ.hom.charZero
    exact ⟨φ.hom, rfl⟩
  exact ⟨(Equiv.ofBijective _ h₁).trans (Equiv.ofBijective _ h₂).symm⟩

theorem finsum_add_const [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0)
    (f : ∀ σ : k →+* ℂ, CxPts q σ → ℝ) (c : ℝ) :
    ∑ᶠ σ, ∑ᶠ y, (f σ y + c) =
      (∑ᶠ σ, ∑ᶠ y, f σ y) + c * Nat.card (Z.residueField (genericPoint Z) →+* ℂ) := by
  have := finite_ringHom hZ
  have := hZ.finite_emb
  obtain ⟨e⟩ := nonempty_equiv hZ
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [finsum_eq_sum_of_fintype, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sum, Finset.mul_sum, mul_comm]

theorem card_ringHom_eq (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem curveDeg_shift (hX : IsArithVar p D) (L : HermLB p) (t : ℝ) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    {r : (L.restr i).B.ι → Z.functionFieldˣ} (hr : IsRatSec (L.restr i).B r) :
    ((L.shift (fun _ => t) fun _ => rfl).restr i).curveDeg (r := r) hr =
      (L.restr i).curveDeg hr + t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  have e (σ : k →+* ℂ) (y : CxPts (i ≫ p) σ) :
      logNorm (((L.shift (fun _ => t) fun _ => rfl).restr i).φ σ) r y =
        logNorm ((L.restr i).φ σ) r y + -t := by
    have e₁ := ((L.shift (fun _ => t) fun _ => rfl).φ σ).pull_φ i rfl
      (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₂ := (L.φ σ).pull_φ i rfl (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₃ := e₁.trans (congrArg (· + 2 * t) e₂.symm)
    refine (congrArg (_ - · / 2) e₃).trans ?_
    unfold logNorm
    exact (fun a b : ℝ => (by ring : a - (b + 2 * t) / 2 = a - b / 2 + -t)) _ _
  unfold HermLB.curveDeg
  simp only [e]
  rw [finsum_add_const hZ, card_ringHom_eq]
  exact (fun a b c : ℝ => (by ring : a - (b + -t * c) = a - b + t * c)) _ _ _

theorem isAlgPt_genericPoint (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (hc : CharZero Γ(Z, ⊤))
    (hd : topologicalKrullDim Z = 1) : IsAlgPt (i (genericPoint Z)) := by
  have := charZero_residueField_genericPoint hc
  refine ⟨(i.residueFieldMap _).hom.charZero, ?_⟩
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [h₁.def, ← hd]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem isNef_shift (hX : IsArithVar p D) {L : HermLB p} {e : ℝ} (hs : L.SemiPos D) (hf : NefFib L)
    (hh : ∀ x, IsAlgPt x → ∃ b, IsPtHt L x b ∧ e ≤ b) :
    (L.shift (fun _ => -e) fun _ => rfl).IsNef D := by
  refine ⟨hs.shift _ _, fun Z i _ _ κ _ _ _ hd => hf Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨b, ⟨h, H, hb⟩, hle⟩ := hh _ (isAlgPt_genericPoint i hc hd)
  refine ⟨r, hr, ?_⟩
  rw [curveDeg_shift hX L (-e) i hc hd hr, ← H.point Z i hc hd r hr, hb, ← add_mul]
  exact mul_nonneg (by linarith) (Nat.cast_nonneg _)

end GlobalTheory.HtSelfInter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubsetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset : ∀ (T : Type) [TopologicalSpace T] (A B : Set T), IsClosed A → IsIrreducible A → IsIrreducible B → A ⊂ B → topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  first | exact @GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | exact GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | (intros; apply GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset <;> assumption)
end

