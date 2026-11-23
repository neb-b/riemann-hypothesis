module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem potModel_semiAbelian_torusExtension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA
  obtain ⟨K', _, _, _, V', _, _, _, _, _, _, hfin, hinj, hcomm, G, _, hc, hsm, hsep, hqc, he, hT⟩ :=
    GlobalTheory.SS.semistableReduction_zero V K A hA
  obtain ⟨hloc, hcpl⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V V' hfin hinj
  haveI := hcpl
  have hA' : IsAbelianScheme (baseChange K K' A) := Out.TLinPf.isAb_pullback _ A hA
  have hG : IsSemiAbelian G :=
    GlobalTheory.SS.isSemiAbelian_of_abelian_generic_of_torusExt V' K' (baseChange K K' A) hA' G hc hsm hsep hqc he hT
  obtain ⟨V'', _, _, _, hcpl', _, hfin', hinj', hloc', hG', hT'⟩ :=
    GlobalTheory.exists_finite_dvr_torusExtension_specialFibre V' G hG
  obtain ⟨alg, hfd, hcomm', he'⟩ := GlobalTheory.SS.model_finite_ext V K A K' V' hcomm G he V'' hfin' hinj'
  let : Algebra V V'' := ((algebraMap V' V'').comp (algebraMap V V')).toAlgebra
  have : IsScalarTower V V' V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinV : Module.Finite V V'' := Module.Finite.trans V' V''
  have hlocV : IsLocalHom (algebraMap V V'') := by
    haveI := hloc; haveI := hloc'
    exact (inferInstance : IsLocalHom ((algebraMap V' V'').comp (algebraMap V V')))
  exact ⟨V'', FractionRing V'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, alg, inferInstance, hcomm', hfinV, hlocV, hcpl', baseChange V' V'' G, inferInstance, he', hG', hT'⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPointIntegralRelativeLocalBasis
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

open Matrix

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_natCast_eq_one (l : ℕ) [Fact l.Prime] {s : ℕ} (hs : ¬ l ∣ s) : ‖(s : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs)

theorem norm_le_one_of_cols {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ} (U : Matrix (Fin n) (Fin n) C) (p : C)
    (hp : ‖p‖ < 1) (h : ∀ b, ∃ T : Fin n → C, (∀ c, ‖T c‖ ≤ 1) ∧ ∀ a, ‖U a b - p * ∑ c, U a c * T c‖ ≤ 1) (a b : Fin n) :
    ‖U a b‖ ≤ 1 := by
  haveI : Nonempty (Fin n × Fin n) := ⟨(a, b)⟩
  obtain ⟨⟨a₀, b₀⟩, hmax⟩ := Finite.exists_max fun q : Fin n × Fin n => ‖U q.1 q.2‖
  refine (hmax (a, b)).trans ?_
  obtain ⟨T, hT, hU⟩ := h b₀
  by_contra hm
  have hm : 1 < ‖U a₀ b₀‖ := not_le.1 hm
  have h1 : ‖∑ c, U a₀ c * T c‖ ≤ ‖U a₀ b₀‖ :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hT c)).trans (hmax (a₀, c))
  have h2 : ‖p * ∑ c, U a₀ c * T c‖ < ‖U a₀ b₀‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_lt (mul_lt_of_lt_one_left (one_pos.trans hm) hp)
  have h3 := IsUltrametricDist.norm_add_le_max (U a₀ b₀ - p * ∑ c, U a₀ c * T c) (p * ∑ c, U a₀ c * T c)
  rw [sub_add_cancel] at h3
  exact absurd h3 (not_le.2 (max_lt ((hU a₀).trans_lt hm) h2))

theorem exists_col {A E : Type} [CommRing A] [CommRing E] (j : E →+* A) (S : Subring A) {n : ℕ}
    (happ : ∀ M : ℕ, 0 < M → ∀ z : A, ∃ (e : E) (s : A), s ∈ S ∧ z = j e + (M : A) * s)
    (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Yi * Y = 1) {N : ℕ} (hN : 0 < N) (hNm : ∀ a b, (N : A) * Yi a b ∈ S)
    {p : ℕ} (hp : 0 < p) (b : Fin n) :
    ∃ (x : Fin n → E) (t : Fin n → A), (∀ c, t c ∈ S) ∧ Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t := by
  choose x s hs hx using fun i => happ (p * N) (Nat.mul_pos hp hN) (Y i b)
  refine ⟨x, ((N : A) • Yi) *ᵥ s, fun c => ?_, ?_⟩
  · rw [Matrix.mulVec, dotProduct]
    exact S.sum_mem fun k _ => S.mul_mem (hNm c k) (hs k)
  · have e : (fun i => j (x i)) = Y *ᵥ Pi.single b 1 - (p : A) • (N : A) • s := by
      funext i
      rw [Matrix.mulVec_single_one]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
      rw [hx i]
      push_cast
      ring
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.smul_mulVec]

theorem read_col {A E C : Type} [CommRing A] [CommRing E] [CommRing C] (j : E →+* A) (ev : A →+* C) (inc : E →+* C)
    (hj : ∀ e, ev (j e) = inc e) {n : ℕ} (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Y * Yi = 1) (Bi : Matrix (Fin n) (Fin n) E)
    {p : ℕ} {b : Fin n} {x : Fin n → E} {t : Fin n → A}
    (h : Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t) (a : Fin n) :
    (Bi.map inc * Y.map ev) a b - (p : C) * ∑ c, (Bi.map inc * Y.map ev) a c * ev (t c) = inc ((Bi *ᵥ x) a) := by
  have h1 : Y *ᵥ (Pi.single b 1 - (p : A) • t) = fun i => j (x i) := by
    rw [← h, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec]
  have h2 : (ev ∘ (Pi.single b 1 - (p : A) • t : Fin n → A)) = Pi.single b 1 - (p : C) • fun c => ev (t c) := by
    funext c
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_natCast,
      Pi.single_apply, apply_ite ev, map_one, map_zero]
  have h3 : Y.map ev *ᵥ (Pi.single b 1 - (p : C) • fun c => ev (t c)) = inc ∘ x := by
    funext i
    rw [← h2, ← RingHom.map_mulVec, h1, hj]
    rfl
  rw [RingHom.map_mulVec, ← h3, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

theorem stdLat_of {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (h : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Seed.FrmC.StdLat V := by
  intro x
  show (∑ i, x i • V.frame i ∈ V.L0) ↔ _
  rw [h, V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), V.frame.repr_sum_self]
  exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem approx (M : ℕ) (hM : 0 < M) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ (e : E) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F), s ∈ Formalism.L2.Herm.intAf F E ∧
      z = e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) + (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨e₁, s₁, h₁, rfl⟩ := hx
    obtain ⟨e₂, s₂, h₂, rfl⟩ := hy
    refine ⟨e₁ + e₂, s₁ + s₂, add_mem h₁ h₂, ?_⟩
    rw [TensorProduct.add_tmul]
    ring
  | tmul b α =>
    obtain ⟨d, hd, ho⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E b
    obtain ⟨x, β, hβ, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F (M * d) (Nat.mul_pos hM hd) α
    refine ⟨x • b, ((d : E) * b) ⊗ₜ[F] β, GlobalTheory.PlaceDatum.tmul_mem_int ho (α := β) hβ, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      ← nsmul_eq_mul, ← nsmul_eq_mul, mul_smul]
    rfl

theorem norm_ev_le_one {l : ℕ} [Fact l.Prime] {inc : E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (hev : EvOk inc ev) {r : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hr : r ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm r)‖ ≤ 1 := by
  induction hr using Subring.closure_induction with
  | mem r hr =>
    rcases hr with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
    · refine (congrArg norm (hev.1 (algebraMap (𝓞 E) E o))).le.trans ?_
      exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
    · exact hev.2.1 β hβ
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

end General


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem norm_le_one_of_isLocBasis : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val a b‖ ≤ 1 := by
  intro D V l hl inc ev hev hL0 y B hB
  have hV := stdLat_of V hL0
  have hY := GlobalTheory.HLatStd.invM_mul y
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (GlobalTheory.HLatStd.invM y)
  let j : D.host.E →+* Lev.EAf D := Algebra.TensorProduct.includeLeftRingHom
  let ev' : Lev.EAf D →+* PadicAlgCl l := ev.comp (GlobalTheory.HeckeTrans.unswap D)
  have hU : ((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val =
      (B⁻¹).val.map inc * ((Units.val ((y : Bridge.Gf V) : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).map (Lev.swapAE D)).map ev' := by
    rw [← map_inv, Units.val_mul]
    congr 1
    ext a b
    exact (congrArg ev (GlobalTheory.HeckeTrans.unswap_swap _)).symm
  rw [hU]
  refine norm_le_one_of_cols _ (l : PadicAlgCl l) (norm_natCast_lt_one l) fun b => ?_
  obtain ⟨x, t, ht, hx⟩ := exists_col j (GlobalTheory.StdFrameExist.SI D) (fun M hM z => approx M hM z) _ _
    (mul_eq_one_comm.1 hY) hN hNm hl.out.pos b
  refine ⟨fun c => ev' (t c), fun c => norm_ev_le_one hev (ht c), fun a => ?_⟩
  rw [read_col j ev' inc (fun e => hev.1 e) _ _ hY _ hx a]
  have hmem : x ∈ Bridge.hLat V y := by
    refine GlobalTheory.HLatStd.mem_hLat_of hV y fun i => ?_
    have hi : (GlobalTheory.HLatStd.invM y *ᵥ GlobalTheory.HLatStd.iv x) i = _ := congrFun hx i
    rw [hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    refine sub_mem ?_ (mul_mem (natCast_mem _ _) (ht i))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨s, hs, hint⟩ := (hB x).1 ⟨1, hl.out.not_dvd_one, by rw [Nat.cast_one, one_smul]; exact hmem⟩
  obtain ⟨o, ho⟩ := hint a
  have h1 : ‖inc (algebraMap (𝓞 D.host.E) D.host.E o)‖ ≤ 1 :=
    GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
  rwa [ho, map_mul, map_natCast, norm_mul, norm_natCast_eq_one l hs, one_mul] at h1

end GlobalTheory.LocBasisInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dot_smul_rat {κ : Type} [Fintype κ] (s t : AF F) (u v : (κ → F) × (κ → F)) :
    (s • ((fun i => algebraMap F (AF F) (u.1 i)), (fun i => algebraMap F (AF F) (u.2 i)))).1 ⬝ᵥ
      (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))).2 =
      s * t * algebraMap F (AF F) (u.1 ⬝ᵥ v.2) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show (fun i => algebraMap F (AF F) (u.1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v.2 i)) =
    algebraMap F (AF F) (u.1 ⬝ᵥ v.2) from (RingHom.map_dotProduct (algebraMap F (AF F)) u.1 v.2).symm]
  ring

theorem inv_sum (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ)
    {ι : Type} (s : Finset ι) (t : ι → AF F) (w : ι → (κ → F) × (κ → F)) (hw : ∀ j, w j ∈ L) :
    ∀ φ ∈ schA F κ, l (schr ψ (∑ j ∈ s, t j • ((fun i => algebraMap F (AF F) ((w j).1 i)),
      (fun i => algebraMap F (AF F) ((w j).2 i)))) φ) = l φ := by
  classical
  induction s using Finset.induction_on with
  | empty => intro φ _; simp only [Finset.sum_empty]; congr 1; funext x; simp [schr]
  | insert j s hj ih =>
    intro φ hφ
    set a := t j • ((fun i => algebraMap F (AF F) ((w j).1 i)), (fun i => algebraMap F (AF F) ((w j).2 i)))
    set b := ∑ k ∈ s, t k • ((fun i => algebraMap F (AF F) ((w k).1 i)), (fun i => algebraMap F (AF F) ((w k).2 i)))
    have hab : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0 := by
      simp only [a, b, Prod.fst_sum, Prod.snd_sum, dotProduct_sum, sum_dotProduct, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [dot_smul_rat, dot_smul_rat, hL _ (hw j) _ (hw k)]
      ring
    have e := GlobalTheory.ThetaQuasiRat.schr_schr ψ a b φ
    rw [hab, mul_zero, AddChar.map_zero_eq_one, one_smul] at e
    rw [Finset.sum_insert hj, ← e, hl _ _ (hw j) _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ b φ hφ), ih φ hφ]

end GlobalTheory.AdelicSvN

namespace GlobalTheory.AdelicSvN
variable {F : Type} [Field F] [NumberField F]

theorem realised_of_mem_closure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (gens F κ)) : Realised ψ g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · exact _root_.GlobalTheory.AdelicSvNLevi.realised_levi F ψ κ A hA
    · exact _root_.GlobalTheory.AdelicSvNQuad.realised_unip F ψ hψ κ C hC
    · exact _root_.GlobalTheory.AdelicSvN.Weyl.realised_weyl F ψ hψ κ
  | one => exact realised_one ψ
  | mul g h _ _ hg hh => exact hg.mul hh

theorem act_zero_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (y : κ → AF F) :
    act g (0, y) = ∑ j, y j • ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inl) i)),
      (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inr) i))) := by
  have key : ∀ k, (g.map (algebraMap F (AF F)) *ᵥ Sum.elim 0 y) k =
      ∑ j, y j * algebraMap F (AF F) ((g *ᵥ Sum.elim 0 (Pi.single j 1)) k) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [Pi.single_apply, hm]) (by simp)]
    simp [mul_comm]
  ext i
  · simp only [act, Function.comp_apply, key, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  · simp only [act, Function.comp_apply, key, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro F _ _ ψ hψ κ _ L hL hdim l₁ hl₁ l₂ hl₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg
  have key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hl hi
    obtain ⟨l', hl', e⟩ := hSa l hl
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.CharInvForm.main F ψ hψ κ l' hl' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hl₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hl₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp
end GlobalTheory.AdelicSvN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  first | exact @GlobalTheory.RestCofactor.rest_of_rest | exact GlobalTheory.RestCofactor.rest_of_rest | (intros; apply GlobalTheory.RestCofactor.rest_of_rest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeCompletion
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatHatCong

theorem cong_zero {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ) :
    t • (K *ᵥ 0 - 0) = M • (0 : Fin n → R) := by
  rw [Matrix.mulVec_zero, sub_zero, smul_zero, smul_zero]

theorem cong_add {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u w y y' : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) (e' : t • (K *ᵥ w - w) = M • y') :
    t • (K *ᵥ (u + w) - (u + w)) = M • (y + y') := by
  rw [Matrix.mulVec_add, add_sub_add_comm, smul_add, e, e', smul_add]

theorem cong_neg {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (-u) - (-u)) = M • (-y) := by
  rw [Matrix.mulVec_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, smul_neg, e, smul_neg]

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t c : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (c • u) - c • u) = M • (c • y) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, e, smul_comm]

theorem cong_on_hat : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  intro D V β Λ hβ K t M h z hz
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl] at h hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    obtain ⟨y, hy, e⟩ := h x hx
    have hm : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hy' := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ hm y hy
    have hc : (Algebra.TensorProduct.comm D.host.F _ D.host.E).symm ((1 : D.host.E) ⊗ₜ[D.host.F] a) =
        a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc] at hy'
    have hv : (fun i => a ⊗ₜ[D.host.F] x i) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • finVec V x := by
      funext i
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    refine ⟨_, hy', ?_⟩
    rw [hv]
    exact cong_smul e
  | zero =>
    exact ⟨0, AddSubgroup.zero_mem _, cong_zero K t M⟩
  | add u w _ _ hu hw =>
    obtain ⟨y, hy, e⟩ := hu
    obtain ⟨y', hy', e'⟩ := hw
    exact ⟨y + y', add_mem hy hy', cong_add e e'⟩
  | neg u _ hu =>
    obtain ⟨y, hy, e⟩ := hu
    exact ⟨-y, neg_mem hy, cong_neg e⟩

end GlobalTheory.LatHatCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpannedStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x h Z σ hσ a n hD hpos hn
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · have := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]
      exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z
    have e : goodOf c σ = σ := ite_eq_left hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dite_eq_left]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]
      exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact GlobalTheory.AllWt.rdU_mul (U σ) _ _
end

