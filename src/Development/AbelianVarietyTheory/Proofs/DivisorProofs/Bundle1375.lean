module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelic
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.DerCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem commute_isRealLine_finPts {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) {k : GAd σ J}
    (hk : k ∈ finPts σ J) : Commute (γ t) k := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  obtain ⟨y, e, -⟩ := hy t
  rw [e]; exact commute_embArch σ J y (mem_finPts_iff_forall.1 hk w)

theorem foldr_lineDer_mul_level {φ : GAd σ J → ℂ} {U : Subgroup (GAd σ J)}
    (hφ : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, l.foldr lineDer φ (g * k) = l.foldr lineDer φ g := by
  intro l
  induction l with
  | nil => intro _ k hk hk' g; exact hφ k hk hk' g
  | cons γ l ih =>
    intro hl k hk hk' g
    have hγ := hl γ List.mem_cons_self
    have ih' := ih (fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) k hk hk'
    simp only [List.foldr_cons, lineDer]
    congr 1
    funext t
    rw [mul_assoc, ← (commute_isRealLine_finPts hγ t hk').eq, ← mul_assoc, ih']

theorem eventually_decomp {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (g₀ : GAd σ J) :
    Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝 1) ∧
    ∀ᶠ g in 𝓝 g₀, ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ U ∧ ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ finPts σ J := by
  have hc : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    exact Continuous.tendsto' (by fun_prop) g₀ 1 (by simp)
  have h1 : Tendsto (fun h => ofInf σ J (projInf σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofInf σ J).comp (continuous_projInf σ J)) 1 1 (by simp)
  have h2 : Tendsto (fun h => ofFin σ J (projFin σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofFin σ J).comp (continuous_projFin σ J)) 1 1 (by simp)
  refine ⟨h1.comp hc, ?_⟩
  filter_upwards [(h2.comp hc).eventually (hU.mem_nhds U.one_mem)] with g hg
  exact ⟨hg, mem_finPts.2 (projInf_ofFin σ J _)⟩

theorem chart (h : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
      ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod :=
  _root_.GlobalTheory.infPts_secondKind_chart F E σ h n J hJ

theorem continuous_foldr_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  intro F E _ _ _ _ _ σ h n J hJ φ ⟨U, hU, hlev⟩ _ hsm l hl
  obtain ⟨m, η, s, hη, hs, hP⟩ := chart h hJ
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hH : Continuous fun t : Fin m → ℝ => l.foldr lineDer φ (g₀ * (List.ofFn fun i => η i (t i)).prod) :=
    (GlobalTheory.ThK.RealLineGrowthDerivative.contDiff_foldr_lineDer hsm l hl m η hη g₀).continuous
  have hη0 : ∀ i, η i 0 = 1 := fun i => by
    have e := isRealLine_add F E σ h n J (η i) (hη i) 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have h0 : (List.ofFn fun i => η i ((0 : Fin m → ℝ) i)).prod = 1 := by
    simp [hη0]
  obtain ⟨hx, hu⟩ := eventually_decomp hU g₀
  have hx' : Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝[(infPts σ J : Set (GAd σ J))] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun g => mem_infPts.2 (projFin_ofInf σ J _)⟩
  have key : ∀ᶠ g in 𝓝 g₀, l.foldr lineDer φ (g₀ * (List.ofFn fun i =>
      η i (s (ofInf σ J (projInf σ J (g₀⁻¹ * g))) i)).prod) = l.foldr lineDer φ g := by
    filter_upwards [hu, hx'.eventually hP] with g hu' hP'
    rw [← hP']
    have e : g = g₀ * ofInf σ J (projInf σ J (g₀⁻¹ * g)) * ofFin σ J (projFin σ J (g₀⁻¹ * g)) := by
      rw [mul_assoc, ofInf_projInf_mul_ofFin_projFin, mul_inv_cancel_left]
    conv_rhs => rw [e]
    exact (foldr_lineDer_mul_level hlev l hl _ hu'.1 hu'.2 _).symm
  have lim := (hH.tendsto 0).comp (hs.comp hx')
  rw [h0, mul_one] at lim
  exact lim.congr' key

end GlobalTheory.DerCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviProjTwo
section
noncomputable section

namespace GlobalTheory.LocRankBig

open GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem totallyDisconnected : TotallyDisconnectedSpace k := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem nonarchimedeanGroup_GL (n : ℕ) : NonarchimedeanGroup (GL (Fin n) k) := by
  haveI := totallyDisconnected (k := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (GL (Fin n) k) :=
    ⟨isTotallyDisconnected_of_image (f := fun g : GL (Fin n) k => g.val) Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  haveI : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  haveI : NonarchimedeanGroup (KO k (Fin n)) := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  exact NonarchimedeanGroup.nonarchimedean_of_emb (KO k (Fin n)).subtype
    GlobalTheory.SplitFlip.isOpen_KO.isOpenEmbedding_subtypeVal

end Local

end GlobalTheory.LocRankBig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValues
section
open IsDedekindDomain NumberField
open scoped Classical

theorem GlobalTheory.continuousMultilinear_norm_le_basis_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  intro E _ _ ι _ b j
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖ := by
    intro x c
    have h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c := rfl
    rw [h1]
    exact (norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)
  refine ⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun r => ∑ c, b.repr (v r) c • b c := funext fun r => (b.sum_repr (v r)).symm
  have key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r)) := by
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [M.map_sum]
    refine Finset.sum_congr rfl fun cs _ => ?_
    exact M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))
  rw [key]
  calc ‖∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖
      ≤ ∑ cs : Fin j → ι, ‖(∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖ := norm_sum_le _ _
    _ ≤ ∑ cs : Fin j → ι, (C ^ j * ∏ r, ‖v r‖) * ‖M (fun r => b (cs r))‖ := by
      refine Finset.sum_le_sum fun cs _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)
    _ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cs _ => ?_
      ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockLevel

open Matrix
open scoped TensorProduct
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAFE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAFE : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_ad (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add (f := _), LinearMap.map_add (f := _), ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem infTens_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    GlobalTheory.LFun.infTens F E (sigR (AF F) σ z) = sigR (Ainf F) σ (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem continuous_finGL (d : ℕ) : Continuous (GlobalTheory.CuspRep.finGL E d) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (GlobalTheory.CuspRep.sFin E : GlobalTheory.CuspRep.Af E → GlobalTheory.CuspRep.Ad E) :=
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GlobalTheory.CuspRep.Af E => ((0, x) : InfiniteAdeleRing E × GlobalTheory.CuspRep.Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E) => 1 - GlobalTheory.CuspRep.matN d (GlobalTheory.CuspRep.sFin E) 1 + x.map (GlobalTheory.CuspRep.sFin E))

variable [_root_.NumberField.IsTotallyComplex E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
  {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ} {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem continuous_of_isBlockEmb (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) : Continuous ι := by
  obtain ⟨Φ, j, -, hΦs, -, -, hf⟩ := hι
  have hval : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
    simp only [hf, cT]
    have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g.1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := Units.continuous_val
    have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((g⁻¹).1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) :=
      Units.continuous_val.comp continuous_inv
    have h3 := h1.matrix_map hΦs
    have h4 := ((h2.matrix_map hΦs).matrix_map (continuous_sigR_ad σ)).matrix_transpose
    exact (continuous_const.add ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h4.sub continuous_const)).matrix_mul continuous_const)
  have hU : Continuous fun g : GlobalTheory.CuspRep.GA E d => matHom (AF F) σ J (ι g) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1) =
        (fun g => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) ∘ fun g => g⁻¹ := by
      funext g; simp [map_inv]
    rw [this]
    exact hval.comp continuous_inv
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 hU

theorem infTens_symm_finGL (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E)
    (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
    (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) :
    GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = (1 : Matrix (Fin d) (Fin d) (Ainf F ⊗[F] E)) a b := by
  have e1 : GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = j.symm (((GlobalTheory.CuspRep.finGL E d k).1 a b).1) := by
    have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
      have e := congrArg Prod.fst (hΦ (Φ.symm x))
      rw [RingEquiv.apply_symm_apply] at e
      rw [e, RingEquiv.symm_apply_apply]
    exact key _
  rw [e1]
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b - GlobalTheory.CuspRep.sFin E ((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E)) a b) + GlobalTheory.CuspRep.sFin E (k.1 a b)).1) = _
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b).1 - 0 + 0) = _
  rw [sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem finGL_mem_finPts (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) :
    ι (GlobalTheory.CuspRep.finGL E d k) ∈ finPts σ J := by
  obtain ⟨Φ, j, -, -, -, hΦ, hf⟩ := hι
  have hA : ∀ k : GL (Fin d) (GlobalTheory.CuspRep.Af E),
      (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm) = 1 := by
    intro k
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact infTens_symm_finGL Φ j hΦ k a b
  have hB : (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E))
      (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm)) = 1 := by
    rw [← map_inv]
    ext a b
    have e := congrArg (fun M => M b a) (hA k⁻¹)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cT, Matrix.transpose_apply, infTens_sigR, e]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
  simp only [finPts, MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply Units.ext
  change (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) (matHom (AF F) σ J (ι (GlobalTheory.CuspRep.finGL E d k))).1 = 1
  have hA' : ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hA, map_one, sub_self]
  have hB' : (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm) - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hB, map_one, sub_self]
  rw [hf]
  simp only [map_add (f := _), map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hA', hB', Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem isOpen_rightInv_finGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        IsOpen {k : GL (Fin d) (GlobalTheory.CuspRep.Af E) | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)} := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι hι _ _ _ _ ψ hψ g₀ _
  obtain ⟨U, hUo, hU⟩ := hψ.1.level
  let H : Subgroup (GL (Fin d) (GlobalTheory.CuspRep.Af E)) :=
    { carrier := {k | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)}
      one_mem' := fun g => by simp
      mul_mem' := fun {a b} ha hb g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d (a * b)) * g₀) = _
        rw [(GlobalTheory.CuspRep.finGL E d).map_mul a b, ← mul_assoc, hb (g * GlobalTheory.CuspRep.finGL E d a), ha g]
      inv_mem' := fun {a} ha g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d a⁻¹) * g₀) = _
        have e : g * GlobalTheory.CuspRep.finGL E d a⁻¹ * GlobalTheory.CuspRep.finGL E d a = g := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
        rw [← ha (g * GlobalTheory.CuspRep.finGL E d a⁻¹), e] }
  let m : GL (Fin d) (GlobalTheory.CuspRep.Af E) → GAd σ J := fun k => g₀⁻¹ * ι (GlobalTheory.CuspRep.finGL E d k) * g₀
  have hm : Continuous m :=
    (continuous_const.mul ((continuous_of_isBlockEmb hι).comp (continuous_finGL d))).mul continuous_const
  have hN : (finPts σ J).Normal := MonoidHom.normal_ker _
  have hsub : m ⁻¹' (U : Set (GAd σ J)) ⊆ (H : Set (GL (Fin d) (GlobalTheory.CuspRep.Af E))) := by
    intro k hk g
    have hfin : m k ∈ finPts σ J := by
      have := hN.conj_mem _ (finGL_mem_finPts hι k) g₀⁻¹
      simpa [m] using this
    have e := hU (m k) hk hfin (ι g * g₀)
    rw [← e]
    simp only [m, map_mul, mul_assoc, mul_inv_cancel_left]
  have h1 : m ⁻¹' (U : Set (GAd σ J)) ∈ nhds (1 : GL (Fin d) (GlobalTheory.CuspRep.Af E)) := by
    refine hm.continuousAt.preimage_mem_nhds ?_
    have : m 1 = 1 := by simp [m]
    rw [this]
    exact hUo.mem_nhds U.one_mem
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset h1 hsub)

end GlobalTheory.BlockLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealWeil

theorem exists_weylAlg_conj {l : Type} [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : Sch l →ₗ[ℂ] Sch l) (hI : ∀ w f, A' (dRho w f) = dRho (L' w) (A' f))
    {B : Sch l →L[ℂ] Sch l} (hB : B ∈ weylAlg l) :
    ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f) := by
  refine weylAlg_induction (P := fun B => ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f))
    ⟨1, fun f => by simp⟩ ?_ ⟨0, fun f => by simp⟩ ?_ ?_ hB
  · rintro A w ⟨B', h⟩
    refine ⟨B' * dRho (L'.symm w), fun f => ?_⟩
    have e := hI (L'.symm w) f
    rw [LinearEquiv.apply_symm_apply] at e
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← e, h]
  · rintro A B ⟨A₁, h₁⟩ ⟨B₁, h₂⟩
    exact ⟨A₁ + B₁, fun f => by simp [h₁, h₂]⟩
  · rintro c A ⟨A₁, h⟩
    exact ⟨c • A₁, fun f => by simp [h]⟩

theorem norm_toLp_le_of_lintegral_le {l : Type} [Fintype l] (A' : Sch l →ₗ[ℂ] Sch l) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) (f : Sch l) :
    ‖(A' f).toLp 2 volume‖ ≤ C.toReal ^ (1 / 2 : ℝ) * ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
    (f.eLpNorm_lt_top 2 volume).ne) ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (A' f).continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (h f) (by norm_num)

end GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  intro l _ L' A' C hC h2 hI
  refine WithSeminorms.continuous_of_continuous_comp (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ) A'
    fun i => ?_
  obtain ⟨B, hB, hle⟩ := GlobalTheory.RealWeil.exists_seminorm_le (l := l) i.1 i.2
  choose B' hB' using fun r => GlobalTheory.RealWeil.exists_weylAlg_conj L' A' hI (hB r)
  let c : NNReal := Real.toNNReal (C.toReal ^ (1 / 2 : ℝ))
  let q : Seminorm ℂ (GlobalTheory.RealWeil.Sch l) := ∑ r, c • (normSeminorm ℂ (GlobalTheory.RealWeil.L2 l)).comp
    ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).toLinearMap
  refine Seminorm.continuous_of_le (q := q) (Seminorm.continuous_finsetSum fun r _ => ?_) fun f => ?_
  · change Continuous fun f => (c : ℝ) * ‖(GlobalTheory.RealWeil.schwartzToL2 l) (B' r f)‖
    exact continuous_const.mul (continuous_norm.comp ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).continuous)
  · have e : q f = ∑ r, (c : ℝ) * ‖(B' r f).toLp 2 volume‖ := by
      simp [q, GlobalTheory.RealWeil.schwartzToL2_apply, NNReal.smul_def, smul_eq_mul]
    rw [e]
    change SchwartzMap.seminorm ℂ i.1 i.2 (A' f) ≤ _
    refine (hle (A' f)).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [hB']
    refine (GlobalTheory.RealWeil.norm_toLp_le_of_lintegral_le A' C hC h2 _).trans (le_of_eq ?_)
    rw [show (c : ℝ) = C.toReal ^ (1 / 2 : ℝ) from Real.coe_toNNReal _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntri
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.BlockForms


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem isBlockEmb_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  intro F E _ _ _ _ _ _ σ hσ n J _ r Xf Yf _ l d h ι hι
  obtain ⟨Φ, j, _, hΦs, -, -, hform⟩ := hι
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsig : Continuous (sigR (AF F) σ) := by
    have hc := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine hc.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => g.1.map Φ.symm :=
    Units.continuous_val.matrix_map hΦs
  have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g⁻¹).1.map Φ.symm :=
    Units.continuous_coe_inv.matrix_map hΦs
  have h3 : Continuous fun g : GlobalTheory.CuspRep.GA E d => Matrix.transpose (((g⁻¹).1.map Φ.symm).map (sigR (AF F) σ)) :=
    (h2.matrix_map hsig).matrix_transpose
  have hM : Continuous fun g : GlobalTheory.CuspRep.GA E d => (matHom _ σ J (ι g)).1 := by
    refine Continuous.congr ?_ fun g => (hform g).symm
    exact (continuous_const.add ((continuous_const.matrix_mul (h1.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)
  have hMi : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom _ σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
    refine (hM.comp continuous_inv).congr fun g => ?_
    simp only [Function.comp_apply, map_inv]
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hM, hMi⟩)

end GlobalTheory.BlockForms
end

