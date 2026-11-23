module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLeStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_subgroup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (S : Subgroup (GL (Fin N) (Af E))), IsOpen (S : Set (GL (Fin N) (Af E))) → ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧ IsCompact (L : Set (GL (Fin N) (Af E))) := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le | exact GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequence
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimVec

theorem normalised_subseq_limit : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  intro M _ _ _ g hg
  let e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) := (Module.finBasis ℂ M).equivFun
  let s : ℕ → ℂ := fun k => ((‖e (g k)‖⁻¹ : ℝ) : ℂ)
  have hv : ∀ k, e (g k) ≠ 0 := fun k h => hg k (by simpa using h)
  have hmem : ∀ k, s k • e (g k) ∈ Metric.sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1 := by
    intro k
    have hn : ‖e (g k)‖ ≠ 0 := norm_ne_zero_iff.mpr (hv k)
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp only [s, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn
  obtain ⟨v, hvs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1).tendsto_subseq hmem
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hvs
    simp at hvs
  refine ⟨fun k => s (φ k), φ, e.symm v, hφ, by simpa using hv0, fun ℓ => ?_⟩
  let L : (Fin (Module.finrank ℂ M) → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ e.symm.toLinearMap
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h := (hL.tendsto v).comp hlim
  have hfun : (L ∘ ((fun k => s k • e (g k)) ∘ φ)) = fun k => s (φ k) * ℓ (g (φ k)) := by
    funext k
    simp [L]
  rw [hfun] at h
  simpa [L] using h

end GlobalTheory.CompanionTheory.LimVec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.CompanionTheory.TwY
open PositivityTheory.RgBcC (KMod lefE lefT phiOf infOf IsMult Inf GLs IsEig MultAlg)
open PositivityTheory.RgBcC.Real (IsLefK)
open PositivityTheory.RgBcC.RealD (invA flipA trOn hwSp harmSet kF gelA barF IsPair IsDerivK)
open PositivityTheory.RgTw (G Mat)
open scoped ContDiff InnerProductSpace
attribute [local instance] borelH Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TwY.ThInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def adjH : Lie E n →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᴴ
      map_add' := fun X Y => by
        rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
      map_smul' := fun t X => by
        rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

theorem adjH_apply (X : Lie E n) (i j : Fin n) : adjH X i j = star (X j i) := rfl

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
  ext i j
  change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
  rw [h, ← map_inv]
  rfl

theorem thetaA_infGL (y : GL (Fin n) (Cinf E)) :
    thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [pFin_finGL]; rfl)

theorem thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
  classical
  have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
  rw [e, thetaA_infGL]
  congr 1
  refine Units.ext ?_
  ext i j v
  rw [thetaR_val, ← map_inv, ← map_inv]
  change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
  rw [locInf_apply, locInf_apply]
  by_cases hv : v = w
  · simp only [hv, if_true]
    change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
    simp [Matrix.star_apply]
  · simp only [hv, if_false]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem toL_thetaR (y : GL (Fin n) (Cinf E)) :
    toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [thetaR_val]
  ext i j : 2
  change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
    chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

theorem lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
    lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
  have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
      chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
  have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
    (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
    ((adjH (E := E) (n := n)).hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
  unfold lieD
  rw [e.fderiv_eq, h2.fderiv]
  simp


open ComplexConjugate in
theorem atEmb_conjugate (w : InfinitePlace E) (z : ℂ) :
    atEmb (ComplexEmbedding.conjugate w.embedding) z = atEmb w.embedding (conj z) := by
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
  unfold atEmb
  rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne, if_pos rfl]


open ComplexConjugate in
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) : star (atEmb w.embedding z) = atEmb w.embedding (conj z) := by
  funext v
  simp only [atEmb, InfinitePlace.mk_embedding, if_true, Pi.star_apply]
  by_cases hv : v = w
  · subst hv; simp
  · classical
    rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, star_zero]

def sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : Lie E n := toL (Matrix.single a b (atEmb w.embedding z))

open ComplexConjugate in
theorem adjH_sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : adjH (sg w a b z) = sg w b a (conj z) := by
  funext i j
  rw [adjH_apply]
  change star (Matrix.single a b (atEmb w.embedding z) j i) = Matrix.single b a (atEmb w.embedding (conj z)) i j
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos h.symm, star_atEmb]
  · rw [if_neg h, if_neg fun h' => h h'.symm, star_zero]

theorem Eop_apply (τ : E →+* ℂ) (a b : Fin n) (φ : Sm E n) (g : GA E n) :
    (Eop τ a b φ).1 g = (1 / 2 : ℂ) * (lieD (toL (Matrix.single a b (atEmb τ 1))) φ.1 g -
      Complex.I * lieD (toL (Matrix.single a b (atEmb τ Complex.I))) φ.1 g) := rfl

def thV (π : CuspSub E n) (h : ThetaFix π) : Module.End ℂ π.V where
  toFun ψ := ⟨(h.2 ψ.1 ψ.2).choose, (h.2 ψ.1 ψ.2).choose_spec.1⟩
  map_add' a b := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (a + b).1 (a + b).2).choose.1 x =
      (h.2 a.1 a.2).choose.1 x + (h.2 b.1 b.2).choose.1 x
    rw [(h.2 (a + b).1 (a + b).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2, (h.2 b.1 b.2).choose_spec.2]
    rfl
  map_smul' c a := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (c • a).1 (c • a).2).choose.1 x = c * (h.2 a.1 a.2).choose.1 x
    rw [(h.2 (c • a).1 (c • a).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2]
    rfl

theorem thV_apply (π : CuspSub E n) (h : ThetaFix π) (ψ : π.V) (x : GA E n) :
    ((thV π h ψ : π.V) : Sm E n).1 x = (ψ : Sm E n).1 (thetaA E n x) :=
  (h.2 ψ.1 ψ.2).choose_spec.2 x

end GlobalTheory.CompanionTheory.TwY.ThInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpan
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem act_fin_val {N : ℕ} (g : GL (Fin N) (Af E)) (φ : Sm E N) (x : GA E N) :
    (act (.fin g) φ).1 x = φ.1 (x * finGL E N g) := rfl

theorem memInd2_act_fin {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)}
    (g : GL (Fin (r + s)) (Af E)) {φ : Sm E (r + s)} (h : MemInd2 U₁ U₂ φ) :
    MemInd2 U₁ U₂ (act (.fin g) φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun k g' => ?_⟩
  · rw [act_fin_val, act_fin_val, mul_assoc, h1]
  · convert h2 k (g' * g) using 2 with m
    rw [act_fin_val, map_mul, mul_assoc, mul_assoc]

theorem indSpan_finStable (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    FinStable (indSpan U₁ U₂) := by
  intro g φ hφ
  change φ ∈ Submodule.span ℂ _ at hφ
  change _ ∈ Submodule.span ℂ _
  induction hφ using Submodule.span_induction with
  | mem φ h => exact Submodule.subset_span (memInd2_act_fin g h)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwist
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem finStable_tw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ) (h : FinStable U) : FinStable (tw U z) := by
  rintro g _ ⟨ψ, hψ, rfl⟩
  exact ⟨_, U.add_mem (U.smul_mem _ (h g ψ hψ)) (U.smul_mem _ hψ), (act_mulChi _ (.fin g) ψ).symm⟩

end GlobalTheory.CompanionTheory.LimV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpan
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LimV

theorem finiteDimensional_prodSpan_of_fd : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)),
    FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  intro A B U₁ U₂ h₁ h₂
  let φ : U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b x => a.1 x.1 * b.1 x.2)
      (fun a a' b => by ext x; simp [add_mul])
      (fun c a b => by ext x; simp [mul_assoc])
      (fun a b b' => by ext x; simp [mul_add])
      (fun c a b => by ext x; simp [mul_left_comm])
  let T : U₁ ⊗[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) := TensorProduct.lift φ
  have hle : prodSpan U₁ U₂ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro F ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : U₁) ⊗ₜ[ℂ] (⟨b, hb⟩ : U₂), by simp [T, φ]⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := LinearMap.finiteDimensional_range T
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscrete
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdV

open GlobalTheory.CompanionTheory.AdmDiscFin GlobalTheory.LevelTypeProj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem continuous_sliceTC (φ : Sm E N) (g : GA E N) :
    Continuous fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E N => (Unitary.toUnits k : GL (Fin N) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin N) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E N) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E N =>
      ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E N =>
      toL ((Unitary.toUnits k : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

theorem fd_typed {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (V : Submodule ℂ (Sm E N))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (hV : IsDiscrete V)
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed V K W) := by
  haveI := hW
  obtain ⟨ψ, hψV, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  have hadm : PrAdm.SupSpansPsiPart V ψ = V :=
    (hV.irred _ (PrAdm.admissible_span_le V ψ) (PrAdm.isStable_admissible_span hV.stable ψ)).resolve_left fun h => hψ0 (by
      have h2 := PrAdm.mem_admissible_span_self hψV
      rw [h] at h2
      simpa using h2)
  let Y : Submodule ℂ (Kinf E N → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E N, φ ∈ typed V K W ∧ ∃ g : GA E N, f = fun k => φ.1 (g * infGL E N (Unitary.toUnits k))}
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, g, rfl⟩
    exact hφ.2.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφ, g * infGL E N (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, g, rfl⟩ := hf
      exact continuous_sliceTC φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  have hF := PrAdm.finiteDimensional_admissible_isotypic hV.aut (hV.aut ψ hψV) hK (dualRep Y hYl) (isContRep_dualRep Y hYl hYc)
  rw [hadm] at hF
  refine Submodule.finiteDimensional_of_le (S₂ := V ⊓ typePart K (dualRep Y hYl)) ?_
  intro φ hφ
  refine ⟨hφ.1, fun k hk => Subtype.ext (funext fun g => hφ.2.1 k hk g), fun g => ?_⟩
  exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφ, g, rfl⟩)

end GlobalTheory.CompanionTheory.LimV.FdV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

open GlobalTheory.Mem.Chr.CharModel

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem logFin_eq_zero_of_integral (t : (Af E)ˣ)
    (h1 : (t : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E)
    (h2 : ((t⁻¹ : (Af E)ˣ) : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : logFin E t = 0 := by
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v
    have a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

theorem det_mem_of_entries {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem logFin_det_of_mem {N : ℕ} {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logFin E (GeneralLinearGroup.det c) = 0 := by
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc
  refine logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_
  rw [← map_inv]
  exact det_mem_of_entries _ _ h2

theorem logNorm_finId (u : (Af E)ˣ) : logNorm E (finId E u) = - logFin E u := by
  have h1 : finPart E (finId E u) = u := Units.ext (by
    change (1 : Af E) - 1 + u = u
    simp)
  have h2 : infPart E (finId E u) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, h2, logInf_one, zero_sub]

theorem norm_det_unitary_at {N : ℕ} (k : Kinf E N) (v : InfinitePlace E) :
    ‖((GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) v‖ = 1 := by
  have hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E) := Matrix.det_of_mem_unitary k.2
  have h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1 :=
    congrFun (Unitary.star_mul_self_of_mem hd) v
  have h2 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h2
  exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])

theorem logNorm_det_cf (N : ℕ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logNorm E (GeneralLinearGroup.det (cf N k c)) = 0 := by
  rw [cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc,
    Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]
  simp

theorem chiDet_absC_cf (N : ℕ) (w : ℂ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    chiDet N (GlobalTheory.CuspRep.Model.absC E w) (cf N k c) = 1 := by
  apply Units.ext
  change Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1
  rw [logNorm_det_cf N k hc]
  simp

end

theorem absFn_flat : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ),
    FlatFn (absFn (E := E) N w) := by
  intro E _ _ _ N w
  refine ⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩
  · simp only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]
  · have h : absFn (E := E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by
      rw [mulChi_apply]
      simp [absFn, oneFn]
    rw [h]
    exact (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2

end GlobalTheory.CompanionTheory.LimV

end
end

