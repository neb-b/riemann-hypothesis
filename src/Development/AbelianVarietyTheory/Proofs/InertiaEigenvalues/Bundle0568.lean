module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LocalisationCoefficientExtensionIsWildInertiaCyc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExten
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiveDescent

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem isLocalHom_of_nonunit {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) {a : A} (ha : a ≠ 0) (hf : f a ∈ IsLocalRing.maximalIdeal B) : IsLocalHom f := by
  have hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥ := fun h => ha (by
    have : a ∈ (IsLocalRing.maximalIdeal B).comap f := hf
    rwa [h, Ideal.mem_bot] at this)
  have hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have : x ∈ (IsLocalRing.maximalIdeal B).comap f := by rw [he]; exact h
  exact this hx

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A →+* B)
    [IsLocalHom f] : Continuous f := by
  have hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  intro s hs
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  refine Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _))
    fun x hx => hn ?_)
  have h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

theorem span_eq_top_of_map {ι k K : Type} [Field k] [Field K] (f : k →+* K) {r : ℕ}
    (M : ι → Matrix (Fin r) (Fin r) k) (h : Submodule.span K (Set.range fun g => (M g).map f) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f) := h ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      have h0 : l (M g) = 0 := hl (Submodule.subset_span ⟨g, rfl⟩)
      have := congrArg f ((hexp (M g)).symm.trans h0)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]
    | smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]
  apply hl0
  refine LinearMap.ext fun Y => ?_
  rw [hexp, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have h1 := key (Matrix.single p q 1)
  rw [Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp),
    Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)] at h1
  simp only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1
  rw [h1, mul_zero]

theorem trace_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (h : ∃ e, IsDecomp (t := t) σ ρ χ e)
    (g : Γ) : (mat σ g).trace = (mat ρ g).trace + ∑ c : Fin t, ((χ ((c : ℕ) + 1) g : Aˣ) : A) := by
  obtain ⟨e, he⟩ := h
  apply IsFractionRing.injective A (FractionRing A)
  let d : Fin t → FractionRing A := fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)
  have h1 : Matrix.toLin' ((mat σ g).map (toFr A)) =
      e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d))) := by
    apply LinearMap.ext
    intro u
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    refine (he g u).trans ?_
    ext c
    · rfl
    · simp [Matrix.mulVec_diagonal, d]
  have h2 := congrArg (LinearMap.trace _ _) h1
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_toLin'_eq, Matrix.trace_diagonal] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  exact h2

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem charZero_O (N : NData R H what₂) (A : NAut N) (i : N.Loc) : CharZero (N.O i) :=
  (iotaO N A i).charZero

theorem l_mem_maximalIdeal (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  have hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i)) := by
    intro x y h
    have hx := A.iotaQ_alg i x
    rw [h, A.iotaQ_alg i y] at hx
    exact (Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm
  have : FaithfulSMul ℤ_[N.l i] (N.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := PadicInt.p_nonunit
  have := map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h
  rwa [map_natCast] at this

variable {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {i₀ : N₀.Loc} {i₁ : N₁.Loc}

theorem isLocalHom_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : IsLocalHom a.φ := by
  have := charZero_O N₀ A₀ i₀
  have hl : (N₁.l i₁).Prime := Fact.out
  refine isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_
  rw [map_natCast]
  exact l_mem_maximalIdeal N₁ A₁ i₁

theorem continuous_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Continuous a.φ :=
  haveI := isLocalHom_φ a
  continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem trace_eq (hC : GlobalTheory.TwSys.Cheb) (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁)
    (r₀ : GE N₀ →* GL (Fin R.nV) (N₀.O i₀)) (r₁ : GE N₁ →* GL (Fin R.nV) (N₁.O i₁))
    (h₀ : IsHeckeGalois N₀ i₀ (a.e x) r₀) (h₁ : IsHeckeGalois N₁ i₁ x r₁) (g : GE N₁) :
    a.φ (mat r₀ (a.γ g)).trace = (mat r₁ g).trace := by
  haveI := (N₁.O_complete i₁).toIsHausdorff
  haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance
  refine congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC
    (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace)
    ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g
  filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ
  obtain ⟨B₀, hB₀, hσ₀⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
  have e₀ := h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀
  have e₁ := h₁.2.2 w (h hw) B σ hB hσ
  rw [GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map] at e₁
  rw [AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]

end Record

theorem live_of_locExt : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  rintro hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩
  have hπ₀ := (a.Z π).1 hπ
  obtain ⟨ρ₀, hd₀⟩ := hZ _ hπ₀ _ (hr₀ _)
  refine ⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩
  have htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace := by
    intro g
    have h := trace_eq hC a π _ r (hr₀ _) hr g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add (f := _), map_sum,
      Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g] at h
    exact add_right_cancel h
  haveI := isLocalHom_φ a
  have hpos := pos_of_absIrrSub _ habs
  haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩
  refine absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)
  have h := span_eq_top_of_trace_eq
    ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom)
    (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
  · rw [eq_top_iff, ← h]
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨a.γ g, (mat_mapRep _ _ _).symm⟩
  · change (mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀))
      (a.γ g)).trace = _
    rw [mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace,
      ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]

end GlobalTheory.LiveDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A}
    (h : IsFrame bk B t p) (k : Hom B B') : IsFrame bk B' (k.f t) (k.f p) := by
  refine ⟨?_, k.f_str _ p h.2⟩
  rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ B B' k, h.1, Ideal.map_span, Set.image_singleton]

theorem env_inl_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A),
    IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  intro l _ K bk B t p hF En
  refine ⟨⟨fun m => (_root_.GlobalTheory.BSP.envFF l K bk B t p En m).flat, fun B' k => ?_⟩, _root_.GlobalTheory.BSP.envFF l K bk B t p En⟩
  obtain ⟨En'⟩ := _root_.GlobalTheory.BSP.nonempty_env l K bk B' (k.f t) (k.f p) (isFrame_map hF k)
  obtain ⟨k', hk'⟩ := _root_.GlobalTheory.BSP.env_isPO l K bk B B' t p k En En'
  exact ⟨En'.Q, k', En'.inl, hk'⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiscBasisCrystallineLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_discBasis_crystallineLattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  first | exact @GlobalTheory.BSP.height_Z_isUnit | exact GlobalTheory.BSP.height_Z_isUnit | (intros; apply GlobalTheory.BSP.height_Z_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.EtaleLattice

theorem exists_frob_matrix {R : Type} [CommRing R] [IsDomain R] (O : Subring R) (φ : R →+* R) (p : R) (hp : p ≠ 0)
    (hφp : φ p = p) (hφO : ∀ w ∈ O, φ w ∈ O) {d : ℕ} (Y A P Y' : Matrix (Fin d) (Fin d) R) (k m : ℕ) (u u' : R)
    (hu' : u' ∈ O) (huu : u * u' = 1) (hA : ∀ i j, A i j ∈ O) (hP : ∀ i j, P i j ∈ O)
    (hφ : (p ^ k * u) • Y.map φ = Y * A) (hY' : p ^ m • Y' = Y * P)
    (hlat : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, p ^ n ∣ (Y *ᵥ v) i) →
      ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • v = p ^ n • (P *ᵥ w)) :
    ∃ B : Matrix (Fin d) (Fin d) R, (∀ i j, B i j ∈ O) ∧ Y'.map φ = Y' * B := by
  have cancel : ∀ (n : ℕ) (M N : Matrix (Fin d) (Fin d) R), p ^ n • M = p ^ n • N → M = N := by
    intro n M N h
    refine Matrix.ext fun i j => ?_
    exact mul_left_cancel₀ (pow_ne_zero n hp) (congrFun (congrFun h i) j)
  have h1 : p ^ m • Y'.map φ = Y.map φ * P.map φ := by
    rw [← Matrix.map_mul, ← hY']
    refine Matrix.ext fun i j => ?_
    simp [hφp]
  set V : Matrix (Fin d) (Fin d) R := u' • (A * P.map φ) with hV
  have hVO : ∀ i j, V i j ∈ O := by
    intro i j
    rw [hV, Matrix.smul_apply, Matrix.mul_apply]
    exact O.mul_mem hu' (O.sum_mem fun c _ => O.mul_mem (hA i c) (hφO _ (hP c j)))
  have h2 : Y * V = p ^ (k + m) • Y'.map φ := by
    rw [hV, Matrix.mul_smul, ← Matrix.mul_assoc, ← hφ, Matrix.smul_mul, ← h1, smul_smul, smul_smul]
    congr 1
    linear_combination (p ^ k * p ^ m) * huu
  have h3 : ∀ j, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • (fun i => V i j) = p ^ (k + m) • (P *ᵥ w) := by
    intro j
    refine hlat _ (fun i => hVO i j) _ fun i => ⟨φ (Y' i j), ?_⟩
    exact congrFun (congrFun h2 i) j
  choose w hwO hw using h3
  refine ⟨Matrix.of fun i j => w j i, fun i j => hwO j i, ?_⟩
  have h4 : p ^ m • V = p ^ (k + m) • (P * Matrix.of fun i j => w j i) := by
    refine Matrix.ext fun i j => ?_
    exact congrFun (hw j) i
  apply cancel (k + m)
  apply cancel m
  rw [← h2, ← Matrix.mul_smul, h4, Matrix.mul_smul, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul, smul_comm]

theorem isUnit_saturated_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  intro l hl K bk τ hτ d N ρ hρ Y1 δ A1 hdet hδ hφ hg m P Y' hP hPdet hY' hlat hsat
  obtain ⟨-, -, h3, -, -, h6, h7⟩ := _root_.GlobalTheory.OEDvr.main l K bk
  obtain ⟨ht1, -, -, ht4⟩ := _root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  haveI : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have hlu : ¬ IsUnit (l : bk.S) := fun h => by
    have := h.map bk.evW
    rw [map_natCast] at this
    exact (WittVector.irreducible l (k := Cb l)).not_isUnit this
  have hev : ∀ s, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨k, δ', hnd, rfl⟩ := WfDvdMonoid.max_power_factor' hδ hlu
  obtain ⟨u', hu', huu⟩ := h3 δ' hnd
  have hφW : ((l : WCb l) ^ k * bk.evW δ') • (Y1.map (inclW l)).map (frobW l).toRingHom =
      Y1.map (inclW l) * A1.map bk.evW := by
    have := congrArg (fun M => Matrix.map M (inclW l)) hφ
    simp only [Matrix.map_mul] at this
    rw [show A1.map bk.evW = (A1.map bk.ev).map (inclW l) from rfl, ← this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [BK.evW, RingHom.comp_apply, ← GlobalTheory.Prism.frobW_inclW]
    rfl
  obtain ⟨B, hB, hBφ⟩ := exists_frob_matrix bk.OE (frobW l).toRingHom (l : WCb l) hl0 (map_natCast _ _) h7
    (Y1.map (inclW l)) (A1.map bk.evW) P Y' k m (bk.evW δ') u' hu' huu (fun i j => hev _) hP hφW hY' hlat
  refine _root_.GlobalTheory.SatInvUnit.isUnit_of_saturated l K bk d Y' B ?_ hB hBφ ?_ hsat
  · intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hdet hPdet this.symm
  · intro g hfix
    obtain ⟨t, ht⟩ := ht1
    obtain ⟨s, hs⟩ := ht4 (g : GQ l)
    set Z : Matrix (Fin d) (Fin d) (WCb l) := ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) with hZ
    have hZu : IsUnit Z := ((hρ g).map (algebraMap ℤ_[l] (Ainf l)).mapMatrix).map (inclW l).mapMatrix
    have e1 : (t : WCb l) ^ N • (Z * (Y1.map (inclW l)).map (galW l (g : GQ l))) =
        (s : WCb l) ^ N • Y1.map (inclW l) := by
      have := congrArg (fun M => Matrix.map M (inclW l)) (hg g hfix)
      have e : (Y1.map (inclW l)).map (galW l (g : GQ l)) = (Y1.map (Per.σA (g : GQ l))).map (inclW l) := by
        refine Matrix.ext fun i j => ?_
        exact GlobalTheory.Prism.galW_inclW _ _
      rw [e, hZ, ← Matrix.map_mul, ht, hs]
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun this i) j
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow] using this
    have e2 : (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) = (Y1.map (inclW l)).map (galW l (g : GQ l)) * P := by
      have eP : P.map (galW l (g : GQ l)) = P := by
        refine Matrix.ext fun i j => ?_
        exact h6 g hfix _ (hP i j)
      rw [← eP, ← Matrix.map_mul, ← hY']
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    refine ⟨((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z, ?_, ?_⟩
    · exact hZu.smul _
    · have e3 : (l : WCb l) ^ m • ((((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z) * Y'.map (galW l (g : GQ l))) =
          (l : WCb l) ^ m • Y' := by
        rw [← Matrix.mul_smul, e2, hY', ← Matrix.mul_assoc, Units.smul_def, Matrix.smul_mul, Units.val_pow_eq_pow_val,
          Units.val_mul, mul_pow, mul_smul, e1, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      refine Matrix.ext fun i j => ?_
      exact mul_left_cancel₀ (pow_ne_zero m hl0) (congrFun (congrFun e3 i) j)

end GlobalTheory.EtaleLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHom
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PackMap

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

theorem latW_TWact {T T' : LocLat G ℚ_[l] K O} (f : LatHom T.L T'.L) (s : GQ l) (g : G)
    (y : TW (OW l O) T) :
    latW f (TWact (galOW O s) T g y) = TWact (galOW O s) T' g (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [latW, TWact, TensorProduct.map_tmul]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem homW_act {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L} {F : BK.Hom P Q}
    (h : IsMapOf I I' f F) (s : GQ l) (g : G) (v : ι → OW l O) :
    homW t ϖ F (I.act s g v) = I'.act s g (homW t ϖ F v) :=
  I'.j.injective (by rw [h, I.j_act, latW_TWact, I'.j_act, h])

variable [TameDescentExponentData K l e a]

theorem app_act_of_cover {s : G →* GQ l} {η H η' H' : ℕ} {D₁ : BKDat O K l e a ι η H}
    {D₂ : BKDat O K l e a κ η' H'} {T₁ T₂ : LocLat G ℚ_[l] K O} (R₁ : GalDat t ϖ s D₁ T₁)
    (R₂ : GalDat t ϖ s D₂ T₂) {f : LatHom T₁.L T₂.L} {F : BK.Hom D₁.toPhiMod D₂.toPhiMod}
    (hF : IsMapOf R₁.I R₂.I f F) (hcov : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (γ : TameGal K l e a) (v : Vec K a ι) :
    F.app (D₁.desc.act γ v) = D₂.desc.act γ (F.app v) := by
  have hb : ∀ i : ι, F.app (D₁.desc.act γ (bas i)) = D₂.desc.act γ (F.app (bas i)) := by
    intro i
    obtain ⟨g, hg⟩ := hcov γ
    have m0 : (bas i : Vec K a ι) ∈ D₁.M := PhiMod.bas_mem_M _ i
    have m1 : D₁.desc.act γ (bas i) ∈ D₁.M := D₁.desc.act_mem_M γ _ m0
    have m2 : F.app (bas i) ∈ D₂.M := F.app_mem_M m0
    have m3 : D₂.desc.act γ (F.app (bas i)) ∈ D₂.M := D₂.desc.act_mem_M γ _ m2
    have m4 : F.app (D₁.desc.act γ (bas i)) ∈ D₂.M := F.app_mem_M m1
    have e1 := R₁.desc g γ hg ⟨_, mem_ME_of_mem_M m0⟩ ⟨_, mem_ME_of_mem_M m1⟩ rfl
    have e2 := R₂.desc g γ hg ⟨_, mem_ME_of_mem_M m2⟩ ⟨_, mem_ME_of_mem_M m3⟩ rfl
    have h1 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m1⟩
    have h2 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m0⟩
    have key : toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩ =
        toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ :=
      calc toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩
          = homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m1⟩) := h1.symm
        _ = homW t ϖ F (R₁.I.act (s g) g (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) := by rw [e1]
        _ = R₂.I.act (s g) g (homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) :=
          homW_act hF _ _ _
        _ = R₂.I.act (s g) g (toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m2⟩) := by rw [h2]
        _ = toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ := e2
    exact congrArg Subtype.val (toW_injective t ϖ _ key)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_bas v, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D₁.desc.act_smul_tot, F.app_smul_tot, F.app_smul_tot, D₂.desc.act_smul_tot, hb]

end General

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL)
    (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L),
    ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  intro BS l _ a e _ _ ϖ LL _ _ η H T₁ T₂ P₁ P₂ f
  let f' : LatHom (resF T₁ (ϖ.field a)).L (resF T₂ (ϖ.field a)).L :=
    ⟨f.f, fun _ x => f.equiv _ x, f.cont, f.T_le⟩
  obtain ⟨F, hF⟩ := GlobalTheory.BKReal.Full.main BS l a e _ _ (thetaW a LL) ϖ _ _ P₁.D.toPhiMod P₂.D.toPhiMod
    (resF T₁ (ϖ.field a)) (resF T₂ (ϖ.field a))
    (P₁.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
    (P₂.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) P₁.isBK P₂.isBK f'
  have hF' : IsMapOf P₁.R.I P₂.R.I f F := hF
  have hcov : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hc⟩ := (_root_.GlobalTheory.TameCover.main l a e ϖ LL).2.2.1 γ
    refine ⟨⟨k, ?_⟩, hc⟩
    show k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  exact ⟨⟨F, app_act_of_cover P₁.R P₂.R hF' hcov⟩, hF'⟩

end GlobalTheory.BKGal.PackMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBounds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact _root_.GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
end

