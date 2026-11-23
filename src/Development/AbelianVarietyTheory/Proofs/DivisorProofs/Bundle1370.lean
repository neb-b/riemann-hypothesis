module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFinite
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

def intFin : Set (Af F) := {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

theorem isOpen_intFin : IsOpen (intFin F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ => Valued.isOpen_valuationSubring _)

theorem isCompact_intFin : IsCompact (intFin F) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem sub_archIn_apply (w : κ → AF F) (i : κ) :
    (w - archIn F κ (archOut F κ w)) i = ((0 : Ainf F), (w i).2) := by
  have h : archIn F κ (archOut F κ w) i = infAd F (evI F (w i)) := by
    rw [archIn_apply, archOut_apply, LinearEquiv.symm_apply_apply]; rfl
  rw [Pi.sub_apply, h]
  refine Prod.ext ?_ ?_
  · change (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1) = 0
    rw [RingEquiv.symm_apply_apply, sub_self]
  · change (w i).2 - 0 = (w i).2
    rw [sub_zero]

theorem mem_slab_iff (m : ℕ) (hm : 0 < m) (w : κ → AF F) :
    w ∈ slab F κ m ↔ ∀ i, algebraMap F (Af F) ((m : F)⁻¹) * (w i).2 ∈ intFin F := by
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hc : algebraMap F (Af F) ((m : F)⁻¹) * (m : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, inv_mul_cancel₀ hm0, map_one]
  change (∀ i, ∃ a : AF F, _ ∧ _ ∧ _) ↔ _
  refine forall_congr' fun i => ?_
  rw [sub_archIn_apply]
  constructor
  · rintro ⟨a, -, ha, he⟩
    have h2 : (w i).2 = (m : Af F) * a.2 := by
      have := congrArg Prod.snd he
      rw [this]
      change sndA F ((m : AF F) * a) = _
      rw [map_mul, map_natCast]; rfl
    intro v
    rw [h2, ← mul_assoc, hc, one_mul]
    exact ha v
  · intro h
    refine ⟨pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2), ?_, fun v => h v, ?_⟩
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 = 0
      exact map_zero _
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = fstA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul]
        change (0 : Ainf F) = fstA F (m : AF F) * 0
        rw [mul_zero]
      · change (w i).2 = sndA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul, map_natCast]
        change (w i).2 = (m : Af F) * (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2)
        rw [← mul_assoc, mul_comm (m : Af F), hc, one_mul]

theorem isOpen_slab (m : ℕ) (hm : 0 < m) : IsOpen (slab F κ m) := by
  have : slab F κ m = ⋂ i, (fun w : κ → AF F => algebraMap F (Af F) ((m : F)⁻¹) * (w i).2) ⁻¹' intFin F := by
    ext w; rw [mem_slab_iff F κ m hm]; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_intFin F).preimage
    (continuous_const.mul (continuous_snd.comp (continuous_apply i)))

theorem archIn_mem_slab (t : Fin (dimA F κ) → ℝ) : archIn F κ t ∈ slab F κ 1 := by
  rw [mem_slab_iff F κ 1 one_pos]
  intro i v
  have : (archIn F κ t i).2 = 0 := rfl
  rw [this, mul_zero]
  exact zero_mem _

open scoped Pointwise in
theorem slab_open_cube_pos_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧ ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ := by
  intro F _ _ κ _
  refine ⟨fun m hm => isOpen_slab F κ m hm, fun μ hμ => ?_⟩
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  refine ⟨?_, fun A hA => ?_⟩
  · let U := archOut F κ ⁻¹' (Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1) ∩ slab F κ 1
    have hU : IsOpen U :=
      ((isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage (continuous_archOut F κ)).inter
        (isOpen_slab F κ 1 one_pos)
    have hne : U.Nonempty := by
      refine ⟨archIn F κ (fun _ => 1 / 2), ?_, archIn_mem_slab F κ _⟩
      simp only [Set.mem_preimage, archOut_archIn, Set.mem_pi, Set.mem_univ, true_implies]
      intro _; constructor <;> norm_num
    refine lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono ?_)
    exact Set.inter_subset_inter_left _ (Set.preimage_mono (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self))
  · let K : Set (κ → AF F) := (fun y : κ → Af F => fun i => pairA F 0 (y i)) '' Set.univ.pi fun _ => intFin F
    have hK : IsCompact K := by
      refine (isCompact_univ_pi fun _ => isCompact_intFin F).image (continuous_pi fun i => ?_)
      exact (continuous_const.prodMk (continuous_apply i) : Continuous fun y : κ → Af F => ((0 : Ainf F), y i))
    have hsub : archOut F κ ⁻¹' A ∩ slab F κ 1 ⊆ archIn F κ '' A + K := by
      rintro w ⟨hwA, hw⟩
      refine Set.mem_add.2 ⟨archIn F κ (archOut F κ w), ⟨_, hwA, rfl⟩, w - archIn F κ (archOut F κ w),
        ⟨fun i => (w i).2, fun i _ => ?_, funext fun i => (sub_archIn_apply F κ w i).symm⟩, add_sub_cancel _ _⟩
      have h := (mem_slab_iff F κ 1 one_pos w).1 hw i
      rwa [Nat.cast_one, inv_one, map_one, one_mul] at h
    exact ((measure_mono hsub).trans_lt ((hA.image (continuous_archIn F κ)).add hK).measure_lt_top).ne

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPoint
section
noncomputable section

namespace GlobalTheory.LevModel

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem exists_frBor_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {p p' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d p y) (h' : FrOver d p' y') (hb : FrBor t p p') : ∃ t' : Ix Dw → Sˣ, FrBor t' y y' := by
  obtain ⟨e, hu, -⟩ := h
  obtain ⟨e', hu', -⟩ := h'
  obtain ⟨ex, au, -⟩ := hb
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').2.1 (by rw [← e, ← e', ex]) fun τ i => ?_
  obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
  refine ⟨cf, by rw [c₁]; exact (t _).isUnit, c₂, ?_⟩
  have k := (GlobalTheory.FrameLift.comb_iff d.m e (fun j => (p.tan τ j).1) cf (ex ▸ (p'.tan τ i).1)).1 hcf
  rw [funext (hu τ), hu'] at k
  exact k

theorem lact_conj_eq_rmul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hLev σ₂ hσ₂ k₂ k δ hG hδ hOv γ₂ hγ₂ x hx x' hM
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    unfold GoodEmb at hσ₂ ⊢
    rw [← hσ₂]
    rfl
  have hU := hL.unf _ hσ
  have hU₂ := hL₂.unf _ hσ₂
  have hγx : lact γ₂ x ∈ ((U₂ σ₂).X k₂).dom := (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ hγ₂ x).2 hx
  obtain ⟨t₀, ht₀⟩ := (hU₂.2.2.2.1 k₂ k₂ ⟨x, hx⟩ ⟨lact γ₂ x, hγx⟩).2
    ⟨γ₂, hγ₂, ExtFPf.oneF _, ExtFPf.oneF_mem _, by rw [ExtFPf.rmul_oneF]⟩
  have hM' : Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ (lact γ₂ x) (lact (MulAut.conj δ γ₂) x') := by
    intro τ h₂ h₁
    have e := hM τ h₂ h₁
    show ((MulAut.conj δ γ₂ : GL _ _) : Matrix _ _ _).map τ * mat x' ⟨τ, h₁⟩ =
      (δ : Matrix _ _ _).map τ * ((γ₂ : Matrix _ _ _).map τ * mat x ⟨τ, h₂⟩)
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul (f := τ), ← Matrix.map_mul (f := τ),
      ← Units.val_mul, ← Units.val_mul, MulAut.conj_apply, inv_mul_cancel_right]
  obtain ⟨hx', t₁, -, y, hy₁, hy₂⟩ := hOv x hx x' hM
  obtain ⟨hx'', t₂, -, y', hy₁', hy₂'⟩ := hOv (lact γ₂ x) hγx _ hM'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨t', ht'⟩ := exists_frBor_of_frOver d hy₂ hy₂' ht₀
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have hb := G.2.1 _ _ _ _ _ (G.2.1 _ _ _ _ _ hy₁ ht') (G.2.2.1 _ _ _ hy₁')
  obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k ⟨x', hx'⟩ ⟨_, hx''⟩).1 ⟨_, hb⟩
  exact ⟨γ, hγ, b, hb', eq_of_heq (Sigma.mk.inj e).2⟩

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothing
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SelfSmoothing

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smoothings (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∃ β, IsTest (invSet E a) β ∧ smoothing ν β φ.1 = f}
  zero_mem' := ⟨0, isTest_zero, funext fun x => by simp [smoothing]⟩
  add_mem' := by
    rintro _ _ ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
    refine ⟨β + γ, hβ.add hγ, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_add (hβ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hγ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn))
    simp only [smoothing, Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c _ ⟨β, hβ, rfl⟩
    refine ⟨fun y => β y * c, hβ.mul contDiff_const, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_const_mul c _)
    simp only [smoothing]
    congr 1
    funext y
    ring

theorem exists_smoothing_eq_self : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  intro hP E _ _ _ a ν _ φ hφ
  obtain ⟨α, hα, hlim⟩ := _root_.GlobalTheory.AutGrowth.ApproxId.exists_approx_identity E a ν
  obtain ⟨V, hVf, -, hV⟩ := _root_.GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space hP E a ν φ hφ
  let V₀ : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  let V' : Submodule ℂ (GA E a → ℂ) := smoothings ν φ ⊓ V₀
  have hf : FiniteDimensional ℂ V' := Submodule.finiteDimensional_of_le (S₂ := V₀) inf_le_right
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨⟨α n, (hα n).1, rfl⟩, ⟨_, hv, rfl⟩⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  exact hφ'.1

end GlobalTheory.AutGrowth.SelfSmoothing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjective
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem multilinear_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] {N : Type} [AddCommGroup N] [Module ℂ N]
    (Φ : MultilinearMap (RingHom.id ℂ) M N) (s : ∀ i, Set (M i)) (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ Submodule.span ℂ (s i)) :
    Φ f ∈ Submodule.span ℂ {y | ∃ g : ∀ i, M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  first
  | exact @_root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
  | exact _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
  | (apply _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image ..)

theorem span_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    Submodule.span ℂ (Set.range (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) mu)) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem span_wInf (lam : InfinitePlace E → DomWeight n) :
    Submodule.span ℂ (Set.range fun k : infU E n => wInf lam k.1) = ⊤ := by
  rw [eq_top_iff]
  rintro Q -
  obtain ⟨z, rfl⟩ := GlobalTheory.PiTensorCommute.mem_range_piTensorHomMap Q
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.piTensorHomMap_tprod_eq_map]
    refine Submodule.smul_mem _ _ ?_
    have h := multilinear_mem_span
      (PiTensorProduct.mapMultilinear ℂ (fun v => nablaSq ℂ n (lam v)) (fun v => nablaSq ℂ n (lam v)))
      (fun v => Set.range (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) (lam v))) f
      (fun v => by rw [span_smallRep_unitary]; trivial)
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨g, hg, rfl⟩
    choose u hu using hg
    obtain ⟨x, hx, hxc⟩ := GlobalTheory.InfSurj.exists_infU_cAll_eq E n
      (fun v => GlobalTheory.Branching.unitaryIncl n (u v)) (fun v => (u v).2)
    refine Submodule.subset_span ⟨⟨x, hx⟩, ?_⟩
    rw [PiTensorProduct.mapMultilinear_apply]
    change PiTensorProduct.map _ = _
    congr 1
    funext v
    rw [← hu v]
    have h1 := congrFun hxc v
    change cEmb v.embedding x = _ at h1
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x) = GlobalTheory.Branching.sqRep ℂ n (lam v) _
    rw [h1]
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem Phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let b := Module.finBasis ℂ (Wsp lam)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := vecM S lam K') b
  have hxe : x = ∑ j, e x j ⊗ₜ b j := by
    conv_lhs => rw [← e.symm_apply_apply x]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
    simp
  have hval : ∀ (x₀ : finU (E := E) (n := n)) (k : infU E n), ∑ j, (e x j).1 x₀ (wInf lam k.1 (b j)) = 0 := by
    intro x₀ k
    have h := congrFun hx (x₀.1 * k.1)
    have hw : wInf lam (x₀.1 * k.1) = wInf lam k.1 := by rw [map_mul, wInf_fin, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxe, map_sum] at h
    simpa only [Phi_tmul, phiFun_apply, splitFin_mul, hw, Finset.sum_apply, Pi.zero_apply] using h
  have hall : ∀ (x₀ : finU (E := E) (n := n)) (T : Module.End ℂ (Wsp lam)), ∑ j, (e x j).1 x₀ (T (b j)) = 0 := by
    intro x₀ T
    let Λ : Module.End ℂ (Wsp lam) →ₗ[ℂ] ℂ :=
      { toFun := fun T => ∑ j, (e x j).1 x₀ (T (b j))
        map_add' := fun T T' => by simp [Finset.sum_add_distrib]
        map_smul' := fun c T => by simp [Finset.mul_sum] }
    have hS : Submodule.span ℂ (Set.range fun k : infU E n => wInf lam k.1) ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hval x₀ k
    rw [span_wInf] at hS
    exact hS (Submodule.mem_top (x := T))
  have hc : e x = 0 := by
    refine Finsupp.ext fun j => Subtype.ext (funext fun x₀ => LinearMap.ext fun w => ?_)
    have h := hall x₀ ((b.coord j).smulRight w)
    simp [Finsupp.single_apply] at h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp), if_pos rfl] at h
  exact e.injective (hc.trans e.map_zero.symm)

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectivePairTOfLev
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.TatePerfect

theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (k n : ℕ) :
    (k • t).lev n = t.lev n ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem lev_congr {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (h2 : ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s)
    (φ : Tate p M →ₗ[ℤ_[p]] Tate p M') {n : ℕ} {t t' : Tate p M} (h : t.lev n = t'.lev n) :
    (φ t).lev n = (φ t').lev n := by
  have e : t = t' + (t - t') := by abel
  have h3 : (t - t').lev n = 1 := by
    have := congrArg (·.lev n) e
    simp only [Tate.lev_add] at this
    rw [h] at this
    exact left_eq_mul.1 this
  obtain ⟨s, hs⟩ := (h2 n _).1 h3
  rw [e, hs, map_add (f := _), map_smul, Tate.lev_add, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, lev_nsmul,
    Tate.lev_pow, _root_.mul_one]

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  (A : Out.PolAV (Sp C))

theorem weilT_flip_surjective
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (h2 : ∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s)
    (φ : TateA A p →ₗ[ℤ_[p]] Tate p Cˣ) : ∃ s : TateA A p, ∀ t, weilT A p t s = φ t := by
  choose! τ hτ using h1
  let κ : ℕ → GlobalTheory.ChTor.Pts A.A → Cˣ := fun n x => (φ (τ n x)).lev n
  have hκ : ∀ n (t : TateA A p), κ n (t.lev n) = (φ t).lev n := fun n t =>
    lev_congr h2 φ (hτ n _ (t.lev_pow n))
  have hm : ∀ n z z', z ^ p ^ n = 1 → z' ^ p ^ n = 1 → κ n (z * z') = κ n z * κ n z' := by
    intro n z z' hz hz'
    have e : z * z' = (τ n z + τ n z').lev n := by rw [Tate.lev_add, hτ n z hz, hτ n z' hz']
    rw [e, hκ, map_add (f := _), Tate.lev_add]
  have hp := fun n => weil_perfect (A := A) (one_le_ppow p n) (κ n) (hm n)
  choose s hs hu using hp
  have hc : ∀ n, s (n + 1) ^ p = s n := by
    intro n
    refine hu n _ ⟨?_, fun z hz => ?_⟩
    · rw [← pow_mul, ← pow_succ']; exact (hs (n + 1)).1
    · have hz' : z ^ p ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hz, one_pow]
      rw [← weil_level (one_le_ppow p n) (Fact.out : p.Prime).pos hz
        (by rw [← pow_succ]; exact (hs (n + 1)).1), ← pow_succ, (hs (n + 1)).2 z hz']
      have e : z = (p • τ n z).lev (n + 1) := by rw [lev_nsmul, Tate.lev_succ, hτ n z hz]
      conv_lhs => rw [e, hκ, map_nsmul, lev_nsmul, Tate.lev_succ]
  refine ⟨Tate.mk s fun n => ⟨(hs n).1, hc n⟩, fun t => Tate.ext fun n => ?_⟩
  rw [lev_weilT, Tate.lev_mk, (hs n).2 _ (t.lev_pow n), hκ]

theorem eq_zero_of_weilT
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (s : TateA A p) (hs : ∀ t, weilT A p t s = 0) : s = 0 := by
  refine Tate.ext fun n => ?_
  have hp := weil_perfect (A := A) (one_le_ppow p n) (fun _ => 1) (fun _ _ _ _ => (_root_.mul_one _).symm)
  refine hp.unique ⟨s.lev_pow n, fun z hz => ?_⟩ ⟨(0 : TateA A p).lev_pow n, fun z hz => ?_⟩
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, hs, Tate.lev_zero]
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, map_zero, Tate.lev_zero]

end GlobalTheory.HTLat.TatePerfect

namespace GlobalTheory.HTLat

theorem bijective_pairT_of_lev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) (ε : Eps p C), (∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x) → (∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s) → Function.Bijective (pairT A ε).flip ∧ Function.Bijective (pairT A ε) := by
  intro p _ C _ _ _ A ε h1 h2
  have hb : Function.Bijective (pairT A ε).flip := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun s hs => TatePerfect.eq_zero_of_weilT A h1 s fun t => ?_
      have : ε.equiv.symm (weilT A p t s) = 0 := LinearMap.congr_fun hs t
      exact ε.equiv.symm.map_eq_zero_iff.1 this
    · intro l
      obtain ⟨s, hs⟩ := TatePerfect.weilT_flip_surjective A h1 h2 (ε.equiv.toLinearMap ∘ₗ l)
      refine ⟨s, LinearMap.ext fun t => ?_⟩
      change ε.equiv.symm (weilT A p t s) = l t
      rw [hs]
      exact ε.equiv.symm_apply_apply _
  refine ⟨hb, ?_⟩
  have e : ⇑(pairT A ε) = Neg.neg ∘ ⇑(pairT A ε).flip := by
    funext s
    exact LinearMap.ext fun t => ((isAlt_pairT A ε).neg_eq t s).symm
  rw [e]
  exact (Equiv.neg _).bijective.comp hb

end GlobalTheory.HTLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassGradedTensorBundleFinsetSum
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem cls_LL_add (F : FlagMod.Frames Y π) (e e' : Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (e + e')) (F.isLB_LL _) =
      GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _) + GlobalTheory.CechPic.cls (F.LL e') (F.isLB_LL _) := by
  have h := GlobalTheory.CechPic.isLB_tens (F.isLB_LL e) (F.isLB_LL e')
  refine ((GlobalTheory.CechPic.cls_eq_iff (F.isLB_LL (e + e')) h).2 (GlobalTheory.CechPic.iso_of_chart h ⟨fun k => (k, k), fun _ _ h => ⟨h, h⟩, ?_⟩)).trans
    (GlobalTheory.CechPic.cls_tens _ _ h)
  intro y p q hp hq
  refine Eq.trans ?_ (GlobalTheory.CechPic.gm_tens (F.LL e) (F.LL e') (𝟙 Z) y (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).symm
  exact (congrArg (gm (𝟙 Z) y _) (F.LL_add_g e e' p q)).trans (map_mul _ _ _)

def clsLLHom (F : FlagMod.Frames Y π) : (Ix Dw → ℤ) →+ GlobalTheory.CechPic.Pic Z :=
  AddMonoidHom.mk' (fun e => GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _)) (cls_LL_add F)

theorem cls_LL_sum (F : FlagMod.Frames Y π) {ι : Type} (s : Finset ι) (e : ι → Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (∑ i ∈ s, e i)) (F.isLB_LL _) = ∑ i ∈ s, GlobalTheory.CechPic.cls (F.LL (e i)) (F.isLB_LL _) :=
  map_sum (clsLLHom F) e s

end GlobalTheory.FlagPlucker
end
end

