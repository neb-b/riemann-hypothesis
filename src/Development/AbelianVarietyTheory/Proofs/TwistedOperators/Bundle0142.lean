module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricCompact

theorem exists_compact_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ x : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) : _ →+* _) x ∈ St β → ∀ i j, x.1 i j ∈ C := by
  classical
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨-, C0, hC0, hC0m⟩ := GlobalTheory.Mass.intTens_open_compact F E
  let s := GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)

  let b : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := (β : Matrix (Fin n) (Fin n) _).map s.symm
  let c : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map s.symm

  let f : Fin n → Fin n → (Fin n → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
    fun i j a => ∑ l, (∑ k, b i k * a k l) * c l j
  have hf : ∀ i j, Continuous (f i j) := fun i j =>
    continuous_finsetSum _ fun l _ =>
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_apply l).comp (continuous_apply k))).mul continuous_const
  have hS : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC0
  refine ⟨⋃ i, ⋃ j, f i j '' Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hS.image (hf i j), ?_⟩
  intro x hx i j
  obtain ⟨y, hy⟩ := hx
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j,
    ⟨fun k l => s.symm ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l), ?_, ?_⟩⟩⟩
  · intro k _ l _
    apply hC0m
    change (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (s.symm _) ∈ Formalism.L2.Herm.intAf F E
    rw [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l).2
  · have hx' : (x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j =
        s.symm (((Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x :
          GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) i j) := by
      rw [Formalism.UG.P.bc_coe]
      simp
    have hy' : Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x =
        β * Formalism.L2.DIV.intGL F E n y * β⁻¹ := by
      rw [← hy]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', hy', Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Formalism.L2.DIV.intGL, Formalism.UG.P.bc_coe]
    rfl

variable {D : D7}

theorem isOpen_comap_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hκ
  obtain ⟨hU, hS, hR⟩ := hκ
  show finE V κ ∈ lev D.sp.cm V.gram β L
  refine Formalism.L2.DIV.Kg_le_lev (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right ?_
  simp only [Formalism.L2.DIV.Kg, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact ⟨⟨hU, hS⟩, fun PP hPP => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hR PP hPP⟩⟩

theorem exists_compact (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, k ∈ GfC V → finE V k ∈ St β → k ∈ C := by
  obtain ⟨C1, hC1, hC1m⟩ := exists_compact_entries (F := D.host.F) (E := D.host.E) β
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C1 hC1

  haveI : T2Space (InfiniteAdeleRing D.host.F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  haveI : T2Space (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    inferInstanceAs (T2Space (RestrictedProduct
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
      (fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))) Filter.cofinite))
  haveI : T2Space (AF D.host.F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  obtain ⟨K', hK', hK'm⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) K hK
  refine ⟨K', hK', fun k hk hst => hK'm k fun i j => hKm _ ?_ ?_⟩
  ·
    have hsw : (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _) = swapAE D :=
      RingHom.ext fun _ => rfl
    have hst' : Formalism.UG.bc (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _)
        (finHom V k) ∈ St β := by
      rw [hsw]
      exact hst
    have h := hC1m (finHom V k) hst' i j
    rw [finHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe] at h
    exact h
  ·
    intro ρ
    have h1 : infHom V k = 1 := hk
    have h2 : infPart D ((HA.mat (AF D.host.F) D.sp.cm.sig V.gram k : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
      have h3 := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        (g : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j) h1
      simp only [infHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe, Units.val_one] at h3
      exact h3
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, norm_one, le_refl]
    · simp only [Matrix.one_apply_ne hij, map_zero, norm_zero, zero_le_one]

theorem isCompact_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsCompact ((levG V β L : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  obtain ⟨C, hC, hCm⟩ := exists_compact V β
  refine hC.of_isClosed_subset ?_ ?_
  · rw [levG, levA, Subgroup.coe_inf]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter
      (Subgroup.isClosed_of_isOpen _ (isOpen_comap_lev V β L))
  · intro k hk
    rw [SetLike.mem_coe, levG, levA, Subgroup.mem_inf] at hk
    exact hCm k hk.1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2))

theorem isCompact_flag_and_lift : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  intro D V β L
  refine ⟨isCompact_levG V β (flagL L), fun g0 κ hκ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hκ
  rw [levG, levA, Subgroup.mem_inf]
  refine ⟨h1, ?_⟩
  show finE V κ ∈ lev D.sp.cm V.gram β (flagL L)
  rw [Formalism.L2.DIV.mem_lev]
  exact ⟨h2, Subgroup.mem_top _⟩

end GlobalTheory.ParahoricCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumFock

open GlobalTheory.SplitScalar

theorem exists_derivForm : ∃ l : (ℝ → ℂ) →ₗ[ℂ] ℂ, ∀ g, DifferentiableAt ℝ g 0 → l g = deriv g 0 := by
  let p : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {g | DifferentiableAt ℝ g 0}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := differentiableAt_const _
      smul_mem' := fun c _ hg => hg.const_smul c }
  let d : p →ₗ[ℂ] ℂ :=
    { toFun := fun g => deriv g.1 0
      map_add' := fun g h => deriv_add g.2 h.2
      map_smul' := fun c g => deriv_const_smul c g.2 }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend d
  exact ⟨l, fun g hg => LinearMap.congr_fun hl ⟨g, hg⟩⟩

variable {D : D7}

def alongLine (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ → WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun g := fun x => l fun t => heisO ψ S T (L t) g x
  map_add' g g' := by
    funext x
    rw [Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_add g g') x
  map_smul' c g := by
    funext x
    rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_smul c g) x

theorem alongLine_heisO (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {L : ℝ → WO S T}
    (hL : ∀ t, (L t).map (finPart D) = 0) {u : WO S T} (hu : u.map (infPart D) = 0) (g : WO S T → ℂ) :
    alongLine l ψ S T L (heisO ψ S T u g) = heisO ψ S T u (alongLine l ψ S T L g) := by
  funext x
  have hc : ∀ t, heisO ψ S T (L t) (heisO ψ S T u g) = heisO ψ S T u (heisO ψ S T (L t) g) := by
    intro t
    rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_real_fin S T (hL t) hu, AddChar.map_zero_eq_one,
      one_smul]
  have key : ∀ h : WO S T → ℂ, heisO ψ S T u h x = ψ (symplOH S T x u) * h (x + u) := fun _ => rfl
  simp only [alongLine, LinearMap.coe_mk, AddHom.coe_mk, hc, key]
  exact l.map_smul (ψ (symplOH S T x u)) (fun t => heisO ψ S T (L t) g (x + u))

private lemma differentiable_of_continuous_additive_char {φ : ℝ → ℂ} (hφ : Continuous φ) (h0 : φ 0 = 1)
    (hmul : ∀ s t, φ (s + t) = φ s * φ t) : Differentiable ℝ φ := by
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, φ x with hFdef
  have hF : ∀ b, HasDerivAt F (φ b) b := fun b => (hφ.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    by_contra hcon
    have hz : F = fun _ => (0:ℂ) := funext fun δ => by
      by_contra h
      exact hcon ⟨δ, h⟩
    have h1 := hF 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  have key : ∀ t, φ t = (F (δ + t) - F t) * (F δ)⁻¹ := by
    intro t
    have h1 : ∫ x in (0:ℝ)..δ, φ (x + t) = F (δ + t) - F t := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, hFdef]
      exact (intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (0:ℝ)..δ, φ (x + t) = F δ * φ t := by
      simp_rw [hmul]
      exact intervalIntegral.integral_mul_const _ _
    rw [← h1, h2, mul_comm (F δ) (φ t), mul_assoc, mul_inv_cancel₀ hδ, mul_one]
  intro t
  have hd : DifferentiableAt ℝ (fun t => (F (δ + t) - F t) * (F δ)⁻¹) t :=
    ((((hF (δ + t)).differentiableAt).comp t (differentiableAt_id.const_add δ)).sub
      (hF t).differentiableAt).mul_const _
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

theorem exists_annihLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      (∀ u : WO S T, u.map (infPart D) = 0 → ∀ g, A (heisO ψ S T u g) = heisO ψ S T u (A g)) ∧
      ∀ g, IsThetaFunO ψ S T g → A g = annih (heisO ψ S T) θ τ J z g := by
  obtain ⟨l, hl⟩ := exists_derivForm
  have hex := GlobalTheory.RealLineAt.lineAt_exists D
  unfold LineAtExists at hex
  have hspec : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, IsLineAt θ τ w (lineAt θ τ w) := by
    intro w
    obtain ⟨L, hL⟩ := hex θ hθ T.rank S.rank τ w
    exact Classical.epsilon_spec ⟨L, hL⟩
  have hfin : ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), (lineAt θ τ w t).map (finPart D) = 0 := by
    intro w t
    have h := hspec w
    unfold IsLineAt at h
    exact h.2.1 t
  have hcont : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, Continuous (lineAt θ τ w) := by
    intro w
    have h := hspec w
    unfold IsLineAt at h
    exact h.1
  have hdiff : ∀ g, IsThetaFunO ψ S T g → ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : WO S T),
      DifferentiableAt ℝ (fun t => heisO ψ S T (lineAt θ τ w t) g x) 0 := by
    intro g hg w x
    obtain ⟨-, -, -, hsm⟩ := hg
    have hgL : DifferentiableAt ℝ (fun t => g (x + lineAt θ τ w t)) 0 := by
      let L1 : (Fin 1 → ℝ) →+ WO S T := (lineAt θ τ w).comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
      have h1 := hsm 1 L1 ((hcont w).comp (continuous_apply 0)) (fun t => hfin w (t 0)) x
      have h2 : (fun t : ℝ => g (x + lineAt θ τ w t)) =
          (fun t : Fin 1 → ℝ => g (x + L1 t)) ∘ (fun t : ℝ => fun _ : Fin 1 => t) := rfl
      rw [h2]
      exact ((h1.differentiable (by simp)) _).comp _ (differentiableAt_pi.2 fun _ => differentiableAt_id)
    have hφ : Differentiable ℝ (fun t => ψ (symplOH S T x (lineAt θ τ w t))) := by
      apply differentiable_of_continuous_additive_char
      · have hc : (fun t => symplOH S T x (lineAt θ τ w t)) =
            fun t => algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x (lineAt θ τ w t) := rfl
        exact hψ.comp (hc ▸ continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const (hcont w)))
      · rw [map_zero]
        show ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x 0) = 1
        rw [GlobalTheory.SplitScalar.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
      · intro s t
        rw [map_add (f := _), GlobalTheory.SplitScalar.symplOH_add_right, AddChar.map_add_eq_mul]
    exact (hφ 0).mul hgL
  refine ⟨alongLine l ψ S T (lineAt θ τ z) + Complex.I • alongLine l ψ S T (lineAt θ τ (J z)), ?_, ?_⟩
  · intro u hu g
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [alongLine_heisO l ψ S T (hfin z) hu, alongLine_heisO l ψ S T (hfin (J z)) hu]
    funext x
    unfold heisO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro g hg
    funext x
    unfold annih Datum.dRho
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, alongLine,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [hl _ (hdiff g hg z x), hl _ (hdiff g hg (J z) x)]

theorem infPart_of_isHalf {S T : HSp D} {e : AE D} (he : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, he, zero_mul]

theorem isFockVacAt_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} {e : AE D} (he : infPart D e = 0) (he' : infPart D (cA D e) = 0) {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) (hf : IsThetaFunO ψ S T f) {τ : D.what₂.Tau}
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hv : IsFockVacAt (heisO ψ S T) θ τ J f₀) : IsFockVacAt (heisO ψ S T) θ τ J f := by
  unfold IsThetaAt AllSome at h
  obtain ⟨⟨Tm, hTm⟩, hU⟩ := h
  unfold IsFockVacAt at hv ⊢
  intro z
  obtain ⟨A, hA, hAθ⟩ := exists_annihLin hψ hθ S T τ J z
  have hadd : ∀ (w : WO S T) (g g' : WO S T → ℂ),
      heisO ψ S T w (g + g') = heisO ψ S T w g + heisO ψ S T w g' :=
    fun _ _ _ => funext fun _ => mul_add _ _ _
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) := by
    obtain ⟨htr, hmod, hvac⟩ := hTm
    refine ⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [htr Φ' hΦ x hx, hA x (infPart_of_isHalf he hx), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hmod Φ' hΦ y hy, hA y (infPart_of_isHalf he' hy), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hvac, hAθ f₀ h₀, hv z, add_zero]
  have e1 : f = Tm Φ := hU Tm hTm
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hU _ hTm'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  rw [← hAθ f hf]
  simpa using e2

theorem isFockVacAt_thPVec : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ (f₀ f : WO S T → ℂ), IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f → IsThetaFunO ψ S T f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f h hf τ
  obtain ⟨hv, e, he, ht⟩ := h
  unfold IsVacO IsStdChar at hv
  obtain ⟨hs, ⟨hθ, h₀, -, hfock, -⟩⟩ := hv
  have hψ : Continuous ψ := by
    have h1 := hs.1
    unfold IsCharAF at h1
    exact h1.1
  have ho : GlobalTheory.PlaceModelSum.IsOrthSum e := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  exact isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq ht h₀ hf (hfock τ)

end GlobalTheory.DatumFock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section Rat

variable {T L : Type} [Field L] (σ : L →+* ℂ) (t₀ : T)

def RatIn (f : T → ℂ) : Prop := ∀ t, f t ≠ 0 ∧ ∃ y : Lˣ, σ y = f t / f t₀

variable {σ t₀}

theorem RatIn.mul {f g : T → ℂ} (hf : RatIn σ t₀ f) (hg : RatIn σ t₀ g) : RatIn σ t₀ fun t => f t * g t := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  obtain ⟨hg0, z, hz⟩ := hg t
  refine ⟨mul_ne_zero hf0 hg0, y * z, ?_⟩
  rw [Units.val_mul, map_mul, hy, hz, mul_div_mul_comm]

theorem RatIn.inv {f : T → ℂ} (hf : RatIn σ t₀ f) : RatIn σ t₀ fun t => (f t)⁻¹ := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  refine ⟨inv_ne_zero hf0, y⁻¹, ?_⟩
  rw [map_units_inv, hy, inv_div, inv_div_inv]

theorem ratIn_const {κ : ℂ} (h : κ ≠ 0) : RatIn σ t₀ fun _ => κ := by
  intro _
  exact ⟨h, 1, by rw [Units.val_one, map_one, div_self h]⟩

theorem ratIn_of_unit {f : T → ℂ} (h : ∀ t, ∃ y : Lˣ, σ y = f t) : RatIn σ t₀ f := by
  intro t
  obtain ⟨y, hy⟩ := h t
  obtain ⟨y₀, hy₀⟩ := h t₀
  refine ⟨hy ▸ (map_ne_zero σ).2 y.ne_zero, y * y₀⁻¹, ?_⟩
  rw [Units.val_mul, map_mul, map_units_inv, hy, hy₀, div_eq_mul_inv]

theorem RatIn.of_mul {f g u : T → ℂ} (hg : RatIn σ t₀ g) (hu : RatIn σ t₀ u) (h : ∀ t, f t * u t = g t) : RatIn σ t₀ f := by

  have e : f = fun t => g t * (u t)⁻¹ := funext fun t => by rw [← h t, mul_inv_cancel_right₀ (hu t).1]
  rw [e]
  exact hg.mul hu.inv

end Rat

variable {D : D7}

section Factor

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def Factor (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧
    ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
      (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
      Function.Surjective p ∧ (∀ t, Function.Injective (J t)) ∧
      (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧
      (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
      (∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I' ψ θ t P' = J t (p' P')) ∧
      ∃ P', p' P' ≠ 0 ∧ ∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m'

variable {X ψ θ}

theorem Factor.isConst [Nonempty T] {lam : T → ℂ} (h : Factor X ψ θ lam) : X.IsConst ψ θ lam := by
  unfold Factor at h
  obtain ⟨hlam, Pi, p, p', J, hp, hJ, hint, hI, hI', P', hP', hint'⟩ := h

  obtain ⟨P, hPP⟩ := hp (p' P')
  unfold Tri.IsConst
  refine ⟨⟨Classical.arbitrary T, hlam _⟩, P, P', fun t => ⟨fun h => ⟨hint t P h, hint' t h⟩, ?_, fun h => ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    apply hP'
    apply hJ t
    rw [map_zero, ← hI' t P' (hint' t)]
    funext h
    exact hcon h
  · rw [hI t P, hI' t P' (hint' t), hPP]
    rfl

theorem Factor.eq_mul {lam c : T → ℂ} (h : Factor X ψ θ lam) (hc : X.IsConst ψ θ c) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ t, c t = κ * lam t := by
  unfold Factor at h
  unfold Tri.IsConst at hc
  obtain ⟨hlam, Pi, p, p', J, -, hJ, -, hI, hI', -⟩ := h
  obtain ⟨⟨t₁, ht₁⟩, P, P', hc⟩ := hc

  have key : ∀ t, lam t • p P = c t • p' P' := by
    intro t
    obtain ⟨hi, -, heq⟩ := hc t
    apply hJ t
    rw [map_smul, map_smul, ← hI t P, ← hI' t P' (fun h => (hi h).2)]
    funext h
    exact heq h
  have hne : p' P' ≠ 0 := by
    intro h0
    obtain ⟨hi, ⟨h₁, hh₁⟩, -⟩ := hc t₁
    apply hh₁
    rw [hI' t₁ P' (fun h => (hi h).2), h0, map_zero]
    rfl
  have hq : ∀ t, p P = ((lam t)⁻¹ * c t) • p' P' := by
    intro t
    rw [← smul_smul, ← key t, inv_smul_smul₀ (hlam t)]
  refine ⟨(lam t₁)⁻¹ * c t₁, mul_ne_zero (inv_ne_zero (hlam t₁)) ht₁, fun t => ?_⟩
  have e := smul_left_injective ℂ hne ((hq t).symm.trans (hq t₁))
  rw [← e]
  field_simp [hlam t]

end Factor

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks}

def NegIdx (V : HSp D) (q : ℕ) : Prop := ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) (V.rank - q) q

end GlobalTheory.ConstRatio

end
end

