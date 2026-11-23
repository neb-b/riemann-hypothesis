module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolyBallOfCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_GL_norm_one_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∃ e : GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a) × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  first | exact @GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | exact GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | (intros; apply GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMinorHeightBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1 → ∀ f e : Fin n → ι,
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | exact GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | (intros; apply GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesClosedCell
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocC

open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl GlobalTheory.CompanionTheory.MirFourier ValuativeRel

attribute [local instance] instMSpi instBSpi

section Final

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

abbrev thL (ψ : AddChar k Circle) (s : kˣ) : Lball k i t s →* ℂˣ :=
  (mirChar k ψ ((i + 1) + t)).comp (Subgroup.inclusion (Lball_le s))

theorem thL_uEl (ψ : AddChar k Circle) (s : kˣ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k)
    (h : uEl k i t c d ∈ Lball k i t s) :
    thL ψ s ⟨uEl k i t c d, h⟩ = Circle.toUnits (ψ (d (Fin.last t))) :=
  mirChar_uEl ψ i t c d (Lball_le s h)

theorem isOpen_ker_thL (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) :
    IsOpen ((thL (i := i) (t := t) ψ s).ker : Set (Lball k i t s)) :=
  (GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirChar_ker_open ψ hψ ((i + 1) + t)).preimage
    (show Continuous (Subgroup.inclusion (Lball_le (i := i) (t := t) s)) from continuous_subtype_val.subtype_mk _)

theorem iF_sub (ψ : AddChar k Circle) (hψ : Continuous ψ) (a b : XS τ σ) : iF ψ (a - b) = iF ψ a - iF ψ b :=
  (iL ψ hψ).map_sub a b

theorem iF_zero (ψ : AddChar k Circle) (hψ : Continuous ψ) : iF ψ (0 : XS τ σ) = 0 :=
  (iL ψ hψ).map_zero

theorem gen (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (v : XS τ σ) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d) v - ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • v) =
      ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • (rU τ σ (Multiplicative.ofAdd c) (iF ψ v) - iF ψ v) := by
  have a1 := iF_smul ψ hψ ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) v
  have a2 := iF_translate ψ hψ v c d
  exact (iF_sub ψ hψ _ _).trans ((congrArg₂ (fun a b => a - b) a2 a1).trans (smul_sub _ _ _).symm)

theorem thL_eq (ψ : AddChar k Circle) (s : kˣ) (l : Mir k ((i + 1) + t + 1)) (hl : l ∈ Lball k i t s)
    (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (e : l = uEl k i t c d) :
    thL ψ s ⟨l, hl⟩ = Circle.toUnits (ψ (d (Fin.last t))) := by
  subst e
  exact thL_uEl ψ s c d hl

theorem mem_of_eq {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V) {z y : V} (h : z = y) (hy : y ∈ K) : z ∈ K :=
  h ▸ hy

theorem gen_mem (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) (l : Mir k ((i + 1) + (t + 1))) (hl : l ∈ Lball k i t s)
    (v : XS τ σ) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) l v - ((thL ψ s ⟨l, hl⟩ : ℂˣ) : ℂ) • v) ∈
      twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  have h := exists_of_mem_Lball hl
  refine Exists.elim h fun c h => Exists.elim h fun d h => ?_
  have hc := h.1
  have e := h.2.2
  have e1 : cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) l v = cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d) v :=
    congrArg (fun x => cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) x v) e
  have e2 : ((thL ψ s ⟨l, hl⟩ : ℂˣ) : ℂ) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) :=
    congrArg _ (thL_eq ψ s l hl c d e)
  have e3 := congrArg₂ (fun (a : XS τ σ) (b : ℂ) => iF ψ (a - b • v)) e1 e2
  refine mem_of_eq _ (e3.trans (gen ψ hψ c d v)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hc⟩, iF ψ v, ?_⟩))
  simp

theorem iF_twKer (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) (v : XS τ σ)
    (hv : v ∈ twKer (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (Lball k i t s) (thL ψ s)) :
    iF ψ v ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine Exists.elim hx fun l h => Exists.elim h fun v h => ?_
    exact mem_of_eq _ (congrArg (iF ψ) h) (gen_mem ψ hψ s l.1 l.2 v)
  | zero => exact mem_of_eq _ (iF_zero ψ hψ) (zero_mem _)
  | add x y _ _ hx hy => exact mem_of_eq _ (iF_add ψ hψ x y) (add_mem hx hy)
  | smul c x _ hx => exact mem_of_eq _ (iF_smul ψ hψ c x) (Submodule.smul_mem _ _ hx)

theorem eig_eval (ψ : AddChar k Circle) (s : kˣ) (g : XS τ σ)
    (g2 : ∀ l : Lball k i t s, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (l : Mir k ((i + 1) + t + 1)) g = ((thL ψ s l : ℂˣ) : ℂ) • g)
    (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (hc : Multiplicative.ofAdd c ∈ polyBall (i + 1) s)
    (hd : Multiplicative.ofAdd d ∈ polyBall (t + 1) s) (x : Mir k ((i + 1) + t + 1)) :
    evX g (x * uEl k i t c d) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • evX g x := by
  have hm := uEl_mem_Lball hc hd
  have e := congrArg (fun w : XS τ σ => evX w x) (g2 ⟨_, hm⟩)
  have e2 : ((thL ψ s ⟨_, hm⟩ : ℂˣ) : ℂ) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) :=
    congrArg _ (thL_uEl ψ s c d hm)
  exact (evX_cInd g _ x).symm.trans (e.trans ((evX_smul _ g x).trans (congrArg (fun b : ℂ => b • evX g x) e2)))

theorem supp_of (s : kˣ) (f : XS τ σ)
    (hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (l : Mir k ((i + 1) + t + 1)) (hl : l ∈ Lball k i t s) (d : Fin (t + 1) → k)
    (hne : evX f (dEmb k i t d * 1 * l) ≠ 0) : Multiplicative.ofAdd d ∈ polyBall (t + 1) s := by
  obtain ⟨c, d₁, hc, hd₁, rfl⟩ := exists_of_mem_Lball hl
  rw [dEmb_mul_uEl, evX_left] at hne
  have h3 : evX f (dEmb k i t (d + d₁) * 1) ≠ 0 := by
    intro h0
    exact hne (by rw [h0, map_zero])
  have h4 := (polyBall (t + 1) s).mul_mem (hF _ h3) ((polyBall (t + 1) s).inv_mem hd₁)
  have e : Multiplicative.ofAdd (d + d₁) * (Multiplicative.ofAdd d₁)⁻¹ = Multiplicative.ofAdd d := by
    rw [ofAdd_add, mul_inv_cancel_right]
  rwa [e] at h4

theorem avgVanish_of_data (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (s : kˣ) (hz : iF ψ f ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1)
    (hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (g : XS τ σ) (g1 : f - g ∈ twKer (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (Lball k i t s) (thL ψ s))
    (g2 : ∀ l : Lball k i t s, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (l : Mir k ((i + 1) + t + 1)) g = ((thL ψ s l : ℂˣ) : ℂ) • g)
    (g3 : ∀ x : Mir k ((i + 1) + t + 1), evX g x ≠ 0 → ∃ l ∈ Lball k i t s, evX f (x * l) ≠ 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f 1 := by
  have hsupp : ∀ d : Fin (t + 1) → k, evX g (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s := by
    intro d hd
    refine Exists.elim (g3 _ hd) fun l h => ?_
    exact supp_of s f hF l h.1 d h.2
  have hk : iF ψ g ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
    have h5 := iF_twKer ψ hψ s (f - g) g1
    have e : iF ψ g = iF ψ f - iF ψ (f - g) := by
      have := iF_sub ψ hψ f g
      rw [this, sub_sub_cancel]
    exact mem_of_eq _ e (sub_mem hz h5)
  refine ⟨Lball k i t s, Lball_le s, isCompact_Lball s, g, g1, g2, fun u hu => ?_⟩
  refine Exists.elim (exists_uEl i t u hu) fun c h => Exists.elim h fun d e => ?_
  have h7 := vanish_of_eigen ψ hτ hσ s g (eig_eval ψ s g g2) hsupp hk c d
  have e2 : (1 : Mir k ((i + 1) + t + 1)) * u = uEl k i t c d := by rw [one_mul, e]
  exact (congrArg (evX g) e2).trans h7

theorem avgVanish_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (hq : qC τ σ (iF ψ f) = 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f 1 := by
  obtain ⟨s₁, h₁⟩ := exists_polyBall_of_qC _ hq
  obtain ⟨s₂, h₂⟩ := exists_polyBall_of_compact
    (GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f 1).2
  obtain ⟨s, a, b⟩ := exists_val_ge s₁ s₂
  have hz : iF ψ f ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := twKer_one_mono _ (polyBall_mono _ a) h₁
  have hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s :=
    fun d hd => polyBall_mono _ b (h₂ d (subset_tsupport _ hd))
  have hg := exists_avg (HPG k (i + 1) (t + 1)) (sigX τ σ) (Lball k i t s) (isCompact_Lball s)
    (thL ψ s) (isOpen_ker_thL ψ hψ s) f
  exact Exists.elim hg fun g h => avgVanish_of_data ψ hψ hτ hσ f s hz hF g h.1 h.2.1 h.2.2

theorem mirChar_sEmb_conj (ψ : AddChar k Circle) {n : ℕ} (m : Mir k n) (u : MirUin k (n + 1))
    (h : (sEmb k n m)⁻¹ * (u : Mir k (n + 1)) * sEmb k n m ∈ MirUin k (n + 1)) :
    mirChar k ψ n ⟨_, h⟩ = mirChar k ψ n u := by
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
  rw [mirChar_eq k ψ n u w hw.symm]
  let mi : GL (Fin (n + 1)) k := ((m⁻¹ : Mir k n) : GL (Fin (n + 1)) k)
  have e0 : (((sEmb k n m)⁻¹ : Mir k (n + 1)) : GL (Fin (n + 2)) k) = glEmb k (n + 1) mi := by
    rw [← map_inv]
    rfl
  have e1 : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 2)) k) = (glEmb k (n + 1) mi)⁻¹ := by
    rw [← e0]
    simp
  have e : (((sEmb k n m)⁻¹ * (u : Mir k (n + 1)) * sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd ((mi : Matrix _ _ k).mulVec w.toAdd)) := by
    simp only [Subgroup.coe_mul]
    rw [e0, e1, ← hw, glEmb_mul_unip', mul_inv_cancel_right]
  rw [mirChar_eq k ψ n ⟨_, h⟩ _ e, toAdd_ofAdd,
    mulVec_last_of_mem k mi (m⁻¹ : Mir k n).2 w.toAdd]

theorem avgVanish_cell (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (h0 : eC ψ f = 0) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f
      (h * dEmb k i t d * sEmb k ((i + 1) + t) m) := by
  have hq : qC τ σ (intC ψ f (sEmb k _ m)) = 0 := by
    have h1 : ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m)) = 0 := congrFun h0 m
    exact (smul_eq_zero.1 h1).resolve_left (Units.ne_zero _)
  have hp : phi ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f) =
      fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * sEmb k _ m) := by
    funext d
    simp only [phi]
    rw [evX_cInd, mul_one]
    rfl
  have hi : iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f) = intC ψ f (sEmb k _ m) :=
    congrArg (GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1))) hp
  have A1 := avgVanish_one ψ hψ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f)
    ((congrArg (qC τ σ) hi).trans hq)
  have hU : ∀ u ∈ MirUin k ((i + 1) + t + 1), sEmb k _ m * u * (sEmb k _ m)⁻¹ ∈ MirUin k ((i + 1) + t + 1) :=
    fun u hu => GlobalTheory.CompanionTheory.BZMirSeq.conj_mem_MirUin _ ⟨u, hu⟩
  have hU' : ∀ u ∈ MirUin k ((i + 1) + t + 1), (sEmb k _ m)⁻¹ * u * sEmb k _ m ∈ MirUin k ((i + 1) + t + 1) := by
    intro u hu
    have := GlobalTheory.CompanionTheory.BZMirSeq.conj_mem_MirUin (sEmb k _ m)⁻¹ ⟨u, hu⟩
    rwa [inv_inv] at this
  have A2 := avgVanish_conj _ _ _ _ (sEmb k _ m) hU hU' (fun u h => mirChar_sEmb_conj ψ m u h) f A1
  exact avgVanish_left _ _ _ _ f _ _ h hh (hU' _ (uEl_mem i t 0 d)) A2

end Final

theorem avgVanish_of_mem_Cl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eC ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∈ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  intro k _ _ _ _ i t ψ hψ τ σ hτ hσ f h0 p hp
  refine Exists.elim ((GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells k i t).1 p hp) fun h hh =>
    Exists.elim hh.2 fun d hd => Exists.elim hd fun m e => ?_
  exact (congrArg (AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f) e).mpr
    (avgVanish_cell ψ hψ hτ hσ f h0 h hh.1 d m)

end GlobalTheory.CompanionTheory.BZPhiPG.LocC

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCellStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_vanishes_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eO ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∉ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | exact GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.LocO.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

def CovAt {D : D7} {n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {θ : InfFam D}
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (γ : G D n) : Prop :=
  ∀ (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n), Ψ.1 = EC.Heisenberg₂ ψ V v Φ.1 →
    (ω γ Ψ).1 = EC.Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1

def FieldGen (K : Type) [Field K] (σ : K →+* K) (n : ℕ) : Prop :=
  ∀ T : Matrix (Fin (n + n)) (Fin (n + n)) K → Prop, (∀ g h, T g → T h → T (g * h)) →
    (∀ a : Matrix (Fin n) (Fin n) K, IsUnit a.det → T (mA σ a)) →
    (∀ b : Matrix (Fin n) (Fin n) K, cT σ b = b → T (nB b)) → T (Jm K n) →
    ∀ g, IsUnit g.det → IsUnitary σ (Jm K n) g → T g

variable {D : D7} {n : ℕ}

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := by
  unfold mat; rw [map_mul]; rfl

theorem mat_one' : mat (1 : G D n) = 1 := by
  unfold mat; rw [map_one]; rfl

theorem mat_inv_mul' (g : G D n) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem mat_mul_inv' (g : G D n) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, mat_one']

theorem mat_injective' : Function.Injective (mat : G D n → Mx D (n + n) (n + n)) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem x_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    xPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) A + HMul.hMul (yPart v) C := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]

theorem y_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    yPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) B + HMul.hMul (yPart v) E := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' = blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem covAt_mul {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {θ : InfFam D}
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {γ₁ γ₂ : G D n}
    (h₁ : CovAt ψ V ω γ₁) (h₂ : CovAt ψ V ω γ₂) : CovAt ψ V ω (γ₁ * γ₂) := by
  intro v Φ Ψ hΨ
  have e1 := h₁ _ (ω γ₂ Φ) (ω γ₂ Ψ) (h₂ v Φ Ψ hΨ)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, mul_inv_rev, mat_mul', Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.EisCovar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Finset

theorem mem_subalgebra_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem cas_mem_of_qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ)
    (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E)
    (hcap : ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) ∈ S) : Formalism.REAL.Cas E ∈ S := by
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Formalism.REAL.Cas]
    · have h0 := hcap 0
      rw [hR] at h0
      have h1 : E 0 0 ∈ S := by
        simpa [Finset.filter_singleton] using h0
      have : Formalism.REAL.Cas E = E 0 0 * E 0 0 := by simp [Formalism.REAL.Cas]
      rw [this]
      exact Subalgebra.mul_mem _ h1 h1
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) =>
    scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i))
      (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := hf _ (hcap Y)
        rw [hR] at h1
        have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1
        simp only [e, mul_zero] at h1 ⊢
        exact h1)
  have hT : ∑ i, E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have := (core f hf).1
    rw [hρ0, e] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    linear_combination this
  have hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have h2 := (core f hf).2
    rw [e] at h2
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub f, map_sum, map_smul, smul_eq_mul]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i)
        = - (2 * ∑ i, (0 - ρ i) * f (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h5]
    simp only [map_sub f] at h2
    linear_combination h2
  have h3 := sq_sub_cas E hE
  have : Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i)
      - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i) := by
    rw [← h3]; abel
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW

theorem cas_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro F _ _ _ n τ
  have hcap : ∀ Y : ℂ, cap (a := n) τ Y ∈ Zalg F n := fun Y =>
    Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)
  exact cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap

end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterEnvelopingCommutesLie
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem Zalg_comm_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z :=
  GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteAdelicDenominatorStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finite_adelic_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Set (Af F ⊗[F] E)), IsCompact L → ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ L → IsIntegral ℤ ((d : E) * e) := by
  first | exact @GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact | exact GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact <;> assumption)
end

