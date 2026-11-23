module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealLineBlockEmbeddingExpInfinitePlace
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AutomorphicFunctionRestrictBlock
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.CoreGL.CapScalar

def linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun Z := ∑ a, ∑ b, Z a b • E a b
  map_add' Z W := by simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem linOf_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin n) :
    linOf E (Matrix.single a b 1) = E a b := by
  classical
  change ∑ i, ∑ j, (Matrix.single a b (1 : ℂ)) i j • E i j = E a b
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
  · simp
  · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [Matrix.single_apply, Ne.symm hi]
  · simp

theorem glRel_linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M) :
    Formalism.REAL.GlRel fun i j => linOf E (M i j) := by
  have h : Formalism.REAL.GlRel (fun i j => linOf E (Matrix.single i j 1)) := by
    simpa only [linOf_single] using hE
  intro a b c d
  simp only
  rw [GlobalTheory.CapelliLowest.lie_of_glRel (linOf E) h, hM a b c d, map_sub, apply_ite (linOf E), apply_ite (linOf E), map_zero]

theorem qdet_commute {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M)
    (hs : Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) = ⊤) (v : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    linOf E Z * Formalism.REAL.qdet (fun i j => linOf E (M i j)) v = Formalism.REAL.qdet (fun i j => linOf E (M i j)) v * linOf E Z := by
  have hZ : Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) := hs ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact (Formalism.REAL.qDetCentral A n _ (glRel_linOf hE hM) v p.1 p.2).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), add_mul, mul_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

end GlobalTheory.CompanionTheory.CoreGL.CapScalar

namespace GlobalTheory.CompanionTheory.CoreGL

open GlobalTheory.CompanionTheory.CoreGL.CapScalar GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

attribute [local instance 100] LieRing.ofAssociativeRing

theorem qdet_scalar_of_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Submodule.span ℂ (Set.range fun p : Fin V.rank × Fin V.rank => M p.1 p.2) = ⊤ → ∀ (c : ℕ → ℂ) (v : ℂ), ∃ s : ℂ,
      ∀ f : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ k, gelf θ V τ k f.1 = c k • f.1) →
        Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v f = s • f := by
  intro D θ hθ V τ M hM hsp c v
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  obtain ⟨P, Q, hPQ, h⟩ := _root_.GlobalTheory.UnitaryLieComplexification.glRel_and_span _ _ (R.1 τ).1 (R.1 τ).2
  obtain ⟨h1, h2⟩ := h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add (f := _)])
    (fun c X => by
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])
  set E : Fin V.rank → Fin V.rank → EnvAt V τ := fun a b =>
    UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] P a b) + Complex.I • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Q a b) with hEdef

  have hcomm := qdet_commute h1 hM hsp v
  set z : EnvAt V τ := Formalism.REAL.qdet (fun i j => linOf E (M i j)) v with hz
  have hι : ∀ X : LieAt V τ, UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * z = z * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
    intro X
    have hX := h2 X
    generalize UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) = y at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      have := hcomm (Matrix.single p.1 p.2 1)
      rwa [linOf_single] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨cg, hc, hg⟩ := exists_gelf R τ
  have hcen : z ∈ Subalgebra.center ℂ (EnvAt V τ) := by
    rw [Subalgebra.mem_center_iff]
    intro u
    have : u ∈ Subalgebra.centralizer ℂ ({z} : Set (EnvAt V τ)) := by
      obtain ⟨w, rfl⟩ := _root_.GlobalTheory.EnvWords.envOf_surjective D V τ u
      refine Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (hι X).symm
    rw [Subalgebra.mem_centralizer_iff] at this
    exact (this z rfl).symm

  have key : ∀ y ∈ Algebra.adjoin ℂ (Set.range cg), ∃ s : ℂ, ∀ ψ : SmF θ V,
      (∀ k, gelf θ V τ k ψ.1 = c k • ψ.1) → envRep R τ y ψ = s • ψ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨c k, fun ψ e => Subtype.ext ((hg k ψ).symm.trans (e k))⟩
    | algebraMap r => exact ⟨r, fun ψ _ => by rw [AlgHom.commutes]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, fun ψ e => by rw [map_add (f := _), LinearMap.add_apply, hs ψ e, ht ψ e, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s * t, fun ψ e => by
        rw [map_mul, Module.End.mul_apply, ht ψ e, map_smul, hs ψ e, smul_smul, mul_comm]⟩
  rw [hc] at hcen
  obtain ⟨s, hs⟩ := key z hcen

  have e : GlobalTheory.Mem.AutSpace.SmFun θ V = SmF θ V := Submodule.ext fun φ => smooth_iff R φ
  let T := (LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ
  have k0 : ∀ a b, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1)) = envRep R τ (E a b) := by
    intro a b
    rw [hEdef]
    simp only [map_add (f := _), map_smul, envRep_ι]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change RderC θ V τ (Matrix.single a b 1) φ.1 = _
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl
  have k1 : ∀ Z, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ Z) = envRep R τ (linOf E Z) := by
    intro Z
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    change _ = envRep R τ (∑ a, ∑ b, Z a b • E a b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, k0]
  have k2 : T (Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v) = envRep R τ z := by
    have a1 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet T.toAlgHom (fun i j => GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (M i j)) v
    have a2 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet (envRep R τ) (fun i j => linOf E (M i j)) v
    change T _ = _ at a1
    rw [a1, hz, a2]
    congr 1
    funext i j
    exact k1 (M i j)
  refine ⟨s, fun f hf => ?_⟩
  have k3 := congrArg (fun S : Module.End ℂ (SmF θ V) => (S (LinearEquiv.ofEq _ _ e f)).1) k2
  have k4 := hs (LinearEquiv.ofEq _ _ e f) hf
  exact Subtype.ext (k3.trans (congrArg Subtype.val k4))

end GlobalTheory.CompanionTheory.CoreGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockEmbeddingAdaptedBasis
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.CuspSmooth

theorem mem_Sm_blockEmb_smFun : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ F : GlobalTheory.Mem.AutSpace.SmFun θ V, (fun x => F.1 (ι x)) ∈ GlobalTheory.CuspRep.Sm D.host.E d := by
  intro D _ θ hθ V m Xf Yf hW l d h ι hι F g
  classical
  obtain ⟨hcm, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  refine _root_.GlobalTheory.SecondKind.contDiffOn_of_prodExp D.host.E d _ {X | ∃ v, ∀ i j, ∀ u, u ≠ v → X i j u = 0} ?_ ?_
  · rw [eq_top_iff]
    intro X _
    have e : X = ∑ v : InfinitePlace D.host.E, (Matrix.of fun i j => Pi.single v (X i j v)) := by
      ext i j u
      rw [Matrix.sum_apply, Finset.sum_apply]
      simp [Pi.single_apply]
    rw [e]
    exact Submodule.sum_mem _ fun v _ => Submodule.subset_span ⟨v, fun i j u hu => by simp [hu]⟩
  · intro k X hX y hy
    choose v hv using hX
    have hγ : ∀ i, IsRealLine D.sp.cm.sig V.gram (fun t : ℝ => ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t • X i)))) :=
      fun i => GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp D.host.F D.host.E D.sp.cm.sig hcm _ V.gram (hJ V) m Xf Yf hW l d h ι hι (v i) (X i) (hv i)
    choose p hp e using fun i => (hγ i).eq_oneP hθ
    have hs := F.2 k (fun i => (p i).1) (fun i => (p i).2) hp (ι (g * GlobalTheory.CuspRep.infGL D.host.E d hy.unit))
    simp only [← e] at hs
    convert hs using 2 with t
    set P : GL (Fin d) (GlobalTheory.CuspRep.Cinf D.host.E) := (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).prod
    have hP : (P : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf D.host.E)) =
        (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod := by
      simp only [P]
      rw [← Units.coeHom_apply, map_list_prod, List.map_ofFn]
      rfl
    have hU : GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) =
        GlobalTheory.CuspRep.toL (hy.unit * P).val := by
      rw [Units.val_mul, hP]
      congr 2
    rw [hU, GlobalTheory.CuspRep.chart_val]
    have e3 : (List.ofFn fun i => ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t i • X i)))) =
        (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).map (ι.comp (GlobalTheory.CuspRep.infGL D.host.E d)) := by
      simp [List.map_ofFn, Function.comp_def]
    rw [e3, ← map_list_prod]
    simp only [P, map_mul, MonoidHom.comp_apply, mul_assoc]

end GlobalTheory.CompanionTheory.CuspSmooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep

open MeasureTheory GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem finiteDimensional_coeffs {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  let T : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (K → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ w => fun k => ℓ (ρ k w))
      (fun ℓ₁ ℓ₂ w => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
      (fun ℓ w₁ w₂ => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
  have hle : coeffSpan ρ ≤ LinearMap.range (TensorProduct.lift T) := by
    unfold coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ⊗ₜ w, by simp [T]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem exists_interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → K) (a : ι → K → ℂ), (∀ i, a i ∈ A) ∧
      ∀ f ∈ A, ∀ k, f k = ∑ i, f (p i) * a i k := by
  classical
  let E : K → Module.Dual ℂ A := fun k => (LinearMap.proj k).comp A.subtype
  have htop : Submodule.span ℂ (Set.range E) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range E)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      apply Subtype.ext
      funext k
      have h := hf (E k) (Submodule.subset_span ⟨k, rfl⟩)
      simpa [E] using h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range E)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range E)
  have hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Module.Dual ℂ A)) := by
    rw [Subtype.range_coe, hbspan, htop]
  let B : Module.Basis b ℂ (Module.Dual ℂ A) := Module.Basis.mk hbli hbtop
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hp : ∀ i : b, ∃ k, E k = (i : Module.Dual ℂ A) := fun i => hbsub i.2
  choose p hpE using hp
  let a : b → A := fun i => (Module.evalEquiv ℂ A).symm (B.coord i)
  refine ⟨b, inferInstance, p, fun i k => (a i : K → ℂ) k, fun i => (a i).2, ?_⟩
  intro f hf k
  have key := B.sum_dual_apply_smul_coord (Module.evalEquiv ℂ A ⟨f, hf⟩)
  have key2 : (⟨f, hf⟩ : A) = ∑ i, (B i ⟨f, hf⟩) • a i := by
    apply (Module.evalEquiv ℂ A).injective
    conv_lhs => rw [← key]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, a, LinearEquiv.apply_symm_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have hk := congrArg (fun g : A => (g : K → ℂ) k) key2
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  rw [hk]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hBi : B i = (i : Module.Dual ℂ A) := by simp [B]
  rw [hBi, ← hpE i]
  rfl

theorem hasTypeAt_of_isConstAlong : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  intro D θ V m X Y hW S T hST τ e P W _ _ _ ρ φ c hφ hty hc
  classical
  have hst := GlobalTheory.StdPar.constAlong_cocompact_unique_stages (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) hW
  obtain ⟨hcoc, μ, 𝓕, hμ, h𝓕, h1⟩ := hst.1 T
  haveI := hμ
  have hcI := hc μ 𝓕 hμ h𝓕 h1
  haveI := finiteDimensional_coeffs ρ
  obtain ⟨ι, _, p, a, ha, hrep⟩ := exists_interp (coeffSpan ρ)
  have hcoc' : GlobalTheory.Cusp.Cocompact (GQ V ⊓ unip D.sp.cm.sig V.gram X T) (unip D.sp.cm.sig V.gram X T) := by
    obtain ⟨K, hK, hKc⟩ := hcoc
    refine ⟨K, hK, fun n => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKc n
    refine ⟨γ, ?_, hγK⟩
    rw [Subgroup.inf_subgroupOf_right]
    exact hγ
  have h𝓕' : IsFundamentalDomain ((GQ V ⊓ unip D.sp.cm.sig V.gram X T).subgroupOf
      (unip D.sp.cm.sig V.gram X T)) 𝓕 μ := by
    rw [Subgroup.inf_subgroupOf_right]
    exact h𝓕
  haveI hdQ : DiscreteTopology ↥(GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram) := inferInstance
  haveI hdisc : DiscreteTopology ↥(GQ V ⊓ unip D.sp.cm.sig V.gram X T) :=
    DiscreteTopology.of_subset hdQ (fun y hy => hy.1)
  have hint : ∀ g : GA D V, IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => φ ((u : GA D V) * g)) 𝓕 μ := by
    intro g
    exact GlobalTheory.Cusp.Cocompact.integrableOn hcoc' h𝓕'
      (fun γ hγ g' => hφ.left γ (ratPts_unip_le_leftSub D V m X Y hW S T hST hγ) g') hφ.cont g
  intro x
  have hfun : (fun k => c (x * kAt θ V τ e P k)) = ∑ i, c (x * kAt θ V τ e P (p i)) • a i := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcI (x * kAt θ V τ e P k)]
    have hpt : ∀ u : unip D.sp.cm.sig V.gram X T, φ ((u : GA D V) * (x * kAt θ V τ e P k)) =
        ∑ i, φ ((u : GA D V) * (x * kAt θ V τ e P (p i))) * a i k := by
      intro u
      have h := hrep _ (hty ((u : GA D V) * x)) k
      simpa [mul_assoc] using h
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => Integrable.mul_const (hint _) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, hcI]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha i)

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GelfandEigenvalueCasimirScalar
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.DerGlRel

private theorem commutator_eq_of_glRel {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M)
    (hL : Formalism.REAL.GlRel fun a b : Fin n => L (Matrix.single a b 1))
    (Z W : Matrix (Fin n) (Fin n) ℂ) :
    L Z * L W - L W * L Z = L (Z * W - W * Z) := by
  classical
  have hs : ∀ (i j : Fin n) (x : ℂ),
      (Matrix.single i j x : Matrix (Fin n) (Fin n) ℂ) = x • Matrix.single i j 1 := by
    intro i j x
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have base : ∀ a b c d : Fin n,
      L (Matrix.single a b 1) * L (Matrix.single c d 1) -
          L (Matrix.single c d 1) * L (Matrix.single a b 1) =
        L (Matrix.single a b 1 * Matrix.single c d 1 -
          Matrix.single c d 1 * Matrix.single a b 1) := by
    intro a b c d
    have h := hL a b c d
    simp only at h
    rw [h, map_sub]
    congr 1
    · by_cases h' : b = c
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
    · by_cases h' : d = a
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
  have key1 : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      L Z * L (Matrix.single c d 1) - L (Matrix.single c d 1) * L Z =
        L (Z * Matrix.single c d 1 - Matrix.single c d 1 * Z) := by
    intro Z c d
    refine Matrix.induction_on' Z ?_ ?_ ?_
    · simp
    · intro p q hp hq
      rw [show (p + q) * Matrix.single c d 1 - Matrix.single c d 1 * (p + q) =
          (p * Matrix.single c d 1 - Matrix.single c d 1 * p) +
            (q * Matrix.single c d 1 - Matrix.single c d 1 * q) by noncomm_ring]
      simp only [map_add (f := _)]
      rw [← hp, ← hq]
      noncomm_ring
    · intro i j x
      rw [hs i j x]
      simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, base]
  refine Matrix.induction_on' W ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [show Z * (p + q) - (p + q) * Z = (Z * p - p * Z) + (Z * q - q * Z) by noncomm_ring]
    simp only [map_add (f := _)]
    rw [← hp, ← hq]
    noncomm_ring
  · intro i j x
    rw [hs i j x]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, key1]

theorem glRel_derEnd_family : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Formalism.REAL.GlRel (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) := by
  intro D θ hθ V τ M hM
  unfold Formalism.REAL.GlRel at hM ⊢
  dsimp only at hM ⊢
  intro a b c d
  have h1 := commutator_eq_of_glRel (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ)
    (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) (M a b) (M c d)
  rw [h1, hM a b c d, map_sub]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.DerGlRel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def IsAdapted {D : D7} (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, ∃ (k : Formalism.REAL.KG (ε τ)) (S : Set (Fin V.rank)),
    Submodule.span ℂ (Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (X j i))) ∪
        Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (Y j i)))) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin V.rank) (1 : ℂ) : Fin V.rank → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

