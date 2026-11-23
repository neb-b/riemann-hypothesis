module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0008
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0011
public import ReciprocityTheory.GaloisValuations.ArithOfA

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAScPOneInt
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_vecV_add' (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a + b) = PI.FinKW.vecV X.B.I v a + PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero' (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.vecV X.B.I v (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem scalarAt_one_mem_integralAdeles (p : TypX X) : scP X p 1 ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  have h := scalarAt_mem_integralAdeles X p 1
  simpa using h

theorem imA_lift_sp (p : TypX X) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    {a : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (ha : a ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F)
      {w | ∃ t ∈ OEp X p, ∃ s ∈ PI.FinKW.vecV X.B.I p.1 '' S, w = t • s}) :
    ∃ A ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S, PI.FinKW.vecV X.B.I p.1 A = a ∧
      ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ⟨τ, hτ, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩ := hx
    refine ⟨(scP X p 1 * τ) • s, ?_, ?_, ?_⟩
    · exact Submodule.smul_mem _
        (⟨scP X p 1 * τ, Subring.mul_mem _ (scalarAt_one_mem_integralAdeles X p) hτ⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span hs)
    · rw [imA_vecV_smul', map_mul, component_scalarAt_same, map_one, one_mul]
    · intro v hv
      rw [imA_vecV_smul', map_mul, component_scalarAt_of_ne X p v hv, zero_mul, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

theorem imA_lift_lat (p : TypX X) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ∃ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A = u ∧ ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    refine ⟨scP X p 1 • (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)),
      Submodule.smul_mem _ (⟨_, scalarAt_one_mem_integralAdeles X p⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hin, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, map_one, one_smul]
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffFlagC
section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

section Reindex

variable {K : Type} [Field K] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {m : ℕ}

end Reindex

section Split

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

def cmp1 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).1)

def cmp2 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).2)

def jm1 : Matrix (Fin n) (Fin n) R := (JR R J).map (fun t => (θ t).1)

theorem cmp_unit (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) (g : HA R σ J) :
    (cmp2 σ J θ g)ᵀ * jm1 J θ * cmp1 σ J θ g = jm1 J θ := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = JR R J := g.2
  let f1 : R ⊗[F] E →+* R := (RingHom.fst R R).comp θ.toRingEquiv.toRingHom
  have h1 := congrArg (fun M => Matrix.map M f1) hg
  simp only [Matrix.map_mul] at h1
  have e1 : (Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))).map f1 = (cmp2 σ J θ g)ᵀ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    show (θ (sigR R σ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i))).1 = (θ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i)).2
    rw [hθ]
    rfl
  rw [e1] at h1
  exact h1

private theorem mem_span_image_iff_pr1_pr2_mem_span {ι : Type} [Fintype ι] (s : Set ι) (u : ι → Fin n → R ⊗[F] E)
    (w : Fin n → R ⊗[F] E) :
    w ∈ Submodule.span (R ⊗[F] E) (u '' s) ↔
      pr1 θ w ∈ Submodule.span R ((fun i => pr1 θ (u i)) '' s) ∧
      pr2 θ w ∈ Submodule.span R ((fun i => pr2 θ (u i)) '' s) := by
  classical
  have h1 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr1 θ (c • v) = (θ c).1 • pr1 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1
    rw [map_mul]
    rfl
  have h2 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr2 θ (c • v) = (θ c).2 • pr2 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2
    rw [map_mul]
    rfl
  have hinj : ∀ x y : Fin n → R ⊗[F] E, pr1 θ x = pr1 θ y → pr2 θ x = pr2 θ y → x = y := by
    intro x y hx hy
    funext i
    apply θ.injective
    exact Prod.ext (congrFun hx i) (congrFun hy i)
  simp only [Set.image_eq_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨⟨fun i => (θ (c i)).1, ?_⟩, ⟨fun i => (θ (c i)).2, ?_⟩⟩
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (h1 (c i) (u ↑i)).symm
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (h2 (c i) (u ↑i)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨fun i => θ.symm (a i, b i), ?_⟩
    apply hinj
    · rw [map_sum]
      simp only [h1, AlgEquiv.apply_symm_apply]
      exact ha
    · rw [map_sum]
      simp only [h2, AlgEquiv.apply_symm_apply]
      exact hb

private theorem pr1_lin_eq_cmp1_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr1 θ (lin R σ J g v) = cmp1 σ J θ g *ᵥ pr1 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr1 θ w k = (θ (w k)).1 := fun _ _ => rfl
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp1, Matrix.map_apply,
    map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]

private theorem pr2_lin_eq_cmp2_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr2 θ (lin R σ J g v) = cmp2 σ J θ g *ᵥ pr2 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr2 θ w k = (θ (w k)).2 := fun _ _ => rfl
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp2, Matrix.map_apply,
    map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]

theorem mem_Ssub_iff_flagC {r : ℕ} (P : Frame E n r) (g : HA R σ J) :
    g ∈ Ssub R σ J P ↔ FlagC (cmp1 σ J θ g) (fun b => pr1 θ (ratV (F := F) R (F0 P b))) ∧
      FlagC (cmp2 σ J θ g) (fun b => pr2 θ (ratV (F := F) R (F0 P b))) := by
  have hm : g ∈ Ssub R σ J P ↔ UniC R σ J (F0 P) g := Iff.rfl
  rw [hm]
  unfold UniC FlagC
  rw [← forall_and]
  apply forall_congr'
  intro b
  show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ spanR (F := F) R (F0 P) {a | a < b} ↔
    (cmp1 σ J θ g *ᵥ pr1 θ (ratV (F := F) R (F0 P b)) - pr1 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr1 θ (ratV (F := F) R (F0 P c))) '' {a | a < b})) ∧
    (cmp2 σ J θ g *ᵥ pr2 θ (ratV (F := F) R (F0 P b)) - pr2 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr2 θ (ratV (F := F) R (F0 P c))) '' {a | a < b}))
  unfold spanR
  rw [mem_span_image_iff_pr1_pr2_mem_span, map_sub, map_sub, pr1_lin_eq_cmp1_mulVec, pr2_lin_eq_cmp2_mulVec]

end Split

end MassDataIdxStIm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxStImB MassDataIdxRed

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev SuX (u : D.what₂.Word) (p : TypX X) : Subgroup (HAp X p) :=
  Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)

def StSImgB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ((SuX X u p).comap K.subtype).map ψ = (sG (Op X p) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

theorem parabolic_image_of_residue (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (hS : StSImgB X u p) :
    ParabolicReductionImage X u p := by
  obtain ⟨π, hπ, hker⟩ := hR
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := hS
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) := (glRed π).comp ψ with hρ₀
  have hker₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hmemK : ∀ y : HAp X p, y ∈ KvX X p → y ∈ K := fun y hy => by
    rw [← SetLike.mem_coe, hK]; exact hy
  refine ⟨K, hK, ρ₀, (glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ, hker₀,
    (SuX X u p).comap K.subtype ⊔ ρ₀.ker, ?_, le_sup_right, glRed π c, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, κ, hκ, rfl⟩ := (mem_sup_ker ρ₀ _).1 hx
      have hκ' : (κ : HAp X p) ∈ KgX X p := (hker₀ κ).1 hκ
      have hsK : (s : HAp X p) ∈ KvX X p := by rw [← hK]; exact s.2
      have hxK : ((s * κ : K) : HAp X p) ∈ KvX X p := by rw [← hK]; exact (s * κ).2
      exact ⟨hxK, s, κ, hs, hsK, hκ', rfl⟩
    · rintro ⟨hy, s, κ, hs, hsK, hκ, rfl⟩
      refine ⟨⟨s, hmemK s hsK⟩ * ⟨κ, hmemK κ hκ.1⟩, ?_, rfl⟩
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact hs
      · rw [MonoidHom.mem_ker, hker₀]; exact hκ
  · rw [map_sup_ker, hρ₀, ← Subgroup.map_map, hc, map_conj,
      sG_map_glRed π hπ]

def StFrameB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, (x : HAp X p) ∈ SuX X u p ↔ c⁻¹ * ψ x * c ∈ sG (Op X p) D.R.rS D.R.k

theorem stSImgB_of (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : StSImgB X u p := by
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := h
  exact ⟨K, hK, ψ, hψ, hP, c, map_eq_conj ψ hψ _ _ c fun x => hc x⟩

theorem parabolic_image_of_residue_frame (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (h : StFrameB X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_residue X u p hR (stSImgB_of X u p h)

theorem parabolic_image_of_frame (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : ParabolicReductionImage X u p :=
  parabolic_image_of_residue_frame X u p (stResZ_holds X p) h

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem coreAll : CoreAll := by
  intro K T _ _ _ O n _ _ θ s J P hs hJ hJu
  exact MassDataIdxCore.coreAll_gen O hs J P hJ hJu

def LatBasisAll {D : D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → ∃ P, LatBasis X p θ P

theorem stRed_of_splitLat {D : D7} (X : HidaSetting D) (p : TypX X) (hS : StSplitLat X p) : StRed X p :=
  stRed_of_core X p (stResZ_holds X p) hS coreAll

theorem stRed_of_emb {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) (hL : LatBasisAll X p) :
    StRed X p := by
  obtain ⟨θ, hθ⟩ := splitTheta_of X p hE
  obtain ⟨P, hP⟩ := hL θ hθ
  exact stRed_of_splitLat X p ⟨θ, hθ, P, hP⟩

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
section
noncomputable section

namespace MassDataIdxEmb

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_primes (h2 : Module.finrank F E = 2) (l : ℕ) [hl : Fact l.Prime]
    (hsplit : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    ∃ Q Q' : Ideal (𝓞 E), Q.IsMaximal ∧ Q'.IsMaximal ∧ Q ≠ Q' ∧ Q.LiesOver p.asIdeal ∧
      Q'.LiesOver p.asIdeal := by
  have := p.isMaximal
  have : Fintype (p.asIdeal.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 E)
  have hrk : Module.finrank (𝓞 F) (𝓞 E) = 2 := (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm.trans h2
  rw [hrk] at hsum
  have hterm : ∀ q : p.asIdeal.primesOver (𝓞 E),
      (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) ≤ 1 := by
    intro q
    have hqp : (q : Ideal (𝓞 E)).IsPrime := q.2.1
    have hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal := q.2.2
    have hq0 : (q : Ideal (𝓞 E)) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _
    let w : HeightOneSpectrum (𝓞 E) := ⟨q, hqp, hq0⟩
    have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
      have := (Ideal.mem_of_liesOver (q : Ideal (𝓞 E)) p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
      simpa using this
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one l hsplit w hw
    change (q : Ideal (𝓞 E)).ramificationIdx ℤ = 1 at he
    change (q : Ideal (𝓞 E)).inertiaDeg ℤ = 1 at hf
    have h1 := Ideal.ramificationIdx_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))
    have h2 := Ideal.inertiaDeg_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))
    rw [he] at h1
    rw [hf] at h2
    calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
      _ = 1 := rfl
  have hcard : 2 ≤ Fintype.card (p.asIdeal.primesOver (𝓞 E)) := by
    calc 2 = ∑ q : p.asIdeal.primesOver (𝓞 E),
          (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) := hsum.symm
      _ ≤ ∑ _q : p.asIdeal.primesOver (𝓞 E), 1 := Finset.sum_le_sum fun q _ => hterm q
      _ = _ := by simp
  obtain ⟨q, q', hqq⟩ := Fintype.one_lt_card_iff.1
    (show 1 < Fintype.card (p.asIdeal.primesOver (𝓞 E)) by omega)
  have hqp : (q : Ideal (𝓞 E)).IsPrime := q.2.1
  have hqp' : (q' : Ideal (𝓞 E)).IsPrime := q'.2.1
  have hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal := q.2.2
  have hqo' : (q' : Ideal (𝓞 E)).LiesOver p.asIdeal := q'.2.2
  refine ⟨q, q', hqp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _),
    hqp'.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _), fun h => hqq (Subtype.ext h), hqo, hqo'⟩

end MassDataIdxEmb

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem embP_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : EmbP X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := (resArith_holds X p).2.1
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨Q, Q', hQ, hQ', hne, hQo, hQ'o⟩ :=
    MassDataIdxEmb.two_primes (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.deg2 (gOf p) hsplit p.1 hmem
  exact MassDataIdxEmb.emb_of_two X.B.I.cm.deg2 p.1 Q Q' hne

end MassDataIdxSteps
end
end

