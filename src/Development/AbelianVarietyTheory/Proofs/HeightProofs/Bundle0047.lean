module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DerFamExpandWords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem derFam_expand_words : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n) (c : Fin d → GlobalTheory.TypeSum.Mx n → ℝ), (∀ i, b i ∈ lieSet ε) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g) →
    ∀ (m : ℕ) (Y : Fin m → GlobalTheory.TypeSum.Mx n), (∀ j, Y j ∈ lieSet ε) → ∀ g ∈ UJset ε,
      F (List.ofFn Y) g = ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j) : ℂ)) * F (List.ofFn fun j => b (J j)) g := by
  intro n ε F hF d b c hb hlin m
  induction m with
  | zero =>
    intro Y _ g _
    simp
  | succ m ih =>
    intro Y hY g hg
    have hwb : ∀ J : Fin m → Fin d, ∀ Z ∈ List.ofFn (fun j => b (J j)), Z ∈ lieSet ε := by
      intro J Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hb _
    have hwY : ∀ Z ∈ List.ofFn (fun j : Fin m => Y j.succ), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hY _
    have key : ∀ i, F (b i :: List.ofFn (fun j : Fin m => Y j.succ)) g =
        ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g := by
      intro i
      have h1 := hF (List.ofFn fun j : Fin m => Y j.succ) hwY (b i) (hb i) g hg
      have h2 : HasDerivAt (fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
          F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)))
          (∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g) 0 := by
        apply HasDerivAt.fun_sum
        intro J _
        exact (hF _ (hwb J) (b i) (hb i) g hg).const_mul _
      have heq : (fun t : ℝ => F (List.ofFn fun j : Fin m => Y j.succ) (g * NormedSpace.exp (t • b i))) =
          fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
            F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)) := by
        funext t
        exact ih (fun j => Y j.succ) (fun j => hY _) _ (mul_mem_UJ hg (exp_mem_UJ (hb i) t))
      rw [heq] at h1
      exact h1.unique h2
    rw [List.ofFn_succ, hlin _ hwY (Y 0) (hY 0) g hg]
    simp_rw [key, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem exists_hom_of_ann {R V M : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R V] {d : ℕ} (w : Fin d → V) (m₀ : M) (h : ∀ α : R, α • w = 0 → α • m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[R] M), ∑ a, T a (w a) = m₀ ∧ ∀ a v, ∃ α : R, T a v = α • m₀ := by
  classical
  let f : R →ₗ[R] (Fin d → V) := LinearMap.toSpanSingleton R _ w
  let g : R →ₗ[R] M := LinearMap.toSpanSingleton R _ m₀
  have hk : LinearMap.ker f ≤ LinearMap.ker g := fun α hα => h α hα
  let φ : LinearMap.range f →ₗ[R] M := (LinearMap.ker f).liftQ g hk ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ α : R, φ ⟨f α, α, rfl⟩ = α • m₀ := by
    intro α
    have : f.quotKerEquivRange.symm ⟨f α, α, rfl⟩ = Submodule.Quotient.mk α := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker f).liftQ g hk (f.quotKerEquivRange.symm ⟨f α, α, rfl⟩) = _
    rw [this]; rfl
  obtain ⟨P, hP⟩ := IsSemisimpleModule.extension_property (LinearMap.range f).subtype
    (LinearMap.range f).injective_subtype LinearMap.id
  refine ⟨fun a => φ ∘ₗ P ∘ₗ LinearMap.single R (fun _ => V) a, ?_, fun a v => ?_⟩
  · have e : ∑ a, Pi.single a (w a) = (LinearMap.range f).subtype ⟨f 1, 1, rfl⟩ := by
      rw [Finset.univ_sum_single]
      exact (one_smul R w).symm
    have e2 := LinearMap.congr_fun hP ⟨f 1, 1, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_single]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sum, e]
    rw [LinearMap.comp_apply] at e2
    rw [e2, LinearMap.id_apply, hφ, one_smul]
  · obtain ⟨α, hα⟩ := (P (Pi.single a v)).2
    refine ⟨α, ?_⟩
    rw [← hφ]
    exact congrArg φ (Subtype.ext hα.symm)

theorem exists_words {L : Type} (α : FreeAlgebra ℂ L) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), α = ∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod := by
  have h1 : α ∈ (Algebra.adjoin ℂ (Set.range (FreeAlgebra.ι ℂ : L → _))).toSubmodule := by
    rw [FreeAlgebra.adjoin_range_ι]; trivial
  rw [Algebra.adjoin_eq_span] at h1
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h1
  have : ∀ x ∈ Submonoid.closure (Set.range (FreeAlgebra.ι ℂ : L → _)),
      ∃ u : List L, (u.map (FreeAlgebra.ι ℂ)).prod = x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨y, rfl⟩ := hx; exact ⟨[y], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u ++ v, by simp⟩
  choose u hu using fun i => this _ (g i).2
  exact ⟨m, c, u, by rw [← e]; simp only [hu]⟩

theorem lift_words {L M : Type} [AddCommGroup M] [Module ℂ M] (τ : L → Module.End ℂ M) {m : ℕ} (c : Fin m → ℂ)
    (u : Fin m → List L) (x : M) :
    FreeAlgebra.lift ℂ τ (∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod) x =
      ∑ i, c i • (u i).foldr (fun y => τ y) x := by
  have : ∀ l : List L, FreeAlgebra.lift ℂ τ (l.map (FreeAlgebra.ι ℂ)).prod x = l.foldr (fun y => τ y) x := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih => rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]; simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, this]

theorem exists_intertwiner {L V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : L → Module.End ℂ V) (hρ : ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤)
    (τ : L → Module.End ℂ M) {d : ℕ} (w : Fin d → V) (m₀ : M)
    (h : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), (∀ a, ∑ i, c i • (u i).foldr (fun y => ρ y) (w a) = 0) →
      ∑ i, c i • (u i).foldr (fun y => τ y) m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[ℂ] M), (∀ a v x, T a (ρ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), T a v = ∑ i, c i • (u i).foldr (fun y => τ y) m₀ := by
  letI : Module (FreeAlgebra ℂ L) V := Module.compHom V (FreeAlgebra.lift ℂ ρ).toRingHom
  letI : Module (FreeAlgebra ℂ L) M := Module.compHom M (FreeAlgebra.lift ℂ τ).toRingHom
  have eV : ∀ (α : FreeAlgebra ℂ L) (v : V), α • v = FreeAlgebra.lift ℂ ρ α v := fun _ _ => rfl
  have eM : ∀ (α : FreeAlgebra ℂ L) (v : M), α • v = FreeAlgebra.lift ℂ τ α v := fun _ _ => rfl
  have cV : ∀ (c : ℂ) (v : V), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eV, AlgHom.commutes]; rfl
  have cM : ∀ (c : ℂ) (v : M), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eM, AlgHom.commutes]; rfl
  have hs : ∀ N : Submodule (FreeAlgebra ℂ L) V, N = ⊥ ∨ N = ⊤ := by
    intro N
    let W : Submodule ℂ V :=
      { carrier := N
        add_mem' := N.add_mem
        zero_mem' := N.zero_mem
        smul_mem' := fun c v hv => by rw [← cV]; exact N.smul_mem _ hv }
    by_cases h0 : W = ⊥
    · left
      rw [eq_bot_iff] at h0 ⊢
      exact fun v hv => h0 (show v ∈ W from hv)
    · right
      have := hρ W (fun x v hv => by
        have := N.smul_mem (FreeAlgebra.ι ℂ x) hv
        rwa [eV, FreeAlgebra.lift_ι_apply] at this) h0
      rw [eq_top_iff] at this ⊢
      exact fun v _ => (show v ∈ W from this trivial)
  haveI : IsSemisimpleModule (FreeAlgebra ℂ L) V := by
    refine (isSemisimpleModule_iff _ _).2 ⟨fun N => ?_⟩
    rcases hs N with rfl | rfl
    exacts [⟨⊤, isCompl_bot_top⟩, ⟨⊥, isCompl_top_bot⟩]
  obtain ⟨T, h1, h2⟩ := exists_hom_of_ann (R := FreeAlgebra ℂ L) w m₀ (by
    intro α hα
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    rw [eM, lift_words]
    refine h m c u fun a => ?_
    rw [← lift_words, ← eV]
    exact congrFun hα a)
  refine ⟨fun a =>
    { toFun := T a
      map_add' := (T a).map_add
      map_smul' := fun c v => by rw [← cV, map_smul, cM]; rfl }, fun a v x => ?_, h1, fun a v => ?_⟩
  · have := (T a).map_smul (FreeAlgebra.ι ℂ x) v
    rwa [eV, eM, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply] at this
  · obtain ⟨α, hα⟩ := h2 a v
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    exact ⟨m, c, u, hα.trans (by rw [eM, lift_words])⟩

theorem exists_maps_of_relations : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  intro hHC n ε H _ _ _ σ hσ d w hw M _ _ τ m₀ h
  have hmem : ∀ (x : Ltr ε) v, IsKFin ε σ v → IsKFin ε σ (ltrV σ x v) := by
    rintro (X | k) v hv
    exacts [isKFin_dRep n ε H σ hσ v hv X.1 X.2, isKFin_translate hv k.2]
  let ρ : Ltr ε → Module.End ℂ (kfin ε σ) := fun x =>
    { toFun := fun v => ⟨ltrV σ x v.1, hmem x v.1 v.2⟩
      map_add' := fun a b => Subtype.ext (by
        rcases x with X | k
        · exact Dw_add hσ.1 (l := [X.1]) (by simpa using X.2) (hσ.2.2.1 _ a.2) (hσ.2.2.1 _ b.2)
        · exact map_add (σ k.1) _ _)
      map_smul' := fun c a => Subtype.ext (by
        rcases x with X | k
        · exact Dw_smul hσ.1 (l := [X.1]) (by simpa using X.2) c (hσ.2.2.1 _ a.2)
        · exact map_smul (σ k.1) _ _) }
  have hword : ∀ (u : List (Ltr ε)) (v : kfin ε σ), (u.foldr (fun y => ρ y) v : kfin ε σ).1 = wordV σ u v.1 := by
    intro u v
    induction u with
    | nil => rfl
    | cons x u ih =>
      show ltrV σ x (u.foldr (fun y => ρ y) v : kfin ε σ).1 = ltrV σ x (wordV σ u v.1)
      rw [ih]
  have hρ : ∀ W : Submodule ℂ (kfin ε σ), (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW h0
    have k1 : ∀ v ∈ W.map (kfin ε σ).subtype, IsKFin ε σ v := by
      rintro _ ⟨v, -, rfl⟩; exact v.2
    have k2 : ∀ (x : Ltr ε), ∀ v ∈ W.map (kfin ε σ).subtype, ltrV σ x v ∈ W.map (kfin ε σ).subtype := by
      rintro x _ ⟨v, hv, rfl⟩; exact ⟨ρ x v, hW x v hv, rfl⟩
    have k3 : ∀ k ∈ Kset ε, ∀ v ∈ W.map (kfin ε σ).subtype, σ k v ∈ W.map (kfin ε σ).subtype :=
      fun k hk => k2 (Sum.inr ⟨k, hk⟩)
    have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hσ.1 hσ.2.1 k1 (fun X hX => k2 (Sum.inl ⟨X, hX⟩)) k3
      (fun e => h0 (Submodule.map_injective_of_injective (kfin ε σ).injective_subtype
        (e.trans (Submodule.map_bot _).symm)))
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, e⟩ := GlobalTheory.HCModIrred.mem_of_dense hσ hd k1 k3 v.2
    exact (Subtype.ext e : y = v) ▸ hy
  obtain ⟨T, h1, h2, h3⟩ := exists_intertwiner ρ hρ τ (fun a => (⟨w a, hw a⟩ : kfin ε σ)) m₀ (by
    intro m c u hu
    refine h m c u fun a => ?_
    have := congrArg Subtype.val (hu a)
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, hword, Submodule.coe_zero] using this)
  choose T' hT' using fun a => LinearMap.exists_extend (T a)
  have e : ∀ a v (hv : IsKFin ε σ v), T' a v = T a ⟨v, hv⟩ := fun a v hv => LinearMap.congr_fun (hT' a) ⟨v, hv⟩
  refine ⟨T', fun a v hv x => ?_, ?_, fun a v hv => ?_⟩
  · rw [e a _ (hmem x v hv), e a v hv]
    exact h1 a ⟨v, hv⟩ x
  · rw [← h2]
    exact Finset.sum_congr rfl fun a _ => e a _ (hw a)
  · rw [e a v hv]
    exact h3 a _

end GlobalTheory.TypeSum.CoefClos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

open GlobalTheory.TypeSum.CoefLow GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.GrowthForm

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)} {N : ℕ} {T : H →ₗ[ℂ] (Mx n → ℂ)}

omit [CompleteSpace H] in
theorem deriv_at (hd : ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0)
    {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X)))
      (T (dRep σ X v) (g * NormedSpace.exp (s • X))) s := by
  have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
  have h1 := hd v hv X hX _ hs
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = T v _
  rw [mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem taylor (h : Std ε σ)
    (hb : ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g)
    (hd : ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0)
    {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    ∃ C, 0 ≤ C ∧ ∀ g ∈ UJset ε, ∀ t : ℝ, |t| ≤ 1 →
      ‖T v (g * NormedSpace.exp (t • X)) - T v g - t • T (dRep σ X v) g‖ ≤ C * wt N g * t ^ 2 := by
  have hv1 := isKFin_dRep n ε H σ h v hv X hX
  have hv2 := isKFin_dRep n ε H σ h _ hv1 X hX
  obtain ⟨C, hC⟩ := hb _ hv2
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
    ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
  refine ⟨|C| * |B|, by positivity, fun g hg t ht => ?_⟩
  have := taylor_two (deriv_at hd hv hX hg) (deriv_at hd hv1 hX hg)
    (K := |C| * |B| * wt N g) (fun s hs => by
      refine (hC _ (mul_mem_UJ hg (exp_mem_UJ hX s))).trans ?_
      refine (mul_le_mul_of_nonneg_right (le_abs_self C) (wt_pos _ _).le).trans ?_
      rw [mul_assoc, mul_comm |B|]
      refine mul_le_mul_of_nonneg_left ((wt_mul_le N g _).trans ?_) (abs_nonneg C)
      exact mul_le_mul_of_nonneg_left ((hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)) (wt_pos N g).le) ht
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using this

omit [CompleteSpace H] in
theorem exists_bdMap (hb : ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g) :
    ∃ T₀ : H →ₗ[ℂ] Bd (Unit × UJset ε), ∀ v, IsKFin ε σ v → ∀ i, T₀ v i = T v i.2.1 / wt N i.2.1 := by
  let f : kfin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun v => mkBd (fun i => T v i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hb v v.2
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [mkBd, add_div]; rfl
      map_smul' := fun c v => by ext i; simp [mkBd, mul_div_assoc] }
  obtain ⟨T₀, hT⟩ := LinearMap.exists_extend f
  refine ⟨T₀, fun v hv i => ?_⟩
  have : T₀ v = f ⟨v, hv⟩ := LinearMap.congr_fun hT ⟨v, hv⟩
  rw [this]
  rfl

theorem exists_form : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  intro hCW n ε H _ _ _ σ h N T hb hK hd
  change ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g at hb
  obtain ⟨T₀, hT₀⟩ := exists_bdMap hb
  have key : ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, ∀ i : Unit × UJset ε, rt ε _ N y (T₀ v) i = T v (i.2.1 * y) / wt N i.2.1 := by
    intro v hv y hy i
    rw [rt_apply hy, hT₀ v hv]
    have := wt_ne N (i.2.1 * y)
    field_simp
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := casselmanWallach_banach hCW n ε H σ h _ _ (modRep_rt ε Unit N) T₀
    (fun k hk v hv => by
      ext i
      rw [key v hv k (K_le_UJ hk), hT₀ _ (isKFin_translate hv hk), hK v hv k hk _ i.2.2])
    (fun X hX v hv => by
      obtain ⟨C, hC, hb⟩ := taylor h hb hd hv hX
      refine hasDerivAt_of_sq (K := C) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X v)) i = t • T₀ (dRep σ X v) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key v hv _ (exp_mem_UJ hX _),
        key v hv _ (exp_mem_UJ hX _), hT₀ _ (isKFin_dRep n ε H σ h v hv X hX), zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _), mul_right_comm]
      exact hb _ i.2.2 t ht)
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx n) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun c x => by simp; ring }
  have hL : ∀ w, Sm ε σ w → ‖L w‖ ≤ wt N (1 : Mx n) * |C| * sobNorm σ S w := fun w hw => by
    change ‖(wt N (1 : Mx n) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  refine ⟨L, ⟨S, _, hS, hL⟩, fun v hv y hy => ?_⟩
  change _ = wt N (1 : Mx n) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
  rw [hT2 y hy v (h.2.2.1 v hv), hT1 v hv, key v hv y hy]
  have := wt_ne N (1 : Mx n)
  simp only [one_mul]
  field_simp

end GlobalTheory.TypeSum.GrowthForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem mem_kFin_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Mx n → (H →L[ℂ] H)} {v : H} : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ↔ IsKFin ε σ v := by
  constructor
  · intro hv
    have : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ≤ kfin ε σ := sSup_le fun W hW w hw => ⟨W, hW.1, hw, hW.2⟩
    exact this hv
  · rintro ⟨S, h1, h2, h3⟩
    exact (le_sSup (show S ∈ {W : Submodule ℂ H | FiniteDimensional ℂ W ∧ IsKStableOn ε σ W} from ⟨h1, h3⟩)) h2

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool}
  {σ : Mx V.rank → (H →L[ℂ] H)} {P : Mx V.rank} {T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)}

theorem map_K (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) {k : Mx V.rank} (hk : k ∈ Kset ε)
    (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (hw : (w : H) = σ k v) (x : GA D V) {y : Mx V.rank} (hy : y ∈ UJset ε) :
    T w (x * atTau θ V τ (P⁻¹ * y * P)) = T v (x * atTau θ V τ (P⁻¹ * (y * k) * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hkU := K_le_UJ hk
  have e : P * (P⁻¹ * k * P) * P⁻¹ = k := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have := hT.mapK (P⁻¹ * k * P) (conj_inv_mem hP h hkU) (by rw [e]; exact hk) v w (by rw [e]; exact hw)
  rw [this, rTr, conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h hkU), mul_assoc]

theorem hasDerivAt_map (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) {X : Mx V.rank}
    (hX : X ∈ lieSet ε) (hv : Sm ε σ (v : H)) (hw : (w : H) = dRep σ X v) (x : GA D V) {y : Mx V.rank}
    (hy : y ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)))
      (T w (x * atTau θ V τ (P⁻¹ * y * P))) 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hX' : P⁻¹ * X * P ∈ lieAt V τ := conj_lie hP h hX
  have e1 : ∀ t : ℝ, P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹ = NormedSpace.exp (t • X) := fun t => by
    rw [← conj_exp hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have hder : HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹) v) w 0 := by
    simp only [e1]; rw [hw]; exact hasDerivAt_dRep (G := Jm ε) hv hX
  have hTw := hT.mapLie _ hX' v w hder
  rw [hTw, Rder]
  have hdiff := differentiable_oneP (hT.aut v).smooth hX' (x * atTau θ V τ (P⁻¹ * y * P)) 0
  refine hdiff.hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)) =
    T v (x * atTau θ V τ (P⁻¹ * y * P) * oneP θ V τ (P⁻¹ * X * P) t)
  rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
    ← mul_assoc]
  rfl

end GlobalTheory.TypeSum.GKCoef
end
end

