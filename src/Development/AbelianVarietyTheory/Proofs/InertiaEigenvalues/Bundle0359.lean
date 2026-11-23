module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilteredComparisonCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.DRFilCoord
open Module

theorem deRham_filtered_Ql (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (TT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (hdR : IsDR (P.PD K) ρ) (a : ℤ) (y : V ⊗[ℚ_[l]] P.R.BdR)
    (hy : y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a) :
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
      (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧
        b i ∈ (P.PD K).Fil (a - k i)) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDd : (DdR (P.PD K) ρ').restrictScalars ℚ_[l] = DdR (P.PD K) ρ := by
    ext x
    rw [Submodule.restrictScalars_mem, hD]
  set_option synthInstance.maxHeartbeats 200000 in
  have hDr : finrank ↥LL.1 ↥(DdR (P.PD K) ρ') = finrank ℚ_[l] ↥(DdR (P.PD K) ρ) := by
    rw [← hDd, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (DdR (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(DdR (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hDR' : IsDR (P.PD K) ρ' := by
    unfold IsDR at hdR ⊢
    rw [hDr, hV]; exact hdR
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR' a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

theorem filtered_coords : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  intro l _ P AI TT K d ρ hdR a y hy
  let f : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    (TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)).toLinearMap ∘ₗ
      (TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR).toLinearMap
  have hf : ∀ (v : Fin d → ℚ_[l]) (β : P.R.BdR), f (v ⊗ₜ β) = fun i => v i • β := by
    intro v β; simp [f]
  have hfmul : ∀ (β : P.R.BdR) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (AlgebraTensorModule.map (LinearMap.id : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin d → ℚ_[l]))
        (LinearMap.mulLeft ℚ_[l] β) x) = β • f x := by
    intro β x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, hf]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      ring
    | add u w hu hw => simp only [map_add (f := _), hu, hw, smul_add]
  have hfil : ∀ (c : ℤ) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) c → ∀ i, f x i ∈ (P.PD K).Fil c := by
    intro c x hx i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun x => f x i ∈ (P.PD K).Fil c) ?_ ?_ ?_ hx
    · simp
    · intro v β hβ
      rw [hf]
      exact (((P.PD K).Fil c).restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro x x' h h'
      rw [map_add (f := _)]
      exact Submodule.add_mem _ h h'
  have hact : ∀ (g : ↥(GK K)) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (actVdR (P.PD K) (qRep ρ) g x) =
        (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ
          (fun i => P.actQdR (g : GQ l) (f x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) (qRep ρ) g (v ⊗ₜ β) = qRep ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, hf, hf]
      funext i
      have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
        simp [qRep, Matrix.toLin'_apply]
      rw [hq]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      rfl
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  let x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ y i
  have hx : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) (LL := ℚ_[l]) _ (hy i)
  have hfx : f x = y := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [x, map_sum, hf, Pi.single_apply]
  obtain ⟨m, k, b, dd, h, e⟩ :=
    deRham_filtered_Ql l P AI TT K (Fin d → ℚ_[l]) (qRep ρ) hdR a x hx
  refine ⟨m, k, b, fun r => f (dd r), fun r => ⟨fun g => ?_, hfil _ _ (h r).2.1, (h r).2.2⟩, ?_⟩
  · have hg : actVdR (P.PD K) (qRep ρ) g (dd r) = dd r :=
      (GlobalTheory.DRFil.mem_DdR (P.PD K) (qRep ρ) _).1 (h r).1 g
    rw [← hact, hg]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← hfx, e, map_sum]
      exact Finset.sum_congr rfl fun r _ => hfmul _ _

end GlobalTheory.DRFilCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationBoundsInvariantCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.DRMat

theorem invariant_coord_bounds : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (N : ℕ), DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) → DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥ → ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ≠ 0 → (∀ i, c i ∈ (P.PD K).Fil (-(N : ℤ))) ∧ ¬ ∀ i, c i ∈ (P.PD K).Fil ((N : ℤ) + 1) := by
  intro l _ P K d ρ N hlow hhigh c hc hc0
  let b := Pi.basisFun ℚ_[l] (Fin d)
  let M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR := fun g =>
    (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l]))
  let e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => v i • β := by
    intro v β
    simp [e, b]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) (qRep ρ) g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, he_tmul, he_tmul]
      funext i
      simp only [M, qRep, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul,
        AlgEquiv.commutes, MonoidHom.coe_comp, Function.comp_apply]
      change algebraMap ℚ_[l] P.R.BdR ((((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) i) * _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [PadicInt.algebraMap_apply]
      ring
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  set x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ c i with hx
  have hex : e x = c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    funext j
    simp only [he_tmul, Finset.sum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul]
    simp
  have hxD : x ∈ DdR (P.PD K) (qRep ρ) := by
    rw [GlobalTheory.DRFil.mem_DdR]
    intro g
    apply e.injective
    rw [he, hex]
    exact hc g
  have hcoord : ∀ (a : ℤ) (y : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a → ∀ i, e y i ∈ (P.PD K).Fil a := by
    intro a y hy i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun y => e y i ∈ (P.PD K).Fil a) ?_ ?_ ?_ hy
    · simp
    · intro v β hβ
      rw [he_tmul]
      exact ((P.PD K).Fil a |>.restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro y z hy hz
      simpa only [map_add (f := _), Pi.add_apply] using Submodule.add_mem _ hy hz
  refine ⟨fun i => ?_, fun hall => hc0 ?_⟩
  · simpa [hex] using hcoord _ x (hlow hxD) i
  · have hxF : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) :=
      Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hall i)
    have h0 : x ∈ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) :=
      ⟨hxD, hxF⟩
    rw [hhigh, Submodule.mem_bot] at h0
    rw [← hex, h0, map_zero]

end GlobalTheory.DRMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness
section
noncomputable section

namespace GlobalTheory.DRSubQuot

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.DRFil

theorem mem_of_invariant {G K B M ι : Type} [Field K] [CommRing B] [Algebra K B] (hF : IsField B)
    [AddCommGroup M] [Module B M] [Module K M] [IsScalarTower K B M]
    (σ : G → B → B) (ρ : G → M →+ M) (hρ : ∀ g b w, ρ g (b • w) = σ g b • ρ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * σ g b' = σ g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (hinv : ∀ b : B, (∀ g, σ g b = b) → ∃ c : K, algebraMap K B c = b)
    (F : ℤ → Submodule K B) (hFa : Antitone F) (h1 : (1 : B) ∉ F 1)
    (E : ℤ → AddSubgroup M) (hEa : Antitone E) (hEK : ∀ k (c : K) x, x ∈ E k → c • x ∈ E k)
    (k : ι → ℤ) (e : ι → M) (he : ∀ i, e i ∈ E (k i)) (hei : ∀ g i, ρ g (e i) = e i) (a : ℤ) (n : ℕ) :
    ∀ s : Finset ι, s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (a - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • e i) = ∑ i ∈ s, b i • e i) → ∑ i ∈ s, b i • e i ∈ E a := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hy
  by_cases hli : LinearIndepOn K e s
  · haveI := hF.isDomain
    haveI : Module.IsTorsionFree B M := ⟨fun r hr x y hxy => by
      obtain ⟨u, hu⟩ := hF.mul_inv_cancel hr.ne_zero
      have := congrArg (u • ·) hxy
      simpa only [smul_smul, mul_comm u r, hu, one_smul] using this⟩
    have hB := linearIndepOn_finset_iff.1
      (GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant σ ρ hρ hreg e hei s hli)
    refine (E a).sum_mem fun i hi => ?_
    obtain ⟨c, hc⟩ := hinv (b i) fun g => sub_eq_zero.1 (hB (fun j => σ g (b j) - b j) (by
      have := hy g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hρ, hei] at this
      simp only [sub_smul, Finset.sum_sub_distrib, this, sub_self]) i hi)
    by_cases hc0 : c = 0
    · rw [← hc, hc0, map_zero, zero_smul]
      exact (E a).zero_mem
    rw [← hc, algebraMap_smul]
    refine hEK _ _ _ (hEa ?_ (he i))
    by_contra hlt
    apply h1
    have h2 := (F _).smul_mem c⁻¹ (hb i hi)
    rw [← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one] at h2
    exact hFa (by omega) h2
  · rw [linearIndepOn_finset_iff] at hli
    push Not at hli
    obtain ⟨κ, hκ, i₀, hi₀, hκ₀⟩ := hli
    obtain ⟨i, hi, hmin⟩ := (s.filter fun j => κ j ≠ 0).exists_min_image k
      ⟨i₀, Finset.mem_filter.2 ⟨hi₀, hκ₀⟩⟩
    obtain ⟨his, hκi⟩ := Finset.mem_filter.1 hi
    have hrel : e i = - ∑ j ∈ s.erase i, ((κ i)⁻¹ * κ j) • e j := by
      rw [← Finset.add_sum_erase s _ his] at hκ
      have := congrArg ((κ i)⁻¹ • ·) hκ
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hκi, one_smul, Finset.smul_sum, smul_zero] at this
      exact eq_neg_of_add_eq_zero_left this
    have heq : ∑ j ∈ s, b j • e j = ∑ j ∈ s.erase i, (b j - ((κ i)⁻¹ * κ j) • b i) • e j := by
      rw [← Finset.add_sum_erase s _ his]
      conv_lhs => rw [hrel]
      simp only [smul_neg, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, smul_assoc,
        smul_comm (b i)]
      abel
    rw [heq] at hy ⊢
    refine ih _ (hn ▸ Finset.card_erase_lt_of_mem his) _ rfl _ (fun j hj => ?_) hy
    have hjs := Finset.mem_of_mem_erase hj
    refine (F _).sub_mem (hb j hjs) ?_
    by_cases hj0 : κ j = 0
    · simp [hj0]
    · have := hmin j (Finset.mem_filter.2 ⟨hjs, hj0⟩)
      exact (F _).smul_mem _ (hFa (by omega) (hb i his))

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
include hf

theorem ext_mem_DdR {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) : ext Qp F f x ∈ DdR PD ρ' :=
  (mem_DdR PD _ _).2 fun g => by rw [act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx]

theorem spans_of_surjective (hs : Function.Surjective f) (h : Spans PD ρ) : Spans PD ρ' := by
  intro y
  obtain ⟨a, ha⟩ := exists_mem_FilV PD (LL := LL) y
  obtain ⟨x, -, rfl⟩ := exists_ext_mem_FilV PD f hs ha
  obtain ⟨m, b, d, hd, rfl⟩ := h x
  exact ⟨m, b, fun i => ext Qp F f (d i), fun i => ext_mem_DdR PD ρ ρ' f hf (hd i), by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ext_mulR]⟩

theorem spans_of_injective [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    [FiniteDimensional LL V] [FiniteDimensional LL V'] (hF : IsField F)
    (hi : Function.Injective f) (h : Spans PD ρ') : Spans PD ρ := by
  have h1 : Spans PD ρ'.dual := spans_dual_of_spans PD ρ' ρ'.dual (Module.Dual.eval LL V') hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id h
  have h2 : Spans PD ρ.dual := spans_of_surjective PD ρ'.dual ρ.dual f.dualMap
    (fun g x => by ext v; simp [Module.Dual.transpose_apply, hf]) (LinearMap.dualMap_surjective_of_injective hi) h1
  exact spans_dual_of_spans PD ρ.dual ρ LinearMap.id hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) (Module.bijective_dual_eval LL V) h2

theorem strict_of_surjective (hF : IsField F) (hs : Function.Surjective f) (h : FilSpans PD ρ) (a : ℤ)
    (y : V' ⊗[Qp] F) (hy : y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a) :
    ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a, ext Qp F f x = y := by
  let φ : F →+* Module.End LL (V' ⊗[Qp] F) :=
    { toFun := fun b => mulR Qp F LL V' b
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module F (V' ⊗[Qp] F) := Module.compHom _ φ
  letI : Module K (V' ⊗[Qp] F) := Module.compHom _ (algebraMap K F)
  haveI : IsScalarTower K F (V' ⊗[Qp] F) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsm : ∀ (b : F) (x : V' ⊗[Qp] F), b • x = mulR Qp F LL V' b x := fun _ _ => rfl
  obtain ⟨x, hx, rfl⟩ := exists_ext_mem_FilV PD f hs hy.2
  obtain ⟨m, k, b, d, hd, rfl⟩ := h a x hx
  have hsum : ext Qp F f (∑ i, mulR Qp F LL V (b i) (d i)) = ∑ i, b i • ext Qp F f (d i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ext_mulR, hsm]
  have hinv := (mem_DdR PD _ _).1 hy.1
  rw [hsum] at hinv ⊢
  exact mem_of_invariant (K := K) hF (fun g b => PD.actdR g b) (fun g => (actVdR PD ρ' g).toAddMonoidHom)
    (fun g b w => by
      change actVdR PD ρ' g (mulR Qp F LL V' b w) = mulR Qp F LL V' _ (actVdR PD ρ' g w)
      rw [← sm_one_tmul, act_sm, ← sm_one_tmul]
      simp)
    (GlobalTheory.Per.FontaineBound.frac_dR PD hF) PD.invdR PD.Fil (fil_antitone PD) (one_notMem_fil_one PD)
    (fun c => ((DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c).map (ext Qp F f)).toAddSubgroup)
    (fun c c' hc => Submodule.map_mono (inf_le_inf_left _ (FilV_antitone PD hc)))
    (by
      rintro c κ _ ⟨z, hz, rfl⟩
      refine ⟨mulR Qp F LL V (algebraMap K F κ) z, ⟨mulR_mem_DdR PD ρ κ hz.1, ?_⟩, ext_mulR f _ z⟩
      have h0 : algebraMap K F κ ∈ PD.Fil 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ PD.one_mem
      have := mulR_mem_FilV PD (LL := LL) h0 hz.2
      rwa [zero_add] at this)
    k (fun i => ext Qp F f (d i)) (fun i => ⟨d i, ⟨(hd i).1, (hd i).2.1⟩, rfl⟩)
    (fun g i => (mem_DdR PD _ _).1 (ext_mem_DdR PD ρ ρ' f hf (hd i).1) g) a _ Finset.univ rfl b
    (fun i _ => (hd i).2.2) hinv

end Generic

theorem deRham_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  have := K.2
  have := LL.2
  refine ⟨fun hi h => isDR_of_spans T K LL ρ (spans_of_injective (P.PD K) ρ ρ' f hf (isField_dR T) hi
    ((filSpans T K LL ρ' h).spans _)), fun hs h => ⟨isDR_of_spans T K LL ρ'
    (spans_of_surjective (P.PD K) ρ ρ' f hf hs ((filSpans T K LL ρ h).spans _)), fun a y hy => ?_⟩⟩
  exact strict_of_surjective (P.PD K) ρ ρ' f hf (isField_dR T) hs (filSpans T K LL ρ h) a y hy

end GlobalTheory.DRSubQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSucc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_pow_succ_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A),
    (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  intro l hl A _ D J hlJ n
  have hl0 : 0 < l := hl.out.pos
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have key : x ∈ J ^ (n + 1 + 1) ∧ D.δ x ∈ J ^ (n + 1) := by
      rw [pow_succ' J (n + 1)] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        refine ⟨?_, ?_⟩
        · rw [pow_succ' J (n + 1)]; exact Ideal.mul_mem_mul ha hb
        · rw [D.δ_mul]
          have h1 : a ^ l * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.pow_mem_of_mem J ha l hl0) (ih b hb)
          have h2 : b ^ l * D.δ a ∈ J ^ (n + 1) :=
            Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb l hl0)
          have h3 : (l : A) * D.δ a * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hlJ) (ih b hb)
          exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨Ideal.add_mem _ hy1 hz1, ?_⟩
        rw [D.δ_add]
        refine Ideal.sub_mem _ (Ideal.add_mem _ hy2 hz2) (Ideal.sum_mem _ fun k hk => ?_)
        have hk0 : 0 < k := (Finset.mem_Ioo.1 hk).1
        have hyk : y ^ k ∈ J ^ (n + 1) :=
          Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_of_mem _ hy1 k hk0)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hyk)
    exact key.2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem deltaHom_unique_of_base : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  intro l _ A _ Q _ C _ DQ DC J JC i w tb hb hH h h' hδ hδ' hJ hi hw
  have hit : ∀ (g : Q →+* C), IsδMap DQ DC g → ∀ k x, g (DQ.δ^[k] x) = DC.δ^[k] (g x) := by
    intro g hg k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]
  have hbα : ∀ α, h (tb.b α) = h' (tb.b α) := by
    intro α
    simp only [hb, Finsupp.prod, map_prod, map_pow, hit h hδ, hit h' hδ', hw]
  ext x
  have key : ∀ n, h x - h' x ∈ JC ^ n := by
    intro n
    have hF : ∀ α, α ∉ (tb.fin x n).toFinset → tb.c α x ∈ J ^ n := by
      intro α hα
      by_contra hc
      exact hα ((tb.fin x n).mem_toFinset.2 hc)
    have hap := tb.approx x n _ hF
    have hs : h (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) =
        h' (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← RingHom.comp_apply h i, hi, RingHom.comp_apply, hbα]
    have mem : ∀ g : Q →+* C, g.comp i = h.comp i →
        g (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) ∈ JC ^ n := by
      intro g hg
      have hm := Ideal.mem_map_of_mem g hap
      rw [Ideal.map_map, hg, Ideal.map_pow] at hm
      exact Ideal.pow_right_mono hJ n hm
    have e : h x - h' x = h (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) -
        h' (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      rw [map_sub, map_sub, hs]; ring
    rw [e]
    exact sub_mem (mem h rfl) (mem h' hi.symm)
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP
end

