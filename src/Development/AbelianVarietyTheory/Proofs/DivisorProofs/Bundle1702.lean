module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuous
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ThK.ModelLocInt

open scoped Classical
open Filter GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem incM_one (m : ℕ) : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem heis_loc {B : Base F E} {M M₁ : Model σ X W} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e : Fn F n d →ₗ[ℂ] Fn F n d} (he : IsEv B M M₁ 1 1 ∅ e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB _)
    (φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₁ : φ₁ ∈ SB _) (hA : Acts (evFin F v) (M.co.rho B.ψ z) φ φ₁)
    (χ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hA₁ : Acts (evFin F v) (M₁.co.rho B.ψ z) (ev v φ) χ₁) :
    ev v φ₁ = χ₁ := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
  rw [incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h1
  rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
  have hevφ : ev v φ ∈ SB _ := by
    rw [← (hvm v).2]
    exact Submodule.mem_map_of_mem hφ
  rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
  exact canc _ _ h1

def ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k))

theorem at_ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    At (evFin F v) (ptAt M v w) := by
  intro a ha
  unfold ptAt
  rw [← LinearEquiv.map_smul, ← M.co.e.symm.map_zero]
  congr 1
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · exact GlobalTheory.LatVac.at_liftV v _ a ha

theorem locCo_ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    GlobalTheory.LatVac.locCo M.co v (ptAt M v w) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp [ptAt, GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.ThK.ModelLocInt


open GlobalTheory.ThK.ModelLocInt in
theorem GlobalTheory.ThK.ModelLocInt.exists_loc_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl (F := F)) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e he ei ev hei hvm hloc v _
  obtain rfl : ‹Invertible (2 : Fv F v)› = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  have hψe : GlobalTheory.LatVac.psiAt B.ψ v = GlobalTheory.VacAny.psiV B.ψ v :=
    by
    ext t
    exact (GlobalTheory.LatVac.psiAt_apply B.ψ v t).trans (GlobalTheory.VacAny.psiV_eq_psiLoc B.ψ v t).symm
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := by
    rw [hψe]; exact GlobalTheory.VacAny.continuous_psiV hP.base.std.1 v
  refine ⟨GlobalTheory.LatVac.psiAt B.ψ v, hψc, by rw [hψe]; exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hP.base.std v,
    fun w => GlobalTheory.LatVac.locCo M₁.co v (ptAt M v w), fun w φ hφ => ?_⟩
  have hA := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v (ptAt M v w) (at_ptAt M v w) φ
  rw [locCo_ptAt] at hA
  have hA₁ := GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v (ptAt M v w) (at_ptAt M v w) (ev v φ)
  exact heis_loc hP.good hM₁ he ei ev hei hvm hloc v (ptAt M v w) φ hφ _
    (GlobalTheory.SchrSBFin.schr_mem_SB v _ hψc w φ hφ) hA _ hA₁
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchSurj

theorem exists_point_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y : κ → Af F, ∀ v, φ v (fun i => y i v) ≠ 0 := by
  have key : ∀ v : Pl (F := F), ∃ z : κ → Fv F v, φ v z ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, z i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨z, hz⟩ := Function.ne_iff.mp (hne v)
    refine ⟨z, hz, fun h => ?_⟩
    rw [h] at hz
    exact Set.mem_of_indicator_ne_zero hz
  choose z hz hz' using key
  exact ⟨fun i => ⟨fun v => z v i, hstd.mono fun v hv => hz' v hv i⟩, hz⟩

theorem surjective_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hsurj ei ev hev he h
  have h₁ : pure h M₁.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA h M₁.vac (fun v => (hM₁.vac v).1) hM₁.std
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj h₁
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = M.vac v := by
    intro i
    filter_upwards [hM.std, T.eventually_cofinite_notMem] with v hv hT
    rw [hv, hstd i v hT]
  have hid : pure h M₁.vac = ∑ i, pure (ei (f i)) fun v => ev v (φ i v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨y, hy⟩ := exists_point_ne_zero M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set c : ℂ := ∏ᶠ v, M₁.vac v (fun j => y j v) with hc
  have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
  set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
  refine ⟨∑ i, (cs i / c) • f i, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  let a : Fin n × Fin d → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
  have hI : (fun j => evI F (a j)) = x := by
    funext j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
  have hx : h x * c = ∑ i, ei (f i) x * cs i := by
    have := congrFun hid a
    rw [Finset.sum_apply] at this
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
    exact this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
    rw [SchwartzMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]; rfl
  rw [hs]
  apply mul_right_cancel₀ hc0
  rw [hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end GlobalTheory.ArchSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympUnip

open GlobalTheory.SympChange GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Ring

variable {R κ : Type} [CommRing R] [Fintype κ]

def mulR (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulR_apply (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) (φ : (κ → R) → ℂ) (x : κ → R) :
    mulR χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulR_neg (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) (φ : (κ → R) → ℂ) :
    mulR χ h (-A) (mulR χ h A φ) = φ := by
  funext x
  rw [mulR_apply, mulR_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulR_mem [TopologicalSpace R] [IsTopologicalRing R] {χ : AddChar R ℂ} (hχ : IsLocallyConstant χ) (h : R)
    (A : Matrix κ κ R) {φ : (κ → R) → ℂ} (hφ : φ ∈ SB (κ → R)) : mulR χ h A φ ∈ SB (κ → R) :=
  ⟨(hχ.comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem spAct_unipM {K : Type} [Field K] [Algebra K R] [DecidableEq κ] (S : Matrix κ κ K)
    (w : (κ → R) × (κ → R)) : spAct (unipM S) w = (w.1, S.map (algebraMap K R) *ᵥ w.1 + w.2) := by
  have h1 : (1 : Matrix κ κ K).map (algebraMap K R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix κ κ K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [spAct, unipM, Matrix.fromBlocks_map, h1, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Sum.elim_inl, Sum.elim_inr]

theorem mulR_schr [Invertible (2 : R)] {K : Type} [Field K] [Algebra K R] [DecidableEq κ] (χ : AddChar R ℂ)
    (S : Matrix κ κ K) (hS : Sᵀ = S) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulR χ (⅟2) (-S.map (algebraMap K R)) (schr χ w φ) =
      schr χ (spAct (unipM S) w) (mulR χ (⅟2) (-S.map (algebraMap K R)) φ) := by
  have hA : (-S.map (algebraMap K R))ᵀ = -S.map (algebraMap K R) := by
    rw [Matrix.transpose_neg, ← Matrix.transpose_map, hS]
  funext x
  rw [spAct_unipM, mulR_apply]
  simp only [schr]
  rw [mulR_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add _ hA,
    Matrix.neg_mulVec, neg_neg]

end Ring

variable {F : Type} [Field F] [NumberField F]

theorem eventually_integral (z : Af F) : ∀ᶠ v : Pl F in cofinite, evalV F v z ∈ v.adicCompletionIntegers F := z.2

theorem eventually_evFin (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  eventually_integral (sndA F a)

theorem exists_finite_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) : ∃ I : Set (Pl (F := F)), I.Finite ∧
    ∀ z : Af F, (∀ v, evalV F v z ∈ v.adicCompletionIntegers F) → (∀ v ∈ I, evalV F v z = 0) → finChar ψ z = 1 := by
  let f : (∀ v : Pl (F := F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : Continuous f := RestrictedProduct.isEmbedding_structureMap.continuous
  have hlc : IsLocallyConstant (fun y => finChar ψ (f y)) := (finChar_isLocallyConstant ψ hψ).comp_continuous hf
  have h0 := hlc.eventually_eq 0
  rw [Filter.Eventually, nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, hI, t, ht, hs⟩ := h0
  refine ⟨I, hI, fun z hz hz0 => ?_⟩
  have hy : (fun v : Pl F => (⟨evalV F v z, hz v⟩ : v.adicCompletionIntegers F)) ∈ I.pi t := fun v hv => by
    have : (⟨evalV F v z, hz v⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (hz0 v hv)
    exact Set.mem_of_eq_of_mem this (mem_of_mem_nhds (ht v))
  have h1 : finChar ψ z = finChar ψ 0 := hs hy
  rw [h1, AddChar.map_zero_eq_one]

theorem finChar_eq_finprod (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (z : Af F) :
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evalV F v z)).Finite ∧
      finChar ψ z = ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evalV F v z) := by
  classical
  obtain ⟨I, hI, h⟩ := exists_finite_trivial ψ hψ
  have hT : (I ∪ {v | evalV F v z ∉ v.adicCompletionIntegers F}).Finite := hI.union (eventually_integral z)
  have hloc : ∀ (v : Pl (F := F)) (y : Fv F v), GlobalTheory.LatVac.psiAt ψ v y = finChar ψ (singleFin v y) := fun _ _ => rfl
  have hsub : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evalV F v z)) ⊆ hT.toFinset := by
    intro v hv
    by_contra hn
    simp only [Set.Finite.coe_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    refine hv ((hloc v _).trans (h _ (fun u => ?_) fun u hu => ?_))
    · by_cases huv : u = v
      · subst huv
        rw [evalV_singleFin_self]; exact hn.2
      · rw [evalV_singleFin_ne huv]; exact zero_mem _
    · exact evalV_singleFin_ne (fun e : u = v => hn.1 (e ▸ hu)) _
  refine ⟨hT.toFinset.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  set s : Af F := ∑ v ∈ hT.toFinset, singleFin v (evalV F v z) with hs
  have hev : ∀ u, evalV F u s = if u ∈ hT.toFinset then evalV F u z else 0 := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single_of_mem u hu fun v _ hv => evalV_singleFin_ne hv.symm _, evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _
  have h1 : finChar ψ (z - s) = 1 := by
    refine h _ (fun u => ?_) fun u hu => ?_
    · rw [map_sub, hev]
      split_ifs with hu
      · rw [sub_self]; exact zero_mem _
      · simp only [Set.Finite.mem_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hu
        rw [sub_zero]; exact hu.2
    · rw [map_sub, hev, if_pos (hT.mem_toFinset.2 (Or.inl hu)), sub_self]
  have h2 : ∀ T : Finset (Pl (F := F)), finChar ψ (∑ v ∈ T, singleFin v (evalV F v z)) =
      ∏ v ∈ T, GlobalTheory.LatVac.psiAt ψ v (evalV F v z) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    | insert a T ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih, hloc]
  rw [← h2, ← hs, ← one_mul (finChar ψ s), ← h1, ← AddChar.map_add_eq_mul, sub_add_cancel]

theorem psiAt_isLocallyConstant (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) :
    IsLocallyConstant (GlobalTheory.LatVac.psiAt ψ v) :=
  (finChar_isLocallyConstant ψ hψ).comp_continuous (continuous_singleFin v)

theorem quad_mem {κ : Type} [Fintype κ] {v : Pl (F := F)} {h : Fv F v} {A : Matrix κ κ (Fv F v)} {x : κ → Fv F v}
    (hh : h ∈ v.adicCompletionIntegers F) (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) : quad h A x ∈ v.adicCompletionIntegers F :=
  mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))


open scoped Classical in
theorem hasOp_unipM : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (S : Matrix κ κ F), S.transpose = S →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.unipM S) := by
  intro F _ _ ψ hψ hunr _ κ _ _ S hS
  have evFin_invOf_two (v : Pl F) : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  let A : Matrix κ κ (AF F) := -S.map (algebraMap F (AF F))
  let Av : ∀ v : Pl (F := F), Matrix κ κ (Fv F v) := fun v => -S.map (algebraMap F (Fv F v))
  have hAv : ∀ v, A.map (evFin F v : AF F →+* Fv F v) = Av v := fun v => by
    refine Matrix.ext fun i j => ?_
    change evFin F v (-algebraMap F (AF F) (S i j)) = -algebraMap F (Fv F v) (S i j)
    rw [map_neg, AlgHom.commutes]
  let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let hi := q (⅟2)
  let Ai := A.map q
  refine ⟨mulR ψ (⅟2) A, SchwartzMap.smulLeftCLM ℂ (archMul hi Ai),
    fun v => mulR (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v), fun f => ?_, mulQ_mem ψ hψ _ A,
    fun w Φ _ => mulR_schr ψ S hS w Φ, fun v => ?_, fun v φ _ h0 => ?_,
    fun v w φ _ => mulR_schr _ S hS w φ, ?_, fun f φ _ hφ => ?_⟩
  · refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul hi (-Ai)) f, SchwartzMap.ext fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_smul, archMul, archMul, eChar_apply,
      eChar_apply, ← Complex.exp_add, quad_neg, map_neg, neg_neg]
    rw [show ∀ a : ℂ, a = 0 → Complex.exp a • f y = f y from fun a ha => by rw [ha, Complex.exp_zero, one_smul]]
    push_cast
    ring
  · have hlc := psiAt_isLocallyConstant ψ hψ.1 v
    refine le_antisymm ?_ fun φ hφ => ⟨mulR _ (⅟2) (-Av v) φ, mulR_mem hlc _ _ hφ, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      exact mulR_mem hlc _ _ hφ
    · have := mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-Av v) φ
      rwa [neg_neg] at this
  · rw [← mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v) φ]
    exact (congrArg _ h0).trans (map_zero _)
  · have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := eventually_evFin _
    have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i j, evFin F v (A i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => eventually_evFin (A i j)
    filter_upwards [hunr, h2, h3] with v hv h2 h3
    funext x
    rw [mulR_apply]
    by_cases hx : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · rw [(evFin_invOf_two v)] at h2
      have h4 := (hv 1).2 (one_mem _) _ (quad_mem (A := Av v) h2 (fun i j => by rw [← hAv v]; exact h3 i j) hx)
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, one_mul]
    · rw [indO, Set.indicator_of_notMem hx, mul_zero]
  · funext x
    have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφ, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl (F := F), evalV F v (p2 (quad (⅟2) A x)) = quad (⅟2) (Av v) fun i => evFin F v (x i) := fun v => by
      have := map_quad (evFin F v : AF F →+* Fv F v) (⅟2) A x
      rw [hAv] at this
      exact this.trans (congrArg (fun t => quad t (Av v) fun i => evFin F v (x i)) (evFin_invOf_two v))
    obtain ⟨hs, hp⟩ := finChar_eq_finprod ψ hψ.1 (p2 (quad (⅟2) A x))
    simp only [hq] at hs hp
    have h3 : ψ (mk (p1 (quad (⅟2) A x)) 0) = archMul hi Ai fun i => evI F (x i) := by
      have e1 : evI F (mk (p1 (quad (⅟2) A x)) 0) = quad hi Ai fun i => evI F (x i) := map_quad q (⅟2) A x
      rw [hψ.2.2 _ (at_mk _), e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mulR_apply]
    rw [finprod_mul_distrib hs hfin, ← hp, map_eq_mul ψ, h3,
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
    ring

end GlobalTheory.SympUnip

end
end

