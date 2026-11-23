module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRepOfMatrixTuplePadicBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CovRep

variable {l : ℕ} [Fact l.Prime]

theorem zOm_smul_eq {m a : ℕ} (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    zOm l c • x = ((c : ℚ_[l])) • x := by
  rw [← algebraMap_smul (Om l) (c : ℚ_[l]) x]
  rfl

theorem isInducing_coe : Topology.IsInducing (fun x : ℤ_[l] => (x : ℚ_[l])) := { eq_induced := rfl }

theorem coord_unique {m a d' : ℕ} {bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)}
    (hli : LinearIndependent ℚ_[l] bb) {z z' : Fin d' → ℤ_[l]}
    (h : ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s) : z = z' := by
  simp only [zOm_smul_eq] at h
  have h0 : ∑ s, (((z s : ℚ_[l])) - (z' s : ℚ_[l])) • bb s = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := (Fintype.linearIndependent_iff.mp hli) _ h0
  funext s
  have hs := this s
  rw [sub_eq_zero] at hs
  exact Subtype.ext hs

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs (g * h) = GlobalTheory.TraceConjugationCover.tup ρs g * GlobalTheory.TraceConjugationCover.tup ρs h := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) :
    GlobalTheory.TraceConjugationCover.tup ρs 1 = 1 := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_inv {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ = fun k => (((ρs k g)⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

end GlobalTheory.CovRep

open GlobalTheory.CovRep in
theorem GlobalTheory.CovRep.rep_of_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (T : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l))) (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), (∀ k, Continuous (ρs k)) → LinearIndependent ℚ_[l] bb → (∀ s, bb s ∈ T) → (∀ x ∈ T, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) → (∀ g, ∀ x ∈ T, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ T) → ∃ ρ' : Γ →* GL (Fin d') ℤ_[l], Continuous ρ' ∧ ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) • bb s := by
  intro l _ Γ _ _ a m ρs T d' bb hc hli hbbT hcoord hstab
  classical
  let crd : (Fin m → Matrix (Fin a) (Fin a) (Om l)) → Fin d' → ℤ_[l] := fun x =>
    if h : ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s then h.choose else 0
  have hcrd : ∀ x ∈ T, x = ∑ s, zOm l (crd x s) • bb s := by
    intro x hx
    have h := hcoord x hx
    simp only [crd, dif_pos h]
    exact h.choose_spec
  have hcrd_eq : ∀ z : Fin d' → ℤ_[l], crd (∑ s, zOm l (z s) • bb s) = z := by
    intro z
    have h : ∃ z' : Fin d' → ℤ_[l], ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s := ⟨z, rfl⟩
    simp only [crd, dif_pos h]
    exact (coord_unique hli h.choose_spec).symm
  let Mf : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun s j => crd (GlobalTheory.TraceConjugationCover.tup ρs g * bb j) s
  have hMf : ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (Mf g s j) • bb s :=
    fun g j => hcrd _ (hstab g _ (hbbT j))
  have key : ∀ g (z : Fin d' → ℤ_[l]),
      GlobalTheory.TraceConjugationCover.tup ρs g * ∑ s, zOm l (z s) • bb s = ∑ t, zOm l ((Mf g *ᵥ z) t) • bb t := by
    intro g z
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hMf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hmul : ∀ g h, Mf (g * h) = Mf g * Mf h := by
    intro g h
    apply Matrix.ext
    intro s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j = ∑ t, zOm l ((Mf g *ᵥ fun s => Mf h s j) t) • bb t := by
      rw [tup_mul, mul_assoc, hMf h j, key]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j) s = _
    rw [e, hcrd_eq]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hone : Mf 1 = 1 := by
    apply Matrix.ext
    intro s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j = ∑ t, zOm l ((1 : Matrix (Fin d') (Fin d') ℤ_[l]) t j) • bb t := by
      rw [tup_one, one_mul]
      simp [Matrix.one_apply]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j) s = _
    rw [e, hcrd_eq]
  let ρM : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] :=
    { toFun := Mf, map_one' := hone, map_mul' := hmul }
  let ρ' : Γ →* GL (Fin d') ℤ_[l] := ρM.toHomUnits
  have hval : ∀ g, ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) = Mf g := fun g => rfl

  let W := Submodule.span ℚ_[l] (Set.range bb)
  let B : Module.Basis (Fin d') ℚ_[l] W := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] W := Module.Finite.of_basis B
  have hW : ∀ x ∈ T, x ∈ W := by
    intro x hx
    rw [hcrd x hx]
    simp only [zOm_smul_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  have hrepr : ∀ x (hx : x ∈ T) s, ((crd x s : ℚ_[l])) = B.repr ⟨x, hW x hx⟩ s := by
    intro x hx s
    have e : (⟨x, hW x hx⟩ : W) = ∑ t, ((crd x t : ℚ_[l])) • B t := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      have hB : ∀ t, ((B t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t := fun t => by
        show ((Module.Basis.span hli t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t
        rw [Module.Basis.span_apply]
      simp only [Submodule.coe_smul, hB]
      show x = _
      conv_lhs => rw [hcrd x hx]
      exact Finset.sum_congr rfl fun t _ => zOm_smul_eq _ _
    rw [e, B.repr_sum_self]
  have hcont : ∀ F : Γ → (Fin m → Matrix (Fin a) (Fin a) (Om l)), Continuous F → (∀ g, F g ∈ T) →
      ∀ s, Continuous fun g => crd (F g) s := by
    intro F hF hT s
    rw [isInducing_coe.continuous_iff]
    have e : (fun x : ℤ_[l] => (x : ℚ_[l])) ∘ (fun g => crd (F g) s) =
        fun g => B.coord s ⟨F g, hW _ (hT g)⟩ := by
      funext g
      simp only [Function.comp_apply, Module.Basis.coord_apply]
      exact hrepr _ (hT g) s
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional (B.coord s)).comp (hF.subtype_mk _)
  have htup : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g :=
    continuous_pi fun k => Units.continuous_val.comp (hc k)
  have htupi : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ := by
    simp_rw [tup_inv]
    exact continuous_pi fun k => Units.continuous_coe_inv.comp (hc k)
  have hMc : Continuous Mf := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htup).matrix_mul continuous_const))
      (fun g => hstab g _ (hbbT j)) s
  have hMci : Continuous fun g => Mf g⁻¹ := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htupi).matrix_mul continuous_const))
      (fun g => hstab g⁻¹ _ (hbbT j)) s
  refine ⟨ρ', ?_, fun g j => by rw [hval]; exact hMf g j⟩
  rw [Units.continuous_iff]
  refine ⟨hMc, ?_⟩
  have e : (fun g => (((ρ' g)⁻¹ : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) = fun g => Mf g⁻¹ := by
    funext g
    rw [← map_inv]
    exact hval _
  rw [e]
  exact hMci

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.PhiD

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_letter (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ (∀ g, actVB PD ρ g x = x) ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp [DcrisL, Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem phi_injective : Function.Injective (φVB PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj

theorem iota_injective : Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem phi_mem (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL := LL) x ∈ DcrisL PD ρ τ := by
  have h1 : ∀ g x, φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ (c : K₀) (x : V ⊗[Qp] B),
      φVB PD (LL := LL) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  intro x hx
  rw [mem_letter] at hx ⊢
  refine ⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩
  obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
  rw [← h2, hx.2, map_smul, h]

theorem iSupIndep_letter : iSupIndep fun τ : K₀ →ₐ[Qp] LL => DcrisL PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K₀) (a : LL) => Module.End.eigenspace
      (mulVB (Qp := Qp) (K₀ := K₀) (B := B) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K₀ →ₐ[Qp] LL => (τ : K₀ → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact ((mem_letter PD ρ τ x).1 hx).2

variable [FiniteDimensional LL V] [IsDomain B]

theorem phi_bijOn (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ)
    (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    Set.BijOn (φVB PD (LL := LL) (V := V)) (DcrisL PD ρ τ') (DcrisL PD ρ τ) := by
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine ⟨phi_mem PD ρ τ τ' h, (phi_injective PD).injOn, fun y hy => ?_⟩
  have hi : Function.Injective ((φVB PD (LL := LL) (V := V)).restrict (phi_mem PD ρ τ τ' h)) :=
    fun x y hxy => Subtype.ext (phi_injective PD (congrArg Subtype.val hxy))
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV])).1 hi
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem iSup_letter (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ) :
    (⨆ τ : K₀ →ₐ[Qp] LL, DcrisL PD ρ τ) = Dcris PD ρ := by
  classical
  haveI := PD.finK₀
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine Submodule.eq_of_le_of_finrank_eq (iSup_le fun τ => inf_le_left) ?_
  have hinj := (iSupIndep_letter PD ρ).dfinsupp_lsum_injective
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hinj]
  change finrank LL (DirectSum _ fun τ => ↥(DcrisL PD ρ τ)) = _
  rw [Module.finrank_directSum]
  simp only [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hc]
  exact hV.symm

end General

theorem phi_letters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW l _ K s LL h W T hV
  haveI := GlobalTheory.RegularRing.isDomain_of_tied (D.locT l) K
  have hc : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K) := by
    rw [← Nat.card_eq_of_bijective _ W.emb_bij, Nat.card_zmod]
  refine ⟨fun i => phi_bijOn _ T.ρ hc hV _ _ fun c => ?_, ?_,
    (iSupIndep_letter ((D.loc l).PD K) T.ρ).comp W.emb_bij.1, iota_injective _⟩
  · have := AlgHom.congr_fun (W.emb_σ (i - 1)) c
    rw [sub_add_cancel] at this
    exact this.symm
  · rw [← iSup_letter _ T.ρ hc hV]
    exact W.emb_bij.2.iSup_comp (fun τ => DcrisL ((D.loc l).PD K) T.ρ τ)

end GlobalTheory.NL.PhiD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.Components

theorem card_le_of_idem_indep {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
    {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → κ → R)
    (h : ∀ r : ι → R, (∀ j, ∑ i, r i * a i j = 0) → ∀ i, e * r i = 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  let I : Ideal R := Ideal.span {1 - e}
  have hI : ∀ x, x ∈ I ↔ e * x = 0 := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      linear_combination (-c) * he
    · intro hx
      exact ⟨x, by linear_combination -hx⟩
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hT
    have : (1 : R) ∈ I := by rw [hT]; trivial
    rw [hI, mul_one] at this
    exact he0 this)
  have hli : LinearIndependent (R ⧸ I) (fun i j => Ideal.Quotient.mk I (a i j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (g i)
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem, hI, ← he, mul_assoc]
    refine h (fun i => e * r i) (fun j => ?_) i
    have := congrFun hg j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hr, ← map_mul,
      ← map_sum] at this
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  simpa using hli.fintype_card_le_finrank

section Bound

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K]
    [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]


open GlobalTheory.DRFil in
theorem finrank_DdRE_le (hF : IsField F) (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] : finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem_indep (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

end Bound

theorem exists_baseChange {G : Type} [Group G] (Qp LL LL' : Type) [Field Qp] [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module LL' V') (_ : Module LL V') (_ : Module Qp V')
      (_ : IsScalarTower Qp LL' V') (_ : IsScalarTower LL LL' V') (_ : FiniteDimensional LL' V')
      (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'),
      IsBaseChange LL' j ∧ ∀ g x, j (ρ g x) = ρ' g (j x) :=
  ⟨LL' ⊗[LL] V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (Module.End.baseChangeHom LL LL' V).toMonoidHom.comp ρ, TensorProduct.mk LL LL' V 1,
    TensorProduct.isBaseChange LL V LL', fun _ _ => rfl⟩

theorem components_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ≤ finrank ↥LL.1 V ∧ (IsDR (P.PD K) ρ → finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V)) ∧ ∀ τ, IsCrys (P.PD K) ρ → finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := K.2
  obtain ⟨LL', ⟨f⟩, hK, hK0⟩ := GlobalTheory.exists_finExt_embedding_splitting l K ↥LL.1
  haveI := LL'.2
  letI : Algebra ↥LL.1 ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ↥LL.1 ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  obtain ⟨V', _, _, _, _, _, _, _, ρ', j, hj, hρj⟩ := exists_baseChange ℚ_[l] ↥LL.1 ↥LL'.1 ρ
  obtain ⟨hV, -, ⟨hc, -⟩, ⟨hd, -⟩, -, hl, he⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) ↥LL.1 ↥LL'.1 V V' ρ ρ' j hj hρj
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI T K LL' V' ρ'
  refine ⟨fun τ => ?_, fun τ hρ => ?_⟩
  · haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
    haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
      Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
    refine ⟨this, finrank_DdRE_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ τ, fun hρ => ?_⟩
    rw [← (he τ).1, ← hV]
    refine h2 hK ?_ _
    unfold IsDR at hρ ⊢
    rw [hd, hV, hρ]
  · rw [← hl τ, ← hV]
    refine h1 hK0 ?_ _
    unfold IsCrys at hρ ⊢
    rw [hc, hV, hρ]

end GlobalTheory.Per.Components
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationBoundsInvariantCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (N : ℕ), DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) → DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥ → ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ≠ 0 → (∀ i, c i ∈ (P.PD K).Fil (-(N : ℤ))) ∧ ¬ ∀ i, c i ∈ (P.PD K).Fil ((N : ℤ) + 1) := by
  first | exact @GlobalTheory.DRMat.invariant_coord_bounds | exact GlobalTheory.DRMat.invariant_coord_bounds | (intros; apply GlobalTheory.DRMat.invariant_coord_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictnessStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_subrep_quotient_and_strictness : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  first | exact @GlobalTheory.DRSubQuot.deRham_sub_quot | exact GlobalTheory.DRSubQuot.deRham_sub_quot | (intros; apply GlobalTheory.DRSubQuot.deRham_sub_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_add_sub_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  intro l _ A _ D J hl n x y hy
  have hy' : y ∈ J ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hy
  have hδ : D.δ y ∈ J ^ n := _root_.GlobalTheory.BSP.delta_pow_succ_mem_pow l A D J hl n y hy
  rw [D.δ_add x y]
  have e : D.δ x + D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) - D.δ x
      = D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) := by ring
  rw [e]
  refine Ideal.sub_mem _ hδ (Ideal.sum_mem _ fun k hk => ?_)
  have hk' : 0 < l - k := Nat.sub_pos_of_lt (Finset.mem_Ioo.1 hk).2
  have : y ^ (l - k) ∈ J ^ n := by
    obtain ⟨m, hm⟩ : ∃ m, l - k = m + 1 := ⟨l - k - 1, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ hy'
  exact Ideal.mul_mem_left _ _ this

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusCommStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deltaRingStructure_delta_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A), D.δ (D.φ a) = D.φ (D.δ a) := by
  first | exact @GlobalTheory.BSP.Delta.δ_φ_comm | exact GlobalTheory.BSP.Delta.δ_φ_comm | (intros; apply GlobalTheory.BSP.Delta.δ_φ_comm <;> assumption)
end

