module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0593

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmConj
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem kur_map {l : ℕ} [Fact l.Prime] (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    g x ∈ MaximalUnramifiedExtension l := by
  have h1 : g x ∈ (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    (Set.mem_image_of_mem _ hx :)
  rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map] at h1
  refine (IntermediateField.adjoin_le_iff.mpr ?_) h1
  rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩

private theorem iq_normal (l : ℕ) [Fact l.Prime] : (Iq l).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (kur_map g⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

section Gen

variable {Q Γ G A V B : Type} [Field Q] [Group Γ] [Group G] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V]
  [Module Q V] [IsScalarTower Q A V] [CommRing B] [Algebra Q B] (α : Γ →* (B ≃ₐ[Q] B))

private noncomputable def cj (c : Γ) : V ⊗[Q] B ≃ₗ[A] V ⊗[Q] B :=
  AlgebraTensorModule.congr (LinearEquiv.refl A V) (α c).toLinearEquiv

private theorem cj_act (c g : Γ) (f : V →ₗ[A] V) (x : V ⊗[Q] B) :
    AlgebraTensorModule.map f (α (c * g * c⁻¹)).toLinearMap (cj (A := A) α c x) =
      cj (A := A) α c (AlgebraTensorModule.map f (α g).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    have h : α (c * g * c⁻¹) (α c b) = α c (α g b) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
    simp only [cj, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul, LinearEquiv.refl_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearEquiv_apply, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem cj_one (c : Γ) (v : V) : cj (A := A) α c (v ⊗ₜ[Q] (1 : B)) = v ⊗ₜ[Q] (1 : B) := by
  simp [cj]

private theorem finrank_inv (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) :
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) =
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (φ g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) := by
  symm
  refine ((cj (A := A) α c).ofSubmodules _ _ ?_).finrank_eq
  ext x
  obtain ⟨y, rfl⟩ := (cj (A := A) (V := V) α c).surjective x
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, (cj α c).injective.eq_iff]

private theorem cob_iff (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) (z : G → V) :
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap x - x) ↔
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g) (α (φ g)).toLinearMap x - x) := by
  rw [(cj (A := A) (V := V) α c).surjective.exists]
  refine exists_congr fun y => forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, ← map_sub, ← cj_one (A := A) α c, (cj α c).injective.eq_iff, cj_one]

private theorem index_conj (c : Γ) (φ : G →* Γ) (N : Subgroup Γ) [hN : N.Normal] :
    (((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N).index = (φ.range ⊔ N).index := by
  have h1 : N.map (MulAut.conj c).toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy c
    · intro hx
      refine ⟨c⁻¹ * x * c⁻¹⁻¹, hN.conj_mem x hx c⁻¹, ?_⟩
      simp [mul_assoc]
  have h2 : ((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N = (φ.range ⊔ N).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_sup, h1, MonoidHom.range_comp]
  rw [h2]
  exact Subgroup.index_map_of_bijective (MulAut.conj c).bijective _

end Gen

theorem UpperTheory.V.Loc.admissible_conjugate :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (c : GQ l), (IsCr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsCr φ ρ) ∧ (IsDr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsDr φ ρ) ∧ UpperTheory.V.Loc.finiteCocycles ((MulAut.conj c).toMonoidHom.comp φ) ρ = UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro l _ G _ _ _ φ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ c
  refine ⟨?_, ?_, ?_⟩
  · haveI := iq_normal l
    have h1 : finrank ℚ_[l] ↥(Dcr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Dcr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQ c φ (resCoef ℚ_[l] ρ)
    rw [IsCr, IsCr, h1, index_conj]
  · have h1 : finrank ℚ_[l] ↥(Ddr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Ddr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQdR c φ (resCoef ℚ_[l] ρ)
    have h2 := index_conj c φ ⊥
    rw [sup_bot_eq, sup_bot_eq] at h2
    rw [IsDr, IsDr, h1, h2]
  · ext z
    exact and_congr_right fun _ => cob_iff (PP l).actQ c φ ρ z
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
variable {Q : Type} [Field Q] {G V V' B : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
  [AddCommGroup B] [Module Q B]

private def fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (r g) (a g) - LinearMap.id)

private theorem mem_fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B)
    (x : V ⊗[Q] B) : x ∈ fixT r a ↔ ∀ g, AlgebraTensorModule.map (r g) (a g) x = x := by
  simp [fixT, Submodule.mem_iInf, sub_eq_zero]

private theorem prodLeft_act (r : V →ₗ[Q] V) (r' : V' →ₗ[Q] V') (a : B →ₗ[Q] B) (x : (V × V') ⊗[Q] B) :
    TensorProduct.prodLeft Q Q V V' B (AlgebraTensorModule.map (r.prodMap r') a x) =
      (AlgebraTensorModule.map r a (TensorProduct.prodLeft Q Q V V' B x).1,
        AlgebraTensorModule.map r' a (TensorProduct.prodLeft Q Q V V' B x).2) := by
  induction x with
  | tmul v b => obtain ⟨v, v'⟩ := v; simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

private theorem fixT_map (r : G → V →ₗ[Q] V) (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) :
    (fixT (fun g => (r g).prodMap (r' g)) a).map (TensorProduct.prodLeft Q Q V V' B).toLinearMap =
      (fixT r a).prod (fixT r' a) := by
  ext y
  obtain ⟨x, rfl⟩ := (TensorProduct.prodLeft Q Q V V' B).surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_prod, mem_fixT, mem_fixT, mem_fixT,
    ← forall_and]
  refine forall_congr' fun g => ?_
  rw [← (TensorProduct.prodLeft Q Q V V' B).injective.eq_iff, prodLeft_act, Prod.ext_iff]

private def prodEquiv' {M N : Type} [AddCommGroup M] [Module Q M] [AddCommGroup N] [Module Q N]
    (p : Submodule Q M) (q : Submodule Q N) : ↥(p.prod q) ≃ₗ[Q] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixT_finite [FiniteDimensional Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) : Module.Finite Q ↥(fixT r a) := by
  rcases Nat.eq_zero_or_pos (finrank Q V) with h0 | h0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ Nat.mul_pos (Nat.pos_of_ne_zero hn) h0)

private theorem fixT_prod [FiniteDimensional Q V] [FiniteDimensional Q V'] (r : G → V →ₗ[Q] V)
    (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) (h' : finrank Q ↥(fixT r' a) = n * finrank Q V') :
    finrank Q ↥(fixT (fun g => (r g).prodMap (r' g)) a) = n * finrank Q (V × V') := by
  haveI := fixT_finite r a hn h
  haveI := fixT_finite r' a hn h'
  rw [← LinearEquiv.finrank_map_eq (TensorProduct.prodLeft Q Q V V' B), fixT_map,
    (prodEquiv' _ _).finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end

theorem UpperTheory.V.Loc.isCrys_isDR_prod :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] (ρ : Representation A G V) (ρ' : Representation A G V'), ContAction ρ → ContAction ρ' → (IsCr φ ρ → IsCr φ ρ' → IsCr φ (ρ.prod ρ')) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ (ρ.prod ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _
  have ho : IsOpen (φ.range : Set (GQ l)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ ho
  have h1 : φ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (φ.range ⊔ Iq l).index ≠ 0 := fun h =>
    h1 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_left))
  exact ⟨fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQ (φ g)).toLinearMap) h2 h h',
    fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQdR (φ g)).toLinearMap) h1 h h'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallinePeriodMatrixMemFilZeroOfWeightZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → BdR) (i : Fin d) :
    (TensorProduct.lid Qp BdR) (LinearMap.rTensor BdR (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem sum_mem_fil_iff (a : ℤ) (c : Fin d → BdR) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ FilV PD (LL := Qp) (V := V) a ↔ ∀ i, c i ∈ PD.Fil a := by
  constructor
  · rintro ⟨z, hz⟩ i
    rw [← coord_sum e c i, ← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v x =>
      have := ((PD.Fil a).restrictScalars Qp).smul_mem (e.coord i v) x.2
      simpa using this
    | add x y hx hy =>
      simp only [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · intro h
    exact Submodule.sum_mem _ fun j _ => ⟨e j ⊗ₜ ⟨c j, h j⟩, rfl⟩

private theorem sum_mem_DdR (c : Fin d → BdR)
    (h : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)).mulVec (fun j => PD.actdR g (c j)) = c) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro g
  conv_rhs => rw [← h g]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actdR g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core
    (hinv : ∀ a b, b ∈ PD.Fil a → b ∉ PD.Fil (a + 1) → ∃ β ∈ PD.Fil (-a), β * b - 1 ∈ PD.Fil 1)
    (hT : ∀ n x, x ∈ PD.Fil n → (∀ g, PD.actdR g x - x ∈ PD.Fil (n + 1)) →
      ∃ κ ∈ PD.Fil 0, (∀ g, PD.actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ x - κ ∈ PD.Fil (n + 1))
    (h0 : DdR PD ρ ≤ FilV PD (LL := Qp) (V := V) 0) (h1 : DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 = ⊥)
    (N N' : Matrix (Fin d) (Fin d) BdR) (hN : N * N' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR) * N.map (PD.actdR g) = N) :
    (∀ i j, N i j ∈ PD.Fil 0) ∧ ∀ i j, N' i j ∈ PD.Fil 0 := by
  let A : G → Matrix (Fin d) (Fin d) BdR := fun g => (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)
  have hA : ∀ g i j, A g i j ∈ PD.Fil 0 := fun g i j => by
    change algebraMap Qp BdR _ ∈ _
    rw [IsScalarTower.algebraMap_apply Qp K BdR, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ PD.one_mem
  have hcol : ∀ j g, (A g).mulVec (fun i => PD.actdR g (N i j)) = fun i => N i j := fun j g => by
    funext i
    exact congrFun (congrFun (hg g) i) j
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hA' : ∀ g, N' * A g = N'.map (PD.actdR g) := fun g => by
    have h2 : N.map (PD.actdR g) * N'.map (PD.actdR g) = 1 := by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) BdR => X.map (PD.actdR g : BdR →+* BdR)) hN
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    calc N' * A g = N' * A g * (N.map (PD.actdR g) * N'.map (PD.actdR g)) := by rw [h2, mul_one]
      _ = N' * (A g * N.map (PD.actdR g)) * N'.map (PD.actdR g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg g, hN', one_mul]
  refine ⟨fun i j => (sum_mem_fil_iff PD e 0 (fun i => N i j)).1 (h0 (sum_mem_DdR PD ρ e _ (hcol j))) i,
    fun i j => ?_⟩
  have hFa : Antitone fun a => (PD.Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => PD.Fil_anti a
  let R : G → (Fin d → BdR) →+ (Fin d → BdR) := fun g =>
    { toFun := fun c => (A g).mulVec (fun j => PD.actdR g (c j))
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext j
        simp }
  let FM : ℤ → AddSubgroup (Fin d → BdR) := fun a => AddSubgroup.pi Set.univ fun _ => (PD.Fil a).toAddSubgroup
  have hFM : ∀ a c, c ∈ FM a ↔ ∀ i, c i ∈ PD.Fil a := fun a c => by
    simp [FM, AddSubgroup.mem_pi]
  obtain ⟨m, k, b, c, h, hs⟩ := GlobalTheory.DRFil.filtered (G := G) (fun g => (PD.actdR g : BdR →+* BdR)) R
    (fun a => (PD.Fil a).toAddSubgroup) FM
    (fun g b x => by
      change (A g).mulVec _ = _ • (A g).mulVec _
      rw [← Matrix.mulVec_smul]
      congr 1
      funext j
      simp)
    PD.Fil_mul
    (fun a c x z hx hz => (hFM _ _).2 fun i => PD.Fil_mul _ _ _ _ hx ((hFM _ _).1 hz i))
    PD.Fil_G
    (fun g a z hz => (hFM _ _).2 fun i => by
      change ∑ j, A g i j * PD.actdR g (z j) ∈ _
      refine Submodule.sum_mem _ fun j _ => ?_
      have := PD.Fil_mul _ _ _ _ (hA g i j) (PD.Fil_G g _ _ ((hFM _ _).1 hz j))
      rwa [zero_add] at this)
    hinv hT hFa (fun a a' h z hz => (hFM _ _).2 fun i => hFa h ((hFM _ _).1 hz i)) PD.Fil_exh
    (fun x => by
      choose r hr using fun i => PD.Fil_exh (x i)
      obtain ⟨a, ha⟩ := (Set.finite_range r).bddBelow
      exact ⟨a, (hFM _ _).2 fun i => hFa (ha ⟨i, rfl⟩) (hr i)⟩)
    0 (fun i => (1 : Matrix (Fin d) (Fin d) BdR) i j)
    ((hFM _ _).2 fun i => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [PD.one_mem, Submodule.zero_mem _])
    d (fun i => N' i j) (fun j i => N i j) (fun j g => hcol j g)
    (by
      funext i
      rw [← hN, Matrix.mul_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _)
  have h3 : N' i j = ∑ n, b n * N'.mulVec (c n) i := by
    have h4 := congrFun (congrArg N'.mulVec hs) i
    rw [Matrix.mulVec_sum, Finset.sum_apply] at h4
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h4
    rw [← h4]
    exact (congrFun (congrFun (mul_one N') i) j).symm
  rw [h3]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨hc, hk, hb⟩ := h n
  by_cases hk1 : 1 ≤ k n
  · have h5 : ∑ j, e j ⊗ₜ[Qp] c n j ∈ DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 :=
      ⟨sum_mem_DdR PD ρ e _ hc, (sum_mem_fil_iff PD e 1 _).2 fun i => hFa hk1 ((hFM _ _).1 hk i)⟩
    rw [h1, Submodule.mem_bot] at h5
    have h6 : c n = 0 := funext fun i => by
      rw [← coord_sum e (c n) i, h5]
      simp
    rw [h6]
    simp
  · have h5 : b n ∈ PD.Fil 0 := hFa (show (0 : ℤ) ≤ 0 - k n by omega) hb
    obtain ⟨κ, hκ⟩ := PD.invdR (N'.mulVec (c n) i) fun g => by
      have h6 : (A g).mulVec (fun j => PD.actdR g (c n j)) = c n := hc g
      conv_rhs => rw [← h6, Matrix.mulVec_mulVec, hA' g]
      simp [Matrix.mulVec, dotProduct]
    have h6 : N'.mulVec (c n) i ∈ PD.Fil 0 := by
      rw [← hκ, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ PD.one_mem
    simpa using PD.Fil_mul _ _ _ _ h5 h6

end Coord

theorem UpperTheory.crystalline_period_matrix_mem_fil_zero_of_weight_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → DdR ((PP l).PD K) ρ ≤ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0 → DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 1 = ⊥ → ∀ (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ ∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil 0 := by
  intro l _ K V _ _ _ ρ d e _ h0 h1 M M' hM hg
  obtain ⟨T⟩ := tiedP l
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
  have key := core ((PP l).PD K) ρ e (GlobalTheory.DRFil.graded_inv Θ K) (GlobalTheory.DRFil.graded_invariants T Θ K) h0 h1
    (M.map (PP l).ιB) (M'.map (PP l).ιB)
    (by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) (Bcr l) => X.map ((PP l).ιB : Bcr l →+* Bdr l)) hM
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this)
    (fun g => by
      ext i j
      have := congrArg (PP l).ιB (congrFun (congrFun (hg g) i) j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, ← this, Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.map_apply, map_mul, AlgHom.commutes]
      rw [← (PP l).PD_actB K g, ← (PP l).PD_ι K, ← (PP l).PD_ι K, ((PP l).PD K).ι_comm])
  exact ⟨fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key.1 i j), fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key.2 i j)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallinePeriodMatrixBcrisOfIsCrys
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Generic

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V] [IsDomain B]

private theorem exists_inv_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ M M' : Matrix (Fin d) (Fin d) B, M * M' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  classical
  obtain ⟨h1, -⟩ := finite_le₀ PD hf ρ
  have h2 : finrank K₀ ↥(DcrisK₀ PD ρ) = d := by
    rw [(isCrys_iff_finrank PD ρ).1 h, finrank_eq_card_basis v, Fintype.card_fin]
  let d₀ := Module.finBasisOfFinrankEq K₀ ↥(DcrisK₀ PD ρ) h2
  let b := (Algebra.TensorProduct.basis B d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))
  have hd : ∀ g i, sig PD ρ g (b i) = b i := by
    intro g i
    have : b i = (d₀ i : B ⊗[Qp] V) := by simp [b, comparison_tmul]
    rw [this]
    exact (mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g
  let e := Algebra.TensorProduct.basis B v
  have hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k =
      ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, sig_smul, map_smul, Finset.sum_apply', Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext k i
  rw [Matrix.mul_apply]
  change _ = e.repr (b i) k
  conv_rhs => rw [← hd g i, hrep]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply]

private theorem exists_period_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ (M M' : Matrix (Fin d) (Fin d) B) (A : Matrix (Fin d) (Fin d) K₀), M * M' = 1 ∧ IsUnit A.det ∧
      M.map PD.φ = M * A.map (algebraMap K₀ B) ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  obtain ⟨M, M', hM, hg⟩ := exists_inv_matrix PD hf hu ρ v h
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hinv : ∀ g, (M' * M.map PD.φ).map (PD.actB g) = M' * M.map PD.φ := by
    intro g
    set R := (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) with hR
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : M'.map (PD.actB g) = M' * R := by
      have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
        rw [← Matrix.mul_assoc, hg g]
      rw [h1, Matrix.mul_one] at this
      rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
    have h3 : R * (M.map PD.φ).map (PD.actB g) = M.map PD.φ := by
      have h4 : R.map PD.φ = R := by
        ext i j
        simp [hR]
      have h5 : (M.map PD.φ).map (PD.actB g) = (M.map (PD.actB g)).map PD.φ := by
        ext i j
        simp [PD.φ_comm]
      rw [h5, ← h4, ← Matrix.map_mul, hg g]
    rw [Matrix.map_mul, h2, Matrix.mul_assoc, h3]
  choose A hA using fun i j => PD.invB ((M' * M.map PD.φ) i j) fun g => congrFun (congrFun (hinv g) i) j
  have hA' : (Matrix.of A).map (algebraMap K₀ B) = M' * M.map PD.φ := by
    ext i j
    exact hA i j
  refine ⟨M, M', Matrix.of A, hM, ?_, by rw [hA', ← Matrix.mul_assoc, hM, Matrix.one_mul], hg⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 : ((Matrix.of A).map (algebraMap K₀ B)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2 : (M' * M.map PD.φ) * (M'.map PD.φ * M) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M.map PD.φ), ← Matrix.map_mul, hM,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hM']
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, ← hA', h1, zero_mul, Matrix.det_one] at h3
  exact zero_ne_one h3

end Generic

theorem UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → ∃ (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 ∧ IsUnit A.det ∧ M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) ∧ (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) := by
  intro l _ K V _ _ _ ρ d e h
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨M, M', A, h1, h2, h3, h4⟩ := exists_period_matrix ((PP l).PD K)
    (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K) ρ e h
  refine ⟨M, M', A, h1, h2, ?_, fun g => ?_⟩
  · rw [← h3]
    ext i j
    exact ((PP l).PD_φ K _).symm
  · have h5 : M.map ((PP l).actQ (g : GQ l)) = M.map (((PP l).PD K).actB g) := by
      ext i j
      exact ((PP l).PD_actB K g _).symm
    rw [h5, h4]
end

