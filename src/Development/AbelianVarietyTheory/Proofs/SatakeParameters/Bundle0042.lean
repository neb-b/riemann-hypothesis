module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankAddOfBiprod
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.SumJumps

theorem finrank_add_of_biprod {L M M₁ M₂ : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup M₁] [Module L M₁] [AddCommGroup M₂] [Module L M₂]
    (p₁ : M →ₗ[L] M₁) (p₂ : M →ₗ[L] M₂) (i₁ : M₁ →ₗ[L] M) (i₂ : M₂ →ₗ[L] M)
    (h11 : ∀ x, p₁ (i₁ x) = x) (h22 : ∀ x, p₂ (i₂ x) = x) (h12 : ∀ x, p₁ (i₂ x) = 0)
    (h21 : ∀ x, p₂ (i₁ x) = 0) (h : ∀ x, i₁ (p₁ x) + i₂ (p₂ x) = x)
    (S : Submodule L M) (S₁ : Submodule L M₁) (S₂ : Submodule L M₂)
    [Module.Finite L S₁] [Module.Finite L S₂]
    (a₁ : ∀ x ∈ S, p₁ x ∈ S₁) (a₂ : ∀ x ∈ S, p₂ x ∈ S₂) (b₁ : ∀ x ∈ S₁, i₁ x ∈ S)
    (b₂ : ∀ x ∈ S₂, i₂ x ∈ S) : finrank L S = finrank L S₁ + finrank L S₂ := by
  rw [← Module.finrank_prod]
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective
    ((p₁.restrict a₁).prod (p₂.restrict a₂)) ⟨?_, ?_⟩)
  · intro x y hxy
    have e1 : p₁ x = p₁ y := congrArg (fun z : S₁ × S₂ => (z.1 : M₁)) hxy
    have e2 : p₂ x = p₂ y := congrArg (fun z : S₁ × S₂ => (z.2 : M₂)) hxy
    apply Subtype.ext
    rw [← h x, ← h y, e1, e2]
  · rintro ⟨x, y⟩
    refine ⟨⟨i₁ x + i₂ y, S.add_mem (b₁ _ x.2) (b₂ _ y.2)⟩, ?_⟩
    ext
    · simp [h11, h12]
    · simp [h21, h22]

section Funct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

def ext1 (Qp : Type) [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (C : Type) [AddCommGroup C] [Module Qp C] (f : V →ₗ[LL] V') :
    V ⊗[Qp] C →ₗ[LL] V' ⊗[Qp] C :=
  AlgebraTensorModule.map f LinearMap.id

theorem ext1_comm {C C' : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup C'] [Module Qp C']
    (f : V →ₗ[LL] V') (r : V →ₗ[LL] V) (r' : V' →ₗ[LL] V') (hf : ∀ v, f (r v) = r' (f v))
    (u : C →ₗ[Qp] C') (x : V ⊗[Qp] C) :
    AlgebraTensorModule.map r' u (ext1 Qp C f x) = ext1 Qp C' f (AlgebraTensorModule.map r u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1, hf]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext1_comp_ext1 {C : Type} [AddCommGroup C] [Module Qp C]
    (f : V →ₗ[LL] V') (f' : V' →ₗ[LL] V'') (x : V ⊗[Qp] C) :
    ext1 Qp C f' (ext1 Qp C f x) = ext1 Qp C (f' ∘ₗ f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext1_id {C : Type} [AddCommGroup C] [Module Qp C] (x : V ⊗[Qp] C) :
    ext1 Qp C (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [ext1]

theorem ext1_zero {C : Type} [AddCommGroup C] [Module Qp C] (x : V ⊗[Qp] C) :
    ext1 Qp C (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem ext1_add {C : Type} [AddCommGroup C] [Module Qp C] (f f' : V →ₗ[LL] V') (x : V ⊗[Qp] C) :
    ext1 Qp C f x + ext1 Qp C f' x = ext1 Qp C (f + f') x := by
  simp [ext1, AlgebraTensorModule.map_add_left]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ Dcris PD ρ, ext1 Qp B f x ∈ Dcris PD ρ' := by
  intro x hx
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVB at this ⊢
  rw [ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem fildR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    ∀ x ∈ FildR PD ρ τ a, ext1 Qp BdR f x ∈ FildR PD ρ' τ a := by
  intro x hx
  simp only [FildR, DdRE, DdR, FilV, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero,
    LinearMap.mem_range] at hx ⊢
  obtain ⟨⟨h1, h2⟩, y, hy⟩ := hx
  refine ⟨⟨fun g => ?_, fun c => ?_⟩, ext1 Qp _ f y, ?_⟩
  · have := h1 g
    unfold actVdR at this ⊢
    rw [ext1_comm f (ρ g) (ρ' g) (hf g), this]
  · have := h2 c
    unfold mulVdR at this ⊢
    rw [ext1_comm f LinearMap.id LinearMap.id (fun _ => rfl), this, map_smul]
  · rw [ext1_comm f LinearMap.id LinearMap.id (fun _ => rfl), hy]

theorem finrank_add_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] (V' × V''))
    (S : Submodule LL (V ⊗[Qp] C)) (S₁ : Submodule LL (V' ⊗[Qp] C)) (S₂ : Submodule LL (V'' ⊗[Qp] C))
    [Module.Finite LL S₁] [Module.Finite LL S₂]
    (a₁ : ∀ x ∈ S, ext1 Qp C (LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) x ∈ S₁)
    (a₂ : ∀ x ∈ S, ext1 Qp C (LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, ext1 Qp C (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') x ∈ S)
    (b₂ : ∀ x ∈ S₂, ext1 Qp C (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') x ∈ S) :
    finrank LL S = finrank LL S₁ + finrank LL S₂ := by
  refine finrank_add_of_biprod _ _ _ _ ?_ ?_ ?_ ?_ ?_ S S₁ S₂ a₁ a₂ b₁ b₂
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_id (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_id (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_zero (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_zero (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1, ext1_comp_ext1, ext1_add]
    convert ext1_id (LL := LL) x
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      ← map_add]
    apply e.injective
    simp

variable {ρ'' : Representation LL G V''}

theorem equivariant_inl_inr_of_prod_equiv (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2)) :
    (∀ g v, (LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) (ρ g v) =
      ρ' g ((LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) (ρ g v) =
      ρ'' g ((LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') (ρ' g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') (ρ'' g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') v)) := by
  refine ⟨fun g v => by simp [he], fun g v => by simp [he], fun g v => ?_, fun g v => ?_⟩
  · apply e.injective
    rw [he]; simp
  · apply e.injective
    rw [he]; simp

theorem finite_fildR [Module.Finite LL (DdR PD ρ)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Module.Finite LL (FildR PD ρ τ a) :=
  Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) (inf_le_left.trans inf_le_left)

theorem multV_add (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2))
    [Module.Finite LL (DdR PD ρ')] [Module.Finite LL (DdR PD ρ'')] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a + multV PD ρ'' τ a := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant_inl_inr_of_prod_equiv e he
  have key : ∀ b, finrank LL (FildR PD ρ τ b) =
      finrank LL (FildR PD ρ' τ b) + finrank LL (FildR PD ρ'' τ b) := fun b => by
    haveI := finite_fildR PD (ρ := ρ') τ b
    haveI := finite_fildR PD (ρ := ρ'') τ b
    exact finrank_add_tensor e _ _ _ (fildR_map PD _ h1 τ b) (fildR_map PD _ h2 τ b)
      (fildR_map PD _ h3 τ b) (fildR_map PD _ h4 τ b)
  simp only [multV, key]
  push_cast
  ring

end Funct

end GlobalTheory.HTW.SumJumps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbedding
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem size_not_thick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  intro D L C g j hR hnt
  obtain ⟨-, hw100, hwη, hwb, hbT, -⟩ := hR
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρe : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  have hfl : (⌊(hcAt D g).e j⌋ : ℝ) = wj D (j.1 + 1) ρ := by
    rw [hw]
    show (⌊(D.hc ρ).e j⌋ : ℝ) = (((D.hc ρ).e j : ℚ) : ℝ)
    rw [hz, Int.floor_intCast]; push_cast; rfl
  rw [hfl]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb' : 0 < L.sc.b' := by linarith
  have hq : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hnt' : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρe]; exact hnt
  by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
    obtain ⟨a1, a2⟩ := L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm
    have a3 := L.bT_ge ⟨t, ht'⟩
    have a4 := hbT ⟨t, ht'⟩
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := L.win_thin _ (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hnt'⟩
    constructor <;> linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternal
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem isoSub_summand_of_isInternal {Γ L : Type} [Group Γ] [Field L] {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)) (hI : DirectSum.IsInternal Us)
    (hU : ∀ m, IsIrrSub τ (Us m)) (W : Submodule L (Fin a → L)) (hW : IsIrrSub τ W) :
    ∃ m, IsoSub τ W (Us m) := by
  classical
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.mulVecLin ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  have hTv : ∀ g v, T g v = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v := fun g v => rfl
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap Us) hI
  let P : ∀ m, (Fin a → L) →ₗ[L] Us m := fun m =>
    (DirectSum.component L (Fin n) (fun k => Us k) m).comp
      (e.symm : (Fin a → L) →ₗ[L] DirectSum (Fin n) fun k => Us k)
  have hstab : ∀ g k, ∀ v ∈ Us k, T g v ∈ Us k := fun g k v hv => (hU k).2.1 g v hv
  let φ : Γ → ∀ k, Us k →ₗ[L] Us k := fun g k => (T g).restrict (hstab g k)
  have hcomm : ∀ g (d : DirectSum (Fin n) fun k => Us k),
      DirectSum.coeLinearMap Us (DFinsupp.mapRange.linearMap (φ g) d) = T g (DirectSum.coeLinearMap Us d) := by
    intro g
    have : (DirectSum.coeLinearMap Us).comp (DFinsupp.mapRange.linearMap (φ g)) =
        (T g).comp (DirectSum.coeLinearMap Us) := by
      apply DirectSum.linearMap_ext
      intro k
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DFinsupp.mapRange.linearMap_apply]
      rw [show (DirectSum.of (fun i => Us i) k x) = DFinsupp.single k x from rfl]
      rw [show DFinsupp.mapRange.linearMap (φ g) (DFinsupp.single k x) = DFinsupp.single k (φ g k x) from
        DFinsupp.mapRange_single (hf := fun i => map_zero _)]
      rw [show (DFinsupp.single k ((φ g k) x) : DirectSum (Fin n) fun i => Us i) =
        DirectSum.of (fun i => Us i) k (φ g k x) from rfl]
      simp [DirectSum.coeLinearMap_of, φ]
      rw [show (DFinsupp.single k x : DirectSum (Fin n) fun i => Us i) = DirectSum.of (fun i => Us i) k x from rfl,
        DirectSum.coeLinearMap_of]
    intro d
    exact LinearMap.congr_fun this d
  have hequiv : ∀ g m v, (P m (T g v) : Fin a → L) = T g (P m v) := by
    intro g m v
    have h1 : e.symm (T g v) = DFinsupp.mapRange.linearMap (φ g) (e.symm v) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      show _ = DirectSum.coeLinearMap Us _
      rw [hcomm]
      congr 1
      exact (e.apply_symm_apply v).symm
    simp only [P, LinearMap.comp_apply, LinearEquiv.coe_coe, h1]
    simp only [← DirectSum.apply_eq_component, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply]
    rfl
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hW.1
  obtain ⟨m, hm⟩ : ∃ m, P m w ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw0
    have h0 : e.symm w = 0 := by
      ext k : 1
      have := h k
      simpa [P, ← DirectSum.apply_eq_component] using this
    have := e.apply_symm_apply w
    rw [h0, map_zero] at this
    exact this.symm
  refine ⟨m, ?_⟩
  have hKinv : IsInv τ (W ⊓ LinearMap.ker (P m)) := by
    rintro g v ⟨hvW, hvK⟩
    have hvK' : P m v = 0 := hvK
    refine ⟨hW.2.1 g v hvW, show P m _ = 0 from ?_⟩
    apply Subtype.ext
    rw [← hTv, hequiv, hvK']
    simp
  have hK : W ⊓ LinearMap.ker (P m) = ⊥ := by
    rcases hW.2.2 _ inf_le_left hKinv with h | h
    · exact h
    · exfalso
      have : w ∈ W ⊓ LinearMap.ker (P m) := by rw [h]; exact hwW
      exact hm this.2
  let R : Submodule L (Fin a → L) := (W.map (P m)).map (Us m).subtype
  have hRinv : IsInv τ R := by
    rintro g y ⟨y', ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨P m (T g v), ⟨T g v, hW.2.1 g v hv, rfl⟩, ?_⟩
    simp only [Submodule.coe_subtype]
    rw [hequiv, hTv]
  have hR : R = Us m := by
    rcases (hU m).2.2 R (Submodule.map_subtype_le _ _) hRinv with h | h
    · exfalso
      have : ((P m w : Us m) : Fin a → L) ∈ R := ⟨P m w, ⟨w, hwW, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hm (Subtype.ext this)
    · exact h
  let f : W →ₗ[L] Us m := (P m).comp W.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have : (x : Fin a → L) ∈ W ⊓ LinearMap.ker (P m) := ⟨x.2, hx⟩
    rw [hK, Submodule.mem_bot] at this
    exact (Submodule.mem_bot L).2 (Subtype.ext this)
  have hsurj : Function.Surjective f := by
    intro u
    have hu : (u : Fin a → L) ∈ R := by rw [hR]; exact u.2
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := hu
    exact ⟨⟨v, hv⟩, Subtype.ext hy⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun g v h => ?_⟩
  simp only [LinearEquiv.ofBijective_apply, f, LinearMap.comp_apply, Submodule.coe_subtype]
  have := hequiv g m (v : Fin a → L)
  rw [hTv, hTv] at this
  exact this

end GlobalTheory.SplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct
open TensorProduct

noncomputable section

namespace GlobalTheory.HTW

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem algebraTensorModule_map_id_eq_rTensor (f : V →ₗ[LL] V') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = (f.restrictScalars Qp).rTensor BdR x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem comap_ker_sub_eq_ker_sub_of_injective_intertwining {M M' : Type} [AddCommGroup M] [Module LL M] [AddCommGroup M'] [Module LL M']
    (F : M →ₗ[LL] M') (hF : Function.Injective F) (A B : M →ₗ[LL] M) (A' B' : M' →ₗ[LL] M')
    (hA : ∀ x, A' (F x) = F (A x)) (hB : ∀ x, B' (F x) = F (B x)) :
    (LinearMap.ker (A' - B')).comap F = LinearMap.ker (A - B) := by
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, hA, hB,
    ← map_sub]
  exact map_eq_zero_iff F hF

private theorem mem_filV_iff_of_isScalarTower {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (a : ℤ) (y : W ⊗[Qp] BdR) :
    y ∈ FilV PD (LL := LL) (V := W) a ↔ (((PD.Fil a).restrictScalars Qp).mkQ.lTensor W) y = 0 := by
  have e : ∀ z, AlgebraTensorModule.map (LinearMap.id : W →ₗ[LL] W) ((PD.Fil a).restrictScalars Qp).subtype z =
      (((PD.Fil a).restrictScalars Qp).subtype.lTensor W) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [← LinearMap.mem_ker, lTensor_mkQ, FilV, LinearMap.mem_range, LinearMap.mem_range]
  simp only [e]

private theorem filV_comap_tensorMap_of_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) (a : ℤ) :
    (FilV PD (LL := LL) (V := V') a).comap (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FilV PD (LL := LL) (V := V) a := by
  ext x
  rw [Submodule.mem_comap, mem_filV_iff_of_isScalarTower, mem_filV_iff_of_isScalarTower, algebraTensorModule_map_id_eq_rTensor]
  have hc : ((PD.Fil a).restrictScalars Qp).mkQ.lTensor V' ((f.restrictScalars Qp).rTensor BdR x) =
      (f.restrictScalars Qp).rTensor _ (((PD.Fil a).restrictScalars Qp).mkQ.lTensor V x) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [hc]

  exact map_eq_zero_iff _ (Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars Qp) hf)

private theorem injective_algebraTensorModule_map_id_of_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  intro x y hxy
  rw [algebraTensorModule_map_id_eq_rTensor, algebraTensorModule_map_id_eq_rTensor] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars Qp) hf hxy

private theorem ddRE_comap_tensorMap_eq_of_injective_equivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) :
    (DdRE PD ρ' τ).comap (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) = DdRE PD ρ τ := by
  have hF := injective_algebraTensorModule_map_id_of_injective f hf (Qp := Qp) (BdR := BdR)
  rw [DdRE, DdRE, Submodule.comap_inf, DdR, DdR, Submodule.comap_iInf, Submodule.comap_iInf]
  congr 1
  · refine iInf_congr fun g => comap_ker_sub_eq_ker_sub_of_injective_intertwining _ hF _ _ _ _ ?_ (fun x => rfl)
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, he]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · refine iInf_congr fun c => comap_ker_sub_eq_ker_sub_of_injective_intertwining _ hF _ _ _ _ ?_ ?_
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    · intro x
      simp

theorem FildR_eq_comap (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FildR PD ρ' τ a).comap
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  rw [FildR, FildR, Submodule.comap_inf, ddRE_comap_tensorMap_eq_of_injective_equivariant PD ρ ρ' f hf he τ, filV_comap_tensorMap_of_injective PD f hf a]

end

theorem isJumpV_of_injective : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V'), Function.Injective f → (∀ g v, f (ρ g v) = ρ' g (f v)) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD ρ τ a → IsJumpV PD ρ' τ a := by
  intros
  rename_i ρ ρ' f hf he τ a hJ
  unfold IsJumpV at hJ ⊢
  intro h
  apply hJ
  rw [FildR_eq_comap _ _ _ _ hf he, FildR_eq_comap _ _ _ _ hf he, h]

end GlobalTheory.HTW
end
end

