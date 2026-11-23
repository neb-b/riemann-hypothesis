module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0093

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubEigenTailHecke
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep PositivityTheory.Rg.BcB.F.Tail.PExp GlobalTheory.CompanionTheory.SubEig

namespace GlobalTheory.CompanionTheory.SubEigIrr

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    simpa using h k.1 k.2

theorem hkS_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    hkS ρ K f v = ∑ q ∈ hf.toFinset, f q.out • ρ q.out v := by
  unfold hkS
  refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
  simp only [Set.Finite.coe_toFinset]
  intro h0
  exact hq (by simp [h0])

theorem hkS_map {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : Representation.IntertwiningMap ρ σ)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    φ (hkS ρ K f v) = hkS σ K f (φ v) := by
  rw [hkS_eq_sum ρ K f hf, hkS_eq_sum σ K f hf]
  show φ.toLinearMap _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul]
  congr 1
  exact φ.isIntertwining _ _ q.out v

theorem subEig : SubEig := by
  intro G _ _ _ V _ _ ρ hρ K X f e hfin u hu hu0 heig
  let S := cyc ρ u
  let u' : S.toSubmodule := ⟨u, mem_cyc ρ u⟩
  have hu' : u' ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  obtain ⟨T, huT, hmax⟩ := exists_max_avoid S.toRepresentation hu'
  have hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (S.toRepresentation g) :=
    fun g _ hv => T.apply_mem_toSubmodule g hv
  let τ := S.toRepresentation.quotient T.toSubmodule hst
  have hirr : τ.IsIrreducible := quot_irred S.toRepresentation T huT hmax (cyc_gen ρ u) hst
  have hsm : IsSmooth τ := smooth_quot (smooth_sub hρ S) _ hst
  let p := mkI S.toRepresentation T.toSubmodule hst
  let w : S.toSubmodule ⧸ T.toSubmodule := p u'
  have hw0 : w ≠ 0 := by
    show (Submodule.Quotient.mk u' : S.toSubmodule ⧸ T.toSubmodule) ≠ 0
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hsub : IsSubquotient τ ρ := by
    refine ⟨S, p, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨x, rfl⟩
  refine ⟨⟨_, τ, hsm, hirr⟩, hsub, w, ?_, hw0, fun x => ?_⟩
  · refine mem_fixed_iff.2 fun k hk => ?_
    have hh' : S.toRepresentation k u' = u' := Subtype.ext (mem_fixed_iff.1 hu k hk)
    have := p.isIntertwining _ _ k u'
    rw [hh'] at this
    exact this.symm
  · have h1 : hkS S.toRepresentation K (f x) u' = e x • u' := by
      apply Subtype.ext
      have := hkS_map (inclI S) K (f x) (hfin x) u'
      exact this.trans (heig x)
    have := hkS_map p K (f x) (hfin x) u'
    rw [h1, map_smul] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SubEigIrr

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ W →ₗ[ℂ] V where
  toFun l := TensorProduct.rid ℂ V (LinearMap.lTensor V l v)
  map_add' l m := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [add_smul]
    | add s t hs ht =>
      simp only [map_add (f := _)] at hs ht ⊢
      rw [hs, ht]; abel
  map_smul' c l := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_smul]
    | add s t hs ht =>
      simp only [map_add (f := _), RingHom.id_apply, smul_add] at hs ht ⊢
      rw [hs, ht]

@[simp] theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ W) :
    contr (a ⊗ₜ[ℂ] b) l = l b • a := by
  show TensorProduct.rid ℂ V (LinearMap.lTensor V l (a ⊗ₜ[ℂ] b)) = l b • a
  rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr v l = TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := rfl

theorem contr_add (s t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (s + t) l = contr s l + contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_add (f := _)]

theorem contr_smul (c : ℂ) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (c • t) l = c • contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_smul]

theorem contr_map (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (TensorProduct.map f g t) l = f (contr t (l ∘ₗ g)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, GlobalTheory.CompanionTheory.TensContr.contr_apply]
  | tmul a b =>
    rw [TensorProduct.map_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
      LinearMap.comp_apply, map_smul]
  | add s t hs ht =>
    rw [map_add (f := _), GlobalTheory.CompanionTheory.TensContr.contr_add, GlobalTheory.CompanionTheory.TensContr.contr_add, hs, ht, map_add (f := _)]

theorem exists_finset_contr (v : V ⊗[ℂ] W) :
    ∃ s : Finset V, ∀ l, contr v l ∈ Submodule.span ℂ (s : Set V) := by
  classical
  induction v using TensorProduct.induction_on with
  | zero =>
    refine ⟨∅, fun l => ?_⟩
    simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_zero]
    exact Submodule.zero_mem _
  | tmul a b =>
    refine ⟨{a}, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    refine ⟨S ∪ T, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_add]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ (hS l)) (Submodule.span_mono ?_ (hT l))
    · exact_mod_cast Finset.subset_union_left
    · exact_mod_cast Finset.subset_union_right

theorem finiteDimensional_range_contr (v : V ⊗[ℂ] W) :
    FiniteDimensional ℂ (LinearMap.range (contr v)) := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.TensContr.exists_finset_contr v
  haveI := FiniteDimensional.span_finset ℂ s
  have hle : LinearMap.range (GlobalTheory.CompanionTheory.TensContr.contr v) ≤ Submodule.span ℂ (s : Set V) := by
    rintro _ ⟨l, rfl⟩
    exact hs l
  exact Submodule.finiteDimensional_of_le hle

theorem eq_zero_of_contr (v : V ⊗[ℂ] W) (h : ∀ l, contr v l = 0) : v = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have key : ∀ (t : V ⊗[ℂ] W) i, e t i = GlobalTheory.CompanionTheory.TensContr.contr t (b.coord i) := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, GlobalTheory.CompanionTheory.TensContr.contr_apply]
    | tmul a w =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
        Module.Basis.coord_apply]
    | add s t hs ht =>
      rw [map_add (f := _), Finsupp.add_apply, hs, ht, GlobalTheory.CompanionTheory.TensContr.contr_add]
  have he : e v = 0 := by
    ext i
    rw [key, h, Finsupp.coe_zero, Pi.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp he

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {X Y : Type*}

theorem exists_contr_eigen [Nonempty Y]
    (A : X → V →ₗ[ℂ] V) (B : Y → W →ₗ[ℂ] W) (lam : X → ℂ) (mu : Y → ℂ)
    (hlam : ∀ x, lam x ≠ 0) (hmu : ∀ y, mu y ≠ 0)
    (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (heig : ∀ x y, TensorProduct.map (A x) (B y) v = (lam x * mu y) • v) :
    ∃ (l : Module.Dual ℂ W) (c : ℂ), c ≠ 0 ∧
      TensorProduct.rid ℂ V (LinearMap.lTensor V l v) ≠ 0 ∧
      ∀ x, A x (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
        (c * lam x) • TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := by
  simp only [← GlobalTheory.CompanionTheory.TensContr.contr_apply]
  set φ := GlobalTheory.CompanionTheory.TensContr.contr v with hφ
  have hne : ∃ l, φ l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (GlobalTheory.CompanionTheory.TensContr.eq_zero_of_contr v hcon)
  obtain ⟨l₀, hl₀⟩ := hne
  by_cases hX : IsEmpty X
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun x => (hX.false x).elim⟩
  obtain ⟨x₀⟩ := not_isEmpty_iff.mp hX
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have rel : ∀ x l, A x (φ (l ∘ₗ B y₀)) = (lam x * mu y₀) • φ l := by
    intro x l
    rw [hφ, ← GlobalTheory.CompanionTheory.TensContr.contr_map, heig, GlobalTheory.CompanionTheory.TensContr.contr_smul]
  let U := LinearMap.range φ
  haveI : FiniteDimensional ℂ U := GlobalTheory.CompanionTheory.TensContr.finiteDimensional_range_contr v
  let U' := LinearMap.range (φ ∘ₗ (B y₀).dualMap)
  have hU'U : U' ≤ U := LinearMap.range_comp_le_range _ _
  have hmapU' : U ≤ Submodule.map (A x₀) U' := by
    rintro _ ⟨l, rfl⟩
    have hk : lam x₀ * mu y₀ ≠ 0 := mul_ne_zero (hlam x₀) (hmu y₀)
    refine ⟨φ (((lam x₀ * mu y₀)⁻¹ • l) ∘ₗ B y₀), ⟨(lam x₀ * mu y₀)⁻¹ • l, ?_⟩, ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.dualMap_apply']
    · rw [rel, map_smul, smul_smul, mul_inv_cancel₀ hk, one_smul]
  haveI : FiniteDimensional ℂ U' := Submodule.finiteDimensional_of_le hU'U
  have hUU' : U' = U := by
    refine Submodule.eq_of_le_of_finrank_le hU'U ?_
    calc Module.finrank ℂ U ≤ Module.finrank ℂ (Submodule.map (A x₀) U') :=
          Submodule.finrank_mono hmapU'
      _ ≤ Module.finrank ℂ U' := Submodule.finrank_map_le _ _
  have hrepr : ∀ u ∈ U, ∃ l, u = φ (l ∘ₗ B y₀) := by
    intro u hu
    rw [← hUU'] at hu
    obtain ⟨l, rfl⟩ := hu
    exact ⟨l, by rw [LinearMap.comp_apply, LinearMap.dualMap_apply']⟩
  have hmaps : ∀ x, ∀ u ∈ U, A x u ∈ U := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel]
    exact Submodule.smul_mem _ _ ⟨l, rfl⟩
  have hprop : ∀ x, ∀ u ∈ U, A x u = (lam x * (lam x₀)⁻¹) • A x₀ u := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel, rel, smul_smul]
    congr 1
    field_simp [hlam x₀, hmu y₀]
  let T : Module.End ℂ U := (A x₀).restrict (hmaps x₀)
  have hsurj : Function.Surjective T := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw, hwu⟩ := hmapU' hu
    exact ⟨⟨w, hU'U hw⟩, Subtype.ext (by simpa [T, LinearMap.restrict_apply] using hwu)⟩
  have hinj : Function.Injective T := LinearMap.injective_iff_surjective.mpr hsurj
  haveI : Nontrivial U := nontrivial_of_ne (⟨φ l₀, ⟨l₀, rfl⟩⟩ : U) 0
    (fun h => hl₀ (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue T
  obtain ⟨u, hu⟩ := ht.exists_hasEigenvector
  have hTu := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hTu
    exact hu0 (hinj (by rw [hTu, map_zero]))
  have hAu : A x₀ u = t • (u : V) := by
    have := congrArg Subtype.val hTu
    simpa [T, LinearMap.restrict_apply] using this
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, t * (lam x₀)⁻¹, mul_ne_zero ht0 (inv_ne_zero (hlam x₀)), ?_, fun x => ?_⟩
  · rw [hl]
    exact fun h => hu0 (Subtype.ext h)
  · rw [hl, hprop x _ u.2, hAu, smul_smul]
    congr 1
    ring

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

theorem tensEig : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  intro V W X Y _ _ _ _ A B lam mu v hv hY hlam hmu heig
  exact GlobalTheory.CompanionTheory.TensContr.exists_contr_eigen A B lam mu hlam hmu v hv heig

end GlobalTheory.CompanionTheory.TensContr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensEigSecond

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ V →ₗ[ℂ] W where
  toFun l := TensorProduct.lid ℂ W (LinearMap.rTensor W l v)
  map_add' l m := by simp [LinearMap.rTensor_add]
  map_smul' c l := by simp [LinearMap.rTensor_smul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    contr v l = TensorProduct.lid ℂ W (LinearMap.rTensor W l v) := rfl

theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ V) : contr (a ⊗ₜ[ℂ] b) l = l a • b := by
  simp [contr_apply]

theorem contr_add (v w : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (v + w) l = contr v l + contr w l := by
  simp [contr_apply]

theorem contr_smul (c : ℂ) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (c • v) l = c • contr v l := by
  simp [contr_apply]

theorem contr_map (A : Module.End ℂ V) (B : Module.End ℂ W) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    B (contr v (l ∘ₗ A)) = contr (TensorProduct.map A B v) l := by
  induction v using TensorProduct.induction_on with
  | zero => simp [contr_apply]
  | tmul a b => simp [contr_tmul]
  | add x y hx hy => simp only [map_add (f := _), contr_add, hx, hy]

theorem exists_finiteDimensional (v : V ⊗[ℂ] W) :
    ∃ T : Submodule ℂ W, FiniteDimensional ℂ T ∧ ∀ l, contr v l ∈ T := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, fun l => by simp [contr_apply]⟩
  | tmul a b =>
    exact ⟨ℂ ∙ b, inferInstance, fun l => by
      rw [contr_tmul]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)⟩
  | add x y hx hy =>
    obtain ⟨T, hT, h⟩ := hx
    obtain ⟨T', hT', h'⟩ := hy
    exact ⟨T ⊔ T', inferInstance, fun l => by
      rw [contr_add]; exact Submodule.add_mem_sup (h l) (h' l)⟩

theorem exists_contr_ne_zero {v : V ⊗[ℂ] W} (hv : v ≠ 0) : ∃ l, contr v l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hv
  let b := Module.Free.chooseBasis ℂ V
  have key : ∀ (w : V ⊗[ℂ] W) i, TensorProduct.equivFinsuppOfBasisLeft b w i = contr w (b.coord i) := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp [contr_apply]
    | tmul a c => simp [contr_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, contr_add, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := W) b).injective
  ext i : 1
  rw [key, hcon]
  simp

theorem core {Y : Type} (A : Module.End ℂ V) (B : Y → Module.End ℂ W) (a : ℂ) (ha : a ≠ 0) (mu : Y → ℂ)
    (hmu : ∀ y, mu y ≠ 0) (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (h : ∀ y, TensorProduct.map A (B y) v = (a * mu y) • v) :
    ∃ (l : Module.Dual ℂ V) (c : ℂ), c ≠ 0 ∧ contr v l ≠ 0 ∧
      ∀ y, B y (contr v l) = (c * mu y) • contr v l := by
  obtain ⟨l₀, hl₀⟩ := exists_contr_ne_zero hv
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun y => isEmptyElim y⟩
  have key : ∀ y l, B y (contr v (l ∘ₗ A)) = (a * mu y) • contr v l := by
    intro y l
    rw [contr_map, h, contr_smul]
  let S := LinearMap.range (contr v)
  obtain ⟨T, hT, hST⟩ := exists_finiteDimensional v
  have hSfd : FiniteDimensional ℂ S :=
    Submodule.finiteDimensional_of_le (S₂ := T) (by rintro _ ⟨l, rfl⟩; exact hST l)
  let b : Module.Dual ℂ V →ₗ[ℂ] W := contr v ∘ₗ A.dualMap
  have hb : ∀ l, b l = contr v (l ∘ₗ A) := fun l => rfl
  let S' := LinearMap.range b
  have hle : S' ≤ S := LinearMap.range_comp_le_range _ _
  have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  have hne : a * mu y0 ≠ 0 := mul_ne_zero ha (hmu y0)
  have hmap : S ≤ S'.map (B y0) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨b ((a * mu y0)⁻¹ • l), ⟨_, rfl⟩, ?_⟩
    rw [hb, key, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hfr : Module.finrank ℂ S ≤ Module.finrank ℂ S' :=
    (Submodule.finrank_mono hmap).trans (Submodule.finrank_map_le _ _)
  have hSS' : S' = S := Submodule.eq_of_le_of_finrank_le hle hfr
  have hrep : ∀ s ∈ S, ∃ l, s = contr v (l ∘ₗ A) := by
    intro s hs
    rw [← hSS'] at hs
    obtain ⟨l, rfl⟩ := hs
    exact ⟨l, hb l⟩
  have hform : ∀ s ∈ S, ∀ y, mu y0 • B y s = mu y • B y0 s := by
    intro s hs y
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key, key, smul_smul, smul_smul]
    congr 1
    ring
  have hinv : ∀ s ∈ S, B y0 s ∈ S := by
    intro s hs
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key]
    exact S.smul_mem _ ⟨l, rfl⟩
  let R : Module.End ℂ S := (B y0).restrict hinv
  have hsurj : Function.Surjective R := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, rfl⟩ := hmap hs
    exact ⟨⟨t, hle ht⟩, rfl⟩
  have hinj : Function.Injective R := LinearMap.injective_iff_surjective.mpr hsurj
  have hnt : Nontrivial S :=
    ⟨⟨⟨contr v l₀, ⟨l₀, rfl⟩⟩, 0, fun e => hl₀ (congrArg Subtype.val e)⟩⟩
  obtain ⟨γ, hγ⟩ := Module.End.exists_eigenvalue R
  obtain ⟨u, hu⟩ := hγ.exists_hasEigenvector
  have hRu : R u = γ • u := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    apply hu0
    apply hinj
    rw [hRu]
    simp
  have hBu : B y0 (u : W) = γ • (u : W) := congrArg Subtype.val hRu
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, γ / mu y0, div_ne_zero hγ0 (hmu y0), ?_, fun y => ?_⟩
  · rw [hl]
    exact fun e => hu0 (Subtype.ext e)
  · rw [hl]
    have e := hform u u.2 y
    rw [hBu] at e
    have e2 : B y (u : W) = (mu y0)⁻¹ • mu y0 • B y (u : W) := by
      rw [smul_smul, inv_mul_cancel₀ (hmu y0), one_smul]
    rw [e2, e, smul_smul, smul_smul]
    congr 1
    field_simp [hmu y0]

theorem tensEigR : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  intro V W X Y _ _ _ _ A B lam mu v hv hX hlam hmu hAB
  obtain ⟨x0⟩ := hX
  exact core (A x0) B (lam x0) (hlam x0) mu hmu v hv (hAB x0)

end GlobalTheory.CompanionTheory.TensEigSecond
end

