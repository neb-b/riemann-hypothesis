module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProduct
section
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology

namespace GlobalTheory.JR.WeilProd.TensorTest

section Basic
variable {X : Type} [TopologicalSpace X]

theorem isTest_of_lc {g : X → ℂ} (hg : IsLocallyConstant g) {K : Set X} (hK : IsCompact K)
    (hs : Function.support g ⊆ K) : IsTest g := by
  refine ⟨hg, ?_⟩
  have hcl : IsClosed (Function.support g) := by
    show IsClosed {x | g x ≠ 0}
    exact (hg.isOpen_fiber 0).isClosed_compl
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hs

theorem isTest_zero : IsTest (0 : X → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isTest_add {f f' : X → ℂ} (hf : IsTest f) (hf' : IsTest f') : IsTest (f + f') :=
  ⟨hf.1.add hf'.1, hf.2.add hf'.2⟩

theorem isTest_smul (c : ℂ) {f : X → ℂ} (hf : IsTest f) : IsTest (c • f) :=
  ⟨hf.1.comp (c * ·), hf.2.smul_left⟩

theorem isTest_sum {ι : Type} (s : Finset ι) (F : ι → X → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (∑ j ∈ s, F j) := by
  classical
  revert hF
  refine Finset.induction_on s (fun _ => by simpa using (isTest_zero : IsTest (0 : X → ℂ))) ?_
  intro a s ha ih hF
  rw [Finset.sum_insert ha]
  exact isTest_add (hF a (Finset.mem_insert_self a s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem map_zero {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) : W g 0 = 0 := by
  have := hW.2.2.2 g 1 0 0 isTest_zero isTest_zero
  simpa using this

theorem map_sum {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j ∈ s, IsTest (f j)) :
    W g (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • W g (f j) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => by simp [map_zero hW g]) ?_
  intro a s ha ih hf
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  have hs : IsTest (∑ j ∈ s, c j • f j) :=
    isTest_sum s _ fun j hj => isTest_smul _ (hf j (Finset.mem_insert_of_mem hj))
  rw [hW.2.2.2 g (c a) (f a) _ (hf a (Finset.mem_insert_self a s)) hs,
    ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end Basic

section Prod
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isTest_mul_prod {a : X → ℂ} {b : Y → ℂ} (ha : IsTest a) (hb : IsTest b) :
    IsTest (fun p : X × Y => a p.1 * b p.2) := by
  refine isTest_of_lc ?_ (ha.2.isCompact.prod hb.2.isCompact) ?_
  · exact IsLocallyConstant.comp₂ (ha.1.comp_continuous continuous_fst) (hb.1.comp_continuous continuous_snd)
      (fun x y => x * y)
  · intro p hp
    have h1 : a p.1 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : b p.2 ≠ 0 := right_ne_zero_of_mul hp
    exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

theorem isTest_fibre {f : X × Y → ℂ} (hf : IsTest f) (u : X) : IsTest (fun v => f (u, v)) := by
  refine isTest_of_lc (hf.1.comp_continuous (continuous_const.prodMk continuous_id)) (hf.2.isCompact.image continuous_snd) ?_
  intro v hv
  exact ⟨(u, v), subset_tsupport _ hv, rfl⟩

theorem isLocallyConstant_curry {f : X × Y → ℂ} (hf : IsTest f) :
    IsLocallyConstant (fun u => fun v => f (u, v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hK : IsCompact (Prod.snd '' tsupport f) := hf.2.isCompact.image continuous_snd
  have hev : ∀ᶠ u in 𝓝 u₀, ∀ v ∈ Prod.snd '' tsupport f, f (u, v) = f (u₀, v) := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro y _
    have h1 : ∀ᶠ z in 𝓝 (u₀, y), f z = f (u₀, y) := ((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y)
    have hc : Continuous (fun z : X × Y => (u₀, z.2)) := (continuous_const.prodMk continuous_id).comp continuous_snd
    have ht : Tendsto (fun z : X × Y => (u₀, z.2)) (𝓝 (u₀, y)) (𝓝 (u₀, y)) := hc.continuousAt
    have h2 : ∀ᶠ z in 𝓝 (u₀, y), f (u₀, z.2) = f (u₀, y) :=
      ht.eventually (((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y))
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  filter_upwards [hev] with u hu
  funext v
  by_cases hv : v ∈ Prod.snd '' tsupport f
  · exact hu v hv
  · have hA : (u, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    have hB : (u₀, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isTest_sum_fn {ι : Type} (s : Finset ι) (F : ι → X × Y → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (fun p => ∑ j ∈ s, F j p) := by
  have := isTest_sum s F hF
  rwa [Finset.sum_fn] at this

theorem decomp {f : X × Y → ℂ} (hf : IsTest f) :
    ∃ (s : Finset (Y → ℂ)) (a : (Y → ℂ) → X → ℂ), (∀ φ ∈ s, IsTest (a φ)) ∧ (∀ φ ∈ s, IsTest φ) ∧
      ∀ p : X × Y, f p = ∑ φ ∈ s, a φ p.1 * φ p.2 := by
  classical
  have hF : IsLocallyConstant (fun u => fun v => f (u, v)) := isLocallyConstant_curry hf
  have hK₁ : IsCompact (Prod.fst '' tsupport f) := hf.2.isCompact.image continuous_fst
  have hzero : ∀ u, u ∉ Prod.fst '' tsupport f → (fun v => f (u, v)) = 0 := by
    intro u hu; funext v
    by_contra h
    exact hu ⟨(u, v), subset_tsupport _ h, rfl⟩
  have hfin : (Set.range (fun u => fun v => f (u, v))).Finite := by
    have : CompactSpace (Prod.fst '' tsupport f) := isCompact_iff_compactSpace.1 hK₁
    have h1 : (Set.range ((fun u => fun v => f (u, v)) ∘ ((↑) : Prod.fst '' tsupport f → X))).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ Prod.fst '' tsupport f
    · exact Or.inl ⟨⟨u, hu⟩, rfl⟩
    · exact Or.inr (hzero u hu)
  refine ⟨hfin.toFinset.erase 0, fun φ u => if (fun v => f (u, v)) = φ then 1 else 0, ?_, ?_, ?_⟩
  · intro φ hφ
    have hφ0 : φ ≠ 0 := Finset.ne_of_mem_erase hφ
    refine isTest_of_lc (hF.comp fun ψ => if ψ = φ then (1:ℂ) else 0) hK₁ ?_
    intro u hu
    by_contra hK
    apply hu
    show (if (fun v => f (u, v)) = φ then (1:ℂ) else 0) = 0
    rw [hzero u hK, if_neg (Ne.symm hφ0)]
  · intro φ hφ
    obtain ⟨u, rfl⟩ : φ ∈ Set.range (fun u => fun v => f (u, v)) :=
      (hfin.mem_toFinset).1 (Finset.mem_of_mem_erase hφ)
    exact isTest_fibre hf u
  · rintro ⟨u, v⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have h0 : (fun v => f (u, v)) = 0 := by
        by_contra h0
        exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨u, rfl⟩⟩)
      exact congrFun h0 v

theorem tensorRep_eq {G H : Type} [Group G] [Group H] {W₁ : G → (X → ℂ) → X → ℂ}
    {W₂ : H → (Y → ℂ) → Y → ℂ} (hW₁ : IsTestRep W₁) (hW₂ : IsTestRep W₂) {ι : Type} (s : Finset ι)
    (A : ι → X → ℂ) (B : ι → Y → ℂ) (hA : ∀ j ∈ s, IsTest (A j)) (hB : ∀ j ∈ s, IsTest (B j))
    (f : X × Y → ℂ) (hf : ∀ p : X × Y, f p = ∑ j ∈ s, A j p.1 * B j p.2) (gh : G × H) :
    tensorRep W₁ W₂ gh f = fun p => ∑ j ∈ s, W₁ gh.1 (A j) p.1 * W₂ gh.2 (B j) p.2 := by
  funext p
  have h1 : ∀ u, (fun v => f (u, v)) = ∑ j ∈ s, A j u • B j := by
    intro u; funext v; rw [hf (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
  have h2 : (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) = ∑ j ∈ s, W₂ gh.2 (B j) p.2 • A j := by
    funext u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1 u, map_sum hW₂ gh.2 s _ _ hB, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tensorRep_apply, h2, map_sum hW₁ gh.1 s _ _ hA, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul, mul_comm]

end Prod
end GlobalTheory.JR.WeilProd.TensorTest

namespace GlobalTheory.JR.WeilProd
open TensorTest

theorem isTestRep_tensorRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  intro hW₁ hW₂
  have hslice : ∀ f : X × Y → ℂ, IsTest f → ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
    intro f hf h y
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have e : (fun u => W₂ h (fun v => f (u, v)) y) = ∑ φ ∈ s, W₂ h φ y • a φ := by
      funext u
      have h1 : (fun v => f (u, v)) = ∑ φ ∈ s, a φ u • φ := by
        funext v; rw [hfs (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum hW₂ h s (fun φ => a φ u) (fun φ => φ) hb, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp [smul_eq_mul, mul_comm]
    rw [e]
    exact isTest_sum s _ fun φ hφ => isTest_smul _ (ha φ hφ)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun f hf => ⟨isTest_fibre hf, hslice f hf⟩⟩
  · intro gh f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh]
    exact isTest_sum_fn s _ fun φ hφ => isTest_mul_prod (hW₁.1 _ _ (ha φ hφ)) (hW₂.1 _ _ (hb φ hφ))
  · intro f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs 1]
    funext p
    rw [hfs p]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_one, Prod.snd_one]
    rw [hW₁.2.1 _ (ha φ hφ), hW₂.2.1 _ (hb φ hφ)]
  · intro gh gh' f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have hs' : ∀ p, tensorRep W₁ W₂ gh' f p = ∑ φ ∈ s, W₁ gh'.1 (a φ) p.1 * W₂ gh'.2 φ p.2 := fun p => by
      rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh']
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs (gh * gh'),
      tensorRep_eq hW₁ hW₂ s (fun φ => W₁ gh'.1 (a φ)) (fun φ => W₂ gh'.2 φ) (fun φ hφ => hW₁.1 _ _ (ha φ hφ))
        (fun φ hφ => hW₂.1 _ _ (hb φ hφ)) _ hs' gh]
    funext p
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hW₁.2.2.1 _ _ _ (ha φ hφ), hW₂.2.2.1 _ _ _ (hb φ hφ)]
  · intro gh c f f' hf hf'
    funext p
    have e2 : (fun u => W₂ gh.2 (fun v => (c • f + f') (u, v)) p.2) =
        c • (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) + (fun u => W₂ gh.2 (fun v => f' (u, v)) p.2) := by
      funext u
      show W₂ gh.2 (c • (fun v => f (u, v)) + fun v => f' (u, v)) p.2 = _
      rw [hW₂.2.2.2 gh.2 c _ _ (isTest_fibre hf u) (isTest_fibre hf' u)]
      rfl
    rw [tensorRep_apply, e2, hW₁.2.2.2 gh.1 c _ _ (hslice f hf _ _) (hslice f' hf' _ _)]
    rfl

end GlobalTheory.JR.WeilProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacStages

section Rel

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def relUnipD (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => unipRad k (f i)

def relEmbD (f : ∀ i, (Σ j, c i j) ≃ m i) : (∀ i, Levi k (c i)) →* Levi k m :=
  MonoidHom.pi fun i => (leviEmb k (f i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relEmbD_apply (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) (i : α) :
    relEmbD k f g i = leviEmb k (f i) (g i) := rfl

theorem relEmbD_mem_normalizer (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) :
    relEmbD k f g ∈ Subgroup.normalizer (relUnipD k f : Set (Levi k m)) :=
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun i _ =>
    Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (f i) (g i)) (u i)

def relDeltaHalfD (c : ∀ i, β i → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ i, Levi k (c i)) →* ℂˣ :=
  ∏ i, (deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relDeltaHalfD_apply (g : ∀ i, Levi k (c i)) :
    relDeltaHalfD k c g = ∏ i, deltaHalf k (c i) (g i) := by
  simp [relDeltaHalfD, MonoidHom.finsetProd_apply]

variable {k}

def relJacD (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (∀ i, Levi k (c i)) (Jacquet ρ (relUnipD k f)) :=
  twist (jacquet ρ (relUnipD k f) (relEmbD k f) (relEmbD_mem_normalizer k f)) (relDeltaHalfD k c)⁻¹

theorem relJacD_mk (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJacD f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalfD k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmbD k f g) v) := rfl

end Rel

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def refinePlace {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun p : Σ a, Fin (t a) => Fin (d' p.1 p.2)) finSigmaFinEquiv.symm).trans
    ((Equiv.sigmaAssoc fun a b => Fin (d' a b)).trans ((Equiv.sigmaCongrRight e').trans e))

theorem refinePlace_apply {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a))
    (i : Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) :
    refinePlace e e' ⟨c, i⟩ =
      e ⟨(finSigmaFinEquiv.symm c).1, e' _ ⟨(finSigmaFinEquiv.symm c).2, i⟩⟩ := rfl

def flatHom (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    (∀ a b, Γ a b) →* ∀ c : Fin (∑ a, t a), Γ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 where
  toFun g c := g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem flatHom_apply (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] (g : ∀ a b, Γ a b)
    (c : Fin (∑ a, t a)) :
    flatHom Γ g c = g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := rfl

theorem flatHom_surjective (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    Function.Surjective (flatHom Γ) := by
  have h : ⇑(flatHom Γ) = (Equiv.piCongrLeft' (fun p : Σ a, Fin (t a) => Γ p.1 p.2) finSigmaFinEquiv) ∘
      (Equiv.piCurry fun a b => Γ a b).symm := rfl
  rw [h]
  exact (Equiv.surjective _).comp (Equiv.surjective _)

end Flat

section Pull

variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_of_comp {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (ψ : G' →* G)
    (hψ : Function.Surjective ψ) (h : IsSubquotient (σ.comp ψ) (ρ.comp ψ)) : IsSubquotient σ ρ := by
  obtain ⟨S, f, hf⟩ := h
  refine ⟨⟨S.toSubmodule, fun g v hv => ?_⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf⟩
  · obtain ⟨g', rfl⟩ := hψ g
    exact S.apply_mem_toSubmodule g' hv
  · obtain ⟨g', rfl⟩ := hψ g
    exact f.isIntertwining' g'

theorem isSubquotient_of_equiv {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (φ : σ.Equiv ρ) :
    IsSubquotient σ ρ :=
  .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective

end Pull

end GlobalTheory.JacStages
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProd
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section
namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_one {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₁) :
    Algebra.norm F ((x, 1) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (x, 1) = (Algebra.lmul F R₁ x).prodMap (Algebra.lmul F R₂ 1) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₂), map_one LinearMap.det, mul_one]

theorem norm_one_prod {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₂) :
    Algebra.norm F ((1, x) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (1, x) = (Algebra.lmul F R₁ 1).prodMap (Algebra.lmul F R₂ x) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₁), map_one LinearMap.det, one_mul]

theorem coi_prod {R₁ R₂ : Type} [Ring R₁] [Ring R₂] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {e₁ : ι₁ → R₁} {e₂ : ι₂ → R₂} (h₁ : CompleteOrthogonalIdempotents e₁)
    (h₂ : CompleteOrthogonalIdempotents e₂) :
    CompleteOrthogonalIdempotents (Sum.elim (fun i => ((e₁ i, 0) : R₁ × R₂)) (fun j => ((0, e₂ j) : R₁ × R₂))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact Prod.ext (h₁.idem i).eq (mul_zero 0)
    · exact Prod.ext (mul_zero 0) (h₂.idem j).eq
  · rintro (i | j) (i' | j') hne
    · have hii : i ≠ i' := fun h => hne (congrArg Sum.inl h)
      exact Prod.ext (h₁.ortho hii) (mul_zero 0)
    · exact Prod.ext (mul_zero _) (zero_mul _)
    · exact Prod.ext (zero_mul _) (mul_zero _)
    · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
      exact Prod.ext (mul_zero 0) (h₂.ortho hjj)
  · rw [Fintype.sum_sum_type]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, h₁.complete]
    · simp [Prod.snd_sum, h₂.complete]

theorem factor_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₁) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₁, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₁ f = f) ∧ (¬Q → f * σ₁ f = 0 ∧ e = f + σ₁ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (e, 0) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (e, 0) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(f, 0), Prod.ext hf.eq (mul_zero 0), fun h0 => hf0 (congrArg Prod.fst h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₁ : f * y₁ ≠ 0 := fun h0 => hy (Prod.ext h0 (zero_mul y₂))
    obtain ⟨z, hz⟩ := hfy y₁ hy₁
    exact ⟨(z, 0), Prod.ext hz (mul_zero _)⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ f, σ₂ 0) = (f, 0)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((f, 0) * (σ₁ f, σ₂ 0) : R₁ × R₂) = 0 ∧ (e, 0) = (f, 0) + (σ₁ f, σ₂ 0)
    rw [map_zero]
    exact ⟨Prod.ext h1 (mul_zero 0), Prod.ext h2 (add_zero 0).symm⟩

theorem factor_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₂) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₂ f = f) ∧ (¬Q → f * σ₂ f = 0 ∧ e = f + σ₂ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (0, e) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (0, e) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(0, f), Prod.ext (mul_zero 0) hf.eq, fun h0 => hf0 (congrArg Prod.snd h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₂ : f * y₂ ≠ 0 := fun h0 => hy (Prod.ext (zero_mul y₁) h0)
    obtain ⟨z, hz⟩ := hfy y₂ hy₂
    exact ⟨(0, z), Prod.ext (mul_zero _) hz⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ 0, σ₂ f) = (0, f)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((0, f) * (σ₁ 0, σ₂ f) : R₁ × R₂) = 0 ∧ (0, e) = (0, f) + (σ₁ 0, σ₂ f)
    rw [map_zero]
    exact ⟨Prod.ext (mul_zero 0) h1, Prod.ext (add_zero 0).symm h2⟩

theorem unit_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₁) (hu : IsUnit x) (hσ : σ₁ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((x, 1) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (x, 1) = (x, 1)) ∧
      ((x, 1) : R₁ × R₂) * (1 - (e, 0)) = 1 - (e, 0) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨hu, isUnit_one⟩, ?_⟩, ?_⟩
  · show (σ₁ x, σ₂ 1) = (x, 1)
    rw [hσ, map_one]
  · exact Prod.ext (by simpa using h1) (by simp)

theorem unit_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₂) (hu : IsUnit x) (hσ : σ₂ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((1, x) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (1, x) = (1, x)) ∧
      ((1, x) : R₁ × R₂) * (1 - (0, e)) = 1 - (0, e) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨isUnit_one, hu⟩, ?_⟩, ?_⟩
  · show (σ₁ 1, σ₂ x) = (1, x)
    rw [hσ, map_one]
  · exact Prod.ext (by simp) (by simpa using h1)

theorem isFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ h₁ h₂
  obtain ⟨⟨hc₁, hf₁⟩, hπ₁⟩ := h₁
  obtain ⟨⟨hc₂, hf₂⟩, hπ₂⟩ := h₂
  refine ⟨⟨coi_prod hc₁ hc₂, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact factor_inl B₁.σ B₂.σ (e₁ i) _ _ Finset.inl_mem_disjSum (hf₁ i)
    · exact factor_inr B₁.σ B₂.σ (e₂ j) _ _ Finset.inr_mem_disjSum (hf₂ j)
  · rintro (i | j) hi
    · rw [Finset.inl_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₁ i hi
      obtain ⟨hA, hB⟩ := unit_inl B₁.σ B₂.σ (π₁ i) (e₁ i) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((π₁ i, 1) : B₁.A × B₂.A)) = -1
      rw [norm_prod_one]
      exact hη
    · rw [Finset.inr_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₂ j hi
      obtain ⟨hA, hB⟩ := unit_inr B₁.σ B₂.σ (π₂ j) (e₂ j) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((1, π₂ j) : B₁.A × B₂.A)) = -1
      rw [norm_one_prod]
      exact hη

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApplyStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  first | exact @GlobalTheory.slices_test' | exact GlobalTheory.slices_test' | (intros; apply GlobalTheory.slices_test' <;> assumption)
end

