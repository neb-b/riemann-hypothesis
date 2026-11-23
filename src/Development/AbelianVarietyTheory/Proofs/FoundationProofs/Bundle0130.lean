module

public import Mathlib
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sha1TorsionLevelFiltration
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem mk_mem_sha1_iff_locally_coboundary {R : Type} [CommRing R] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {I : Type} {D : I → Type} [∀ i, Group (D i)]
    [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) {N : Type}
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousConstSMul R N] (τ : Representation R Γ N) (z : Z1 τ) :
    (Submodule.Quotient.mk z : H1 τ) ∈ Sha1 τ φ hφ ↔
      ∀ i, ∃ b : N, ∀ g, z.1 (φ i g) = τ (φ i g) b - b := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun i => ?_
  have : resH1 τ (φ i) (hφ i) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (restrictCocycles1 τ (φ i) (hφ i) z) := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  rfl

theorem sha1_exhausted_by_torsion_levels : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (I : Type) [Finite I] (D : I → Type) [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A] [Module ℤ_[l] A] [TopologicalSpace A] [DiscreteTopology A] (σ : Representation ℤ_[l] Γ A), (∀ a : A, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) → ∃ P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ), Monotone P ∧ (∀ y, ∃ r, y ∈ P r) ∧ ∀ (r : ℕ) (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] (τ : Representation R Γ N) (ι : N →+ A), Function.Injective ι → (∀ a : A, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) → (∀ g n, ι (τ g n) = σ g (ι n)) → (∀ a : A, (∀ i, ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ (φ i g) a - a = σ (φ i g) b - b) → ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ g a - a = σ g b - b) → Nat.card (P r) = Nat.card (Sha1 τ φ hφ) := by
  intro l _ Γ _ _ _ I _ D _ _ φ hφ A _ _ _ _ σ htor
  have hup : ∀ (r s : ℕ) (a : A), r ≤ s → (l : ℤ_[l]) ^ r • a = 0 → (l : ℤ_[l]) ^ s • a = 0 := by
    intro r s a hrs h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
    rw [pow_add, mul_comm, mul_smul, h, smul_zero]
  let P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ) := fun r =>
    { carrier := {x | ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧
        (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧
        ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a}
      zero_mem' := ⟨0, rfl, fun g => by simp, fun i => ⟨0, by simp, fun g => by simp⟩⟩
      add_mem' := by
        rintro x y ⟨z, hz, hz1, hz2⟩ ⟨w, hw, hw1, hw2⟩
        refine ⟨z + w, by rw [Submodule.Quotient.mk_add, hz, hw]; rfl, fun g => ?_, fun i => ?_⟩
        · change _ • (z.1 g + w.1 g) = 0
          rw [smul_add, hz1, hw1, add_zero]
        · obtain ⟨a, ha, ha'⟩ := hz2 i
          obtain ⟨b, hb, hb'⟩ := hw2 i
          refine ⟨a + b, by rw [smul_add, ha, hb, add_zero], fun g => ?_⟩
          change z.1 _ + w.1 _ = _
          rw [ha', hb', map_add (f := _)]; abel
      smul_mem' := by
        rintro c x ⟨z, hz, hz1, hz2⟩
        refine ⟨c • z, by rw [Submodule.Quotient.mk_smul, hz]; rfl, fun g => ?_, fun i => ?_⟩
        · change _ • (c • z.1 g) = 0
          rw [smul_comm, hz1, smul_zero]
        · obtain ⟨a, ha, ha'⟩ := hz2 i
          refine ⟨c • a, by rw [smul_comm, ha, smul_zero], fun g => ?_⟩
          change c • z.1 _ = _
          rw [ha', map_smul, smul_sub] }
  have hP : ∀ r x, x ∈ P r ↔ ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧
        (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧
        ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a :=
    fun r x => Iff.rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · intro r s hrs x hx
    obtain ⟨z, hz, hz1, hz2⟩ := (hP r x).1 hx
    refine (hP s x).2 ⟨z, hz, fun g => hup r s _ hrs (hz1 g), fun i => ?_⟩
    obtain ⟨a, ha, ha'⟩ := hz2 i
    exact ⟨a, hup r s _ hrs ha, ha'⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    choose b hb using (mk_mem_sha1_iff_locally_coboundary φ hφ σ z).1 hy
    choose e he using htor
    have hfin : (Set.range z.1 ∪ Set.range b).Finite :=
      (isCompact_range z.2.1).finite_of_discrete.union (Set.finite_range b)
    obtain ⟨r, hr⟩ := (hfin.image e).bddAbove
    refine ⟨r, (hP r _).2 ⟨z, rfl, fun g => hup _ _ _ (hr ⟨_, Or.inl ⟨g, rfl⟩, rfl⟩) (he _),
      fun i => ⟨b i, hup _ _ _ (hr ⟨_, Or.inr ⟨i, rfl⟩, rfl⟩) (he _), hb i⟩⟩⟩
  · intro r R _ N _ _ _ _ τ ι hinj hrange heq hloc
    let ιZ : Z1 τ →+ Z1 σ :=
      { toFun := fun z => ⟨fun g => ι (z.1 g), continuous_of_discreteTopology.comp z.2.1,
          fun g h => by beta_reduce; rw [z.2.2, map_add (f := _), heq]⟩
        map_zero' := Subtype.ext (funext fun g => map_zero ι)
        map_add' := fun z w => Subtype.ext (funext fun g => map_add ι _ _) }
    have hιZ : ∀ z g, (ιZ z).1 g = ι (z.1 g) := fun _ _ => rfl
    let F : H1 τ →+ H1 σ := QuotientAddGroup.map
      ((B1 τ).comap (Z1 τ).subtype).toAddSubgroup ((B1 σ).comap (Z1 σ).subtype).toAddSubgroup ιZ
      (by
        intro z hz
        obtain ⟨m, hm⟩ := (mem_coboundaries1 τ _).1 hz
        refine (mem_coboundaries1 σ _).2 ⟨ι m, fun g => ?_⟩
        change ι (z.1 g) = _
        rw [← heq, ← map_sub]
        exact congrArg ι (hm g))
    have hF : ∀ z, F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (ιZ z) := fun _ => rfl
    have hkill : ∀ n, (l : ℤ_[l]) ^ r • ι n = 0 := fun n => (hrange _).2 ⟨n, rfl⟩
    have hmem : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → ∃ h : F x ∈ Sha1 σ φ hφ, ⟨F x, h⟩ ∈ P r := by
      intro x hx
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 := (mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx
      have h2 : ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧
          ∀ g, (ιZ z).1 (φ i g) = σ (φ i g) a - a := by
        intro i
        obtain ⟨b, hb⟩ := h1 i
        exact ⟨ι b, hkill b, fun g => by rw [hιZ, hb, map_sub, heq]⟩
      refine ⟨?_, (hP r _).2 ⟨ιZ z, rfl, fun g => hkill _, h2⟩⟩
      rw [hF, mk_mem_sha1_iff_locally_coboundary]
      intro i
      obtain ⟨a, -, ha⟩ := h2 i
      exact ⟨a, ha⟩
    have hker : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → F x = 0 → x = 0 := by
      intro x hx h0
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 := (mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx
      rw [hF, Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨a, ha⟩ := (mem_coboundaries1 σ _).1 h0
      have ha' : ∀ g, ι (z.1 g) = σ g a - a := ha
      obtain ⟨b, hb, hb'⟩ := hloc a (fun i => by
        obtain ⟨b, hb⟩ := h1 i
        exact ⟨ι b, hkill b, fun g => by rw [← ha', hb, map_sub, heq]⟩)
      obtain ⟨n, rfl⟩ := (hrange b).1 hb
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 τ _).2 ⟨n, fun g => hinj ?_⟩
      change ι (z.1 g) = _
      rw [ha', hb', map_sub, heq]
    let f : Sha1 τ φ hφ → P r := fun x => ⟨⟨F x.1, (hmem x.1 x.2).1⟩, (hmem x.1 x.2).2⟩
    refine (Nat.card_eq_of_bijective f ⟨?_, ?_⟩).symm
    · intro x y hxy
      have h : F x.1 = F y.1 := congrArg (fun t : P r => t.1.1) hxy
      apply Subtype.ext
      rw [← sub_eq_zero]
      exact hker _ (sub_mem x.2 y.2) (by rw [map_sub, h, sub_self])
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz, hz1, hz2⟩ := (hP r x).1 hx
      have hlift : ∀ g, ∃ n, ι n = z.1 g := fun g => (hrange _).1 (hz1 g)
      choose w hw using hlift
      have hwc : Continuous w := by
        have : w = Function.invFun ι ∘ z.1 := by
          funext g
          rw [Function.comp_apply, ← hw, Function.leftInverse_invFun hinj]
        rw [this]
        exact continuous_of_discreteTopology.comp z.2.1
      let z' : Z1 τ := ⟨w, hwc, fun g h => hinj (by rw [map_add (f := _), heq, hw, hw, hw, z.2.2])⟩
      have hz' : ιZ z' = z := Subtype.ext (funext hw)
      refine ⟨⟨Submodule.Quotient.mk z', ?_⟩, ?_⟩
      · rw [mk_mem_sha1_iff_locally_coboundary]
        intro i
        obtain ⟨a, ha, ha'⟩ := hz2 i
        obtain ⟨n, rfl⟩ := (hrange a).1 ha
        refine ⟨n, fun g => hinj ?_⟩
        change ι (w _) = _
        rw [hw, ha', map_sub, heq]
      · apply Subtype.ext
        apply Subtype.ext
        change F (Submodule.Quotient.mk z') = x.1
        rw [hF, hz', hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBound
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem mass_true_le_one (g : ℕ) [Fact g.Prime] (N : ℕ) : (mass g N fun _ => True) ≤ 1 := by
  refine (_root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun _ => True)).trans (le_of_eq ?_)
  rw [Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  exact div_self hN

theorem mass_dvd_le (g : ℕ) [Fact g.Prime] (N a : ℕ) (h : (ZMod g)[X]) (hh : h ∈ sqSet g a) :
    (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ * mass g (N - a) fun _ => True := by
  obtain ⟨hmon, hdeg, -, -⟩ := mem_sqSet.1 hh
  have hh0 : h ≠ 0 := hmon.ne_zero
  unfold mass
  set S := (sqSet g N).filter fun f => h ∣ f with hS
  have hfac : ∀ f ∈ S, h * (f /ₘ h) = f := by
    intro f hf
    have hd : h ∣ f := (Finset.mem_filter.1 hf).2
    have e := Polynomial.modByMonic_add_div f h
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hmon).2 hd, zero_add] at e
  have hmem : ∀ f ∈ S, f /ₘ h ∈ sqSet g (N - a) := by
    intro f hf
    obtain ⟨fmon, fdeg, fsq, fc0⟩ := mem_sqSet.1 (Finset.mem_filter.1 hf).1
    have e := hfac f hf
    have umon : (f /ₘ h).Monic := hmon.of_mul_monic_left (by rw [e]; exact fmon)
    refine mem_sqSet.2 ⟨umon, ?_, ?_, ?_⟩
    · have hd := hmon.natDegree_mul umon
      rw [e, fdeg, hdeg] at hd
      omega
    · exact Squarefree.of_mul_right (by rw [e]; exact fsq)
    · intro hz
      apply fc0
      rw [← e, Polynomial.mul_coeff_zero, hz, mul_zero]
  have hinj : Set.InjOn (fun f => f /ₘ h) (S : Set (ZMod g)[X]) := by
    intro f hf f' hf' hq
    rw [← hfac f hf, ← hfac f' hf']
    exact congrArg (h * ·) hq
  have hterm : ∀ f ∈ S, ((torusCard g f : ℝ))⁻¹ =
      ((torusCard g h : ℝ))⁻¹ * ((torusCard g (f /ₘ h) : ℝ))⁻¹ := by
    intro f hf
    have e := hfac f hf
    have hu0 : f /ₘ h ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at e
      exact (mem_sqSet.1 (Finset.mem_filter.1 hf).1).1.ne_zero e.symm
    conv_lhs => rw [← e]
    rw [torusCard_mul hh0 hu0, Nat.cast_mul, mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← Finset.sum_image (f := fun u => ((torusCard g u : ℝ))⁻¹) hinj, Finset.filter_true]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
  intro u hu
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
  exact hmem f hf

theorem divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧
    ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  intro g _
  refine ⟨mass_true_le_one g, fun N a h hh => ?_⟩
  refine (mass_dvd_le g N a h hh).trans ?_
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLe
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

open Polynomial Classical in
private lemma exists_le_degType_sum_eq_of_hasDiv {g : ℕ} [Fact g.Prime] {N a : ℕ}
    {f : (ZMod g)[X]} (hf : f ∈ _root_.GlobalTheory.BadShare.sqSet g N) (hd : _root_.GlobalTheory.BadShare.HasDiv g a f) :
    ∃ ν ≤ _root_.GlobalTheory.BadShare.degType g f, ν.sum = a := by
  unfold _root_.GlobalTheory.BadShare.HasDiv at hd
  obtain ⟨h, hdvd, hdeg⟩ := hd
  obtain ⟨hmon, -, hsq, hc0⟩ := (_root_.GlobalTheory.BadShare.mem_sqSet).mp hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hf0 (zero_dvd_iff.mp hdvd)
  have hlc : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hh0
  obtain ⟨u, hu⟩ : ∃ u : (ZMod g)[X], u = h * C h.leadingCoeff⁻¹ := ⟨_, rfl⟩
  have hudvd : u ∣ f := by
    refine dvd_trans ⟨C h.leadingCoeff, ?_⟩ hdvd
    rw [hu, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  have humon : u.Monic := hu ▸ monic_mul_leadingCoeff_inv hh0
  have hudeg : u.natDegree = a := by rw [hu, natDegree_mul_C (inv_ne_zero hlc), hdeg]
  have husq : Squarefree u := hsq.squarefree_of_dvd hudvd
  have huc0 : u.coeff 0 ≠ 0 := by
    intro h0
    apply hc0
    obtain ⟨k, hk⟩ := hudvd
    rw [hk, mul_coeff_zero, h0, zero_mul]
  have hmem : u ∈ _root_.GlobalTheory.BadShare.sqSet g a :=
    (_root_.GlobalTheory.BadShare.mem_sqSet).mpr ⟨humon, hudeg, husq, huc0⟩
  obtain ⟨k, hk⟩ := hudvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hf0 hk
  refine ⟨_root_.GlobalTheory.BadShare.degType g u, ?_,
    ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 a u hmem).2.2.1⟩
  rw [hk, ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).2.1 u k humon.ne_zero hk0).1]
  exact Multiset.le_add_right _ _

open Polynomial Classical in
private lemma exists_subset_map_eq_of_le_map {β γ : Type} (f : β → γ) (s : Finset β) :
    ∀ ν : Multiset γ, ν ≤ s.val.map f → ∃ t ⊆ s, t.val.map f = ν := by
  induction s using Finset.cons_induction with
  | empty =>
    intro ν h
    rw [Finset.empty_val, Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨∅, Finset.empty_subset _, by rw [h]; rfl⟩
  | cons a s ha ih =>
    intro ν h
    rw [Finset.cons_val, Multiset.map_cons] at h
    by_cases hm : f a ∈ ν
    · obtain ⟨t, ht, htν⟩ := ih (ν.erase (f a))
        (by rw [← Multiset.cons_le_cons_iff (f a), Multiset.cons_erase hm]; exact h)
      refine ⟨Finset.cons a t (fun hat => ha (ht hat)), fun x hx => ?_, ?_⟩
      · rw [Finset.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (ht hx)
      · rw [Finset.cons_val, Multiset.map_cons, htν, Multiset.cons_erase hm]
    · obtain ⟨t, ht, htν⟩ := ih ν ((Multiset.le_cons_of_notMem hm).mp h)
      exact ⟨t, fun x hx => Finset.mem_cons.mpr (Or.inr (ht hx)), htν⟩

open Polynomial Classical in
private lemma exists_invariant_finset_card_of_le_cycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) (ν : Multiset ℕ)
    (hν : ν ≤ σ.partition.parts) : ∃ S : Finset (Fin n), S.card = ν.sum ∧ S.map σ.toEmbedding = S := by
  rw [Equiv.Perm.parts_partition] at hν
  have h1 : ν.filter (2 ≤ ·) ≤ σ.cycleType := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx),
      Multiset.filter_eq_nil.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), add_zero]
  have h2 : ν.filter (fun x => ¬ 2 ≤ x) ≤ Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1 := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr (fun x hx => not_not.mpr (Equiv.Perm.two_le_of_mem_cycleType hx)),
      Multiset.filter_eq_self.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), zero_add]
  have hν2 : ν.filter (fun x => ¬ 2 ≤ x) = Multiset.replicate (Multiset.card (ν.filter (fun x => ¬ 2 ≤ x))) 1 :=
    Multiset.eq_replicate_of_mem fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le h2 hb)
  have hk := Multiset.card_le_card h2
  rw [Multiset.card_replicate] at hk
  rw [Equiv.Perm.cycleType_def] at h1
  obtain ⟨C, hC, hCν⟩ := exists_subset_map_eq_of_le_map _ _ _ h1
  have hcompl : (σ.support)ᶜ.card = Fintype.card (Fin n) - σ.support.card := Finset.card_compl _
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (hcompl ▸ hk)
  have hCσ : ∀ c ∈ C, ∀ x ∈ c.support, σ x = c x := fun c hc x hx =>
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hC hc)).2 x hx).symm
  have hS1 : ∀ x ∈ C.biUnion (fun c => c.support), σ x ∈ C.biUnion (fun c => c.support) ∧ σ x ≠ x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    rw [hCσ c hc x hxc]
    exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, Equiv.Perm.apply_mem_support.mpr hxc⟩, Equiv.Perm.mem_support.mp hxc⟩
  have hT' : ∀ x ∈ T, σ x = x := fun x hx => Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hT hx))
  have hdisj : Disjoint (C.biUnion (fun c => c.support)) T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (hS1 x hx).2 (hT' x hxT)
  have hcard1 : (C.biUnion (fun c => c.support)).card = (ν.filter (2 ≤ ·)).sum := by
    rw [Finset.card_biUnion, ← hCν, Finset.sum_eq_multiset_sum]
    · rfl
    · intro c hc e he hce
      exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ (hC hc) (hC he) hce).disjoint_support
  refine ⟨C.biUnion (fun c => c.support) ∪ T, ?_, ?_⟩
  · have hs2 : (ν.filter (fun x => ¬ 2 ≤ x)).sum = Multiset.card (ν.filter (fun x => ¬ 2 ≤ x)) := by
      conv_lhs => rw [hν2]
      rw [Multiset.sum_replicate, smul_eq_mul, mul_one]
    rw [Finset.card_union_of_disjoint hdisj, hcard1, hTc, ← hs2, ← Multiset.sum_add, Multiset.filter_add_not]
  · refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map])
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hS1 x hx).1
    · simp only [Equiv.toEmbedding_apply]
      rw [hT' x hx]
      exact Finset.mem_union_right _ hx


open Polynomial Classical in
theorem _root_.GlobalTheory.BadShare.mass_hasDiv_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N →
    _root_.GlobalTheory.BadShare.mass g N (_root_.GlobalTheory.BadShare.HasDiv g a) ≤ 7 / 8 := by
  intro g _ N a ha haN
  have hmono := (_root_.GlobalTheory.BadShare.mass_union_bounds g N).1
  refine (hmono _ (fun f => (fun μ : Multiset ℕ => ∃ ν ≤ μ, ν.sum = a) (_root_.GlobalTheory.BadShare.degType g f))
    (fun f hf hd => exists_le_degType_sum_eq_of_hasDiv hf hd)).trans ?_
  refine (_root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun μ => ∃ ν ≤ μ, ν.sum = a)).trans ?_
  have h := _root_.GlobalTheory.StableSubset.card_exists_stable_subset_le N a ha haN
  have hc := Finset.card_le_card (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ ν ≤ σ.partition.parts, ν.sum = a)
    (t := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A)
    (fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      obtain ⟨ν, hν, rfl⟩ := hσ
      exact exists_invariant_finset_card_of_le_cycleType σ ν hν)
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf]
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at h' hc'
  linarith

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLe
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) (h : p ≠ q) : p + q ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  have hq' : q ∈ t := (Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hq'
  rw [Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]
  exact Nat.le_add_right _ _

theorem card_perm_no_long_cycle (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]

theorem mass_not_hasPrimeFactor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
  have hT := _root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith

end GlobalTheory.BadShare
end

