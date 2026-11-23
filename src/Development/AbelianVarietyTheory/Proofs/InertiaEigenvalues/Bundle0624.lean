module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LocGL

section Rad

variable {R S : Type} [CommRing R] [CommRing S] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem map_mem_unipRad_of_ringHom (f : R →+* S) {e : (Σ a, m a) ≃ n} {g : GL n R} (hg : g ∈ unipRad R e) :
    GeneralLinearGroup.map f g ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [mem_parab.1 h1 i j hij, map_zero]
  · show f ((g : Matrix n n R) _ _) = _
    rw [h2 a i j]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end Rad

theorem isCuspidal_comp_generalLinearGroupMap {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi : Continuous i.symm) {n : Type} [Fintype n]
    [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (h : IsCuspidal π) : IsCuspidal (π.comp (GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM
  have hc : Continuous M :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  refine ⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩
  have hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e := fun u hu => map_mem_unipRad_of_ringHom _ hu
  have hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w := fun w hw =>
    ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw,
      Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩
  have hinj : Function.Injective M := fun x y hxy => Units.ext (Matrix.ext fun a b =>
    i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))
  have hne : unipRad k e ≠ ⊥ := fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu =>
    hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))
  have h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨M u, hmem u u.2⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u', hu', hu⟩ := hsurj u u.2
      exact ⟨⟨u', hu'⟩, v, by simp [hu]⟩
  exact Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

theorem frame_exists (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e π : ι → B.A) (S : Finset ι), IsFrame B e π S := by
  obtain ⟨ι, _, e, S, hP⟩ := _root_.GlobalTheory.UnitLemma.Desc.isPre_of_separable K B hs
  have : ∀ i, ∃ y : B.A, i ∈ S → B.Plus y ∧ y * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E y) = -1 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨f, hf, hf0, hfld, hS, -⟩ := hP.2 i
      obtain ⟨he, hσ⟩ := hS hi
      obtain ⟨y, hy⟩ := _root_.GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one K B f hf hf0 hfld hσ
      exact ⟨y, fun _ => by rw [he]; exact hy⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose π hπ using this
  exact ⟨ι, inferInstance, e, π, S, hP, fun i hi => hπ i hi⟩

theorem plus_mul {K : UQ} (B : InvAlg K) {x y : B.A} (hx : B.Plus x) (hy : B.Plus y) : B.Plus (x * y) :=
  ⟨hx.1.mul hy.1, by rw [map_mul, hx.2, hy.2]⟩

theorem plus_one {K : UQ} (B : InvAlg K) : B.Plus 1 := ⟨isUnit_one, map_one _⟩

theorem plus_prod {K : UQ} (B : InvAlg K) {ι : Type} (π : ι → B.A) (J : Finset ι) (h : ∀ j ∈ J, B.Plus (π j)) :
    B.Plus (∏ j ∈ J, π j) :=
  Finset.prod_induction _ B.Plus (fun _ _ => plus_mul B) (plus_one B) h

theorem isUnit_a {K : UQ} (B : InvAlg K) (a : K.O) (ha : K.Small a) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
  intro h
  exact ha.1 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))

theorem lim_HH {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) (x : B.A) (hx : B.Plus x) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x))) := by
  have hπ : ∀ J ∈ S.powerset, B.Plus ((∏ j ∈ J, π j) * x) := fun J hJ =>
    plus_mul B (plus_prod B π J fun j hj => (hF.2 j (Finset.mem_powerset.1 hJ hj)).1) hx
  have hu : ∀ k : ℕ, IsUnit (x * algebraMap K.O B.A a ^ (2 * k)) := fun k => hx.1.mul ((isUnit_a B a ha).pow _)
  have heq : ∀ k : ℕ, ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ) = ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card *
        ((B.GG ((∏ j ∈ J, π j) * x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    intro k
    rw [_root_.GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG K B ι e π S hB hF I hI _ (hu k)]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_assoc, mul_div_assoc]
  simp_rw [heq]
  exact tendsto_finsetSum _ fun J hJ => (hℓ _ (hπ J hJ)).const_mul _

theorem sum_formula {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j))) ∧
    ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card *
      ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) := by
  set h : Finset ι → ℝ := fun I => ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) with hh
  have lim1 : ∀ I ⊆ S, Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 (h I)) := by
    intro I hI
    have := lim_HH B e π S a hB ha hF ℓ hℓ I hI 1 (plus_one B)
    simp only [one_mul, mul_one] at this
    exact this
  have key : ∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I := by
    intro I hI x hx
    have t1 := lim_HH B e π S a hB ha hF ℓ hℓ I hI x hx
    have t2 := _root_.GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible K B ι e π S a hB ha hF I hI x hx
    have t3 := (lim1 I hI).const_mul (chi B e I x : ℝ)
    have t4 := t2.add t3
    rw [zero_add] at t4
    refine tendsto_nhds_unique t1 (t4.congr fun k => ?_)
    push_cast
    ring
  refine ⟨lim1 I hI, ?_⟩
  haveI : Finite B.Cl := _root_.GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable K B hB.2
  exact _root_.GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl K B ι e π S hF this ℓ h key I hI

theorem linearDescent : LinearDescent := by
  intro K B₁ B₂ hg₁ hg₂ hsep a ha ℓ ℓ₁ ℓ₂ hℓ hℓ₁ hℓ₂
  have hs₁ : B₁.P.Separable := hsep.of_mul_left
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  obtain ⟨ι₁, _, e₁, π₁, S₁, hF₁⟩ := frame_exists K B₁ hs₁
  obtain ⟨ι₂, _, e₂, π₂, S₂, hF₂⟩ := frame_exists K B₂ hs₂
  have hF := _root_.GlobalTheory.UnitLemma.Desc.isFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  have hL₁ : B₁.LieReg := ⟨hg₁, hs₁⟩
  have hL₂ : B₂.LieReg := ⟨hg₂, hs₂⟩
  have hL : (B₁.prod B₂).LieReg := ⟨by
    show ((B₁.σ B₁.g, B₂.σ B₂.g) : B₁.A × B₂.A) = (B₁.g, B₂.g)
    rw [hg₁, hg₂], hP ▸ hsep⟩
  have hΛ : (S₁.disjSum S₂) \ S₁.map Function.Embedding.inl = S₂.map Function.Embedding.inr := by
    ext x; cases x <;> simp
  have hΛS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by
    intro x; cases x <;> simp
  obtain ⟨l₁, c₁⟩ := sum_formula B₁ e₁ π₁ S₁ a hL₁ ha hF₁ ℓ₁ hℓ₁ S₁ subset_rfl
  obtain ⟨l₂, c₂⟩ := sum_formula B₂ e₂ π₂ S₂ a hL₂ ha hF₂ ℓ₂ hℓ₂ ∅ (Finset.empty_subset _)
  obtain ⟨l, c⟩ := sum_formula (B₁.prod B₂) _ _ _ a hL ha hF ℓ hℓ _ hΛS
  rw [Finset.sdiff_self] at l₁
  rw [Finset.sdiff_empty] at l₂
  rw [hΛ] at l
  change Tendsto (fun k : ℕ => ((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 : ℚ) : ℝ) / ((B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) : ℝ)) atTop _ at l
  set h₁ := ∑ J ∈ S₁.powerset, (-1 : ℝ) ^ (J ∩ S₁).card * ℓ₁ (∏ j ∈ J, π₁ j)
  set h₂ := ∑ J ∈ S₂.powerset, (-1 : ℝ) ^ (J ∩ ∅).card * ℓ₂ (∏ j ∈ J, π₂ j)
  set h := ∑ J ∈ (S₁.disjSum S₂).powerset, (-1 : ℝ) ^ (J ∩ S₁.map Function.Embedding.inl).card *
    ℓ (∏ j ∈ J, Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) j)
  have hd := _root_.GlobalTheory.UnitLemma.Desc.hh_prod_tendsto K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  set v := val K.O (resultant B₁.P B₂.P)
  have hrho : ∀ k : ℕ, (B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := fun k =>
    _root_.GlobalTheory.RhoProd.rho_prod K B₁ B₂ _ _
  have hh : h = (-(K.q : ℝ)) ^ v * (h₁ * h₂) := by
    have t1 := (l₁.mul l₂).const_mul ((-(K.q : ℝ)) ^ v)
    have t2 := hd.add t1
    rw [zero_add] at t2
    refine tendsto_nhds_unique l (t2.congr fun k => ?_)
    rw [hrho k]
    push_cast
    ring
  have e₁' : ∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep =
      ∑ᶠ k : B₁.Cl, (chi B₁ e₁ S₁ k.rep : ℝ) * ℓ₁ k.rep := by
    refine finsum_congr fun k => ?_
    rw [((_root_.GlobalTheory.UnitLemma.Desc.chi_frame_props K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k) ⟨Units.isUnit _, (Quot.out k).2⟩)]
  have e₂' : ∑ᶠ k : B₂.Cl, ℓ₂ k.rep = ∑ᶠ k : B₂.Cl, (chi B₂ e₂ ∅ k.rep : ℝ) * ℓ₂ k.rep := by
    refine finsum_congr fun k => ?_
    simp [chi, eS, UQ.eta, val]
  have e' : ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      ∑ᶠ k : (B₁.prod B₂).Cl, (chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A))
        (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) k.rep : ℝ) * ℓ k.rep := by
    refine finsum_congr fun k => ?_
    rw [_root_.GlobalTheory.UnitLemma.Desc.chi_prod_inl K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ (InvAlg.Cl.rep k)]
    have hk : (B₁.prod B₂).Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩
    have hk1 : B₁.Plus (InvAlg.Cl.rep k).1 :=
      ⟨(Prod.isUnit_iff.1 hk.1).1, congrArg Prod.fst hk.2⟩
    rw [((_root_.GlobalTheory.UnitLemma.Desc.chi_frame_props K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k).1 hk1)]
  rw [e₁', e₂', e', c, c₁, c₂, hh, _root_.GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod, Finset.card_disjSum]
  push_cast
  ring

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFiniteStatement
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) → ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  first | (exact @GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (exact GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (intros; apply GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightEx

theorem exists_cols_det_ne_zero {R : Type} [CommRing R] [IsDomain R] {d : ℕ} {κ : Type} (col : κ → Fin d → R)
    (h : ∀ r : Fin d → R, (∀ k, r ⬝ᵥ col k = 0) → r = 0) :
    ∃ σ : Fin d → κ, (Matrix.of fun a b => col (σ b) a).det ≠ 0 := by
  classical
  let F := FractionRing R
  let v : κ → Fin d → F := fun k a => algebraMap R F (col k a)
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun a : Fin d => f (Pi.single a 1))
    choose r hr using hb
    have hb0 : algebraMap R F b ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero b (hinj (h0.trans (map_zero _).symm))
    have hr0 : r = 0 := h r fun k => hinj (by
      have h1 : f (v k) = 0 := hf (Submodule.subset_span ⟨k, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, dotProduct, map_sum]
      have h2 : ∀ a, algebraMap R F (r a * col k a) =
          algebraMap R F b * (v k a • f fun j => if a = j then 1 else 0) := fun a => by
        have e : (fun j => if a = j then (1 : F) else 0) = Pi.single a 1 := by
          ext j; simp [Pi.single_apply, eq_comm]
        rw [map_mul, hr, e, Algebra.smul_def, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun a _ => h2 a, ← Finset.mul_sum, h1, mul_zero])
    refine hf0 ((Pi.basisFun F (Fin d)).ext fun a => ?_)
    have h3 := hr a
    rw [hr0, Pi.zero_apply, map_zero, Algebra.smul_def] at h3
    rw [Pi.basisFun_apply]
    exact (mul_eq_zero.1 h3.symm).resolve_left hb0
  obtain ⟨κ', a, -, hs, hli⟩ := exists_linearIndependent' F v
  let B : Module.Basis κ' F (Fin d → F) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ' ≃ Fin d := B.indexEquiv (Pi.basisFun F (Fin d))
  refine ⟨a ∘ e.symm, fun h0 => ?_⟩
  have hu : IsUnit ((Matrix.of fun x y => col (a (e.symm y)) x).map (algebraMap R F)) :=
    Matrix.linearIndependent_cols_iff_isUnit.1 (hli.comp e.symm e.symm.injective)
  have h4 := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h4
  exact h4.ne_zero ((congrArg (algebraMap R F) h0).trans (map_zero _))

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem injective_of_topBasis {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  have e : ∀ a, TB.c TB.i₀ (s a * TB.b TB.i₀) = a := fun a => by rw [TB.c_mul, TB.c_self, mul_one]
  rw [← e a, h, e]

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem exists_cols (hinj : Function.Injective bk.iA) {d : ℕ} {ι : Type}
    (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (β : ι → Ainf l) (c : Ainf l) (hc : c ≠ 0)
    (h : ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * β i)) (bk.iA (c * if a = b then 1 else 0))) :
    ∃ σ : Fin d → ι × Fin d, (Matrix.of fun a b => v (σ b).1 a (σ b).2).det ≠ 0 := by
  refine exists_cols_det_ne_zero (fun (k : ι × Fin d) a => v k.1 a k.2) fun r hr => funext fun b => ?_
  have h1 := hasSum_sum (s := Finset.univ) fun a _ => (h a b).mul_left (bk.iA (r a))
  have h2 : (fun i => ∑ a, bk.iA (r a) * bk.iA (v i a b * β i)) = fun _ => 0 := funext fun i => by
    have h3 := hr (i, b)
    simp only [dotProduct] at h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_mul, ← map_sum, ← mul_assoc, ← Finset.sum_mul, h3, zero_mul, map_zero]
  rw [h2] at h1
  have h4 := h1.unique hasSum_zero
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum] at h4
  have h5 := hinj (h4.trans (map_zero _).symm)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h5
  exact (mul_eq_zero.1 h5).resolve_right hc

theorem mem_lattice (hev : Function.Injective bk.ev) {d : ℕ} (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (m : ℕ)
    (P Y' : Matrix (Fin d) (Fin d) (WCb l)) (hY' : (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P)
    (hP : ∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) →
      ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w))
    (y : Fin d → Ainf l) (δ : bk.S) (c : Fin d → bk.S) (hδ : δ ≠ 0)
    (h : (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a)) :
    ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w := by
  have h0 : bk.evW δ ≠ 0 := fun h0 =>
    hδ (hev (inclW_injective (h0.trans (by rw [map_zero, map_zero]))))
  obtain ⟨n, u, u', -, hu', huu, he⟩ := (_root_.GlobalTheory.OEDvr.main l K bk).2.2.2.1 _ (evW_mem bk δ) h0
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have h1 : Y1.map (inclW l) *ᵥ (u' • fun a => bk.evW (c a)) = (l : WCb l) ^ n • fun a => inclW l (y a) := by
    rw [Matrix.mulVec_smul]
    funext a
    have h2 := congrArg (inclW l) (congrFun h a)
    rw [RingHom.map_mulVec, map_mul] at h2
    change bk.evW δ * _ = (Y1.map (inclW l) *ᵥ fun a => bk.evW (c a)) a at h2
    rw [Pi.smul_apply, ← h2, he, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination ((l : WCb l) ^ n * inclW l (y a)) * huu
  obtain ⟨w, hw, hw2⟩ := hP (u' • fun a => bk.evW (c a)) (fun i => bk.OE.mul_mem hu' (evW_mem bk _)) n
    (fun i => by rw [h1]; exact ⟨_, rfl⟩)
  refine ⟨w, hw, ?_⟩
  have h3 := congrArg (Y1.map (inclW l)).mulVec hw2
  rw [Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, smul_comm] at h3
  exact smul_right_injective _ (pow_ne_zero m hl0) (smul_right_injective _ (pow_ne_zero n hl0) h3)

theorem nonempty_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (_root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.crystallineLattice_frobenius_rational_columns l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.crystallineDiscPeriods_galois_action_eq l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := _root_.GlobalTheory.SatLattice.exists_lattice_basis l K bk d _ hdet
  have hY'u := _root_.GlobalTheory.EtaleLattice.isUnit_saturated_basis l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := _root_.GlobalTheory.BSP.saturated_module_free l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add (f := _)]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.crystallineLattice_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.basis_dvd_tauPow_lPow_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := _root_.GlobalTheory.BSP.HeightAprime.main l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨⟨Y, hYu, _, GlobalTheory.T.isUnit_discBasis_crystallineLattice l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, 0, b, _, A', hA', by
    rw [pow_zero, one_smul]; exact hA⟩⟩

end GlobalTheory.BSP.HeightEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
section
open MeasureTheory

namespace GlobalTheory.SplitWeil

theorem nabs_map_of_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' x
  haveI : SecondCountableTopology k := (Model.secondCountable_and_t2_local_field (k := k)).1
  haveI : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2
  haveI : SecondCountableTopology k' := (Model.secondCountable_and_t2_local_field (k := k')).1
  haveI : T2Space k' := (Model.secondCountable_and_t2_local_field (k := k')).2
  let e : k ≃ₜ+ k' :=
    { i.toAddEquiv with
      continuous_toFun := hi
      continuous_invFun := hi' }
  unfold nabs
  congr 1
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e x (Units.map i.toRingHom.toMonoidHom x) (fun y => by
    change i ((x : k) * y) = i x * i y
    exact map_mul i _ _)

end GlobalTheory.SplitWeil
end

