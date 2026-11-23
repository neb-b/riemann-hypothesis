module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryProdCreationLeviChains
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestriction
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem bdL_inRR_eq {n : ℕ} {lev : Fin n → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) {x : Cq n V} (hx : SuppL (inUU lev) x) :
    bdL (inRR lev) E1 E2 x = bdL (inUU lev) E1 E2 x := by
  classical
  have h1 : ∀ l : Lt n, ¬inUU lev l → annL l x = 0 := fun l hl => by
    funext A
    by_contra h
    exact hl (hx _ (annL_ne h).2 l (mem_insert_self _ _))
  have h2 : ∀ l m : Lt n, ¬inUU lev m → annL m (annL l x) = 0 := fun l m hm => by
    funext A
    by_contra h
    obtain ⟨-, h3⟩ := annL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    exact hm (hx _ h4 m (mem_insert_of_mem (mem_insert_self _ _)))
  simp only [bdL, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  · refine sum_congr rfl fun l _ => ?_
    by_cases hl : inUU lev l
    · rw [if_pos (Or.inr hl : inRR lev l), if_pos hl]
    · rw [if_neg hl]
      split_ifs
      · simp [Module.End.mul_apply, h1 l hl]
      · rfl
  · refine sum_congr rfl fun l _ => sum_congr rfl fun m _ => sum_congr rfl fun k _ => ?_
    by_cases hl : inUU lev l
    · by_cases hm : inUU lev m
      · by_cases hc : l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2
        · rw [if_pos ⟨Or.inr hl, Or.inr hm, hc⟩, if_pos ⟨hl, hm, hc⟩]
        · rw [if_neg fun t => hc t.2.2, if_neg fun t => hc t.2.2]
      · have hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧
            k.2.1.2 = m.2.1.2) := fun t => hm t.2.1
        rw [if_neg hn]
        split_ifs
        · simp [Module.End.mul_apply, h2 l m hm]
        · rfl
    · have hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧
          k.2.1.2 = m.2.1.2) := fun t => hl t.1
      rw [if_neg hn]
      split_ifs
      · simp [Module.End.mul_apply, h1 l hl]
      · rfl

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem creL_single (f : Lt n) (S : Finset (Lt n)) (w : V) (h : f ∉ S) :
    (creL f : Module.End ℂ (Cq n V)) (Pi.single S w : Cq n V) =
      sgL f (insert f S) • (Pi.single (insert f S) w : Cq n V) := by
  funext A
  rw [creL_apply, Pi.smul_apply]
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (mem_insert_self f S), erase_insert h, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hA, smul_zero]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun e => hA (by rw [← e, insert_erase hf])
      rw [Pi.single_eq_of_ne hne, smul_zero]
    · rfl

theorem prod_creL_single (l : List (Lt n)) (S : Finset (Lt n)) (w : V) (hl : l.Nodup) (hS : ∀ i ∈ l, i ∉ S) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((l.map creL).prod : Module.End ℂ (Cq n V)) (Pi.single S w : Cq n V) = c • (Pi.single (S ∪ l.toFinset) w : Cq n V) := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons f t ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨c, hc, e⟩ := ih hl.2 fun i hi => hS i (List.mem_cons_of_mem f hi)
    have hf : f ∉ S ∪ t.toFinset := by
      rw [mem_union, not_or]
      exact ⟨hS f List.mem_cons_self, fun h => hl.1 (List.mem_toFinset.1 h)⟩
    have hU : S ∪ (f :: t).toFinset = insert f (S ∪ t.toFinset) := by
      rw [List.toFinset_cons, union_insert]
    refine ⟨c * sgL f (insert f (S ∪ t.toFinset)), mul_ne_zero hc (sgL_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, e, map_smul, creL_single f _ w hf, hU, smul_smul]

theorem suppL_degL_prod (P : Lt n → Prop) (l : List (Lt n)) (x : Cq n V) (j : ℕ) (hl : ∀ i ∈ l, P i)
    (hx : SuppL P x) (hd : DegL j x) :
    SuppL P (((l.map creL).prod : Module.End ℂ (Cq n V)) x) ∧
      DegL (j + l.length) (((l.map creL).prod : Module.End ℂ (Cq n V)) x) := by
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := creL_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := creL_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.LvChain

namespace GlobalTheory.CompanionTheory.LvChain


open GlobalTheory.CompanionTheory.FarReg in
theorem highest_preimage {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    (T : Submodule ℂ (Cq n V)) (a b : ι → Module.End ℂ (Cq n V)) (D : Module.End ℂ (Cq n V)) (y : Cq n V)
    (hT : FiniteDimensional ℂ T) (hadj : ∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) : ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  let e : Cq n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Lt n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Lt n) → V)).symm
  let c : Module.End ℂ (Cq n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Lt n) => V)) := fun f =>
    (e : Cq n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cq n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

theorem injUU_of_injRL : InjRL → InjUU := by
  intro hR n lam hlam lev hlev V _ _ E1 E2 hA u y hu hy hd hb
  have hm : Monotone lev := hlev.1
  have hP : IsPairA E1 E2 := ⟨hA.gl1, hA.gl2, hA.comm⟩
  have hup : ∀ a b : Fin n, a < b → kA E1 E2 a b u = 0 := fun a b hab => hu.2 a b hab rfl
  obtain ⟨T, hTf, hyT, hTS, hTs⟩ := _root_.GlobalTheory.CompanionTheory.LvStableChains.exists_stable n lev V E1 E2 _ y hA.locFin hy hd
  have hC := _root_.GlobalTheory.CompanionTheory.LvComm.lv_bd_comm n lev V E1 E2 hm hP
  have hone := _root_.GlobalTheory.CompanionTheory.LvChain.Lv_single_omU n lev V E1 E2 u hup
  obtain ⟨y', hy'T, hy'0, hy'b⟩ := highest_preimage
    (ι := {pq : Fin n × Fin n // pq.1 < pq.2 ∧ lev pq.1 = lev pq.2}) T
    (fun i => Lv lev E1 E2 i.1.1 i.1.2) (fun i => Lv lev E1 E2 i.1.2 i.1.1) (bdL (inUU lev) E1 E2) y hTf
    (fun i x z => _root_.GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint n lev V E1 E2 hA.unitK _ _ i.2.2 x z)
    (fun i t ht => hTs _ _ i.2.2 t ht)
    (fun i t ht => hTs _ _ i.2.2.symm t ht)
    (fun i t _ => (LinearMap.congr_fun (hC _ _ i.2.2) t).symm ▸ rfl)
    (fun i t _ => (LinearMap.congr_fun (hC _ _ i.2.2.symm) t).symm ▸ rfl) hyT
    (fun i => by rw [hb]; exact hone _ _ i.2.1 i.2.2)
  obtain ⟨hy's, hy'd⟩ := hTS y' hy'T
  obtain ⟨l, hnd, hmem, hcl⟩ := GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order n (fun _ => true) lev hm
  have hlc : ∀ e ∈ l, lev e.1.1 = lev e.1.2 := fun e he => by
    obtain ⟨-, h2⟩ := (hmem e).1 he
    refine le_antisymm (hm e.2.le) ?_
    by_contra h3
    exact h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, not_le.1 h3⟩)
  have hbd := _root_.GlobalTheory.CompanionTheory.LvChain.BdProdL.bd_prodL n lev V E1 E2 l y' hlc hcl hy's
    (fun e he => hy'0 ⟨e.1, e.2, hlc e he⟩)
  rw [bdL_inRR_eq E1 E2 hy's, hy'b, hb] at hbd
  set l' : List (Lt n) := l.map fun i => (false, i) with hl'
  have hmap : (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))) = l'.map creL := by
    rw [hl', List.map_map]; rfl
  have hnd' : l'.Nodup := hnd.map fun a b h => (Prod.ext_iff.1 h).2
  have hout : ∀ i ∈ l', i ∉ omU lev := by
    intro i hi h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
    have := (Finset.mem_filter.1 h).2.2
    have h2 := hlc e he
    simp only at this
    omega
  obtain ⟨c, hc0, hcw⟩ := prod_creL_single (V := V) l' (omU lev) u hnd' hout
  have hun : omU lev ∪ l'.toFinset = omN n := by
    ext ⟨t, i⟩
    simp only [Finset.mem_union, List.mem_toFinset, hl', List.mem_map, omU, omN, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | ⟨e, -, h⟩)
      · exact h.1
      · exact (Prod.ext_iff.1 h).1.symm
    · rintro rfl
      by_cases h2 : lev i.1.1 < lev i.1.2
      · exact Or.inl ⟨rfl, h2⟩
      · refine Or.inr ⟨i, (hmem i).2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, fun h => h2 (Finset.mem_filter.1 h).2.2⟩, rfl⟩
  have hcard : (omN n).card = (omU lev).card + l'.length := by
    rw [← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd']
    exact Finset.disjoint_left.2 fun i h1 h2 => hout i (List.mem_toFinset.1 h2) h1
  obtain ⟨hs1, hs2⟩ := suppL_degL_prod (V := V) (inRR lev) l' y' _
    (fun i hi => by obtain ⟨e, -, rfl⟩ := List.mem_map.1 hi; exact Or.inl rfl)
    (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd
  set C : Cq n V := ((l'.map creL).prod : Module.End ℂ (Cq n V)) y' with hCd
  have hsm : ∀ (s : ℂ) (x : Cq n V) (A : Finset (Lt n)), (s • x) A ≠ 0 → x A ≠ 0 :=
    fun s x A h h0 => h (by simp [h0])
  refine hR n lam hlam lev hlev V E1 E2 hA u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu ?_ ?_ ?_
  · exact fun A hA' => hs1 A (hsm _ C A hA')
  · intro A hA'
    have h3 := hs2 A (hsm _ C A hA')
    rw [h3, hcard]
    have : l'.length = l.length := by rw [hl', List.length_map]
    omega
  · rw [map_smul, hCd]
    rw [hmap] at hbd
    rw [hbd, hcw, hun, smul_smul, smul_smul]
    have hlen : l'.length = l.length := by rw [hl', List.length_map]
    have h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1 := by
      rw [← mul_pow]; simp
    have h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1 := by
      rw [mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]
    rw [h2, one_smul]

end GlobalTheory.CompanionTheory.LvChain
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.SubquotExt

theorem isSubquotient_sub_or_quot :
    ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  intro G V W _ _ _ _ _ ρ σ A B hAB hσ hB
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  unfold GlobalTheory.SmGL.IsSubquotient at hB ⊢
  obtain ⟨S, f, hf⟩ := hB
  let P : Submodule ℂ S.toSubmodule :=
    (A.toSubmodule.comap B.toSubmodule.subtype).comap S.toSubmodule.subtype
  have hNinv : ∀ (g : G) ⦃w : W⦄, w ∈ P.map f.toLinearMap → σ g w ∈ P.map f.toLinearMap := by
    intro g w hw
    rw [Submodule.mem_map] at hw ⊢
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    refine ⟨S.toRepresentation g s, A.apply_mem_toSubmodule g hs', ?_⟩
    exact f.isIntertwining _ _ g s
  let N : Subrepresentation σ := ⟨P.map f.toLinearMap, hNinv⟩
  let Z : Subrepresentation σ := ⟨⊥, by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]⟩
  let Fu : Subrepresentation σ := ⟨⊤, by
    intro g w _
    exact Submodule.mem_top⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · right
    have hle : N ≤ Z := by
      rw [hN]
      exact bot_le
    have hfP : P ≤ LinearMap.ker f.toLinearMap := by
      intro s hs
      have h0 : f.toLinearMap s ∈ (⊥ : Submodule ℂ W) := hle (Submodule.mem_map_of_mem hs)
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h0)
    let A' : Submodule ℂ B.toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
    have hQ : ∀ (g : G) (b : B.toSubmodule), GlobalTheory.SmGL.subQuot B A g (A'.mkQ b) =
        A'.mkQ (B.toRepresentation g b) := by
      intro g b
      first
      | rfl
      | (unfold GlobalTheory.SmGL.subQuot
         rw [Representation.quotient_apply]
         rfl)
    have hSinv : ∀ (g : G) ⦃x : B.toSubmodule ⧸ A'⦄, x ∈ S.toSubmodule.map A'.mkQ →
        GlobalTheory.SmGL.subQuot B A g x ∈ S.toSubmodule.map A'.mkQ := by
      intro g x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨B.toRepresentation g b, S.apply_mem_toSubmodule g hb, (hQ g b).symm⟩
    let S'' : Subrepresentation (GlobalTheory.SmGL.subQuot B A) := ⟨S.toSubmodule.map A'.mkQ, hSinv⟩
    let ψ0 : S.toSubmodule →ₗ[ℂ] (S.toSubmodule.map A'.mkQ) :=
      LinearMap.codRestrict _ (A'.mkQ ∘ₗ S.toSubmodule.subtype) (fun s => Submodule.mem_map_of_mem s.2)
    have hPker : P ≤ LinearMap.ker ψ0 := by
      intro s hs
      have hs' : (s : B.toSubmodule) ∈ A' := hs
      rw [LinearMap.mem_ker]
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero A').2 hs')
    have hkerP : LinearMap.ker ψ0 ≤ P := by
      intro s hs
      rw [LinearMap.mem_ker] at hs
      have h2 : (Submodule.Quotient.mk (s : B.toSubmodule) : B.toSubmodule ⧸ A') = 0 := congrArg Subtype.val hs
      exact (Submodule.Quotient.mk_eq_zero A').1 h2
    have hinj : Function.Injective (P.liftQ ψ0 hPker) :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot P ψ0 hPker hkerP)
    have hsurj : Function.Surjective (P.liftQ ψ0 hPker) := by
      intro x
      obtain ⟨y, hy⟩ := x
      rw [Submodule.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, rfl⟩
    let e := LinearEquiv.ofBijective (P.liftQ ψ0 hPker) ⟨hinj, hsurj⟩
    let F'' : (S.toSubmodule.map A'.mkQ) →ₗ[ℂ] W := P.liftQ f.toLinearMap hfP ∘ₗ e.symm.toLinearMap
    have key : ∀ s, F'' (ψ0 s) = f s := by
      intro s
      have he : ψ0 s = e (Submodule.Quotient.mk s) := rfl
      show P.liftQ f.toLinearMap hfP (e.symm (ψ0 s)) = f s
      rw [he, LinearEquiv.symm_apply_apply]
      rfl
    have hrep : ∀ (g : G) (s : S.toSubmodule), S''.toRepresentation g (ψ0 s) = ψ0 (S.toRepresentation g s) :=
      fun g s => Subtype.ext (hQ g s)
    have hψ0 : ∀ x : S.toSubmodule.map A'.mkQ, ∃ s, ψ0 s = x := by
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective P y
      exact ⟨s, rfl⟩
    let f'' : S''.toRepresentation.IntertwiningMap σ := ⟨F'', fun g => LinearMap.ext fun x => by
      obtain ⟨s, rfl⟩ := hψ0 x
      show F'' (S''.toRepresentation g (ψ0 s)) = σ g (F'' (ψ0 s))
      rw [hrep, key, key]
      exact f.isIntertwining _ _ g s⟩
    refine ⟨S'', f'', fun w => ?_⟩
    obtain ⟨s, rfl⟩ := hf w
    exact ⟨ψ0 s, key s⟩
  · left
    have hge : Fu ≤ N := by
      rw [hN]
      exact le_top
    have hAB' : A.toSubmodule ≤ B.toSubmodule := fun x hx => hAB hx
    have hS'inv : ∀ (g : G) ⦃a : A.toSubmodule⦄, a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') →
        A.toRepresentation g a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      intro g a ha
      exact S.apply_mem_toSubmodule g ha
    let S' : Subrepresentation A.toRepresentation := ⟨S.toSubmodule.comap (Submodule.inclusion hAB'), hS'inv⟩
    let r : (S.toSubmodule.comap (Submodule.inclusion hAB')) →ₗ[ℂ] S.toSubmodule :=
      (Submodule.inclusion hAB').restrict (fun a ha => ha)
    let f' : S'.toRepresentation.IntertwiningMap σ := ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun x => by
      show f.toLinearMap (r (S'.toRepresentation g x)) = σ g (f.toLinearMap (r x))
      exact f.isIntertwining _ _ g (r x)⟩
    refine ⟨S', f', fun w => ?_⟩
    have hw : w ∈ P.map f.toLinearMap := hge (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))
    rw [Submodule.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    have ha : (⟨((s : B.toSubmodule) : V), hs'⟩ : A.toSubmodule) ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      first
      | exact s.2
      | simpa using s.2
    exact ⟨⟨⟨((s : B.toSubmodule) : V), hs'⟩, ha⟩, rfl⟩

end GlobalTheory.CompanionTheory.SubquotExt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSepClosureOfRangeEq
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

theorem GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [Algebra F (Om l)] (K : FinExt l),
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) → IsSepClosure F (Om l) := by
  intro l _ F _ _ K hK
  have hmem : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Om l) q ∈ (algebraMap F (Om l)).fieldRange := by
    intro q
    have h : algebraMap ℚ_[l] (Om l) q ∈ Set.range (algebraMap F (Om l)) := by
      rw [hK]
      exact K.1.algebraMap_mem q
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  let e := (algebraMap F (Om l)).rangeRestrictFieldEquiv
  let φ : ℚ_[l] →+* F :=
    e.symm.toRingHom.comp ((algebraMap ℚ_[l] (Om l)).codRestrict (algebraMap F (Om l)).fieldRange hmem)
  have hφ : ∀ q, algebraMap F (Om l) (φ q) = algebraMap ℚ_[l] (Om l) q := by
    intro q
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨algebraMap ℚ_[l] (Om l) q, hmem q⟩)
    exact h
  have hcomp : (algebraMap F (Om l)).comp φ = algebraMap ℚ_[l] (Om l) := RingHom.ext hφ
  haveI : CharZero F := (algebraMap F (Om l)).charZero
  haveI halg : Algebra.IsAlgebraic F (Om l) := by
    constructor
    intro x
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact hpx
  exact IsSepClosure.mk inferInstance (Algebra.IsAlgebraic.isSeparable_of_perfectField)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open Classical in
def ker (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (v : GA E a) : ℂ :=
  if GeneralLinearGroup.map (pFin E) v ∈ U then β (toL (GeneralLinearGroup.map (pInf E) v).val) else 0

def tst (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (y : GA E a) : ℂ := ker U β y⁻¹

structure IsTest (β : Lie E a → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ β
  compact : HasCompactSupport β
  support : tsupport β ⊆ invSet E a

def ConjInv (β : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a), β (toL (k.1 * Matrix.of x * star k.1)) = β x

def dTest (X : Lie E a) (β : Lie E a → ℂ) (w : Lie E a) : ℂ :=
  fderiv ℝ β w (toL (Matrix.of w * Matrix.of X))

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem sphericalProduct_A4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  intro G _ _ _
  unfold PositivityTheory.SphericalProduct.A4
  intro D V _ _ π hπ hex
  obtain ⟨t, ht⟩ := hex
  refine ⟨fun v => GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN G D V π v, ?_⟩
  have hsm : GlobalTheory.PRep.IsSmooth π := by
    unfold GlobalTheory.PRep.IsAdmissible at hπ
    exact hπ.1
  have hH := _root_.GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique
  unfold PositivityTheory.Lbc.HeckeExistsUnique at hH
  obtain ⟨U, hU, -⟩ := hH G D.J D.isOpen_J D.isCompact_J V π hsm (t : G)
  exact _root_.GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective G D V π hπ t ht U hU

end GlobalTheory.CompanionTheory.Cass
end

