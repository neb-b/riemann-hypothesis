module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw

def finSecPullId {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) : LB.Sec (M.pull (𝟙 X)) where
  f := fun j => rs X (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) (s.f (j PUnit.unit))
  compat := fun i j => by
    have h := congrArg (rs X (inf_le_inf (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) i PUnit.unit)
      (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) :
        (M.pull (𝟙 X)).U i ⊓ (M.pull (𝟙 X)).U j ≤ M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)))
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at h
    erw [rs_rs, rs_rs] at h
    erw [rs_rs, rs_rs, h]
    congr 1
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    rfl

theorem finSec_eq_zero_of_cover {X : Scheme.{0}} {I : Type} (V : I → X.Opens) (hV : ⨆ i, V i = ⊤)
    {U : X.Opens} (x : Γ(X, U)) (hx : ∀ i, rs X (inf_le_left : U ⊓ V i ≤ U) x = 0) : x = 0 := by
  refine X.sheaf.eq_of_locally_eq' (fun i => U ⊓ V i) U (fun i => homOfLE inf_le_left) ?_ x 0 ?_
  · rw [← inf_iSup_eq, hV, inf_top_eq]
  · intro i
    exact (hx i).trans (map_zero (rs X (inf_le_left : U ⊓ V i ≤ U))).symm

theorem Perf.exists_relation {X : Scheme.{0}} {K : Type} [Field K] {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} (Q : Perf f M) (s : Fin (Q.a + 1) → LB.Sec M) :
    ∃ c : Fin (Q.a + 1) → K, c ≠ 0 ∧ ∀ i, ∑ k, cst f (M.U i) (c k) * (s k).f i = 0 := by
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec K (RingHom.id K) X (𝟙 X) f hpb
  let v : Fin (Q.a + 1) → Fin Q.a → K := fun k => (E.symm (finSecPullId (s k))).1
  have hv : ∀ k j, rs X (Q.le j) ((s k).f (Q.ch j)) = ∑ l, cst f (Q.W j) (v k l) * Q.u l j := by
    intro k j
    have h := hE (E.symm (finSecPullId (s k))) j
    rw [Equiv.apply_symm_apply] at h
    refine Eq.trans ?_ h
    exact (rs_rs _ _ _).symm
  have hdep : ¬ LinearIndependent K v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, k₀, hk₀⟩ := hdep
  have hc' : ∀ l, ∑ k, c k * v k l = 0 := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply] using this
  have hW : ∀ j, ∑ k, cst f (Q.W j) (c k) * rs X (Q.le j) ((s k).f (Q.ch j)) = 0 := by
    intro j
    simp only [hv, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Finset.sum_mul, ← map_sum, hc', map_zero, zero_mul, Finset.sum_const_zero]
  refine ⟨c, fun h => hk₀ (congrFun h k₀), fun i => ?_⟩
  refine finSec_eq_zero_of_cover Q.W Q.cover _ fun j => ?_
  have h₁ : ∀ k, rs X (inf_le_left : M.U i ⊓ Q.W j ≤ M.U i) ((s k).f i) =
      rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)) (M.g i (Q.ch j)).val *
        rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j) (rs X (Q.le j) ((s k).f (Q.ch j))) := by
    intro k
    have h := congrArg (rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)))
      ((s k).compat i (Q.ch j))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  have h₂ := congrArg (rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j)) (hW j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rs_cst, map_zero] at h₂
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rs_cst, h₁]
  simp only [mul_left_comm (cst f _ _), ← Finset.mul_sum, h₂, mul_zero]

theorem sections_finite_of_perf
    (hperf : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M))
    (hva : ∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)),
      IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)),
        (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s)
    (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left)
    (hM : M.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
      ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  obtain ⟨N, -, m, σ, hLB, hσ⟩ := hva _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.id_horiz _)
  have hsm : Smooth P.A.hom := by
    haveI := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g _
  obtain ⟨Q⟩ := hperf K P.A.left P.A.hom hsm ⟨_, hLB, m, σ, hσ⟩ M hM
  refine ⟨Q.a + 1, fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := Q.exists_relation s
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c k), fun h0 => hc ?_, h⟩
  funext k
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  exact hinj ((congrFun h0 k).trans (map_zero _).symm)

end GlobalTheory.AbLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TrivLocus

theorem exists_ker_iff_minors {K : Type} [Field K] {a b : ℕ} (D : Matrix (Fin b) (Fin a) K) :
    (∃ v : Fin a → K, v ≠ 0 ∧ D.mulVec v = 0) ↔ ∀ σ : Fin a → Fin b, (D.submatrix σ id).det = 0 := by
  classical
  constructor
  · rintro ⟨v, hv, h⟩ σ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    funext i
    exact congrFun h (σ i)
  · intro h
    by_contra hn
    have hinj : Function.Injective D.mulVec := by
      intro v w e
      by_contra hvw
      exact hn ⟨v - w, sub_ne_zero.2 hvw, by rw [Matrix.mulVec_sub, e, sub_self]⟩
    have hcol : LinearIndependent K D.col := Matrix.mulVec_injective_iff.1 hinj
    have hrank : D.rank = a := by
      rw [← Matrix.rank_transpose]
      have := LinearIndependent.rank_matrix (M := D.transpose) hcol
      simpa using this
    obtain ⟨κ, e, -, hspan, hli⟩ := exists_linearIndependent' K D.row
    have : Finite κ := hli.finite
    let _ : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hrank]
    let ε : Fin a ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent K (D.submatrix (e ∘ ε) id).row := hli.comp ε ε.injective
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')
    exact hu.ne_zero (h _)

theorem nontrivial_ker_iff {R K : Type} [CommRing R] [Field K] (g : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) :
    Nontrivial {v : Fin a → K // (D.map g).mulVec v = 0} ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det ∈ RingHom.ker g := by
  have h := exists_ker_iff_minors (D.map g)
  have h' : ∀ σ : Fin a → Fin b, ((D.map g).submatrix σ id).det = g (D.submatrix σ id).det := fun σ => by
    rw [RingHom.map_det]; rfl
  simp only [h'] at h
  simp only [RingHom.mem_ker]
  rw [← h, nontrivial_iff_exists_ne ⟨0, Matrix.mulVec_zero _⟩]
  exact ⟨fun ⟨v, hv⟩ => ⟨v.1, fun e => hv (Subtype.ext e), v.2⟩,
    fun ⟨v, hv, e⟩ => ⟨⟨v, e⟩, fun e' => hv (congrArg Subtype.val e')⟩⟩

variable {X Y : Scheme.{0}}

def zeroSec (N : LB X) : LB.Sec N where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem nontrivial_sec_iff (N : LB X) : Nontrivial (LB.Sec N) ↔ ∃ (s : LB.Sec N) (i : N.ι), s.f i ≠ 0 := by
  rw [nontrivial_iff_exists_ne (zeroSec N)]
  refine exists_congr fun s => ?_
  obtain ⟨sf, hs⟩ := s
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have : sf = fun _ => 0 := funext hn
    subst this
    exact h rfl
  · rintro ⟨i, hi⟩ h
    exact hi (congrArg (fun s => s.f i) h)

theorem pull_pw (M : LB X) (π : Y ⟶ X) (t : ℤ) : (pw M t).pull π = pw (M.pull π) t := by
  refine congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_
  funext j j'
  change ∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t
  refine Eq.trans ?_ (Finset.prod_zpow (G := Γ(Y, LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)
  exact (congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)

theorem rs_ne_zero [IsIntegral X] {U V : X.Opens} (h : V ≤ U) (hV : (V : Set X).Nonempty) {x : Γ(X, U)}
    (hx : x ≠ 0) : rs X h x ≠ 0 := by
  have : Nonempty V := hV.to_subtype
  intro e
  exact hx (map_injective_of_isIntegral X (homOfLE h) (e.trans (map_zero _).symm))

theorem nonempty_of_ne_zero {U : X.Opens} {x : Γ(X, U)} (hx : x ≠ 0) : (U : Set X).Nonempty := by
  by_contra h
  have : U = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h)
  subst this
  exact hx (Subsingleton.elim _ _)

theorem triv_iff [IsIntegral X] (hX : IsField Γ(X, ⊤)) (N : LB X) (hN : ⨆ i, N.U i = ⊤) :
    Triv N ↔ Nontrivial (LB.Sec N) ∧ Nontrivial (LB.Sec (pw N (-1))) := by
  rw [nontrivial_sec_iff, nontrivial_sec_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, N.U i := by rw [hN]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have : Nonempty (N.U i) := ⟨⟨x, hi⟩⟩
    refine ⟨⟨⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩, i, (t.s i).ne_zero⟩,
      ⟨⟨fun i => ((t.s i)⁻¹).val, fun i j => ?_⟩, i, ((t.s i)⁻¹).ne_zero⟩⟩
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    rw [← zpow_neg_one (N.g i j)] at h
    exact congrArg Units.val h
  · rintro ⟨⟨s, i, hi⟩, ⟨s'', j, hj⟩⟩
    let s' : ∀ k : N.ι, Γ(X, N.U k) := s''.f
    change N.ι at j
    change s' j ≠ 0 at hj
    have hc : ∀ k l, rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k * s' k) =
        rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l * s' l) := by
      intro k l
      have h₁ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k) =
        (N.g k l).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l) := s.compat k l
      have h₂ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s' k) =
        (N.g k l ^ (-1 : ℤ)).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s' l) := s''.compat k l
      rw [map_mul, map_mul, h₁, h₂, _root_.mul_mul_mul_comm, ← Units.val_mul, zpow_neg_one, mul_inv_cancel,
        Units.val_one, _root_.one_mul]
    obtain ⟨h, hh, -⟩ := X.sheaf.existsUnique_gluing' N.U ⊤ (fun _ => homOfLE le_top) hN.ge
      (fun k => s.f k * s' k) hc
    change Γ(X, ⊤) at h
    have hh' : ∀ k, rs X (le_top : N.U k ≤ ⊤) h = s.f k * s' k := hh
    have hne : (↑(N.U i ⊓ N.U j) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen (nonempty_of_ne_zero hi) (nonempty_of_ne_zero hj)
    have hsj : s.f j ≠ 0 := by
      intro e
      have h₁ : rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i) =
        (N.g i j).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j) := s.compat i j
      rw [e, map_zero, mul_zero] at h₁
      exact rs_ne_zero _ hne hi h₁
    have : Nonempty (N.U j) := (nonempty_of_ne_zero hsj).to_subtype
    have h0 : h ≠ 0 := by
      intro e
      have := hh' j
      rw [e, map_zero] at this
      exact mul_ne_zero hsj hj this.symm
    have hu : IsUnit h := by
      obtain ⟨c, hc⟩ := hX.mul_inv_cancel h0
      exact IsUnit.of_mul_eq_one c hc
    have hs : ∀ k, IsUnit (s.f k) := fun k =>
      isUnit_of_mul_isUnit_left (hh' k ▸ hu.map (rs X (le_top : N.U k ≤ ⊤)))
    exact ⟨⟨fun k => (hs k).unit⟩, fun k l => Units.ext (s.compat k l)⟩

theorem triv_fibre_iff {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (hM : M.IsLB)
    (P : Perf f M) (Q : Perf f (pw M (-1))) [IsProper f] [GeometricallyIntegral f]
    {K : Type} [Field K] (g : R →+* K) {X' : Scheme.{0}} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Triv (M.pull π) ↔ (∀ σ : Fin P.a → Fin P.b, (P.D₀.submatrix σ id).det ∈ RingHom.ker g) ∧
      ∀ σ : Fin Q.a → Fin Q.b, (Q.D₀.submatrix σ id).det ∈ RingHom.ker g := by
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ h
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  obtain ⟨E, -⟩ := P.sec K g X' π f' h
  obtain ⟨E', -⟩ := Q.sec K g X' π f' h
  rw [triv_iff (isField_of_universallyClosed K f') _ (LB.isLB_linComb hM _ _).cover, ← pull_pw,
    ← nontrivial_ker_iff, ← nontrivial_ker_iff, E.nontrivial_congr, E'.nontrivial_congr]

theorem isClosed_trivLocus :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → IsClosed {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
  rintro R _ X f M hM ⟨P⟩ ⟨Q⟩ _ _
  convert PrimeSpectrum.isClosed_zeroLocus
    ((Set.range fun σ : Fin P.a → Fin P.b => (P.D₀.submatrix σ id).det) ∪
      Set.range fun σ : Fin Q.a → Fin Q.b => (Q.D₀.submatrix σ id).det)
  rename_i p
  change _ ↔ p ∈ PrimeSpectrum.zeroLocus _
  rw [PrimeSpectrum.mem_zeroLocus, Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · rintro ⟨K, _, g, X', π, f', hg, h, ht⟩
    rw [← hg]
    exact (triv_fibre_iff hM P Q g h).1 ht
  · intro hp
    have hk : RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal := Ideal.ker_algebraMap_residueField _
    refine ⟨p.asIdeal.ResidueField, inferInstance, algebraMap R _, _, _, _, hk, IsPullback.of_hasPullback _ _, ?_⟩
    refine (triv_fibre_iff hM P Q _ (IsPullback.of_hasPullback _ _)).2 ?_
    rw [hk]
    exact hp

end GlobalTheory.TrivLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isOpenImmersion_of_section_of_etale {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have : Etale (s ≫ f) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp s f
  have : Mono s := (SplitMono.mk f hs).mono
  exact IsOpenImmersion.of_flat_of_mono s

theorem exists_section_of_etale {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Etale f] (x : X) :
    ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = 𝟙 _ ∧ x ∈ Set.range s := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let W : Set X := ⋃ s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = 𝟙 _}, Set.range s.1
  have hW : IsOpen W := isOpen_iUnion fun s => by
    have := isOpenImmersion_of_section_of_etale f s.1 s.2
    exact s.1.isOpenEmbedding.isOpen_range
  have hx : x ∈ W := by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := Wᶜ) ⟨x, hx⟩
      hW.isClosed_compl.isLocallyClosed
    replace hc' : IsClosed {c} := hc'
    exact hc (Set.mem_iUnion.mpr ⟨⟨_, pointOfClosedPoint_comp f c hc'⟩,
      IsLocalRing.closedPoint K, pointOfClosedPoint_apply f c hc' _⟩)
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  exact ⟨s.1, s.2, hs⟩

theorem exists_local_rational_torsion {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (n : ℕ) [Etale (mulA A n).left]
    {Z : Over (Spec (CommRingCat.of K))} (d : Z ⟶ A) (hd : d ^ n = 1) (p : Z.left) :
    ∃ (W : Over (Spec (CommRingCat.of K))) (c : W ⟶ Z) (_ : IsOpenImmersion c.left),
      p ∈ Set.range c.left ∧ ∃ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A,
        y ^ n = 1 ∧ c ≫ d = toUnit W ≫ y := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of K))},
      (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have e : d.left ≫ (mulA A n).left = Z.hom ≫ η[A].left := by
    rw [← Over.comp_left, hmul, hd, hone]
  let l : Z.left ⟶ pullback (mulA A n).left η[A].left := pullback.lift _ _ e
  obtain ⟨s, hs, t, ht⟩ := exists_section_of_etale (K := K)
    (pullback.snd (mulA A n).left η[A].left) (l p)
  have := isOpenImmersion_of_section_of_etale (pullback.snd (mulA A n).left η[A].left) s hs
  have hy : (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ A.hom = 𝟙 _ := by
    rw [← Over.w (mulA A n), Category.assoc, pullback.condition_assoc]
    erw [hη]
    exact (congrArg (s ≫ ·) (Category.comp_id _)).trans hs
  let y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A := Over.homMk _ hy
  refine ⟨Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, y, ?_, ?_⟩
  · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p t ht.symm
    exact ⟨w, hw⟩
  · rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    change (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ (mulA A n).left = 𝟙 _ ≫ η[A].left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ η[A].left) hs
  · apply Over.OverMorphism.ext
    change pullback.fst l s ≫ d.left =
      (pullback.fst l s ≫ Z.hom) ≫ s ≫ pullback.fst (mulA A n).left η[A].left
    have h1 : d.left = l ≫ pullback.fst (mulA A n).left η[A].left := (pullback.lift_fst _ _ _).symm
    have h2 : Z.hom = l ≫ pullback.snd (mulA A n).left η[A].left := (pullback.lift_snd _ _ _).symm
    have h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s := by
      rw [h2, pullback.condition_assoc]
      exact (congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)
    rw [h3, h1, pullback.condition_assoc]

theorem existsUnique_appTop_eq_of_flat {X Y : Scheme.{0}} (m : X ⟶ Y) [QuasiCompact m]
    [Surjective m] [Flat m] (f : Γ(X, ⊤))
    (h : ∀ {Z : Scheme.{0}} (a b : Z ⟶ X), a ≫ m = b ≫ m → a ≫ TLinPf.mOf f = b ≫ TLinPf.mOf f) :
    ∃! g : Γ(Y, ⊤), m.appTop.hom g = f := by
  refine ⟨TLinPf.fnOf (EffectiveEpi.desc m (TLinPf.mOf f) h), ?_, ?_⟩
  · beta_reduce
    rw [← TLinPf.fnOf_comp, EffectiveEpi.fac, TLinPf.fnOf_mOf]
  · intro g hg
    rw [← TLinPf.fnOf_mOf g]
    congr 1
    apply EffectiveEpi.uniq
    rw [TLinPf.comp_mOf, hg]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem existsUnique_descend_of_torsion_invariant {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [Etale (mulA A n).left] [Surjective (mulA A n).left] [QuasiCompact (mulA A n).left]
    (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U))
    (hf : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤
        ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) :
    ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  let m := (mulA A n).left
  have hm : m = (mulA A n).left := rfl
  let V := m ⁻¹ᵁ U
  let f' : Γ(V, ⊤) := V.topIso.inv.hom f
  have key : ∀ {Z : Scheme.{0}} (a b : Z ⟶ V), a ≫ (m ∣_ U) = b ≫ (m ∣_ U) →
      a ≫ TLinPf.mOf f' = b ≫ TLinPf.mOf f' := by
    intro Z a b hab
    have hab' : (a ≫ V.ι) ≫ m = (b ≫ V.ι) ≫ m := by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% hab]
    have hw : (a ≫ V.ι) ≫ A.hom = (b ≫ V.ι) ≫ A.hom := by
      rw [← Over.w (mulA A n), ← hm, ← Category.assoc, hab', Category.assoc _ m]
    let FinalForm : Over (Spec (CommRingCat.of K)) := Over.mk ((b ≫ V.ι) ≫ A.hom)
    let z₁ : FinalForm ⟶ A := Over.homMk (a ≫ V.ι) hw
    let z₂ : FinalForm ⟶ A := Over.homMk (b ≫ V.ι) rfl
    have hz : z₁ ^ n = z₂ ^ n := by
      rw [← hmul, ← hmul]
      exact Over.OverMorphism.ext hab'
    have hd : (z₁ * z₂⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hz, mul_inv_cancel]
    have hloc := exists_local_rational_torsion A n _ hd
    choose W c hc hp y hy hcy using hloc
    let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Z (fun p => (W p).left)
      (fun p => (c p).left) (fun p => ⟨p, hp p⟩) hc
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change (c p).left ≫ a ≫ _ = (c p).left ≫ b ≫ _
    let t : A ⟶ A := (toUnit A ≫ y p) * 𝟙 A
    have htm : t ≫ mulA A n = mulA A n := by
      rw [hmul, mul_pow, ← MonObj.comp_pow, hy p, MonObj.comp_one, _root_.one_mul]
    have htm' : t.left ≫ m = m := by rw [hm, ← Over.comp_left, htm]
    have e : V ≤ t.left ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, htm']
    have h1 : c p ≫ z₁ = c p ≫ z₂ ≫ t := by
      have h2 := hcy p
      rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul] at h2
      rw [h2, ← Category.assoc _ z₂, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    have h3 : (c p).left ≫ a = (c p).left ≫ b ≫ t.left.resLE V V e := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
      have := congr(($h1).left)
      simpa [z₁, z₂] using this
    have h4 : t.left.resLE V V e ≫ TLinPf.mOf f' = TLinPf.mOf f' := by
      rw [TLinPf.comp_mOf]
      congr 1
      exact (resLE_appTop_topIso_inv t.left e f).trans (congrArg _ (hf _ (hy p) e))
    rw [← Category.assoc, h3, Category.assoc, Category.assoc, h4]
  have : Surjective (m ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨g, hg, hu⟩ := existsUnique_appTop_eq_of_flat (m ∣_ U) f' key
  have h7 : ∀ g : Γ(A.left, U), (m ∣_ U).appTop.hom (U.topIso.inv.hom g) =
      V.topIso.inv.hom ((m.app U).hom g) := fun g => by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_topIso_inv, Scheme.Hom.appLE_eq_app]
  have hV : Function.Injective V.topIso.inv.hom := V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hU : Function.Bijective U.topIso.inv.hom := U.topIso.symm.commRingCatIsoToRingEquiv.bijective
  obtain ⟨g, rfl⟩ := hU.2 g
  refine ⟨g, hV ((h7 g).symm.trans hg), fun g' hg' => hU.1 (hu _ ?_)⟩
  exact (h7 g').trans (congrArg _ hg')

theorem torsion_invariant_descends :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧
        (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ),
      (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)),
      (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 →
        ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤
          ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)),
          (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) →
      ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f := by
  intro H K _ _ P n hn U f hf
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => hn (by rw [h, Nat.cast_zero])
  obtain ⟨h1, -, h3, h4⟩ := H _ P n hn1
  have : Etale (mulA P.A n).left := h4 (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : IsCommMonObj P.A := P.isAb.comm
  exact existsUnique_descend_of_torsion_invariant P.A n U f hf

end GlobalTheory
end

