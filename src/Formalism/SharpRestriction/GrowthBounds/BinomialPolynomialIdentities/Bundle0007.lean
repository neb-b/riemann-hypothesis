module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.FormalSeriesConditionsB1ToB4
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0023

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleLowerSetSpan
section
namespace Formalism.MainNotions.G.ColumnFamilies

theorem admissible_lowerSet_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.SaturatedLowerSetSpan D := saturatedLowerSetSpan_of_lowerSetTypesSpan D (lower_set_types_span D)

end Formalism.MainNotions.G.ColumnFamilies
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DisjointRestrictSupportOfDisjoint
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt

theorem disjoint_restrictSupport_of_disjoint {R σ : Type*} [CommRing R] {s t : Set (σ →₀ ℕ)} (h : Disjoint s t) :
    Disjoint (MvPolynomial.restrictSupport R s) (MvPolynomial.restrictSupport R t) := by
  rw [Submodule.disjoint_def]
  intro x hs ht
  rw [MvPolynomial.mem_restrictSupport_iff] at hs ht
  by_contra hx
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx
  exact (Set.disjoint_left.1 h) (hs (by simpa using hm)) (ht (by simpa using hm))

theorem linearIndependent_words_all_degrees (R : Type) [CommRing R] (N n : ℕ) (LL : Letters (Fin N)) :
    LinearIndependent R (fun x : (Σ b : Fin N → ℕ, WI n N LL b) => Psi R x.2.1.1.mu x.2.1.2) := by
  refine linearIndependent_iUnion_finite (f := fun (b : Fin N → ℕ) (x : WI n N LL b) => Psi R x.1.1.mu x.1.2)
    (fun b => (standardPath_basis_any_ring R N n LL b).1) ?_
  intro b t _ hb
  have h1 : ∀ b' : Fin N → ℕ, Submodule.span R (Set.range fun x : WI n N LL b' => Psi R x.1.1.mu x.1.2) ≤
      Pol R n b' := by
    intro b'
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact standardWord_mem_multihomogeneous R x.1.1 x.1.2 x.2
  have h2 : (⨆ i ∈ t, Submodule.span R (Set.range fun x : WI n N LL i => Psi R x.1.1.mu x.1.2)) ≤
      MvPolynomial.restrictSupport R {m : Fin N × Fin n →₀ ℕ | ∃ i ∈ t, ∀ j, multideg m j = i j} := by
    refine iSup₂_le fun i hi => (h1 i).trans ?_
    intro x hx
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hx
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    exact ⟨i, hi, hx hm⟩
  refine Disjoint.mono (h1 b) h2 (disjoint_restrictSupport_of_disjoint ?_)
  rw [Set.disjoint_left]
  rintro m hm ⟨i, hi, hmi⟩
  apply hb
  have : b = i := by
    funext j
    rw [← hm j, hmi j]
  rw [this]
  exact hi

section Theta

variable (R : Type) [CommRing R] (N r K : ℕ)

def towerToPolynomialHom : MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) →+*
    MvPolynomial (Fin N × Fin (r + K)) R :=
  MvPolynomial.eval₂Hom (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom
    (fun v => X (plVar (K := K) v))

def joinVarsRingHom : MvPolynomial (Fin N × Fin (r + K)) R →+*
    MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun v => Fin.addCases (motive := fun _ => MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R))
      (fun a => X (v.1, a)) (fun b => C (X (v.1, b))) v.2)

theorem towerToPolynomialHom_C_eq_rename_tan (s : MvPolynomial (Fin N × Fin K) R) : towerToPolynomialHom R N r K (C s) = rename (tanVar (r := r)) s := by
  simp [towerToPolynomialHom]

theorem towerToPolynomialHom_X_eq_X_pl (v : Fin N × Fin r) : towerToPolynomialHom R N r K (X v) = X (plVar (K := K) v) := by
  simp [towerToPolynomialHom]

theorem joinVarsRingHom_comp_towerToPolynomialHom_eq_id : (joinVarsRingHom R N r K).comp (towerToPolynomialHom R N r K) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro s
    have : ((joinVarsRingHom R N r K).comp (towerToPolynomialHom R N r K)).comp MvPolynomial.C = (RingHom.id _).comp MvPolynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [towerToPolynomialHom_C_eq_rename_tan, joinVarsRingHom]
      · intro w
        simp [towerToPolynomialHom_C_eq_rename_tan, joinVarsRingHom, tanVar]
    exact congrArg (fun f => f s) this
  · intro v
    simp [towerToPolynomialHom_X_eq_X_pl, joinVarsRingHom, plVar]

theorem towerToPolynomialHom_injective : Function.Injective (towerToPolynomialHom R N r K) := by
  intro x y h
  have := congrArg (joinVarsRingHom R N r K) h
  have e : ∀ z, joinVarsRingHom R N r K (towerToPolynomialHom R N r K z) = z := fun z => congrArg (fun f => f z) (joinVarsRingHom_comp_towerToPolynomialHom_eq_id R N r K)
  rwa [e, e] at this

theorem towerToPolynomialHom_map_C_eq_rename_pl (a : MvPolynomial (Fin N × Fin r) R) :
    towerToPolynomialHom R N r K (MvPolynomial.map MvPolynomial.C a) = rename (plVar (K := K)) a := by
  have : (towerToPolynomialHom R N r K).comp (MvPolynomial.map MvPolynomial.C) =
      (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [towerToPolynomialHom_C_eq_rename_tan]
    · intro v
      simp [towerToPolynomialHom_X_eq_X_pl]
  exact congrArg (fun f => f a) this

def towerToPolynomialLinearMap : MvPolynomial (Fin N × Fin r) (MvPolynomial (Fin N × Fin K) R) →ₗ[R]
    MvPolynomial (Fin N × Fin (r + K)) R where
  toFun := towerToPolynomialHom R N r K
  map_add' := map_add _
  map_smul' := by
    intro c x
    have h1 : c • x = C (C c) * x := by
      rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    rw [h1, map_mul, towerToPolynomialHom_C_eq_rename_tan, rename_C, RingHom.id_apply, MvPolynomial.smul_eq_C_mul]

end Theta

theorem linearIndependent_productBasis (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    LinearIndependent R (pvec R r K LL B) := by
  classical
  have hb := linearIndependent_words_all_degrees R N K LL
  have hc := linearIndependent_words_all_degrees (MvPolynomial (Fin N × Fin K) R) N r LL
  have hbc := linearIndependent_smul hb hc
  have hex : ∀ x : PIdx r K LL B, ∃ y : (Σ b : Fin N → ℕ, WI K N LL b) × (Σ b : Fin N → ℕ, WI r N LL b),
      y.1.2.1.1.mu = x.1.2.1 ∧ y.1.2.1.2 = x.1.2.2 ∧ y.2.2.1.1.mu = x.1.1.1 ∧ y.2.2.1.2 = x.1.1.2 := by
    rintro ⟨⟨⟨nu, I'⟩, ⟨ka, I''⟩⟩, ⟨b', b'', _, ⟨P1, e1⟩, ⟨P2, e2⟩⟩, h2, h3⟩
    have e1' : P1.mu = nu := e1
    have e2' : P2.mu = ka := e2
    have h2' : IsSt P1.mu I' := by rw [e1']; exact h2
    have h3' : IsSt P2.mu I'' := by rw [e2']; exact h3
    exact ⟨(⟨b'', ⟨(P2, I''), h3'⟩⟩, ⟨b', ⟨(P1, I'), h2'⟩⟩), e2', rfl, e1', rfl⟩
  choose io hio using hex
  have hinj : Function.Injective io := by
    intro x y hxy
    obtain ⟨a1, a2, a3, a4⟩ := hio x
    obtain ⟨c1, c2, c3, c4⟩ := hio y
    rw [hxy] at a1 a2 a3 a4
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rw [← a3, c3]
      · rw [← a4, c4]
    · apply Prod.ext
      · rw [← a1, c1]
      · rw [← a2, c2]
  have h1 := (hbc.comp io hinj).map' (towerToPolynomialLinearMap R N r K)
    (LinearMap.ker_eq_bot.2 (towerToPolynomialHom_injective R N r K))
  have h2 : (⇑(towerToPolynomialLinearMap R N r K) ∘ (fun p : (Σ b : Fin N → ℕ, WI K N LL b) × (Σ b : Fin N → ℕ, WI r N LL b) =>
      Psi R p.1.2.1.1.mu p.1.2.1.2 • Psi (MvPolynomial (Fin N × Fin K) R) p.2.2.1.1.mu p.2.2.1.2) ∘ io) =
      pvec R r K LL B := by
    funext x
    obtain ⟨a1, a2, a3, a4⟩ := hio x
    simp only [Function.comp_apply]
    rw [a1, a2, a3, a4]
    change towerToPolynomialHom R N r K _ = _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, towerToPolynomialHom_C_eq_rename_tan, ← map_Psi' (MvPolynomial.C : R →+* _), towerToPolynomialHom_map_C_eq_rename_pl]
    unfold pvec PsiPl PsiTan
    rw [mul_comm]
  rw [← h2]
  exact h1

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsIsotypicDecomposition
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem span_inter_eq_span_image {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    {σ X : Type} (bO : X → MvPolynomial σ O) (bK : X → MvPolynomial σ Kf)
    (hmap : ∀ x, MvPolynomial.map (algebraMap O Kf) (bO x) = bK x) (hLI : LinearIndependent Kf bK)
    (Y : Submodule Kf (MvPolynomial σ Kf)) (A : Set X)
    (hY : Submodule.span Kf (Set.range bK) ⊓ Y = Submodule.span Kf (bK '' A)) :
    {f | f ∈ Submodule.span O (Set.range bO) ∧ MvPolynomial.map (algebraMap O Kf) f ∈ Y} =
      (Submodule.span O (bO '' A) : Set _) := by
  classical
  have hmaplc : ∀ c : X →₀ O, MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) =
      Finsupp.linearCombination Kf bK (c.mapRange (algebraMap O Kf) (map_zero _)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmap, ← MvPolynomial.smul_eq_C_mul]
  ext G
  constructor
  · rintro ⟨hG, hGY⟩
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hG
    change (c.sum fun x a => a • bO x) ∈ Submodule.span O (bO '' A)
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
    have h1 : MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) ∈
        Submodule.span Kf (bK '' A) := by
      rw [← hY]
      refine ⟨?_, hGY⟩
      rw [hmaplc]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩
    obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Kf).1 h1
    rw [hmaplc] at hle
    have hlc := hLI hle
    have hxl : x ∈ l.support := by
      rw [hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      intro h0
      exact (Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))
    exact (Finsupp.mem_supported Kf l).1 hl hxl
  · intro hG
    change G ∈ Submodule.span O (bO '' A) at hG
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
      rw [hmap]
      have : bK x ∈ Submodule.span Kf (Set.range bK) ⊓ Y := by
        rw [hY]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      exact this.2
    | zero => exact ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨Submodule.add_mem _ hx.1 hy.1, by rw [map_add (f := _)]; exact Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨Submodule.smul_mem _ _ hx.1, by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hx.2⟩

abbrev GLWeightLabels (N r K : ℕ) : Fin (N + 1) ⊕ Fin (N + 1) → Type
  | .inl _ => Fin r → ℤ
  | .inr _ => Fin K → ℤ

structure ExternalProductHyps : Prop where
  p16 : ExternalProductBasis
  e1 : GlOperatorsFormRepresentation
  e2 : IsotypicZeroOfNonDominant
  e3 : ProjectorsPreserveMultidegree
  e5a : ProjectorsCommuteNested
  e5b : ProjectorsCommuteDisjoint
  lowPl : RestLowPl
  lowTan : RestLowTan
  sum : RestJointSum

section

variable (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) {F : Type} [Field F] [CharZero F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
  (B : Fin N → ℕ)

include D H in
theorem exists_decSys_isoSub_glOpsE_of_injective {m k : ℕ} (S : Set (Fin N)) (e : Fin m → Fin k) (he : Function.Injective e) :
    ∃ pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F), DecSys (isoSub (glOpsE F LL S e)) pr :=
  isoDecomp (glOpsE F LL S e) D (weight_condition_from_integral_form D) (H.e1 F N m k LL S e he)

abbrev EPl (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps r F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)

abbrev ETan (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps K F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)

def prPl (i : Fin (N + 1)) : (Fin r → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

def prTan (i : Fin (N + 1)) : (Fin K → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem prPl_sys (i : Fin (N + 1)) : DecSys (isoSub (EPl F r K LL i)) (prPl D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

theorem prTan_sys (i : Fin (N + 1)) : DecSys (isoSub (ETan F r K LL i)) (prTan D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem initialSegments_nested (i j : Fin (N + 1)) :
    ({l : Fin N | l.val < i.val} ⊆ {l : Fin N | l.val < j.val}) ∨
      ({l : Fin N | l.val < j.val} ⊆ {l : Fin N | l.val < i.val}) := by
  rcases le_total i j with h | h
  · exact Or.inl fun l (hl : l.val < i.val) => lt_of_lt_of_le hl h
  · exact Or.inr fun l (hl : l.val < j.val) => lt_of_lt_of_le hl h

theorem fin_castAdd_ne_natAdd (a : Fin r) (b : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

def externalProductJointData : JointData F (MvPolynomial (Fin N × Fin (r + K)) F) (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K)
    (PIdx r K LL B) where
  le := fun s => match s with
    | .inl _ => DomLE
    | .inr _ => DomLE
  dom := fun s => match s with
    | .inl _ => Dominant
    | .inr _ => Dominant
  le_refl := fun s => match s with
    | .inl _ => fun a => dominance_refl a
    | .inr _ => fun a => dominance_refl a
  le_trans := fun s => match s with
    | .inl _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
    | .inr _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
  le_antisymm := fun s => match s with
    | .inl _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
    | .inr _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
  W := fun s => match s with
    | .inl i => isoSub (EPl F r K LL i)
    | .inr i => isoSub (ETan F r K LL i)
  e := fun s => match s with
    | .inl i => prPl D H r K LL i
    | .inr i => prTan D H r K LL i
  sys := fun s => match s with
    | .inl i => prPl_sys D H r K LL i
    | .inr i => prTan_sys D H r K LL i
  comm := fun s t => match s, t with
    | .inl i, .inl j => fun a b => H.e5a F N r (r + K) LL _ _ _ (Fin.castAdd_injective r K) (initialSegments_nested i j) _ _
        (prPl_sys D H r K LL i) (prPl_sys D H r K LL j) a b
    | .inr i, .inr j => fun a b => H.e5a F N K (r + K) LL _ _ _ (Fin.natAdd_injective K r) (initialSegments_nested i j) _ _
        (prTan_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inl i, .inr j => fun a b => H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inr i, .inl j => fun a b => (H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL j) (prTan_sys D H r K LL i) b a).symm
  bot := fun s => match s with
    | .inl i => fun a h => H.e2 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) a h
    | .inr i => fun a h => H.e2 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) a h
  Pl := Pol F (r + K) B
  stab := fun s => match s with
    | .inl i => fun a x hx => H.e3 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) _ (prPl_sys D H r K LL i) B a x hx
    | .inr i => fun a x hx => H.e3 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) _ (prTan_sys D H r K LL i) B a x hx
  b := pvec F r K LL B
  P := fun x s => match s with
    | .inl i => x.1.1.1 i
    | .inr i => x.1.2.1 i
  Pdom := fun x s => match s with
    | .inl i => by
        obtain ⟨_, _, _, ⟨P1, h1⟩, _⟩ := x.2.1
        exact h1 ▸ P1.dom i
    | .inr i => by
        obtain ⟨_, _, _, _, ⟨P2, h2⟩⟩ := x.2.1
        exact h2 ▸ P2.dom i
  li := (H.p16 F N r K LL B).1
  span := (H.p16 F N r K LL B).2
  low := fun s => match s with
    | .inl i => fun pi h1 h2 => H.lowPl F N r K LL B i pi ⟨h1, h2⟩
    | .inr i => fun pi h1 h2 => H.lowTan F N r K LL B i pi ⟨h1, h2⟩

end

end Formalism.MainNotions.G.ColumnFamilies
end
end

