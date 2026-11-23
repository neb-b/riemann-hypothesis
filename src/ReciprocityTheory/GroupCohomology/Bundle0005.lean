module

public import ReciprocityTheory.GroupCohomology.Bundle0002
public import ReciprocityTheory.GroupCohomology.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.IsSuccSubset
section
namespace ReciprocityTheory.Coh

noncomputable section

universe u

open Cx

namespace InflationTower

variable {R : Type u} [CommRing R]

lemma H_mk {A B : Cx R} (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

lemma lift_cocycle {A B : Cx R} (φ : Hom A B) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ)
    (z : A.Z n) (w : B.Z n) (h : φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk w) :
    ∃ z' : A.Z n, (Submodule.Quotient.mk z' : A.H n) = Submodule.Quotient.mk z ∧ φ.Z n z' = w := by
  rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap] at h
  cases n with
  | zero =>
    refine ⟨z, rfl, ?_⟩
    have h' : ((φ.Z 0 z - w : B.Z 0) : B.X 0) = 0 := h
    exact sub_eq_zero.mp (Subtype.ext h')
  | succ k =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨c', rfl⟩ := hs k c
    have hdc : A.d (k+1) (A.d k c') = 0 := A.dd k c'
    refine ⟨z - ⟨A.d k c', hdc⟩, ?_, ?_⟩
    · rw [Submodule.Quotient.eq, Submodule.mem_comap]
      refine ⟨-c', ?_⟩
      show A.d k (-c') = (z : A.X (k+1)) - A.d k c' - z
      rw [map_neg]; abel
    · apply Subtype.ext
      have hc' : B.d k (φ.f k c') = φ.f (k+1) z - w := hc
      show φ.f (k+1) ((z : A.X (k+1)) - A.d k c') = w
      rw [map_sub, φ.comm, hc']; abel

theorem surj_part (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (n : ℕ) (y : ∀ m, (A m).H n) (hy : ∀ m, (τ m).H n (y (m + 1)) = y m) :
    ∃ x, ∀ m, (π m).H n x = y m := by
  have step : ∀ m (z : (A m).Z n), (Submodule.Quotient.mk z : (A m).H n) = y m →
      ∃ z' : (A (m+1)).Z n, (Submodule.Quotient.mk z' : (A (m+1)).H n) = y (m+1) ∧ (τ m).Z n z' = z := by
    intro m z hz
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (y (m+1))
    obtain ⟨z', h1, h2⟩ := lift_cocycle (τ m) (hT.surj m) n w z (by rw [hw, hy, hz])
    exact ⟨z', h1.trans hw, h2⟩
  let seq : ∀ m, {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m} := fun m =>
    Nat.rec (motive := fun m => {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m})
      ⟨Classical.choose (Submodule.Quotient.mk_surjective _ (y 0)),
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (y 0))⟩
      (fun m s => ⟨Classical.choose (step m s.1 s.2), (Classical.choose_spec (step m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).Z n (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (step m (seq m).1 (seq m).2)).2
  obtain ⟨x, hx⟩ := hT.lift n (fun m => ((seq m).1 : (A m).X n)) (fun m => congrArg Subtype.val (hseq m))
  have hdx : L.d n x = 0 := by
    apply hT.ext
    intro m
    rw [(π m).comm, hx]; exact (seq m).1.2
  refine ⟨Submodule.Quotient.mk ⟨x, hdx⟩, fun m => ?_⟩
  rw [H_mk, ← (seq m).2]
  congr 1; exact Subtype.ext (hx m)

def Hs (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) : ℕ → ∀ m, Submodule R ((A m).H k)
  | 0 => fun _ => ⊤
  | j + 1 => fun m => (Hs A τ k j (m + 1)).map ((τ m).H k)

def Is (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1)) :
    ℕ → ∀ m, Set ((A m).X k)
  | 0 => fun m => {b | (A m).d k b = c m}
  | j + 1 => fun m => (τ m).f k '' Is A τ k c j (m + 1)

section Inj

variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

lemma Is_torsor (hs : ∀ m n, Function.Surjective ((τ m).f n)) :
    ∀ j m p, p ∈ Is A τ k c j m → ∀ q, q ∈ Is A τ k c j m ↔
      ∃ hx : (A m).d k (q - p) = 0, (Submodule.Quotient.mk ⟨q - p, hx⟩ : (A m).H k) ∈ Hs A τ k j m := by
  intro j
  induction j with
  | zero =>
    intro m p hp q
    have hp' : (A m).d k p = c m := hp
    show (A m).d k q = c m ↔ _
    simp only [Hs, Submodule.mem_top, exists_prop, and_true, map_sub, hp', sub_eq_zero]
  | succ j ih =>
    intro m p hp q
    obtain ⟨p', hp', rfl⟩ := hp
    constructor
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨hx, hmem⟩ := (ih (m+1) p' hp' q').1 hq'
      have hx' : (A m).d k ((τ m).f k q' - (τ m).f k p') = 0 := by
        rw [← map_sub, ← (τ m).comm, hx, map_zero]
      refine ⟨hx', ?_⟩
      have he : (Submodule.Quotient.mk ⟨(τ m).f k q' - (τ m).f k p', hx'⟩ : (A m).H k) =
          (τ m).H k (Submodule.Quotient.mk ⟨q' - p', hx⟩) := by
        rw [H_mk]; congr 1; exact Subtype.ext (map_sub _ _ _).symm
      rw [he]
      exact Submodule.mem_map_of_mem hmem
    · rintro ⟨hx, hmem⟩
      obtain ⟨h, hh, he⟩ := hmem
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      obtain ⟨y', h1, h2⟩ := lift_cocycle (τ m) (hs m) k y ⟨_, hx⟩ he
      have h2' : (τ m).f k y' = q - (τ m).f k p' := congrArg Subtype.val h2
      refine ⟨p' + y', ?_, ?_⟩
      · rw [ih (m+1) p' hp']
        have hy0 : (A (m+1)).d k (p' + y' - p') = 0 := by rw [add_sub_cancel_left]; exact y'.2
        refine ⟨hy0, ?_⟩
        have : (⟨p' + y' - p', hy0⟩ : (A (m+1)).Z k) = y' := Subtype.ext (add_sub_cancel_left _ _)
        rw [this, h1]; exact hh
      · rw [map_add (f := _), h2']; abel

lemma Is_nonempty (hP : ∀ m, ∃ b, (A m).d k b = c m) : ∀ j m, (Is A τ k c j m).Nonempty := by
  intro j
  induction j with
  | zero => exact hP
  | succ j ih => intro m; exact (ih (m+1)).image _

lemma Is_succ_subset (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) :
    ∀ j m, Is A τ k c (j+1) m ⊆ Is A τ k c j m := by
  intro j
  induction j with
  | zero =>
    rintro m _ ⟨b, hb, rfl⟩
    have hb' : (A (m+1)).d k b = c (m+1) := hb
    show (A m).d k ((τ m).f k b) = c m
    rw [← (τ m).comm, hb', hc]
  | succ j ih => intro m; exact Set.image_mono (ih (m+1))

lemma Hs_succ_le : ∀ j m, Hs A τ k (j+1) m ≤ Hs A τ k j m := by
  intro j
  induction j with
  | zero => intro m; exact le_top
  | succ j ih => intro m; exact Submodule.map_mono (ih (m+1))

end Inj

section Inj2

variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

lemma Is_anti (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) (m : ℕ) :
    Antitone fun j => Is A τ k c j m :=
  antitone_nat_of_succ_le fun j => Is_succ_subset A τ k c hc j m

lemma Hs_anti (m : ℕ) : Antitone fun j => Hs A τ k j m :=
  antitone_nat_of_succ_le fun j => Hs_succ_le A τ k j m

lemma Hs_stab (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Hs A τ k j m = Hs A τ k J m := by
  obtain ⟨J, hJ⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (Hs A τ k j m), fun _ _ h => Hs_anti A τ k m h⟩ :
      ℕ →o (Submodule R ((A m).H k))ᵒᵈ)
  exact ⟨J, fun j hj => (congrArg OrderDual.ofDual (hJ j hj)).symm⟩

lemma Is_stab (hs : ∀ m n, Function.Surjective ((τ m).f n)) (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m)
    (hP : ∀ m, ∃ b, (A m).d k b = c m) (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m := by
  obtain ⟨J, hJ⟩ := Hs_stab A τ k hA m
  refine ⟨J, fun j hj => ?_⟩
  apply le_antisymm (Is_anti A τ k c hc m hj)
  obtain ⟨p, hp⟩ := Is_nonempty A τ k c hP j m
  have hpJ := Is_anti A τ k c hc m hj hp
  intro q hq
  rw [Is_torsor A τ k c hs j m p hp, hJ j hj]
  exact (Is_torsor A τ k c hs J m p hpJ q).1 hq

theorem inj_part (L : Cx R) (π : ∀ m, Hom L (A m)) (hT : IsTowerLim A τ L π)
    (hA : ∀ m, IsArtinian R ((A m).H k)) (x : L.H (k + 1)) (hx : ∀ m, (π m).H (k + 1) x = 0) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ∀ m, ∃ b, (A m).d k b = (π m).f (k+1) z := by
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb⟩
  let c : ∀ m, (A m).X (k + 1) := fun m => (π m).f (k+1) z
  have hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m := fun m => hT.compat m (k+1) z
  have hstab : ∀ m, ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m :=
    Is_stab A τ k c hT.surj hc hP hA
  let J : ℕ → ℕ := fun m => Classical.choose (hstab m)
  have hJ : ∀ m j, J m ≤ j → Is A τ k c j m = Is A τ k c (J m) m := fun m => Classical.choose_spec (hstab m)
  let S : ∀ m, Set ((A m).X k) := fun m => Is A τ k c (J m) m
  have hS : ∀ m j, S m ⊆ Is A τ k c j m := by
    intro m j
    rcases le_total j (J m) with h | h
    · exact Is_anti A τ k c hc m h
    · rw [hJ m j h]
  have hSsurj : ∀ m, ∀ s ∈ S m, ∃ t ∈ S (m+1), (τ m).f k t = s := fun m s hs =>
    hS m (J (m+1) + 1) hs
  have hS0 : (S 0).Nonempty := Is_nonempty A τ k c hP _ _
  let seq : ∀ m, {b : (A m).X k // b ∈ S m} := fun m =>
    Nat.rec (motive := fun m => {b : (A m).X k // b ∈ S m}) ⟨hS0.some, hS0.some_mem⟩
      (fun m s => ⟨Classical.choose (hSsurj m s.1 s.2), (Classical.choose_spec (hSsurj m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).f k (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (hSsurj m (seq m).1 (seq m).2)).2
  obtain ⟨b, hb⟩ := hT.lift k (fun m => (seq m).1) hseq
  have hdb : L.d k b = z := by
    rw [← sub_eq_zero]
    apply hT.ext
    intro m
    have h0 : (A m).d k (seq m).1 = c m := hS m 0 (seq m).2
    rw [map_sub, (π m).comm, hb, h0, sub_self]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact ⟨b, hdb⟩

end Inj2

theorem inj_zero (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (x : L.H 0) (hx : ∀ m, (π m).H 0 x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : L.X 0) = 0 := by
    apply hT.ext
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    exact h
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hz]
  exact Submodule.zero_mem _

end InflationTower

end

universe u

open InflationTower in
theorem tower_holds : TowerStatement.{u} := by
  intro R _ A τ L π hT n
  refine ⟨surj_part A τ L π hT n, fun hA x hx => ?_⟩
  cases n with
  | zero => exact inj_zero A τ L π hT x hx
  | succ k => exact inj_part A τ k L π hT (hA k rfl) x hx

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.LocaliseA
section
namespace ReciprocityTheory.Coh

open Cx Function

universe u

section Alg

variable {R : Type u} [CommRing R] {A B : Cx R}

theorem cx_smul_d {n : ℕ} (t : R) (x : B.X n) : B.d n (t • x) = t • B.d n x := map_smul _ _ _

theorem bij_H_of_bij (t : R) (ht : ∀ n, Bijective fun x : B.X n => t • x) (n : ℕ) :
    Bijective (algebraMap R (Module.End R (B.H n)) t) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Module.algebraMap_end_apply, cls_smul, cls_eq_zero_iff] at hc
      rw [cls_eq_zero_iff]
      cases n with
      | zero =>
        have h0 : t • x = 0 := hc
        exact (ht 0).1 (h0.trans (smul_zero t).symm)
      | succ n =>
        obtain ⟨y, hy⟩ := hc
        obtain ⟨y', rfl⟩ := (ht n).2 y
        refine ⟨y', (ht (n + 1)).1 ?_⟩
        show t • B.d n y' = t • x
        rw [← cx_smul_d, hy]
  · intro c
    induction c using H_ind with
    | h x hx =>
      obtain ⟨x', rfl⟩ := (ht n).2 x
      have hx' : B.d n x' = 0 := (ht (n + 1)).1 (by
        show t • B.d n x' = t • 0
        rw [← cx_smul_d, smul_zero]; exact hx)
      exact ⟨B.cls n x' hx', by rw [Module.algebraMap_end_apply, cls_smul]⟩

theorem isLocalized_of_cx (j : Hom A B) (t : R) (hj : ∀ n, Injective (j.f n))
    (ht : ∀ n, Bijective fun x : B.X n => t • x)
    (hc : ∀ n (x : B.X n), ∃ (m : ℕ) (y : A.X n), j.f n y = t ^ m • x) (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t) (j.H n) := by
  constructor
  case map_units =>
    rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap R (Module.End R (B.H n)) (t ^ k))
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht n)).pow k
  case surj =>
    intro y
    induction y using H_ind with
    | h x hx =>
      obtain ⟨m, a, ha⟩ := hc n x
      have ha0 : A.d n a = 0 := (hj (n + 1)) (by
        rw [j.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
      refine ⟨(A.cls n a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
      show (t ^ m) • B.cls n x hx = j.H n (A.cls n a ha0)
      rw [cls_smul, Hom.H_cls]
      exact cls_congr _ _ ha.symm
  case exists_of_eq =>
    have key : ∀ z : A.H n, j.H n z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
      intro z hz
      induction z using H_ind with
      | h g hg =>
        rw [Hom.H_cls, cls_eq_zero_iff] at hz
        cases n with
        | zero =>
          have h0 : j.f 0 g = 0 := hz
          refine ⟨1, ?_⟩
          rw [one_smul, cls_eq_zero_iff]
          exact (hj 0) (h0.trans (map_zero _).symm)
        | succ n =>
          obtain ⟨h, hh⟩ := hz
          obtain ⟨m, k, hk⟩ := hc n h
          refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
          show (t ^ m) • A.cls (n + 1) g hg = 0
          rw [cls_smul, cls_eq_zero_iff]
          refine ⟨k, (hj (n + 1)) ?_⟩
          rw [j.comm, hk, cx_smul_d, hh, map_smul]
    intro x₁ x₂ h
    obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
    exact ⟨c, by rw [smul_sub, sub_eq_zero] at hc'; exact hc'⟩

end Alg

section Trunc

variable {R : Type u} [CommRing R] (A : Cx R) (L : Submodule R (A.H 1))

end Trunc

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

universe u

section AdmAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem pair_hom_f_coe_of_id {M M' : TRep R G} (P : Pair M M') (h : P.φ = MonoidHom.id G) (n : ℕ)
    (x : M.coch.X n) : (P.hom.f n x).1 = fun g => P.u (x.1 g) := by
  funext g
  show P.u (x.1 fun i => P.φ (g i)) = P.u (x.1 g)
  rw [h]
  rfl

end AdmAux

theorem admissibility_holds : AdmStatement.{u} := by
  intro R _ G _ _ _ A B C i p h
  refine ⟨fun n x y hxy => ?_, fun n => ?_, fun n => ?_⟩
  · refine Subtype.ext (funext fun g => h.emb.injective ?_)
    have hg := congrArg (fun z => z.1 g) hxy
    simp only [pair_hom_f_coe_of_id i h.i_id] at hg
    exact hg
  · intro y
    constructor
    · intro hy
      have hy' : ∀ g, p.u (y.1 g) = 0 := fun g => by
        have hg := congrArg (fun z => z.1 g) hy
        simp only [pair_hom_f_coe_of_id p h.p_id] at hg
        exact hg
      have hex : ∀ g, ∃ a, i.u a = y.1 g := fun g => (h.exact (y.1 g)).1 (hy' g)
      choose x hx using hex
      have hxc : Continuous x := by
        rw [h.emb.continuous_iff]
        have hfx : (i.u ∘ x) = y.1 := funext hx
        rw [hfx]
        exact y.2
      exact ⟨⟨x, hxc⟩, Subtype.ext ((pair_hom_f_coe_of_id i h.i_id n _).trans (funext hx))⟩
    · rintro ⟨x, rfl⟩
      refine Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans ?_)
      funext g
      rw [pair_hom_f_coe_of_id i h.i_id]
      exact (h.exact (i.u (x.1 g))).2 ⟨x.1 g, rfl⟩
  · intro c
    obtain ⟨s, hs, hps⟩ := h.sec
    exact ⟨⟨s ∘ c.1, hs.comp c.2⟩,
      Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans (funext fun g => hps _))⟩

theorem limRep_holds : LimRepStatement.{u} := by
  intro R _ G _ _ _ A _ τ L π hτ hemb hlift
  have cτ : ∀ m n (x : (A (m + 1)).coch.X n), ((τ m).hom.f n x).1 = fun g => (τ m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (τ m) (hτ m).1 n x
  have cπ : ∀ m n (x : L.coch.X n), ((π m).hom.f n x).1 = fun g => (π m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (π m) (hτ m).2.1 n x
  refine ⟨fun m n c => ?_, fun m n x => ?_, fun n x hx => ?_, fun n y hy => ?_⟩
  · choose s hs using (hτ m).2.2.1
    exact ⟨⟨s ∘ c.1, (continuous_of_discreteTopology (f := s)).comp c.2⟩,
      Subtype.ext ((cτ m n _).trans (funext fun g => hs _))⟩
  · refine Subtype.ext ?_
    rw [cτ, cπ, cπ]
    funext g
    exact (hτ m).2.2.2 _
  · refine Subtype.ext (funext fun g => ?_)
    apply hemb.injective
    funext m
    have hg := congrArg (fun z => z.1 g) (hx m)
    simp only [cπ] at hg
    refine hg.trans ?_
    show (0 : (A m).V) = (π m).u 0
    rw [map_zero]
  · have hy' : ∀ g m, (τ m).u ((y (m + 1)).1 g) = (y m).1 g := fun g m => by
      have hg := congrArg (fun z => z.1 g) (hy m)
      simp only [cτ] at hg
      exact hg
    choose x hx using fun g => hlift (fun m => (y m).1 g) (hy' g)
    have hxc : Continuous x := by
      rw [hemb.continuous_iff]
      have hfx : ((fun (x : L.V) m => (π m).u x) ∘ x) = fun g m => (y m).1 g :=
        funext fun g => funext (hx g)
      rw [hfx]
      exact continuous_pi fun m => by exact (y m).2
    exact ⟨⟨x, hxc⟩, fun m => Subtype.ext ((cπ m n _).trans (funext fun g => hx g m))⟩

section ColimAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end ColimAux

end ReciprocityTheory.Coh
end

