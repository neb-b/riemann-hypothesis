module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  Submodule.span M.L.O (Set.range (H.MMfam t))

def MMsharp (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V where
  carrier := {u | u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Type :=
  ↥(MMsharp H t) ⧸ (MMo H t).comap (MMsharp H t).subtype

def ddMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (u : ↥(MMsharp H t)) : DDt H t :=
  Submodule.Quotient.mk u

def IsomD (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  ∀ (x y : ↥(MMsharp H t₁)) (x₂ y₂ : ↥(MMsharp H t₂)), θ (ddMk H t₁ x) = ddMk H t₂ x₂ →
    θ (ddMk H t₁ y) = ddMk H t₂ y₂ → H.h x₂ y₂ - H.h x y ∈ M.L.O

def Gam (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)), p = (ddMk H t u, H.mkW t.f ⟨u, hu⟩)}

def Gam' (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f') :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f')), p = (ddMk H t u, H.mkW t.f' ⟨u, hu⟩)}

def GamR (H : HermSp M V) {r : ℕ} (t : Term V M r) (c : E) :
    Set (DDt H t × DDt H t × H.Wb t.f × H.Wb t.f') :=
  {p | ∃ (u u' u'' : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)) (hu' : (u' : V) ∈ H.perp (H.X t.f')),
    (u : V) - u' = c • (u'' : V) ∧
      p = (ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hu⟩, H.mkW t.f' ⟨u', hu'⟩)}

def MMInt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Prop :=
  ∀ m ∈ MMo H t, ∀ m' ∈ MMo H t, H.h m m' ∈ M.L.O

def Theta (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Set (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :=
  {θ | IsUnit (H.Dl t₂.f t₂.f' (r + 1)) ∧ MMInt H t₂ ∧ IsomD H t₁ t₂ θ ∧
    (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))}

def LocalCountHypotheses (H : HermSp M V) {r : ℕ} (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') : Prop :=
  H.IsGeneric t₁ ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂ t₁.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂' t₁.T' ∧
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ∧
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) ∧
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r))

end Cut

section Props

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def LatSide (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    Nat.card {Λ₂ : Submodule M.L.O V | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'} =
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ')

def ModSide0 (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = H.ZZplus t₁ →
      Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIso Z₁ Z₂

def ModSideU (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = H.ZZplus t₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = H.ZZplus t₁ a.castSucc (Fin.last r) ∧
        (be₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc (Fin.last r) ∧
        (al₁ a : E) = H.ZZplus t₁ (Fin.last r) a.castSucc ∧
        (al₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' (Fin.last r) a.castSucc) →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂

end Props

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdE

section Gen

variable {G : Type} [Group G] {ι : Type} {H : ι → Type} [∀ i, Group (H i)] (π : ∀ i, G →* H i)

def glob (A : ∀ i, Subgroup (H i)) : Subgroup G := ⨅ i, (A i).comap (π i)

theorem mem_glob {A : ∀ i, Subgroup (H i)} {g : G} : g ∈ glob π A ↔ ∀ i, π i g ∈ A i := by
  simp [glob, Subgroup.mem_iInf]

theorem relIndex_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfin : ∀ i, (C i).relIndex (A i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    (glob π C).relIndex (glob π A) = ∏ i ∈ S, (C i).relIndex (A i) := by
  classical
  set K := (glob π C).subgroupOf (glob π A) with hK
  let Φ : ↥(glob π A) → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) := fun g i =>
    QuotientGroup.mk ⟨π i g, (mem_glob π).1 g.2 i⟩
  have hrel : ∀ a b : ↥(glob π A), Φ a = Φ b ↔ a⁻¹ * b ∈ K := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, mem_glob]
    simp only [Φ, funext_iff]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have h1 := h ⟨i, hi⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · rw [← hS i hi]
        simpa using (A i).mul_mem ((A i).inv_mem ((mem_glob π).1 a.2 i)) ((mem_glob π).1 b.2 i)
    · intro h i
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h i
  have hsurj : Function.Surjective Φ := by
    intro q
    choose r hr using fun i : S => QuotientGroup.mk_surjective (q i)
    obtain ⟨g, hg1, hg2⟩ := happrox (fun i => if hi : i ∈ S then ((r ⟨i, hi⟩ : A i) : H i) else 1)
    have hgA : g ∈ glob π A := by
      rw [mem_glob]
      intro i
      by_cases hi : i ∈ S
      · have h1 := hg1 i hi
        simp only [dif_pos hi] at h1
        have h2 := (A i).mul_mem (r ⟨i, hi⟩).2 (Subgroup.mem_inf.1 h1).1
        simpa using h2
      · exact hg2 i hi
    refine ⟨⟨g, hgA⟩, ?_⟩
    funext i
    rw [← hr i]
    simp only [Φ]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hg1 i.1 i.2
    simp only [dif_pos i.2] at h1
    simpa using (C i).inv_mem (Subgroup.mem_inf.1 h1).2
  let Ψ : ↥(glob π A) ⧸ K → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) :=
    Quotient.lift Φ (fun a b hab => (hrel a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((hrel a b).1 hxy)
    · intro q
      obtain ⟨a, ha⟩ := hsurj q
      exact ⟨QuotientGroup.mk a, ha⟩
  have hcard := Nat.card_congr (Equiv.ofBijective Ψ hbij)
  rw [Nat.card_pi] at hcard
  rw [← Finset.prod_coe_sort S]
  exact hcard

theorem idxRatio_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfinA : ∀ i, (C i).relIndex (A i) ≠ 0) (hfinC : ∀ i, (A i).relIndex (C i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (glob π A) (glob π C) = ∏ i ∈ S, Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A i) (C i) := by
  have happrox' : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ C i ⊓ A i) ∧ ∀ i ∉ S, π i g ∈ C i := by
    intro h
    obtain ⟨g, hg1, hg2⟩ := happrox h
    refine ⟨g, fun i hi => ?_, fun i hi => ?_⟩
    · rw [inf_comm]
      exact hg1 i hi
    · rw [← hS i hi]
      exact hg2 i hi
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [relIndex_glob π A C S hS hfinA happrox,
    relIndex_glob π C A S (fun i hi => (hS i hi).symm) hfinC happrox']
  push_cast
  rw [Finset.prod_div_distrib]

end Gen

end Formalism.L2.SG.Pf.ProdE
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZhatOMMono
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

section Gen

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

theorem zLoc_mono (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (σ : Fin (r + 1) → Fin (r + 1))
    (ν : Fin (r + 1) → E) :
    zLoc ι cj Dd (mono σ ν) = mono σ (fun a => Dd (σ a) * cj (Dd a) * ι (ν a)) := by
  ext a b
  simp only [zLoc, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem zhatOM_mono (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    ZhatOM (mono σ ν) = mono σ (fun a => (-1) ^ (r - (σ a).val) * ν a) := by
  ext a b
  simp only [ZhatOM, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem linG_mono {F : Type*} [Field F] [Algebra F K] (e : K ≃ₐ[F] F × F) (q : F) {σ : Fin (r + 1) → Fin (r + 1)}
    (hσ : ∀ a, σ (σ a) = a) (ν : Fin (r + 1) → K) :
    linG e q (mono σ ν) = mono σ (fun a => e.symm ((e (ν a)).1 / q, -((e (ν (σ a))).2 / q))) := by
  ext a b
  simp only [linG, mono, Matrix.of_apply]
  by_cases h : b = σ a
  · subst h
    rw [if_pos rfl, if_pos (hσ a).symm, if_pos rfl]
  · have h' : ¬ a = σ b := fun h' => h (by rw [h', hσ])
    rw [if_neg h, if_neg h', if_neg h]
    simp

theorem fix_single {K : Type*} [CommRing K] {l ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) :
    l * Matrix.single (Fin.last r) (Fin.last r) κ * ρ = Matrix.single (Fin.last r) (Fin.last r) κ := by
  ext x y
  rw [mul_single_mul]
  have h1 : l x (Fin.last r) = if x = Fin.last r then 1 else 0 := by
    by_cases hx : x = Fin.last r
    · subst hx; rw [if_pos rfl]; exact (hl _ _).2 rfl
    · rw [if_neg hx]; exact (hl _ _).1 (lt_of_le_of_ne (Fin.le_last x) hx)
  have h2 : ρ (Fin.last r) y = if y = Fin.last r then 1 else 0 := by
    by_cases hy : y = Fin.last r
    · subst hy; rw [if_pos rfl]; exact (hρ _ _).2 rfl
    · rw [if_neg hy]; exact (hρ _ _).1 (lt_of_le_of_ne (Fin.le_last y) hy)
  rw [h1, h2, Matrix.single_apply]
  by_cases hx : x = Fin.last r <;> by_cases hy : y = Fin.last r
  · subst hx; subst hy; simp
  · simp [hy, Ne.symm hy]
  · simp [hx, Ne.symm hx]
  · simp [hx, Ne.symm hx]

theorem fix_of_fix {K : Type*} [CommRing K] {l ρ N : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) (h : l * (N - Matrix.single (Fin.last r) (Fin.last r) κ) * ρ =
      N - Matrix.single (Fin.last r) (Fin.last r) κ) : l * N * ρ = N := by
  rw [Matrix.mul_sub, Matrix.sub_mul, fix_single hl hρ] at h
  exact sub_left_injective h

end Gen

section Rec

open Formalism.L2.SG.CntLocal

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (u u' : D.what₂.Word)

theorem zzp_mono {p : PlF D} (hA : Agree δ M p) {σ : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)} (hσ : ∀ a, σ (σ a) = a)
    (ν : Fin (D.R.rS + 1) → D.host.E) (hν : ∀ a, ν a ≠ 0) :
    ∃ ν' : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν' a)) ∧ ∃ κ : (D.s.atP p).Ep,
      ZZP (M := M) δ u u' p (mono σ ν) = mono σ ν' - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep)
  have hu : ∀ a, IsUnit (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a)) := fun a =>
    ((frFac_unit δ M hA (σ a)).mul ((frFac_unit δ M hA a).map cj)).mul ((isUnit_iff_ne_zero.2 (hν a)).map _)
  cases h : (M p).split with
  | none =>
    refine ⟨fun a => frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a), hu, 0, ?_⟩
    rw [zzp_none δ M u u' h, zLoc_mono, Matrix.single_zero, sub_zero]
  | some g =>
    refine ⟨fun a => g.e.symm ((g.e (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a))).1 / (g.q : (D.s.atP p).Fp),
      -((g.e (frFac δ p (σ (σ a)) * cj (frFac δ p (σ a)) * (D.s.atP p).ιE (ν (σ a)))).2 / (g.q : (D.s.atP p).Fp))),
      fun a => ?_, g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
          (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)), ?_⟩
    · have hq := q_ne M g
      have h1 := (Prod.isUnit_iff.1 ((hu a).map g.e)).1
      have h2 := (Prod.isUnit_iff.1 ((hu (σ a)).map g.e)).2
      refine IsUnit.map g.e.symm (Prod.isUnit_iff.2 ⟨?_, ?_⟩)
      · exact isUnit_iff_ne_zero.2 (div_ne_zero h1.ne_zero hq)
      · exact isUnit_iff_ne_zero.2 (neg_ne_zero.2 (div_ne_zero h2.ne_zero hq))
    · rw [zzp_some δ M u u' h, zLoc_mono, linG_mono _ _ hσ]

end Rec

end Formalism.L2.SG.Pf.ProdEApprox
end
end

