module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.FaceStdSeqGLConjugateCommutingStab
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

noncomputable section

open scoped Matrix

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

def pm (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) R := Matrix.of fun a b => if f b = a then 1 else 0

theorem pm_mul (f h : Fin n → Fin n) : pm R f * pm R h = pm R (f ∘ h) := by
  ext a c
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

theorem pm_id : pm R (id : Fin n → Fin n) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [pm]
  · simp [pm, Matrix.one_apply, h, Ne.symm h]

def pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) : GL (Fin n) R :=
  ⟨pm R f, pm R g, by rw [pm_mul, show f ∘ g = id from funext h1, pm_id],
    by rw [pm_mul, show g ∘ f = id from funext h2, pm_id]⟩

theorem pm_mulVec (f : Fin n → Fin n) (k : Fin n) :
    pm R f *ᵥ (fun a : Fin n => if a = k then (1 : R) else 0) = fun a => if a = f k then 1 else 0 := by
  funext a
  simp only [pm, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : a = f k
  · simp [h]
  · simp [h, Ne.symm h]

theorem vecMul_pm (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (k : Fin n) :
    (fun a : Fin n => if a = k then (1 : R) else 0) ᵥ* pm R g = fun c => if c = f k then 1 else 0 := by
  funext c
  have key : g c = k ↔ c = f k := ⟨fun e => by rw [← e, h1], fun e => by rw [e, h2]⟩
  simp only [pm, Matrix.vecMul, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [key]

theorem pm_mul_apply (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k)
    (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) : (pm R f * M) a c = M (g a) c := by
  have key : ∀ b, f b = a ↔ b = g a := fun b => ⟨fun e => by rw [← e, h2], fun e => by rw [e, h1]⟩
  simp only [pm, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_pm_apply (f : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) :
    (M * pm R f) a c = M a (f c) := by
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

variable (m i : ℕ) (hmi : m + i < n)

def cyc (k : Fin n) : Fin n :=
  if h : m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then ⟨k + 1, by omega⟩
  else if (k : ℕ) = m + i then ⟨m, by omega⟩ else k

def cycInv (k : Fin n) : Fin n :=
  if h : m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then ⟨k - 1, by omega⟩
  else if (k : ℕ) = m then ⟨m + i, hmi⟩ else k

theorem cyc_val (k : Fin n) : (cyc m i hmi k : ℕ) =
    if m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then (k : ℕ) + 1 else if (k : ℕ) = m + i then m else k := by
  unfold cyc; split_ifs <;> rfl

theorem cycInv_val (k : Fin n) : (cycInv m i hmi k : ℕ) =
    if m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then (k : ℕ) - 1 else if (k : ℕ) = m then m + i else k := by
  unfold cycInv; split_ifs <;> rfl

theorem cyc_cycInv (k : Fin n) : cyc m i hmi (cycInv m i hmi k) = k := by
  apply Fin.ext
  rw [cyc_val, cycInv_val]
  split_ifs <;> omega

theorem cycInv_cyc (k : Fin n) : cycInv m i hmi (cyc m i hmi k) = k := by
  apply Fin.ext
  rw [cycInv_val, cyc_val]
  split_ifs <;> omega

end GlobalTheory.HomStab.FacePerm

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

theorem pairAct_pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (K : ℕ)
    (hK : K < n) (L : ℕ) (hL : (f ⟨K, hK⟩ : ℕ) = L) :
    pairAct R n (pmU R f g h1 h2) ((fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0)) =
    ((fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0)) := by
  subst hL
  have e1 : (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0) = fun a => if a = ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  have e2 : (fun a : Fin n => if (a : ℕ) = (f ⟨K, hK⟩ : ℕ) then (1 : R) else 0) = fun a => if a = f ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  rw [e1, e2]
  exact Prod.ext (pm_mulVec R f ⟨K, hK⟩) (vecMul_pm R f g h1 h2 ⟨K, hK⟩)

end GlobalTheory.HomStab.FacePerm


open GlobalTheory.HomStab.FacePerm in
theorem GlobalTheory.HomStab.exists_perm_face_stdSeq : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := open GlobalTheory.HomStab.FacePerm in by
  intro R _ n p h i
  have hi := i.isLt
  have hmi : n - (p + 1) + (i : ℕ) < n := by omega
  refine ⟨pmU R (cyc (n - (p + 1)) i hmi) (cycInv (n - (p + 1)) i hmi) (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), ?_, ?_⟩
  · apply Subtype.ext
    show ((stdList R n (p + 1)).eraseIdx i).map (pairAct R n _) = stdList R n p
    apply List.ext_getElem
    · simp only [List.length_map, List.length_eraseIdx, stdList, List.length_ofFn]
      split_ifs <;> omega
    · intro j h1 h2
      have hjp : j < p := by simpa [stdList] using h2
      simp only [List.getElem_map, List.getElem_eraseIdx, stdList, List.getElem_ofFn, Fin.val_mk]
      split_ifs with hj
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
  · intro x
    have lo1 : ∀ k : Fin n, ((cyc (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cyc_val]
      split_ifs <;> omega
    have lo2 : ∀ k : Fin n, ((cycInv (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cycInv_val]
      split_ifs <;> omega
    have fx1 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cyc (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cyc_val]
      split_ifs <;> omega
    have fx2 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cycInv (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cycInv_val]
      split_ifs <;> omega
    have bij : ∀ a c : Fin n, cycInv (n - (p + 1)) i hmi a = c ↔ a = cyc (n - (p + 1)) i hmi c := by
      intro a c
      constructor
      · rintro rfl
        rw [cyc_cycInv]
      · rintro rfl
        rw [cycInv_cyc]
    ext a c
    rw [Units.val_mul, Units.val_mul]
    show ((pm R (cyc (n - (p + 1)) i hmi) * padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) : Matrix (Fin n) (Fin n) R)) a c = ((padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) * pm R (cyc (n - (p + 1)) i hmi) : Matrix (Fin n) (Fin n) R)) a c
    rw [pm_mul_apply R _ _ (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), mul_pm_apply]
    by_cases ha : (a : ℕ) < n - (p + 1)
    · by_cases hc : (c : ℕ) < n - (p + 1)
      · rw [fx2 a ha, fx1 c hc]
      · simp only [padMat, Matrix.of_apply]
        rw [dite_eq_right, dite_eq_right]
        all_goals first
          | simp only [bij]
          | (rw [lo1]; omega)
          | (rw [lo2]; omega)
    · simp only [padMat, Matrix.of_apply]
      rw [dite_eq_right, dite_eq_right]
      all_goals first
        | simp only [bij]
        | (rw [lo1]; omega)
        | (rw [lo2]; omega)

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := by
  first
  | exact @GlobalTheory.HomStab.exists_perm_face_stdSeq
  | exact @GlobalTheory.HomStab.FacePerm.pairAct_pmU
  | exact @GlobalTheory.HomStab.FacePerm.cycInv_cyc
  | exact @GlobalTheory.HomStab.FacePerm.cyc_cycInv
  | exact @GlobalTheory.HomStab.FacePerm.cycInv_val
  | exact @GlobalTheory.HomStab.FacePerm.cyc_val
  | exact @GlobalTheory.HomStab.FacePerm.mul_pm_apply
  | exact @GlobalTheory.HomStab.FacePerm.pm_mul_apply
  | exact @GlobalTheory.HomStab.FacePerm.vecMul_pm
  | exact @GlobalTheory.HomStab.FacePerm.pm_mulVec
  | exact @GlobalTheory.HomStab.FacePerm.pm_id
  | exact @GlobalTheory.HomStab.FacePerm.pm_mul
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyDimensionShiftIsIso
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
namespace GlobalTheory.HomStab

theorem isIso_map_succ_of_shortExact : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)), X.ShortExact → Y.ShortExact → ∀ (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, IsZero (groupHomology X.X₂ (n + 1)) → IsZero (groupHomology Y.X₂ (n + 1)) → IsIso (groupHomology.map φ u₁ n) → IsIso (groupHomology.map φ u₂ n) → IsIso (groupHomology.map φ u₃ (n + 1)) := by
  intro k G H _ _ _ φ X Y hX hY u₁ u₂ u₃ h12 h23 n hX2 hY2 hb hc
  have c12 : groupHomology.chainsMap φ u₁ ≫ (groupHomology.chainsFunctor k G).map Y.f =
      (groupHomology.chainsFunctor k H).map X.f ≫ groupHomology.chainsMap φ u₂ := by
    show groupHomology.chainsMap φ u₁ ≫ groupHomology.chainsMap (MonoidHom.id G) Y.f =
      groupHomology.chainsMap (MonoidHom.id H) X.f ≫ groupHomology.chainsMap φ u₂
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact groupHomology.chainsMap_congr (by ext; rfl) (by ext a; simpa using (h12 a).symm)
  have c23 : groupHomology.chainsMap φ u₂ ≫ (groupHomology.chainsFunctor k G).map Y.g =
      (groupHomology.chainsFunctor k H).map X.g ≫ groupHomology.chainsMap φ u₃ := by
    show groupHomology.chainsMap φ u₂ ≫ groupHomology.chainsMap (MonoidHom.id G) Y.g =
      groupHomology.chainsMap (MonoidHom.id H) X.g ≫ groupHomology.chainsMap φ u₃
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact groupHomology.chainsMap_congr (by ext; rfl) (by ext a; simpa using (h23 a).symm)
  let Φ : X.map (groupHomology.chainsFunctor k H) ⟶ Y.map (groupHomology.chainsFunctor k G) :=
    { τ₁ := groupHomology.chainsMap φ u₁
      τ₂ := groupHomology.chainsMap φ u₂
      τ₃ := groupHomology.chainsMap φ u₃
      comm₁₂ := c12
      comm₂₃ := c23 }
  have sX := groupHomology.map_chainsFunctor_shortExact hX
  have sY := groupHomology.map_chainsFunctor_shortExact hY
  have hnat := HomologicalComplex.HomologySequence.δ_naturality Φ sX sY (n + 1) n rfl
  have hf : groupHomology.map φ u₁ n ≫
      HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n =
      HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n ≫
        groupHomology.map φ u₂ n := by
    have h := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map c12
    exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map_comp
      (groupHomology.chainsMap φ u₁) ((groupHomology.chainsFunctor k G).map Y.f)).symm.trans
      (h.trans ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map_comp
        ((groupHomology.chainsFunctor k H).map X.f) (groupHomology.chainsMap φ u₂)))
  have hz := sY.δ_comp (n + 1) n rfl
  have monoX := groupHomology.mono_δ_of_isZero hX n hX2
  have monoY := groupHomology.mono_δ_of_isZero hY n hY2
  have exX := (ShortComplex.moduleCat_exact_iff _).mp (sX.homology_exact₁ (n + 1) n rfl)
  rw [ModuleCat.mono_iff_injective] at monoX monoY
  rw [ConcreteCategory.isIso_iff_bijective] at hb hc ⊢
  have e1 : ∀ x, ConcreteCategory.hom (groupHomology.map φ u₁ n)
      (ConcreteCategory.hom (groupHomology.δ hX (n + 1) n rfl) x) =
      ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl)
        (ConcreteCategory.hom (groupHomology.map φ u₃ (n + 1)) x) := by
    intro x
    have h := ConcreteCategory.congr_hom hnat x
    exact h
  have e2 : ∀ x, ConcreteCategory.hom
      (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n)
      (ConcreteCategory.hom (groupHomology.map φ u₁ n) x) =
      ConcreteCategory.hom (groupHomology.map φ u₂ n)
        (ConcreteCategory.hom
          (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n) x) := by
    intro x
    have h := ConcreteCategory.congr_hom hf x
    exact h
  have e3 : ∀ y, ConcreteCategory.hom
      (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n)
      (ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl) y) = 0 := by
    intro y
    have h := ConcreteCategory.congr_hom hz y
    exact h.trans rfl
  constructor
  · intro a b hab
    apply monoX
    apply hb.1
    rw [e1, e1, hab]
  · intro y
    obtain ⟨x1, hx1⟩ := hb.2 (ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl) y)
    have h0 : ConcreteCategory.hom
        (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n) x1 = 0 := by
      apply hc.1
      rw [← e2, hx1, e3]
      exact (map_zero _).symm
    obtain ⟨x3, hx3⟩ := exX x1 h0
    refine ⟨x3, monoY ?_⟩
    exact (e1 x3).symm.trans ((congrArg _ hx3).trans hx1)

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.groupHomology_dimension_shift_isIso : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)), X.ShortExact → Y.ShortExact → ∀ (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, IsZero (groupHomology X.X₂ (n + 1)) → IsZero (groupHomology Y.X₂ (n + 1)) → IsIso (groupHomology.map φ u₁ n) → IsIso (groupHomology.map φ u₂ n) → IsIso (groupHomology.map φ u₃ (n + 1)) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_succ_of_shortExact
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairNilHbdVbdEqZeroOfCycle
section
namespace GlobalTheory.SeqCx

theorem cycle_pair_empty (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ)
    (hc : c ∈ chains {l | (l, ([] : List W)) ∈ D} p) (hb : bd V c = 0) :
    Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧
      hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧
      vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  have hlin : ∀ d : List V →₀ ℤ, Finsupp.mapDomain (fun l => (l, ([] : List W))) d
      = Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))) d := fun d => rfl
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [chains2, Finsupp.mem_supported]
    rw [chains, Finsupp.mem_supported] at hc
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    rw [Finset.mem_image] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    have := hc (Finset.mem_coe.mpr hl)
    exact ⟨this.1, this.2, rfl⟩
  · have key : (hbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))))
        = (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [hbd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simp only [LinearMap.comp_apply] at this
    rw [hlin, this, hb, map_zero]
  · have key : (vbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = 0 := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [vbd, bd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simpa [LinearMap.comp_apply] using this

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ), c ∈ chains {l | (l, ([] : List W)) ∈ D} p → bd V c = 0 → Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧ hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧ vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.cycle_pair_empty
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqBoundariesLowerBidegreeOfSubClosed
section
noncomputable section

namespace GlobalTheory.SeqCx

open Finsupp

theorem map_supported_mem {α β : Type} {S : Set α}
    (f : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ)) (P : Submodule ℤ (β →₀ ℤ)) (h : ∀ z ∈ S, f (Finsupp.single z 1) ∈ P) :
    ∀ x ∈ Finsupp.supported ℤ ℤ S, f x ∈ P := by
  intro x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finsupp.sum_single x, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  rw [← Finsupp.smul_single_one, map_zsmul]
  exact P.smul_mem _ (h a (hx ha))

theorem hbd_single (V W : Type) (z : List V × List W) :
    hbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.1.length, (-1 : ℤ) ^ i • Finsupp.single (z.1.eraseIdx i, z.2) (1 : ℤ) := by
  simp only [hbd, bd, Finsupp.linearCombination_single, one_smul, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem vbd_single (V W : Type) (z : List V × List W) :
    vbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.2.length, (-1 : ℤ) ^ i • Finsupp.single (z.1, z.2.eraseIdx i) (1 : ℤ) := by
  simp only [vbd, bd, Finsupp.linearCombination_single, one_smul, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem bd_chains2 : ∀ (V W : Type) (D : Set (List V × List W)), SubClosed2 D →
    (∀ a b, ∀ x ∈ chains2 D (a + 1) b, hbd V W x ∈ chains2 D a b) ∧
    (∀ a b, ∀ x ∈ chains2 D a (b + 1), vbd V W x ∈ chains2 D a b) ∧
    (∀ b, ∀ x ∈ chains2 D 0 b, hbd V W x = 0) := by
  intro V W D hD
  refine ⟨fun a b => ?_, fun a b => ?_, fun b => ?_⟩
  · refine map_supported_mem (hbd V W) _ ?_
    rintro z ⟨hz, h1, h2⟩
    rw [hbd_single]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    refine Finsupp.single_mem_supported ℤ _ ?_
    have hi' : i < z.1.length := Finset.mem_range.mp hi
    refine ⟨hD z hz _ _ (List.eraseIdx_sublist _ _) (List.Sublist.refl _), ?_, h2⟩
    rw [List.length_eraseIdx_of_lt hi', h1]
    rfl
  · refine map_supported_mem (vbd V W) _ ?_
    rintro z ⟨hz, h1, h2⟩
    rw [vbd_single]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    refine Finsupp.single_mem_supported ℤ _ ?_
    have hi' : i < z.2.length := Finset.mem_range.mp hi
    refine ⟨hD z hz _ _ (List.Sublist.refl _) (List.eraseIdx_sublist _ _), h1, ?_⟩
    rw [List.length_eraseIdx_of_lt hi', h2]
    rfl
  · intro x hx
    have := map_supported_mem (hbd V W) (⊥ : Submodule ℤ _) ?_ x hx
    · simpa using this
    rintro z ⟨_, h1, _⟩
    rw [hbd_single, h1]
    simp

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqBoundaries_lower_bidegree_of_subClosed : ∀ (V W : Type) (D : Set (List V × List W)), SubClosed2 D → (∀ a b, ∀ x ∈ chains2 D (a + 1) b, hbd V W x ∈ chains2 D a b) ∧ (∀ a b, ∀ x ∈ chains2 D a (b + 1), vbd V W x ∈ chains2 D a b) ∧ (∀ b, ∀ x ∈ chains2 D 0 b, hbd V W x = 0) := by
  first
  | exact @GlobalTheory.SeqCx.bd_chains2
  | exact @GlobalTheory.SeqCx.vbd_single
  | exact @GlobalTheory.SeqCx.hbd_single
  | exact @GlobalTheory.SeqCx.map_supported_mem
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSetPermRepChainsIsoSplitSeqChains
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

private theorem split_set_boundary_comp_face_sum (R : Type) [CommRing R] (n p : ℕ) :
    (Finsupp.lmapDomain ℤ ℤ (fun x : SplitSet R n p => (x.1 : List ((Fin n → R) × (Fin n → R))))) ∘ₗ
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face R n p i)) =
    bd _ ∘ₗ Finsupp.lmapDomain ℤ ℤ
      (fun x : SplitSet R n (p + 1) => (x.1 : List ((Fin n → R) × (Fin n → R)))) := by
  apply Finsupp.lhom_ext
  intro l a
  have hlen : l.1.length = p + 1 := l.2.2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  unfold bd
  rw [Finsupp.linearCombination_single, hlen, Finset.smul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => a • ((-1 : ℤ) ^ i • Finsupp.single (l.1.eraseIdx i) (1 : ℤ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) a =
    a • ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) (1 : ℤ))
  simp [Finsupp.smul_single, mul_comm]

theorem splitSet_chains_incl : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  intro R _ n p
  have hD : ∀ c : SplitSet R n (p + 1) →₀ ℤ, (splitD R n p).hom c =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain (face R n p i) c : SplitSet R n p →₀ ℤ) := by
    intro c
    simp [splitD, permMap, Rep.sum_hom, Rep.hom_ofHom, Rep.zsmul_hom, Rep.smul_hom,
      Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, Set.image_univ]
    unfold chains
    congr 1
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
  · intro c
    rw [hD]
    have key := LinearMap.congr_fun (split_set_boundary_comp_face_sum R n p) c
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply] at key
    exact key

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSet_permRep_chains_iso_splitSeq_chains : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  first
  | exact @GlobalTheory.HomStab.splitSet_chains_incl
end
end

