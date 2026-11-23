module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R]

theorem free_ext {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G)
    (h : ∀ U x, Sec.map a (freeGen R P U x) = Sec.map b (freeGen R P U x)) : a = b := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down

theorem free_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let η : (freeP R).obj P ⟶ F.obj :=
    { app := fun U => ModuleCat.freeDesc (TypeCat.ofHom fun x => a U.unop x.down)
      naturality := fun U V g => by
        apply ModuleCat.free_hom_ext
        intro x
        change (ModuleCat.freeDesc _) ((ModuleCat.free _).map _ (ModuleCat.freeMk x)) =
          (F.obj.map g) ((ModuleCat.freeDesc _) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        exact (ha V.unop U.unop g.unop x.down).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm η,
    fun U x => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ F).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h) (ModuleCat.freeMk (ULift.up x))
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom (ModuleCat.free_map_apply _ _)

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))) (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.free_map_apply _ _)

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

def mapHom (F G : Shv R) {U : Scheme.{0}} (x : Sec F U) : (F ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun φ => Sec.map φ x) (fun _ _ => rfl)

theorem isZero_chains (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => ?_)
  change -(i : ℤ) = p at hi
  omega

theorem chains_d (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl
  have h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p
  rw [h1, Iso.inv_hom_id_assoc]
  exact congrArg (· ≫ (chainsXIso R E p).inv) h2

theorem chains_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ ((chainsN R).map f).f p ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

variable {E : Spc} {I : Cx R} {n : ℤ}

theorem ev_def (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl

theorem ev_ext (α β : Cochain ((chains R).obj E) I n) (h : ∀ p s h U x, _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = _root_.GlobalTheory.EtC.ev (R := R) β p s h U x) : α = β := by
  ext p s hs : 1
  by_cases hp : p ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    exact free_ext _ _ (fun U x => h k s hs U x)
  · exact (isZero_chains E p (by omega)).eq_of_src _ _

theorem ev_exists (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = a p s h U x := by
  have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
      Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
        a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using key
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

theorem ev_res (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sx E p U) : Sec.res g (_root_.GlobalTheory.EtC.ev (R := R) α p s h U x) = _root_.GlobalTheory.EtC.ev (R := R) α p s h V (x.res g) := by
  rw [ev_def, map_res, freeGen_res]
  rfl

theorem ev_add (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) (a + b) p s h U x = _root_.GlobalTheory.EtC.ev (R := R) a p s h U x + _root_.GlobalTheory.EtC.ev (R := R) b p s h U x := by
  simp [_root_.GlobalTheory.EtC.ev, Cochain.add_v]

def evHom (I : Cx R) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun a => _root_.GlobalTheory.EtC.ev (R := R) a p s h U x) (fun a b => ev_add a b p s h U x)

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := map_zero (evHom I n p s h U x)

theorem ev_zsmul (c : ℤ) (a : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : _root_.GlobalTheory.EtC.ev (R := R) (c • a) p s h U x = c • _root_.GlobalTheory.EtC.ev (R := R) a p s h U x := map_zsmul (evHom I n p s h U x) c a

theorem ev_pull {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = _root_.GlobalTheory.EtC.ev (R := R) α p s h U (x.map f) := by
  rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

theorem ev_δ_zero {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (s t : ℤ)
    (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
    _root_.GlobalTheory.EtC.ev (R := R) (δ n m α) 0 t ht U x = Sec.map (I.d s t) (_root_.GlobalTheory.EtC.ev (R := R) α 0 s hs U x) := by
  rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
    (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
  rfl

theorem ev_δ_succ {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
    _root_.GlobalTheory.EtC.ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (_root_.GlobalTheory.EtC.ev (R := R) α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • _root_.GlobalTheory.EtC.ev (R := R) α p t (by omega) U (x.face i) := by
  rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
    Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
  refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zsmul, map_sum, Units.smul_def]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [Preadditive.zsmul_comp, map_zsmul]
  congr 1
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

end GlobalTheory.EtC.CupSpec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterPrincipalSpec
section
open GlobalTheory.StepData ValuativeRel Matrix

namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reGL_symm_mem_KO {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  have hinv : ((reGL e).symm g)⁻¹ = (reGL e).symm g⁻¹ := (map_inv _ _).symm
  rw [mem_KO, mem_KO, hinv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 (e i) (e j), fun i j => h2 (e i) (e j)⟩

variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem blk_ixSucc_inl {j : ℕ} (a : Ix r t j) : (ixSucc r t j (.inl a)).blk = a.blk := by
  rcases a with x | ⟨i, s⟩ <;> rfl

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem blk_ixSucc_inr {j : ℕ} (s : t) : (ixSucc r t j (.inr s)).blk = j + 1 := rfl

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem Ix.blk_le {j : ℕ} (a : Ix r t j) : a.blk ≤ j := by
  rcases a with x | ⟨i, s⟩
  · exact Nat.zero_le _
  · exact i.isLt

private theorem mem_reindex_J_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : TypeDatum k a) (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J :=
  Level.mem_map

theorem mem_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix r t j) k) :
    g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ KO k (Ix r t j) ∧
      (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1) := by
  revert g
  induction j with
  | zero =>
    intro g
    rw [TypeDatum.iter_zero, mem_reindex_J_iff]
    change (reGL (ixZero r t)).symm g ∈ KOne k r ↔ _
    have e0 : ((reGL (ixZero r t)).symm g).val - 1 = g.val.toBlocks₁₁ - 1 := by
      rw [reGL_symm_val]; rfl
    constructor
    · intro hg
      refine ⟨(reGL_symm_mem_KO (ixZero r t) g).1 (KOne_le_KO hg), ?_, ?_⟩
      · intro a b hab
        exfalso
        rcases a with x | ⟨i, _⟩
        · exact Nat.not_lt_zero _ hab
        · exact i.elim0
      · rw [← e0]; exact mem_KOne.1 hg
    · rintro ⟨-, -, h1⟩
      rw [mem_KOne, e0]; exact h1
  | succ j ih =>
    intro g
    rw [TypeDatum.iter_succ, mem_reindex_J_iff, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, reGL_symm_mem_KO]
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm g).val x y = g.val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    constructor
    · rintro ⟨hK, ⟨g', hg', e'⟩, h21⟩
      obtain ⟨-, hlow, h11⟩ := (ih g').1 hg'
      have hg'v : ∀ x y, g'.val x y = g.val (ixSucc r t j (.inl x)) (ixSucc r t j (.inl y)) := by
        intro x y; rw [e']; exact hv (.inl x) (.inl y)
      refine ⟨hK, ?_, ?_⟩
      · intro a b hab
        obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [← hg'v]
          rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          exact hlow x y hab
        · rw [blk_ixSucc_inr, blk_ixSucc_inl] at hab
          have := Ix.blk_le x
          omega
        · rw [← hv]; exact h21 s y
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'; exact hg'v (.inl i) (.inl i')
        rw [← hb]; exact h11
    · rintro ⟨hK, hlow, h11⟩
      have hK' : (reGL (ixSucc r t j)).symm g ∈ KO k (Ix r t j ⊕ t) := (reGL_symm_mem_KO _ g).2 hK
      have h21 : MaxM ((reGL (ixSucc r t j)).symm g).val.toBlocks₂₁ := by
        intro s y
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inr s) (.inl y)) < 1
        rw [hv]
        apply hlow
        rw [blk_ixSucc_inr, blk_ixSucc_inl]
        exact Nat.lt_succ_of_le (Ix.blk_le y)
      refine ⟨hK, ?_, h21⟩
      obtain ⟨⟨g', hg'K, e'⟩, -⟩ := exists_diag_blocks hK' h21
      refine ⟨g', (ih g').2 ⟨hg'K, ?_, ?_⟩, e'⟩
      · intro x y hxy
        rw [e']
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inl x) (.inl y)) < 1
        rw [hv]
        apply hlow
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'
          rw [e']
          exact hv (.inl (.inl i)) (.inl (.inl i'))
        rw [hb]; exact h11

theorem lam_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ)
    (hd : ∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) :
    ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) := by
  revert g d hd
  induction j with
  | zero =>
    intro g d hd
    rw [Fin.prod_univ_zero]
    exact (Level.map_lam (reGL (ixZero r t)) (TypeDatum.principal k r).toLevel g).trans rfl
  | succ j ih =>
    intro g d hd
    have hmem : (reGL (ixSucc r t j)).symm (g : GL (Ix r t (j + 1)) k) ∈
        ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := g.2
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm (g : GL (Ix r t (j + 1)) k)).val x y =
        (g : GL (Ix r t (j + 1)) k).val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    obtain ⟨-, ⟨g', hg', e'⟩, -, -, ⟨D, -, eD⟩⟩ := ((TypeDatum.principal k r).iter t μ hμ j).mem_stepJ.1 hmem
    have hstep := ((TypeDatum.principal k r).iter t μ hμ j).step_lam_eq (μ (j + 1)) (hμ _) ⟨_, hmem⟩
      ⟨g', hg'⟩ e' D eD
    have hre := Level.map_lam (reGL (ixSucc r t j))
      (((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).toLevel g
    refine hre.trans (hstep.trans ?_)
    have hD : Matrix.GeneralLinearGroup.det D = d (Fin.last j) := by
      ext
      rw [hd (Fin.last j)]
      show (D : Matrix t t k).det = _
      rw [eD]
      congr 1
    rw [Fin.prod_univ_castSucc, ih ⟨g', hg'⟩ (fun c => d c.castSucc) (fun c => by
      show ((d c.castSucc : kˣ) : k) = _
      rw [hd c.castSucc]
      congr 1
      ext s s'
      show (g : GL (Ix r t (j + 1)) k).val (.inr (c.castSucc, s)) (.inr (c.castSucc, s')) =
        g'.val (.inr (c, s)) (.inr (c, s'))
      rw [e']
      exact (hv (.inl (.inr (c, s))) (.inl (.inr (c, s')))).symm), hD]
    simp only [Fin.val_castSucc, Fin.val_last]

theorem iter_principal_spec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, GlobalTheory.SplitWeil.IsTame (μ j)) (j : ℕ), (∀ g : GL (Ix r t j) k, g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ GlobalTheory.SplitWeil.KO k (Ix r t j) ∧ (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1)) ∧ ∀ (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ), (∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) → ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) :=
  fun μ hμ j => ⟨fun g => mem_iter_principal μ hμ j g, fun g d hd => lam_iter_principal μ hμ j g d hd⟩

end GlobalTheory.StepData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem ker_kappa_xI_comap :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C))
      (U : Z.affineOpens),
      (letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = secAlg C h U ∧
         RingHom.ker (kappa A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))
           ((xI A B C J).comap (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) =
         J.map (Algebra.TensorProduct.map φ (AlgHom.id A B))) := by
  intro A B C _ _ _ _ _ J Z h U
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := h ≫ f
  let W := pullback.snd (str A B) g ⁻¹ᵁ (U : Z.Opens)
  let := (secAlg A g U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        have hs : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ U (by simp) =
            CommRingCat.ofHom (algebraMap A C) ≫
              (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) := by
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
                h.appLE ⊤ U (by simp) :=
              congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h f ⊤ U (by simp))
            _ = _ := (Scheme.ΓSpecIso_inv_naturality_assoc
              (CommRingCat.ofHom (algebraMap A C)) (h.appLE ⊤ U (by simp))).symm
        exact (congrArg (fun F => F.hom a) hs).symm }
  refine ⟨φ, rfl, ?_⟩
  have : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have hTensor : ((bc A B f h).appLE ⊤ W (by simp)).hom.comp (psi A B C) =
      (theta A B g U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
    have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (pullback.snd (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have hpsi (c : C) (b : B) : psi A B C (c ⊗ₜ[A] b) =
        (pullback.fst (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        (pullback.snd (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      have h1 := congrArg (fun F => F.hom b) eL
      have h2 := congrArg (fun F => F.hom c) eR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      rw [h1, h2, ← map_mul, ← map_mul]
      simp [psi]
    have eF : (pullback.fst (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        (pullback.fst (str A B) g).appLE ⊤ W (by simp) := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
    have eS : (pullback.snd (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        h.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) g ≫ h)
        (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
      have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
      rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, mul_comm]
      let : Algebra A Γ(pullback (str A B) g, W) :=
        (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      symm
      change theta A B g U (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) g).app U).hom (secAlg C h U c) *
          ((pullback.fst (str A B) g).appLE ⊤ W (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B f h)) ⟨W, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine,
    GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, hTensor,
    ← Ideal.map_map, Ideal.comap_map_of_bijective _
      (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
section
open ValuativeRel

noncomputable section

namespace GlobalTheory.UnfoldLoss

open GlobalTheory.SplitFlip GlobalTheory.FunObj

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def varLat (G : Grid k) (ϖ : kˣ) (n : ℕ) : AddSubgroup (Vars G) where
  carrier := {e | ∀ j r, valuation k (e j r) ≤ valuation k ((ϖ ^ n : kˣ) : k)}
  zero_mem' := fun j r => by
    show valuation k 0 ≤ _
    simp
  add_mem' := fun {a b} ha hb j r => (Valuation.map_add _ _ _).trans (max_le (ha j r) (hb j r))
  neg_mem' := fun {a} ha j r => by
    show valuation k (-(a j r)) ≤ _
    rw [Valuation.map_neg]
    exact ha j r

def varCount (G : Grid k) : ℕ :=
  ∑ j : Fin (G.m - 1), Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)))

end GlobalTheory.UnfoldLoss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocalStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → IsSMulRegular A f → Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) → Module.Free R A := by
  first | exact @GlobalTheory.AnnRegSeq.free_of_free_quotient_map | exact GlobalTheory.AnnRegSeq.free_of_free_quotient_map | (intros; apply GlobalTheory.AnnRegSeq.free_of_free_quotient_map <;> assumption)
end

