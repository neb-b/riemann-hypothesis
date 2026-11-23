module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.PelPrim

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (ψ : X ⟶ Y) (e : ψ ≫ φ = 𝟙 X) :
    ChartPull L (L.pull φ) ψ :=
  have le : ∀ i, L.U i ≤ ψ ⁻¹ᵁ (L.pull φ).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : (ψ ≫ φ) y ∈ L.U i := by rw [e]; exact hy
    exact this)
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj =>
      ((gm_pull_g L φ ψ y (fun _ => i) (fun _ => j) (le i hi) (le j hj)).trans (by rw [e])).symm }

theorem lbIso_inv {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} {ψ : X ⟶ Y} (e : ψ ≫ φ = 𝟙 X)
    (h : LBIso M (L.pull φ)) : LBIso L (M.pull ψ) :=
  (LBIso.chartPull (chartPullPull M ψ ψ rfl) (chartPullSection L φ ψ e) h).symm

theorem lbIso_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (h : LBIso L' (L.pull F)) (h' : LBIso L'' (L'.pull F')) :
    LBIso L'' (L.pull (F' ≫ F)) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  obtain ⟨w'', T⟩ := exists_comp hL' w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') hL hL''
  exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp hL' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw φ ε⟩

section Cube
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem psum_comp (ψ : A ⟶ G) [IsMonHom ψ] {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A)) (x : Fin n → (T ⟶ G))
    (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) (I : Finset (Fin n)) :
    (psum A x' I).left ≫ ψ.left = U.left ≫ (psum G x I).left := by
  have e : psum A x' I ≫ ψ = U ≫ psum G x I :=
    (psum_hom (MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ) x' I).trans
      ((congrArg (fun z => psum G z I) (funext hx)).trans (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

def chartPullCube (ψ : A ⟶ G) [IsMonHom ψ] (M : LB G.left) {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A))
    (x : Fin n → (T ⟶ G)) (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) :
    ChartPull (cubeLB A x' (M.pull ψ.left)) (cubeLB G x M) U.left :=
  chartPullLinComb M _ _ _ _ U.left fun I => psum_comp ψ x' x U hx I.down

omit [IsCommMonObj A] in
theorem cube_isLB {L : LB A.left} (hL : L.IsLB) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB L hL _ _

omit [IsCommMonObj A] in
theorem cube_congr {L M : LB A.left} (h : LBIso L M) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) :
    LBIso (cubeLB A x L) (cubeLB A x M) := lbIso_linComb h _ _

theorem adj_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u v : A ⟶ A} {u₀ v₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀) (hv : v ≫ ψ = ψ ≫ v₀)
    (H : LBIso (cubeLB G ![fst G G ≫ u₀, snd G G] M) (cubeLB G ![fst G G, snd G G ≫ v₀] M)) :
    LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  have hP : (M.pull ψ.left).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hM (ψ.left y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g M ψ.left (𝟙 _) y J J hy hy]
      exact gm_self hM _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g M ψ.left (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g M ψ.left (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g M ψ.left (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hM _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine ((cube_congr h _).trans (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hP _) ?_).trans
    (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) H
  · fin_cases i <;> simp [hu]
  · fin_cases i <;> simp [hv]

theorem prim_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u : A ⟶ A} {u₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀)
    (H : LBIso M (cubeLB G ![𝟙 G, u₀] M)) : LBIso L (cubeLB A ![𝟙 A, u] L) := by
  have hP : (M.pull ψ.left).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hM (ψ.left y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g M ψ.left (𝟙 _) y J J hy hy]
      exact gm_self hM _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g M ψ.left (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g M ψ.left (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g M ψ.left (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hM _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine (h.trans hL hP (cube_isLB hP _) ?_).trans hL (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullPull M _ ψ.left rfl) (chartPullCube ψ M _ _ ψ fun i => ?_) H
  fin_cases i <;> simp [hu]

end Cube

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have h2 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have e := H.bar_eq H.rt
      rw [h] at e
      have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj, ← e]
      have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
      rw [hr] at e3
      have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
      have : (0 : ℝ) < H.d := by exact_mod_cast hd
      nlinarith [sq_nonneg r]
    · exact h
  have h3 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, h2, map_ofNat] at this
    rw [this]; ring
  have h4 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, h3, H.two_weight_eq_one_add_root]; ring
  exact mul_left_cancel₀ two_ne_zero h4

end GlobalTheory.PelPrim


open GlobalTheory.PelPrim in
theorem GlobalTheory.pelClass_prim_and_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b (spMap em)), PELClass D a bas ρ em t → (a w = H.w0 → a w' = H.bar H.w0 → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → PELClass D a bas ρ em t' := by
  intro E _ _ _ H D o _ g k J b em w w' a bas ρ t ⟨τ, φ, hφ, hL, hact, hpt⟩
  refine ⟨fun hw hw' => ?_, fun t' ⟨ψ, hψ, hL', hpt', hact'⟩ => ?_⟩
  · let _ := t.ab.comm
    have hinv : ∀ j, t.act j ≫ φ.inv = φ.inv ≫ τ.act.act (a j) := fun j => by
      rw [Iso.comp_inv_eq, Category.assoc, hact, φ.inv_hom_id_assoc]
    have hL₀ : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]) hL
    refine ⟨?_, adj_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) (hinv w') ?_,
      prim_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) ?_⟩
    · rw [← cancel_epi φ.hom, MonObj.comp_mul, ← hact, ← hact, ← MonObj.mul_comp, ← τ.act.add, hw, hw', cmHostUnit_add_conj_eq_one,
        τ.act.one, Category.id_comp, Category.comp_id]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
    obtain ⟨e, he, hl⟩ := grpPullback_iso hψ (isGrpPullback_of_iso (Iso.refl t.A))
    have hl' : e.hom.left = ψ := (Category.comp_id _).symm.trans hl
    subst hl'
    have hact₀ : ∀ j, t.act j ≫ e.inv = e.inv ≫ t'.act j := fun j => by
      have : t'.act j ≫ e.hom = e.hom ≫ t.act j := Over.OverMorphism.ext (hact' j)
      rw [Iso.comp_inv_eq, Category.assoc, this, e.inv_hom_id_assoc]
    have hpt₀ : ∀ i, t.pt i ≫ e.inv = t'.pt i := fun i => by
      have : t'.pt i ≫ e.hom = t.pt i := Over.OverMorphism.ext ((hpt' i).trans (Category.id_comp _))
      rw [Iso.comp_inv_eq, this]
    have hL₀ : LBIso t.L (t'.L.pull e.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]) hL'
    refine ⟨τ, φ ≪≫ e.symm, inferInstanceAs (IsMonHom (φ.hom ≫ e.inv)),
      lbIso_comp t'.isLB t.isLB τ.PP.isLB hL₀ hL, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
    · show _ ≫ φ.hom ≫ e.inv = (φ.hom ≫ e.inv) ≫ _
      rw [← Category.assoc, hact, Category.assoc, hact₀, Category.assoc]
    · obtain ⟨h₁, I, h₂, h₃⟩ := hpt K x β hx
      refine ⟨h₁, I, h₂, fun i => ?_⟩
      show _ ≫ φ.hom ≫ e.inv = _
      rw [← Category.assoc, h₃, Category.assoc, hpt₀]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreimageTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)

noncomputable section

namespace GlobalTheory.InvFieldBasis

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}

def expPt {B : Type} [CommRing B] [Algebra K B] (v : Fin n → (epsR K ⟶ G)) (e : Fin n → B)
    (he : ∀ i, e i * e i = 0) : sp (R₀ := K) B ⟶ G :=
  (List.ofFn fun i => (Chart.spMap (epsTo K (e i) (he i)) ≫ v i : sp (R₀ := K) B ⟶ G)).prod

variable {C : Type} [CommRing C] [Algebra K C]

theorem pushR_prodPts' (v : Fin n → (epsR K ⟶ G)) (c : Fin n → C) :
    pushR G (Chart.prodPts c (bcVec C v)) =
      expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  unfold Chart.prodPts expPt
  have key : ∀ i, pushR G (Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i) =
      (Chart.spMap (epsTo K (inr (c i) : DualNumber C) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v i :
        sp (R₀ := K) (DualNumber C) ⟶ G) := by
    intro i
    rw [Chart.pushR_spMap, pushR_bcVec, ← Category.assoc, Chart.spMap_comp]
    congr 2
    apply DualNumber.algHom_ext
    change Chart.scaleD (c i) (Chart.dualMapA K C (inr 1)) = epsTo K (inr (c i) : DualNumber C) _ (inr 1)
    rw [Chart.dualMapA_inr, map_one]
    simp only [Chart.scaleD]
    rw [show (inr 1 : DualNumber K) = DualNumber.eps from rfl, epsTo_eps, TrivSqZeroExt.map_inr,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]
  calc pushR G _ = pushRHom G (DualNumber C)
        (List.ofFn fun i => Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i).prod := rfl
    _ = _ := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg List.prod (List.ofFn_inj.mpr (funext key))

theorem existsUnique_expPt [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (w : sp (R₀ := K) (DualNumber C) ⟶ G) (hw : Chart.spMap ((fstD C).restrictScalars K) ≫ w = 1) :
    ∃! c : Fin n → C,
      w = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  have hb : IsLieBasis (bcVec C v) :=
    Chart.isLieBasis_baseChange (algebraMap K C) (isGrpPullback_pullback G (fB K C)) hv
      (fun j => bcVec_left_fst v j)
  have hwT : Chart.IsTan (pullR (R' := C) G w) := by
    rw [isTan_iff_mem, Chart.pushR_pullR]
    exact mem_redKer_of_section _ ((Algebra.ofId C (DualNumber C)).restrictScalars K) (fun a => by simp) hw
  have hT : IsTangent (pullR (R' := C) G w) := (Chart.isTan_iff _).1 hwT
  have key : ∀ c : Fin n → C, IsLieComb c (bcVec C v) (pullR (R' := C) G w) ↔
      w = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
    intro c
    rw [Chart.isLieComb_iff, ← pushR_prodPts']
    constructor
    · intro h'
      rw [← h', Chart.pushR_pullR]
    · intro h'
      apply Chart.pushR_inj (G := G)
      rw [Chart.pushR_pullR, h']
  obtain ⟨c, hc, hu⟩ := hb.2 _ hT
  exact ⟨c, (key c).1 hc, fun c' hc' => hu c' ((key c').2 hc')⟩

theorem preimage_translate {v : epsR K ⟶ G} (hv : IsTangent v) (W : G.left.Opens) :
    ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W = (snd (epsR K) G).left ⁻¹ᵁ W := by
  have e0w : Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (epsR K).hom = (𝟙_ (Over (Sp K))).hom := by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let e0 : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom) e0w
  have hev : e0 ≫ v = η := Over.OverMorphism.ext hv
  let J : G ⟶ epsR K ⊗ G := lift (toUnit G ≫ e0) (𝟙 G)
  have hJ1 : J ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) = 𝟙 G := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, Category.assoc, hev]
    exact _root_.one_mul (𝟙 G)
  have hJ2 : J ≫ snd (epsR K) G = 𝟙 G := lift_snd _ _
  have hpb : IsPullback (snd (epsR K) G).left (fst (epsR K) G).left G.hom (epsR K).hom :=
    (IsPullback.of_hasPullback (epsR K).hom G.hom).flip
  have hs := GlobalTheory.ConstThickening.structure_dualNumber K G.left (epsR K ⊗ G).left G.hom (fst (epsR K) G).left
    (snd (epsR K) G).left J.left hpb
    (by simpa using congrArg (fun f => f.left) hJ2)
    (by simp [J, e0])
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have h3 : J.left ⁻¹ᵁ (((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W) =
      J.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ W) := by
    rw [hc, hc, ← Over.comp_left, ← Over.comp_left, hJ1, hJ2]
  rw [← hs.1 (((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W), h3, hs.1]

theorem evalPt_pbT {B : Type} [CommRing B] {Y Z : Scheme.{0}} (x : Sp B ⟶ Z) (f : Z ⟶ Y) {O : Y.Opens}
    {O' : Z.Opens} (h : O' ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ x ⁻¹ᵁ O') (y : Sp B ⟶ Y) (hy : x ≫ f = y)
    (h'' : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Y, O)) : evalPt x O' h' (pbT f s O') = evalPt y O h'' s := by
  subst hy
  simp only [evalPt, pbT, dif_pos h]
  rw [← Scheme.Hom.appLE_comp_appLE (e₁ := h) (e₂ := h')]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]

private lemma evalPt_add {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a + b) = evalPt x O h a + evalPt x O h b := by
  unfold evalPt
  exact map_add _ a b

private lemma evalPt_mul {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a * b) = evalPt x O h a * evalPt x O h b := by
  unfold evalPt
  exact map_mul _ a b

private lemma evalPt_constFn' {B A : Type} [CommRing B] [CommRing A] {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (q : Z ⟶ Sp A) (φ : A →+* B) (hq : x ≫ q = Spec.map (CommRingCat.ofHom φ)) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a : A) : evalPt x O h (constFn q O a) = φ a := by
  unfold evalPt constFn
  have e1 : ∀ (g : Sp B ⟶ Sp A) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = g.appTop := fun g e => by
    simp only [Scheme.Hom.appLE]
    rw [show (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _]
    exact Category.comp_id _
  rw [← CommRingCat.comp_apply, ← Category.assoc]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [e1, hq, Scheme.ΓSpecIso_naturality]
  simp

variable {B : Type} [CommRing B] [Algebra K B]

theorem evalPt_translate {v : epsR K ⟶ G} (hv : IsTangent v)
    {dd : ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : IsInvDer v dd) (e : B) (he : e * e = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + e * evalPt z.left O h (dd O f) := by
  let t : sp (R₀ := K) B ⟶ epsR K ⊗ G := lift (Chart.spMap (epsTo K e he)) z
  have ht1 : t ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) =
      (Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
  have ht2 : t ≫ snd (epsR K) G = z := lift_snd _ _
  have ht3 : t ≫ fst (epsR K) G = Chart.spMap (epsTo K e he) := lift_fst _ _
  have hP := preimage_translate hv O
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have hO : t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) = z.left ⁻¹ᵁ O := by
    rw [hc, ← Over.comp_left, ht2]
  have hO' : ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O = z.left ⁻¹ᵁ O := by
    rw [← ht1, Over.comp_left, ← hc, hP, hO]
  have hT : ⊤ ≤ t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) := hO ▸ h
  refine ⟨hO' ▸ h, fun f => ?_⟩
  have e1 : evalPt t.left _ hT (pbT (snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h f :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h f
  have e2 : evalPt t.left _ hT (pbT (snd (epsR K) G).left (dd O f) ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h (dd O f) :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h (dd O f)
  have e3 : evalPt t.left _ hT (constFn (R := DualNumber K) (fst (epsR K) G).left
      ((snd (epsR K) G).left ⁻¹ᵁ O) DualNumber.eps) = e := by
    rw [evalPt_constFn' t.left (fst (epsR K) G).left (epsTo K e he : DualNumber K →+* B)]
    · simp
    · rw [← Over.comp_left, ht3]
      rfl
  rw [← evalPt_pbT t.left ((fst (epsR K) G ≫ v) * snd (epsR K) G).left hP.ge hT
    ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left (by rw [← Over.comp_left, ht1]) _ f,
    hd O f, evalPt_add, evalPt_mul, e1, e2, e3]

private lemma evalPt_congr' {B : Type} [CommRing B] {Z : Scheme.{0}} {x y : Sp B ⟶ Z} (hxy : x = y)
    (O : Z.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ O) (hy : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Z, O)) : evalPt x O hx s = evalPt y O hy s := by
  subst hxy
  rfl

theorem evalPt_expPt {v : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i))
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (expPt v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction n with
  | zero =>
    have h1 : expPt v e (fun i => he i i) * z = z := by
      simp only [expPt, List.ofFn_zero, List.prod_nil]
      exact _root_.one_mul z
    refine ⟨by rw [h1]; exact h, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left = z.left := congrArg (fun w => w.left) h1
    exact (evalPt_congr' hx O _ h f).trans (by simp)
  | succ n ih =>
    have hs : expPt v e (fun i => he i i) * z =
        (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [← _root_.mul_assoc]
      congr 1
      simp only [expPt, List.ofFn_succ, List.prod_cons]
    obtain ⟨h1, H1⟩ := ih (v := fun i => v i.succ) (hv := fun i => hv i.succ) (dd := fun i => dd i.succ)
      (hd := fun i => hd i.succ) (e := fun i => e i.succ) (he := fun i j => he i.succ j.succ)
    obtain ⟨h2, H2⟩ := evalPt_translate (hv 0) (hd 0) (e 0) (he 0 0) _ O h1
    refine ⟨by rw [hs]; exact h2, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left =
        ((Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z)).left :=
      congrArg (fun w => w.left) hs
    rw [evalPt_congr' hx O _ h2 f, H2 f, H1 f, H1 (dd 0 O f), Fin.sum_univ_succ]
    have hz : e 0 * ∑ i : Fin n, e i.succ * evalPt z.left O h (dd i.succ O (dd 0 O f)) = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [← _root_.mul_assoc, he 0 i.succ]; simp
    rw [_root_.mul_add, hz]
    ring

end GlobalTheory.InvFieldBasis
end
end

