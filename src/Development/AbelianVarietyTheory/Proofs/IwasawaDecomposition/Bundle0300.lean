module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
public import Formalism.LocalToGlobal.Columns.LevGCount
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.ChartBase

open NumberField

variable {E : Type} [Field E] [NumberField E]

theorem hform_one (σ : E →+* E) {n : ℕ} (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.one_apply]

theorem sig_int (σ : E →+* E) (s : 𝓞 E) : σ (s : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom σ s, rfl⟩

theorem sup_dual_eq (σ : E →+* E) {n : ℕ} (t pb : 𝓞 E) (ht : (t : E) ≠ 0) (hpb : (pb : E) = σ t)
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = r ∧ (j.1 + 1 = n → t ∣ r))
    (M : Submodule (𝓞 E) (Fin n → E))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Λ ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) Λ) = M := by
  classical
  have hσt : σ (t : E) ≠ 0 := (map_ne_zero σ).2 ht
  have hpb0 : (pb : E) ≠ 0 := by rw [hpb]; exact hσt
  apply le_antisymm
  · refine sup_le (fun x hx => (hM x).2 fun j => ?_) ?_
    · obtain ⟨r, hr, -⟩ := (hΛ x).1 hx j
      exact ⟨r, hr.symm⟩
    ·
      have key : ∀ y ∈ Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) Λ), pb • y ∈ M := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          refine (hM _).2 fun j => ?_
          have hs : ∀ c : 𝓞 E, (∀ j' : Fin n, j'.1 + 1 = n → t ∣ (if j' = j then c else 0)) →
              Pi.single j (c : E) ∈ Λ := by
            intro c hc
            refine (hΛ _).2 fun j' => ⟨if j' = j then c else 0, ?_, hc j'⟩
            by_cases h : j' = j
            · subst h; simp
            · simp [h, Pi.single_apply]
          have hval : ∀ c : 𝓞 E, Pi.single j (c : E) ∈ Λ → σ (c : E) * y j ∈ (algebraMap (𝓞 E) E).range := by
            intro c hc
            have := hy _ hc
            rw [hform_one] at this
            rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at this
            simpa using this
          show ((pb • y) j) ∈ _
          rw [Pi.smul_apply, Algebra.smul_def]
          by_cases hj : j.1 + 1 = n
          · have h1 := hval t (hs t fun j' _ => by split_ifs <;> simp)
            rw [show algebraMap (𝓞 E) E pb = (pb : E) from rfl, hpb]
            exact h1
          · have h1 := hval 1 (hs 1 fun j' hj' => by
              split_ifs with h
              · subst h; exact absurd hj' hj
              · simp)
            have h1' : y j ∈ (algebraMap (𝓞 E) E).range := by simpa using h1
            obtain ⟨a, ha⟩ := h1'
            exact ⟨pb * a, by rw [map_mul, ha]⟩
        | zero => simpa using M.zero_mem
        | add a b _ _ ha hb => rw [smul_add]; exact M.add_mem ha hb
        | smul c a _ ha => rw [smul_comm]; exact M.smul_mem c ha
      refine Submodule.smul_le.2 fun r hr y hy => ?_
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact M.smul_mem a (key y hy)
  · intro x hx
    have hx' := (hM x).1 hx
    let x1 : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let z : Fin n → E := fun j => if j.1 + 1 = n then x j / (pb : E) else 0
    have hsplit : x = x1 + pb • z := by
      funext j
      simp only [x1, z, Pi.add_apply, Pi.smul_apply, Algebra.smul_def]
      split_ifs
      · rw [show algebraMap (𝓞 E) E pb = (pb : E) from rfl]; field_simp; ring
      · simp
    rw [hsplit]
    refine Submodule.add_mem_sup ?_ ?_
    · refine (hΛ _).2 fun j => ?_
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x1, hj], fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hx' j
        exact ⟨r, by simp [x1, hj, hr], fun h => absurd h hj⟩
    · refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self pb) (Submodule.subset_span ?_)
      intro x0 hx0
      rw [hform_one]
      refine Subring.sum_mem _ fun i _ => ?_
      by_cases hi : i.1 + 1 = n
      · obtain ⟨r, hr, hd⟩ := (hΛ x0).1 hx0 i
        obtain ⟨s, rfl⟩ := hd hi
        obtain ⟨a, ha⟩ := hx' i
        simp only [z, hi, if_true, hr]
        have e : σ ((t * s : 𝓞 E) : E) * (x i / (pb : E)) = σ (s : E) * x i := by
          rw [hpb]; push_cast; rw [map_mul]; field_simp
        rw [e, ← ha]
        obtain ⟨b, hb⟩ := sig_int σ s
        exact ⟨b * a, by rw [map_mul, hb]⟩
      · simp only [z, hi, if_false, mul_zero]
        exact Subring.zero_mem _

end GlobalTheory.Mem.Col2.TC.ChartBase

namespace GlobalTheory.Mem.Col2.TC.ChartBase

open NumberField

variable {E : Type} [Field E] [NumberField E]

theorem mem_reL_iff {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin a → E)) (x : Fin a → E) :
    x ∈ L ↔ Formalism.L2.Forms.reV h E x ∈ Formalism.L2.Forms.reL h L := by
  subst h
  have e : ∀ y : Fin a → E, Formalism.L2.Forms.reV rfl E y = y := fun y => by
    funext j; simp [Formalism.L2.Forms.reV]
  constructor
  · intro hx; exact Submodule.mem_map.2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have : y = x := by
      have := hyx
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, e] at this
      exact this
    exact this ▸ hy

theorem reV_apply {a b : ℕ} (h : a = b) (x : Fin a → E) (j : Fin b) :
    Formalism.L2.Forms.reV h E x j = x (Fin.cast h.symm j) := by
  subst h; simp [Formalism.L2.Forms.reV]

end GlobalTheory.Mem.Col2.TC.ChartBase

namespace GlobalTheory.Mem.Col2.TC.ChartBase

theorem mem_of_baseL {B : Base} {a b : ℕ} (h : a = b) (t : 𝓞 B.host.E) (L : Submodule (𝓞 B.host.E) (Fin a → B.host.E))
    (L' : Submodule (𝓞 B.host.E) (Fin b → B.host.E)) (hL' : L' = Formalism.L2.Forms.reL h L)
    (hb : ∀ x, x ∈ L' ↔ x ∈ baseL B b t) (x : Fin a → B.host.E) :
    x ∈ L ↔ ∀ j : Fin a, ∃ r : 𝓞 B.host.E, x j = r ∧ (j.1 + 1 = a → t ∣ r) := by
  rw [mem_reL_iff h L x, ← hL', hb]
  unfold baseL
  simp only [Set.mem_setOf_eq, reV_apply]
  constructor
  · intro H j
    obtain ⟨r, hr, hd⟩ := H (Fin.cast h j)
    exact ⟨r, by simpa using hr, fun hj => hd (by simp [← h, hj])⟩
  · intro H j
    obtain ⟨r, hr, hd⟩ := H (Fin.cast h.symm j)
    exact ⟨r, hr, fun hj => hd (by simp [h, hj])⟩

end GlobalTheory.Mem.Col2.TC.ChartBase


open GlobalTheory.Mem.Col2.TC.ChartBase in
theorem GlobalTheory.Mem.Col2.TC.chart_base_sup_dual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • Formalism.L2.Herm.dualL (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 hm β).Lb = Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 := by
  intro B X I hOk hP l Z H F A hS hH hT u pb hpb i h1 hm β
  have hC := _root_.GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z
  obtain ⟨hG, hL0, -⟩ := hC.2.2.2 i hm

  have hG1 : ((I.rec7 l Z).sp.X i).gram = 1 := by
    ext a b
    have := congrFun (congrFun hG (finCongr (rankN (I.rec7 l Z) i hm) a)) (finCongr (rankN (I.rec7 l Z) i hm) b)
    simpa [gramN, Matrix.one_apply] using this

  have hσ : ∀ x : (I.rec7 l Z).host.E, ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = (I.rec7 l Z).host.conj x := fun x => by
    have := (I.rec7 l Z).host.isCMField_hostE
    exact (I.rec7 l Z).host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ (I.rec7 l Z).host.φ₀ x).trans
      ((I.rec7 l Z).host.conjE_apply (I.rec7 l Z).host.φ₀ x).symm)

  have hpi : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  have hT0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h0 => by
    have e := X.piT_norm u
    rw [h0, zero_mul] at e
    exact (B.T_prime u).ne_zero (by exact_mod_cast e.symm)

  have hM : ∀ x, x ∈ Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    rw [mem_reL_iff (rankN (I.rec7 l Z) i hm) _ x]
    have e : Formalism.L2.Forms.reL (rankN (I.rec7 l Z) i hm)
        (Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0) = selfDualLatticeCoords (I.rec7 l Z) i hm := by
      unfold Formalism.L2.Forms.reL Formalism.L2.Herm.crdLat
      rw [← Submodule.map_comp]; rfl
    rw [e, hL0]
    simp only [reV_apply]
    constructor
    · intro H j
      have h' := H (Fin.cast (rankN (I.rec7 l Z) i hm) j)
      rwa [Fin.cast_cast, Fin.cast_eq_self] at h'
    · intro H j; exact H _

  have hΛ : ∀ x, x ∈ (H.lev u i h1 hm β).Lb ↔ ∀ j : Fin ((I.rec7 l Z).sp.X i).rank, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r ∧
      (j.1 + 1 = ((I.rec7 l Z).sp.X i).rank → X.piT u ∣ r) := by
    rcases Nat.lt_or_ge i (I.rec7 l Z).R.m with hlt | hge
    · have h2 : i + 1 ≤ (I.rec7 l Z).R.m := hlt
      have hc := hH.carC u i h1 h2 β
      obtain ⟨k, hk⟩ := (hS u).1.mid i h1 h2
      exact mem_of_baseL (rankN (I.rec7 l Z) i (le_of_succ_m h2)) (X.piT u) _ _ hc.Lb_eq (hk.lb β)
    · obtain rfl : i = (I.rec7 l Z).R.m := le_antisymm hm hge
      obtain rfl : β = chM H u := @Unique.eq_default _ (H.Ch_m u).some β
      have hc := hH.carM u
      obtain ⟨k, hk⟩ := (hS u).1.ends _ le_rfl (Or.inr rfl)
      exact mem_of_baseL (rankN (I.rec7 l Z) _ le_rfl) (X.piT u) _ _ hc.Lb_eq (hk.lb ())
  unfold Formalism.L2.Herm.dualL
  rw [hG1]
  exact sup_dual_eq _ (X.piT u) pb hT0 (by
    have e := hσ ((X.piT u : 𝓞 B.host.E) : B.host.E)
    rw [hpi] at hpb
    exact hpb.trans e.symm) _ hΛ _ hM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelFunctionalsIntermediateStepsTrueColumn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.FvChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (J.reindex (finCongr h) (finCongr h)) (fun j => x ((finCongr h).symm j))
      (fun j => y ((finCongr h).symm j)) = hform σ J x y := by
  subst h
  simp [hform]

theorem mem_latS_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E)
    (Lb : Submodule (𝓞 E) (Fin a → E)) (w : HeightOneSpectrum (𝓞 F)) (t : Fin a → E ⊗[F] w.adicCompletion F)
    (ht : t ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb))) :
    (fun j => t ((finCongr h).symm j)) ∈ latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet σ (J.reindex (finCongr h) (finCongr h)) (reL h Lb))) := by
  subst h
  have hL : reL rfl Lb = Lb := by
    ext x
    simp [reL, reV]
  simpa [hL] using ht

theorem reGL_solve {a b : ℕ} (h : a = b) (w : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hg' : g' = reGL h _ g) (t : Fin a → E ⊗[F] w.adicCompletion F) (z : Fin a → E)
    (ht : (bc (prV (E := E) w) g).1 *ᵥ t = fun j => inclE (F := F) (w.adicCompletion F) (z j)) :
    ((bc (prV (E := E) w) g')⁻¹).1 *ᵥ
      (fun j => inclE (F := F) (w.adicCompletion F) (z ((finCongr h).symm j))) =
      fun j => t ((finCongr h).symm j) := by
  subst h hg'
  have hg : reGL rfl _ g = g := by
    ext
    simp [reGL]
  simp only [hg, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  rw [← ht, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem crdN_mem_LdG (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ LdG D i hi (clsCrd D u i hi c) := by
  apply Submodule.subset_span
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have h2 := hform_reindex (rankN D i hi) (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd (D.sp.X i) y) (Formalism.L2.Herm.crd (D.sp.X i) z.1)
  have h3 := Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) y z.1
  have hz := z.2
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hz
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hz y hy)
  refine ⟨r, ?_⟩
  change _ = hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) y ((finCongr (rankN D i hi)).symm j))
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) z.1 ((finCongr (rankN D i hi)).symm j))
  unfold gramN
  rw [h2]
  rw [hr]
  exact h3

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem exists_reindex_hom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h))
    (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ tr : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb)) →+
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' Lb')),
      ∀ t, (tr t).1 = fun j => t.1 ((finCongr h).symm j) := by
  subst hJ hL
  exact ⟨{ toFun := fun t => ⟨fun j => t.1 ((finCongr h).symm j), mem_latS_reindex h σ J Lb w t.1 t.2⟩
           map_zero' := rfl
           map_add' := fun _ _ => rfl }, fun _ => rfl⟩

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart


set_option maxHeartbeats 1000000 in
theorem fvTie_of_car {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A)
    (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u i) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
      (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  have hc := hH.carC u i h1 h2 β
  have hw : (H.vT u v).1 = ((F u).atT.eV v).1 := congrArg (fun e => (e v).1) (hH.eV u).symm
  suffices hs : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
        (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) from hs _ hw
  intro w hw'
  subst hw'
  obtain ⟨tr, htr⟩ := exists_reindex_hom (F := D.host.F) (rankN D i (le_of_succ_m h2))
    (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram (gramN D i (le_of_succ_m h2)) rfl
    (H.lev u i h1 (le_of_succ_m h2) β).Lb ((F u).ch i h1 h2 β).lev.Lb hc.Lb_eq ((F u).atT.eV v).1
  refine ⟨⟨((F u).fMeC i h1 h2 β v).toAddMonoidHom.comp
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2).toAddMonoidHom.comp tr), ?_⟩⟩
  intro c z t ht
  have hmem := crdN_mem_LdG D u i (le_of_succ_m h2) c.1 z
  have hp := hT.prC u i h1 h2 v c.1 z ⟨_, hmem⟩ rfl
  refine (congrArg ((D.fm u).fv i v c.1) hp).symm.trans ?_
  have key : ((bc (prV (E := D.host.E) ((F u).atT.eV v).1) (((F u).ch i h1 h2 β).y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
        (crdN D i (le_of_succ_m h2) z.1 a)) = (tr t).1 :=
    (reGL_solve (rankN D i (le_of_succ_m h2)) ((F u).atT.eV v).1 ((H.cls u i h1 (le_of_succ_m h2) β).y c).1
      (((F u).ch i h1 h2 β).y c).1 (hc.y_eq c) t.1 (Formalism.L2.Herm.crd (D.sp.X i) z.1) ht).trans (htr t).symm
  have hz := (congrArg (fun x => x ∈ latS (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
    (intV D.host.E ((F u).atT.eV v).1)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E)
      (gramN D i (le_of_succ_m h2)) ((F u).ch i h1 h2 β).lev.Lb))) key).mpr (tr t).2
  refine ((F u).fvC i h1 h2 v β c ⟨_, hmem⟩ hz).trans ?_
  exact congrArg (fun x => ((F u).fMeC i h1 h2 β v)
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2) x)) (Subtype.ext key)

end GlobalTheory.Mem.Col2.TC.FvChart


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TC.fvTie_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u i), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => (I.rec7 l Z).clsLat u i c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u i h1 h2 v β
  exact FvChart.fvTie_of_car H F A hH hT u i h1 h2 v β
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoarseLast
section
open Formalism.L2.Col

namespace GlobalTheory.MemXSym

open Formalism.L2.Forms

theorem facts {n k r t m rS : ℕ} (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1) (x : ℕ) (hx : x < n) :
    (x < r ∧ coarse r (List.replicate m t) x = 0 ∧ lvSym k rS t x = symIdx k rS x ∧ symIdx k rS x < r) ∨
    (r ≤ x ∧ lvSym k rS t x + 1 = r + coarse r (List.replicate m t) x ∧ 1 ≤ coarse r (List.replicate m t) x) := by
  rcases Nat.lt_or_ge x r with h1 | h1
  · refine Or.inl ⟨h1, coarse_of_lt h1, ?_, ?_⟩
    · have : x < rSym k rS := by unfold rSym; omega
      rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega
    · unfold symIdx; split_ifs <;> omega
  · refine Or.inr ⟨h1, ?_, by rw [coarse_of_le h1]; omega⟩
    have hx' : ¬ x < rSym k rS := by unfold rSym; omega
    have hs : rSym k rS = r := by unfold rSym; omega
    unfold lvSym; rw [if_neg hx', hs]
    rcases Nat.lt_or_ge x (r + m * t) with h2 | h2
    · rw [GlobalTheory.TopLawSym.coarse_eq ht h1 h2, Nat.add_assoc]
    · have hx2 : x = r + m * t := by omega
      subst hx2
      rw [coarse_of_le h1, blkIdx_replicate_of_le t m (r + m * t - r) (by omega), Nat.add_sub_cancel_left,
        Nat.mul_div_cancel _ ht, Nat.add_assoc]

theorem facts_lt {k r t rS x : ℕ} (hr : r = k + 2 * rS + 1) (hx : x < r) :
    lvSym k rS t x = symIdx k rS x := by
  have : x < rSym k rS := by unfold rSym; omega
  rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega

theorem coarse_last {r t m x : ℕ} (hx : x < r + m * t) :
    coarse r (List.replicate m t) x < coarse r (List.replicate m t) (r + m * t) := by
  have cN : coarse r (List.replicate m t) (r + m * t) = m + 1 := by
    rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m (r + m * t - r) (by omega)]
  rw [cN]
  rcases Nat.lt_or_ge x r with h1 | h1
  · rw [coarse_of_lt h1]; omega
  · rw [coarse_of_le h1]; have := blkIdx_replicate_lt t m (x - r) (by omega); omega

variable {κ : Type} [Field κ]

theorem inJ_of_mem {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : M ∈ HXmsym κ n k r t m rS h) : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ) := by
  obtain ⟨hJ, hF⟩ := Subgroup.mem_inf.mp hM
  have hF' : ∀ i j : Fin n, j.val = r + m * t → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := hF
  obtain ⟨hB, h0⟩ := mem_HPar.mp hJ
  have hkr : k + rS ≤ r := by omega
  rw [mem_HPsymF_iff hkr] at h0
  obtain ⟨p1, p2, p3⟩ := h0
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩
  · rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩
    · rw [lx, ly] at hxy
      exact p1 ⟨x, hx⟩ ⟨y, hy⟩ hxy
    · exfalso; omega
    · exact (mem_btG.mp hB) x y (by omega)
    · exact (mem_btG.mp hB) x y (by omega)
  · exact p2 ⟨x, by unfold rSym at hx; omega⟩
  · exact p3 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy
  · have hy' : y.val = r + m * t := by omega
    constructor
    · rw [hF' x y hy', Matrix.one_apply]
    · by_cases hxy : x = y
      · subst hxy; rw [hF' x x hy', Matrix.one_apply]
      · rw [if_neg hxy]
        apply (mem_btG.mp hB) y x
        have hx1 : x.val < r + m * t := by
          have := x.2; have : x.val ≠ y.val := fun e => hxy (Fin.ext e); omega
        rw [hy']
        exact coarse_last hx1

theorem mem_of_inJ {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ)) : M ∈ HXmsym κ n k r t m rS h := by
  obtain ⟨q1, q2, q3, q4⟩ := hM
  have hkr : k + rS ≤ r := by omega
  have hB : M ∈ blockUT n κ r (List.replicate m t) := mem_btG.mpr fun x y hxy => q1 x y (by
    rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩ <;> omega)
  refine Subgroup.mem_inf.mpr ⟨mem_HPar.mpr ⟨hB, ?_⟩, ?_⟩
  · rw [mem_HPsymF_iff hkr]
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · refine q1 (Fin.castLE h i) (Fin.castLE h j) ?_
      simp only [Fin.coe_castLE]
      rw [facts_lt hr i.2, facts_lt hr j.2]
      exact hij
    · exact q2 (Fin.castLE h i) (by simp only [Fin.coe_castLE]; unfold rSym; omega)
    · exact q3 (Fin.castLE h i) (Fin.castLE h j) (by simpa using hi) (by simpa using hj)
  · intro x y hy
    rw [(q4 rfl x y (by omega)).1, Matrix.one_apply]

theorem memX (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t)
    (hn : n = r + m * t + 1) (M : GL (Fin n) κ) :
    M ∈ HXmsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t true := by
  constructor
  · intro hM
    show InJSym k rS t true _ ∧ InJSym k rS t true _
    exact ⟨inJ_of_mem h hr ht hn hM, inJ_of_mem h hr ht hn (Subgroup.inv_mem _ hM)⟩
  · intro hM
    exact mem_of_inJ h hr ht hn hM.1

end GlobalTheory.MemXSym
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpoly
section
noncomputable section

namespace GlobalTheory.SemisimplificationExists

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_semisimplification : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k),
    ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
      ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  fun ρ => GlobalTheory.RowPar.exists_ss ρ

end GlobalTheory.SemisimplificationExists
end
end

