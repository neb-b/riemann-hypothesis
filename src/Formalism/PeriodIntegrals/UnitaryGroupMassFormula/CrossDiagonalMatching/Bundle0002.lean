module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PKerAtP

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnkLkLocP
section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dnk_tld (T : Forms0 D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → D.host.E)
    (hy : y ∈ Ld D u 0 (Nat.zero_le _) c) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y ∈ clsCrd D u 0 (Nat.zero_le _) c := by
  rw [Nat.cast_smul_eq_nsmul]
  have hLd := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.dual_class_lattice_eq_global T.cls0 c
  have hfin := tld_isLat (u := u) 0 (Nat.zero_le _) c
  have hone := Formalism.L2.GlobalTheoryTheory.Comp.glob_one (F := D.host.F) hfin
  have hdl : ∀ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb,
      ((D.mem u).A.T : ℕ) • x ∈ T.cls0.lev.Lb := by
    intro x hx
    unfold Formalism.L2.GlobalTheoryTheory.Comp.dl at hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact T.cls0.lev.Lb_dual x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ ihx ihy => rw [smul_add]; exact add_mem ihx ihy
    | smul a x _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih
  have hkey : ∀ w ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb),
      ((D.mem u).A.T : ℕ) • w ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) T.cls0.lev.Lb := by
    intro w hw
    unfold latS at hw ⊢
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨_, hdl x hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, map_nsmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ ihx ihy => rw [smul_add]; exact add_mem ihx ihy
    | smul a x _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih
  have hmem : ∀ (g : GL (Fin (D.R.N 0)) (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Λ : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (x : Fin (D.R.N 0) → D.host.E),
      x ∈ Formalism.UG.CS.globLat g Λ ↔ ((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ
        (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Λ :=
    fun _ _ _ => Iff.rfl
  rw [hLd, hmem] at hy
  rw [← hone, hmem, inv_one, Units.val_one, Matrix.one_mulVec, T.cls0.y_lat c]
  have e : (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((((D.mem u).A.T : ℕ) • y) i)) =
      ((D.mem u).A.T : ℕ) • (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (y i)) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [e, Matrix.mulVec_smul]
  exact hkey _ hy

theorem dnk_lk_le (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    Lk T.atT 0 (Nat.zero_le _) v c ≤ Ld D u 0 (Nat.zero_le _) c := sup_le (cls_le_ld T c) Submodule.smul_le_right


set_option maxHeartbeats 2000000 in
theorem dnk_lk_locP (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c) ≤
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
  intro x hx
  have hx' : ∃ s ∈ (T.atT.Pv v).primeCompl, s • x ∈ Lk T.atT 0 (Nat.zero_le _) v c := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
  obtain ⟨t, ht, y, hy, hty⟩ := exists_smul_eq_smul_of_mem_ideal_smul T.atT v (Ld D u 0 (Nat.zero_le _) c) b hb
  show ∃ r ∈ (T.atT.Pv v).primeCompl, r • x ∈ clsCrd D u 0 (Nat.zero_le _) c
  refine ⟨t * s, Submonoid.mul_mem _ (Ideal.mem_primeCompl_iff.mpr ht) hs, ?_⟩
  rw [mul_smul, ← hab, smul_add, hty]
  exact Submodule.add_mem _ (Submodule.smul_mem _ t ha) (dnk_tld T c y hy)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem dnk_char (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (y : Fin (D.R.N 0) → D.host.E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔
      ∃ s : 𝓞 D.host.E, s ∉ T.atT.Pv v ∧ ∃ h : s • y ∈ Lk T.atT 0 (Nat.zero_le _) v c,
        g (T.lv0.prk v c ⟨_, h⟩) = 0 := by
  have memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L := fun _ _ => Iff.rfl
  have memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z := fun _ _ _ => Iff.rfl
  have hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x) :=
    fun M t x => Matrix.mulVec_smul M t x
  have hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl →
      a * b ∈ (T.atT.Pv v).primeCompl := fun ha hb => Submonoid.mul_mem _ ha hb
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := (memP _ _).mp hy
    obtain ⟨x, hx, hxy⟩ := (memM _ _ _).mp hsy
    have hxd : x ∈ Ld D u 0 (Nat.zero_le _) c1 := dnk_lk_le T v c1 hx
    have h1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
      rw [← hl]
      exact (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hxd, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp h1
    have htx' : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [hsm]; exact Submodule.mem_sup_left htx
    have hfx : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨t • x, Submodule.smul_mem _ t hxd⟩) = 0 :=
      (T.lv0.fv_ker v c1 _).mpr (Submodule.smul_mem _ t hx)
    have hmem : (t * s) • y ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [mul_smul, ← hxy, ← hsm]; exact htx'
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mp (hPc ht hs), hmem, ?_⟩
    have e : (⟨(t * s) • y, hmem⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, htx'⟩ := by
      apply Subtype.ext
      show (t * s) • y = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x)
      rw [mul_smul, ← hxy, hsm]
    rw [e]
    exact (hfun ⟨t • x, Submodule.smul_mem _ t hxd⟩ htx').symm.trans hfx
  · rintro ⟨s, hs, hsy, hg⟩
    have h1 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
      dnk_lk_locP T v c ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hsy⟩)
    rw [← hl] at h1
    obtain ⟨t, ht, htm⟩ := (memP _ _).mp h1
    obtain ⟨x, hx, hxe⟩ := (memM _ _ _).mp htm
    have hxk : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [hxe]; exact Submodule.smul_mem _ t hsy
    have hf : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨x, hx⟩) = g (T.lv0.prk v c ⟨_, hxk⟩) := hfun ⟨x, hx⟩ hxk
    have e : (⟨_, hxk⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = t • ⟨s • y, hsy⟩ := Subtype.ext hxe
    rw [e, T.lv0.prk_smul, map_smul, hg, smul_zero] at hf
    have hxk1 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c1 := (T.lv0.fv_ker v c1 ⟨x, hx⟩).mp hf
    exact (memP _ _).mpr ⟨t * s, hPc ht (Ideal.mem_primeCompl_iff.mpr hs),
      (memM _ _ _).mpr ⟨x, hxk1, by rw [hxe, mul_smul]⟩⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem dnk_latP (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (γ γ' : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun' : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = g (T.lv0.prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by
  have memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L := fun _ _ => Iff.rfl
  have memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z := fun _ _ _ => Iff.rfl
  have hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x) :=
    fun M t x => Matrix.mulVec_smul M t x
  have hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl →
      a * b ∈ (T.atT.Pv v).primeCompl := fun ha hb => Submonoid.mul_mem _ ha hb
  have hloc : ∀ (c' : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E), w ∈ Lk T.atT 0 (Nat.zero_le _) v c' →
      ∃ r ∈ (T.atT.Pv v).primeCompl, r • w ∈ clsCrd D u 0 (Nat.zero_le _) c' := fun c' w hw =>
    (memP _ _).mp (dnk_lk_locP T v c' ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hw⟩))
  have hA : ∀ y, y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔
      y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) := fun y =>
    (dnk_char T v c c1 g γ hl hfun y).trans (dnk_char T v c c2 g γ' hl' hfun' y).symm
  have hcomp : ∀ x : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x) :=
    fun x => by rw [Units.val_mul, Matrix.mulVec_mulVec]
  have hinv : ∀ w : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ w : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinj : ∀ a b : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ a = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ b → a = b := fun a b h =>
    (hinv a).symm.trans ((congrArg (fun w => ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) h).trans (hinv b))
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (memP _ _).mp hz
    obtain ⟨x, hx, hxz⟩ := (memM _ _ _).mp hsz
    have hx2 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := Submodule.mem_sup_left hx
    have hA2 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) :=
      (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hx2, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp ((hA _).mpr hA2)
    obtain ⟨w, hw, hwx⟩ := (memM _ _ _).mp htx
    have hx' : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) := by rw [← hxz, hcomp, hinv']
    have hwz : w = (t * s) • z := by
      apply hinj
      rw [hwx, hx', mul_smul, hsm _ t (s • z)]
    obtain ⟨r, hr, hrw⟩ := hloc c1 w hw
    exact (memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), by rw [mul_smul, ← hwz]; exact hrw⟩
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (memP _ _).mp hz
    have hk1 : s • z ∈ Lk T.atT 0 (Nat.zero_le _) v c1 := Submodule.mem_sup_left hsz
    have hA1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) :=
      (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨_, hk1, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp ((hA _).mp hA1)
    obtain ⟨w, hw, hwx⟩ := (memM _ _ _).mp htx
    obtain ⟨r, hr, hrw⟩ := hloc c2 w hw
    refine (memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), (memM _ _ _).mpr ⟨r • w, hrw, ?_⟩⟩
    simp only [hcomp, hsm, hwx, hinv, mul_smul]

end CrossDiaZero

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.UpF
section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upF (T : Forms0 D u) (v v' : (D.mem u).A.vT) (hvv : v ≠ v') (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ)
    (c c1 c2 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (κd : T.cls0.lev.U)
    (hx : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1)
    (γ γ2 : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ2 : γ2 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}))
    (h5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
        (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩))
    (g5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c3))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c2),
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 x) = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hx⟩))
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3)) :
    ∀ w (hw : w ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) •
          (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈
          Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • w,
            Submodule.smul_mem _ _ hw⟩) := by
  intro w hw
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨hdd, hfg, hH⟩ := rlv_coordFacts (D := D) (u := u) 0 (Nat.zero_le _)
  have hLat := diamond_lattice_transport T v' k δ hδ c c2 γd hγd κd hx
  have memInv : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c,
      ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈
        Ld D u 0 (Nat.zero_le _) c2 := by
    intro y hy
    rw [← hLat.2, mem_mul_lattice_iff] at hy
    exact hy
  have hΓU : (γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) ∈
      UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (mul_mem (inv_mem hγ2) (inv_mem hγd)) hγ
  have hne1 : (1 : 𝓞 D.host.E) ∉ T.atT.Pv v := (T.atT.Pv v).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)

  have hQd := local_dual_Q_eq_of_P T.atT v c3 c1 _ hΓU hP
  obtain ⟨a1, ha1P, ha1Q, ha1⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPd.le hQd.le
    (x := ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)
    ⟨w, hw, rfl⟩

  have hPw : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w ∈
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) :=
    (rlv_mem_locP _ _ _).2 ⟨1, hne1, by rw [one_smul]; exact ⟨w, hw, rfl⟩⟩
  rw [h4, rlv_mem_locP] at hPw
  obtain ⟨s, hs, hsw⟩ := hPw
  have hs' : s • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈
      Ld D u 0 (Nat.zero_le _) c := by
    rw [smul_comm]; exact natSmul_mem_of_sup _ _ hT0 z hz _ hsw
  have e1 : Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) (Ld D u 0 (Nat.zero_le _) c1) =
      clsCrd D u 0 (Nat.zero_le _) c1 := hdd c1
  have hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) ≤
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    have hg1 : cT (sigD D : D.host.E →+* D.host.E) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        gramN D 0 (Nat.zero_le _) * (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = gramN D 0 (Nat.zero_le _) := hγ
    refine rlv_dualQ (sigD D) rlv_sig_sig (gramN D 0 (Nat.zero_le _)) hH _ hg1 (T.atT.Pv v) (hfg c) (hdd c).le ?_
    rw [e1]; exact h3.ge
  have hne1Q : (1 : 𝓞 D.host.E) ∉ rlvQ T.atT v := (rlvQ T.atT v).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have hQw := hQ ((rlv_mem_locP _ _ _).2 ⟨1, hne1Q, by rw [one_smul]; exact ⟨w, hw, rfl⟩⟩)
  obtain ⟨t, ht, htw⟩ := (rlv_mem_locP _ _ _).1 hQw
  have ht' : t • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈
      Ld D u 0 (Nat.zero_le _) c := by
    rw [smul_comm]; exact Submodule.smul_mem _ _ (cls_le_ld T c htw)
  obtain ⟨a2, ha2P, ha2Q, ha2⟩ := avoid_two _ _ _ _ s t hs ht hs' ht'

  have haP : a1 * a2 ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha1P ha2P
  have haQ : a1 * a2 ∉ rlvQ T.atT v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha1Q ha2Q
  obtain ⟨r, hr, b, hb⟩ := rlv_norm T.atT v (a1 * a2) haP haQ
  have m1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
      (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈
      Ld D u 0 (Nat.zero_le _) c3 := by
    rw [hb, show b * (a1 * a2) = (b * a2) * a1 by ring, mul_smul]
    exact Submodule.smul_mem _ _ ha1
  have m2 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
      ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈ Ld D u 0 (Nat.zero_le _) c := by
    rw [hb, show b * (a1 * a2) = (b * a1) * a2 by ring, mul_smul]
    exact Submodule.smul_mem _ _ ha2
  refine ⟨r, hr, m1, ?_⟩
  have eV1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w)) =
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) := by
    rw [Matrix.mulVec_smul, smul_comm]
  have hB : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w)) ∈ Ld D u 0 (Nat.zero_le _) c := by
    rw [eV1]; exact m2
  have eV2 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) =
      ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
          ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) := by
    have eg : (γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) =
        ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
          ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [Matrix.mulVec_smul, eg, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]
  have hA : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) ∈
      Ld D u 0 (Nat.zero_le _) c2 := by
    rw [eV2]; exact memInv _ m2
  calc (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, m1⟩)
      = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hA⟩) := g5 ⟨_, m1⟩ hA
    _ = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, memInv _ m2⟩) := congrArg _ (pr_congr T v c2 ⟨_, hA⟩ ⟨_, memInv _ m2⟩ eV2)
    _ = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, m2⟩) :=
        diamond_class_function T v v' hvv k δ hδ c c2 γd κd hx _ m2 (memInv _ m2)
    _ = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hB⟩) := congrArg _ (pr_congr T v c ⟨_, m2⟩ ⟨_, hB⟩ eV1.symm)
    _ = _ := (h5 ⟨_, Submodule.smul_mem _ _ hw⟩ hB).symm

end CrossDiaZero

end
end

