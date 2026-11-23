module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.SameCommon

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUPt0FOfVals
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem lp_smul_map (P : Ideal (𝓞 E)) [P.IsPrime] (A : Matrix (Fin n) (Fin n) E)
    (M N : Submodule (𝓞 E) (Fin n → E)) (h : ∀ m ∈ M, A *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ P N)
    (x : Fin n → E) (hx : x ∈ P • M) : A *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N) := by
  refine Submodule.smul_induction_on (p := fun x => A *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N)) hx
    (fun p hp m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hsm⟩ := h m hm
    refine ⟨s, hs, ?_⟩
    show s • (A *ᵥ (p • m)) ∈ P • N
    rw [Matrix.mulVec_smul, smul_comm]
    exact Submodule.smul_mem_smul hp hsm
  · show A *ᵥ (x + y) ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N)
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy

theorem inv_mv (g : GL (Fin n) E) (z : Fin n → E) :
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem res_ne (T : Forms0 D u) {v : (D.mem u).A.vT} {s : 𝓞 D.host.E} (hs : s ∉ T.atT.Pv v) :
    T.atT.res v s ≠ 0 := fun h => hs ((RingHom.mem_ker).2 h)

section Mv

variable (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
  {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
  {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
  {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}

theorem dn_fwd (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E)
    (hm : m ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) :
    γ.1.1 *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
  have h1 : γ.1.1 *ᵥ m ∈ mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) := by
    rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.mem_mul_lattice_iff γ.1, inv_mv]
    exact hm
  have h2 : γ.1.1 *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) :=
    ⟨1, (T.atT.Pv v).primeCompl.one_mem, by simpa using h1⟩
  rw [hD.2.2.1] at h2
  exact h2

theorem dn_bwd (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E)
    (hm : m ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ m ∈
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) := by
  have h1 : m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
    CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hm)
  rw [← hD.2.2.1] at h1
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 htm
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
  refine (rlv_mem_locP _ _ _).2 ⟨t, ht, ?_⟩
  rw [← Matrix.mulVec_smul, ← hxe, inv_mv]
  exact hx

end Mv

theorem ptz_sub (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    (z z' : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) {y y' : (D.fm u).lk 0 v c}
    (s s' : 𝓞 D.host.E) (hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c)
    (hz' : s' • (γ.1.1 *ᵥ z'.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c)
    (hy : T.lv0.prk v c ⟨_, hz⟩ = T.atT.res v s • y) (hy' : T.lv0.prk v c ⟨_, hz'⟩ = T.atT.res v s' • y') :
    ∃ w : ↥(Lk T.atT 0 (Nat.zero_le _) v c), w.1 = (s * s') • (γ.1.1 *ᵥ (z.1 - z'.1)) ∧
      T.lv0.prk v c w = (T.atT.res v s * T.atT.res v s') • (y - y') := by
  refine ⟨s' • ⟨_, hz⟩ - s • ⟨_, hz'⟩, ?_, ?_⟩
  · show s' • (s • (γ.1.1 *ᵥ z.1)) - s • (s' • (γ.1.1 *ᵥ z'.1)) = _
    rw [Matrix.mulVec_sub, smul_sub, smul_smul, smul_smul, mul_comm s' s]
  · rw [map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy, hy', smul_smul, smul_smul, smul_sub,
      mul_comm (T.atT.res v s') _]

theorem ptEx_holds (T : Forms0 D u) : PtEx T := by
  intro v c g _ γ η κ hD z
  obtain ⟨s, hs, hsz⟩ := (rlv_mem_locP _ _ _).1 (dn_fwd T hD z.1 z.2)
  have hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left hsz
  refine ⟨(T.atT.res v s)⁻¹ • T.lv0.prk v c ⟨_, hz⟩, s, hs, hz, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ (res_ne T hs), one_smul]

theorem ptWd_holds (T : Forms0 D u) : PtWd T := by
  rintro v c g _ γ η κ hD x y y' ⟨z, hzx, s, hs, hz, hy⟩ ⟨z', hzx', s', hs', hz', hy'⟩
  obtain ⟨w, hw, hpw⟩ := ptz_sub T z z' s s' hz hz' hy hy'
  have hd : (z - z').1 ∈ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) :=
    (T.lv0.pr_ker v _ (z - z')).1 (by rw [map_sub, hzx, hzx', sub_self])
  obtain ⟨t, ht, htd⟩ := (rlv_mem_locP _ _ _).1 (lp_smul_map _ γ.1.1 _ _ (dn_fwd T hD) _ hd)
  have h0 : T.lv0.prk v c (t • w) = 0 := by
    refine (T.lv0.prk_ker v c _).2 ?_
    show t • w.1 ∈ _
    rw [hw, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mono le_rfl le_sup_left htd)
  rw [T.lv0.prk_smul, hpw, smul_smul] at h0
  have hne : T.atT.res v t * (T.atT.res v s * T.atT.res v s') ≠ 0 :=
    mul_ne_zero (res_ne T ht) (mul_ne_zero (res_ne T hs) (res_ne T hs'))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hne)

theorem ptInj_holds (T : Forms0 D u) : PtInj T := by
  rintro v c g _ γ η κ hD x x' y ⟨z, hzx, s, hs, hz, hy⟩ ⟨z', hzx', s', hs', hz', hy'⟩
  obtain ⟨w, hw, hpw⟩ := ptz_sub T z z' s s' hz hz' hy hy'
  rw [sub_self, smul_zero] at hpw
  have hwP : w.1 ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := (T.lv0.prk_ker v c w).1 hpw
  have hb := lp_smul_map _ ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    _ _ (dn_bwd T hD) _ hwP
  rw [hw, ← Matrix.mulVec_smul, inv_mv] at hb
  obtain ⟨t, ht, htd⟩ := (rlv_mem_locP _ _ _).1 hb
  have h0 : T.lv0.pr v _ ((t * (s * s')) • (z - z')) = 0 := by
    refine (T.lv0.pr_ker v _ _).2 ?_
    show (t * (s * s')) • (z.1 - z'.1) ∈ _
    rw [mul_smul]
    exact htd
  rw [T.lv0.pr_smul, map_sub, hzx, hzx'] at h0
  have hne : T.atT.res v (t * (s * s')) ≠ 0 := by
    rw [map_mul, map_mul]
    exact mul_ne_zero (res_ne T ht) (mul_ne_zero (res_ne T hs) (res_ne T hs'))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hne)

theorem dn_img (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}
    (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E) (hm : m ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    ∃ t : 𝓞 D.host.E, t ∉ T.atT.Pv v ∧
      ∃ x ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g), γ.1.1 *ᵥ x = t • m := by
  have h1 : m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
    CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hm)
  rw [← hD.2.2.1] at h1
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 htm
  exact ⟨t, ht, x, hx, hxe⟩

theorem one_nmem (T : Forms0 D u) {v : (D.mem u).A.vT} : (1 : 𝓞 D.host.E) ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)

set_option maxHeartbeats 1000000 in
theorem ptSurj_holds (T : Forms0 D u) : PtSurj T := by
  intro v c g _ γ η κ hD y
  obtain ⟨w0, hw0⟩ := T.lv0.prk_surj v c y
  obtain ⟨t, ht, x, hx, hxe⟩ := dn_img T hD w0.1 w0.2
  obtain ⟨r, hr⟩ := T.atT.res_surj v (T.atT.res v t)⁻¹
  have htne := res_ne T ht
  have hrx : r • x ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) := Submodule.smul_mem _ r hx
  have hz1 : (1 : 𝓞 D.host.E) • (γ.1.1 *ᵥ (r • x)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul, Matrix.mulVec_smul, hxe, smul_smul]
    exact Submodule.smul_mem _ _ w0.2
  refine ⟨T.lv0.pr v _ ⟨r • x, hrx⟩, ⟨r • x, hrx⟩, rfl, 1, one_nmem T, hz1, ?_⟩
  have e : (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = (r * t) • w0 := by
    apply Subtype.ext
    show (1 : 𝓞 D.host.E) • (γ.1.1 *ᵥ (r • x)) = (r * t) • w0.1
    rw [one_smul, Matrix.mulVec_smul, hxe, smul_smul]
  rw [e, T.lv0.prk_smul, map_mul, hr, inv_mul_cancel₀ htne, one_smul, map_one, one_smul, hw0]

theorem dUPt0F_of_vals (T : Forms0 D u) (vS : ValSame T) (vT : ValTe T) (vD : ValDia T) : DUPt0F T :=
  dUPt0F_of T (ptEx_holds T) (ptWd_holds T) (ptInj_holds T) (ptSurj_holds T) vS vT vD

theorem dUAll_of_vals (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), ValSame T ∧ ValTe T ∧ ValDia T) :
    Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll := dUAll_of fun D u T =>
  duFib_of_pt T (dUPt0F_of_vals T (h D u T).1 (h D u T).2.1 (h D u T).2.2)

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.MulLatSupSpan
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

theorem localization_sup_congr {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P : Ideal R) [P.IsPrime]
    {X Y : Submodule R W} (S : Submodule R W) (h : Formalism.HermitianLatticesTheory.localization₂ P X = Formalism.HermitianLatticesTheory.localization₂ P Y) :
    Formalism.HermitianLatticesTheory.localization₂ P (X ⊔ S) = Formalism.HermitianLatticesTheory.localization₂ P (Y ⊔ S) := by
  have key : ∀ {X Y : Submodule R W}, Formalism.HermitianLatticesTheory.localization₂ P X = Formalism.HermitianLatticesTheory.localization₂ P Y →
      Formalism.HermitianLatticesTheory.localization₂ P (X ⊔ S) ≤ Formalism.HermitianLatticesTheory.localization₂ P (Y ⊔ S) := by
    intro X Y h x hx
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsx
    have ha0 : a ∈ Formalism.HermitianLatticesTheory.localization₂ P X := ⟨1, P.primeCompl.one_mem, by simpa using ha⟩
    rw [h] at ha0
    obtain ⟨t, ht, hta⟩ := ha0
    refine ⟨t * s, P.primeCompl.mul_mem ht hs, ?_⟩
    rw [mul_smul, ← hab, smul_add]
    exact Submodule.add_mem_sup hta (S.smul_mem t hb)
  exact le_antisymm (key h) (key h.symm)

theorem mulLat_sup_span {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    mulLat g (L ⊔ Submodule.span (𝓞 E) {y}) = mulLat g L ⊔ Submodule.span (𝓞 E) {g *ᵥ y} := by
  unfold mulLat
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  rfl

variable {D : D7} {u : D.what₂.Word}

def IsCompMv (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (Γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (k : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * h.1 * k.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat Γ.1.1 (clsCrd D u 0 (Nat.zero_le _) c1)) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat Γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w}) ∧
  ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1))
    (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ.1.1 *ᵥ x.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩)


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem comp_of_moves (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (d1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (d2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (d3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (d4 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η' : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : T.cls0.lev.U)
    (u1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1)
    (u2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
      (T.cls0.y ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z))).1 =
        (T.cls0.y ((D.fm u).dn 0 v c g)).1 * η'.1 * κ'.1)
    (u3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ'.1.1 (clsCrd D u 0 (Nat.zero_le _)
        ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (u4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ'.1.1 (Ld D u 0 (Nat.zero_le _)
        ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}))
    (u5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z))))
      (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = (D.fm u).fv 0 v _ (T.lv0.pr v _ ⟨_, hx⟩)) :
    IsCompMv T v c ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)) (γ.1.1 *ᵥ z.1) g (γ * γ')
      (hcomp T η κ η') (κ * κ') := by
  have eM : ((γ * γ').1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = γ.1.1 * γ'.1.1 := by
    simp only [Subgroup.coe_mul, Units.val_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v' hv'
    simp only [hcomp, kU, Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, d1 v' hv', u1 v' hv', one_mul, mul_one,
      mul_inv_cancel]
  · simp only [hcomp, kU, Subgroup.coe_mul, InvMemClass.coe_inv, map_mul]
    rw [mul_assoc, u2, ← mul_assoc, ← mul_assoc, d2]
    group
  · rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ d3 u3
  · rw [eM]
    refine rlv_chainP (T.atT.Pv v) _ _ ?_ u4
    rw [mulLat_sup_span, Matrix.mulVec_smul]
    exact localization_sup_congr _ _ d3
  · intro x hx
    have hmem : γ'.1.1 *ᵥ x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) := by
      rw [← u4]; exact mem_localization_of_mem₂ _ ⟨x.1, x.2, rfl⟩
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hmem
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 htx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have hTE : ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by simp
    have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast (D.mem u).A.T_prime.ne_zero

    have e1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • a + r • z.1 := by
      have : (t • x).1 = t • x.1 := rfl
      rw [this, Matrix.mulVec_smul, ← e, smul_add]
      congr 1
      rw [smul_comm, ← algebraMap_smul D.host.E (((D.mem u).A.T : ℕ) : 𝓞 D.host.E), ← algebraMap_smul D.host.E r,
        ← algebraMap_smul D.host.E r, smul_smul, smul_smul]
      congr 1
      simp only [map_natCast]
      field_simp
    have hin : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) := by
      rw [e1]
      exact add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ z.2)
    have e2 : γ.1.1 *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1)) =
        t • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ * γ').1.1 *ᵥ x.1)) := by
      have : (t • x).1 = t • x.1 := rfl
      rw [this, eM, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm]
    have hin2 : γ.1.1 *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [e2]; exact Submodule.smul_mem _ _ hx
    have f1 := u5 (t • x) hin
    have f2 := d4 ⟨_, hin⟩ hin2
    have p1 : T.lv0.prk v c ⟨_, hin2⟩ = T.atT.res v t • T.lv0.prk v c ⟨_, hx⟩ := by
      rw [← T.lv0.prk_smul]
      exact congrArg _ (Subtype.ext e2)
    rw [T.lv0.pr_smul, map_smul, f2, p1, map_smul] at f1
    have hres : T.atT.res v t ≠ 0 := fun h0 => ht (RingHom.mem_ker.2 h0)
    exact smul_right_injective _ hres f1

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

