module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DualSigmaApply
section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

def dualSigma {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (φ : W ≃ₗ[K] V) (tv : V) (tw : W) (h : φ tw = tv) :
    {x : Module.Dual K V // x tv = 1} ≃ {y : Module.Dual K W // y tw = 1} where
  toFun x := ⟨x.1 ∘ₗ φ.toLinearMap, by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h]; exact x.2⟩
  invFun y := ⟨y.1 ∘ₗ φ.symm.toLinearMap, by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← h, LinearEquiv.symm_apply_apply]; exact y.2⟩
  left_inv x := Subtype.ext (LinearMap.ext fun w => by simp)
  right_inv y := Subtype.ext (LinearMap.ext fun w => by simp)

theorem dualSigma_apply {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (φ : W ≃ₗ[K] V) (tv : V) (tw : W) (h : φ tw = tv) (x : {x : Module.Dual K V // x tv = 1}) (w : W) :
    (dualSigma φ tv tw h x).1 w = x.1 (φ w) := rfl

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 2000000 in
theorem dni_lk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c') :
    mulLat g (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c' := by
  show mulLat g (clsCrd D u 0 (Nat.zero_le _) c ⊔ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c) =
    clsCrd D u 0 (Nat.zero_le _) c' ⊔ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c'
  unfold mulLat at hL hLd ⊢
  rw [Submodule.map_sup, Submodule.map_smul'', hL, hLd]

theorem dni_mem_of {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : mulLat g M = M') {z : Fin n → E} (hz : z ∈ M) : g *ᵥ z ∈ M' := by
  rw [← h]
  exact Submodule.mem_map_of_mem hz

set_option maxHeartbeats 2000000 in
theorem dni_mem (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    {z : Fin (D.R.N 0) → D.host.E} (hz : z ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    g *ᵥ z ∈ Lk T.atT 0 (Nat.zero_le _) v c' :=
  dni_mem_of g (dni_lk T v c c' g hL hLd) hz

set_option maxHeartbeats 2000000 in
theorem dni_mem_ker (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    {z : Fin (D.R.N 0) → D.host.E} (hz : z ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c) :
    g *ᵥ z ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c' := by
  have h := dni_lk T v c c' g hL hLd
  have h2 : mulLat g (T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c) =
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c' := by
    unfold mulLat at h ⊢
    rw [Submodule.map_smul'', h]
  exact dni_mem_of g h2 hz

def dniFun (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (w : (D.fm u).lk 0 v c) : (D.fm u).lk 0 v c' :=
  T.lv0.prk v c' ⟨g *ᵥ (Function.surjInv (T.lv0.prk_surj v c) w).1,
    dni_mem T v c c' g hL hLd (Function.surjInv (T.lv0.prk_surj v c) w).2⟩

set_option maxHeartbeats 2000000 in
theorem dniFun_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniFun T v c c' g hL hLd (T.lv0.prk v c z) = T.lv0.prk v c' ⟨g *ᵥ z.1, dni_mem T v c c' g hL hLd z.2⟩ := by
  have hs := Function.surjInv_eq (T.lv0.prk_surj v c) (T.lv0.prk v c z)
  have hd : (Function.surjInv (T.lv0.prk_surj v c) (T.lv0.prk v c z) - z).1 ∈
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [← T.lv0.prk_ker, map_sub, hs, sub_self]
  have hg := dni_mem_ker T v c c' g hL hLd hd
  unfold dniFun
  rw [← sub_eq_zero, ← map_sub, T.lv0.prk_ker]
  simpa [Matrix.mulVec_sub] using hg


set_option maxHeartbeats 2000000 in
def dniLin (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c') :
    (D.fm u).lk 0 v c →ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c' where
  toFun := dniFun T v c c' g hL hLd
  map_add' w1 w2 := by
    obtain ⟨z1, rfl⟩ := T.lv0.prk_surj v c w1
    obtain ⟨z2, rfl⟩ := T.lv0.prk_surj v c w2
    rw [← map_add (f := _), dniFun_prk, dniFun_prk, dniFun_prk, ← map_add (f := _)]
    congr 1
    apply Subtype.ext
    show g *ᵥ (z1.1 + z2.1) = g *ᵥ z1.1 + g *ᵥ z2.1
    exact Matrix.mulVec_add _ _ _
  map_smul' r w := by
    obtain ⟨a, rfl⟩ := T.atT.res_surj v r
    obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
    rw [RingHom.id_apply, ← T.lv0.prk_smul, dniFun_prk, dniFun_prk, ← T.lv0.prk_smul]
    congr 1
    apply Subtype.ext
    show g *ᵥ (a • z.1) = a • (g *ᵥ z.1)
    exact Matrix.mulVec_smul _ _ _

theorem dniLin_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniLin T v c c' g hL hLd (T.lv0.prk v c z) = T.lv0.prk v c' ⟨g *ᵥ z.1, dni_mem T v c c' g hL hLd z.2⟩ :=
  dniFun_prk T v c c' g hL hLd z

theorem dni_inv_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (g : GL (Fin n) E)
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : mulLat (g : Matrix (Fin n) (Fin n) E) M = M') :
    mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) M' = M := by
  have hid : ((Matrix.mulVecLin ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)).comp
      ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      LinearMap.id_apply]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← h]
  unfold mulLat
  rw [← Submodule.map_comp, hid, Submodule.map_id]


set_option maxHeartbeats 2000000 in
def dniEquiv (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c') :
    (D.fm u).lk 0 v c ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c' :=
  LinearEquiv.ofLinear (dniLin T v c c' _ hL hLd) (dniLin T v c' c _ (dni_inv_eq g hL) (dni_inv_eq g hLd))
    (LinearMap.ext fun w => by
      obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c' w
      rw [LinearMap.comp_apply, dniLin_prk, dniLin_prk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        (((g⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])
    (LinearMap.ext fun w => by
      obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
      rw [LinearMap.comp_apply, dniLin_prk, dniLin_prk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      show ((g⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        ((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec])

theorem dniEquiv_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniEquiv T v c c' g hL hLd (T.lv0.prk v c z) =
      T.lv0.prk v c' ⟨(g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1, dni_mem T v c c' _ hL hLd z.2⟩ :=
  dniLin_prk T v c c' _ hL hLd z


set_option maxHeartbeats 2000000 in
theorem dniEquiv_te (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1)
    (hgz : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) c')
    (hz' : (D.fm u).fv 0 v c' (T.lv0.pr v c' ⟨_, hgz⟩) = 1) :
    dniEquiv T v c c' g hL hLd ((D.fm u).te 0 v c) = (D.fm u).te 0 v c' := by
  have e1 := T.lv0.te v c z hz
    (Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u T.atT v) z.2))
  have e2 := T.lv0.te v c' ⟨_, hgz⟩ hz'
    (Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u T.atT v) hgz))
  rw [← e1, ← e2, dniEquiv_prk]
  congr 1
  apply Subtype.ext
  simp only [Matrix.mulVec_smul]

theorem dni_exists_one (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    ∃ z : ↥(Ld D u 0 (Nat.zero_le _) c), (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, (D.fm u).fv 0 v c w ≠ 0 := by
    by_contra h
    push_neg at h
    exact (D.fm u).fv_ne 0 v c (LinearMap.ext h)
  obtain ⟨z, hz⟩ := T.lv0.pr_surj v c (((D.fm u).fv 0 v c w)⁻¹ • w)
  refine ⟨z, ?_⟩
  rw [hz, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

end CrossDiaZero

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.UpMatch
section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upMatch (T : Forms0 D u) : UpDiaMatch0F T := by
  intro v v' hvv a k hk δ hδ c γd hγd κd hx
  set c2 := (D.fm u).dil 0 v' a c with hc2
  have hLat := diamond_lattice_transport T v' k δ hδ c c2 γd hγd κd hx
  have hInv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c2 := by
    rw [← hLat.2, rlv_mulLat_inv]
  have memInv : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c, ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈ Ld D u 0 (Nat.zero_le _) c2 := by
    intro y hy
    rw [← hLat.2, mem_mul_lattice_iff] at hy
    exact hy
  have memFwd : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c2, (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈ Ld D u 0 (Nat.zero_le _) c := by
    intro y hy
    rw [← hLat.2]
    exact ⟨y, hy, rfl⟩
  have eInvFwd : ∀ y : Fin (D.R.N 0) → D.host.E, ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have eFwdInv : ∀ y : Fin (D.R.N 0) → D.host.E, (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun h => hvv (T.atT.eV.injective (Subtype.ext h))
  have hδv : bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 = 1 := hδ.1 _ hne
  have h3d : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1 := hx

  choose zf hzf using fun x : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} => T.lv0.pr_surj v c x.1
  have hz1 : ∀ x, (D.fm u).fv 0 v c (T.lv0.pr v c (zf x)) = 1 := fun x => by rw [hzf x]; exact x.2
  choose γ η κ h1 h2 h3 h4 h5 h6 using fun x => T.up_natural_level_zero v c (zf x) (hz1 x)

  let z2 : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} → ↥(Ld D u 0 (Nat.zero_le _) c2) :=
    fun x => ⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1, memInv _ (zf x).2⟩
  have hz2 : ∀ x, (D.fm u).fv 0 v c2 (T.lv0.pr v c2 (z2 x)) = 1 := fun x =>
    (diamond_class_function T v v' hvv k δ hδ c c2 γd κd hx (zf x).1 (zf x).2 (memInv _ (zf x).2)).trans (hz1 x)
  choose γ2 η2 κ2 g1 g2 g3 g4 g5 g6 using fun x => T.up_natural_level_zero v c2 (z2 x) (hz2 x)

  choose zl hzl using fun y : {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} => T.lv0.pr_surj v c2 y.1
  have hinvf : ∀ y, (D.fm u).fv 0 v c (T.lv0.pr v c ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩) = 1 := by
    intro y
    have hm : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1) ∈ Ld D u 0 (Nat.zero_le _) c2 := by
      rw [eInvFwd]; exact (zl y).2
    rw [← diamond_class_function T v v' hvv k δ hδ c c2 γd κd hx _ (memFwd _ (zl y).2) hm,
      pr_congr T v c2 ⟨_, hm⟩ (zl y) (eInvFwd _), hzl y]
    exact y.2
  let σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
      {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} :=
    { toFun := fun x => ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩
      invFun := fun y => ⟨T.lv0.pr v c ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩, hinvf y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hzz : T.lv0.pr v c2 (zl ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩) = T.lv0.pr v c2 (z2 x) := hzl _
        have hm : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (z2 x).1 ∈ Ld D u 0 (Nat.zero_le _) c := by
          show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1) ∈ _
          rw [eFwdInv]; exact (zf x).2
        exact (pr_tr T v c2 c (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) hLat.2 _ (z2 x) hzz (memFwd _ (zl _).2) hm).trans
          ((pr_congr T v c ⟨_, hm⟩ (zf x) (eFwdInv _)).trans (hzf x))
      right_inv := by
        intro y
        apply Subtype.ext
        have hzz := hzf ⟨T.lv0.pr v c ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩, hinvf y⟩
        have hm : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1) ∈ Ld D u 0 (Nat.zero_le _) c2 := by
          rw [eInvFwd]; exact (zl y).2
        exact (pr_tr T v c c2 _ hInv _ ⟨_, memFwd _ (zl y).2⟩ hzz (memInv _ (zf _).2) hm).trans
          ((pr_congr T v c2 ⟨_, hm⟩ (zl y) (eInvFwd _)).trans (hzl y)) }
  refine ⟨σ, η, fun y => η2 (σ.symm y), ?_, ?_, ?_⟩
  · intro x
    have hmv : IsUpMvF T v c (T.lv0.pr v c (zf x)) (η x) :=
      ⟨γ x, κ x, h1 x, h2 x, fun h => by
        funext s
        rw [h6 x h s _ (is_translate_inverse T (γ x) s), Units.val_inv_eq_inv_val]
        rfl⟩
    rw [hzf x] at hmv
    exact hmv
  · intro y
    have hmv : IsUpMvF T v c2 (T.lv0.pr v c2 (z2 (σ.symm y))) (η2 (σ.symm y)) :=
      ⟨γ2 _, κ2 _, g1 _, g2 _, fun h => by
        funext s
        rw [g6 _ h s _ (is_translate_inverse T (γ2 _) s), Units.val_inv_eq_inv_val]
        rfl⟩
    have e : T.lv0.pr v c2 (z2 (σ.symm y)) = y.1 := congrArg Subtype.val (σ.apply_symm_apply y)
    rw [e] at hmv
    exact hmv
  · intro x
    show (η2 (σ.symm (σ x))).1⁻¹ * κd.1 * (η x).1 ∈ T.cls0.lev.U
    rw [σ.symm_apply_apply]
    have hΓU : ((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) ∈
        UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
      mul_mem (mul_mem (inv_mem (γ2 x).2) (inv_mem hγd)) (γ x).2
    have eΓ : (((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
        (((γ2 x).1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) * ((γ x).1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) := by
      rw [Units.val_mul, Units.val_mul, mul_assoc]

    have stepB : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c)) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2) := by rw [hInv]
    have ch1 := rlv_chainP (T.atT.Pv v) ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) ((γ x).1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) stepB (h3 x)
    have ch2 := rlv_chainP (T.atT.Pv v) (((γ2 x).1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) _ (use₄ (T.atT.Pv v) (γ2 x).1 (g3 x)) ch1
    have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c (zf x))))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c2 (T.lv0.pr v c2 (z2 x)))) := by
      rw [eΓ]; exact ch2

    have eG : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1}) =
        Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (z2 x).1} := by
      rw [show mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1}) =
          mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) ⊔
            mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1}) from
          Submodule.map_sup _ _ _, hInv]
      congr 1
      unfold mulLat
      rw [Submodule.map_span, Set.image_singleton]
      congr 2
      show ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1) = (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1)
      rw [Matrix.mulVec_smul]
    have stepB' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1})) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (z2 x).1}) := by rw [eG]
    have ch1' := rlv_chainP (T.atT.Pv v) ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) ((γ x).1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) stepB' (h4 x)
    have ch2' := rlv_chainP (T.atT.Pv v) (((γ2 x).1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) _ (use₄ (T.atT.Pv v) (γ2 x).1 (g4 x)) ch1'
    have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c (zf x))))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c2 (T.lv0.pr v c2 (z2 x)))) := by
      rw [eΓ]; exact ch2'
    have hF := upF T v v' hvv k δ hδ c _ c2 _ γd hγd κd hx (γ x).1 (γ2 x).1 (γ x).2 (γ2 x).2 (zf x).1 (zf x).2
      (h3 x) (h4 x) (h5 x) (g5 x) hP hPd
    have hU := matching_unitary_eq T.cls0 c _ c2 _ (γ x).1 (γ2 x).1 γd (η x) (η2 x) δ (κ x) (κ2 x) κd (h2 x) (g2 x) h3d
    exact matching_move_mem_level_zero T v c _ c2 _ (γ x).1 (γ2 x).1 γd (η x) (η2 x) δ (κ x) (κ2 x) κd (h1 x) (g1 x) hδv
      (h2 x) (g2 x) h3d (local_unitary_of_matching_zero T v _ _ _ hΓU hU hP hPd hF)

end CrossDiaZero

end
end

