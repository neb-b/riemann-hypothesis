module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfPt
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.LocalUnitaryOfMatchingZero

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfParts
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def DnMvL (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
    (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) ∧
  (∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (hx : γ.1.1 *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = g (T.lv0.prk v c ⟨_, hx⟩)) ∧
  ∀ (h : (D.mem u).C.Y 0 → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (T.val0.eY s') (T.val0.eY s) →
    (D.fm u).dnT 0 v c g h s = (((T.cls0.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

def UpMvL (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (z : ↥(Ld D u 0 (Nat.zero_le _) c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
    (T.cls0.y ((D.fm u).up 0 v c (T.lv0.pr v c z))).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
  (∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z))))
    (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
    (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩)) ∧
  ∀ (h : (D.mem u).C.Y 0 → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (T.val0.eY s') (T.val0.eY s) →
    (D.fm u).upT 0 v c (T.lv0.pr v c z) h s = (((T.cls0.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

def IsPtZ (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (y : (D.fm u).lk 0 v c) : Prop :=
  ∃ (s : 𝓞 D.host.E), s ∉ T.atT.Pv v ∧ ∃ (hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    T.lv0.prk v c ⟨_, hz⟩ = T.atT.res v s • y

def IsPt (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g)) (y : (D.fm u).lk 0 v c) : Prop :=
  ∃ z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)), T.lv0.pr v _ z = x ∧ IsPtZ T v c g γ z y

theorem dnMvL_ex (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (hg : g ≠ 0) :
    ∃ p : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ×
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      DnMvL T v c g p.1 p.2.1 p.2.2 := by
  obtain ⟨γ, η, κ, h⟩ := T.down_natural_level_zero v c g hg
  exact ⟨(γ, η, κ), h⟩

theorem upMvL_ex (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1) :
    ∃ p : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ×
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      UpMvL T v c z p.1 p.2.1 p.2.2 := by
  obtain ⟨γ, η, κ, h⟩ := T.up_natural_level_zero v c z hz
  exact ⟨(γ, η, κ), h⟩

set_option maxHeartbeats 4000000 in
theorem dnMvL_dnMvs (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {κ : T.cls0.lev.U} (h : DnMvL T v c g γ η κ) :
    (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
    ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T γ κ h := by
  obtain ⟨h1, h2, -, -, h5⟩ := h
  refine ⟨h1, h2, fun f => funext fun s => ?_⟩
  unfold natTr0
  rw [h5 f s _ ?_, Units.val_inv_eq_inv_val]
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ *
    (atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← mul_assoc]
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

set_option maxHeartbeats 4000000 in
theorem upMvL_isUp (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {z : ↥(Ld D u 0 (Nat.zero_le _) c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {κ : T.cls0.lev.U} (h : UpMvL T v c z γ η κ) : IsUpMvF T v c (T.lv0.pr v c z) η := by
  unfold IsUpMvF
  obtain ⟨h1, h2, -, -, -, h6⟩ := h
  refine ⟨γ, κ, h1, h2, ?_⟩
  intro f
  funext s
  unfold natTr0
  rw [h6 f s _ ?_, Units.val_inv_eq_inv_val]
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ *
    (atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← mul_assoc]
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

def IsPair (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (μ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (y : (D.fm u).lk 0 v c) : Prop :=
  g ≠ 0 ∧ ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), DnMvL T v c g γ η κ ∧
    ∃ (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
      (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ' : T.cls0.lev.U),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ z) = 1 ∧ UpMvL T v ((D.fm u).dn 0 v c g) z γ' μ κ' ∧
      IsPtZ T v c g γ z y

def PtEx (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ z, ∃ y, IsPtZ T v c g γ z y

def PtWd (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ x y y', IsPt T v c g γ x y → IsPt T v c g γ x y' → y = y'

def PtInj (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ x x' y, IsPt T v c g γ x y → IsPt T v c g γ x' y → x = x'

def PtSurj (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ y, ∃ x, IsPt T v c g γ x y

def ValSame (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∀ G ∈ AdFun T.cls0.lev (embT D),
    ∀ g η κ μ g' η' κ' μ' y, IsPair T v c g η κ μ y → IsPair T v c g' η' κ' μ' y →
      G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c * hcomp T η' κ' μ')

def ValTe (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∀ G ∈ AdFun T.cls0.lev (embT D),
    ∀ g η κ μ, IsPair T v c g η κ μ ((D.fm u).te 0 v c) → G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c)

def ValDia (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∃ τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ,
    ∀ G ∈ AdFun T.cls0.lev (embT D), ∀ (a : ((D.mem u).A.Fv v)ˣ) g η κ μ,
      IsPair T v c g η κ μ ((a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c) →
      ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
      ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ → G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c * δ)


set_option maxHeartbeats 8000000 in
theorem dUPt0F_of (T : Forms0 D u) (hE : PtEx T) (hW : PtWd T) (hI : PtInj T) (hS : PtSurj T)
    (vS : ValSame T) (vT : ValTe T) (vD : ValDia T) : DUPt0F T := by
  classical
  unfold DUPt0F
  intro v c
  obtain ⟨P, hP⟩ : ∃ P : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) × UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      ∀ g, g ≠ 0 → DnMvL T v c g (P g).1 (P g).2.1 (P g).2.2 :=
    ⟨fun g => if hg : g ≠ 0 then (dnMvL_ex T v c g hg).choose else 1,
      fun g hg => by simp only [dif_pos hg]; exact (dnMvL_ex T v c g hg).choose_spec⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)),
      ∀ g x, T.lv0.pr v _ (Z g x) = x.1 :=
    ⟨fun g x => (T.lv0.pr_surj v _ x.1).choose, fun g x => (T.lv0.pr_surj v _ x.1).choose_spec⟩
  have hZ1 : ∀ g x, (D.fm u).fv 0 v _ (T.lv0.pr v _ (Z g x)) = 1 := fun g x => by rw [hZ]; exact x.2
  obtain ⟨Q, hQ⟩ : ∃ Q : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) × UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      ∀ g x, UpMvL T v ((D.fm u).dn 0 v c g) (Z g x) (Q g x).1 (Q g x).2.1 (Q g x).2.2 :=
    ⟨fun g x => (upMvL_ex T v _ (Z g x) (hZ1 g x)).choose, fun g x => (upMvL_ex T v _ (Z g x) (hZ1 g x)).choose_spec⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), (D.fm u).lk 0 v c,
      ∀ g x, g ≠ 0 → IsPtZ T v c g (P g).1 (Z g x) (Y g x) :=
    ⟨fun g x => if hg : g ≠ 0 then (hE v c g hg _ _ _ (hP g hg) (Z g x)).choose else 0,
      fun g x hg => by simp only [dif_pos hg]; exact (hE v c g hg _ _ _ (hP g hg) (Z g x)).choose_spec⟩
  have key : ∀ g, g ≠ 0 → ∀ z y, IsPtZ T v c g (P g).1 z y → g y = (D.fm u).fv 0 v _ (T.lv0.pr v _ z) := by
    intro g hg z y hz0
    obtain ⟨s, hs, hz, hy⟩ := hz0
    obtain ⟨-, -, -, h4, -⟩ := hP g hg
    have hres : T.atT.res v s ≠ 0 := fun h0 => hs ((RingHom.mem_ker).2 h0)
    have hx : (P g).1.1.1 *ᵥ (s • z).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [Submodule.coe_smul, Matrix.mulVec_smul]; exact hz
    have h4' := h4 (s • z) hx
    have e : T.lv0.prk v c ⟨_, hx⟩ = T.lv0.prk v c ⟨_, hz⟩ := by
      congr 1; apply Subtype.ext; simp only [Submodule.coe_smul, Matrix.mulVec_smul]
    rw [e, hy, T.lv0.pr_smul] at h4'
    simp only [map_smul, smul_eq_mul] at h4'
    exact (mul_left_cancel₀ hres h4').symm
  have hpair : ∀ g (hg : g ≠ 0) x, IsPair T v c g (P g).2.1 (P g).2.2 (Q g x).2.1 (Y g x) :=
    fun g hg x => ⟨hg, (P g).1, hP g hg, Z g x, (Q g x).1, (Q g x).2.2, hZ1 g x, hQ g x, hY g x hg⟩
  refine ⟨fun g => (P g).1, fun g => (P g).2.1, fun g => (P g).2.2, fun g x => (Q g x).2.1, ?_, ?_, Y,
    (vD v c).choose, ?_, ?_, ?_⟩
  · intro g hg
    exact dnMvL_dnMvs T (hP g hg)
  · intro g x
    have h := upMvL_isUp T (hQ g x)
    rwa [hZ] at h
  · intro g hg x
    rw [key g hg _ _ (hY g x hg), hZ]
    exact x.2
  · intro g hg y hy
    obtain ⟨x', z', hz', hpz⟩ := hS v c g hg _ _ _ (hP g hg) y
    have hx1 : (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x' = 1 := by
      rw [← hz', ← key g hg z' y hpz, hy]
    refine ⟨⟨x', hx1⟩, ?_, ?_⟩
    · exact hW v c g hg _ _ _ (hP g hg) x' _ _ ⟨Z g ⟨x', hx1⟩, hZ g _, hY g _ hg⟩ ⟨z', hz', hpz⟩
    · intro x hx
      apply Subtype.ext
      refine hI v c g hg _ _ _ (hP g hg) x.1 x' y ⟨Z g x, hZ g x, ?_⟩ ⟨z', hz', hpz⟩
      rw [← hx]
      exact hY g x hg
  · intro G hG
    have hD : ∀ p : PD D u v c, (p.1 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) ≠ 0 := fun p h0 => by
      have h := p.1.2
      rw [h0, LinearMap.zero_apply] at h
      exact zero_ne_one h
    refine ⟨fun p hp => ?_, fun p q hpq => ?_, fun p q hpq => ?_, fun a q hq k hk δ hδ => ?_⟩
    · have h := hpair _ (hD p) p.2
      rw [hp] at h
      exact vT v c G hG _ _ _ _ h
    · have h1 := hpair _ (hD p) p.2
      have h2 := hpair _ q.1.2 q.2
      rw [← hpq] at h2
      exact vS v c G hG _ _ _ _ _ _ _ _ _ h1 h2
    · have h1 := hpair _ p.1.2 p.2
      have h2 := hpair _ q.1.2 q.2
      rw [← hpq] at h2
      exact vS v c G hG _ _ _ _ _ _ _ _ _ h1 h2
    · have h := hpair _ q.1.2 q.2
      rw [hq] at h
      exact (vD v c).choose_spec G hG a _ _ _ _ h k hk δ hδ

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TripMem
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
theorem val_of_mem (T : Forms0 D u) (v : (D.mem u).A.vT)
    (y h1 h2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hs1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h1.1 = 1)
    (hs2 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h2.1 = 1)
    (hm : h1.1⁻¹ * h2.1 ∈ T.cls0.lev.U)
    (G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ)
    (hG : G ∈ AdFun T.cls0.lev (embT D)) :
    G (y * h2) = G (y * h1) := by
  have hx : (y * h2).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (1 : GL (Fin (D.R.N 0)) D.host.E) * (y * h1).1 * (⟨h1.1⁻¹ * h2.1, hm⟩ : T.cls0.lev.U).1 := by
    simp [mul_assoc]
  have key := hG 1 (one_mem _) (y * h1) (y * h2) ⟨h1.1⁻¹ * h2.1, hm⟩ hx
  have hχ : ((T.cls0.lev.chi ⟨h1.1⁻¹ * h2.1, hm⟩ : ℂˣ) : ℂ) = 1 := by
    rw [T.cls0.lev.chi_triv ⟨h1.1⁻¹ * h2.1, hm⟩ (fun w hw => ?_)]
    · rfl
    have hne : w ≠ (T.atT.eV v).1 := fun h => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.level_places_not_bad T.atT v (h ▸ hw)
    show bc (prV (E := D.host.E) w) (h1.1⁻¹ * h2.1) = 1
    rw [map_mul, map_inv, hs1 w hne, hs2 w hne, inv_one, one_mul]
  funext s
  rw [key s s (fun τ => by simp [atInf, Matrix.map_one]), hχ, one_mul]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem trip_mem (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c3 : (D.mem u).C.cls 0)
    (Γ1 Γ3 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h1 h3 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (k1 k3 : T.cls0.lev.U)
    (hs1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h1.1 = 1)
    (hs3 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h3.1 = 1)
    (e1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * h1.1 * k1.1)
    (e3 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1 * (T.cls0.y c3).1 = (T.cls0.y c).1 * h3.1 * k3.1)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3))
    (hF : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) •
          (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
          Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    h3.1⁻¹ * h1.1 ∈ T.cls0.lev.U := by
  have hΓ : ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E)) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (inv_mem Γ3.2) Γ1.2
  have hX : (T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Γ3.1⁻¹ * Γ1.1) *
      (T.cls0.y c1).1 = k3.1⁻¹ * (h3.1⁻¹ * h1.1) * k1.1 := by
    rw [map_mul, map_inv]
    rw [show (T.cls0.y c3).1⁻¹ * ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1) * (T.cls0.y c1).1 =
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1 * (T.cls0.y c3).1)⁻¹ *
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1 * (T.cls0.y c1).1) by group, e1, e3]
    group
  have hmem := fun x => T.cls0.lev.21 x
  have H := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.local_unitary_of_matching_zero T v c3 c1 (Γ3.1⁻¹ * Γ1.1) hΓ (by
    rw [hX]
    exact mul_mem (mul_mem (inv_mem ((hmem _).1 k3.2).1) (mul_mem (inv_mem h3.2) h1.2)) ((hmem _).1 k1.2).1) hP hPd hF
  have hh : h3.1⁻¹ * h1.1 = k3.1 * ((T.cls0.y c3).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Γ3.1⁻¹ * Γ1.1) * (T.cls0.y c1).1) * k1.1⁻¹ := by
    rw [hX]; group
  refine (hmem _).2 ⟨mul_mem (inv_mem h3.2) h1.2, fun w => ?_⟩
  by_cases hw : w = (T.atT.eV v).1
  · rw [hw, hh, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (((hmem _).1 k3.2).2 _) H) (inv_mem (((hmem _).1 k1.2).2 _))
  · rw [map_mul, map_inv, hs1 w hw, hs3 w hw, inv_one, one_mul]
    exact one_mem _

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

