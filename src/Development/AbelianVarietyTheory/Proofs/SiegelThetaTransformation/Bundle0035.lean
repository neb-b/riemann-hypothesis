module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_ex_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (ptO Xo x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧
      (∀ z, ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, ex (fun j => ty j (a : E) * z j) = ex z ≫ Xo.univ.t.act.act a) ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo x0 a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  refine ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, F.ex_onto i P hP, F.ex_ker i P hP, F.ex_lin i P hP, ?_⟩
  intro a ha
  exact F.ex_eta i P hP a ha


set_option maxHeartbeats 1000000 in
theorem uw_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hS hpv hrow x hxu
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Pm, hPm, hPer, hux, hder, hfr⟩ := W.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, hHm, -, hIm, hfrhol, hfrne, hfrg, hfr0, hfrper, hread, hFd, hmean⟩ := hfr hxu
  obtain ⟨ex, hexl, hadd, honto, hker, hlin, hmark⟩ :=
    exists_ex_transport W.F (W.ik k) Pm hPer (U.un k x).x hux

  have hPv : ∀ a, Pm a = pv (U.X k) idx x.1 (W.φ k a : Fin r → E) := fun a => funext fun j => by
    rw [hPm, hpv]
  have hφs : ∀ u ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = u := fun u hu =>
    ⟨(W.φ k).symm ⟨u, hu⟩, by simp⟩
  have hembφ : ∀ a, W.emb k a = (W.φ k a : Fin r → E) := fun a => rfl
  have hrange : ∀ z, z ∈ Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := by
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, SetLike.coe_mem _, hPv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hPv a⟩
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := _root_.GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr W k
  have hrng : Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [hembφ]
      exact SetLike.coe_mem _
    · intro hv
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hembφ a⟩
  obtain ⟨-, -, -, -, hsm, -, hL, -⟩ := hx_laws E r (U.X k) W.g bas idx 0 hS ⟨0, rfl⟩ x.1 x.2

  have him : ∀ u ∈ (U.X k).Λ, ∀ v ∈ (U.X k).Λ,
      (hermForm Hm (pv (U.X k) idx x.1 u) (pv (U.X k) idx x.1 v)).im = (EF (U.X k) u v : ℝ) := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hφs u hu
    obtain ⟨b, rfl⟩ := hφs v hv
    rw [← hPv, ← hPv, hIm, ← hembφ, ← hembφ, ← hEF a b]
    norm_cast
  have hH : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w :=
    (hL (U.X k).Λ (hrng ▸ hspan)).2 Hm hHm him
  have hfun : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm z).left := funext hexl
  refine ⟨{ ex := ex
            ex_add := hadd
            ex_onto := honto
            ex_ker := fun z => (hker z).trans (hrange z)
            ex_lin := fun a z => by
              have e : (fun j => rowType (U.X k) (idx j) (a : E) * z j) =
                  fun j => relab c σ (W.e j).1 (a : E) * z j := funext fun j => by rw [hrow]
              rw [e]
              exact hlin a z
            hol := by
              intro V f
              simp only [Set.sep_univ, hexl]
              exact ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm hPer V f
            der := fun ℓ => by
              rw [hfun]
              exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hexl]; exact hfrhol j
            fr_ne := fun j z => by simp only [hexl]; exact hfrne j z
            fr_g := fun j j' z => by simp only [hexl]; exact hfrg j j' z
            fr_0 := fun j => by simp only [hexl]; exact hfr0 j
            χ := fun v => if ‖χl (pv (U.X k) idx x.1 v)‖ = 1 then χl (pv (U.X k) idx x.1 v) else 1
            χ_norm := fun v _ => by
              try dsimp only
              split_ifs with h
              · exact h
              · simp
            fr_per := fun v hv j z hz => by
              obtain ⟨a, rfl⟩ := hφs v hv
              obtain ⟨hn, hp⟩ := hfrper a j z
              try dsimp only
              rw [← hPv, if_pos hn, ← hH, ← hH]
              exact hp (by simpa only [hexl] using hz) }, ?_, θ, ?_, ?_⟩
  · intro a ha
    have hM : pv (U.X k) idx x.1 (((l.M : E)⁻¹) • W.mark k a) = (l.M : ℂ)⁻¹ • Pm (W.F.t (W.ik k) a) := by
      funext j
      simp only [hsm, hrow, hPv, Pi.smul_apply, smul_eq_mul, map_inv₀, map_natCast]
      rfl
    exact (hmark a ha).trans (congrArg ex hM.symm)
  · intro j z pt h1 h2 h3
    rw [zpow_one]
    exact hread j z pt (h1.trans (hexl z)) h2 (by simpa only [hexl] using h3)
  · refine ⟨Pm.range, Fd, hrange, hFd, ?_⟩
    simpa only [hH] using hmean

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section Cast

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}

theorem SameSp.dmin_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (castFr h.psi x) τ i = dmin X'.Gm x ⟨τ.1, h.psi.ge τ.2⟩ i := by
  rw [← h.gm]
  rfl

theorem SameSp.castFr_mem_dom (h : SameSp X' X) {x : Frame X'.Ψ r} (hx : x ∈ X'.dom) :
    castFr h.psi x ∈ X.dom := by
  have hx' : ∀ τ : X'.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X'.p0 i * (dmin X'.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (castFr h.psi x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (castFr h.psi x) τ i).re
  intro τ
  obtain ⟨hdet, hpos⟩ := hx' ⟨τ.1, h.psi.ge τ.2⟩
  refine ⟨hdet, fun i => ?_⟩
  rw [h.dmin_castFr, ← h.p0]
  exact hpos i

theorem SameSp.EF_eq (h : SameSp X' X) (u v : Fin r → E) : EF X' u v = EF X u v := by
  rw [EF_def, EF_def, h.gm, h.ka]

private theorem GL_inv_mulVec_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    ((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((ga : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem GL_mulVec_inv_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    (ga : Matrix (Fin n) (Fin n) K) *ᵥ (((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem mem_mapL_iff (ga : GL (Fin r) E) (L : Lt E r) (v : Fin r → E) :
    v ∈ mapL ga L ↔ ∃ u ∈ L, v = (ga : Matrix (Fin r) (Fin r) E) *ᵥ u := by
  unfold mapL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩

private theorem EF_mulVec_of_isUn {Y : Data E r} {ga : GL (Fin r) E} (hga : IsUn Y ga) (u v : Fin r → E) :
    EF Y ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF Y u v := by
  rw [EF_def, EF_def, hga u v]

end Cast

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X' X : Data E r) (h : SameSp X' X) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X'.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X' bas' idx' e x L y) (ga : GL (Fin r) E), IsSympl X' bas' → IsSympl X bas → x ∈ X'.dom → SelfD X' L → IsUn X ga → (∀ v, pv X' idx' x v = pv X idx (castFr h.psi x) v) → (∀ j, rowType X' (idx' j) = rowType X (idx j)) → lact ga (castFr h.psi x) ∈ X.dom ∧ (IsUnitFr X' x → IsUnitFr X (lact ga (castFr h.psi x))) ∧ SelfD X (mapL ga L) ∧ ∃ A' : AnFib X bas idx e (lact ga (castFr h.psi x)) (mapL ga L) y, (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y.s θ) ∧ (∀ θ, MeanOne X' bas' idx' x L θ → MeanOne X bas idx (lact ga (castFr h.psi x)) (mapL ga L) θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mvMap ga mk) := by
  intro E _ _ _ H Dw l Xo c _ r g X' X h bas' idx' bas idx e x L y A ga hs' hs hxm hL hga hpv hrow
  have hx₀ : castFr h.psi x ∈ X.dom := h.castFr_mem_dom hxm
  obtain ⟨-, -, L3, -, -, -, -, L8⟩ := hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ _ hx₀
  obtain ⟨-, -, L3', -, -, -, -, -⟩ := hx_laws E r X' g bas' idx' 0 hs' ⟨0, rfl⟩ x hxm
  obtain ⟨hdom1, hpv1, hunit1, hhx1⟩ := L8 ga hga
  have pvT : ∀ u, pv X idx (lact ga (castFr h.psi x)) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) =
      pv X' idx' x u := fun u => (hpv1 u).trans (hpv u).symm
  have hxeq : ∀ z w, hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x z w := by
    intro z w
    rw [hx_eq_hermForm idx, hx_eq_hermForm idx']
    have key := hermForm_eq_of_im (ThFr.Hm X bas idx (castFr h.psi x)) (ThFr.Hm X' bas' idx' x) 1 1
      (Set.range (pv X idx (castFr h.psi x))) (span_range_pv idx hs hx₀) ?_ z w
    · simpa only [_root_.one_mul] using key
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [_root_.one_mul]
      rw [← hx_eq_hermForm idx, ← hx_eq_hermForm idx', L3 a b, ← hpv a, ← hpv b, L3' a b, h.EF_eq]
  have hxT : ∀ z w, hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x z w :=
    fun z w => (hhx1 z w).trans (hxeq z w)
  have unit0 : IsUnitFr X' x → IsUnitFr X (castFr h.psi x) := by
    unfold IsUnitFr
    intro hu τ i
    rw [h.dmin_castFr]
    exact hu _ i
  have hSD : SelfD X (mapL ga L) := by
    unfold SelfD at hL ⊢
    obtain ⟨hfg, hmem⟩ := hL
    refine ⟨hfg.map _, fun v => ?_⟩
    rw [mem_mapL_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩ w hw
      obtain ⟨u', hu', rfl⟩ := (mem_mapL_iff ga L w).1 hw
      obtain ⟨k, hk⟩ := (hmem u).1 hu u' hu'
      exact ⟨k, by rw [EF_mulVec_of_isUn hga, ← h.EF_eq]; exact hk⟩
    · intro hv
      refine ⟨((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, ?_, (GL_mulVec_inv_mulVec ga v).symm⟩
      rw [hmem]
      intro u' hu'
      obtain ⟨k, hk⟩ := hv _ ((mem_mapL_iff ga L _).2 ⟨u', hu', rfl⟩)
      refine ⟨k, ?_⟩
      rw [h.EF_eq, ← EF_mulVec_of_isUn hga (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) u',
        GL_mulVec_inv_mulVec]
      exact hk
  have hT : ∀ z, (∃ v ∈ L, z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (mem_mapL_iff ga L _).2 ⟨u, hu, rfl⟩, (pvT u).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
      exact ⟨u, hu, pvT u⟩
  refine ⟨hdom1, fun hu => hunit1 (unit0 hu), hSD, ?_⟩
  have hlin : ∀ (a : 𝓞 E) (z : Fin g → ℂ),
      A.ex (fun j => rowType X (idx j) (a : E) * z j) = A.ex z ≫ Xo.univ.t.act.act a := by
    intro a z
    have hfun : (fun j => rowType X (idx j) (a : E) * z j) =
        (fun j => rowType X' (idx' j) (a : E) * z j) := funext fun j => by rw [hrow]
    rw [hfun]
    exact A.ex_lin a z
  have hnorm : ∀ v ∈ mapL ga L, ‖A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)‖ = 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    rw [GL_inv_mulVec_mulVec]
    exact A.χ_norm u hu
  refine ⟨
    { ex := A.ex
      ex_add := A.ex_add
      ex_onto := A.ex_onto
      ex_ker := fun z => (A.ex_ker z).trans (hT z)
      ex_lin := hlin
      hol := A.hol
      der := A.der
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ := fun v => A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      χ_norm := hnorm
      fr_per := ?_ }, fun θ hθ => hθ, ?_, ?_⟩
  · intro v hv j z hz
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    simp only [GL_inv_mulVec_mulVec, pvT, hxT]
    exact A.fr_per u hu j z hz
  · intro θ hθ
    unfold MeanOne at hθ ⊢
    obtain ⟨Ag, Fd, hA, hFd, hint⟩ := hθ
    refine ⟨Ag, Fd, fun z => (hA z).trans (hT z), hFd, ?_⟩
    simp only [hxT]
    exact hint
  · intro mk hmk
    unfold AnFib.Marked at hmk ⊢
    intro a ha
    rw [hmk a ha]
    show A.ex _ = A.ex _
    congr 1
    have hmv : mvMap ga mk a = (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk a := by
      simp [mvMap, Matrix.toLin'_apply]
    rw [hmv, ← Matrix.mulVec_smul, pvT]

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem AnFib.exists_anPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  obtain ⟨-, -, -, hadj, -, hinj, hsp, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let lat : AddSubgroup (Fin g → ℂ) :=
    { carrier := {z | ∃ v ∈ L, z = pv X idx x v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, add_mem hu hv, by rw [pv, pv, pv, per_add]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by rw [pv, per_zero]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨-u, neg_mem hu, by rw [pv, pv, per_neg]; rfl⟩ }
  have hχ (v) : Function.invFun (pv X idx x) (pv X idx x v) = v := Function.leftInverse_invFun hinj v
  let Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e :=
    { e := A.ex
      lat := lat
      span := by
        rw [← (hsp L (SW.TensLat.span_of_selfD X hL)).1]
        congr 1
        ext z
        exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩⟩
      e_add := A.ex_add
      e_onto := A.ex_onto
      e_ker := A.ex_ker
      hol := fun U f => by
        obtain ⟨h1, h2⟩ := A.hol U f
        simp only [Set.mem_univ, true_and] at h1 h2
        exact ⟨h1, h2⟩
      Hm := ThFr.Hm X bas idx x
      herm := Hm_isHermitian idx hs hx
      χ := fun z => A.χ (Function.invFun (pv X idx x) z)
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ_norm := by
        rintro _ ⟨v, hv, rfl⟩
        rw [hχ]
        exact A.χ_norm v hv
      fr_per := by
        rintro _ ⟨v, hv, rfl⟩ j z hz
        rw [hχ, ← hx_eq_hermForm, ← hx_eq_hermForm]
        exact A.fr_per v hv j z hz
      lin := A.ex_lin
      adj := fun a z w => by
        rw [← hx_eq_hermForm, ← hx_eq_hermForm]
        have hb : cc (a : E) = ((H.bar a : 𝓞 E) : E) := (H.bar_eq a).symm
        have h := hadj (a : E) z w
        rw [hb] at h
        exact h
      der := A.der }
  refine ⟨Φ, fun _ => rfl, rfl, fun _ => Iff.rfl, fun z w => (hx_eq_hermForm idx x z w).symm,
    fun v _ => congrArg A.χ (hχ v), fun _ _ _ => Iff.rfl, fun k a θ => ?_⟩
  funext z
  change cexp _ * θ (z + a) = cexp _ * θ (z + a)
  congr 2
  rw [hx_eq_hermForm]
  change _ - _ * _ * hermForm (ThFr.Hm X bas idx x) a a / 2 = _
  change -(_ * _ * hermForm (ThFr.Hm X bas idx x) z a) - _ = _
  simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul, Int.cast_natCast]
  ring

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumnsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_symplectic_unitary_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  first | exact @GlobalTheory.ColumnSymplectic.exists_symplectic_columns | exact GlobalTheory.ColumnSymplectic.exists_symplectic_columns | (intros; apply GlobalTheory.ColumnSymplectic.exists_symplectic_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisGFixOfMemLattice
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private lemma isIntegral_crd_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) {v : Fin r → E}
    (hv : v ∈ X.Λ) (j : Fin g ⊕ Fin g) : IsIntegral ℤ (crd X bas v j) := by

  obtain ⟨m, rfl⟩ : ∃ m, (bas m : Fin r → E) = v := ⟨bas.symm ⟨v, hv⟩, by simp⟩
  rw [← vecQ_intCast X bas m, crd_vecQ hs]
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := m j)

theorem heisG_fix_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ : TF n g, IsSB φ → ∃ N : ℕ, 0 < N ∧ ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ j : ℕ, heisG X bas (((j * N : ℕ) : E) • y) φ = φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn φ hφ
  obtain ⟨R, hR, hlev⟩ := hφ
  refine ⟨2 * R, by omega, fun y hy j => ?_⟩

  have hmem : ∀ k, (j • y) k ∈ X.Λ := fun k => nsmul_mem (hy k) j
  have hsc : (((j * (2 * R) : ℕ) : E) • y) = (2 * R) • (j • y) := by
    rw [Nat.cast_smul_eq_nsmul, smul_smul]
    congr 1
    ring
  rw [hsc, GlobalTheory.SW.TensVac.heisG_eq hs, map_nsmul, Prod.smul_fst, Prod.smul_snd,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).1,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).2]
  exact GlobalTheory.SW.TensVac.heisS_fix hlev (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inl i))
    (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inr i))

end GlobalTheory.Ker
end

