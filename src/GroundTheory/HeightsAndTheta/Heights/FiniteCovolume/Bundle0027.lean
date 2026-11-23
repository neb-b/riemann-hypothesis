module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0018
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0025

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceLift
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace CongruenceLift

theorem exists_nsmul_mem {E W : Type*} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) : ∃ d : ℕ, 0 < d ∧ d • w ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem hLa w

theorem exists_congruence {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]
    (L : AddSubgroup V) (hL : L.FG) (d : ℕ) (hd : 0 < d) :
    ∃ K : Subgroup (MulAction.stabilizer G L), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ L, ∃ u ∈ L, d • u = (k : G) • y - y := by
  set S := MulAction.stabilizer G L
  have hS : ∀ (s : S) (y : V), y ∈ L → (s : G) • y ∈ L := fun s y hy => by
    have := AddSubgroup.smul_mem_pointwise_smul y (s : G) L hy
    rwa [MulAction.mem_stabilizer_iff.1 s.2] at this
  let f : S → L →+ L := fun s =>
    { toFun := fun y => ⟨(s : G) • (y : V), hS s y y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun y z => Subtype.ext (smul_add _ _ _) }
  set N : AddSubgroup L := (nsmulAddMonoidHom (α := L) d).range
  have hN : ∀ s, N ≤ N.comap (f s) := by
    rintro s _ ⟨u, rfl⟩
    exact ⟨f s u, by simp [map_nsmul]⟩
  let _ : MulAction S (L ⧸ N) :=
    { smul := fun s q => QuotientAddGroup.map N N (f s) (hN s) q
      one_smul := fun q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f 1) (hN 1) (y : L ⧸ N) = y
        rw [QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (one_smul G (y : V))
      mul_smul := fun s t q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f (s * t)) (hN _) (y : L ⧸ N) =
          QuotientAddGroup.map N N (f s) (hN s) (QuotientAddGroup.map N N (f t) (hN t) y)
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (mul_smul (s : G) (t : G) (y : V)) }
  have hfg : AddGroup.FG L := (AddGroup.fg_iff_addSubgroup_fg L).2 hL
  have hfin : Finite (L ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    refine QuotientAddGroup.induction_on q fun y => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨d, hd, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩
  refine ⟨(MulAction.toPermHom S (L ⧸ N)).ker, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  intro k hk y hy
  have hq := DFunLike.congr_fun (MonoidHom.mem_ker.1 hk) ((⟨y, hy⟩ : L) : L ⧸ N)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at hq
  change QuotientAddGroup.map N N (f k) (hN k) _ = _ at hq
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hq
  obtain ⟨u, hu⟩ := hq
  refine ⟨-(u : V), L.neg_mem u.2, ?_⟩
  have := congrArg Subtype.val hu
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_nsmul, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at this
  rw [smul_neg, this]
  change -(-((k : G) • y) + y) = (k : G) • y - y
  abel

end CongruenceLift

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem CongruenceLift.proof [FiniteDimensional E W] (h : HermitianForm F E W) :
    CongruenceLift.Statement h := by
  intro D La x₀ w₀ hLa hx₀ hp h' hh'
  obtain ⟨d, hd, hdw⟩ := CongruenceLift.exists_nsmul_mem hLa.isLattice w₀
  set La' : AddSubgroup (hypComplement h x₀ w₀) := La.comap (hypComplement h x₀ w₀).subtype.toAddMonoidHom
  have dec : ∀ x ∈ La, h.toSesq (d • w₀) x • x₀ ∈ La ∧ (h.toSesq x₀ x * d) • w₀ ∈ La ∧
      d • x - h.toSesq (d • w₀) x • x₀ - (h.toSesq x₀ x * d) • w₀ =
        ((d • ComplementExtension.proj hp x : hypComplement h x₀ w₀) : W) := by
    intro x hx
    refine ⟨hLa.isLattice.smul_mem ⟨_, hLa.integral _ hdw x hx⟩ x₀ hx₀, ?_, ?_⟩
    · have := hLa.isLattice.smul_mem ⟨_, hLa.integral _ hx₀ x hx⟩ _ hdw
      rwa [← Nat.cast_smul_eq_nsmul E, smul_smul] at this
    · rw [Submodule.coe_smul_of_tower, ComplementExtension.proj_apply, map_nsmul,
        LinearMap.smul_apply]
      simp only [← Nat.cast_smul_eq_nsmul E, smul_eq_mul]
      module
  obtain ⟨D', hD'⟩ := ComplementLattice.proof h x₀ w₀ hp h' hh' D d hd
  have hLa' : IsDIntegral h' D' La' := hD' La hLa fun x hx =>
    ⟨_, (dec x hx).1, _, (dec x hx).2.1, by rw [(dec x hx).2.2]; exact Submodule.coe_mem _⟩
  obtain ⟨K, hK, hcong⟩ : ∃ K : Subgroup (latticeStab h' La'), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ La', ∃ u ∈ La', d • u = (k : h'.unitaryGroup) • y - y :=
    CongruenceLift.exists_congruence (G := h'.unitaryGroup) La' hLa'.isLattice.fg d hd
  have key : ∀ k ∈ K, ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
      (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((((k : latticeStab h' La') : h'.unitaryGroup) • x : hypComplement h x₀ w₀) : W)) →
      ∀ x ∈ La, γ • x ∈ La := by
    intro k hk γ h1 h2 h3 x hx
    obtain ⟨hA, hB, hC⟩ := dec x hx
    set y : hypComplement h x₀ w₀ := d • ComplementExtension.proj hp x
    have hy : y ∈ La' := by
      change (y : W) ∈ La
      rw [← hC]
      exact La.sub_mem (La.sub_mem (La.nsmul_mem hx d) hA) hB
    obtain ⟨u, hu, hdu⟩ := hcong k hk y hy
    have hx' : d • x = h.toSesq (d • w₀) x • x₀ + (y : W) + (h.toSesq x₀ x * d) • w₀ := by
      rw [← hC]
      abel
    have hγ : d • (γ • x) = d • (x + (u : W)) := by
      have hdu' : (((k : latticeStab h' La') : h'.unitaryGroup) • y : hypComplement h x₀ w₀) = (y : W) + d • (u : W) := by
        rw [← Submodule.coe_smul_of_tower, hdu]
        simp
      rw [← smul_comm, hx', smul_add, smul_add, smul_comm γ (h.toSesq (d • w₀) x),
        smul_comm γ (h.toSesq x₀ x * d), h1, h2, h3, hdu', smul_add, hx']
      abel
    have hne : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have := smul_right_injective W hne (by simpa only [Nat.cast_smul_eq_nsmul] using hγ)
    rw [this]
    exact La.add_mem hx hu
  refine ⟨D', La', K.map (latticeStab h' La').subtype, hLa', Subgroup.map_subtype_le K, ?_, ?_⟩
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (latticeStab h' La').subtype_injective]
    exact hK
  · rintro _ ⟨k, hk, rfl⟩ γ h1 h2 h3
    refine MulAction.mem_stabilizer_iff.2 (le_antisymm ?_ ?_)
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists z γ La).1 hz
      exact key k hk γ h1 h2 h3 x hx
    · intro z hz
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      refine key k⁻¹ (K.inv_mem hk) γ⁻¹ (inv_smul_eq_iff.2 h1.symm) (inv_smul_eq_iff.2 h2.symm)
        (fun x => inv_smul_eq_iff.2 ?_) z hz
      rw [h3]
      simp

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRadicalTorusModulusCoords
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {a : ι → ℂ}

theorem heisMat_conj_scale {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) {α : ℂ}
    (hga : g *ᵥ a = α • a) {y : ι → ℂ} (hgy : g *ᵥ y = y) (s : ℂ) :
    g * heisMat H a y s =
      heisMat H a (starRingEnd ℂ α • y) ((Complex.normSq α : ℂ) * s) * g := by
  refine matrix_ext_mulVec fun z => ?_
  have h1 : hForm H a z = starRingEnd ℂ α * hForm H a (g *ᵥ z) := by
    rw [← hForm_mulVec_of_unitary H hg a z, hga, hForm_smul_left]
  have h2 : hForm H y z = hForm H y (g *ᵥ z) := by
    conv_lhs => rw [← hForm_mulVec_of_unitary H hg y z, hgy]
  rw [← mulVec_mulVec, ← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec, h1, h2, hForm_smul_left,
    Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, hga, hgy]
  module


omit [DecidableEq ι] in
theorem heisS_conj_smul (α : ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H (starRingEnd ℂ α • y) (Complex.normSq α * t) = (Complex.normSq α : ℂ) * heisS H y t := by
  have e : hForm H (starRingEnd ℂ α • y) (starRingEnd ℂ α • y) =
      (Complex.normSq α : ℂ) * hForm H y y := by
    rw [hForm_smul_left, hForm_smul_right, Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
    ring
  apply Complex.ext
  · simp only [heisS, e, Complex.re_ofReal_mul]
    ring
  · simp only [heisS, Complex.im_ofReal_mul]

end Mat

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisScale (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (c : InfinitePlace E → ℂ) :
    heisY h v x₀ w₀ →ₗ[ℝ] heisY h v x₀ w₀ where
  toFun y := ⟨fun w => c w • (y : InfinitePlace E → ι → ℂ) w, mem_heisY.2 fun w => by
    simp only [hForm_smul_right, (y.2 w).1, (y.2 w).2, mul_zero, and_self]⟩
  map_add' y z := by
    apply Subtype.ext
    funext w
    simp [smul_add]
  map_smul' r y := by
    apply Subtype.ext
    funext w
    change c w • ((r • (y : InfinitePlace E → ι → ℂ)) w) =
      r • (c w • (y : InfinitePlace E → ι → ℂ) w)
    rw [Pi.smul_apply, real_smul_vec, real_smul_vec, smul_comm]

theorem heisPoint_torus (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (α : InfinitePlace E → ℂ)
    (hga : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      α w • vecAt v x₀ w)
    (hgy : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisScale h v x₀ w₀ (fun w => starRingEnd ℂ (α w)) p.1,
        fun w => Complex.normSq (α w) * p.2 w) := by
  apply Subtype.ext
  funext w
  apply Units.ext
  have hu := archUnitary_at_place g w
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisMatAt, heisMatAt,
    heisMat_conj_scale hu (hga w) (hgy w _ (p.1.2 w).1 (p.1.2 w).2), mul_assoc, Units.mul_inv,
    mul_one]
  congr 1
  exact (heisS_conj_smul (α w) _ (p.2 w)).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLevi
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace StabilizerLevi

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def mat {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

section Mat

variable {h : HermitianForm F E W} {v : Basis ι E W}

theorem mat_mul (g g' : archUnitary h v) (w : InfinitePlace E) :
    mat (g * g') w = mat g w * mat g' w := rfl

theorem mat_one (w : InfinitePlace E) : mat (1 : archUnitary h v) w = 1 := rfl

theorem mat_mul_inv (g : archUnitary h v) (w : InfinitePlace E) : mat g w * mat g⁻¹ w = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_inv_mul (g : archUnitary h v) (w : InfinitePlace E) : mat g⁻¹ w * mat g w = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem unitary_mat (g : archUnitary h v) (w : InfinitePlace E) :
    (mat g w)ᴴ * gramAt h v w * mat g w = gramAt h v w := by
  have := mem_archUnitary.1 g.2 w
  rwa [conjT_eq] at this

theorem continuous_mat (w : InfinitePlace E) : Continuous fun g : archUnitary h v => mat g w :=
  Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)

end Mat

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W} {n : ℕ}
  (hp : IsHyperbolicPair h x₀ w₀) {h' : HermitianForm F E (hypComplement h x₀ w₀)}
  (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) {v' : Basis (Fin n) E (hypComplement h x₀ w₀)}

abbrev bMat (v : Basis ι E W) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    Matrix ι (Fin n) ℂ :=
  colMat v (fun k => (v' k : W)) w

include hp hh'

theorem q_mul (g g' : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀)
    (hg' : g' ∈ vecFixGroup h v x₀) (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (g * g') w) =
      leviProj (gramAt h v w) (bMat v v' w) (mat g w) *
        leviProj (gramAt h v w) (bMat v v' w) (mat g' w) := by
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [mat_mul]
  exact leviProj_mul hH hG hBX hBY hXX hYY hXY hspan (unitary_mat g w) (hg w) (unitary_mat g' w)
    (hg' w)

theorem q_one (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h v) w) = 1 := by
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [mat_one, leviProj, Matrix.mul_one]
  exact leftInv_mul hG

def qUnit (g : vecFixGroup h v x₀) (w : InfinitePlace E) : GL (Fin n) ℂ where
  val := leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w)
  inv := leviProj (gramAt h v w) (bMat v v' w) (mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w)
  val_inv := by
    rw [← q_mul hp hh' _ _ g.2 (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      q_one hp hh']
  inv_val := by
    rw [← q_mul hp hh' _ _ (g⁻¹).2 g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      q_one hp hh']

theorem qUnit_mem (g : vecFixGroup h v x₀) :
    (fun w => qUnit hp hh' (v' := v') g w) ∈ archUnitary h' v' := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w))ᴴ * gramAt h' v' w *
    leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = gramAt h' v' w
  rw [gramAt_complement v h' hh' v' w]
  exact leviProj_unitary hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)

def qHom : vecFixGroup h v x₀ →* archUnitary h' v' where
  toFun g := ⟨fun w => qUnit hp hh' g w, qUnit_mem hp hh' g⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (q_one hp hh' w))
  map_mul' g g' := Subtype.ext (funext fun w => Units.ext (q_mul hp hh' _ _ g.2 g'.2 w))

def iUnit (m : archUnitary h' v') (w : InfinitePlace E) : GL ι ℂ where
  val := leviSec (gramAt h v w) (bMat v v' w) (mat m w)
  inv := leviSec (gramAt h v w) (bMat v v' w) (mat m⁻¹ w)
  val_inv := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_mul_inv, leviSec_one]
  inv_val := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_inv_mul, leviSec_one]

theorem iUnit_mem (m : archUnitary h' v') : (fun w => iUnit hp hh' (v := v) m w) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviSec (gramAt h v w) (bMat v v' w) (mat m w))ᴴ * gramAt h v w *
    leviSec (gramAt h v w) (bMat v v' w) (mat m w) = gramAt h v w
  refine leviSec_unitary hH hG _ ?_
  rw [← gramAt_complement v h' hh' v' w]
  exact unitary_mat m w

theorem iUnit_mem_vecFixGroup (m : archUnitary h' v') :
    (⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩ : archUnitary h v) ∈ vecFixGroup h v x₀ := by
  intro w
  obtain ⟨hH, hG, hBX, -⟩ := frame v hp h' hh' v' w
  exact leviSec_mulVec_of hBX _

def iHom : archUnitary h' v' →* vecFixGroup h v x₀ where
  toFun m := ⟨⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩, iUnit_mem_vecFixGroup hp hh' m⟩
  map_one' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    change leviSec (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h' v') w) = 1
    rw [mat_one, leviSec_one])))
  map_mul' m m' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (m * m') w) =
      leviSec (gramAt h v w) (bMat v v' w) (mat m w) * leviSec (gramAt h v w) (bMat v v' w) (mat m' w)
    rw [mat_mul, leviSec_mul hG])))

theorem continuous_qHom : Continuous (qHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun g : vecFixGroup h v x₀ =>
      leftInv (gramAt h v w) (bMat v v' w) * mat (g : archUnitary h v) w * bMat v v' w
    exact (continuous_const.matrix_mul ((continuous_mat w).comp continuous_subtype_val)).matrix_mul
      continuous_const
  · change Continuous fun g : vecFixGroup h v x₀ =>
      leftInv (gramAt h v w) (bMat v v' w) * mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w *
        bMat v v' w
    exact (continuous_const.matrix_mul (((continuous_mat w).comp continuous_subtype_val).comp
      continuous_inv)).matrix_mul continuous_const

theorem continuous_iHom : Continuous (iHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2
    (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩))
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul (continuous_mat w)).matrix_mul
      continuous_const)
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m⁻¹ w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul
      ((continuous_mat w).comp continuous_inv)).matrix_mul continuous_const)

end StabilizerLevi

open StabilizerLevi

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem StabilizerLevi.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    StabilizerLevi.Statement h v := by
  intro x₀ w₀ hp h' hh' n v'
  refine ⟨iHom hp hh', qHom hp hh', continuous_iHom hp hh', continuous_qHom hp hh', ?_, ?_, ?_, ?_⟩
  · intro m
    apply Subtype.ext
    funext w
    apply Units.ext
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    exact leviProj_leviSec hG (mat m w)
  · intro g
    rw [mem_unipRadical]
    constructor
    · intro h1 w
      obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
      have e : leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = 1 :=
        congrArg (fun u : archUnitary h' v' =>
          ((u : InfinitePlace E → GL (Fin n) ℂ) w : Matrix (Fin n) (Fin n) ℂ)) h1
      exact ⟨g.2 w, (leviProj_eq_one_iff hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w)
        (g.2 w)).1 e⟩
    · intro h1
      apply Subtype.ext
      funext w
      apply Units.ext
      obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
      exact (leviProj_eq_one_iff hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)).2
        (h1 w).2
  · intro m w
    obtain ⟨hH, hG, hBX, hBY, -⟩ := frame v hp h' hh' v' w
    exact leviSec_mulVec_of hBY _
  · intro γ m hx hw hW
    apply Subtype.ext
    funext w
    apply Units.ext
    obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (archEmbed h' v' m) w) = mat (archEmbed h v γ) w
    symm
    apply eq_leviSec hH hG hBX hBY hXX hYY hXY hspan
    · rw [mat, archEmbed_apply, map_toMatrix_mulVec_vecAt]
      exact congrArg (fun x => vecAt v x w) hx
    · rw [mat, archEmbed_apply, map_toMatrix_mulVec_vecAt]
      exact congrArg (fun x => vecAt v x w) hw
    · apply ext_of_mulVec_single
      intro k
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← vecAt_basis v' k w, ← vecAt_coe, mat, mat,
        archEmbed_apply, archEmbed_apply, map_toMatrix_mulVec_vecAt, map_toMatrix_mulVec_vecAt,
        ← vecAt_coe]
      exact congrArg (fun x => vecAt v x w) (hW (v' k))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

