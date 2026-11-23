module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlOfUnitary
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {D : D7} (X : HidaSetting D)

def matOf (γ : (VS D).V →ₗ[D.host.E] (VS D).V) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (LinearMap.toMatrix X.bas X.bas γ).map X.ιE.symm

theorem matOf_comp (γ δ : (VS D).V →ₗ[D.host.E] (VS D).V) : matOf X (γ ∘ₗ δ) = matOf X γ * matOf X δ := by
  unfold matOf
  rw [LinearMap.toMatrix_comp X.bas X.bas X.bas]
  simpa using map_mul X.ιE.symm.mapMatrix (LinearMap.toMatrix X.bas X.bas γ) (LinearMap.toMatrix X.bas X.bas δ)

theorem matOf_id : matOf X LinearMap.id = 1 := by
  unfold matOf
  rw [LinearMap.toMatrix_id]
  simp

theorem crd_apply (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (γ y) = matOf X γ *ᵥ X.crd y := by
  funext i
  show X.ιE.symm (X.bas.repr (γ y) i) = _
  rw [← LinearMap.toMatrix_mulVec_repr X.bas X.bas γ y]
  exact RingHom.map_mulVec (X.ιE.symm : D.host.E →+* X.B.I.E) _ _ i

theorem crd_inj : Function.Injective (X.crd) := fun _ _ h =>
  X.bas.repr.injective (Finsupp.ext fun i => X.ιE.symm.injective (congrFun h i))

def glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : GL (Fin X.B.I.n) X.B.I.E where
  val := matOf X γ.toLinearMap
  inv := matOf X γ.symm.toLinearMap
  val_inv := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp
  inv_val := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp

theorem matE_glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : matE X (glOf X γ) = γ := by
  apply LinearEquiv.ext
  intro y
  apply crd_inj X
  rw [matE_crd]
  exact (crd_apply X γ.toLinearMap y).symm

theorem matE_inj {M M' : GL (Fin X.B.I.n) X.B.I.E} (h : matE X M = matE X M') : M = M' := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← LatDictK.crd_vOf X x, ← matE_crd, ← matE_crd, h]

theorem hT_coord (x y : (VS D).V) :
    (VS D).hT x y = star (X.bas.equivFun x) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun y) := by
  rw [hT_expand X x y]
  simp only [← X.J_eq]
  rw [qform]

theorem form_ext {m : Type} [Fintype m] [DecidableEq m] {P Q : Matrix m m D.host.E}
    (h : ∀ a c : m → D.host.E, star a ⬝ᵥ (P *ᵥ c) = star a ⬝ᵥ (Q *ᵥ c)) : P = Q := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single i (1 : D.host.E) : m → D.host.E) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  rw [hs] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem mapM_cT (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) M) = (mapM X M)ᴴ := by
  ext i j
  simp only [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT,
    Matrix.transpose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]

theorem glOf_unitary (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    glOf X γ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  set A := mapM X ((glOf X γ : GL _ _) : Matrix _ _ _) with hA
  have hrep : ∀ y, X.bas.equivFun (γ y) = A *ᵥ X.bas.equivFun y := by
    intro y
    rw [hA, ← matE_repr, matE_glOf]
  have key : Aᴴ * mapM X X.B.I.J * A = mapM X X.B.I.J := by
    apply form_ext
    intro a c
    have h1 := hγ (X.bas.equivFun.symm a) (X.bas.equivFun.symm c)
    rw [hT_coord, hT_coord, hrep, hrep, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    rw [← h1, Matrix.star_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  show Formalism.UG.cT (starRingEnd X.B.I.E) ((glOf X γ : GL _ _) : Matrix _ _ _) * X.B.I.J * ((glOf X γ : GL _ _) : Matrix _ _ _) =
    X.B.I.J
  apply Matrix.map_injective X.ιE.injective
  show mapM X _ = mapM X _
  rw [map_mul, map_mul, mapM_cT]
  exact key

end Mat

section UJ

theorem uj_bc {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m]
    (φ : A →+* B) (σA : A →+* A) (σB : B →+* B) (hσ : ∀ a, φ (σA a) = σB (φ a)) (JA : Matrix m m A)
    (g : GL m A) (hg : g ∈ Formalism.UG.UJ σA JA) : Formalism.UG.bc φ g ∈ Formalism.UG.UJ σB (JA.map φ) := by
  have hg' : Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA := hg
  show Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ
  have hc : Formalism.UG.cT σB ((g : Matrix m m A).map φ) = (Formalism.UG.cT σA (g : Matrix m m A)).map φ := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end UJ

section AH

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def AH (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, γ (X.eX a) = X.eX a) ∧ (∀ a, γ (X.fY a) = X.fY a) ∧
    γ (X.zu u) = X.zu u ∧ Formalism.HermitianLatticesTheory.gmap γ Λ = Λ}

theorem crd_fix_of (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, γ (X.eX a) = X.eX a)
    (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    (glOf X γ : Matrix _ _ _) *ᵥ y = y := by
  have hc : ∀ v, γ v = v → (glOf X γ : Matrix _ _ _) *ᵥ X.crd v = X.crd v := fun v hv => by
    rw [← matE_crd, matE_glOf, hv]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
  · exact hc _ (he a)
  · exact hc _ (hf a)
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz']
    exact hc _ hz

def gOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (he : ∀ a, γ (X.eX a) = X.eX a) (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) : Hfin X u :=
  ⟨⟨Formalism.UG.bc (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ),
    uj_bc _ _ _ (fun a => by simp [Formalism.UG.sigR, Formalism.UG.inclE]; rfl) X.B.I.J _ (glOf_unitary X γ hγ)⟩,
    fun y hy => by
      show ((glOf X γ : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))) *ᵥ incl X.B.I y =
        incl X.B.I y
      funext i
      have := (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ : Matrix _ _ _) y i).symm
      rw [crd_fix_of X u γ he hf hz y hy] at this
      exact this⟩

end AH

end Formalism.L2.SG.RhoPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ideal

variable {D : D7}

abbrev dI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

theorem star_F (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c :=
  (NumberField.IsCMField.complexConj D.host.E).commutes c

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨⟨star (o : D.host.E), o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

theorem star_mem_pow (n : ℕ) (y : 𝓞 D.host.E) (hy : y ∈ dI D ^ n) :
    ∃ y' ∈ dI D ^ n, (y' : D.host.E) = star (y : D.host.E) := by
  rw [← Ideal.map_pow] at hy ⊢
  have hy' : y ∈ Submodule.span (𝓞 D.host.E)
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) '' ((differentIdeal ℤ (𝓞 D.host.F) ^ n : Ideal (𝓞 D.host.F)) : Set (𝓞 D.host.F))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, ?_⟩
    have e : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (c : D.host.F) := rfl
    rw [e, star_F]
  | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Ideal.add_mem _ hx' hy', ?_⟩
    rw [show ((x' + y' : 𝓞 D.host.E) : D.host.E) = (x' : D.host.E) + (y' : D.host.E) from rfl,
      show ((x + y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) + (y : D.host.E) from rfl, ex, ey, star_add]
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := star_int a
    refine ⟨a' * x', Ideal.mul_mem_left _ _ hx', ?_⟩
    rw [smul_eq_mul, show ((a' * x' : 𝓞 D.host.E) : D.host.E) = (a' : D.host.E) * (x' : D.host.E) from rfl,
      show ((a * x : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * (x : D.host.E) from rfl, ea, ex, star_mul, mul_comm]

theorem dI_ne_bot (n : ℕ) : dI D ^ n ≠ ⊥ := by
  have h : dI D ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
  rw [← Ideal.zero_eq_bot] at h ⊢
  exact pow_ne_zero n h

theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hy))
    exact ⟨o, ho⟩
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨o, ho⟩ := h y hy
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩

theorem star_mem_inv (n : ℕ) {x : D.host.E}
    (hx : x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹) :
    star x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [mem_inv_coe (dI_ne_bot n)] at hx ⊢
  intro y hy
  obtain ⟨y', hy', ey⟩ := star_mem_pow n y hy
  obtain ⟨o, ho⟩ := hx y' hy'
  obtain ⟨o', eo⟩ := star_int o
  refine ⟨o', ?_⟩
  rw [eo, ho, ey, star_mul, star_star, mul_comm]

end Ideal

section Entry

variable {D : D7}

theorem hT_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (m n : ℕ)
    (v v' : (VS D).V)
    (hv : ∀ x ∈ ((dI D ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹,
      x • v ∈ Λ)
    (hv' : ∀ y ∈ ((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹,
      y • v' ∈ Λ) :
    ∃ o ∈ dI D ^ (m + n), (o : D.host.E) = (VS D).hT v v' := by
  set Z := (VS D).hT v v' with hZ
  let FI := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E
  set A : FI := ((dI D ^ m : Ideal (𝓞 D.host.E)) : FI)⁻¹
  set B : FI := ((dI D ^ n : Ideal (𝓞 D.host.E)) : FI)⁻¹
  have hJ : ((dI D ^ (m + n) : Ideal (𝓞 D.host.E)) : FI) = (A * B)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv, ← FractionalIdeal.coeIdeal_mul, ← pow_add]
  have hAB0 : A * B ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_) <;>
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero] <;> exact dI_ne_bot _
  have hmem : Z ∈ (A * B)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hAB0]
    intro w hw
    refine FractionalIdeal.mul_induction_on hw ?_ ?_
    · intro a ha b hb
      have ha' : star a ∈ A := star_mem_inv m ha
      obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hv _ ha') (hv' _ hb)
      refine (FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩
      show (c : D.host.E) = _
      rw [hc, LinearMap.map_smulₛₗ₂, LinearMap.map_smulₛₗ, RingHom.id_apply, starRingEnd_apply, star_star,
        smul_eq_mul, smul_eq_mul, hZ]
      ring
    · intro x y hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
  rw [← hJ] at hmem
  obtain ⟨o, ho, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨o, ho, e⟩

theorem two_sum_sub (r : ℕ) : ∀ q : ℕ, q ≤ r + 1 → 2 * ∑ i : Fin q, (r - (i : ℕ)) = q * (2 * r + 1 - q)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_add, two_sum_sub r q (by omega)]
    have e1 : 2 * r + 1 - q = q + 2 * (r - q) + 1 := by omega
    have e2 : 2 * r + 1 - (q + 1) = q + 2 * (r - q) := by omega
    rw [e1, e2]
    ring

end Entry

section Norm

variable {D : D7}

theorem discr_sq : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 :=
  D.host.der.discr_sq

theorem absNorm_dI : ((Ideal.absNorm (dI D) : ℕ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := by
  have h := Formalism.MainNotions.BridgeLemma.szf_normDD D discr_sq
  unfold Formalism.MainNotions.BridgeLemma.SzfNormDD Formalism.MainNotions.S.ddE at h
  rw [FractionalIdeal.coeIdeal_absNorm] at h
  exact_mod_cast h

theorem rd_pos : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _

theorem prod_sq_ge (n : ℕ) (o : 𝓞 D.host.E) (ho : o ∈ dI D ^ n) (h0 : (o : D.host.E) ≠ 0) :
    (D.host.rdE ^ D.R.f) ^ (2 * n) ≤ ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm (o : D.host.E)
  have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ w.mult =
      ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 :=
    Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← h2, h1, ← Algebra.coe_norm_int]
  have ho0 : o ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hspan : Ideal.span {o} ≤ dI D ^ n := (Ideal.span_singleton_le_iff_mem _).2 ho
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  rw [Ideal.absNorm_span_singleton, map_pow] at hdvd
  have hne : (Algebra.norm ℤ o).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact Algebra.norm_ne_zero_iff.2 ho0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have hle' : ((Ideal.absNorm (dI D) ^ n : ℕ) : ℝ) ≤ ((Algebra.norm ℤ o).natAbs : ℝ) := by exact_mod_cast hle
  rw [Nat.cast_pow, absNorm_dI, ← pow_mul] at hle'
  have e : (((Algebra.norm ℤ o).natAbs : ℕ) : ℝ) = ((|((Algebra.norm ℤ o : ℤ) : ℚ)| : ℚ) : ℝ) := by
    simp [Nat.cast_natAbs, Rat.cast_abs]
  rw [← e]
  exact hle'

end Norm

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAFG
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section FG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem isNoetherianRing_locE_O' (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] :
    IsNoetherianRing L.O := by
  classical
  haveI : IsReduced E := L.reduced
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hA : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E (a : F) := fun a =>
    IsScalarTower.algebraMap_apply 𝒪[F] F E a
  have hcjA : ∀ (a : F) (w : E), L.cj (algebraMap F E a * w) = algebraMap F E a * L.cj w := by
    intro a w
    rw [map_mul, L.cj.commutes]
  have hcjO : ∀ x ∈ L.O, L.cj x ∈ L.O := by
    intro x hx
    rw [L.O_def] at hx ⊢
    exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  have htr : ∀ z ∈ L.O, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = z + L.cj z := by
    intro z hz
    have hmem : z + L.cj z ∈ L.O := L.O.add_mem hz (hcjO z hz)
    obtain ⟨a, ha⟩ := (L.cj_fix (z + L.cj z)).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
    have hint : IsIntegral 𝒪[F] (algebraMap F E a) := ha ▸ (L.O_def _).1 hmem
    have hint' : IsIntegral 𝒪[F] a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).1 hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    exact ⟨y, by rw [hA, ← ha, ← hy]; rfl⟩
  have hnd : ∀ x : E, (∀ y : E, x * y + L.cj (x * y) = 0) → x = 0 := by
    intro x hx
    have h1 : L.cj x = -x := by
      have h := hx 1
      rw [mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
    have h2 := hx x
    rw [map_mul, h1, neg_mul_neg, ← two_mul] at h2
    have hu : IsUnit (2 : E) := by
      have h3 : (2 : E) = algebraMap F E 2 := (map_ofNat (algebraMap F E) 2).symm
      rw [h3]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    have hxx : x * x = 0 := hu.mul_right_eq_zero.1 h2
    exact IsReduced.eq_zero x ⟨2, by rw [pow_two, hxx]⟩
  let b := Module.finBasisOfFinrankEq F E L.rank
  have hsc : ∀ i, ∃ c : F, c ≠ 0 ∧ algebraMap F E c * b i ∈ L.O := by
    intro i
    haveI : Algebra.IsAlgebraic 𝒪[F] F := IsLocalization.isAlgebraic F (nonZeroDivisors 𝒪[F])
    haveI : Algebra.IsAlgebraic 𝒪[F] E := Algebra.IsAlgebraic.trans 𝒪[F] F E
    obtain ⟨c, hc, hci⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[F]) (b i)).exists_integral_multiple
    refine ⟨(c : F), by exact_mod_cast hc, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def, hA] at hci
  choose c hc0 hcO using hsc
  let φ : 𝒪[F] →+* L.O :=
    (algebraMap 𝒪[F] E).codRestrict L.O (fun a => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hsm : ∀ (a : 𝒪[F]) (x : L.O), ((a • x : L.O) : E) = algebraMap F E (a : F) * x := by
    intro a x
    rw [Algebra.smul_def, Subring.coe_mul, ← hA]
    rfl
  let B : Fin 2 → E := fun i => algebraMap F E (c i) * b i
  let g : L.O →ₗ[𝒪[F]] (Fin 2 → E) :=
    { toFun := fun x i => (x : E) * B i + L.cj ((x : E) * B i)
      map_add' := by
        intro x y
        funext i
        simp only [Subring.coe_add, add_mul, map_add (f := _), Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [hsm, Algebra.smul_def, hA]
        simp only [mul_assoc, hcjA, mul_add] }
  let N : Submodule 𝒪[F] (Fin 2 → E) :=
    Submodule.span 𝒪[F] (Set.range fun i : Fin 2 => Pi.single i (1 : E))
  haveI : IsNoetherian 𝒪[F] N := isNoetherian_span_of_finite 𝒪[F] (Set.finite_range _)
  have hgN : ∀ x, g x ∈ N := by
    intro x
    have hx : ∀ i, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = (x : E) * B i + L.cj ((x : E) * B i) :=
      fun i => htr _ (L.O.mul_mem x.2 (hcO i))
    choose a ha using hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    show _ = fun j => (x : E) * B j + L.cj ((x : E) * B j)
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
  have hinj : Function.Injective (g.codRestrict N hgN) := by
    intro x y hxy
    have h0 : g x = g y := congrArg Subtype.val hxy
    have hd : ∀ i, ((x : E) - y) * B i + L.cj (((x : E) - y) * B i) = 0 := by
      intro i
      have h := congrFun h0 i
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [sub_mul, map_sub]
      linear_combination h
    have hb : ∀ i, ((x : E) - y) * b i + L.cj (((x : E) - y) * b i) = 0 := by
      intro i
      have h := hd i
      simp only [B] at h
      rw [mul_left_comm, hcjA, ← mul_add] at h
      exact ((IsUnit.mk0 _ (hc0 i)).map (algebraMap F E)).mul_right_eq_zero.1 h
    have hall : ∀ w, ((x : E) - y) * w + L.cj (((x : E) - y) * w) = 0 := by
      intro w
      let τ : E →ₗ[F] E := LinearMap.mulLeft F ((x : E) - y) +
        (L.cj.toLinearMap).comp (LinearMap.mulLeft F ((x : E) - y))
      have hτ : τ = 0 := b.ext (fun i => by simpa [τ] using hb i)
      simpa [τ] using LinearMap.congr_fun hτ w
    exact Subtype.ext (sub_eq_zero.1 (hnd _ hall))
  haveI : IsNoetherian 𝒪[F] L.O := isNoetherian_of_injective (g.codRestrict N hgN) hinj
  exact isNoetherianRing_iff.2 (isNoetherian_of_tower 𝒪[F] this)

theorem thFG_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThFG M r := by
  intro V _ _ H t ht
  haveI := hM.loc
  haveI := hM.char0
  haveI : IsNoetherianRing M.L.O := isNoetherianRing_locE_O' M.L
  have hfg : t.abelian₂.FG := ht.1.1.1
  haveI : IsNoetherian M.L.O t.abelian₂ := isNoetherian_of_fg_of_noetherian _ hfg
  have hle : ThL H t ≤ t.abelian₂ := inf_le_left
  haveI := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.1 inferInstance

end FG

end Formalism.L2.SG.LsDatumA
end
end

