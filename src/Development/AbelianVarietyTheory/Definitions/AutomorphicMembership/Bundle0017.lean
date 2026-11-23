module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalDualModel
section
set_option autoImplicit false
noncomputable section
open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix
namespace GlobalTheory.GoodMetric.PolyRep
variable {ι : Type} {m : ι → ℕ}


set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in
theorem _root_.GlobalTheory.GoodMetric.PolyRep.lie_proj_model [Fintype ι] (τ : ι) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) : (_root_.GlobalTheory.GoodMetric.PolyRep.proj m τ).lie A = A τ := by
  classical
  ext i j
  simp [_root_.GlobalTheory.GoodMetric.PolyRep.lie, _root_.GlobalTheory.GoodMetric.PolyRep.proj, pderiv_X, Pi.single_apply]
  rfl

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in
private lemma aeval_dualNumber_inl_add_inr {σ : Type} [Fintype σ] {R : Type} [CommRing R]
    (x y : σ → R) (p : MvPolynomial σ ℤ) :
    aeval (fun v => (TrivSqZeroExt.inl (x v) + TrivSqZeroExt.inr (y v) : DualNumber R)) p
      = TrivSqZeroExt.inl (aeval x p) + TrivSqZeroExt.inr (∑ v, aeval x (pderiv v p) * y v) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => ext <;> simp
  | add p q hp hq =>
    rw [map_add (f := _), hp, hq]
    ext <;> simp [Finset.sum_add_distrib, add_mul]
  | mul_X p v hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
        Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
        Finset.sum_add_distrib]
      simp [Pi.single_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, add_comm]


set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in
theorem _root_.GlobalTheory.GoodMetric.PolyRep.ev_dual_model [Fintype ι] (ρ : _root_.GlobalTheory.GoodMetric.PolyRep m) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) (i j : Fin ρ.M) :
    ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : _root_.GlobalTheory.FlagBundle.Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b)) i j
      = TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) i j) + TrivSqZeroExt.inr (ρ.lie A i j) := by
  have h1 := congrFun (congrFun (ρ.one R) i) j
  simp only [_root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply] at h1
  simp only [_root_.GlobalTheory.GoodMetric.PolyRep.ev, _root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply, Matrix.of_apply,
    _root_.GlobalTheory.GoodMetric.PolyRep.lie]
  refine (aeval_dualNumber_inl_add_inr (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => (1 : _root_.GlobalTheory.FlagBundle.Mat m R) v.1 v.2.1 v.2.2)
    (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => A v.1 v.2.1 v.2.2) _).trans ?_
  rw [h1]

end GlobalTheory.GoodMetric.PolyRep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ColDictLReTr
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) : Transport (reX Z X) u F' where
  wt := T.wt
  wt_isom := T.wt_isom
  wt_e := T.wt_e
  wt_f := T.wt_f
  weight_z := T.weight_z
  ιA := T.ιA
  ιA_rat := T.ιA_rat
  ιA_int := T.ιA_int
  h0 := T.h0
  hc := T.hc
  hc_rep := fun c => by rw [hy]; exact T.hc_rep c
  J := T.J
  J_eqv := T.J_eqv
  J_val := T.J_val
  J_isom := fun c ξ η => by rw [he]; exact T.J_isom c ξ η


set_option maxHeartbeats 4000000 in
theorem colDictL_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (hK : X.LevelSubgroupCharacter) (x : Cu X u hK) :
    colDictL (reX Z X) (reTr Z T hy he) hK x = colDictL X T hK x := by
  funext c z
  show T.J (shP X u x.1 (T.hc c)) (F'.val0.eY z) = T.J (shP X u x.1 (T.hc c)) (F.val0.eY z)
  rw [he]
  rfl

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CxStage
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.ProjVar.Var

namespace GlobalTheory.ProjVar

def cxStage (F : Type) [Field F] [NumberField F] : TrueGeo.CxSt F where
  borel _ _ := inferInstance
  vol := vol
  FnC := FnC
  cx := cx
  cx_smul := cx_smul
  Met := Met
  mAdd Y σ Δ Δ' := mAdd Y σ Δ Δ'
  mPow Y σ Δ := mPow Y σ Δ
  fsMet Y σ Δ := fsMet Y σ Δ
  pn Y σ Δ := pn Y σ Δ
  pnK Y σ Δ := pnK Y σ Δ
  mSmooth Y σ Δ := mSmooth Y σ Δ
  mPsh Y σ Δ := mPsh Y σ Δ
  redZero Y σ Δ := redZero Y σ Δ
  agreeOn Y σ Δ := agreeOn Y σ Δ
  resNorm Y σ Δ := Var.resNorm Y σ Δ
  regOn Y σ Δ := regOn Y σ Δ
  ofWeight Y σ Δ L r := Var.ofWeight Y σ Δ L r
  pn_ofWeight Y σ Δ L r h φ f y i hi _ := by rw [Var.pn_ofWeight h φ (mem_ptsIn.2 hi), fval_cx]
  pn_mAdd Y σ Δ Δ' m m' f f' y h h' := by
    rw [map_mul, Var.pn_mAdd (secReg_cx_iff.2 h) (secReg_cx_iff.2 h')]
  pn_mPow Y σ Δ k m f y h := by rw [map_pow, Var.pn_mPow (secReg_cx_iff.2 h.regularAt)]
  pn_mul Y σ Δ m a f y ha h := by
    rw [map_mul, Var.pn_mul (regC_cx_iff.2 ha) (secReg_cx_iff.2 h), val_cx]
  pn_fs Y σ Δ ι κ _ _ b X f y g hg hb _ _ := by
    have e (k) := hasVal_sum_smul (y := y) hg (fun i => secReg_cx_of_mem (hb i) y) fun i => X i k
    rw [pn_fsMet (fun k => (secReg_iff hg).2 (e k).regC) hg, fval_cx]
    simp only [fval, fun k => (e k).val_eq, ← map_mul, val_cx]

end GlobalTheory.ProjVar
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EHHre
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def reTR {X : HidaSetting D} (T : TypedRed X) : TypedRed (reX Z X) := { T with }


set_option maxHeartbeats 4000000 in
def reCS {X : HidaSetting D} {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u what₂) :
    ColSys (reX Z X) u what₂ := { c with }


set_option maxHeartbeats 4000000 in
def eHHre (X : HidaSetting D) : HHX X ≃ₗᵢ[ℂ] HHX (reX Z X) := LinearIsometryEquiv.refl ℂ (HHX X)

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F] (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (w : Fin n → Y.Fn) (c : Fin Y.dim → Fin n → 𝓞 E)

def GeomPt : Type :=
  {y : Sp (AlgebraicClosure E) ⟶ Y.X // y ≫ Y.str = spMap ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))}

def GenAt (x : Y.X) (k : Fin n) : Prop := w k ≠ 0 ∧ ∀ l, RegAt x (w l / w k)

def coef (i : Fin Y.dim) (l : Fin n) : AlgebraicClosure E := algebraMap E _ (c i l : E)

def cutSet : Set (GeomPt Y E) :=
  {y | ∀ k, GenAt Y w (below y.1) k → ∀ i, ∑ l, coef Y E c i l * valAt y.1 (w l / w k) = 0}

def IsTangent (y : GeomPt Y E) (δ : Y.X.presheaf.stalk (below y.1) →+ AlgebraicClosure E) : Prop :=
  (∀ a b, δ (a * b) = (Scheme.stalkClosedPointTo y.1).hom a * δ b + (Scheme.stalkClosedPointTo y.1).hom b * δ a) ∧
    ∀ (a : Y.X.presheaf.stalk (below y.1)) (t : F), algebraMap _ Y.Fn a = algebraMap F Y.Fn t → δ a = 0

def ReducedAt (y : GeomPt Y E) : Prop :=
  ∀ k, GenAt Y w (below y.1) k → ∀ u : Fin n → Y.X.presheaf.stalk (below y.1),
    (∀ l, algebraMap _ Y.Fn (u l) = w l / w k) → ∀ δ, IsTangent Y E y δ →
      (∀ i, ∑ l, coef Y E c i l * δ (u l) = 0) → δ = 0

def cutGood (bd : Y.Cl) : Prop :=
  (∀ x, ∃ k, GenAt Y w x k) ∧ (cutSet Y E w c).Finite ∧
    ∀ y ∈ cutSet Y E w c, ReducedAt Y E w c y ∧ below y.1 ∉ bd

def cutHt {C : CxSt F} (A : Adl C Y) : ℝ := ∑ᶠ y ∈ cutSet Y E w c, A.ht (below y.1)

def cutOrd (Δ : Y.Dv) (f : Y.Fn) : ℕ :=
  sSup {a : ℕ | ∀ y ∈ cutSet Y E w c, ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
    algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn)}

def cutSt [StarRing F] (C : CxSt F) : CutSt C where
  cutGood := fun Y bd E _ _ _ _ w c => cutGood Y E w c bd
  cutHt := fun Y A E _ _ _ _ w c => cutHt Y E w c A
  cutOrd := fun Y E _ _ _ _ w c Δ f => cutOrd Y E w c Δ f

end GlobalTheory.TrueGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def castV {A B : HLat K} (h : A = B) : A.V ≃ₗ[K] B.V := by
  subst h
  exact LinearEquiv.refl K A.V

def unitLat (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) : HLat K :=
  HLat.ofCoord (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))) fun _ => 1

theorem ofCoord_good {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ}
    (hL : Submodule.IsFullLattice K L) (hX : ∀ v, IsUnit (X v).det) : (HLat.ofCoord L X).Good :=
  ⟨hX, hL.toIsLattice.fg, hL.span_eq_top⟩

theorem unitLat_good (n : ℕ) : (unitLat K n).Good :=
  ⟨fun _ => by
      show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
      rw [Matrix.det_one]; exact isUnit_one,
    Submodule.fg_span (Set.finite_range _),
    (Submodule.span_span_of_tower (𝓞 K) K (Set.range (Pi.basisFun K (Fin n)))).trans (Pi.basisFun K (Fin n)).span_eq⟩

def unitMap (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    (unitLat K (Module.finrank ℂ W)).V →ₛₗ[σ] W :=
  (lin (stdOrthonormalBasis ℂ W)).comp (cptL σ (Module.finrank ℂ W))

theorem unitMap_b (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (k : Fin (Module.finrank ℂ W)) :
    unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k) = stdOrthonormalBasis ℂ W k := by
  have h : cptL σ (Module.finrank ℂ W) (Pi.basisFun K _ k) = Pi.single k 1 := by
    funext i
    by_cases hi : i = k <;> simp [cptL, cpt, hi]
  exact (congrArg (lin (stdOrthonormalBasis ℂ W)) h).trans (lin_single _ k)

theorem unitMap_basis (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    LinearIndependent ℂ (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) ∧
      Submodule.span ℂ (Set.range fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = ⊤ := by
  have h : (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = (stdOrthonormalBasis ℂ W).toBasis :=
    funext fun k => unitMap_b σ W k
  rw [h]
  exact ⟨(stdOrthonormalBasis ℂ W).toBasis.linearIndependent, (stdOrthonormalBasis ℂ W).toBasis.span_eq⟩

theorem hLatTie_castV {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ} {A : HLat K}
    (h : HLat.ofCoord L X = A) : HLatTie A L X (castV h) := by
  subst h
  exact ⟨(Submodule.map_id L).symm, fun _ _ _ => rfl⟩

variable {m : ℕ} {d : Fin m → ℕ} (M : ∀ i, Submodule (𝓞 K) (Fin (d i) → K))
  (X : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ)
  (W : ℕ → Type) [∀ j, NormedAddCommGroup (W j)] [∀ j, InnerProductSpace ℂ (W j)] [∀ j, FiniteDimensional ℂ (W j)]

def latSeq : ℕ → HLat K
  | 0 => unitLat K (Module.finrank ℂ (W 0))
  | j + 1 => if h : j < m then HLat.ofCoord (M ⟨j, h⟩) (X ⟨j, h⟩) else unitLat K (Module.finrank ℂ (W (j + 1)))

theorem latSeq_succ (i : Fin m) : latSeq M X W ((i : ℕ) + 1) = HLat.ofCoord (M i) (X i) := dif_pos i.2

theorem latSeq_off {j : ℕ} (h : j = 0 ∨ m < j) : latSeq M X W j = unitLat K (Module.finrank ℂ (W j)) := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

variable {σ : K →+* ℂ} (f : ∀ i : Fin m, (Fin (d i) → K) →ₛₗ[σ] W ((i : ℕ) + 1))

def mapSeq : ∀ j, (latSeq M X W j).V →ₛₗ[σ] W j
  | 0 => unitMap σ (W 0)
  | j + 1 =>
    if h : j < m then (f ⟨j, h⟩).comp (castV (latSeq_succ M X W ⟨j, h⟩)).toLinearMap
    else (unitMap σ (W (j + 1))).comp (castV (latSeq_off M X W (Or.inr (Nat.lt_succ_of_le (Nat.le_of_not_lt h))))).toLinearMap

theorem mapSeq_succ (i : Fin m) :
    mapSeq M X W f ((i : ℕ) + 1) = (f i).comp (castV (latSeq_succ M X W i)).toLinearMap := dif_pos i.2

theorem mapSeq_off {j : ℕ} (h : j = 0 ∨ m < j) :
    mapSeq M X W f j = (unitMap σ (W j)).comp (castV (latSeq_off M X W h)).toLinearMap := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

theorem castV_ind {H : Type} [AddCommGroup H] [Module ℂ H] (P : ∀ A : HLat K, (A.V →ₛₗ[σ] H) → Prop) {A B : HLat K} (h : A = B)
    {g : B.V →ₛₗ[σ] H} (hg : P B g) : P A (g.comp (castV h).toLinearMap) := by
  subst h
  exact hg

theorem mapSeq_ind (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [mapSeq_succ]
  exact castV_ind (P _) _ (hP i)

theorem mapSeq_ind_all (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i))
    (h0 : ∀ j, P j (unitLat K (Module.finrank ℂ (W j))) (unitMap σ (W j))) (j : ℕ) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  by_cases h : j = 0 ∨ m < j
  · rw [mapSeq_off M X W f h]
    exact castV_ind (P _) _ (h0 j)
  · exact mapSeq_ind M X W f P hP j (by omega) (by omega)

theorem map_castV {H : ℕ → HLat K} {g : ∀ j, (H j).V →ₛₗ[σ] W j} (hH : H = latSeq M X W) (hg : HEq g (mapSeq M X W f))
    (i : Fin m) (h : HLat.ofCoord (M i) (X i) = H ((i : ℕ) + 1)) (x : Fin (d i) → K) :
    g ((i : ℕ) + 1) (castV h x) = f i x := by
  subst hH
  obtain rfl := eq_of_heq hg
  rw [mapSeq_succ]
  have key : ∀ {A B : HLat K} (h : A = B) (h' : B = A) (y : A.V), castV h' (castV h y) = y := by
    intro A B h h' y
    subst h
    rfl
  exact congrArg (f i) (key h _ x)

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

open MjCoord

def mjLat (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ℕ → HLat D.what₂.LL :=
  latSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj

def mjH (_Z : ReadL R F X0 Y) (j : ℕ) : HLat D.what₂.LL := mjLat R F j

def jM (Z : ReadL R F X0 Y) (j : ℕ) : (mjH Z j).V →ₛₗ[D.what₂.embLL] D.what₂.Mj j :=
  mapSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj Z.jW j

variable (Z : ReadL R F X0 Y)

theorem mjH_succ (i : Fin D.R.m) : mjH Z ((i : ℕ) + 1) = HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i) :=
  latSeq_succ _ _ _ i

theorem mjH_good (hH : Holds R F) (j : ℕ) : (mjH Z j).Good :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW (fun _ A _ => A.Good)
    (fun i => by
      exact ofCoord_good (hH.prim.mLat i) fun v =>
        frame_gram_unit _ (RealDat3.kForm_of (F := F) hH.prim.unif false i v).1)
    (fun _ => unitLat_good _) j

theorem jM_basis (hH : Holds R F) (j : ℕ) : LinearIndependent ℂ (fun k => jM Z j ((mjH Z j).b k)) ∧
    Submodule.span ℂ (Set.range fun k => jM Z j ((mjH Z j).b k)) = ⊤ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => LinearIndependent ℂ (fun k => g (A.b k)) ∧ Submodule.span ℂ (Set.range fun k => g (A.b k)) = ⊤)
    (fun i => by
      have h : (fun k => Z.jW i ((HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i)).b k)) = fun k => Z.jW i (Pi.single k 1) :=
        funext fun k => congrArg (Z.jW i) (Pi.basisFun_apply _ _ k)
      exact h ▸ jW_basis Z hH i)
    (fun _ => unitMap_basis _ _) j

theorem jM_lat (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    x ∈ (mjH Z j).L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      jM Z j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun j A g => ∀ x : A.V, x ∈ A.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      g x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v)
    (fun i => (jW_lat Z hP hH i).2) j h1 h2 x

theorem mjLat_sub (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range (jM Z j) :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW (fun j _ g => ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range g)
    (fun i => (jW_lat Z hP hH i).1) j h1 h2

theorem jM_metric (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => jW_norm Z hH i) j h1 h2 x

def mjIds (Xd : DivX D) (h : Xd.MjH = mjH Z) : MjHIds D A3.A Xd (A3.indefDown (s0Of R F)) where
  eW i := castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem mjHTie_of_eq (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW (mjIds Z Xd h) := by
  constructor
  · intro i x
    exact map_castV _ _ D.what₂.Mj Z.jW h hj i _ x
  · intro i
    exact hLatTie_castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem exists_mjHTie (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    ∃ JM, MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM :=
  ⟨_, mjHTie_of_eq Z Xd h hj⟩

section Reface

variable {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {kap : ℝ} {lam : type_of% R.lam3} {err : type_of% (R.updS kap lam).err0}
  {Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}
  (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y')

end Reface

end GlobalTheory.Mem.R3

end
end

