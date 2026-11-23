module

public import Mathlib
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SizeRows (large₂ : SizeData₂ D) : Prop :=
  (∃ (Pm : ParameterChoice' D large₂) (_ : ParamsT D large₂ Pm), Pm.CnW = 10) ∧ Formalism.MainNotions.SizesAt large₂ ∧
  D.R.m ^ 4 ≤ D.R.f ∧ 44 ≤ D.R.m ∧
  large₂.sc.x ^ 2 * (D.R.m : ℝ) ^ 3 * large₂.sc.L * Real.log D.host.rdE ≤ D.R.k ∧
  (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d ≤ large₂.sc.b ∧
  D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 ∧
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  Real.log (q0 D) ≤ large₂.sc.L ∧
  Real.log D.host.rdE ≤ Real.log (LevelStarExponents.condE D) ∧ Real.log (LevelStarExponents.condE D) ≤ large₂.sc.L / 100 ∧
  large₂.Sc + ((D.R.m : ℝ) + 1) * gap D 1 + 1 / 2 ≤ large₂.sc.b ∧
  (∀ τ l, 0 < (D.hc τ).b l ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b) ∧
  D.host.ccK = ⊤

section Columns

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D)

theorem posDef_dual (τ : D.what₂.Tau) : (((Xp G).gram.map (tauE D τ))⁻¹).transpose.PosDef := by
  exact ((posDef_Xp G (tauE D τ)).inv).transpose

def coefPlus : CoefA (G.V (.top 0)) :=
  GlobalTheory.CoefModel.coefOf (LaP G) (posDef_dual G) (invTrK.comp (GlobalTheory.CoefModel.realGL θ (Xp G)))

def levPlus : Subgroup (Bridge.Gf (G.V (.top 0))) := (Lev.toAfE _ G.Kplus).comap (finHom (G.V (.top 0))).range.subtype

def Cols : Submodule ℂ (Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W) :=
  Bridge.AdForms (Bridge.ratF (G.V (.top 0))) (coefPlus G θ).coef.ρ (levPlus G) 1

theorem mem_cols (Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W) : Ψ ∈ Cols G θ ↔
    ∀ (γ : GQ (G.V (.top 0))) g (k : levPlus G), Ψ (Bridge.ratF (G.V (.top 0)) γ * g * k) = (coefPlus G θ).ρ γ (Ψ g) := by
  unfold Cols Bridge.AdForms
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  rfl

end Columns

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : Consts}
  {G : GridData R.toLevCh sc} (W : G.Weil) (M : Vol G)

def rowForm (w : SmT (R.MY 0)) (t : Mult.MMap (R.MY 0)) : GA D (Yc D 0) → ℂ := PiTensorProduct.lift t w

def Separates (w : SmT (R.MY 0)) (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W) : Prop :=
  ∀ t ∈ R.EEat R.triv, t ≠ 0 → ∃ Ψ ∈ Cols G W.θ, ∃ Φ : G.Datum,
    FConv W M ρ ξ Ψ Φ (rowForm R w t) ∧ fPsiPhi W M ρ ξ Ψ Φ (rowForm R w t) ≠ 0

end Main

def FunctionalsSeparate : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    GlobalTheory.GLq.ESerTie D →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
      R.toLevCh.Is A.μ0 → R.grp_record →
      ∀ (G : GridData R.toLevCh ⟨1, CF, large₂.sc.b⟩) (W : G.Weil), W.Over R → ∀ M : Vol G, M.IsRow →
        ∀ w : SmT (R.MY 0), w ≠ 0 →
          ∃ (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W), Separates R W M w ρ ξ

end GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.WeilM
open GlobalTheory.Mem.Th (IsCuspForm)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def flatDet (ξ : (AE D)ˣ →* Circle) (V : HSp D) (g : GA D V) : ℂ := ξ (GlobalTheory.RecDict.exists_isDetRoot D V g).choose

abbrev UB {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) : Type := WeilTensorModels.UA D.sp.cm.sig J

abbrev incM {m n : Type} (J : Matrix m n D.host.E) : Matrix m n (AE D) := WeilTensorModels.incM D.host.F J

theorem mt_gram (V : HSp D) (g : GA D V) : ((mt V g).map (cA D))ᵀ * incM V.gram * mt V g = incM V.gram := g.2

theorem incM_smul {m n : Type} (c : D.host.E) (J : Matrix m n D.host.E) : incM (c • J) = incA D c • incM J := by
  ext a b
  simp only [incM, WeilTensorModels.incM, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

def conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) (g : GA D V) :
    UB J :=
  ⟨GeneralLinearGroup.map (cA D) (matHom V g), by
    have e : ((mt V g).map (cA D)).map (cA D) = mt V g := Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
    show ((mt V g).map (cA D))ᵀ * incM J * ((mt V g).map (cA D)).map (cA D) = incM J
    rw [e, h, incM_smul, Matrix.mul_smul, Matrix.smul_mul, mt_gram]⟩

theorem continuous_conj (D : D7) : Continuous (cA D) := by
  let f : AE D →ₗ[AF D.host.F] AE D :=
    TensorProduct.AlgebraTensorModule.map LinearMap.id D.sp.cm.sig.toLinearMap
  have hf : ⇑(cA D) = ⇑f := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [cA, sigR, f]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [hf]
  exact IsModuleTopology.continuous_of_linearMap f

theorem continuous_conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) :
    Continuous (conjU V c h) := by
  unfold conjU
  refine Continuous.subtype_mk ?_ _
  have hv : Continuous fun g : GA D V =>
      ((matHom V g : GL (Fin V.rank) (AE D)) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V =>
      (((matHom V g)⁻¹ : GL (Fin V.rank) (AE D)) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  rw [Units.continuous_iff]
  exact ⟨hv.matrix_map (continuous_conj D), hi.matrix_map (continuous_conj D)⟩

def blk {R : Type} [Zero R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) : Matrix (Fin d) (Fin d) R := reindex e e (fromBlocks A 0 0 B)

theorem blk_mul {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A A' : Matrix (Fin p) (Fin p) R)
    (B B' : Matrix (Fin q) (Fin q) R) : blk e A B * blk e A' B' = blk e (A * A') (B * B') := by
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]

theorem blk_one {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) :
    blk e (1 : Matrix (Fin p) (Fin p) R) 1 = 1 := by
  simp only [blk, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem blk_map {R R' : Type} [Zero R] [Zero R'] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) {f : R → R'} (h : f 0 = 0) : (blk e A B).map f = blk e (A.map f) (B.map f) := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [Matrix.map_zero _ h]

theorem blk_transpose {R : Type} [Zero R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) : (blk e A B)ᵀ = blk e Aᵀ Bᵀ := by
  simp only [blk, Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero]

def skewGram (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) : Matrix (Fin d) (Fin d) D.host.E :=
  D.host.xi0 • blk e A.gramᵀ B.gramᵀ

def blkU (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e) (x : GA D A × GA D B) : UB J :=
  ⟨⟨blk e (mt A x.1) (mt B x.2), blk e (mt A x.1⁻¹) (mt B x.2⁻¹),
    by simp only [Formalism.L2.Theta.mt, blk_mul, map_inv, Units.mul_inv, blk_one],
    by simp only [Formalism.L2.Theta.mt, blk_mul, map_inv, Units.inv_mul, blk_one]⟩, by
    have k : ∀ (V : HSp D) (g : GA D V), (mt V g)ᵀ * incM V.gramᵀ * (mt V g).map (cA D) = incM V.gramᵀ := fun V g => by
      have := congrArg transpose (mt_gram V g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have e1 : incM (blk e A.gramᵀ B.gramᵀ) = blk e (incM A.gramᵀ) (incM B.gramᵀ) := blk_map _ _ _ (map_zero _)
    show (blk e (mt A x.1) (mt B x.2))ᵀ * incM J * (blk e (mt A x.1) (mt B x.2)).map (cA D) = incM J
    rw [h, skewGram, incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1, blk_map _ _ _ (map_zero _), blk_transpose, blk_mul,
      blk_mul, k, k]⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def routeA (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.down t (i + 1) j) (.one (.right i (j + 1)))

def routeB (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.right i j) (.one (.down t i j))

variable (W : G.Weil) (M : Vol G)

variable (t : T) (i j : ℕ)


variable (G) in
abbrev spV : HSp D := G.V (.grid i (j + 1))


variable (G) in
abbrev spW : HSp D := G.V (.grid (i + 1) (j + 1))


variable (G) in
abbrev spW₁ : HSp D := G.V (.grid i j)


variable (G) in
abbrev spV₁ : HSp D := G.V (.grid (i + 1) j)


variable (G) in
def eps : ℕ := (spW₁ G i j).rank % 2


variable (G) in
def alpha : (AE D)ˣ →* Circle := L.mu t (j + 1) * L.eta ^ eps G i j


variable (G) in
def beta : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - i) * L.eta ^ eps G i j


variable (G) in
def xiV (g : GA D (spV G i j)) : ℂ := flatDet (L.eta ^ (2 * eps G i j))⁻¹ _ g


variable (G) in
def xiV₁ (g : GA D (spV₁ G i j)) : ℂ := flatDet (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ _ g


variable (G) in
abbrev Num : Type := Fin (spV G i j).rank ⊕ Fin (spV₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)


variable (G) in
abbrev Geo : Type := WeilTensorModels.Geo D.sp.cm.sig (spW G i j).rank (spW₁ G i j).rank

structure IsTripleOf (e : Num G i j) (B : WeilTensorModels.Base D.host.F D.host.E) (Γ : Geo G i j)
    (X : WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : B.ψ = W.ψ

  JW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram

  JWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e

  cart : ∀ w, ∃ τ, (∀ x, (B.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = W.cart (.grid (i + 1) (j + 1)) τ ∧
    Γ.V'.θ w = -W.cart (.grid i j) τ ∧
    Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj

  α : X.α = alpha G t i j

  β : X.β = beta G i j

  μW : Γ.M.μ = (M.ν (.grid (i + 1) (j + 1))).map (conjU _ 1 JW)

  μW₁ : Γ.M'.μ = (M.ν (.grid i j)).map (conjU _ (-1) JW₁)

variable {i j}

def mulG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : Matrix (Fin n) (Fin S.rank) (AE D) :=
  HMul.hMul x (incM S.gram)

def colV {n : ℕ} (e : Num G i j) (u : Matrix (Fin n) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin n) (Fin (spV G i j).rank) (AE D) := u.submatrix id fun k => e (.inl k)

def adjV₁ {n : ℕ} (e : Num G i j) (u : Matrix (Fin n) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin n) (Fin (spV₁ G i j).rank) (AE D) :=
  -mulG (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))

variable {t}

def boxA (e : Num G i j) (d : PureT G (routeA t i j))
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : ℂ :=
  (d.1.2 : Sch G (.right i (j + 1))) (mulG (negSp (spW G i j)) (colV e u)ᵀ) *
    (d.2 : Sch G (.down t (i + 1) j)) (adjV₁ e u)

def boxB (e : Num G i j) (d : PureT G (routeB t i j))
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : ℂ :=
  (d.1.2 : Sch G (.down t i j)) (mulG (spW₁ G i j) (colV e u)ᵀ) * (d.2 : Sch G (.right i j)) (adjV₁ e u)

def IsDatumA (e : Num G i j) (Γ : Geo G i j) (τ : TotT G (routeA t i j))
    (Φ : (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → AF D.host.F) → ℂ) : Prop :=
  Φ ∈ schA D.host.F _ ∧ ∀ u, thetaSum D.host.F (Γ.M.co.rho W.ψ u Φ) = τ.sum fun d c => c * boxA e d u

def IsDatumB (e : Num G i j) (Γ : Geo G i j) (τ : TotT G (routeB t i j))
    (Φ : (Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → AF D.host.F) → ℂ) : Prop :=
  Φ ∈ schA D.host.F _ ∧ ∀ u, thetaSum D.host.F (Γ.M'.co.rho W.ψ u Φ) = τ.sum fun d c => c * boxB e d u




theorem nonempty_num {μ0 : T} (hL : L.Is μ0) (hi : i + 1 ≤ D.R.m) (hj : j + 1 ≤ D.R.m) : Nonempty (Num G i j) := by
  have hr : ∀ X : Node, X.InRange D.R.m → (G.V X).rank = X.rank D := fun X hX => (node_isV G hL hX).rank
  have h1 := hr (.grid i (j + 1)) (by simp only [Node.InRange]; constructor <;> omega)
  have h2 := hr (.grid (i + 1) j) (by simp only [Node.InRange]; constructor <;> omega)
  have h3 := hr (.grid (i + 1) (j + 1)) (by simp only [Node.InRange]; constructor <;> omega)
  have h4 := hr (.grid i j) (by simp only [Node.InRange]; constructor <;> omega)
  have key : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
    rw [show (spV G i j).rank = _ from h1, show (spV₁ G i j).rank = _ from h2,
      show (spW G i j).rank = _ from h3, show (spW₁ G i j).rank = _ from h4]
    simp only [Node.rank, rankV]
    ring
  exact ⟨finSumFinEquiv.trans (finCongr key)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

end
end

