module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct

namespace GlobalTheory.ShFam

section Pull

variable {X Z : Scheme.{0}} [IsIntegral X] (B : EffCartierData Z) (f : X ⟶ Z)
  (h : f (genericPoint X) ∉ B.idealSheaf.support)

def pullEqn (i : B.ι) {y : X} (hy : f y ∈ B.U i) : X.functionFieldˣ :=
  have hg : genericPoint X ∈ f ⁻¹ᵁ B.U i := gen_mem (x := y) hy
  Units.mk0 (fnOf (f ⁻¹ᵁ B.U i) hg (f.app _ (B.f i))) (UnitAt.ne_zero ((unitAt_fnOf_iff hg _ _).2 (by
    rw [← Scheme.preimage_basicOpen]
    exact not_not.1 (mt (B.mem_support_iff i hg).2 h))))

theorem germOf_pullEqn {i i' : B.ι} {y : X} (hi : f y ∈ B.U i) (hi' : f y ∈ B.U i') :
    germOf y (pullEqn B f h i hi) = germOf y (pullEqn B f h i' hi') := by
  obtain ⟨u, hu⟩ := ((B.associated_germ i i' _ hi hi').map (f.stalkMap y).hom)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hu
  have e := congrArg (algebraMap _ X.functionField) hu
  rw [map_mul, algebraMap_germ (U := f ⁻¹ᵁ B.U i) hi, algebraMap_germ (U := f ⁻¹ᵁ B.U i') hi'] at e
  exact germOf_eq_iff.2 ⟨u, u.isUnit, (eq_div_iff (Units.ne_zero _)).2 ((mul_comm _ _).trans e)⟩

def pullDiv : CartierDiv X :=
  show cartierGroup X from ⟨fun y => germOf y (pullEqn B f h _ (B.exists_mem (f y)).choose_spec), fun y =>
    ⟨f ⁻¹ᵁ B.U _, (B.exists_mem (f y)).choose_spec, pullEqn B f h _ (B.exists_mem (f y)).choose_spec,
      fun _ hz => germOf_pullEqn B f h _ hz⟩⟩

end Pull

section Comb

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def qDiv {C : CxSt F} (A : Adl C Y) : ℚ ⊗[ℤ] Y.Dv := ((A.n : ℕ) : ℚ)⁻¹ ⊗ₜ A.D



omit [NumberField F] in
def curvMet {σ : F →+* ℂ} {Δ : Y.Dv} (m : Var.Met Y σ Δ) : ChartForm Y.str σ Y.dim :=
  fun c y => ddcForm (m.wt (Var.eqn Δ y)) c y

variable {ι : Type} [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ) (g : ∀ σ, Pts Y σ → ℝ)

def combDen : ℕ+ := ⟨∏ i, (t i / ((ρ i).n : ℕ)).den, Finset.prod_pos fun _ _ => Rat.den_pos _⟩

def combNum (i : ι) : ℤ := ((combDen ρ t : ℕ) * (t i / ((ρ i).n : ℕ))).num

theorem combNum_mul (i : ι) : (combNum ρ t i : ℚ) * ((ρ i).n : ℕ) = (combDen ρ t : ℕ) * t i := by
  obtain ⟨c, hc⟩ : (t i / ((ρ i).n : ℕ)).den ∣ (combDen ρ t : ℕ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e : ((combDen ρ t : ℕ) : ℚ) * (t i / ((ρ i).n : ℕ)) = ((c * (t i / ((ρ i).n : ℕ)).num : ℤ) : ℚ) := by
    rw [hc, Nat.cast_mul, mul_right_comm, Rat.den_mul_eq_num, mul_comm, Int.cast_mul, Int.cast_natCast]
  rw [combNum, e, Rat.num_intCast, ← e, mul_assoc, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (ρ i).n.ne_zero)]

def combEqn (x : Y.X) : Y.Fnˣ := ∏ i, eqn (ρ i).D x ^ combNum ρ t i

def comb : Adl (cxSt F) Y where
  D := ∑ i, combNum ρ t i • (ρ i).D
  n := combDen ρ t
  m σ := show Var.Met Y σ _ from
    { h := fun e y => ‖Var.tv e (combEqn ρ t (under y)) y‖ ^ 2 *
        Real.exp (2 * (∑ i, combNum ρ t i * lnAdl (ρ i) σ y - (combDen ρ t : ℕ) * g σ y))
      nonneg := fun _ _ => by positivity
      trans := fun e e' y he he' => by rw [← mul_assoc, ← mul_pow, ← norm_mul, Var.tv_mul he he'] }
  ci := 0
  lg v e y := Real.log (e.w (valAt y.1 (combEqn ρ t (below y.1) /
    eqn (∑ i, combNum ρ t i • (ρ i).D) (below y.1) : Y.Fn))) + ∑ i, combNum ρ t i * (ρ i).lg v e y

theorem qDiv_comb : qDiv (comb ρ t g) = ∑ i, t i • qDiv (ρ i) := by
  simp only [qDiv, comb, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', zsmul_eq_mul,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => congrArg (· ⊗ₜ _) ?_
  have h₁ : ((combDen ρ t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (combDen ρ t).ne_zero
  have h₂ : (((ρ i).n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (ρ i).n.ne_zero
  field_simp
  rw [combNum_mul]

end Comb

section Weights

variable {T : Type} {N : ℕ}

def varpi (j : ℕ) (i : Fin N) : ℚ := if (i : ℕ) < j then 0 else -1


open Classical in
def fund (τ : T) (i : Fin N) : T → Fin N → ℝ := fun τ' a => if τ' = τ ∧ a ≤ i then 1 else 0

def coef (u : T → Fin N → ℝ) (τ : T) (i : Fin N) : ℝ := if h : (i : ℕ) + 1 < N then u τ i - u τ ⟨i + 1, h⟩ else u τ i

def ratOf (r : ℝ) : ℚ := Classical.epsilon fun q : ℚ => r = q

end Weights

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

theorem mem_support_BD_iff (k : s.Comp) (y : (Φ.C k).Y.X) :
    ((Φ.C k).π ≫ genι s.T.Z) y ∈ s.T.BD.idealSheaf.support ↔ (Φ.C k).π y ∈ genBd s.T.Z :=
  ⟨fun h => mem_genBd_iff.2 (s.T.BD_supp _ h), s.T.BD_pos _⟩

def bdPull (k : s.Comp) : (Φ.C k).Y.Dv :=
  pullDiv s.T.BD ((Φ.C k).π ≫ genι s.T.Z) fun h => CartierDiv.genericPoint_notMem_supp (Φ.C k).bd
    (((Φ.C k).bd_supp _).2 ((mem_support_BD_iff Φ k _).1 h))


variable (S) in
abbrev rootExp (x : DV.Rt D.what₂.Tau N) : Letter S.Dw → ℤ := rootEx S.Dw (DV.tauEmb D x.1) x.2

def qL (k : s.Comp) (u : D.what₂.Tau → Fin N → ℚ) : ℚ ⊗[ℤ] (Φ.C k).Y.Dv :=
  -∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 ⊗ₜ divOf (Φ.C k) (rootExp S x)

abbrev RefMets : Type :=
  ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

def offBd (k : s.Comp) (σ : D.what₂.LL →+* ℂ) : Set (Pts (Φ.C k).Y σ) := {y | (Φ.C k).π (under y) ∉ genBd s.T.Z}


open Classical in
def extBd {k : s.Comp} {σ : D.what₂.LL →+* ℂ} (f : Pts (Φ.C k).Y σ → ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  if y ∈ offBd Φ k σ then f y else limsup f (𝓝[offBd Φ k σ] y)

variable {Φ} (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (h0 : RefMets Φ)

def phW (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  2 * ∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 * lnRatio (hm k none σ (rootExp S x)) (h0 k σ (rootExp S x)) y

def thW (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) : ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim :=
  fun c y ξ => -∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 * curvMet (h0 k σ (rootExp S x)) c y ξ

def CommonConst (om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim) (E : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim)
    (a K δ : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ K ∧ 0 < δ ∧ ∀ k σ τ (i : Fin N), (i : ℕ) + 1 < N →
    IsRegConst (om k σ) (thW h0 k σ (fund τ i)) (rho (om k σ) (E k σ) (phW hm h0 k σ (fund τ i))) a K δ


variable (s) in
def dirOf (b : ℕ) (η : ℚ) (μ : Fin N → ℤ) : D.what₂.Tau → Fin N → ℚ :=
  fun _ i => (2 * b * s.T.m0 : ℕ) * varpi j i + η * μ i


variable (s Φ) in
structure PolDat : Type where

  b : ℕ
  b_pos : 0 < b

  η : ℚ
  η_pos : 0 < η

  μ : Fin N → ℤ
  μ_anti : StrictAnti μ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y
  ab_div : ∀ k, qDiv (ab k) = qL Φ k (dirOf s b η μ) - 1 ⊗ₜ (b • bdPull Φ k)
  ab_ample : ∀ k, (Φ.C k).Y.ample (ab k).D
  ab_model : ∀ k, ∃ (M : TrueGeo.Model (Φ.C k).Y) (L : HermLB M.p) (q : ℕ+), (ab k).Induced M L q 0 ∧ ArInt.NefFib L
  ab_smooth : ∀ k σ, (cxSt D.what₂.LL).mSmooth _ σ _ ((ab k).m σ)

  om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim
  om_kaehler : ∀ k σ, IsKaehlerForm ((Φ.C k).Y.an σ) (om k σ)
  om_conj : ∀ k σ σ' (ι : Pts (Φ.C k).Y σ' → Pts (Φ.C k).Y σ), IsConjMap ι → ∀ W φ,
    IsPotential ((Φ.C k).Y.an σ) (om k σ) W φ → IsPotential ((Φ.C k).Y.an σ') (om k σ') (ι ⁻¹' W) (φ ∘ ι)

  c₀ : ℝ
  c₀_pos : 0 < c₀
  curv_ge : ∀ k σ (c : AlgChart (Φ.C k).Y.str σ (Φ.C k).Y.dim), ∀ y ∈ c.e.source, ∀ ξ,
    c₀ * om k σ c y ξ ≤ curvMet ((ab k).m σ) c y ξ / ((ab k).n : ℕ)

  exph : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim
  exph_is : ∀ k σ, IsExph (om k σ) (exph k σ)
  exph_conj : ∀ k σ σ' (ι : Pts (Φ.C k).Y σ' → Pts (Φ.C k).Y σ), IsConjMap ι → ConjComm ι (exph k σ) (exph k σ')

  a : ℝ

  K : ℝ

  δ : ℝ
  const : (∃ a' K' δ', CommonConst hm h0 om exph a' K' δ') → CommonConst hm h0 om exph a K δ

namespace PolDat

variable {hm h0} (P : PolDat s Φ hm h0)

def m : ℕ := 2 * P.b * s.T.m0

def bd (k : s.Comp) : (Φ.C k).Y.Dv := P.b • bdPull Φ k

def dirQ : D.what₂.Tau → Fin N → ℚ := dirOf s P.b P.η P.μ

def dir : D.what₂.Tau → Fin N → ℝ := fun τ i => P.dirQ τ i

def regFund (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin N) (t : ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  if (i : ℕ) + 1 < N then rho (P.om k σ) (P.exph k σ) (phW hm h0 k σ (fund τ i)) y t + P.K * t ^ 2
  else extBd Φ (phW hm h0 k σ (fund τ i)) y

def reg (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (t : ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  ∑ τ, ∑ i, coef u τ i * P.regFund k σ τ i t y

variable (k : s.Comp) (σ : D.what₂.LL →+* ℂ)

def gens (B : ℝ) : Option (DV.Rt D.what₂.Tau N) → Adl (cxSt D.what₂.LL) (Φ.C k).Y := fun o => o.elim (P.ab k) fun x =>
  adlOf (Φ.C k) (fun _ => h0 k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D x.1) x.2)

def mbarQ (B : ℝ) (u : D.what₂.Tau → Fin N → ℚ) (r : ℚ) : Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  comb (P.gens k B) (fun o => o.elim r fun x => -(u x.1 x.2 - r * P.dirQ x.1 x.2))
    fun σ y => P.reg k σ (fun τ i => u τ i - r * P.dir τ i) (Real.exp (-((r : ℝ) ^ 2)⁻¹)) y / 2

end PolDat

variable {hm h0}


open Classical in
def mbarOf (P : PolDat s Φ hm h0) (B : ℝ) (u : D.what₂.Tau → Fin N → ℝ) (r : ℚ) (k : s.Comp) :
    Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  if (∀ τ i, ∃ q : ℚ, u τ i = q) ∧ 0 < r then P.mbarQ k B (fun τ i => ratOf (u τ i)) r else Adl.triv _ _

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop

def anyGeometry : GeoP := fun _ _ _ => True

section Reading

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def OverIx (Z : R3.ReadL R F X0 Y) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((Z.jW i) '' ((R3.s0Of R F).Wp i c : Set (Fin ((R3.s0Of R F).dW i) → D.what₂.LL)))

def LamAre (Z : R3.ReadL R F X0 Y) (Xd : DivX D) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, OverIx Z σ c) → OverIx Z σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        Xd.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → Xd.logLam ((i : ℕ) + 1) σ e = 0)

end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure OAt (Γ : GeoP) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)
    (X : DivX (w.D Z)) : Type 1 where
  geo : Γ (w.st Z).toD7 t.r.z.core.toCore X
  lam : LamAre t.r.Z X

def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X

end GlobalTheory.Mem.Top.Bl

end
end

