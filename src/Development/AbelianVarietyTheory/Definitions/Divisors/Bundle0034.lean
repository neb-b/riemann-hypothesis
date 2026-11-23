module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.HoweR

section Gl

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def IsGl (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ a b c d, F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)

def negT (F : ι → ι → Module.End ℂ M) : ι → ι → Module.End ℂ M := fun a b => -F b a

def cas (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b, if s a = s b then F a b * F b a else 0

def qop (F : ι → ι → Module.End ℂ M) (α β : ℂ) (a b : ι) : Module.End ℂ M :=
  ∑ c, F a c * F c b - α • F a b - if a = b then β • 1 else 0

def UnitOn (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) : Prop :=
  FiniteDimensional ℂ U ∧ (∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) ∧
    ∃ ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) ∧ (∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) ∧
      ∀ a b, s a = s b → ∀ x ∈ U, ∀ y ∈ U, ip (F a b x) y = ip x (F b a y)

def LocU (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ t : Finset M, ∃ U : Submodule ℂ M, (∀ x ∈ t, x ∈ U) ∧ UnitOn s F U

end Gl

section Act

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def units (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Ix p q → Ix p q → Module.End ℂ V := fun a b => act (Eab a b)

def Stab (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Prop := ∀ Z, ∀ y ∈ N, act Z y ∈ N

def Good (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  IsLieAct act ∧ (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) ∧ LocU (fun a : Ix p q => a.isLeft) (units act)

def QuadMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (α β α' β' : ℂ) (N N' : Submodule ℂ V) : Prop :=
  ∀ a b, ∀ v ∈ N', qop (units act) α β a b v ∈ N ∧ qop (negT (units act)) α' β' a b v ∈ N

def AdmMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) → hwSub act μ ≤ U ⊔ C

def CycMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∃ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ ∧ genSub act {v} ⊔ C = ⊤ ∧ hwSub act μ ≤ Submodule.span ℂ {v} ⊔ C

def Pack (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  Good act ∧ Stab act C ∧ (∃ α β α' β' : ℂ, QuadMod act α β α' β' C ⊤) ∧ AdmMod act C ∧ CycMod act C

end Act

def coinv (P Q R S : ℕ) (x : ℂ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Formalism.BasicNotions.TH.Pol P Q R S), g = fockAct1 P Q R S X f - (x * X.trace) • f}

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

def actAt {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) : Mat p q →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) ∘ₗ a

theorem actAt_apply {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (Z : Mat p q) :
    actAt w a Z = atPl w (a Z) := rfl

def tensAll (H : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∀ w, f w ∈ H w) ∧ y = PiTensorProduct.tprod ℂ f}

def tensAny (C : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∃ w, f w ∈ C w) ∧ y = PiTensorProduct.tprod ℂ f}

end Tensor

def HoweAlg {T : Type} {R S : T → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, (∀ w, Stab (a w) (N k)) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → N ≠ ⊤ → (∀ w, Stab (a w) N') → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

def inter {ι : Type} (U : ι → X.Opens) (s : Finset ι) : X.Opens := s.inf U

def cechFam {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X)
    (a : ℕ) : Finset ι → AddSubgroup (abelian₂ X.functionField) :=
  fun s => logSec (suppAll E) G a (inter 𝒜.U s)

def Decomp (p : ℕ) {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι]
    (𝒜 : SncAtlas E n ι) : Prop :=
  ∀ (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ a b : ℕ,
    DI.HypZero (extD X.functionField) (fun q => cechFam 𝒜 (p • G + ∑ c, r c • E c) q) (a + b) →
      DI.CechZero (cechFam 𝒜 G a) b

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.PairModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finite_levQc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (l : Level H) : Finite (LevQc Dw l) := by
  have hM : Mfr l ≠ ⊥ := by
    intro h
    have h₁ : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := (Mfr l).finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul (Mfr l) (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem hatC_phiHat {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}
    (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    inC c (phiHat c φ q) = hatC l (fun x => inC c (φ x)) q := by
  haveI := finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  have hz : inC c (zetaM c) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    rw [zetaM, map_pow]
    show zeta l.M' ^ (l.M' / l.M) = _
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have h0 : 0 < l.M := by have := l.three_le; omega
    have h1 : l.M' ≠ 0 := Nat.lcm_ne_zero h0.ne' l.A_pos.ne'
    have h2 : (m : ℂ) ≠ 0 := by rintro h; apply h1; rw [hm, Nat.cast_eq_zero.1 h, mul_zero]
    have h3 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [zeta, ← Complex.exp_nat_mul, hm, Nat.mul_div_cancel_left _ h0]
    congr 1
    push_cast
    field_simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [phiHat, hatC, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀, hz]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

end

end GlobalTheory.AdTh.PairModel
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type}

def dblAct (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) :
    (κ' ⊕ κ' → AF F) × (κ' ⊕ κ' → AF F) :=
  (Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).1 (s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).1,
    Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).2 (-(s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).2))

variable [Fintype κ] [Fintype κ']

structure IsOp (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ'
  pres' : ∀ φ ∈ schA F κ', S' φ ∈ schA F κ
  left : ∀ φ ∈ schA F κ, S' (S φ) = φ
  right : ∀ φ ∈ schA F κ', S (S' φ) = φ
  adm : ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ S ∈ (adeleClass F).adm κ
  adm' : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S' ∈ (adeleClass F).adm κ'
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (s w) (S φ)
  theta : ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F κ, thetaSum F (S φ) = c * thetaSum F φ
  norm : ∀ (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

def IsOp2 (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop :=
  IsOp ψ s S S' ∧ ∃ Sd Sd', IsOp ψ (dblAct s) Sd Sd' ∧
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, Sd (boxFun φ₁ φ₂) = boxFun (S φ₁) (star (S (star φ₂)))

end GlobalTheory.TowU

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HoweD

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}


variable (F) in
abbrev TensD (P Q R S : InfinitePlace F → ℕ) : Type := ⨂[ℂ] w : InfinitePlace F, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)

def FramedD (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMapD (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))

def IsGenD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (γ : Multiplicative ℝ →* UG (cA σ) J) (Y : ∀ w : InfinitePlace F, Mat (R w) (S w)) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsByD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : InfinitePlace F → ℕ}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (r w) (s w)) ℂ) (om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (act : ∀ w, Mat (r w) (s w) →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGenD τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act w (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxIs {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (σ : c.F →+* ℂ) {r g : ℕ} (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

def GenReads {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ} (U : Unf Xo c σ r) (k : U.Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : (U.X k).dom) (ϑ : (Fin g → ℂ) → ℂ) : Prop :=
  letI : Algebra c.F ℂ := σ.toAlgebra
  ∃ A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC (Formalism.L2.PjFree.Unf.ofPj U) k x),
    A.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) k x).s ϑ

variable {D : D7}

def AtComp (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D W → Σ k, Frame (X k).Ψ r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h γ : GA D W) : Prop :=
  γ ∈ GQ W ∧ latR hr (latG W (γ * h)) = (X (dict h).1).Λ ∧
    (dict h).2 = frMove θ W hr (X (dict h).1) (γ * h) (fun τ => x₀ τ.1)

def CcIs (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (mu : GA D W → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : U.Comp → ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ∀ h γ : GA D W, AtComp θ W hr U.X dict x₀ h γ →
    ∀ (hx' : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ)
      (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas →
      IdxIs c σ (U.X (dict h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U (dict h).1 bas idx e ⟨(dict h).2, hx'⟩ ϑ →
      ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X (dict h).1) bas idx (dict h).2
            (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b) (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)

theorem CcIs.norm {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc : U.Comp → ℂ}
    (h : CcIs θ V W hr U dict mu x₀ om f₀ cc) (k : U.Comp) : ‖cc k‖ = 1 := h.1 k

end

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.DI

def IsLifted (p : ℕ) {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (x : ι → Fin n → X.functionFieldˣ) : Prop :=
  ∃ (Kt : Type) (_ : CommRing Kt) (π : Kt →+* X.functionField) (F : ι → Kt →+* Kt),
    IsFlatLift p π ∧ (∀ i, IsFrob p π (F i)) ∧
    (∀ i l, ∃ z, π z = (x i l : X.functionField) ∧ F i z = z ^ p) ∧
    ∀ (y : X) (s : Finset ι), (∀ i ∈ s, y ∈ U i) → ∀ g : X.functionFieldˣ, LogDR.LogUnit Z y g →
      LogLift p π F s (LogDR.locRing y : Set X.functionField) (g : X.functionField)

def stalkIm {Y : Scheme.{0}} {η y : Y} (h : η ⤳ y) : Subring (Y.presheaf.stalk η) :=
  (Y.presheaf.stalkSpecializes h).hom.range

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι]

def zp (L : HermLB p) (n : ℤ) : HermLB p := (L.pow n.toNat).tens (L.pow (-n).toNat).dual

def comb (L : ι → HermLB p) (n : ι → ℤ) : HermLB p :=
  (Finset.univ : Finset ι).toList.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p)

def lin (n : ι → ℝ) : MvPolynomial ι ℝ := ∑ i, C (n i) * MvPolynomial.X i

def fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := LB.triv X
  isLB := LB.isLB_triv X
  φ σ := Weight.ofFun (u σ)
  cInf σ := fun _ y _ => hu σ y
  conj := hc

def chInt (L : HermLB p) (D : ℕ) (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : ℝ :=
  ∑ᶠ σ, (L.φ σ).chernInt D Set.univ (f σ)

def gdeg (L : HermLB p) (D : ℕ) : ℝ := chInt L D fun _ _ => 1

def IsArFun [IsIntegral X] (L : ι → HermLB p) (D : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, (comb L n).IsSelfInter (Φ (lin (fun i => (n i : ℝ)) ^ (D + 1)))) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0

def IsGeoFun (L : ι → HermLB p) (D : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) = gdeg (comb L n) D) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Ψ P = 0

def IsAlgPt (x : X) : Prop :=
  CharZero (X.residueField x) ∧ topologicalKrullDim (closure ({x} : Set X)) = 1

def IsPtHt (L : HermLB p) (x : X) (a : ℝ) : Prop :=
  ∃ h, L.IsArithHeight h ∧ h x = a * Nat.card (X.residueField x →+* ℂ)

def NefFib (L : HermLB p) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

def arVol (L : HermLB p) (D : ℕ) : EReal :=
  limsup (fun m : ℕ => ENNReal.log ((L.pow m).smallSec.encard : ENNReal) *
    ((((D + 1).factorial : ℝ) / (m : ℝ) ^ (D + 1) : ℝ) : EReal)) atTop

theorem nefFib_of_isNef {L : HermLB p} {D : ℕ} (h : L.IsNef D) : NefFib L := h.vertical

end GlobalTheory.ArInt
end
end

