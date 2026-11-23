module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FamGerm

structure Pt1 (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (F : Type) [Field F] [Algebra (FractionRing V) F] where
  ϖ : V
  hϖ : Irreducible ϖ
  complete : IsAdicComplete (maximalIdeal V) V
  t : SAB H (Sp V)
  P : PELUnif (maximalIdeal V) t
  tors : P.TorsionIso
  Q : P.D.toPre.X → ℤ
  hQ : QForm.IsQ P.D.toPre ϖ Q
  v : AddValuation F (WithTop ℚ)
  hv : ValOver ϖ F v
  d : ℕ
  x : JetSer.Fam t.G (Fin d)
  hx : Chart.IsUnivChart t.G d x
  j : P.U.LG.L.ι
  hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ P.U.LG.L.U j
  u : letI := H.starRing; ∀ a : 𝓞 E, LB.Gen (LB.LinComb P.U.LG.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε)
  hu : letI := H.starRing; ∀ a, JetSer.IsNormRos P.U.LG.L _ _ (u a)
  B : letI := H.starRing; FB V d (𝓞 E)
  hB : letI := H.starRing; JetSer.IsFBOf P.U.LG P.U.cubG t.act u x j B
  ρ : LB.Gen (LB.LinComb P.U.LG.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)
  hρ : ρ.IsGen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

def Pt1.Germ (q : ℕ) (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d) : Prop :=
  ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 y.P.U.LG.L q) (fi : Fin l → ∀ α, y.P.D.toPre.SecB q α) (g : Fin l → PS V 1 y.d) (r : PS V 1 y.d),
    (∀ i e, y.P.U.ExpandsAt e q (σ i) (fi i)) ∧
    (∀ α, GeneratorPullback.SecLin y.P.D.toPre.P.L (DegPre.famφ y.P.D.toPre F α) (DegPre.famε q) (s.s α) (y.P.D.toPre.famφB α) (DegPre.famε q)
      (fun i => fi i α) (DegPre.prB y.P.D.toPre F).left (fun i => scal (fst (TF (R := V) F) y.P.D.toPre.P.A).left (c i))) ∧
    JetSer.IsSer1 y.x _ (y.ρ.s (fun _ => y.j)).val r ∧
    (∀ i, ∃ S, JetSer.IsSer1 y.x _ ((σ i).f (fun _ => y.j)) S ∧ g i * r ^ q = S) ∧
    f = ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map (TWO.algVF (V := V) (F := F)) (g i)

def Pt1.Red (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) : Prop :=
  0 ≤ Cc ∧ 0 ≤ M₀ ∧ (∀ i, (y.Q (b i) : ℝ) ≤ Cc) ∧ ∀ i z, |(QForm.bOf y.P.D.toPre y.Q (b i) z : ℝ)| ≤ M₀ * y.Q z

def Pt1.Transl (q : ℕ) (c : 𝓞 E) (s h : Fam y.P.D.toPre F q) : Prop :=
  ∃ (p : QkPt y.P.D.toPre F q) (x : TFK (R := V) F ⟶ y.P.A.A)
    (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F) (t' : Fam y.P.D.toPre F q),
    y.P.ToA F q p x ∧ (letI := H.starRing; x ≫ y.P.oA.act c = 1) ∧ w.IsGen ∧ ζ ≠ 0 ∧ FinOrd y.P.D F q p w ζ ∧
      PhiRel y.P.D.toPre F q p w s t' ∧ Fam.IsSmul y.P.D.toPre F ζ t' h

def Pt1.CharAt (a : 𝓞 E) (p : ℕ) {Λ : Type} (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) : Prop :=
  letI := H.starRing
  ∃ (κ : (TFK (R := V) F ⟶ y.P.A.A) → Fˣ) (Z : Over (Spec (CommRingCat.of (TWO.Ov y.v)))) (jZ : Z.left ⟶ y.t.G.left) (k : Γ(Z.left, ⊤)),
    (∀ z z', z ≫ y.P.oA.act a = 1 → z' ≫ y.P.oA.act a = 1 → κ (z * z') = κ z * κ z') ∧
    IsFinite Z.hom ∧ Flat Z.hom ∧ IsReduced (Pdiv.specO (TWO.Ov y.v) F ⊗ Z).left ∧
    jZ ≫ y.t.G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (TWO.fO y.v y.hϖ y.hv)) ∧
    jZ ≫ (y.t.act.act a).left = jZ ≫ (1 : y.t.G ⟶ y.t.G).left ∧
    (∀ (c : Pdiv.specO (TWO.Ov y.v) F ⟶ Z) (z : TFK (R := V) F ⟶ y.P.A.A),
      (z ≫ y.P.U.gen.inv).left ≫ pullback.fst y.t.G.hom (jK V) = c.left ≫ jZ → JetSer.fnVal c.left ⊤ k = (κ z : F)) ∧
    ∀ l, ∃ (w : Pdiv.specO (TWO.Ov y.v) (DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})) ⟶ Z)
      (φ : Chart.JetR V (Fin y.d) 1 →+* DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})),
      (∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (Ideal.Quotient.mk _ (e l i))) ∧
      w.left ≫ jZ = Spec.map (CommRingCat.ofHom φ) ≫ (y.x 1).left ∧
      JetSer.fnVal w.left ⊤ k = 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk _ (yy l))

def Pt1.colVal [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}
    (P : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) : F :=
  letI := H.starRing
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, y.B.nabVal F h H.w0 q (f b) e (MvPolynomial.monomial (colM mo b) 1)

def minorsP (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n)
    (m : ∀ τ, Fin (r τ) → ℕ) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
  ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s

def GermExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∃ gm : Fam y.P.D.toPre F q →ₗ[F] PS F 1 y.d, ∀ s f, y.Germ q s f ↔ f = gm s

def GermValSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∀ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), y.Germ q s f → (∀ r : ℚ, (∀ χ, VGe y.P.D F y.v q χ (s.s χ) r) → ∀ mo, ((r : ℚ) : WithTop ℚ) ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ (χ : y.P.D.toPre.X) (x : F) (r r' : ℚ), Val0 y.P.D F q χ (s.s χ) x → y.v x = (r : ℚ) → r < r' → (∀ β, β ≠ χ → VGe y.P.D F y.v q β (s.s β) r') → y.v (MvPowerSeries.constantCoeff f) = (r : ℚ)

def JetsSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ q n : ℕ, 4 * n + 4 ≤ q → (n : ℝ) * M₀ < q → ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Cc / q ∧ ∀ g : PS F 1 y.d, (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) → ∃ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), NuGe y.P.D y.Q F y.v q s (-gm) ∧ y.Germ q s f ∧ (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g

def PullGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : 𝓞 E) → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∃ (w : PS V 1 y.d) (κ : Vˣ), FB.toK F w = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0) ∧ ∀ (s : Fam y.P.D.toPre F k) (s' : Fam y.P.D.toPre F (k * N)) (f : PS F 1 y.d), PullAl y.P.D F y.P.oD a k N s s' → y.Germ k s f → y.Germ (k * N) s' (MvPowerSeries.C (algebraMap V F κ) * (ev (n := 1) ![y.B.actK F a] f * FB.toK F w ^ k))

def EigGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (p k : ℕ), p.Prime → 4 ≤ k → a * star a = (p : 𝓞 E) → ∀ (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) (α : Λ → TWO.Ov y.v), (∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F)) → y.CharAt a p e yy → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), Nat.Coprime p k → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∃ (pt : QkPt y.P.D.toPre F (k * p)) (x : TFK (R := V) F ⟶ y.P.A.A), y.P.ToA F (k * p) pt x ∧ x ≫ y.P.oA.act (star a) = 1 ∧ ∀ (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b) (DegPre.lineε (k * p)))), w.IsGen → ∀ (s : Fam y.P.D.toPre F k) (s' t' : Fam y.P.D.toPre F (k * p)) (c : F), PullAl y.P.D F y.P.oD a k p s s' → PhiRel y.P.D.toPre F (k * p) pt w s' t' → (∀ χ, VGe y.P.D F y.v (k * p) χ ((c • t').s χ) 0) → ∀ (h : PS F 2 y.d) (ω : PS V 1 y.d), y.B.IsCanonGauge F h → FB.toK F ω = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0) → ∀ f : PS F 1 y.d, y.Germ (k * p) (c • t') (f * FB.toK F ω ^ k) → ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) f - MvPowerSeries.C (yy l : F) * f))

section Basic₂

section ColVal
variable [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}

end ColVal

end Basic₂

end GlobalTheory.FamGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
section
namespace GlobalTheory.TopVec

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

def tv {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) :
    PiLp 2 (fun _ : Wd.Ix (Fin w.length) × M.Ty P => PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ) •
      B.hsVec ((p.TP.E x.2).comp (p.V (p.Θ.Θ w x.1 H) (TBB.bigPt P.r c)))

end

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.SameFns
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section alg

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def hats {r : ℕ} (L : LevelData A r) : Set A :=
  Set.range L.Ahat ∪ Set.range L.R0 ∪ Set.range L.Ahatv ∪ Set.range L.R0v

def SameFns {r : ℕ} (L L' : LevelData A r) : Prop :=
  L.p = L'.p ∧ L.pb = L'.pb ∧ L.c = L'.c ∧ L.ci = L'.ci ∧ L.cb = L'.cb ∧ L.cbi = L'.cbi ∧ L.ζ = L'.ζ ∧ L.ζi = L'.ζi ∧
    L.ζb = L'.ζb ∧ L.ζbi = L'.ζbi ∧ L.GG = L'.GG ∧ L.GGi = L'.GGi ∧ L.TT = L'.TT

def MulRel {r : ℕ} (L : LevelData A r) (m : ℕ → A) : Prop :=
  ∀ q, (∀ f ∈ L.fns, Commute f (m q)) ∧ (∀ l, L.p l * m q = m q * L.p l + m (q + 1)) ∧
    (∀ l, L.pb l * m q = m q * L.pb l + m (q + 1)) ∧
    L.nab * m q = m q * L.nab + L.ζb * L.GGi * m (q + 1) ∧
    L.nabs * m q = m q * L.nabs - L.ζ * L.GGi * m (q + 1)

variable {P : M.Par}

def ssn (d : Q.NFData P A) (l : ℕ) : A := d.L.Drb * d.L.Dri * d.SS l

def bset (d : Q.NFData P A) : Set A :=
  {d.L.ζi, d.L.ζbi, d.L.D * d.L.Dbi, d.L.Db * d.L.Di} ∪ Set.range d.κ ∪
    ssn d '' Set.Icc 1 (P.k - 1) ∪ (fun l => star (ssn d l)) '' Set.Icc 1 (P.k - 1)

def bmon (d : Q.NFData P A) : Submonoid A := Submonoid.closure (bset d)

def HatHyp (d : Q.NFData P A) : Prop :=
  P.OK ∧ IsStarLevel d.L ∧ d.Rel ∧ (∀ l, star (d.L.p l) = -d.L.pb l) ∧ (∀ l, star (d.L.c l) = d.L.cb l) ∧
    (∀ l, star (d.L.ci l) = d.L.cbi l) ∧ ∀ f : M.Ty P → ℂ, ∀ g ∈ TL.siteOps d.L, Commute (d.κ f) g

def Comparison₂ (d : Q.NFData P A) (L : LevelData A P.r) (st : Start A) (s : ℂ) : Prop :=
  TL.AHyp L st ∧ SameFns L d.L ∧ (s = 1 ∨ s = -1) ∧ (∀ Y, st.QQ Y = s • d.QQ Y) ∧
    st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}

def nfSpan (d : Q.NFData P A) (T : Set A) (i j n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ b ∈ bmon d, ∃ H : List A, H.length = n ∧ (∀ h ∈ H, h ∈ T) ∧
    x = b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod}

def rh (d : Q.NFData P A) (y : ℂ) : A := d.L.Drb * (d.QQ y 1 0 * d.L.Ar y + d.QQ y 1 1 * d.L.Br y)

def rhv (d : Q.NFData P A) (y : ℂ) : A := d.L.Dr * (d.QQ y 0 1 * d.L.Avr y + d.QQ y 1 1 * d.L.Bvr y)

def basics (d : Q.NFData P A) : Set A :=
  {x | ∃ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) ∧
    (x = d.L.Ahat y ∨ x = d.L.Ahatv y ∨ x = rh d y ∨ x = rhv d y)}

end alg

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

abbrev RA (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Type := Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')

def nv {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : ℝ :=
  ‖B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)‖

def IsNF {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (RA P Bs)) : Prop :=
  Q.IsActualLevel X d.L ∧ IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def PtB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (b : RA P Bs) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    nv (b.1 Φ) x ≤ C * nv Φ x

def PtAdj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (b : RA P Bs) : Prop :=
  ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    B.hsInner ((b.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
      B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) (((star b).1 Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)

def gR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r) : ℝ :=
  Complex.normSq (∏ a, c a) * Q.GGl P.k P.r Bs.z Bs.z' g

def dR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r) : ℝ :=
  ‖(∏ a, c a) * P5.zeta P.k P.r Bs.z Bs.z' g‖

def IsMulG (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ → ℝ)
    (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ q, P5.multiplicationOperator (W q) fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ)

end actual

end

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
section
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BpJoin

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData BranchingSupport

def Pst {n : ℕ} (lam : Fin n → ℝ) (c : ℝ) (y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)

def GridNum (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  1 ≤ c ∧ c + 2 ≤ b ∧ (P.k : ℝ) ≤ b ∧ |P.u l| ≤ b ∧ |P.u' l| ≤ b ∧ (∀ s, |lam s| ≤ b) ∧
  (∀ s t, s < t → lam t + 2 * c ≤ lam s) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T ∧ b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T'

def StdNum (C b c : ℝ) (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  (∀ l ∈ Icc 1 P.k, GridNum C b c P l lam) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    lam s + 1 / 2 ≤ P.u (s.val + 1) ∧ P.u (s.val + 2) + 1 / 2 ≤ lam s ∧
    lam s + 1 / 2 ≤ P.u' (s.val + 1) ∧ P.u' (s.val + 2) + 1 / 2 ≤ lam s)

def Cases (P : M.Par) (n₀ : ℕ) : Prop :=
  (n₀ = 0 ∧ ∃ l ∈ Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) ∨
  (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Icc 1 P.k, P.u i = P.u' i) ∧
    ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1))

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigDec {k r : ℕ} (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  B.CkOn ⊤ (B.GV k r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧
    ∀ y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (y : ℂ) f g = ((∏ s, (y + mu s) : ℝ) : ℂ) • f g

end BpJoin
end
end

