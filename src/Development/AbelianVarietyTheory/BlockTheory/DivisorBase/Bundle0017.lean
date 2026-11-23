module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

section Group

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {i d : ℕ}

def pairDet (l w : Fin i → Fin d → C) : C := (Matrix.of fun a b : Fin i => ∑ e, l b e * w a e).det

def IsFrameOf (v : AddValuation C (WithTop ℝ)) (u w : Fin i → Fin d → C) : Prop :=
  IsSatFrame v w ∧ ∀ a, w a ∈ Submodule.span C (Set.range u)

def HasChars (G : LogFGL v d) (u : Fin i → Fin d → C) (r : EReal) : Prop :=
  ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧
    ∀ w : Fin i → Fin d → C, IsFrameOf v u w → toE (v (pairDet l w)) ≤ r

theorem isFrameOf_self {u : Fin i → Fin d → C} (hu : IsSatFrame v u) : IsFrameOf v u u :=
  ⟨hu, fun a => Submodule.subset_span ⟨a, rfl⟩⟩

theorem v_pairDet_eq {u w : Fin i → Fin d → C} (hu : IsSatFrame v u) (hw : IsFrameOf v u w)
    (l : Fin i → Fin d → C) : v (pairDet l w) = v (pairDet l u) := by
  choose M hM using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (hw.2 a)
  have hwe : ∀ a e, w a e = ∑ k, M a k * u k e := fun a e => by
    rw [← hM a]; simp [Finset.sum_apply]
  have hmin : ∀ r : Fin i → Fin d, (Matrix.of fun a b => w a (r b)).det =
      (Matrix.of M).det * (Matrix.of fun a b => u a (r b)).det := fun r => by
    rw [← Matrix.det_mul]; congr 1; ext a b; simp [Matrix.mul_apply, hwe]
  have hint : ∀ (x : Fin i → Fin d → C), (∀ a e, IsIntV v (x a e)) → ∀ r : Fin i → Fin d,
      0 ≤ v (Matrix.of fun a b => x a (r b)).det := fun x hx r => by
    rw [Matrix.det_apply']
    refine AddValuation.map_le_sum v fun σ _ => ?_
    rw [AddValuation.map_mul]
    refine add_nonneg ?_ ?_
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · refine Finset.prod_induction _ (fun z => 0 ≤ v z) (fun a b ha hb => ?_) (by simp) fun k _ => hx _ _
      rw [AddValuation.map_mul]; exact add_nonneg ha hb
  obtain ⟨r, hr⟩ := hu.2
  obtain ⟨r', hr'⟩ := hw.1.2
  have h1 : 0 ≤ v (Matrix.of M).det := by
    have := hint w hw.1.1 r
    rwa [hmin, AddValuation.map_mul, hr, add_zero] at this
  have h2 : v (Matrix.of M).det ≤ 0 := by
    rw [hmin, AddValuation.map_mul] at hr'
    exact hr' ▸ le_add_of_nonneg_right (hint u hu.1 r')
  have h3 : pairDet l w = (Matrix.of M).det * pairDet l u := by
    unfold pairDet
    rw [← Matrix.det_mul]; congr 1; ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, hwe, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => by ring
  rw [h3, AddValuation.map_mul, le_antisymm h2 h1, zero_add]

theorem hasChars_iff {G : LogFGL v d} {u : Fin i → Fin d → C} (hu : IsSatFrame v u) (r : EReal) :
    HasChars G u r ↔ ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧ toE (v (pairDet l u)) ≤ r :=
  exists_congr fun l => and_congr_right fun _ =>
    ⟨fun h => h u (isFrameOf_self hu), fun h w hw => by rwa [v_pairDet_eq hu hw]⟩

end Group

section Prime

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def SplitInK (H : Host E) (p : ℕ) : Prop := (H.d : ZMod p) ≠ 0 ∧ IsSquare (-(H.d : ZMod p))

def InertInK (H : Host E) (p : ℕ) : Prop := ¬ IsSquare (-(H.d : ZMod p))

variable {H : Host E} {l : Level H} (c : Coeff l) {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime]
  (X : ValExt T p)

def embX (τ : E →+* ℂ) : 𝓞 E →+* X.C := X.ιF.comp (io.comp (embK c τ))

end Prime

end GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def boundAll (p i k : ℕ) : ℝ := (i : ℝ) * k / ((p : ℝ) - 1)

def boundInert (p j' i k : ℕ) : ℝ := 2 * (i : ℝ) * k / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * (j' : ℝ) * k / ((p : ℝ) - 1)

def upperInert (p N j' k : ℕ) : ℝ :=
  (k : ℝ) * ((j' : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j') * p / ((p : ℝ) ^ 2 - 1))

def boundFine (p N j' i k : ℕ) : ℝ :=
  (k : ℝ) * ((N : ℝ) - 2 * j' - i) * p / ((p : ℝ) ^ 2 - 1) +
    (k : ℝ) * j' * (3 + 1 / 2 * Real.logb p k) / ((p : ℝ) - 1) + (i : ℝ) ^ 2 * (Real.logb p k + 1)

variable {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
  {p : ℕ} [Fact p.Prime]

def AtEvery (la : PointsOfFlagModel.abelian₂ p c) (Q : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, Q T io y


def OscLe (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (b : ℝ) : Prop :=
  AtEvery Xo c la fun _ _ y => AtEvery Xo c la fun _ _ η => nuFac p y f k ≤ nuFac p η f k + (b : EReal)

end GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Col (cx : Lt1 Dw → ℕ) : Type := Σ f : {f : Lt1 Dw // cx f ≠ 0}, Fin (rk f.1)

abbrev Let (cx : Lt1 Dw → ℕ) : Type := Σ b : Col cx, Fin (rk b.1.1)

def polyH (C : Type) [Field C] (cx : Lt1 Dw → ℕ) : MvPolynomial (Let cx) C :=
  ∏ f : {f : Lt1 Dw // cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
    (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Let cx)) (detPow C (rk f.1) (cx f.1))

def blockCols (cx : Lt1 Dw → ℕ) : ℕ := ∑ f : {f : Lt1 Dw // cx f ≠ 0}, 2 * rk f.1

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
  {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ}
  (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)

def expH : (Σ _ : Col cx, Fin (chD Ch.ch)) → MvPowerSeries (Let cx) X.C :=
  expAlong (fun _ : Col cx => fgl Ch X) (fun b => frame Ch X b.1.1)

def colPt : Fin n × Fin (chD Ch.ch) → MvPowerSeries (Let cx) X.C := fun q =>
  subst (fun e : Fin (chD Ch.ch) => ∑ ℓ : Let cx,
    (jX X (B ℓ.1.1.1 ℓ.1.2 q.1) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
    (expOf (fgl Ch X) q.2)

def nuH_vp : EReal := depth (fun _ : Col cx => fgl Ch X) (fun b => frame Ch X b.1.1) (polyH X.C cx)

def nabX (k : ℕ) (g : PS X.C n (chD Ch.ch)) : X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra ℚ X.C := DivisionRing.toRatAlgebra
  nabValN Ch.ch.B X.C (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k g (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx))

def nuLocX_vp (k : ℕ) : EReal :=
  ⨅ g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g}, toE (vX_vp X (nabX Ch X cx B k g.1))

def Restricts (g : PS X.C n (chD Ch.ch)) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) : Prop :=
  subst (colPt Ch X cx B) g = subst (expH Ch X cx) f

def Trivial : Prop :=
  (∀ g, MvIsInt (vX_vp X) g → ∃ f, MvIsInt (vX_vp X) f ∧ Restricts Ch X cx B g f) ∧
  (∀ f, MvIsInt (vX_vp X) f → ∃ g, MvIsInt (vX_vp X) g ∧ Restricts Ch X cx B g f) ∧
  ∃ U : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) U ∧ constantCoeff U = 1 ∧
    ∀ (k : ℕ) g f, Restricts Ch X cx B g f →
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) (f * U ^ k))

def DepthEq : Prop :=
  nuH_vp Ch X cx = nuP p y cx ∧
  (∀ k : ℕ, nuLocX_vp Ch X cx B k = nuP p y cx) ∧
  (∀ k e : ℕ, vV T.V (p : T.Fr) = e → nuLocOf Ch e k (polyT B cx) = nuP p y cx) ∧
  0 ≤ nuP p y cx

end Chart


variable (Dw c) in
def ColsExist (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (cx : Lt1 Dw → ℕ) (n : ℕ), blockCols cx ≤ n →
    ∃ x : ℕ → ∀ f : Lt1 Dw, Fin (rk f) → Fin n → 𝓞 E,
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
        ∃ B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V, IsCols c T io p cx B ∧
          ∀ (N : ℕ) (f : Lt1 Dw) (b : Fin (rk f)) (j : Fin n), ∃ z : T.V,
            io (embK c f.1 (x N f b j)) = algebraMap T.V T.Fr (B f b j + (p : T.V) ^ N * z)



variable (Xo c) in
def LocalDepth (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ)
      (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B →
      Trivial Ch X cx B ∧ DepthEq Ch X cx B



end GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SplitQuadraticMinSums
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable {H : Host E} {Dw : Datum H}

def IsBig (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ k ≤ rk f + 1

def IsSpread (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ rk f + 2 ≤ k

def IsSmall (f : Lt1 Dw) : Prop := ¬ InPsi H f.1

theorem not_isBig_iff (k : ℕ) (f : Lt1 Dw) : ¬ IsBig k f ↔ IsSmall f ∨ IsSpread k f := by
  unfold IsBig IsSmall IsSpread
  by_cases h : InPsi H f.1
  · simp only [h, true_and, not_true, false_or]; omega
  · simp [h]


open Classical in
def sumBig (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ := ∑ f ∈ Finset.univ.filter (IsBig k), cx f


open Classical in
def sumSmallSpread (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f => IsSmall f ∨ IsSpread k f), rk f * cx f

section Place

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime]

end Place

end GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def IsIntHom {d d' : ℕ} (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
    (M : Matrix (Fin d') (Fin d) C) : Prop :=
  (∀ b, constantCoeff (φ b) = 0) ∧ (∀ b, MvIsInt v (φ b)) ∧
    ∀ b, subst φ (G'.lg b) = ∑ a, M b a • G.lg a

def intSpan (v : AddValuation C (WithTop ℝ)) {ι : Type} [Fintype ι] {d : ℕ} (u : ι → Fin d → C) : Set (Fin d → C) :=
  {x | ∃ a : ι → C, (∀ k, IsIntV v (a k)) ∧ x = ∑ k, a k • u k}

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def UnramIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop := ¬ (p : ℤ) ∣ discr E

def SplitInK (H : Host E) (p : ℕ) : Prop := (H.d : ZMod p) ≠ 0 ∧ IsSquare (-(H.d : ZMod p))

def InertInK (H : Host E) (p : ℕ) : Prop := ¬ IsSquare (-(H.d : ZMod p))

variable {Dw : Datum H} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embX (τ : E →+* ℂ) : 𝓞 E →+* X.C := X.ιF.comp (io.comp (embK c τ))

theorem v_embX_le_one (τ : E →+* ℂ) (a : 𝓞 E) : X.v (embX io X τ a) ≤ 1 := by
  have h1 : IsIntegral ℤ (embX io X τ a) := map_isIntegral_int _ (RingOfIntegers.isIntegral a)
  exact X.ints.isIntegral_iff_v_le_one.1 h1.tower_top

def primeBelow (τ : E →+* ℂ) : Ideal (𝓞 E) where
  carrier := {a | X.v (embX io X τ a) < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
    exact X.v.map_add_lt ha hb
  smul_mem' := fun a b hb => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hb ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_right (v_embX_le_one io X τ a) zero_le hb

def IsFrob (σ σ' : E →+* ℂ) : Prop :=
  ∀ a : 𝓞 E, X.v (embX io X σ' a - embX io X σ a ^ p) < 1

def IsOrbit (τ : E →+* ℂ) {h : ℕ} (lab : ZMod h → (E →+* ℂ)) : Prop :=
  lab 0 = τ ∧ (∀ s, IsFrob io X (lab s) (lab (s + 1))) ∧ Function.Injective lab ∧
    ∀ σ, primeBelow io X σ = primeBelow io X τ ↔ ∃ s, lab s = σ

def FrobOnType : Prop :=
  ∀ σ σ' : E →+* ℂ, IsFrob io X σ σ' →
    (SplitInK H p → (InPsi H σ' ↔ InPsi H σ)) ∧
    (InertInK H p → (InPsi H σ' ↔ InPsi H (ComplexEmbedding.conjugate σ)))

end Labels

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def IsPartAt (w : Ideal (𝓞 E)) {d' : ℕ} (G' : LogFGL (vX_vp X) d')
    (I : Matrix (Fin (chD Ch.ch)) (Fin d') X.C) (P : Matrix (Fin d') (Fin (chD Ch.ch)) X.C) : Prop :=
  (∃ ι, IsIntHom G' (fgl Ch X) ι I) ∧ (∃ π, IsIntHom (fgl Ch X) G' π P) ∧ P * I = 1 ∧
    ∀ ℓ : Lt1 Dw, (primeBelow io X ℓ.1 = w → (I * P).mulVec (lieVec Ch X ℓ) = lieVec Ch X ℓ) ∧
      (primeBelow io X ℓ.1 ≠ w → (I * P).mulVec (lieVec Ch X ℓ) = 0)


open Classical in
def TypedPartAt (τ : E →+* ℂ) : Prop :=
  ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧
  ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab ∧
  ∃ (d' : ℕ) (G' : LogFGL (vX_vp X) d') (ty : Fin d' → ZMod h)
    (I : Matrix (Fin (chD Ch.ch)) (Fin d') X.C) (P : Matrix (Fin d') (Fin (chD Ch.ch)) X.C),
    IsPartAt Ch X (primeBelow io X τ) G' I P ∧
    Nonempty (MuAction G' p h ty) ∧
    (∀ s, intSpan (vX_vp X) (fun b : {b : Fin d' // ty b = s} => fun e => I e b.1) =
      intSpan (vX_vp X) (fun k : Fin (Dw.mult (lab s)) => lieVec Ch X ⟨lab s, k⟩)) ∧
    (∀ s, Fintype.card {b : Fin d' // ty b = s} =
      if InPsi H (lab s) then Module.finrank (𝓞 E) Dw.La - Dw.q else Dw.q) ∧
    ∀ (s : ZMod h) (f : Lt1 Dw), f.1 = lab s →
      IsSatFrame (vX_vp X) (fun a => P.mulVec (frame Ch X f a)) ∧
      (∀ a b, ty b ≠ s → P.mulVec (frame Ch X f a) b = 0) ∧
      ∀ k : ℕ, nuFacC Ch X f k = detDepth G' (fun a => P.mulVec (frame Ch X f a)) k


def FormalGroupTypes : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (p : ℕ) [Fact p.Prime], UnramIn E p →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p),
      FrobOnType io X ∧
      ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ), TypedPartAt Ch X τ

end GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes
end
end

