module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RhoExA
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.RhoA

open Pb GlobalTheory.CompanionTheory.LiftLat

section Gr
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem pow_tf (c : b.R) (r : ℤ)
    (hT : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (n : ℕ)
    (T : Q.FullSubcategory) (x : (sP Q).A.obj T) (h : c ^ n • x ∈ (sFil Q r).S T) : x ∈ (sFil Q r).S T := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact hT T x (ih _ h)

theorem gr_part (c : b.R) (r : ℕ)
    (hT : ∀ (r : ℤ) (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (j k : ℕ)
    (h1 : ∀ (x : HG Q r (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : HG Q r j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → HG Q r j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : HG Q r j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, HGm Q (c ^ n) r j, (∀ n, trG Q c n r j (x (n + 1)) = x n) →
      ∃ z : HG Q r j, ∀ n, redG' Q (c ^ n) r j z = c ^ (2 * k) • x n) ∧
    ∀ z : HG Q r j, (∀ n, redG' Q (c ^ n) r j z = 0) → c ^ k • z = 0 := by
  have hle : ∀ T : Q.FullSubcategory, (sFil Q ((r : ℤ) + 1)).S T ≤ (sFil Q r).S T := fun T => T.obj.pdPow_anti (Nat.le_succ r)
  let red := fun n : ℕ => sqLe (a := sFil Q r) (b := sFil Q ((r : ℤ) + 1)) (a' := stdI Q (some (r : ℤ)) (c ^ n))
    (b' := stdI Q (some ((r : ℤ) + 1)) (c ^ n)) (fun _ => le_sup_left) fun _ => le_sup_left
  let tr := fun n : ℕ => sqLe (stdI_le Q (some (r : ℤ)) c n) (stdI_le Q (some ((r : ℤ) + 1)) c n)
  refine gen (G := fun n => sq (stdI Q (some (r : ℤ)) (c ^ n)) (stdI Q (some ((r : ℤ) + 1)) (c ^ n))) c red tr
    (fun n T => (red n).τ T) (fun n T => (tr n).τ T) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_ ?_ ?_ ?_ j k h1 h2 h3
  · intro n T x
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
    rfl
  · intro n T y
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    obtain ⟨u, hu⟩ := (mem_some Q r _ T y).1 hy
    refine ⟨sqMk _ _ _ hu, (sq_eq _ _ (Ideal.mem_sup_left hu) hy).2 ((mem_some Q _ _ T _).2 ⟨-u, ?_⟩)⟩
    rw [smul_neg, show y - c ^ n • u - y - -(c ^ n • u) = 0 by abel]
    exact zero_mem _
  · intro n T x
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e1 : (red n).τ T (sqMk _ _ w hw) = 0 ↔ w ∈ (stdI Q (some ((r : ℤ) + 1)) (c ^ n)).S T :=
      sqMk_eq_zero (stdI Q (some (r : ℤ)) (c ^ n)) _ w (Ideal.mem_sup_left hw)
    refine e1.trans ((mem_some Q _ _ T w).trans ⟨?_, ?_⟩)
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (sFil Q r).S T := pow_tf Q c r (hT r) n T y (by
        have := sub_mem hw (hle T hy)
        rwa [sub_sub_cancel] at this)
      exact ⟨sqMk _ _ y hy', (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy')).2 hy⟩
    · rintro ⟨y, h⟩
      obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      exact ⟨y, (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy)).1 h⟩
  · intro T x hx
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e2 := (sqMk_eq_zero _ _ (c • w) (Submodule.smul_of_tower_mem _ _ hw)).1 hx
    exact (sqMk_eq_zero _ _ w hw).2 (hT _ T w e2)

end Gr

theorem lift_gr (hA : AfgA) {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ) (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) (hO : TFBase (dividedPowersBot O) l m)
    (hL : LatBase γ l m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < m) (j : ℕ) :
    ∃ k : ℕ, (∀ x : ∀ n, HGm (TS γ q l m {⊤}) ((l : A) ^ n) r j, (∀ n, trG (TS γ q l m {⊤}) (l : A) n r j (x (n + 1)) = x n) →
      ∃ z : HG (TS γ q l m {⊤}) r j, ∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = (l : A) ^ (2 * k) • x n) ∧
    ∀ z : HG (TS γ q l m {⊤}) r j, (∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = 0) → (l : A) ^ k • z = 0 := by
  have hf := fun j => hA γ l m m hdv hO hL le_rfl q U {⊤} sSup_singleton r ((r : ℤ) + 1) (by omega) (by omega) j
  obtain ⟨k, a, b, d⟩ := bounds hL (hf j) (hf (j + 1))
  refine ⟨k, gr_part (TS γ q l m {⊤}) (l : A) r ?_ j k a b d⟩
  intro r T x h
  have e : (l : A) • x = (l : T.obj.B) * (show T.obj.B from x) := by
    rw [Algebra.smul_def, map_natCast]
  rw [e] at h
  exact T.property.1.2 _ _ h

theorem sub_trans {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂}
    (m : GlobalTheory.LogCris.Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a))
    (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hs : Function.Surjective c₁) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ₁ l X q κ₁) c₁ r).fn j) :
    (redSub q s 𝒱 d₂ c₂ lam hc₂ r).pull j ((pdOm m (RingHom.id Λ) h₀ r).pull j x) =
      trG (TS γ q l s 𝒱) (l : A) n r j ((redSub q s 𝒱 d₁ c₁ lam hc₁ r).pull j x) := by
  have hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x) := fun x => by
    obtain ⟨a, rfl⟩ := hs x
    rw [h₀, hc₁, hc₂]; rfl
  rw [pull_pull lam]
  change _ = (sqLe (stdI_le (TS γ q l s 𝒱) (some (r : ℤ)) (l : A) n) (stdI_le (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) (l : A) n)).pull j _
  rw [pull_pull lam]
  refine (CrystallineSemistableComparison.P.prism _ _ ⟨fun T => GlobalTheory.CompanionTheory.RedTrans.eta d₁ d₂ m hpt hρ T.obj T.property.1, fun T T' f => ?_⟩
    (fun T x => ?_) j x).symm
  · refine hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) x
    rfl

end CrystallineSemistableComparison.HT.RhoA
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmulMorPull
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.HomP

open Pb

section Gen
variable {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
  {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
  {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₄} {σ₃ : R₁ →+* R₃} {σ₄ : R₃ →+* R₄}

theorem sq4 (m₁ : CH.Mor F₁ F₂ σ₁) (m₂ : CH.Mor F₂ F₄ σ₂) (m₃ : CH.Mor F₁ F₃ σ₃) (m₄ : CH.Mor F₃ F₄ σ₄)
    (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hτ : ∀ (T : C₄) (x : F₁.obj (m₁.G.obj (m₂.G.obj T))),
      m₄.τ T (m₃.τ _ ((F₁.map (η.app T)).hom x)) = m₂.τ T (m₁.τ _ x)) (j : ℕ) (x : CH.H F₁ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  haveI : RingHomCompTriple σ₁ σ₂ (σ₂.comp σ₁) := ⟨rfl⟩
  haveI : RingHomCompTriple σ₃ σ₄ (σ₂.comp σ₁) := ⟨RingHom.ext hσ⟩
  rw [pull_pull (σ₂.comp σ₁), pull_pull (σ₂.comp σ₁)]
  exact CrystallineSemistableComparison.P.prism (m₁.comp m₂) (m₃.comp m₄) η hτ j x

def smulMor (c : R₂) (m : CH.Mor F₁ F₂ σ₁) : CH.Mor F₁ F₂ σ₁ where
  G := m.G
  τ T := { toFun := fun x => c • m.τ T x
           map_add' := fun x y => by rw [map_add (f := _), smul_add]
           map_smul' := fun r x => by rw [LinearMap.map_smulₛₗ, smul_comm] }
  nat φ x := by
    change c • m.τ _ _ = (F₂.map φ).hom (c • m.τ _ x)
    rw [m.nat, map_smul]

theorem smulMor_pull (c : R₂) (m : CH.Mor F₁ F₂ σ₁) (j : ℕ) (x : CH.H F₁ j) : (smulMor c m).pull j x = c • m.pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Gen

section Nl
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def nlHom {T T' : Thick (nlFun γ p X q κ)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r) (dp : IsDPMorphism T.δ T'.δ φ)
    (hpt : ∀ h, Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ h)) ≫ pt T = pt T') : T ⟶ T' :=
  mkH φ comm dp (Ideal.map_le_iff_le_comap.1 dp.1) (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun r => by
    have h1 : (show PtOver X q κ _ from T.y).1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
    have h2 : (show PtOver X q κ _ from T'.y).1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T'.J (T'.i r) := T'.w r
    change Ideal.quotientMap T'.J φ (Ideal.map_le_iff_le_comap.1 dp.1) ((show PtOver X q κ _ from T.y).1.1 (Ideal.Quotient.mk _ r)) =
      (show PtOver X q κ _ from T'.y).1.1 (Ideal.Quotient.mk _ r)
    rw [h1, h2, Ideal.quotientMap_mk, comm])) (hpt _)))

theorem spec_id {B₀ : Type} [CommRing B₀] (J : Ideal B₀) (h) {Z : Scheme.{0}} (y : Spec (CommRingCat.of (B₀ ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B₀) h)) ≫ y = y := by
  have e : Ideal.quotientMap J (RingHom.id B₀) h = RingHom.id _ := by ext; rfl
  rw [e, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end Nl

section S
variable {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
  {Φ₁ : PDF R₁ C₁} {Φ₂ : PDF R₂ C₂} {Φ₃ : PDF R₃ C₃} {Φ₄ : PDF R₄ C₄}
  {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₄} {σ₃ : R₁ →+* R₃} {σ₄ : R₃ →+* R₄}
  (m₁ : SMor Φ₁ Φ₂ σ₁) (m₂ : SMor Φ₂ Φ₄ σ₂) (m₃ : SMor Φ₁ Φ₃ σ₃) (m₄ : SMor Φ₃ Φ₄ σ₄)
  {a₁ b₁ : IdF Φ₁.A} {a₂ b₂ : IdF Φ₂.A} {a₃ b₃ : IdF Φ₃.A} {a₄ b₄ : IdF Φ₄.A}

theorem genA (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hρ : ∀ (T : C₄) (x : Φ₁.A.obj (m₁.G.obj (m₂.G.obj T))), m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom x)) = m₂.ρ T (m₁.ρ _ x))
    (h₁ : m₁.Le a₁ a₂) (k₁ : m₁.Le b₁ b₂) (h₂ : m₂.Le a₂ a₄) (k₂ : m₂.Le b₂ b₄) (h₃ : m₃.Le a₁ a₃) (k₃ : m₃.Le b₁ b₃)
    (h₄ : m₄.Le a₃ a₄) (k₄ : m₄.Le b₃ b₄) (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (m₂.sq h₂ k₂).pull j ((m₁.sq h₁ k₁).pull j x) = (m₄.sq h₄ k₄).pull j ((m₃.sq h₃ k₃).pull j x) := by
  refine sq4 (m₁.sq h₁ k₁) (m₂.sq h₂ k₂) (m₃.sq h₃ k₃) (m₄.sq h₄ k₄) hσ η (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) (hρ T y))

theorem genB (c₁ : R₂) (c c₄ : R₄) (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (hc : σ₂ c₁ = c * c₄) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hρ : ∀ (T : C₄) (x : Φ₁.A.obj (m₁.G.obj (m₂.G.obj T))), m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom x)) = m₂.ρ T (m₁.ρ _ x))
    (h₁ : m₁.LeC c₁ a₁ a₂) (k₁ : m₁.LeC c₁ b₁ b₂) (h₂ : m₂.Le a₂ a₄) (k₂ : m₂.Le b₂ b₄) (h₃ : m₃.Le a₁ a₃) (k₃ : m₃.Le b₁ b₃)
    (h₄ : m₄.LeC c₄ a₃ a₄) (k₄ : m₄.LeC c₄ b₃ b₄) (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (m₂.sq h₂ k₂).pull j ((m₁.sqC c₁ h₁ k₁).pull j x) = c • (m₄.sqC c₄ h₄ k₄).pull j ((m₃.sq h₃ k₃).pull j x) := by
  refine Eq.trans ?_ (smulMor_pull c (m₄.sqC c₄ h₄ k₄) j _)
  refine sq4 (m₁.sqC c₁ h₁ k₁) (m₂.sq h₂ k₂) (m₃.sq h₃ k₃) (smulMor c (m₄.sqC c₄ h₄ k₄)) hσ η (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  have e : c • (algebraMap R₄ _ c₄ * m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom y))) =
      m₂.ρ T (algebraMap R₂ _ c₁ * m₁.ρ (m₂.G.obj T) y) := by
    rw [hρ, map_mul, m₂.comm, hc, map_mul, Algebra.smul_def, mul_assoc]
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) e)

theorem genC {a₁' b₁' : IdF Φ₁.A} {a₂' b₂' : IdF Φ₂.A} (h : m₁.Le a₁ a₂) (k : m₁.Le b₁ b₂) (h' : m₁.Le a₁' a₂') (k' : m₁.Le b₁' b₂')
    (e₁ : ∀ T, a₁.S T ≤ a₁'.S T) (f₁ : ∀ T, b₁.S T ≤ b₁'.S T) (e₂ : ∀ T, a₂.S T ≤ a₂'.S T) (f₂ : ∀ T, b₂.S T ≤ b₂'.S T)
    (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (sqLe e₂ f₂).pull j ((m₁.sq h k).pull j x) = (m₁.sq h' k').pull j ((sqLe e₁ f₁).pull j x) := by
  refine sq4 (m₁.sq h k) (sqLe e₂ f₂) (sqLe e₁ f₁) (m₁.sq h' k') (fun _ => rfl) (𝟙 m₁.G) (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
  change m₁.ρ T ((Φ₁.A.map (𝟙 _)).hom y) = m₁.ρ T y
  rw [Φ₁.A.map_id]
  rfl

end S

section D
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)} {s s' : ℕ} {sA : A →+* A'}
  (nm : NMor γ q (κA O I) γ' q' (κA O I') sA)
  (hm : ∀ T, TS γ' q' l s' {⊤} T → TS γ q l s {⊤} ((nm.mor 0).obj T))
  (d : RedIn δ κ γ l n) (d' : RedIn δ κ γ' l n) {σ : R →+* R}
  (hd : ∀ (x : R) (a : A), d.ρ x = Ideal.Quotient.mk _ a → d'.ρ (σ x) = Ideal.Quotient.mk _ (sA a))
  (mm : GlobalTheory.LogCris.Mor (nlFun δ l X q κ) (nlFun δ l X' q' κ) σ)
  (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (nlFun δ l X' q' κ).Pt.obj B₀),
    (show PtOver X q κ B₀ from mm.pt.app B₀ y).1.2 = (show PtOver X' q' κ B₀ from y).1.2 ≫ nm.u)

theorem std_le (r : ℤ) : (nm.smor _ _ hm).Le (stdI (TS γ q l s {⊤}) (some r) ((l : A) ^ n)) (stdI (TS γ' q' l s' {⊤}) (some r) ((l : A') ^ n)) := by
  intro T x hx
  have e : T.obj.i (sA ((l : A) ^ n)) = T.obj.i ((l : A') ^ n) := by rw [map_pow sA, map_natCast]
  have hx' : (show T.obj.B from x) ∈ T.obj.pdPow r.toNat ⊔ Ideal.span {T.obj.i (sA ((l : A) ^ n))} := hx
  rw [e] at hx'
  exact hx'

include hd in
theorem r_comm (T : Thick (nlFun γ' 0 X' q' (κA O I'))) (x : R) :
    iBar ((nm.mor 0).obj T) l n (d.ρ x) = iBar T l n (d'.ρ (σ x)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d.ρ x)
  rw [hd x a ha.symm, ← ha]
  rfl

def rEta (T : (TS γ' q' l s' {⊤}).FullSubcategory) :
    (redG q s d {⊤}).obj ((nm.smor _ _ hm).G.obj T) ⟶ mm.obj ((redG q' s' d' {⊤}).obj T) :=
  nlHom (T := (redG q s d {⊤}).obj ((nm.smor _ _ hm).G.obj T)) (T' := mm.obj ((redG q' s' d' {⊤}).obj T))
    (RingHom.id (T.obj.B ⧸ lnT T.obj l n)) (r_comm nm d d' hd T.obj)
    (DPMorphism.id (redδ T.obj T.property.1 n)).isDPMorphism fun e => (spec_id _ e _).trans
      ((Category.assoc _ _ _).symm.trans (hpt _ ((redG q' s' d' {⊤}).obj T).y).symm)

def rNat : (nm.smor _ _ hm).G ⋙ redG q s d {⊤} ⟶ redG q' s' d' {⊤} ⋙ mm.functor where
  app := rEta nm hm d d' hd mm hpt
  naturality T T' f := hom_ext (show (RingHom.id (T'.obj.B ⧸ lnT T'.obj l n)).comp (lnMap f.hom.φ l le_rfl) =
    (lnMap f.hom.φ l le_rfl).comp (RingHom.id (T.obj.B ⧸ lnT T.obj l n)) from rfl)

include hd hpt in
theorem genD {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (lam' : Λ →+* A') (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (hc' : ∀ a, d'.ρ (c a) = Ideal.Quotient.mk _ (lam' a)) (sΛ : Λ →+* Λ) (hs : ∀ a, σ (c a) = c (sΛ a))
    (hl : ∀ a, lam' (sΛ a) = sA (lam a)) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ l X q κ) c r).fn j) :
    ((nm.smor _ _ hm).sq (std_le nm hm (r : ℤ)) (std_le nm hm ((r : ℤ) + 1))).pull j ((redSub q s {⊤} d c lam hc r).pull j x) =
      (redSub q' s' {⊤} d' c lam' hc' r).pull j ((pdOm (c := c) (c' := c) mm sΛ hs r).pull j x) := by
  have key := sq4 (F₁ := (B.pdS (nlFun δ l X q κ) c r).fn) (F₃ := (B.pdS (nlFun δ l X' q' κ) c r).fn)
    (redSub q s {⊤} d c lam hc r) ((nm.smor _ _ hm).sq (std_le nm hm (r : ℤ)) (std_le nm hm ((r : ℤ) + 1)))
    (pdOm (L := nlFun δ l X q κ) (L' := nlFun δ l X' q' κ) (c := c) (c' := c) mm sΛ hs r) (redSub q' s' {⊤} d' c lam' hc' r) hl
    (rNat nm hm d d' hd mm hpt)
  refine key (fun T x => ?_) j x
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  exact Subtype.ext rfl

end D

end CrystallineSemistableComparison.HT.HomP
end
end

