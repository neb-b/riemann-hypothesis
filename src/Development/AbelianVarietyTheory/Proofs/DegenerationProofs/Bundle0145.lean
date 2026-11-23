module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionValuedFieldTwistedUniformisation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait.LevelClause

theorem qEq_twist {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {u r : Oˣ} {j : ℕ} (h : r ^ j = u)
    {p q : N.QT j} {p' q' : (N.twist β u).QT j} (e : N.QEq p q) (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (χ : N.X) => ?_)⟩
  · rw [hp.1, hq.1]; exact h1
  · rw [hq.2.1, h2, NumD.Gt.mul_b, NumD.Gt.mul_b, hp.2.1]; rfl
  · have e₁ : (N.twist β u).τ z χ = N.τ z χ * u ^ β.be z χ := N.twist_τ β u z χ
    have e₂ : r ^ β.be (p.1.1.toAdd + j • z) χ = r ^ β.be p.1.1.toAdd χ * u ^ β.be z χ := by
      rw [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, zpow_add, nsmul_eq_mul, zpow_mul,
        zpow_natCast, h]
    have e₃ : (p'.1.2 * (N.twist β u).io z).s χ =
        p'.1.2.s χ * (N.twist β u).τ z χ / N.θ (N.c χ) (show N.A from p'.1.2.b) (N.c z) := rfl
    refine (hq.2.2 χ).trans (Eq.trans ?_ e₃.symm)
    rw [h1, h2, e₁, e₂, hp.2.2 χ, hp.2.1, NumD.Gt.mul_s, NumD.io_s, NumD.io_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem exists_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), ?_⟩, rfl, I.rel_img _⟩
  have a := (I.rel_img p.1.2).pow k
  rw [hp] at a
  exact (I.rel_existsUnique _).unique a (I.rel_io _)

theorem qEq_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (e : N.QEq p q) (hp : p'.1.1.toAdd = J.e p.1.1.toAdd) (hp' : J.Rel p.1.2 p'.1.2)
    (hq : q'.1.1.toAdd = J.e q.1.1.toAdd) (hq' : J.Rel q.1.2 q'.1.2) : N'.QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, by rw [hq, hp, h1, map_add (f := _), map_nsmul], ?_⟩
  have a : I.Rel (p.1.2 * N.io z) (p'.1.2 * N'.io (J.e z)) := NumD.Hom.Rel.mul (I := I) hp' (I.rel_io z)
  rw [← h2] at a
  exact (I.rel_existsUnique _).unique (show I.Rel _ _ from hq') a

theorem genRel_of_gauge {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (ht : t.IsGen)
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (ht₀ : t₀.IsGen) (x : F) (hpt : ∀ k, pt k ≫ φ = pt₀ k)
    (J : (Sp F ⟶ B₀) → M₀.ι) (J' : (Sp F ⟶ B) → M.ι) (gJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M₀.U (J ψ)) (gJ' : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M.U (J' ψ))
    (hv : (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) * vF t (𝟙 _) J' = x * vF t₀ (𝟙 _) J) :
    GenRel w t t₀ x := by
  obtain rfl : pt₀ = fun k => pt k ≫ φ := funext fun k => (hpt k).symm
  have z : Sp F := (default : PrimeSpectrum F)
  rw [genRel_iff w t t₀ x z]
  refine ⟨fun _ => rfl, fun j j₀ h₀ h₁ => ?_⟩
  have hJ := fun ψ => (top_le_iff_mem _ _ z).1 (gJ ψ)
  have hJ' := fun ψ => (top_le_iff_mem _ _ z).1 (gJ' ψ)
  have hp : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have hp' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (𝟙 _ ≫ pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ _
  have hq : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have hq' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (𝟙 _ ≫ pt k)) := Set.mem_iInter.2 fun k => hJ' _
  have P1 := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z hp hp' hq hq'
  have G1 := gen_trans ht (𝟙 _) z hq hq'
  have G0 := gen_trans ht₀ (𝟙 _) z hp hp'
  have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val) =
      (gw w (pt k) z (J (pt k ≫ φ)) (J' (pt k))).val := fun k =>
    toStk_valF (pt k) ((M₀.pull φ).U (fun _ => J (pt k ≫ φ)) ⊓ M.U (J' (pt k))) z ⟨mem_pull.2 (hJ (pt k ≫ φ)), hJ' _⟩ _
  have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) =
      (pw w pt ε (𝟙 _) z (fun k => J (𝟙 _ ≫ pt k ≫ φ)) (fun k => J' (𝟙 _ ≫ pt k))).val := by
    simp only [pw, Category.id_comp]
    rw [map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hu : valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ≠ 0 := fun h0 => by
      have := a₃ k
      rw [h0, map_zero] at this
      exact Units.ne_zero _ this.symm
    have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ hu) = gw w (pt k) z _ _ := Units.ext (a₃ k)
    rw [← e, ← map_zpow]
    show _ = toStk z _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e' := congrArg (toStk z) hv
  rw [map_mul, map_mul, a₄] at e'
  have b₁ : toStk z (vF t (𝟙 _) J') = _ := toStk_valF _ _ z hq' _
  have b₀ : toStk z (vF t₀ (𝟙 _) J) = _ := toStk_valF _ _ z hp' _
  rw [b₁, b₀, ← Units.val_mul] at e'
  have hpw : (∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) = pw w pt ε (𝟙 _) z j₀ j := by
    simp only [pw, Category.id_comp]
  have step : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c * (b * d) = a * (c * d) := fun a b c d => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hpw, P1, G1, G0, step, Units.val_mul, e', Units.val_mul]
  exact mul_left_comm _ _ _

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) (b : N.A) (χ : N.X) (i : Fin 4) :
    DegPre.gtφ D F (ν.eA b) (ν.eX χ) i = (ν.eA (![N.c χ * b, N.c χ, b, 1] i)).left := by
  fin_cases i
  · show _ = (ν.eA (N.c χ * b)).left
    rw [map_mul, ν.c_eq]; rfl
  · show _ = (ν.eA (N.c χ)).left
    rw [ν.c_eq]; rfl
  · rfl
  · show _ = (ν.eA 1).left
    rw [map_one]; rfl

theorem level_clause : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  intro _ hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hTI ψ w e hF k hk hkM hL p₀ v hp₀ z hz
  obtain ⟨-, hw, hA, hX, hne, hh⟩ := hF
  have hrk := hr.pow hk
  obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt (F' := C) a.bimult (algebraMap (FractionRing O') C)
    (RingHom.ext fun _ => rfl) p₀
  obtain ⟨-, -, -, -, B₀⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B₁⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨v₀, hv₀, -⟩ := (B₀ k).1 q₀
  have e₀ := ((B₀ k).2.2 _ _ _ _ hv₀ (A.hq k v)).1 (hp₀ q₀ hq₀)
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_twRel A.be u (r k) hrk v₀
  obtain ⟨t₁, ht₁, -⟩ := existsUnique_twRel A.be u (r k) hrk (A.q k v)
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_image J t₀
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_image J t₁
  obtain ⟨q, hq⟩ := (B₁ k).2.1 s₀
  obtain ⟨p', hp'⟩ := (B₁ k).2.1 s₁
  have e₁ := ((B₁ k).2.2 _ _ _ _ hq hp').2 (qEq_image J (qEq_twist A.be hrk e₀ ht₀ ht₁) hs₀ hs₀' hs₁ hs₁')
  refine ⟨q₀, q, hq₀, ?_, fun χ => ?_, ?_⟩
  · rw [← hq.1, ← hv₀.1, hX, hs₀, ht₀.1]
    rfl
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective χ
    have hb : q.g.b = ν'.eA (J.φ v₀.1.2.b) := by rw [← hq.2.1, hs₀'.1, ht₀.2.1]
    have hc : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
    have g₁ : ∀ i, DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i =
        (ν'.eA (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i))).left := fun i => by
      rw [hb, hX, gtφ_eq, hc]
      fin_cases i
      · exact congrArg (fun x => (ν'.eA x).left) (map_mul J.φ _ _).symm
      · rfl
      · rfl
      · exact congrArg (fun x => (ν'.eA x).left) (map_one J.φ).symm
    refine genRel_of_gauge w hw _ (q.g.isGen _) _ (q₀.g.isGen _) _ (fun i => ?_) A.ν.J ν'.J A.ν.good ν'.good ?_
    · rw [g₁, hA, ← hv₀.2.1, gtφ_eq]
    · have g₂ : ∀ i, valF (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i) _
          (w.s (fun _ => A.ν.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i ≫ ψ),
            ν'.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i))).val =
          wVal ν' A.ν w (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i)) := fun i =>
        congrArg (fun p : Sp C ⟶ M.P.D.toPre.P.A.left => valF p _ (w.s (fun _ => A.ν.J (p ≫ ψ), ν'.J p)).val) (g₁ i)
      have g₃ : vF (q.g.s (e (A.ν.eX χ))) (𝟙 (Sp C)) ν'.J = (s₀.1.2.s (J.e χ) : C) :=
        (congrArg (fun y => vF (q.g.s y) (𝟙 (Sp C)) ν'.J) (hX χ)).trans (hq.2.2 _).symm
      have g₄ := (hv₀.2.2 χ).symm
      have g₅ : (u : C) ^ (a.be q₀.y (A.ν.eX χ) / k) = (r k ^ A.be.be v₀.1.1.toAdd χ : Cˣ) := by
        rw [← hv₀.1, ← A.be_eq, ← hrk, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
          mul_comm, A.be.div_mul hkM]
      have g₆ : s₀.1.2.s (J.e χ) * J.h (A.N.c χ * v₀.1.2.b) =
          v₀.1.2.s χ * r k ^ A.be.be v₀.1.1.toAdd χ * J.h (A.N.c χ) * J.h v₀.1.2.b := by
        have := hs₀'.2 χ
        rw [ht₀.2.1, ht₀.2.2] at this
        exact this
      have g₇ := congrArg Units.val g₆
      simp only [Units.val_mul] at g₇
      refine (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (g₂ i)) g₃).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) g₅ g₄).symm)
      rw [Fin.prod_univ_four]
      have alg : ∀ S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W : C, w₀ ≠ 0 → W ≠ 0 → h₀ * w₀ = W → h₁ * w₁ = W → h₂ * w₂ = W →
          w₃ = W → S * h₀ = S₀ * ρ * h₁ * h₂ →
          w₀ ^ (-1 : ℤ) * w₁ ^ (1 : ℤ) * w₂ ^ (1 : ℤ) * w₃ ^ (-1 : ℤ) * S = ρ * S₀ := by
        intro S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W n₀ nW a₀ a₁ a₂ a₃ a₄
        subst a₃
        simp only [zpow_neg, zpow_one]
        field_simp
        refine mul_left_cancel₀ nW ?_
        linear_combination (-(w₁ * w₂ * S)) * a₀ + (w₀ * w₁ * w₂) * a₄ + (S₀ * ρ * w₀ * h₂ * w₂) * a₁ +
          (S₀ * ρ * w₀ * w₃) * a₂
      exact alg _ _ _ _ _ _ _ _ _ _ _ (hne _) (hne 1) (hh _) (hh _) (hh _)
        (congrArg (wVal ν' A.ν w) (map_one J.φ)) g₇
  · obtain ⟨g, hg, -, hge, -⟩ := hTI C k hk
    exact (hg _ _).2 (((hg _ _).1 (hL v t₁ s₁ p' z ht₁ hs₁ hs₁' hp' hz)).trans ((hge _ _).2 e₁).symm)

end GlobalTheory.Ex.Trait.LevelClause
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeTheta
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.IsoValConst
open GlobalTheory.TorusExt GlobalTheory.ArcTransport

theorem const_of_cube {A U : Type} [CommGroup A] [CommGroup U] (Ω : A → U)
    (hc : ∀ a b c, Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ = 1)
    (P : A → Prop) (hP : ∀ a b, P a → P b → Ω a = Ω b) (n : ℕ) (hd : ∀ x : A, ∃ y, y ^ n = x)
    (hg : ∀ a : A, ∃ t, t ^ n = 1 ∧ P (a * t)) (x : A) : Ω x = Ω 1 := by
  obtain ⟨h, hh⟩ : ∃ h : A → U, ∀ x, h x = Ω x / Ω 1 := ⟨_, fun _ => rfl⟩
  have h1 : h 1 = 1 := by rw [hh, div_self']
  let B : A → A →* U := fun z => MonoidHom.mk' (fun x => h (x * z) / (h x * h z)) fun x y => by
    have e := congrArg Additive.ofMul (hc x y z)
    apply Additive.ofMul.injective
    simp only [hh, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one] at e ⊢
    linear_combination (norm := abel) e
  have hB : ∀ z x, B z x = h (x * z) / (h x * h z) := fun _ _ => rfl
  have sy : ∀ z x, B z x = B x z := fun z x => by rw [hB, hB, mul_comm x, mul_comm (h x)]
  have tors : ∀ t, t ^ n = 1 → ∀ a, h (a * t) = h a * h t := fun t ht a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, sy, ← map_pow, ht, map_one]
  have pw : ∀ t, (∀ a, h (a * t) = h a * h t) → ∀ k : ℕ, h (t ^ k) = h t ^ k := fun t ht k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ k ih => rw [pow_succ, pow_succ, ht, ih]
  have key : ∀ a t, t ^ n = 1 → h (a * t) ^ n = h a ^ n := fun a t ht => by
    rw [tors t ht, mul_pow, ← pw t (tors t ht), ht, h1, _root_.mul_one]
  have kill : ∀ a, h a ^ n = 1 := fun a => by
    obtain ⟨t, ht, p⟩ := hg a
    obtain ⟨s, hs, q⟩ := hg 1
    rw [← key a t ht, hh, hP _ _ p q, ← hh, key 1 s hs, h1, one_pow]
  have mul : ∀ t a, h (a * t) = h a * h t := fun t a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, hB, div_pow, mul_pow, kill, kill, kill, _root_.mul_one, div_one]
  obtain ⟨y, rfl⟩ := hd x
  rw [← div_eq_one, ← hh, pw y (mul y), kill]

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm
end Val

theorem exists_iso_pull {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {w : LB.Iso L' (L.pull Φ)}
    (hw : w.IsGen) (h : Y ⟶ X') : ∃ w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U k →
        gw w' r z j (fun _ => k) = gw w (r ≫ h) z j k := by
  have le : ∀ p : (PUnit → L.ι) × (PUnit → L'.ι), (L.pull (h ≫ Φ)).U p.1 ⊓ (L'.pull h).U p.2 ≤
      h ⁻¹ᵁ ((L.pull Φ).U p.1 ⊓ L'.U (p.2 PUnit.unit)) := fun p y hy =>
    ⟨mem_pull.2 (mem_pull.1 (show y ∈ (L.pull (h ≫ Φ)).U p.1 from hy.1) :), mem_pull.1 hy.2⟩
  let w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)) := ⟨fun p => res (le p) (pullU h _ (w.s (p.1, p.2 PUnit.unit)))⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j (k : PUnit → L'.ι), Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U (k PUnit.unit) →
      gw w' r z j k = gw w (r ≫ h) z j (k PUnit.unit) := fun Z r z j k hj hk =>
    have m : r z ∈ (L.pull (h ≫ Φ)).U (fun _ => j) ⊓ (L'.pull h).U k := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
    (gm_res r z (le (fun _ => j, k)) m _).trans (gm_pull r h z _ (le (fun _ => j, k) m) _)
  refine ⟨w', (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k => v Z r z j fun _ => k⟩
  rw [v Z r z j k hj (mem_pull.1 hk), v Z r z j' k' hj' (mem_pull.1 hk'), gm_pull_g L' h r z k k' hk hk',
    ← Category.assoc]
  exact (isGen_iff _).1 hw Z (r ≫ h) z j j' _ _ hj hj' (mem_pull.1 hk :) (mem_pull.1 hk' :)

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  Units.ext ((congrArg (stalkConst z) (ν.θ_eq x y u)).trans (const_vF _ _ (good ν z)))

theorem stalk_th : ∃ ρ : ((Sp F).presheaf.stalk z)ˣ, ∀ x : N.A,
    stalkConst z (N.th x) * ρ.val = sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  ⟨_, fun x => (congrArg _ (const_vF _ _ (good ν z)).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))⟩

theorem sval_eq (s : H0 D.P.L 1) : ∃ κ : (Sp F).presheaf.stalk z, ∀ x : TF (R := R) F ⟶ D.P.A,
    sval (Z := Sp F) s x.left z ν.J = κ * sval (Z := Sp F) ν.th x.left z ν.J := by
  obtain ⟨r, hr⟩ := ν.th_gen s
  refine ⟨gs (Y := Sp F) (TF (R := R) F).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r), fun x => ?_⟩
  have m := (good ν z).mem (fun _ : Fin 1 => 𝟙 D.P.A.left) (show Sp F ⟶ _ from x.left)
  refine (congrArg (gs _ z _) (hr _)).trans ((gs_mul _ z _ m _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  refine (gs_res _ z le_top m _).trans ?_
  rw [← Over.w x]
  exact gs_pull (show Sp F ⟶ _ from x.left) D.P.A.hom z ⊤ trivial _
end Num

theorem exists_iso_val_const : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (f : R' →+* R) (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N : NumD F) (k : ℕ) (β : N.Form k) (u : Fˣ) (ν : NumOf D F (N.twist β u)) (ν' : NumOf D' F N) (φ : D.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D.P.L (D'.P.L.pull φ)), IsGrpPullback D.P.A D'.P.A (spMap f) φ → w.IsGen → (∀ x, (ν.eA x).left ≫ φ = (ν'.eA x).left) → ∀ n : ℕ, (∀ x : N.A, ∃ y, y ^ n = x) → (∀ a : N.A, ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0) → ∃ (w' : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ))) (c : Fˣ), w'.IsGen ∧ ∀ x, valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w'.s (fun _ => ν'.J (ν'.eA x).left, fun _ => ν.J (ν.eA x).left)).val = c := by
  intro hL R R' _ _ _ _ f D D' F _ _ _ N k β u ν ν' φ w gp hw he n hd hg
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) F).hom ≫ spMap f = (TF (R := R') F).hom := by
    rw [← Over.w (ν.eA 1), ← Over.w (ν'.eA 1), Category.assoc]
    exact (congrArg _ gp.1.w.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D'.P.A.hom) (he 1)))
  have hp : ∀ x : N.A, pushF gp hT (ν.eA x) = ν'.eA x := fun x => Over.OverMorphism.ext (he x)
  let Ω : N.A → ((Sp F).presheaf.stalk z)ˣ := fun x => wVal w z ν'.J ν.J (ν.eA x)
  have em : ∀ a b : N.A, ν.eA (a * b) = ν.eA a * ν.eA b := fun a b => map_mul ν.eA a b
  have e1 : ν.eA (1 : N.A) = 1 := map_one ν.eA
  have hΩ : ∀ x, Ω x = Ω 1 := by
    refine const_of_cube Ω (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ n hd hg
    · have e := thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ' hJ (ν.eA a) (ν.eA b) (ν.eA c)
      rw [hp, hp, hp, ← em, ← em, ← em, ← em, ← e1] at e
      exact mul_eq_right.1 (e.symm.trans ((stalk_θ ν' z a b c).symm.trans (stalk_θ ν z a b c)))
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D'.P.A.left) (h := φ) hw D'.P.isLB D.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν'.th
      obtain ⟨κ, hκ⟩ := sval_eq ν z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 → ρ'.val = (Ω a).val * (κ * ρ.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp F ⟶ _ from (ν.eA a).left) hJ' hJ
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp F).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ'.val = (Ω a).val * (κ * (stalkConst z (N.th a) * ρ.val)) :=
          (hρ' a).trans ((congrArg (fun q => sval (Z := Sp F) ν'.th q z ν'.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ a).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        ring
      intro a b ha hb
      have hu : IsUnit (κ * ρ.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ'.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
  obtain ⟨w', hw', hv⟩ := exists_iso_pull hw (snd (TF (R := R) F) D.P.A).left
  refine ⟨w', (stalkUnits z).symm (Ω 1), hw', fun x => (stalkConst z).injective ?_⟩
  have l : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [l]; exact hJ _
  have m₂ : (((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) ≫ φ) z ∈
      D'.P.L.U (ν'.J (ν'.eA x).left) := by rw [l, he]; exact hJ' _
  refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left
    ((D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ)).U (fun _ => ν'.J (ν'.eA x).left) ⊓
      (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U fun _ => ν.J (ν.eA x).left) z ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _).trans ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply, ← hΩ x]
  refine congrArg Units.val ((hv (Sp F) _ z _ _ m₂ m₁).trans ?_)
  rw [l, ← he]
  rfl

end GlobalTheory.IsoValConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelTraitExtensionPolarisedFlatBundleIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.ModelFacts

theorem exists_extend {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {W : Type} [CommRing W] [IsDomain W]
    [ValuationRing W] (y : Sp (FractionRing W) ⟶ X) (s : Sp W ⟶ B) (h : y ≫ f = jK W ≫ s) :
    ∃ χ : Sp W ⟶ X, y = jK W ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := W, K := FractionRing W, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_open {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨e⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) e⟩
  have sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
      ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, semiPull f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
    have h := isGrpPullback_pullback t.G f
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
        pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
        pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
      Over.OverMorphism.ext (by
        show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull (y ≫ Y.j) Y.t
  obtain ⟨m₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m m₂
  have h₂ : LBIso PP'.L (Y.t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull Y.t.PP.isLB (pullback.fst Y.t.G.hom (y ≫ Y.j))
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem exists_rigPull {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {χ : S' ⟶ S} (m : SABMap t' t χ) :
    ∃ ω : LB.Iso t'.PP.L (t.PP.L.pull m.φ), RigPull t'.G t.G χ m.φ ω t'.PP.rig t.PP.rig := by
  obtain ⟨w, g, r, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
  rw [m.base] at r
  exact ⟨w, m.cart, (isGen_iff w).2 g, t'.PP.rigGen, r⟩

theorem model_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (y : Sp (FractionRing W) ⟶ Y.X) (s : Sp W ⟶ Sp O), y ≫ Y.s = jK W ≫ s → ∃ χ : Sp W ⟶ Y.X, y = jK W ≫ χ) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c), PolAt Y.t (y ≫ Y.j)) ∧ Flat Y.t.G.hom ∧ ∀ (S : Scheme.{0}) (t : SAB H S) (χ : S ⟶ Y.X) (m : SABMap t Y.t χ) (L : RigLB t.G), L = t.PP → ∃ ω : LB.Iso L.L (Y.t.PP.L.pull m.φ), RigPull t.G Y.t.G χ m.φ ω L.rig Y.t.PP.rig := by
  intro E _ _ _ H D l Xo c O _ β Y
  refine ⟨fun W _ _ _ y s h => exists_extend Y.s (projProper O _ _ Y.proj) y s h, fun K _ y => polAt_open Y y, ?_, ?_⟩
  · have := Y.t.semi.smooth
    infer_instance
  · rintro S t χ m L rfl
    exact exists_rigPull m

end GlobalTheory.ModelFacts
end
end

