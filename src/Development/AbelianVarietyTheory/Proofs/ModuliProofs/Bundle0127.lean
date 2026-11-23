module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckePointsOfPartsComm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_transfer_comm
    {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} (u : Obj D l b sX) {k : Type} [Field k]
    {s : Sp k ⟶ Sp B} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c => weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_snd, fun x => ?_, fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

end GlobalTheory.HeckePoint

namespace GlobalTheory

open HeckePoint

theorem heckePoints_of_parts_comm :
    Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj
        G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a'
        : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act
        c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n
        : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing
        B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s
        : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
        : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
        o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b
        : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
        : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
        : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
        f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
        f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
        : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
        : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 *
        (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
        : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
        l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ
        f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓
        : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act
        : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e'
        : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ
        : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p
        : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞
        E), J * 𝔓 = Ideal.span {(p
        : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p
        : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^
        2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p +
        D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n
        * p ^ 2) x y c → e' n (ψ x) (ψ
        y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD
        n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a))) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t
        : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶
        t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p
        ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ
        : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over
        (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow
        t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → (∀ (S : Scheme.{0}) (A B : Over S) [GrpObj
        A] [GrpObj B] (ψ : A ⟶ B) (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y
        : T ⟶ A) (c c' : Γ(T.left,
        ⊤)ˣ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L
        d) (M.pull ψ.left) → Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' → Out.WeilIs A L (n *
        d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d)) → (∀ (O : Type) [CommRing O] (S
        : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b
        : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k
        : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n
        : ℕ), LieMult a x τ n ↔ LieMult b x τ n) → (∀ (k : Type) [Field k] [IsAlgClosed k] (P P'
        : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n
        : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c
        : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn
        c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow
        P.L d)) (abelian₂ P.A (P'.L.pull α.left))) → (∀ (k : Type) [Field k] [IsAlgClosed k] (P
        : Out.PolAV (Sp k)) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)), Finite C → ∃ (B : Over (Sp
        k)) (_ : GrpObj B) (ψ
        : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over
        (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) ∧ ∀ (Y : Over (Sp k)) (f : P.A ⟶ Y), (∀ x ∈ C, ((toUnit
        P.A ≫ x) * 𝟙 P.A) ≫ f = f) → ∃! f' : B ⟶ Y, ψ ≫ f' = f) → ∀ (E : Type) [Field
        E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H), 1 ≤ D.p + D.q → ToroidalHeckeCompatibility (H := H) (D := D) := by
  intro hL _ hPull hComp hfacts _ hTate hQuot hWeil hLie hDet _ E _ _ _ H D _ l Xo 𝔓 p i h𝔓 hco hp hp𝔓 hpM k _ _ y C hC
  obtain ⟨c₁, c₂, c₃, c₄, c₅, -⟩ := hC
  have : CharZero k := charZero_of_injective_ringHom (Spec.preimage (y ≫ Xo.s)).hom.injective
  have pull : ∀ y' : Sp k ⟶ Xo.X, y' ≫ Xo.s = y ≫ Xo.s →
      ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') := fun y' h =>
    hPull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
      (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  obtain ⟨o, ⟨m⟩⟩ := pull y rfl
  obtain ⟨ρ, e, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_comm Xo.univ m
  let C' : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G) := C.comap ρ.toMonoidHom
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun _ => Iff.rfl
  obtain ⟨hC', o₁, ψ₁, h₁, hfin, het, hsur⟩ := exists_isHeckeIsog hL hfacts hTate hQuot hWeil hLie o 𝔓 p h𝔓 hco hp
    hp𝔓 hpM C' (fun x hx a => (mem _).2 (by rw [e₃]; exact c₁ _ hx a))
    (fun J hJ x hx => c₂ J hJ fun a ha => (e₃ a x).symm.trans (by rw [hx a ha, map_one]))
    (fun x hx a ha => ρ.injective ((e₃ a x).trans ((c₃ hx a ha).trans (map_one ρ).symm)))
    (fun x hx x' hx' => by
      have := (e₄ ((p : ℤ) ^ 2) x x' 1).2
        ((congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) (ρ x) (ρ x')) unitOn_one).mpr (c₄ _ hx _ hx'))
      rw [Nat.cast_pow]
      exact (congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) x x') unitOn_one).mp this)
    ((Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)).trans c₅)
  obtain ⟨y₁, ⟨hy₁, ⟨m₁⟩⟩, huniq⟩ := Xo.rep _ (y ≫ Xo.s) inferInstance o₁
  refine ⟨y₁, ⟨hy₁, ?_⟩, ?_⟩
  · obtain ⟨ρ₁, f, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_comm Xo.univ m₁
    obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
    let σ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
      MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
    let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
    have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ ψ₁) := fun x => congrArg (fun z => ρ₁ (z ≫ ψ₁)) (ρ.symm_apply_apply x)
    refine ⟨e.inv ≫ ψ₁.left ≫ f.hom, ψp, ?_, fun x => ?_, fun a x => ?_, fun z => ?_, Subgroup.ext fun x => ?_,
      fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
    · rw [Category.assoc, Category.assoc, f₁, Over.w, Iso.inv_comp_eq, e₁]
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      rw [hψ, e₂, f₂, Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left, Category.assoc]
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      rw [← e₃, hψ, hψ, ← f₃, Category.assoc, lin₁, Category.assoc]
    · obtain ⟨z, rfl⟩ := ρ₁.surjective z
      obtain ⟨x, rfl⟩ := sur₁ z
      exact ⟨ρ x, hψ x⟩
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, ker₁, mem]
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      obtain ⟨x', rfl⟩ := ρ.surjective x'
      rw [hψ, hψ]
      exact (f₄ _ _ _ _).1 (weil₁ n x x' c hn ((e₄ _ _ _ _).2 h))
    · rw [← e₅, ← e₆, hψ, hψ, (lev₁ p' hp' a).1, (lev₁ p' hp' a).2, f₅, f₆]
      exact ⟨rfl, rfl⟩
  · rintro y₂ ⟨hy₂, ψ, ψp, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
    obtain ⟨o₂, ⟨m₂⟩⟩ := pull y₂ hy₂
    obtain ⟨ρ₂, f, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_comm Xo.univ m₂
    let ψ₂ : o.t.G ⟶ o₂.t.G := Over.homMk (e.hom ≫ ψ ≫ f.inv) (by
      rw [← f₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])
    have hψ : ∀ x, ρ₂ (x ≫ ψ₂) = ψp (ρ x) := fun x => fibPt_injective _ (by
      rw [f₂, ← g₂, e₂]
      show (x.left ≫ e.hom ≫ ψ ≫ f.inv) ≫ f.hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hab := isAbelianScheme_of_proper o.t o.proper
    have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
    have := o₂.proper
    have one : ∀ (G : Over (Sp k)) [GrpObj G], (1 : 𝟙_ (Over (Sp k)) ⟶ G) = η[G] := fun G _ => by
      rw [Hom.one_def]; simp
    have h₂ : IsHeckeIsog o o₂ p C' ψ₂ := by
      refine ⟨hL.rigidity _ _ _ hab hab₂ ψ₂ ?_, fun a => hom_ext_pts hab.smooth fun x => ρ₂.injective ?_,
        fun z => ?_, fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ⟨ρ₂.injective ?_, ρ₂.injective ?_⟩⟩
      · rw [← one, ← one]
        exact ρ₂.injective (by rw [hψ, map_one, map_one, map_one])
      · rw [← Category.assoc, ← Category.assoc, hψ, f₃, hψ, e₃, g₃]
      · obtain ⟨x, hx⟩ := g₄ (ρ₂ z)
        obtain ⟨x, rfl⟩ := ρ.surjective x
        exact ⟨x, ρ₂.injective ((hψ x).trans hx)⟩
      · rw [mem, ← g₅, MonoidHom.mem_ker, ← hψ, map_eq_one_iff _ ρ₂.injective]
      · refine (f₄ _ _ _ _).2 ?_
        rw [hψ, hψ]
        exact g₆ n _ _ c hn ((e₄ _ _ _ _).1 h)
      · rw [hψ, e₅, f₅]; exact (g₇ p' hp' a).1
      · rw [hψ, e₆, f₆]; exact (g₇ p' hp' a).2
    obtain ⟨m'⟩ := objMap_of_isHeckeIsog hL hfacts hDet hp hpM hC' h₁ h₂
    obtain ⟨m'', -⟩ := ((hComp E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y₂ (𝟙 _) m₂).1 m'
    rw [Category.id_comp] at m''
    exact huniq y₂ ⟨hy₂, ⟨m''⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkCover

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem exists_geomPt (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X), ∀ q, x q = g :=
  ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g,
    fun _ => Scheme.fromSpecResidueField_apply g _⟩

theorem exists_power {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S) (u : Fin n → (T ⟶ C)), (∀ j, u j ≫ c = x) →
        ∃ y : T ⟶ P, y ≫ π = x ∧ ∀ j, y ≫ σ j = u j := by
  induction n with
  | zero => exact ⟨S, 𝟙 S, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0,
      fun T x u _ => ⟨x, by simp, fun j => j.elim0⟩⟩
  | succ n ih =>
    obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := ih
    refine ⟨pullback π c, pullback.fst π c ≫ π,
      Fin.cons (pullback.snd π c) (fun j => pullback.fst π c ≫ σ j), inferInstance, inferInstance, fun j => ?_,
      fun T x u hu => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [pullback.condition]
      · simp [h₃]
    · obtain ⟨y, hy, hy'⟩ := h₄ T x (fun j => u j.succ) (fun j => hu _)
      refine ⟨pullback.lift y (u 0) (hy.trans (hu 0).symm), by simp [hy], fun j => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [hy']

theorem exists_eqLocus {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C) (h : a ≫ c = b ≫ c) :
    ∃ U : Set P, IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  first
  | (rename_i h_4 h_5; revert P C S c h_4 h_5 a b h; exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer)
  | exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | (apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer ..)

theorem exists_distinct {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      (∀ (k : Type) [Field k] (y : Sp k ⟶ P), Function.Injective fun j => y ≫ σ j) ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (u : Fin n → (Sp k ⟶ C)), (∀ j, u j ≫ c = x) → Function.Injective u →
        ∃ y : Sp k ⟶ P, y ≫ π = x := by
  obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := exists_power c n
  choose U hU hU' using fun a b : Fin n => exists_eqLocus c (σ a) (σ b) ((h₃ a).trans (h₃ b).symm)
  have hV : IsClopen (⋂ a, ⋂ b, ⋂ _ : a ≠ b, (U a b)ᶜ) :=
    isClopen_iInter_of_finite fun a => isClopen_iInter_of_finite fun b =>
      isClopen_iInter_of_finite fun _ => (hU a b).compl
  let V : P.Opens := ⟨_, hV.isOpen⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV.isClosed)
  refine ⟨V, V.ι ≫ π, fun j => V.ι ≫ σ j, inferInstance, inferInstance, fun j => by simp [h₃],
    fun k _ y a b e => ?_, fun k _ x u hu hi => ?_⟩
  · by_contra ne
    have q : Sp k := IsLocalRing.closedPoint k
    have m₁ : (y ≫ V.ι) q ∈ U a b := (hU' a b _ (y ≫ V.ι)).1 (by simpa using e) ⟨q, rfl⟩
    have m₂ : (y ≫ V.ι) q ∈ (V : Set P) := by
      rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    exact (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 m₂ a) b) ne) m₁
  · obtain ⟨y, hy, hy'⟩ := h₄ _ x u hu
    have hr : Set.range y ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      refine Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.2 fun ne m => ne (hi ?_)
      rw [← hy', ← hy', hU']
      rintro _ ⟨q', rfl⟩
      rwa [Subsingleton.elim q' q]
    exact ⟨IsOpenImmersion.lift V.ι y hr, by rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem comp_act_natCast (t : SAB H S) {T : Over S} (z : T ⟶ t.G) (n : ℕ) : z ≫ t.act.act (n : 𝓞 E) = z ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero, show t.act.act 0 = 1 from left_eq_mul.1 this, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem pow_sq_eq_one (t : SAB H S) {T : Over S} {D : Datum H} {P : Ideal (𝓞 E)} {p i : ℕ} (hp : (p : 𝓞 E) ∈ P)
    {C : Subgroup (T ⟶ t.G)} (h : t.HeckeKer T D P p i C) {z : T ⟶ t.G} (hz : z ∈ C) : z ^ (p ^ 2) = 1 := by
  rw [← comp_act_natCast]
  refine h.2.2.1 hz _ ?_
  rw [Nat.cast_pow, sq]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp

end GlobalTheory.HkCover


open GlobalTheory.HkCover in
theorem GlobalTheory.exists_cover_lists_heckeSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → EtSet o.t.G K → HeckeSet D o.t 𝔓 p i K → ∃ (S' : Scheme.{0}) (π : S' ⟶ S) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over S') ⟶ o'.t.G)), IsFinite π ∧ Etale π ∧ Surjective π ∧ Lists (p ^ 2) τ (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l P p i S _ s o K hA hE hK
  obtain ⟨C, j, h₁, h₂, h₃, rfl⟩ := hE
  have hn : p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ≠ 0 := pow_ne_zero _ hA.2.2.1.ne_zero
  have hcard : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ Q : Subgroup (Over.mk x ⟶ o.t.G),
      (∀ z, z ∈ Q ↔ Set.range z.left ⊆ Set.range j.left) ∧ (∀ z ∈ Q, z ^ (p ^ 2) = 1) ∧
      Nat.card Q = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := fun k _ _ x => by
    obtain ⟨Q, hQ, hq⟩ := hK k x
    exact ⟨Q, hQ, fun z hz => pow_sq_eq_one o.t hA.2.2.2.1 hq hz, hq.2.2.2.2.1⟩
  generalize p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) = n at hn hcard ⊢
  have wj : j.left ≫ o.t.G.hom = C.hom := Over.w j
  have rg : ∀ {T : Scheme.{0}} (u : T ⟶ C.left), Set.range (u ≫ j.left) ⊆ Set.range j.left := by
    rintro T u _ ⟨q, rfl⟩
    exact ⟨u q, (Scheme.Hom.comp_apply _ _ _).symm⟩

  have hj : j ^ (p ^ 2) = 1 := by
    have : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
    have := o.proper
    refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_geometricPoints_dense o.t.G.hom _ _
      ((Over.w _).trans (Over.w _).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
    obtain ⟨Q, hQ, hq, -⟩ := hcard k (x ≫ C.hom)
    let x' : Over.mk (x ≫ C.hom) ⟶ C := Over.homMk x rfl
    have e := hq (x' ≫ j) ((hQ _).2 (rg x))
    rw [← MonObj.comp_pow, ← MonObj.comp_one x'] at e
    exact congrArg (fun z => z.left) e
  obtain ⟨S', π, σ, f₁, f₂, f₃, f₄, f₅⟩ := exists_distinct C.hom n
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over S'))
  let σ' : Fin n → (Over.mk ((𝟙_ (Over S')).hom ≫ π) ⟶ C) := fun a => Over.homMk (σ a) (by simpa using f₃ a)
  have e : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ m.toSABMap.φ = σ a ≫ j.left := fun a => by
    rw [← e₀, ρ.apply_symm_apply]; rfl
  have wτ : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ o'.t.G.hom = 𝟙 S' := fun a => Over.w _
  refine ⟨S', π, o', m, fun a => ρ.symm (σ' a ≫ j), f₁, f₂, ⟨fun g => ?_⟩, fun a => ?_, ?_, fun k _ _ y a b hab => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := exists_geomPt S g
    obtain ⟨Q, hQ, -, hc⟩ := hcard k x
    have en : Q ≃ Fin n := Nat.equivFinOfCardPos (hc ▸ hn) |>.trans (finCongr hc)
    have : ∀ a : Fin n, ∃ u : Sp k ⟶ C.left, u ≫ j.left = (en.symm a).1.left := fun a =>
      GlobalTheory.exists_lift_closedImmersion_of_dense j.left _ Set.univ dense_univ
        fun q _ => (hQ _).1 (en.symm a).2 ⟨q, rfl⟩
    choose u hu using this
    obtain ⟨y, hy⟩ := f₅ k x u (fun a => by rw [← wj, ← Category.assoc, hu]; exact Over.w (en.symm a).1)
      fun a b hab => en.symm.injective (Subtype.ext (Over.OverMorphism.ext (by rw [← hu, ← hu, hab])))
    have q : Sp k := IsLocalRing.closedPoint k
    exact ⟨y q, by rw [← Scheme.Hom.comp_apply, hy, hx]⟩
  · rw [← map_pow, ← MonObj.comp_pow, hj, MonObj.comp_one, map_one]
  · refine Set.Subset.antisymm (fun g hg => ?_) (Set.iUnion_subset fun a => ?_)
    · obtain ⟨k, _, _, w, hw⟩ := exists_geomPt _ g
      obtain ⟨Q, hQ, -, hc⟩ := hcard k ((w ≫ o'.t.G.hom) ≫ π)
      let z : Fin n → Q := fun a => ⟨Over.homMk (((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left)
        (by simp [wj, f₃]), (hQ _).2 (rg _)⟩
      have zi : Function.Injective z := fun a b hab => f₄ k (w ≫ o'.t.G.hom)
        ((cancel_mono j.left).1 (congrArg (fun z : Q => z.1.left) hab))
      have : Finite Q := Nat.finite_of_card_ne_zero (hc ▸ hn)
      have zb := (Nat.bijective_iff_injective_and_card z).2 ⟨zi, by simp [hc]⟩
      obtain ⟨a, ha⟩ := zb.2 ⟨Over.homMk (w ≫ m.toSABMap.φ) (by simpa using congrArg (w ≫ ·) m.cart.1.w), (hQ _).2 (by
        rintro _ ⟨q, rfl⟩
        have : (w ≫ m.toSABMap.φ) q ∈ Set.range j.left := by rw [Scheme.Hom.comp_apply, hw]; exact hg
        exact this)⟩
      have ha' : ((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left = w ≫ m.toSABMap.φ := congrArg (fun z : Q => z.1.left) ha
      have hw' : (w ≫ o'.t.G.hom) ≫ (ρ.symm (σ' a ≫ j)).left = w := m.cart.1.hom_ext
        (by rw [Category.assoc, ← ha', Category.assoc _ (σ a)]; exact congrArg (_ ≫ ·) (e a))
        (by rw [Category.assoc, wτ]; exact Category.comp_id _)
      have q : Sp k := IsLocalRing.closedPoint k
      refine Set.mem_iUnion.2 ⟨a, (w ≫ o'.t.G.hom) q, ?_⟩
      rw [← hw q]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun v : Sp k ⟶ _ => v q) hw')
    · rintro _ ⟨q, rfl⟩
      have := rg (σ a) ⟨q, rfl⟩
      rw [← e, Scheme.Hom.comp_apply] at this
      exact this
  · refine f₄ k y ((cancel_mono j.left).1 ?_)
    have := congrArg (· ≫ m.toSABMap.φ) hab
    simpa only [Category.assoc, e] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndSurjectiveOfFormIs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormFinite

open GlobalTheory.CechPic GlobalTheory.AmpleStabFinite

theorem lam_inv_eq {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (m l : CechPic.Pic A.left) (s : A ⟶ A)
    [IsMonHom s] (h : ∀ u v : T ⟶ A, lam m u v = lam l u (v ≫ s)) {x y : T ⟶ A} (e : x ≫ s = y ≫ s) :
    lam m x⁻¹ x = lam m y y⁻¹ := by
  rw [h, e, ← h, lam_comm, h, GrpObj.inv_comp, e, ← GrpObj.inv_comp, ← h]

theorem isFinite_of_lam_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    {M : LB A.left} (hM : IsAmpleLB M) (l : CechPic.Pic A.left) (s : A ⟶ A) [IsMonHom s]
    (h : ∀ (T : Over (Sp K)) (u v : T ⟶ A), lam (cls M hM.isLB) u v = lam l u (v ≫ s)) : IsFinite s.left := by
  obtain ⟨n, -, N, t, hc, ha⟩ := hM.exists_cover
  have : IsProper (s.left ≫ A.hom) := by rw [Over.w s]; infer_instance
  have : IsProper s.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite s.left from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (s.left ⁻¹' {z}) with h0 | ⟨a, hz⟩
  · rw [h0]; exact Set.finite_empty
  let k : Type := A.left.residueField a
  let y₀ : Spec (CommRingCat.of k) ⟶ A.left := A.left.fromSpecResidueField a
  let P : Over (Sp K) := Over.mk (y₀ ≫ A.hom)
  let y : P ⟶ A := Over.homMk y₀ rfl
  let π : pullback s.left (y₀ ≫ s.left) ⟶ A.left := pullback.fst _ _
  let q : pullback s.left (y₀ ≫ s.left) ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
  have w : π ≫ s.left = q ≫ y₀ ≫ s.left := pullback.condition
  let F : Over (Sp K) := Over.mk (π ≫ A.hom)
  let x : F ⟶ A := Over.homMk π rfl
  let r : F ⟶ P := Over.homMk q (by
    change q ≫ y₀ ≫ A.hom = π ≫ A.hom
    rw [← Over.w s, reassoc_of% w])
  have : IsAffineHom (y₀ ≫ s.left) := .of_comp _ A.hom
  have : IsAffineHom π := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
    (IsPullback.of_hasPullback s.left (y₀ ≫ s.left)).flip this
  have key := lam_inv_eq _ l s (h F) (x := x) (y := r ≫ y) (Over.OverMorphism.ext w)
  have triv : ∀ (b : P ⟶ A) (c : CechPic.Pic A.left), CechPic.pull (r ≫ b).left c = 0 := fun b c => by
    rw [Over.comp_left, pull_comp, pull_spec_local (K := k) b.left, map_zero]
  have one : ∀ c : CechPic.Pic A.left, CechPic.pull (1 : F ⟶ A).left c = 0 := fun c => by
    rw [← MonObj.comp_one r, triv]
  simp only [lam, inv_mul_cancel, ← GrpObj.comp_inv, ← MonObj.comp_mul, one, triv] at key
  have : CompactSpace ↥(pullback s.left (y₀ ≫ s.left)) := QuasiCompact.compactSpace_of_compactSpace q
  have : (pullback s.left (y₀ ≫ s.left)).IsQuasiAffine := quasiAffine_of_pull_add π (x⁻¹).left
    (isLB_lbPow hM.isLB n) t hc ha (by
      have e : CechPic.pull x.left (cls M hM.isLB) + CechPic.pull (x⁻¹).left (cls M hM.isLB) = 0 := by
        linear_combination (norm := abel) - key
      change CechPic.pull x.left _ + CechPic.pull (x⁻¹).left _ = 0
      rw [cls_lbPow hM.isLB, map_nsmul, map_nsmul, ← nsmul_add, e, nsmul_zero])
  have : IsAffine (pullback s.left (y₀ ≫ s.left)) := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set ↥(pullback s.left (y₀ ≫ s.left))).Finite :=
    (q.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun b hb => ?_
  have e : s.left b = (y₀ ≫ s.left) (IsLocalRing.closedPoint k) := by
    have e₀ : y₀ (IsLocalRing.closedPoint k) = a := Scheme.fromSpecResidueField_apply a _
    exact (show s.left b = z from hb).trans ((show s.left a = z from hz).symm.trans (congrArg s.left e₀).symm)
  obtain ⟨c, hc, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s.left) (g := y₀ ≫ s.left) b _ e
  exact ⟨c, trivial, hc⟩

theorem isFinite_and_surjective_of_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → Out.RelAmple P.A M → FormIs P M s → IsFinite s.left ∧ Surjective s.left := by
  intro _ _ K _ _ P M s hM hA ⟨hs, H⟩
  have := P.isAb.proper
  have := P.isAb.comm
  have e := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb P.isLB _ _)).2 H
  have e' := (cls_cube_two hM _ _ _).symm.trans (e.trans (cls_cube_two P.isLB _ _ _))
  have hf : IsFinite s.left :=
    isFinite_of_lam_eq (isAmpleLB_of_relAmple_of_isAffine P.A hM hA) (cls P.L P.isLB) s fun T u v => by
      simpa only [pull_lam, lift_fst, lift_snd, lift_snd_assoc] using congrArg (CechPic.pull (lift u v).left) e'
  exact ⟨hf, (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K P.A P.isAb s hs hf).2⟩

end GlobalTheory.FormFinite
end

