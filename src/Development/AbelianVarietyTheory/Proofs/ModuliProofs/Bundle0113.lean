module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjPull

theorem objPull_of_lie_of_ample : (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L')) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) := by
  intro _ hAb
  exact objPull_of_pol hAb

end GlobalTheory.ObjPull

namespace GlobalTheory

theorem obj_rigid_of_laws : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _
  exact obj_rigid_of_pol hL hpol E H D l B B' b b' S S' s s' o o' f

end GlobalTheory

namespace GlobalTheory.LevelFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Main

theorem exists_tate_push_comm
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S') (z : Sp k ⟶ S) (hz : x ≫ f = z) (e : (Over.mk x ⟶ t'.G) ≃* (Over.mk z ⟶ t.G))
    (he : ∀ p, (e p).left = p.left ≫ m.φ)
    (I : TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), J.ζ = I.ζ ∧ ∀ n a, J.ev n a = e (I.ev n a) := by
  exact exists_tate_push m x z hz e he I

variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem exists_sim_of_fibre_comm
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo₂.X), ∃ o' : Obj D l₂ (baseKA l₂) (z ≫ Xo₂.s), Nonempty (ObjMap o' Xo₂.univ z))
    {k : Type} [Field k] [IsAlgClosed k]
    (hDiff : ∀ (z : Sp k ⟶ Xo.X) (I I' : TateIso D k (Over.mk z ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
      (fun n g g' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c))),
      ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hmA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (hLev : ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r)
    (x x' : Sp k ⟶ Xo₂.X) (hr : x ≫ r = x' ≫ r) (hs : x ≫ Xo₂.s = x' ≫ Xo₂.s) :
    ∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ x' = x ≫ ρ.hom := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Xo₂.s)
  obtain ⟨-, I, hIζ, hIA, hI⟩ := Xo₂.univ.geom k x β hβ
  obtain ⟨-, I', hIζ', hIA', hI'⟩ := Xo₂.univ.geom k x' β (hs.symm.trans hβ)
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  obtain ⟨e', he'⟩ := exists_ptEquiv m.cart x' _ hr.symm
  obtain ⟨J, hJζ, hJ⟩ := exists_tate_push_comm m x _ rfl e he I
  obtain ⟨J', hJζ', hJ'⟩ := exists_tate_push_comm m x' _ hr.symm e' he' I'
  obtain ⟨g, hg⟩ := hDiff _ J J'
  have key : ∀ (σ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (d : ℕ),
      (σ ^ d).left ≫ m.φ = r ≫ τ.left → e (toUnit _ ≫ σ) ^ d = e' (toUnit _ ≫ σ) ^ d := fun σ τ d h => by
    apply Over.OverMorphism.ext
    rw [← map_pow, ← map_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, he, he', unit_left, unit_left, Category.assoc,
      Category.assoc]
    exact (congrArg _ h).trans (((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.left) hr).trans
      (Category.assoc _ _ _))).trans (congrArg _ h.symm))
  obtain ⟨hin, hη⟩ := inGam_of_diff l l₂ hd J J' g hg
    (by rw [hJζ, hJζ']; exact Units.ext (hIζ'.trans hIζ.symm))
    (fun a => e (toUnit _ ≫ Xo₂.univ.eta a)) (fun a => e' (toUnit _ ≫ Xo₂.univ.eta a))
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [hJ, hI a ha]) (fun a ha => by rw [hJ', hI' a ha])
    (fun a => key _ _ _ (hm a)) (fun a => by rw [hJ, hJ', ← hIA, ← hIA']; exact key _ _ _ (hmA a))
  have hηA : ∀ a, e' (toUnit _ ≫ Xo₂.univ.etaA a) = e (toUnit _ ≫ Xo₂.univ.etaA (g.f l₂.A a)) := fun a => by
    rw [hIA, hIA', ← hJ, ← hJ', (hg _ l₂.A_pos).1]
  obtain ⟨ρ, hρ, hρr⟩ := hLev g hin
  refine ⟨g, ρ, hin, hρ, hρr, ?_⟩
  obtain ⟨hρs, ν, hν, hνA⟩ := hρ
  obtain ⟨o, ⟨p⟩⟩ := hPull k x'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m p.toSABMap
  obtain ⟨n₂, hn₂⟩ := sab_cast hr.symm n₁
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m n₂
  obtain ⟨n₃, hn₃⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  have lev : ∀ (s : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (σ τ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G),
      s.left ≫ p.toSABMap.φ = x' ≫ σ.left → e' (toUnit _ ≫ σ) = e (toUnit _ ≫ τ) → τ.left ≫ ν.φ = ρ.hom ≫ σ.left →
      s.left ≫ n₃.φ = (x ≫ ρ.hom) ≫ σ.left := fun s σ τ h₁ h₂ h₃ => by
    have h₄ : s.left ≫ n.φ = x ≫ τ.left := by
      apply m.cart.1.hom_ext
      · have := congrArg (fun w => w.left) h₂
        simp only [he, he', unit_left] at this
        refine Eq.trans ?_ this
        rw [← h₁, Category.assoc, Category.assoc]
        exact congrArg _ (hn.symm.trans (hn₂.trans hn₁))
      · rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, sec_w, sec_w]
        exact (Category.id_comp x).trans (Category.comp_id x).symm
    rw [hn₃, ← Category.assoc, h₄, Category.assoc, Category.assoc]
    exact congrArg _ h₃
  obtain ⟨f, -, hf⟩ := Xo₂.rep (Sp k) (x' ≫ Xo₂.s) inferInstance o
  rw [hf x' ⟨rfl, ⟨p⟩⟩]
  refine (hf _ ⟨by rw [Category.assoc, hρs, hs], ⟨⟨n₃, fun a => ?_, fun a => ?_⟩⟩⟩).symm
  · exact lev _ _ _ (p.eta a) (hη a) (hν a)
  · exact lev _ _ _ (p.etaA a) (hηA a) (hνA a)

end Main

theorem levelMap_fibre_simply_transitive_of_laws :
    Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
        : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j
        : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
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
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o
        : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M /
        l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing
        B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨
        IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
        a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
        E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
        : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
        l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ
        f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k
        : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
        : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
        n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
        : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
        : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
        n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
        a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
        : c.F = c₂.F) (rF
        : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
        hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
        : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
        : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ := by
  intro hL hPull _ hPol _ hRig _ hDiff _ hLev E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hm c c₂ hc rF hF₁ hF₂ k _ _ y y' hy
  have pull : ∀ (l : Level H) (Xo : Moduli D l) (k : Type) [Field k] (z : Sp k ⟶ Xo.X),
      ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z) := fun l Xo k _ z =>
    hPull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (z ≫ Xo.s) z rfl rfl
      (by rw [spMap_id', Category.comp_id]) Xo.univ
  constructor
  · have hr : (y ≫ pullback.fst _ _) ≫ r = (y' ≫ pullback.fst _ _) ≫ r := by
      rw [Category.assoc, Category.assoc, ← hF₁, ← Category.assoc, ← Category.assoc, hy]
    have hbij : Function.Bijective (IntermediateField.inclusion hc.le).toRingHom :=
      ⟨(IntermediateField.inclusion hc.le).toRingHom.injective, fun a => ⟨⟨a.1, hc.ge a.2⟩, rfl⟩⟩
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have hsnd : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ := by
      rw [← cancel_mono (spMap (IntermediateField.inclusion hc.le).toRingHom), Category.assoc, Category.assoc, ← hF₂,
        ← Category.assoc, ← Category.assoc, hy]
    have hs : (y ≫ pullback.fst _ _) ≫ Xo₂.s = (y' ≫ pullback.fst _ _) ≫ Xo₂.s := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, hsnd]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hPol E H D l _ (baseKA l) _ Xo.s Xo.univ
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
    have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
    let P : Out.PolAV Xo.X :=
      { A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
        rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
    obtain ⟨g, ρ, a₁, a₂, a₃, a₄⟩ := exists_sim_of_fibre_comm (pull l₂ Xo₂) (k := k)
      (fun z => hDiff E H D k _ _ _ fun n p q a b _ hp hq ha hb =>
        unitOn_injective (((hL.weil _ P n (Over.mk z)).1 p q hp hq).unique ha hb))
      hd r m hm.2.2.1 hm.2.2.2 (hLev E H D l l₂ Xo Xo₂ hpq hd r jK m hm) _ _ hr hs
    exact ⟨g, ρ, a₁, a₂, a₃, a₄.trans (Category.assoc _ _ _)⟩
  · intro g ρ hg hρ hx
    exact trivAt_of_fixed (pull l Xo) (fun k _ z o' => hRig E H D l _ _ _ _ _ _ _ _ Xo.univ o' z (Or.inl inferInstance))
      hd r m hm.2.2.1 _ g ρ hg hρ ((Category.assoc _ _ _).trans hx)

end GlobalTheory.LevelFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.BilinCalc

theorem sum_antisymm {M : Type*} [AddCommGroup M] {n : ℕ} (b : Fin n → Fin n → M) (hb : ∀ i j, b i j = b j i)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : ∀ i j, D i j + D j i = 0) :
    ∑ uv : Fin n × Fin n, D uv.1 uv.2 • b uv.1 uv.2 = 0 := by
  classical

  let E : Fin n → Fin n → ℤ := fun i j => if i < j then D i j else 0
  have hDE : ∀ i j, D i j = E i j - E j i := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [E, hij, not_lt.mpr hij.le]
    · have := hD i i
      simp [E]
      omega
    · have := hD i j
      simp [E, hij, not_lt.mpr hij.le]
      omega
  have hswap : ∑ uv : Fin n × Fin n, E uv.2 uv.1 • b uv.1 uv.2 =
      ∑ uv : Fin n × Fin n, E uv.1 uv.2 • b uv.1 uv.2 := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun uv => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hb]
  simp only [hDE, sub_smul, Finset.sum_sub_distrib, hswap, sub_self]

theorem map_prod_zpow {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) (c : Fin n → ℤ) : f (∏ i, x i ^ c i) = ∑ i, c i • f (x i) := by
  let φ : Additive G →+ M := AddMonoidHom.mk' (fun a => f a.toMul) fun a a' => hf _ _
  have hφ : ∀ g : G, f g = φ (Additive.ofMul g) := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hφ, ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, ← hφ]

theorem sum_subst {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n m : ℕ} (x : Fin n → G)
    (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (h : W' + W'.transpose = c.transpose * (W + W.transpose) * c) :
    ∑ uv : Fin n × Fin n, W' uv.1 uv.2 • B (x uv.1) (x uv.2) =
      ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) := by
  classical
  have hL : ∀ (y : G) (k : Fin n → ℤ), B (∏ i, x i ^ k i) y = ∑ i, k i • B (x i) y :=
    fun y k => map_prod_zpow (fun g => B g y) (fun g g' => hB g g' y) x k
  have hR : ∀ (z : G) (k : Fin n → ℤ), B z (∏ i, x i ^ k i) = ∑ i, k i • B z (x i) :=
    fun z k => map_prod_zpow (fun g => B z g) (fun g g' => by rw [hs z, hB, hs g, hs g']) x k

  have hV : ∀ i j, ∑ a : Fin m, ∑ a' : Fin m, W a a' * (c a i * c a' j) = (c.transpose * W * c) i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) =
      ∑ ij : Fin n × Fin n, (c.transpose * W * c) ij.1 ij.2 • B (x ij.1) (x ij.2) := by
    simp only [hL, hR, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, ← hV, Finset.sum_smul]
    calc _ = ∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n, ∑ a' : Fin m,
          (W a a' * (c a i * c a' j)) • B (x i) (x j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  refine sum_antisymm (fun i j => B (x i) (x j)) (fun i j => hs _ _) (W' - c.transpose * W * c) fun i j => ?_
  have hij := congrFun (congrFun h i) j
  have ht : (c.transpose * W * c).transpose = c.transpose * W.transpose * c := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hji := congrFun (congrFun ht i) j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_add, Matrix.add_mul] at hij hji
  simp only [Matrix.sub_apply]
  linarith


open GlobalTheory.CechPic in
theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  intro S A _ _ Pb hPb hbi hsym T n m x W W' c h
  classical

  let β : (T ⟶ A) → (T ⟶ A) → Pic T.left := fun u v => pull (lift u v).left (cls Pb hPb)
  have hadd : ∀ u u' v : T ⟶ A, β (u * u') v = β u v + β u' v := by
    intro u u' v
    obtain ⟨t, ht⟩ := (hbi T u u' v).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hPb _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hPb] at e
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at e
    simp only [β]
    rw [← sub_eq_zero, ← e]
    abel
  have hsw : ∀ u v : T ⟶ A, β u v = β v u := by
    intro u v
    have e : cls Pb hPb = cls _ (pull_isLB hPb _) := (cls_eq_iff hPb (pull_isLB hPb _)).2 hsym
    rw [cls_pull hPb] at e
    simp only [β]
    conv_lhs => rw [e, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  refine (cls_eq_iff (LB.isLB_linComb hPb _ _) (LB.isLB_linComb hPb _ _)).1 ?_
  rw [cls_linComb hPb, cls_linComb hPb]
  exact sum_subst β hadd hsw x W W' c h

end GlobalTheory.BilinCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjMapOfIsHeckeIsog
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

theorem exists_torsion_lift {Q Q' : Type} [CommGroup Q] [CommGroup Q'] (ψ : Q →* Q') (hs : Function.Surjective ψ)
    {q n : ℕ} (hq : ∀ x, ψ x = 1 → x ^ q = 1) (hn : 0 < n) (hc : n.Coprime q) (y : Q') (hy : y ^ n = 1) :
    ∃ x, x ^ n = 1 ∧ ψ x = y := by
  obtain ⟨u, rfl⟩ := hs y
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hc.symm hn.ne'
  refine ⟨u ^ (q * r), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_mul, hq _ ((map_pow _ _ _).trans hy), one_pow]
  · rw [map_pow, pow_eq_pow_of_modEq (show q * r ≡ 1 [MOD n] from hr) hy, pow_one]

theorem objMap_of_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hDet : ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)))
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    Nonempty (ObjMap o₁ o₂ (𝟙 _)) := by
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, hrig, hsym⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, hrig₁, hsym₁⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, hrig₂, hsym₂⟩ := hfacts E H D l B b _ s o₂
  let P : Out.PolAV (Sp k) :=
    { A := o.t.G, isAb := hab, g := _, smoothDim := hdim,
      L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig, sym := hsym,
      ample := o.ample, ktriv := o.ktriv }
  let P₁ : Out.PolAV (Sp k) :=
    { A := o₁.t.G, isAb := hab₁, g := _, smoothDim := hdim₁,
      L := o₁.t.PP.L, isLB := o₁.t.PP.isLB, rigid := hrig₁, sym := hsym₁,
      ample := o₁.ample, ktriv := o₁.ktriv }
  let P₂ : Out.PolAV (Sp k) :=
    { A := o₂.t.G, isAb := hab₂, g := _, smoothDim := hdim₂,
      L := o₂.t.PP.L, isLB := o₂.t.PP.isLB, rigid := hrig₂, sym := hsym₂,
      ample := o₂.ample, ktriv := o₂.ktriv }
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    hDet k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory.HeckePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem relAmple_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hiso hA _ hamp
  have : IsProper A.hom := hA.proper
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S A L hL inferInstance inferInstance fun s => ?_
  obtain ⟨i, hi⟩ := exists_mem hU s
  obtain ⟨V, hV, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := U i) (x := s) hi
  have hle' : V ≤ U i := hle
  refine ⟨V, hs, ?_⟩
  have h := (hψ i).1
  have hf : S.homOfLE hle' ≫ (U i).ι = V.ι := S.homOfLE_ι hle'
  have sq : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = ((A.hom ∣_ V) ≫ S.homOfLE hle') ≫ (U i).ι := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  let φ : (A.hom ⁻¹ᵁ V).toScheme ⟶ (G i).left := h.lift _ _ sq
  have hφ : φ ≫ ψ i = (A.hom ⁻¹ᵁ V).ι := h.lift_fst _ _ _
  have H : IsPullback φ (A.hom ∣_ V) (G i).hom (S.homOfLE hle') := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hφ, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  obtain ⟨w, hw⟩ : LBIso (L.pull (A.hom ⁻¹ᵁ V).ι) ((M i).pull φ) :=
    LBIso.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ V).ι) (fun _ => ψ i) (fun _ => 1) φ fun _ => hφ.symm)
      (chartPullPull (M i) φ φ rfl) (hiso i).symm
  refine relAmple_pull (A' := Over.mk (A.hom ∣_ V)) H (hM i) (pull_isLB hL _) ((isGen_iff w).1 hw) ((U i).ι ⁻¹ᵁ V)
    (hV.preimage_of_isOpenImmersion _ (by simpa using hle')) (fun y => by
      have hy := congrArg (fun f : V.toScheme ⟶ S => f y) hf
      change ((S.homOfLE hle') y).val = y.val at hy
      change ((S.homOfLE hle') y).val ∈ V
      rw [hy]
      exact y.property) (hamp i)

end GlobalTheory.CoverGlue
end

