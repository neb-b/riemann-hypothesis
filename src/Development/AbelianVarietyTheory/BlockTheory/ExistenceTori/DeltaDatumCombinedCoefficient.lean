module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure IsAuxiliarySplitSquarefreeLevel (l : Level H) where
  p : ℕ
  prime_or_one : p.Prime ∨ p = 1
  coprime : p.Coprime l.M'
  l₂ : Level H
  dvd : l.Dvd l₂
  M_eq : l₂.M = l.M * p
  A_eq : l₂.A = l.A

namespace IsAuxiliarySplitSquarefreeLevel

variable {l : Level H} (a : IsAuxiliarySplitSquarefreeLevel l)

def pId : Ideal (𝓞 E) := Ideal.span {(a.p : 𝓞 E)}

def named : Ideal (𝓞 E) := a.l₂.Mb ⊔ a.pId

def conj : Ideal (𝓞 E) := conjHalf a.l₂ ⊔ a.pId

def SplitsCompletely : Prop :=
  ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (a.p : 𝓞 E) ∈ 𝔮 → Ideal.absNorm 𝔮 = a.p ∧ (a.p : 𝓞 E) ∉ 𝔮 ^ 2

theorem conj_le_comap : a.conj ≤ a.named.comap (H.bar : 𝓞 E →+* 𝓞 E) := by
  refine sup_le (fun x hx => ?_) ?_
  · exact Ideal.mem_sup_left (bar_mem_of_mem_conjHalf a.l₂ hx)
  · rw [pId, Ideal.span_le, Set.singleton_subset_iff]
    change (H.bar : 𝓞 E →+* 𝓞 E) (a.p : 𝓞 E) ∈ a.named
    rw [map_natCast]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

def barQuot : (𝓞 E ⧸ a.conj) →+* (𝓞 E ⧸ a.named) :=
  Ideal.quotientMap a.named (H.bar : 𝓞 E →+* 𝓞 E) a.conj_le_comap

theorem KA_le : KA l ≤ KA a.l₂ := by rw [KA, KA, a.A_eq]

def red (D : Datum H) : ConjCl D a.l₂ →ₗ[𝓞 E] ConjCl D l :=
  Submodule.mapQ _ _ LinearMap.id (Submodule.smul_mono_left (Ideal.map_mono a.dvd.2.1))

end IsAuxiliarySplitSquarefreeLevel

structure DeltaChar {l : Level H} (a : IsAuxiliarySplitSquarefreeLevel l) (F : Type) [Field F] where
  loc : MulChar (𝓞 E ⧸ a.named) F
  ideal : Ideal (𝓞 E) →*₀ F
  ideal_zero : ∀ 𝔞, 𝔞 ⊔ a.pId ≠ ⊤ → ideal 𝔞 = 0
  principal : ∀ α : 𝓞 E, α ≠ 0 → Ideal.span {α} ⊔ a.pId = ⊤ →
    ideal (Ideal.span {α}) * loc (Ideal.Quotient.mk _ α) = loc (Ideal.Quotient.mk _ (H.bar α))
  real : ∀ 𝔟 : Ideal (𝓞 (maximalRealSubfield E)), 𝔟 ≠ ⊥ →
    𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ⊔ a.pId = ⊤ →
    ideal (𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) = 1

def IsDetMod (D : Datum H) (I : Ideal (𝓞 E)) (k : D.La →ₗ[𝓞 E] D.La) (d : 𝓞 E ⧸ I) : Prop :=
  ∀ (φ : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] (𝓞 E ⧸ I)) (x : Fin (D.p + D.q) → D.La), φ (fun i => k (x i)) = d * φ x

def indexIdeal {D D' : Datum H} (β₀ : D'.La →ₗ[𝓞 E] D.La) : Ideal (𝓞 E) :=
  Ideal.span {z | ∃ (φ : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] 𝓞 E) (x : Fin (D.p + D.q) → D'.La), z = φ fun i => β₀ (x i)}

section Datum

variable {D : Datum H} {l : Level H} {a : IsAuxiliarySplitSquarefreeLevel l}

structure Vol (D : Datum H) (a : IsAuxiliarySplitSquarefreeLevel l) where
  ω : ConjCl D a.l₂ [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] (𝓞 E ⧸ a.conj)
  gen : ∃ u, ω u = 1

def Vol.det₁ (v : Vol D a) {n : ℕ} (x : Fin n → ConjCl D a.l₂) : 𝓞 E ⧸ a.conj :=
  if h : D.p + D.q ≤ n then v.ω fun i => x (Fin.castLE h i) else 0

variable {F : Type} [Field F]

def phiDelta (δ : DeltaChar a F) (v : Vol D a) {n : ℕ} (x : Fin n → ConjCl D a.l₂) : F :=
  δ.loc⁻¹ (a.barQuot (v.det₁ x))

end Datum

section Cover

variable {D : Datum H} {l : Level H}

def IsLevelMap (Xo : Moduli D l) (a : IsAuxiliarySplitSquarefreeLevel l) (Xo₂ : Moduli D a.l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r) : Prop :=
  r ≫ Xo.s = Xo₂.s ≫ spMap (IntermediateField.inclusion a.KA_le).toRingHom ∧
    (∀ x, (Xo₂.univ.eta x ^ a.p).left ≫ m.φ = r ≫ (Xo.univ.eta x).left) ∧
    ∀ x, (Xo₂.univ.etaA x).left ≫ m.φ = r ≫ (Xo.univ.etaA x).left

def IsBundleIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (m.cm.thetaPull t.PP.L t.cub.t)

structure Cover (Xo : Moduli D l) (c : Coeff l) (a : IsAuxiliarySplitSquarefreeLevel l) where
  Xo₂ : Moduli D a.l₂
  c₂ : Coeff a.l₂
  field_eq : c.F = c₂.F
  r : Xo₂.X ⟶ Xo.X
  m : SABMap Xo₂.univ.t Xo.univ.t r
  w : LB.Iso Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull m.φ)
  level : IsLevelMap Xo a Xo₂ r m
  bundle : IsBundleIso m w

variable {Xo : Moduli D l} {c : Coeff l} {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

namespace Cover

def incl : c.F →+* C.c₂.F := (IntermediateField.inclusion C.field_eq.le).toRingHom

def IsGroupMap {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (x₂ : Sp S' ⟶ C.Xo₂.X) (x : Sp S ⟶ Xo.X)
    (pm : Gx x₂ ⟶ Gx x) : Prop :=
  pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₂) C.Xo₂.univ.t.G).left ≫ C.m.φ ∧
    pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x₂) C.Xo₂.univ.t.G).left ≫ spMap φ

def SecOver {S S' : Type} [CommRing S] [CommRing S'] {x₂ : Sp S' ⟶ C.Xo₂.X} {x : Sp S ⟶ Xo.X} (pm : Gx x₂ ⟶ Gx x)
    (k : ℤ) (F₂ : LB.Sec (Out.LPow C.Xo₂.univ.t.G C.Xo₂.univ.t.PP.L k (Over.mk x₂)))
    (F : LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) : Prop :=
  ∀ (i : Xo.univ.t.PP.L.ι) (j : C.Xo₂.univ.t.PP.L.ι) (W : (Gx x₂).Opens)
    (h₁ : W ≤ pm ⁻¹ᵁ (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U fun _ => i)
    (h₂ : W ≤ (Out.LPow C.Xo₂.univ.t.G C.Xo₂.univ.t.PP.L k (Over.mk x₂)).U fun _ => j)
    (h₃ : W ≤ (snd (Over.mk x₂) C.Xo₂.univ.t.G).left ⁻¹ᵁ
      (LB.div (Xo.univ.t.PP.L.pull C.m.φ) C.Xo₂.univ.t.PP.L).U (fun _ => i, j)),
    (pm.appLE _ W h₁).hom (F.f fun _ => i) =
      ((res h₃ (pullU (snd (Over.mk x₂) C.Xo₂.univ.t.G).left _ (C.w.s (fun _ => i, j))) ^ k : Γ(Gx x₂, W)ˣ) :
        Γ(Gx x₂, W)) * ((Gx x₂).presheaf.map (homOfLE h₂).op).hom (F₂.f fun _ => j)

def LiesOver {S S' : Type} [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra C.c₂.F S'] (φ : S →+* S')
    (y₂ : FrPt C.Xo₂ C.c₂ S') (y : FrPt Xo c S) : Prop :=
  φ.comp (algebraMap c.F S) = (algebraMap C.c₂.F S').comp C.incl ∧
    y₂.x ≫ C.r = spMap φ ≫ y.x ∧
    (∀ τ i, y₂.u τ i ≫ C.m.φ = spMap (dualMap φ) ≫ y.u τ i) ∧
    ∃ pm : Gx y₂.x ⟶ Gx y.x, C.IsGroupMap φ y₂.x y.x pm ∧ C.SecOver pm 1 y₂.s y.s

def NabOver (nab : NabV Xo c) (nab₂ : NabV C.Xo₂ C.c₂) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra C.c₂.F S] (y₂ : FrPt C.Xo₂ C.c₂ S) (y : FrPt Xo c S),
    C.LiesOver (RingHom.id S) y₂ y → ∀ pm : Gx y₂.x ⟶ Gx y.x, C.IsGroupMap (RingHom.id S) y₂.x y.x pm →
    ∀ (k : ℤ) (F₂ : LB.Sec (Out.LPow C.Xo₂.univ.t.G C.Xo₂.univ.t.PP.L k (Over.mk y₂.x)))
      (F : LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk y.x))), C.SecOver pm k F₂ F →
      ∀ α, nab₂ y₂ k F₂ α = nab y k F α

end Cover

def fnAt {X : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (f : Γ(X, ⊤)) : S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (y.appTop.hom f)

def basePt {Xo : Moduli D l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, sOf]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

structure IsPresentation (a : IsAuxiliarySplitSquarefreeLevel l) (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ)
    (β₀ : D'.La →ₗ[𝓞 E] D.La) (𝔞 : Ideal (𝓞 E)) (d : 𝓞 E ⧸ a.named) : Prop where
  pos : 0 < m
  coprime : m.Coprime a.p
  isom : ∀ x y, D.EF (β₀ x) (β₀ y) = (m : ℤ) ^ 2 * D'.EF x y
  ne_bot : 𝔞 ≠ ⊥
  prime_to : 𝔞 ⊔ a.pId = ⊤
  index : indexIdeal β₀ * 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(m : 𝓞 E) ^ (D.p + D.q)} * 𝔞
  det : IsDetMod D a.named (β₀ ∘ₗ t) d

def IsDeltaDet (δ : DeltaChar a C.c₂.F) (f : Γ(C.Xo₂.XF C.c₂, ⊤)) : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty →
    ∀ (U : FamilyUnif C.Xo₂ (KA a.l₂).val.toRingHom ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)),
      IsPeriod (U.Di i) ty P → ∀ y : Sp ℂ ⟶ C.Xo₂.XF C.c₂, y ≫ pullback.fst _ _ = U.u i P →
      y ≫ pullback.snd _ _ = spMap C.c₂.F.val.toRingHom →
      ∀ (m : ℕ) (β₀ : (U.Di i).La →ₗ[𝓞 E] D.La) (𝔞 : Ideal (𝓞 E)) (d : 𝓞 E ⧸ a.named),
        IsPresentation a (U.Di i) (U.t i) m β₀ 𝔞 d →
        fnAt y f * ((δ.loc ((m : 𝓞 E ⧸ a.named) ^ (D.p + D.q)) : C.c₂.F) : ℂ) =
          ((δ.loc d * δ.ideal 𝔞 : C.c₂.F) : ℂ)

end Cover

section Delta

variable {D : Datum H} {l : Level H}

structure DeltaDatum (Xo : Moduli D l) (c : Coeff l) (nab : NabV Xo c) where
  a : IsAuxiliarySplitSquarefreeLevel l
  split : a.SplitsCompletely
  cov : Cover Xo c a
  nab₂ : NabV cov.Xo₂ cov.c₂
  nab_over : cov.NabOver nab nab₂
  δ : DeltaChar a cov.c₂.F
  vol : Vol D a
  fn : Γ(cov.Xo₂.XF cov.c₂, ⊤)
  fn_eq : IsDeltaDet cov δ fn

namespace DeltaDatum

variable {Xo : Moduli D l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

def fnVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) : S :=
  fnAt (basePt y₂) Δ.fn

def combined {n : ℕ} (x₀ : Fin n → ConjCl D l) (x : Fin n → ConjCl D Δ.a.l₂) : Δ.cov.c₂.F :=
  Δ.cov.incl (indicatorCl c x₀ fun b => Δ.a.red D (x b)) * phiDelta Δ.δ Δ.vol x

def combinedCoeff {n : ℕ} (x₀ : Fin n → ConjCl D l) (t : Fin n → NamedCl D Δ.a.l₂) : Δ.cov.c₂.F :=
  fourier Δ.cov.c₂ (Δ.combined x₀) t

end DeltaDatum

variable {Xo : Moduli D l} {c : Coeff l} {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

end Delta

section Trivial

variable {D : Datum H} {l : Level H}


end Trivial

end GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
