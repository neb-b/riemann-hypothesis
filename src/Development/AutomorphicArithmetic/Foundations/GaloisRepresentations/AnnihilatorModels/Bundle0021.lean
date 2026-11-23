module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MWModEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private def killedSub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S) :
    letI := ptModuleWvs o T
    Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) :=
  letI := ptModuleWvs o T
  { carrier := {g | KilledBy o w g.toMul}
    zero_mem' := KilledBy.one o w T
    add_mem' := fun {g h} hg hh a ha => by
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg a ha, hh a ha, _root_.mul_one]
    smul_mem' := fun c g hg a ha => by
      show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg a ha,
        one_comp] }

theorem UpperTheory.Gal.crystallineComparison.Mod.wModEx_of :
    WModEx := by
  intro p _ D R _ b N S s o w T
  letI := ptModuleWvs o T
  have htor : Module.IsTorsionBySet (𝓞 D.F) (killedSub o w T) (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show (a : 𝓞 D.F) • (x : Additive (T ⟶ o.A)) = Additive.ofMul 1
    exact x.2 a a.2
  letI : Module (𝓞 D.F ⧸ w) (killedSub o w T) := htor.module
  refine ⟨⟨killedSub o w T, fun x => Additive.toMul (x : Additive (T ⟶ o.A)), ?_, ?_, ?_, ?_⟩⟩
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective h)
  · intro g
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hg
      exact ⟨⟨Additive.ofMul g, hg⟩, rfl⟩
  · intro x y
    rfl
  · intro a x
    rw [Module.IsTorsionBySet.mk_smul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

def KerAt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left) : Prop :=
  ∀ a' : Over.mk z ⟶ T.o.A, a'.left ≫ T.ms.φ = a → a' ≫ T.ψ = 1

def PulledRead : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c)
    (S : Scheme.{0}) (x : S ⟶ M.X) (σ : S ⟶ Sp R) (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y : S ⟶ T.Y), y ≫ T.s = x →
    ∀ (P : Pulled T m₁ y) (a : 𝟙_ (Over S) ⟶ o₁.A), (a ≫ P.ψ = 1 ↔ KerAt T y (a.left ≫ m₁.φ)) ∧
      ∀ h, T.img y (a.left ≫ m₁.φ) h = (a ≫ P.ψ).left ≫ P.m'.φ ≫ T.mt.φ

def SecCard : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c), D.m = 1 →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ (x : Sp K ⟶ M.X) (y : Sp K ⟶ T.Y), y ≫ T.s = x →
    Nat.card {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g ∧ KerAt T y g.left} = Ideal.absNorm w ^ j

def SecInj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 →
    ∀ (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    (∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → (KerAt T y g.left ↔ KerAt T y' g.left)) → y = y'

def SecSurj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 →
    ∀ (x : Sp K ⟶ M.X) (G : Subgroup (Over.mk x ⟶ M.univ.A)), (∀ g ∈ G, KilledBy M.univ w g) →
    (∀ g ∈ G, ∀ a : 𝓞 D.F, g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O a) ∈ G) → Nat.card G = Ideal.absNorm w ^ j →
    ∃ y : Sp K ⟶ T.Y, y ≫ T.s = x ∧ ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → (KerAt T y g.left ↔ g ∈ G)

def WVal : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (w : Ideal (𝓞 D.F)) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : Sp V ⟶ M.X),
    ∃ ρ : (Over.mk x ⟶ M.univ.A) ≃* (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A),
      (∀ g, (ρ g).left = spMap (algebraMap V (FractionRing V)) ≫ g.left) ∧ (∀ g (a : M.univ.A ⟶ M.univ.A), ρ (g ≫ a) = ρ g ≫ a) ∧
      (∀ g, KilledBy M.univ w g ↔ KilledBy M.univ w (ρ g)) ∧
      ∀ (r : ℤ) (j c : ℕ) (T : TjD M r w j c) (z : Sp V ⟶ T.Y), z ≫ T.s = x → ∀ g,
        KerAt T z g.left ↔ KerAt T (spMap (algebraMap V (FractionRing V)) ≫ z) (ρ g).left

def RankN : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 → ∀ (x : Sp V ⟶ M.X) (W : WMod M.univ w (Over.mk x)),
    Module.Finite (𝓞 D.F ⧸ w) W.H ∧ Module.finrank (𝓞 D.F ⧸ w) W.H = D.n

def LineC : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [IsAlgClosed (IsLocalRing.ResidueField V)], (p : V) ≠ 0 → ∀ (x : Sp V ⟶ M.X), IsWOrd M.univ w (resPt V ≫ x) →
    ∀ W : WMod M.univ w (Over.mk x), ∃ C : Submodule (𝓞 D.F ⧸ w) W.H, Module.finrank (𝓞 D.F ⧸ w) C = 1 ∧
      ∀ a a', resPt V ≫ (W.pt a).left = resPt V ≫ (W.pt a').left ↔ a - a' ∈ C

def SecEquiv : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 →
    ∀ (x : Sp V ⟶ M.X) (W : WMod M.univ w (Over.mk x)), ∃ e : {z : Sp V ⟶ T.Y // z ≫ T.s = x} ≃ Gr (𝓞 D.F ⧸ w) W.H j,
      ∀ z h, h ∈ (e z).1 ↔ KerAt T z.1 (W.pt h).left

def KerRead : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ) (T : TjD M r w j (p ^ (f * j))) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 →
    ∀ (x : Sp V ⟶ M.X) (z : Sp V ⟶ T.Y), z ≫ T.s = x → ∀ (σ : Sp (IsLocalRing.ResidueField V) ⟶ Sp O) (o₁ : Obj b N σ)
      (m₁ : ObjMap o₁ M.univ (resPt V ≫ x)) (P : Pulled T m₁ (resPt V ≫ z)), RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j) ∧
      ∀ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A, UKer r o₁ P.ψ _ a ↔
        ∃ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g ∧ KerAt T z g.left ∧ a.left ≫ m₁.φ = resPt V ≫ g.left

def CaseE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ M.X) (σ : Sp κ ⟶ Sp O),
    x ≫ M.s = σ → ∀ (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y y' : Sp κ ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    ∀ (P : Pulled T m₁ y) (P' : Pulled T m₁ y') (d : ℕ), RepAlg o₁.A (UKer r o₁ P.ψ) d → RepAlg o₁.A (UKer r o₁ P'.ψ) d →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A // UKer r o₁ P.ψ _ g} = d → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, UKer r o₁ P.ψ _ g ↔ UKer r o₁ P'.ψ _ g) →
    y ≫ T.t = y' ≫ T.t ∧ ∀ a h h', T.img y a h = T.img y' a h'

def CaseW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ) (j₁ : ℕ), j₁ = j + 1 → ∀ (T : TjD M r w j₁ (p ^ (f * j₁))) (T' : TjD M r w j (p ^ (f * j)))
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (φ : κ →+* κ), (∀ a, φ a = a ^ p ^ f) → ∀ (x : Sp κ ⟶ M.X) (β : O →+* κ),
    x ≫ M.s = spMap β → (∀ a ∈ IsLocalRing.maximalIdeal O, β a = 0) → ∀ (o₁ : Obj b N (spMap β)) (m₁ : ObjMap o₁ M.univ x)
      (y : Sp κ ⟶ T.Y) (y' : Sp κ ⟶ T'.Y), y ≫ T.s = x → y' ≫ T'.s = x → ∀ (P : Pulled T m₁ y) (P' : Pulled T' m₁ y'),
    RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j₁) → RepAlg o₁.A (UKer r o₁ P'.ψ) ((p ^ f) ^ j) →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A // UKer r o₁ P'.ψ _ g} = (p ^ f) ^ j → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, UKer r o₁ P.ψ _ g ↔ UKer r o₁ P'.ψ _ g) →
    y ≫ T.t = spMap φ ≫ y' ≫ T'.t ∧ ∀ a h h', T.img y a h = spMap φ ≫ T'.img y' a h'

def PowExt : Prop := ∀ (S : Scheme.{0}) (A : Over S) (k : ℕ), (Smooth A.hom → Flat (GlobalTheory.KS.pow A k).hom) ∧
    ∀ (X : Scheme.{0}) (u v : X ⟶ (GlobalTheory.KS.pow A k).left), u ≫ (GlobalTheory.KS.pow A k).hom = v ≫ (GlobalTheory.KS.pow A k).hom →
      (∀ i, u ≫ (GlobalTheory.KS.pr A i).left = v ≫ (GlobalTheory.KS.pr A i).left) → u = v

end UpperTheory.Gal.crystallineComparison.Mod
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.TensorDecomp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open scoped TensorProduct

private lemma UpperTheory.Gal.crystallineComparison.Mod.tensor_decomp (p : ℕ) [Fact p.Prime] (B : Type) [AddCommGroup B]
    (a : B ⊗[ℤ] ℤ_[p]) :
    ∃ (c : B) (a' : B ⊗[ℤ] ℤ_[p]), a = c ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • a' := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c z =>
    obtain ⟨r, z', hz⟩ : ∃ (r : ℤ) (z' : ℤ_[p]), z = r • (1 : ℤ_[p]) + (p : ℤ) • z' := by
      have h : z - (PadicInt.zmodRepr z : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
        rw [← PadicInt.maximalIdeal_eq_span_p]
        exact PadicInt.sub_zmodRepr_mem z
      obtain ⟨z', hz'⟩ := Ideal.mem_span_singleton'.mp h
      refine ⟨(PadicInt.zmodRepr z : ℤ), z', ?_⟩
      have : z = (PadicInt.zmodRepr z : ℤ_[p]) + z' * p := by rw [hz']; ring
      simp only [zsmul_eq_mul, mul_one]
      push_cast
      rw [mul_comm (p : ℤ_[p])]
      first | (rw [mul_one]; exact this) | simpa using this
    refine ⟨r • c, c ⊗ₜ[ℤ] z', ?_⟩
    rw [hz, TensorProduct.tmul_add, TensorProduct.tmul_smul (p : ℤ), TensorProduct.tmul_smul r,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨c, a', rfl⟩ := ha
    obtain ⟨d, b', rfl⟩ := hb
    exact ⟨c + d, a' + b', by rw [TensorProduct.add_tmul, smul_add]; abel⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.oMod_of :
    OMod := by
  intro p _ D hm x
  obtain ⟨e⟩ := D.splitP
  have hsub : Subsingleton (Fin D.m) := by rw [hm]; infer_instance
  let i0 : Fin D.m := ⟨0, D.m_pos⟩
  obtain ⟨c, a', ha⟩ := tensor_decomp p (𝓞 D.F) (e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) i0 i0)
  let M' : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) := Matrix.of fun _ _ => a'
  have hM : e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) _ c + (p : ℤ) • M' := by
    ext i j
    obtain rfl := Subsingleton.elim i i0
    obtain rfl := Subsingleton.elim j i0
    rw [ha]
    simp [M', Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply]
  have hx : x ⊗ₜ[ℤ] (1 : ℤ_[p]) =
      (algebraMap (𝓞 D.F) D.O c) ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • e.symm M' := by
    have := congrArg e.symm hM
    rw [e.symm_apply_apply, map_add (f := _), map_zsmul, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply] at this
    exact this
  let P : Submodule ℤ D.O := LinearMap.range (LinearMap.lsmul ℤ D.O (p : ℤ))
  have hP : ∀ q : D.O ⧸ P, p • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  letI : Module (ZMod p) (D.O ⧸ P) := AddCommGroup.zmodModule hP
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₗ[ℤ] D.O ⧸ P := TensorProduct.lift <|
    LinearMap.mk₂ ℤ (fun y z => PadicInt.toZMod z • (Submodule.Quotient.mk y : D.O ⧸ P))
      (fun y y' z => by simp [smul_add])
      (fun n y z => by rw [Submodule.Quotient.mk_smul]; exact smul_comm _ _ _)
      (fun y z z' => by simp [add_smul])
      (fun n y z => by rw [map_zsmul, smul_assoc])
  have h1 : ∀ y : D.O, Φ (y ⊗ₜ[ℤ] (1 : ℤ_[p])) = Submodule.Quotient.mk y := by
    intro y
    change PadicInt.toZMod (1 : ℤ_[p]) • (Submodule.Quotient.mk y : D.O ⧸ P) = _
    rw [map_one, one_smul]
  have h2 := congrArg Φ hx
  rw [map_add (f := _), map_zsmul, h1, h1] at h2
  have h3 : (p : ℤ) • Φ (e.symm M') = 0 := by
    rw [natCast_zsmul]; exact hP _
  rw [h3, add_zero, Submodule.Quotient.eq] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨c, y, ?_⟩
  have hy' : (p : ℤ) • y = x - algebraMap (𝓞 D.F) D.O c := hy
  rw [map_natCast, ← sub_eq_iff_eq_add', ← hy']
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.UEltOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.uElt_of :
    UElt := by
  intro p _ D r w hw huw e
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hbb : ∀ x : 𝓞 D.F, D.bar (D.bar x) = x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    rw [D.bar_eq, D.bar_eq]
    exact IsCMField.complexConj_apply_apply _ _
  have hp : (p : 𝓞 D.F) ∈ uIdeal D r := p_mem_uIdeal D r
  have hs : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r := sub_mem_uIdeal D r
  set ub : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.bar D.ω - (r : 𝓞 D.F)} with hub
  have hmap : Ideal.map D.bar (uIdeal D r) = ub := by
    simp [uIdeal, Ideal.map_span, Set.image_pair, hub]
  have hc : (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - r) = (r : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * r + D.nm := by
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    apply hw
    rw [Ideal.eq_top_iff_one]
    apply huw
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - r) * (D.bar D.ω - r)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * hc
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hs))
  have hprod : uIdeal D r * ub ≤ Ideal.span {(p : 𝓞 D.F)} := by
    obtain ⟨k, hk⟩ := hdvd
    show Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)} * ub ≤ _
    rw [hub, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [SetLike.mem_coe, hc, Ideal.mem_span_singleton]
      exact ⟨(k : 𝓞 D.F), by exact_mod_cast hk⟩
  have hsup : uIdeal D r ⊔ ub = ⊤ := by
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 D.disc_p
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    rw [Ideal.eq_top_iff_one]
    have hdiff : D.ω - D.bar D.ω ∈ uIdeal D r ⊔ ub := by
      have : D.ω - D.bar D.ω = (D.ω - r) - (D.bar D.ω - r) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hs) (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    have hpm : (p : 𝓞 D.F) ∈ uIdeal D r ⊔ ub := Ideal.mem_sup_left hp
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - D.bar D.ω) * (D.ω - D.bar D.ω)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * (D.ω + D.bar D.ω + D.tr) * D.tr_eq + 4 * (b : 𝓞 D.F) * D.nm_eq
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hdiff))
  have hcopE : uIdeal D r ^ e ⊔ ub ^ e = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hsup).pow)
  have hle : uIdeal D r ^ e * ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← mul_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hprod e
  have hinf : uIdeal D r ^ e ⊓ ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← Ideal.mul_eq_inf_of_coprime hcopE]
    exact hle
  have h1 : (1 : 𝓞 D.F) ∈ uIdeal D r ^ e ⊔ ub ^ e := by
    rw [hcopE]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  have hbz : D.bar z ∈ uIdeal D r ^ e := by
    rw [← hmap, ← Ideal.map_pow] at hz
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv D.bar z).mp hz
    rwa [hbb]
  have hup : ∀ x ∈ uIdeal D r ^ e, D.bar x ∈ ub ^ e := by
    intro x hx
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  have hx0u : z + D.bar z - 1 ∈ uIdeal D r ^ e := by
    have : z + D.bar z - 1 = D.bar z - y := by
      rw [← hyz]
      ring
    rw [this]
    exact Ideal.sub_mem _ hbz hy
  have hx0b : z + D.bar z - 1 ∈ ub ^ e := by
    have h := hup _ hx0u
    have : D.bar (z + D.bar z - 1) = z + D.bar z - 1 := by
      rw [map_sub, map_add (f := _), map_one, hbb]
      ring
    rwa [this] at h
  exact ⟨z, fun a ha => hle (Ideal.mul_mem_mul ha hz), hinf (Ideal.mem_inf.mpr ⟨hx0u, hx0b⟩), hbz⟩
end

