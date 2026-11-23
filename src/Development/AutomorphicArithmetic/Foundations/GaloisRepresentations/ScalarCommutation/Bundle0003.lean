module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSliceAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateEigenSubDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldedEqOrbitalReps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AdmCusp
section
theorem UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm :
    UpperTheory.Gal.Spc.AdmCusp := by
  intro X _ k _ _ _ _ _ _ _ n Ty hJo hJc hker hcusp f hf h hh
  have hform : ∀ g, f (Ty.L.loc g * h) = UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ g * f h := by
    intro g
    unfold UpperTheory.Gal.W2.Seed.tyFn
    split_ifs with hg
    · rw [Ty.L.comm g h hh]
      exact hf.2.2 ⟨g, hg⟩ h
    · rw [zero_mul]
      by_contra hne
      apply hg
      have hmem := hf.2.1 _ hne
      rwa [map_mul, Ty.L.pr_loc, hh, mul_one] at hmem
  have hTC : GlobalTheory.Block5c.TypeCusp := GlobalTheory.typeFunction_constantTerm_eq_zero
  have hT := hTC k (Fin n) Ty.J hJo hJc Ty.ψ hker
    (fun a b e ha hb u hu h₀ =>
      UpperTheory.Gal.Spc.typeSlice k n Ty.J hJo hJc Ty.ψ hker hcusp a b e ha hb u hu h₀)
    (UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ)
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
  intro a b ε ha hb μ hμ u hu g₀ h₀
  have hz := hT.2.2.2 a b ε ha hb μ hμ u hu g₀ h₀
  simp_rw [hform]
  rw [MeasureTheory.integral_mul_const, hz, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

def Extra (S : Setup A n p) (j : GUf E n →* S.G.GAf) : Prop :=
  (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∃ P : Pl S.G (w.adicCompletion E), ∀ g, P.at (j g) = (comp w g).val) ∧
  ∀ q : ℕ, q.Prime → q ≠ p → ∀ g : GUf E n, (∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → (comp w g).val.charpoly.Separable) →
    GlobalTheory.LKCx.RegAf S.G (j g)

def PlTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S)
  (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∃ P : Pl S.G (w.adicCompletion E), ∀ g, P.at (T.j g) = (comp w g).val

def RegTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S)
  (q : ℕ), q.Prime → q ≠ p → ∀ g : GUf E n, (∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → (comp w g).val.charpoly.Separable) →
    GlobalTheory.LKCx.RegAf S.G (T.j g)

def IsFac (F : Frame S) (w : Spl E p) (L : Loc S.G.GAf (GLw n w.1)) : Prop :=
  (∀ g, L.pr (F.j g) = comp w.1 g) ∧ ∀ y, L.loc y = F.j (CertificateRingHomMap.loc w.2.1 y)

def FacEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (w : Spl E p), ∃ L, IsFac F w L

def FacCont : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (w : Spl E p) (L : Loc S.G.GAf (GLw n w.1)), IsFac F w L → Continuous L.pr

def SplitC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Lv : G.Level) (k : Type) [Field k] [TopologicalSpace k] [T2Space k] [Algebra G.F k] (P : Pl G k)
    (L : Loc G.GAf (GL (Fin G.n) k)), Continuous L.pr → (∀ g, P.at g = (L.pr g : Matrix (Fin G.n) (Fin G.n) k)) →
    ∀ Kw : Subgroup (GL (Fin G.n) k), IsOpen (Kw : Set (GL (Fin G.n) k)) → IsCompact (Kw : Set (GL (Fin G.n) k)) →
    L.Fact Lv.K.toSubgroup Kw → ∃ (_ : TopologicalSpace L.pr.ker) (_ : IsTopologicalGroup L.pr.ker) (_ : T2Space L.pr.ker)
      (S : Split P Lv.K.toSubgroup L.pr.ker), ∀ g h, S.e.symm (g, h) = L.loc g * h

def SepConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E),
  (comp w g).val.charpoly.Separable → (comp (cj w) g).val.charpoly.Separable

variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

abbrev Iw (n : ℕ) (w : Plc E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

structure SlopeTestRemainingChoices (S : Setup A n p) (V : Vec x U w₀ Up) (r : ℕ) (W : Finset (Spl E p)) : Prop where
  prime : r.Prime
  ne : r ≠ p
  good : A.Good r
  off : ∀ u ∈ V.S, (r : 𝓞 E) ∉ u.asIdeal
  half : Half r W
  nonempty : W.Nonempty

structure TyOK (F : Frame S) (V : Vec x U w₀ Up) (W : Finset (Spl E p)) (N : ℕ) (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1))
    (hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal) (Ty : TyLev S.G.GAf (GLw n w₀)) : Prop where
  fac : ∀ w, IsFac F w (L w)
  L_eq : Ty.L = L ⟨w₀, hw⟩
  K₀_eq : Ty.K₀ = S.L.KN N
  K_iff : ∀ k, k ∈ Ty.K ↔ (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1
  J_iff : ∀ y y' : GLw n w₀, y'.val = (y⁻¹).valᵀ → (y ∈ Ty.J ↔ y' ∈ V.J)
  ψ_eq : ∀ (y : Ty.J) (y' : V.J), (y' : GLw n w₀).val = ((y : GLw n w₀)⁻¹).valᵀ → Ty.ψ y = V.χ y'

def Off2 (W : Finset (Spl E p)) (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) (Ty : TyLev S.G.GAf (GLw n w₀)) :
    Submodule ℂ (S.G.GAf → ℂ) :=
  Submodule.span ℂ {f | ∃ h, Ty.L.pr h = 1 ∧ (∀ w ∈ W, (L w).pr h = 1) ∧ f = Ty.tf h}

def ForData (q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (_ : Frame S) (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (_ : Vec x U w₀ Up) (_ : ℕ)
    (_ : Finset (Spl E p)) (_ : Lv p) (_ : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) (_ : TyLev S.G.GAf (GLw n w₀)), Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Odd n → Sc S.D S.G → Gen A x → Off V p → (∃ q : ℕ, q.Prime ∧ A.Good q ∧ (q : 𝓞 E) ∈ w₀.asIdeal) →
    ∀ (r : ℕ) (W : Finset (Spl E p)), SlopeTestRemainingChoices S V r W → ∀ N : Lv p, r ∣ N.1 →
    (∀ k ∈ S.L.KN N.1, Stab F V k) → ∀ (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) hw (Ty : TyLev S.G.GAf (GLw n w₀)),
    TyOK F V W N.1 L hw Ty → q E A n p S F x U w₀ Up V r W N L Ty

def AuxiliaryInertOddPrime : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up), Gen A x → ∀ X : Finset ℕ,
  ∃ r W, r ∉ X ∧ SlopeTestRemainingChoices S V r W

def TyEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up), Off V p →
  ∀ (r : ℕ) (W : Finset (Spl E p)), SlopeTestRemainingChoices S V r W → ∀ N : Lv p, r ∣ N.1 → (∀ k ∈ S.L.KN N.1, Stab F V k) →
  ∃ L hw Ty, TyOK F V W N.1 L hw Ty

def TyTop : Prop := ForData fun _ _ _ _ _ n _ _ S _ _ _ w₀ _ _ _ _ N _ Ty =>
  (∃ Lv : S.G.Level, Lv.K.toSubgroup = S.L.KN N.1) ∧
  (∃ Kw : Subgroup (GLw n w₀), IsOpen (Kw : Set (GLw n w₀)) ∧ IsCompact (Kw : Set (GLw n w₀)) ∧ Ty.L.Fact Ty.K₀ Kw) ∧
  IsOpen (Ty.J : Set (GLw n w₀)) ∧ IsCompact (Ty.J : Set (GLw n w₀)) ∧ IsOpen (Ty.ψ.ker : Set Ty.J) ∧
  ∀ (σ : SmIrr (GLw n w₀)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ

def TyFact : Prop := ForData fun E _ _ _ _ n p _ S _ _ _ _ _ V _ W _ L Ty =>
  (∀ w ∈ W, (L w).Fact Ty.K (Iw n w.1) ∧ Ty.L.Apart (L w) ∧ ∀ w' ∈ W, w ≠ w' → (L w).Apart (L w')) ∧
  (∀ w : Spl E p, w.1 ∉ V.S → cj w.1 ∉ V.S → (∀ u ∈ W, GlobalTheory.Cong.Apart w.1 u.1) →
    (L w).Fact Ty.K (GlobalTheory.LFun.KGL w.1 (n := n)) ∧ Ty.L.Apart (L w)) ∧
  ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ∀ k ∈ Ty.K, ∀ v ∈ LaHat S.D, c • S.L.actG k v ∈ LaHat S.D

def ExistsIdempotentHeckeOperatorWithRegularSupport : Prop := ForData fun E _ _ _ _ n p _ S _ _ _ _ _ _ _ W _ L Ty =>
  ∃ u ∈ Hecke ℂ Ty.K₀, ∃ u' ∈ Hecke ℂ Ty.K₀, conv Ty.K₀ (Ty.tf 1) u = u ∧ conv Ty.K₀ u (Ty.tf 1) = u ∧ conv Ty.K₀ u' u = Ty.tf 1 ∧
    (∀ f ∈ Off2 W L Ty, conv Ty.K₀ u f = conv Ty.K₀ f u) ∧
    ∀ m : ℕ, 1 ≤ m → ∃ X : ∀ w : Spl E p, Set (GLw n w.1),
      (∀ w ∈ W, ∀ y ∈ X w, y.val.charpoly.Separable ∧ ∀ a ∈ Iw n w.1, a * y ∈ X w) ∧
      ∀ g, powFn Ty.K₀ u (Ty.tf 1) m g ≠ 0 → Integ S.L g⁻¹ ∧ ∀ w ∈ W, (L w).pr g ∈ X w

def MemFn : Prop := ForData fun _ _ _ _ _ n _ _ S F _ _ _ _ V r W N L Ty => ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ →
  g.fn ∈ Hecke ℂ Ty.K₀ ∧ (∀ a, g.fn a ≠ 0 → ∀ w ∈ W, (L w).pr a ∈ Iw n w.1) ∧
  ((IsDeckM g ∧ θ = 1 ∧ conv Ty.K₀ g.fn (Ty.tf 1) = Ty.tf 1) ∨
    (Ty.L.pr g.h = 1 ∧ (∀ w ∈ W, (L w).pr g.h = 1) ∧
      conv Ty.K₀ g.fn (Ty.tf 1) = (idx g : ℂ) • Ty.tf g.h⁻¹))

def MemComm : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r W N L Ty => ∀ (g g' : Mem S.L N) (θ θ' : ℂ),
  Seen F V r g θ → Seen F V r g' θ' → conv Ty.K₀ g.fn (Ty.tf 1) ∈ Off2 W L Ty ∧
    conv Ty.K₀ g.fn (conv Ty.K₀ g'.fn (Ty.tf 1)) = conv Ty.K₀ g'.fn (conv Ty.K₀ g.fn (Ty.tf 1))

def PhiEx : Prop := ForData fun E _ _ _ _ n p _ S F _ _ _ _ V r _ N _ Ty =>
  ∃ φ : S.G.GAf → Module.Dual ℂ V.W.Sp, φ ≠ 0 ∧ Ty.IsTy φ ∧
    (∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ GlobalTheory.LFun.KGL w (n := n)) → φ (F.j g) = V.Φ (F.th g)) ∧
    ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ → Formalism.UG.hAct Ty.K₀ g.fn φ = θ • φ

def EigEx : Prop := ForData fun E _ _ _ _ n _ _ S F _ _ _ _ V r _ N _ Ty =>
  ∃ thQ : GL (Fin n) E × ℚˣ →* GL (Fin n) E × ℚˣ, (∀ y, (thQ y).1.val = (y.1⁻¹).valᵀ ∧ (thQ y).2 = y.2⁻¹) ∧
    ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ), (∀ j, Seen F V r (g j) (θ j)) →
      HasEig S.G ((CertificateRingHomMap.xi V.W V.jz).comp thQ) Ty.K₀ (fun j => (g j).fn) θ (Ty.tf 1)

def SpecData : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r _ N _ _ => Extra S F.j →
  ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ), (∀ j, Seen F V r (g j) (θ j)) →
    ∃ f, IsFnL S.L N.1 f ∧ Spec S.L V.lam (S.L.KN N.1) (fun j => (g j).fn) θ f

def SpecTopG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (F : Frame S) (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Odd n → Sc S.D S.G → Gen A x → Off V p → (∃ q : ℕ, q.Prime ∧ A.Good q ∧ (q : 𝓞 E) ∈ w₀.asIdeal) →
    ∀ X : Finset ℕ, ∃ r₀ : ℕ, r₀.Prime ∧ r₀ ∉ X ∧ r₀ ≠ p ∧
      ∀ N : Lv p, r₀ ∣ N.1 → (∀ k ∈ S.L.KN N.1, Stab F V k) → ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ),
        (∀ j, Seen F V r₀ (g j) (θ j)) → ∃ f, IsFnL S.L N.1 f ∧ Spec S.L V.lam (S.L.KN N.1) (fun j => (g j).fn) θ f

end UpperTheory.Gal.Spc
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanForms
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.LKCount
  GlobalTheory.LKCount.OrbKProd GlobalTheory.BCT UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

variable {p : ℕ} [Fact p.Prime]

private def atHom {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) : G.GAf →* GL (Fin G.n) k :=
  (Units.map (P.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k)).comp
    ((MonoidHom.fst _ _).comp (Subgroup.subtype _))

private theorem charpoly_at_toAfF {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) :
    (P.at (toAfF G β x t hx y)).charpoly = (P.ι ((y.1.1 : G.Cˣ) : G.C)).charpoly := by
  have h := Matrix.charpoly_units_conj (Units.map (P.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k) x)
    (P.ι ((y.1.1 : G.Cˣ) : G.C))
  rw [← h, ← P.κ_ι]
  have e : P.at (toAfF G β x t hx y) =
      P.κ (x : AfP p ⊗[ℚ] G.C) * P.κ (1 ⊗ₜ ((y.1.1 : G.Cˣ) : G.C)) * P.κ ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    rw [← map_mul, ← map_mul]
    rfl
  rw [e, ← Matrix.coe_units_inv]
  rfl

private theorem toAfF_cent_comm {G : HTGroup p} (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    ∀ a ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y),
    ∀ b ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y), a * b = b * a := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC ((y.1.1 : G.Cˣ) : G.C) hsep hdeg
  have hcent : ∀ w : G.C, w * ((y.1.1 : G.Cˣ) : G.C) = ((y.1.1 : G.Cˣ) : G.C) * w ↔
      w ∈ Set.range ((Algebra.adjoin G.F ({((y.1.1 : G.Cˣ) : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
    intro w
    constructor
    · intro h
      have hw : w ∈ Subalgebra.centralizer G.F {((y.1.1 : G.Cˣ) : G.C)} := by
        rw [Subalgebra.mem_centralizer_iff]
        simpa using h.symm
      rw [hcsa] at hw
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      have hw : (v : G.C) ∈ Subalgebra.centralizer G.F {((y.1.1 : G.Cˣ) : G.C)} := by rw [hcsa]; exact v.2
      rw [Subalgebra.mem_centralizer_iff] at hw
      exact (hw _ rfl).symm
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y.1.1 with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C) := rfl
  have hδ : ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have conj : ∀ a ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y),
      (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
          ((1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C)) *
          (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
    intro a ha
    have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
    simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
    rw [hδ] at h1
    set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
      calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
        _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
        _ = U * (x⁻¹ * A * x) := by group
    rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]
  intro a ha b hb
  have hc := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (AfP p) G.C _ ((y.1.1 : G.Cˣ) : G.C) _ hcent _ _ (conj a ha) (conj b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

private theorem twisted_centralizer_commutative {G : HTGroup p} (β : G.Cˣ) (y : grp G β)
    (hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    ∀ a ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y),
    ∀ b ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y), a * b = b * a := by
  have hrho : ∀ w, (G.rho w ((y.1.1 : G.Cˣ) : G.C)).charpoly.Separable := by
    intro w
    letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
    have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
      fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
    let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
    have h := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F (G.Fw w) G.C G.n G.rankC g _ hdeg
    have e : g ((y.1.1 : G.Cˣ) : G.C) = G.rho w ((y.1.1 : G.Cˣ) : G.C) := rfl
    rw [e] at h
    rw [h]
    exact hsep.map
  have hb := GlobalTheory.TorCls.AtP.inclG_one_bijective G
  have hy : toP1 G β y = inclG G 1 (locC G y.1) := rfl
  have key : ∀ a ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y), ∃ a' : Gp G, inclG G 1 a' = a ∧
      a' * locC G y.1 = locC G y.1 * a' := by
    intro a ha
    obtain ⟨a', rfl⟩ := hb.2 a
    refine ⟨a', rfl, hb.1 ?_⟩
    rw [map_mul, map_mul, ← hy]
    exact ha
  intro a ha b hb'
  obtain ⟨a', rfl, ha'⟩ := key a ha
  obtain ⟨b', rfl, hb''⟩ := key b hb'
  rw [← map_mul, ← map_mul]
  congr 1
  refine Prod.ext (mul_comm _ _) (funext fun w => ?_)
  exact GlobalTheory.CentSep.centraliser_comm_of_separable (G.Fw w) (Fin G.n) ((locC G y.1).2 w) (a'.2 w) (b'.2 w) (hrho w)
    (congrFun (congrArg Prod.snd ha') w) (congrFun (congrArg Prod.snd hb'') w)

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.vanForms :
    UpperTheory.Gal.Spc.VanForms := by
  intro p _ G _ Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ f hf hC hR B x t hx y hy
  by_cases hs1 : (P₁.ι ((y.1.1 : G.Cˣ) : G.C)).charpoly.Separable
  · have hns := GlobalTheory.SepCharpoly.not_separable_charpoly G.F k₁ G.C G.n P₁.ι ((y.1.1 : G.Cˣ) : G.C)
    have hle := GlobalTheory.VanishNonEll.natDegree_minpoly_le G.F k₁ G.C G.n G.n_pos P₁.ι ((y.1.1 : G.Cˣ) : G.C)
    have hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n := by
      by_contra h
      exact hns (Or.inl (lt_of_le_of_ne hle h)) hs1
    have hms : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable := by
      by_contra h
      exact hns (Or.inr ⟨hdeg, h⟩) hs1
    have hirr : ¬ Irreducible (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)) := fun h => hy ⟨hdeg, hms, h⟩
    have hcp := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F k G.C G.n G.rankC P.ι ((y.1.1 : G.Cˣ) : G.C) hdeg
    have hat := charpoly_at_toAfF P B.β x t hx y
    rw [hcp] at hat
    have hδs : (P.at (toAfF G B.β x t hx y)).charpoly.Separable := by
      rw [hat]
      exact hms.map
    have hδi : ¬ Irreducible (P.at (toAfF G B.β x t hx y)).charpoly := by
      rw [hat]
      exact GlobalTheory.VanishNonEll.not_irreducible_map _ _ (minpoly.monic (IsIntegral.of_finite G.F _)) hirr
    have hT₁ := toAfF_cent_comm B.β x t hx y hdeg hms
    have hT₂ := twisted_centralizer_commutative B.β y hdeg hms
    have h1 := orbK_eq_zero_of_cuspSlices S f hf hC _ hδs hδi hT₁
    have hbi : Formalism.UG.IsBiInv Lv.K.toSubgroup f := hf.1
    refine orbK_prod_eq_zero_of_slices Lv.K.toSubgroup (Kp G) (toAfF G B.β x t hx y) (toP1 G B.β y) _ hT₁ hT₂ ?_ fun z => ?_
    · intro c hc w
      rw [Subgroup.mem_prod] at hc
      have e1 : f (c.1⁻¹ * w.1 * c.1) = f w.1 :=
        hbi ⟨c.1⁻¹, Subgroup.inv_mem _ hc.1⟩ ⟨c.1, hc.1⟩ _
      have e2 : oneP G (c.2⁻¹ * w.2 * c.2) = oneP G w.2 := by
        have hiff : c.2⁻¹ * w.2 * c.2 ∈ Kp G ↔ w.2 ∈ Kp G := by
          rw [(Kp G).mul_mem_cancel_right hc.2, (Kp G).mul_mem_cancel_left ((Kp G).inv_mem hc.2)]
        unfold oneP
        by_cases hw : w.2 ∈ Kp G
        · rw [Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hiff.2 hw),
            Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hw)]
          rfl
        · rw [Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from fun h => hw (hiff.1 h)),
            Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from hw)]
      show f (c.1⁻¹ * w.1 * c.1) * oneP G (c.2⁻¹ * w.2 * c.2) = f w.1 * oneP G w.2
      rw [e1, e2]
    · unfold orbK at h1 ⊢
      rw [orbC_eq] at h1 ⊢
      have e : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) : Set G.GAf)
          (Lv.K.toSubgroup : Set G.GAf),
          oTerm (MonoidHom.id G.GAf) Lv.K.toSubgroup
            (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) ⊓ Lv.K.toSubgroup) (toAfF G B.β x t hx y)
            (fun v => f v * oneP G z) (Quotient.out q) =
          oneP G z * oTerm (MonoidHom.id G.GAf) Lv.K.toSubgroup
            (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) ⊓ Lv.K.toSubgroup) (toAfF G B.β x t hx y) f
            (Quotient.out q) := by
        intro q
        unfold oTerm
        ring
      rw [finsum_congr e]
      exact finsum_mul_eq_zero _ _ h1
  · refine GlobalTheory.orbK_eq_zero_of_charpoly_not_separable _ k₁ G.n ((atHom P₁).comp (MonoidHom.fst _ _)) _ _ _ ?_ ?_
    · intro g hg
      exact hR g.1 (left_ne_zero_of_mul hg)
    · intro h
      apply hs1
      rw [← charpoly_at_toAfF P₁ B.β x t hx y]
      exact h
end
end

