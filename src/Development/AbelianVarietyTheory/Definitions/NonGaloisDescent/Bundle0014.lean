module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal

namespace GlobalTheory.BSP

section Cover

variable {l : ℕ} {R : Type} [CommRing R]

abbrev adI (B : Obj l R) : Ideal B.A := Ideal.span {(l : B.A)} ⊔ B.I

theorem adI_pow_le {B B' : Obj l R} (f : Hom B B') (m : ℕ) : adI B ^ m ≤ (adI B' ^ m).comap f.f := by
  refine le_trans (Ideal.pow_right_mono ?_ m) (Ideal.le_comap_pow f.f m)
  refine sup_le ?_ fun a ha => Ideal.mem_sup_right (f.f_I a ha)
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

def qmap {B B' : Obj l R} (f : Hom B B') (m : ℕ) : (B.A ⧸ adI B ^ m) →+* (B'.A ⧸ adI B' ^ m) :=
  Ideal.quotientMap _ f.f (adI_pow_le f m)

theorem qmap_mk {B B' : Obj l R} (f : Hom B B') (m : ℕ) (a : B.A) :
    qmap f m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f.f a) := rfl

structure IsPO {B C B' C' : Obj l R} (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C') : Prop where
  comm : k'.comp h = h'.comp k
  po : ∀ m : ℕ, CategoryTheory.IsPushout (CommRingCat.ofHom (qmap h m)) (CommRingCat.ofHom (qmap k m))
    (CommRingCat.ofHom (qmap k' m)) (CommRingCat.ofHom (qmap h' m))

structure Stable {B C : Obj l R} (h : Hom B C) : Prop where
  flat : ∀ m : ℕ, (qmap h m).Flat
  po : ∀ (B' : Obj l R) (k : Hom B B'), ∃ (C' : Obj l R) (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h'

structure Cover {B C : Obj l R} (h : Hom B C) : Prop where
  stable : Stable h
  ff : ∀ m : ℕ, (qmap h m).FaithfullyFlat

structure IsLoc {B C : Obj l R} (s : B.A) (h : Hom B C) : Prop where
  away : ∀ m : ℕ, letI := (qmap h m).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (adI B ^ m) s) (C.A ⧸ adI C ^ m)
  univ : ∀ (Q : Obj l R) (a : Hom B Q), IsUnit (a.f s) → ∃ c : Hom C Q, c.comp h = a

end Cover

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

structure Eval (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] where
  fin : Module.Finite B.A N
  proj : Module.Projective B.A N

  v : ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q), Hom bk.prism Q → N →ₛₗ[a.f] (Fin d → Q.A)
  bc : ∀ {Q} (a : Hom B Q) (g : Hom bk.prism Q), SemiBC (v a g)
  v_ε : ∀ {Q} (a : Hom B Q) (g g' : Hom bk.prism Q) (x : N), v a g x = (S.ε g g').mulVec (v a g' x)
  v_nat : ∀ {Q Q'} (c : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) (i : Fin d),
    v (c.comp a) (c.comp g) x i = c.f (v a g x i)

def IsPsi {S : Strat bk d} {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (Ψ : N →ₛₗ[B.D.φ] N) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
    BK.hf g bk.E ^ S.a • V.v a g (Ψ x) =
      a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)

def IsCoord {S : Strat bk d} {M : FCrys l ↥(OL K)} (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism))
    {B : Obj l ↥(OL K)} (V : Eval S B (M.M B)) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B),
    M.tr a x = ∑ i, V.v a g x i • M.tr g (e i)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped NNReal

namespace GlobalTheory.BSP.Height

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

def bas : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * ht.Z

def Rel {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀)) : Prop :=
  ∀ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff → IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) Fg →
    toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff * ε) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg

theorem rel_one {B : Obj l ↥(OL K)} (u : B.A) (f : Hom bk.prism B) : ht.Rel u f f 1 := fun Ff Fg hf hg => by
  rw [hf.unique hg, mul_one]

end GlobalTheory.BSP.Height
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def Over4 (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  (∃ k, OverP H (H.g k) w) ∨ OverP H H.pde w ∨ OverP H H.pde' w

structure IsAuxiliaryHeckeCharacter (w0 : HeightOneSpectrum (𝓞 H.E)) (c : R.Psi → ℤ) (χ : Formalism.L2.Host.HChar H.E) : Prop where

  unitary : χ.IsUnitary

  triv : χ.TrivOn H.F

  inf : χ.HasInfQ (embPsi H) fun g => (c g : ℚ)

  unr : ∀ w, ¬ Over4 H w → below w ≠ below w0 → χ.UnrAt w

  two : ∀ w, Over4 H w → ExpAt χ w 2

  one : ∀ w, below w = below w0 → ExpAt χ w 1

def cond0 (w0 : HeightOneSpectrum (𝓞 H.E)) : Ideal (OF H.E) :=
  Ideal.span {((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E)} ^ 2 * (below w0).asIdeal

structure PlacesOk (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)) : Prop where

  referencePlaceOverPrime : OverP H q0 w0

  distinct : [H.g 0, H.g 1, H.pde, H.pde', q0].Nodup

  splits : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr H.E ∧
    ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p

def phi (g : R.Psi) : H.E →+* ℂ := ComplexEmbedding.conjugate (embPsi H g)

end Host

structure LamDat (D : D7) where

  C : CharFrame D

  q0 : ℕ

  w0 : HeightOneSpectrum (𝓞 D.host.E)

  c : Fin D.R.m → D.R.Psi → ℤ

  chi : Fin D.R.m → Formalism.L2.Host.HChar D.host.E

namespace LamDat

variable {D : D7} (Z : LamDat D)

def lam0 (l : ℕ) (j a : Fin D.R.m) : Formalism.L2.Host.HChar D.host.E := Z.C.mu0 j * Z.C.delAt l * (Z.chi a)⁻¹

def kap (j a : Fin D.R.m) (s : ℕ) (g : D.R.Psi) : ℕ := (⌊eExp D j g⌋ + Z.c a g - s).toNat

structure Ok : Prop where

  places : PlacesOk D.host Z.q0 Z.w0

  aux : ∀ a, IsAuxiliaryHeckeCharacter D.host Z.w0 (Z.c a) (Z.chi a)

  big : ∀ j a g, (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + Z.c a g

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsThOf (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF D.host.E)) (χ : Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∃ u : Kbar X i, u ≠ 0 ∧ ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
    ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
      IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
      ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def IsThEmpty (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF D.host.E)) (χ : Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∃ (u : Kbar X i) (T : ℂ), u ≠ 0 ∧ IsToricSum φ s κ 𝔣 χ T ∧
    algebraMap (FractionRing (X.O i)) (Kbar X i) (∑ δ, X.th i ∅ lam δ) = u * ι T

def IsLam (Z : LamDat D) (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (j a : Fin D.R.m) (s : ℕ) : Prop :=
  j.1 + 1 = X.jL i lam ∧ BlochKatoReduction.Gen.SOk X i lam s ∧
    ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (((Z.lam0 (X.l i) j a).val P : ℂˣ) : ℂ) = 1

def IsLamTie (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

def IsLamTie0 (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ (ι : ℂ →+* Kbar X i) (j a : Fin D.R.m) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s ∧
    IsThEmpty X i ι lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

end Record

section Examples

end Examples

end GlobalTheory.LamTie
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.StepTwo

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def idl : Ideal (X.O0 i) := Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i)

def Small2 (M : ℕ) (L : Subgroup (GE N)) (z : GE N) : Prop :=
  Small i s L z ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ idl i

variable (M : ℕ) {R n : ℕ} (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))))

def PiLocalization₂ (A : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host) : Prop :=
  SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
    (∀ a, (∀ v, Over (P (.inl a)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ L) ∧
      ∀ σ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ a, DecV N (P (.inr a)) ≤ L ∧ ∀ (b : Fin R) (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (P (.inl b)) σ = Multiplicative.ofAdd (if a.val = b.val then 1 else 0)

def NF (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.det →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ F.coeff m ∉ idl i

def NFit (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → a = 0 ∨ ∃ b b', ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.adjugate b b' →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ (∀ j : Fin R, n ≤ j.val → m (.inl j) = 0) ∧ IsUnit (F.coeff m)

def Ext (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) : Prop :=
  ∀ q, P' (Sum.map id Fin.castSucc q) = P q

def Start : Prop :=
  ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (φ φ' : Fin n → GE N), n ≤ R → 4 * D.R.r * n + 2 < X.l i ^ M →
    IsTameInertiaElementAtTwistPrime X i z → Small i s L z → PiLocalization₂ i M d A L z P →
    (∀ a, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧ IsCj X (φ a) (φ' a)) → Corank bkP i s φ φ' 1 →
    NFit bkP i s M d P (4 * D.R.r * n + 1)

def Grow : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) (c : ℕ), n < R →
    c + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P' → Ext P P' →
    (NF bkP i s M d P c → NF bkP i s M d P' (c + 2 * D.R.r)) ∧ (NFit bkP i s M d P c → NFit bkP i s M d P' (c + 2 * D.R.r))

def Step : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) H S d A L z (P : Fin R ⊕ Fin n → PlE D.host) (w e : ℕ), n < R →
    IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e →
    2 * (e + 1) * w + 2 + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M →
    AdmFam X i M H S d → L ≤ H → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P → NFit bkP i s M d P (w + 1) →
    ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A L z P' ∧
      NF bkP i s M d P' (2 * (e + 1) * w + 2 + 2 * D.R.r)

end GlobalTheory.StepTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
section
noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

variable {D : D7}

def EigSpan (P : PairedCharacterCondition.Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x : D.nd.X i) (c : D.nd.O i),
    (∀ PI : D.naut.AV i, D.naut.ptV i PI = some x → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
        iotaO D.nd D.naut i c • F) →
    ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = c • u


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def LocBoundP (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ) : Prop :=
  BlochKatoDuality.lenMod (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M))
                   (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤
    (e : ℕ∞) * lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw)

def TypeLocus (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (k : Fin 2) (Xs : Set (D.nd.X i)) : Prop :=
  ∃ s : D.nd.PlG k → (ZMod (D.host.g k))[X],
    (∀ v, Squarefree (s v) ∧ ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ (s v).IsRoot (u : ZMod (D.host.g k))) ∧
    ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∀ v, ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = s v

def TypeLGC (P : PairedCharacterCondition.Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
  ∀ (x : D.nd.X i) (PI : D.naut.AV i), D.naut.ptV i PI = some x → ∀ (v : D.nd.PlG k), ∀ τ ∈ P.kty i PI k v,
    Squarefree ((P.lz k).lab τ) →
    (∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ).IsRoot (u : ZMod (D.host.g k))) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ u : (ZMod (D.host.g k))ˣ, (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (M : Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
        (w = D.naut.plGw k v ∧
          M = Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)) ∨
        (IsConjPl D.host (D.naut.plGw k v) w ∧
          M = (Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)) →
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod

def CentralElt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]),
    ∃ (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
      (L : List (Σ k : Fin 2, D.nd.PlG k)), L.Nodup ∧ (∀ kv, kv ∈ L) ∧
      mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
        (D.what₂.restRowsFiniteGroupCard : ℂ) • (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod

def StepDeg : Prop :=
  ∀ D : D7, tieBr (D := D) → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
    (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1

def StepPotDirect : Prop :=
  ∀ (D : D7) (P : Pend D), TypeLGC P → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieBr (D := D) → tiePH (D := D) →
    tieChi (D := D) → InertEq D → ElementDenominator.adm12 D → PcrisTensorL D.loc → TieInePoly D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs →
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1)

def StepJumpDirect : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (eta s S : ℕ)
    (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s → HostJ i r eta s S sg U →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      sg w = true →
      JumpFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) (eta + D.R.t + 1) (s + S)

def StepJumpDual : Prop :=
  ∀ D : D7, DualJumpL D.loc → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
      (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), eta + D.R.t + 1 < s → HostJ i r eta s S sg U →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      sg w = false → PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      JumpFam i w hw (fun x : ↥Xs => rDuO D.nd i r x) (D.R.nV + 1) (eta + D.R.t + 1) (s + S)

def StepLift : Prop :=
  ∀ (D : D7) (CT : ℕ), admT (D := D) CT → FontaineAtPlacesOverL (D := D) →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ (ι : Type) (Ms : ι → (GE D.nd →* Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))),
      (∀ x, Continuous fun g => Ms x g) → ∀ eta H : ℕ, eta + D.R.t + 1 < H →
      CT * (H * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i →
      PotFam i w hw Ms (D.R.nV + 1) → JumpFam i w hw Ms (D.R.nV + 1) (eta + D.R.t + 1) H →
      LiftFamW i w hw Ms (eMax D CT eta)

def StepSub : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c)

def StepLocDirect : Prop :=
  ∀ D : D7, LocalPushoutProposition (D := D) → admBK (D := D) → FontaineAtPlacesOverL (D := D) → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ n e : ℕ, PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
      LocBoundP i w hw r Xs M (2 * k * e)

def StepLocDual : Prop :=
  ∀ D : D7, LocalPushoutProposition (D := D) → admBK (D := D) → FontaineAtPlacesOverL (D := D) → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ n e : ℕ, PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      LiftFamW i w hw (fun x : ↥Xs => rDuO D.nd i r x) e →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
      LocBoundP i w hw r Xs M (2 * k * e)

def StepHfChar : Prop :=
  ∀ (D : D7) (_ : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admTB (D := D) HW F → InertEq D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → D.nd.l i ≠ 2 →
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
      HfChar i w hw

def StepCentral : Prop := CentralIdemCoeff → ∀ (D : D7) (_ : Pend D), CentralElt D

end GlobalTheory.Pass

end
end

