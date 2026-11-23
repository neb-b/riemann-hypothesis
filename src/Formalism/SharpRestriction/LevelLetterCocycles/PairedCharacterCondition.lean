module

public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module Polynomial

def mapCoef {A B M : Type} [Semiring A] [Semiring B] (f : A →+* B) (z : MonoidAlgebra A M) :
    MonoidAlgebra B M :=
  MonoidAlgebra.ofCoeff (z.coeff.mapRange f (map_zero f))

structure LzData (g : ℕ) where
  Irr : ℕ → Type
  [finIrr : ∀ a, Fintype (Irr a)]
  idem : ∀ {a : ℕ}, Irr a → MonoidAlgebra ℂ (GL (Fin a) (ZMod g))
  idem_idem : ∀ {a : ℕ} (τ : Irr a), idem τ * idem τ = idem τ
  idem_central : ∀ {a : ℕ} (τ : Irr a) z, idem τ * z = z * idem τ
  idem_ne : ∀ {a : ℕ} (τ : Irr a), idem τ ≠ 0
  idem_orth : ∀ {a : ℕ} (τ σ : Irr a), τ ≠ σ → idem τ * idem σ = 0
  idem_sum : ∀ a : ℕ, ∑ τ : Irr a, idem τ = 1
  idem_prim : ∀ {a : ℕ} (τ : Irr a) (e : MonoidAlgebra ℂ (GL (Fin a) (ZMod g))), e * e = e →
    (∀ z, e * z = z * e) → e * idem τ = e → e = 0 ∨ e = idem τ
  lab : ∀ {a : ℕ}, Irr a → Polynomial (ZMod g)
  lab_spec : ∀ {a : ℕ} (τ : Irr a), (lab τ).Monic ∧ (lab τ).natDegree = a ∧ (lab τ).coeff 0 ≠ 0
  Rep : ℕ → Type
  ofIrr : ∀ {a : ℕ}, Irr a → Rep a
  cons : ∀ {a : ℕ}, Rep a → Irr a → Prop
  cons_ofIrr : ∀ {a : ℕ} (τ σ : Irr a), cons (ofIrr τ) σ ↔ σ = τ
  hc : ∀ {a b : ℕ}, Irr a → Irr b → Rep (a + b)

attribute [instance] LzData.finIrr

def chiJ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) : (ZMod (D.host.g k))ˣ :=
  D.nd.chiT k v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩


open Classical in
structure Pend (D : D7) where
  lz : ∀ k : Fin 2, LzData (D.host.g k)
  eSer_eq : ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]),
    D.ntypes.eSer k f = ∑ τ : (lz k).Irr D.R.r, if (lz k).lab τ = f then (lz k).idem τ else 0

  eSer_LL : ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]) (h : GL (Fin D.R.r) (ZMod (D.host.g k))),
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.ntypes.eSer k f).coeff h
  zetaPrimitiveRoot : ∀ i : D.nd.Loc, ∃ ζ : D.nd.O i, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard
  om : ∀ k : Fin 2, PlE D.host → Fb (D.host.g k) (D.host.g_prime k) → GE D.nd → ℂ
  om_one : ∀ k w x, x ≠ 0 → om k w x 1 = 1
  om_mul : ∀ k w x, x ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ∀ σ' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x (σ * σ') = om k w x σ * om k w x σ'
  tameInertiaChar_mul_root : ∀ k w x y, x ≠ 0 → y ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    om k w (x * y) σ = om k w x σ * om k w y σ
  om_wild : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), om k w x σ = 1
  om_open : ∀ k w x, x ≠ 0 → ∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
    ∀ σ ∈ U, σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → om k w x σ = 1
  om_inj : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x y, x ≠ 0 → y ≠ 0 → x ≠ y →
    ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x σ ≠ om k w y σ
  om_tg : ∀ k (v : D.nd.PlG k) x, x ≠ 0 →
    om k (D.naut.plGw k v) x (D.ntypes.tg k v) = D.ntypes.teichC k x

  inertiaCharpoly_eigenvalues : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol L σ =
      ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (om k w x σ)).prod

  inertiaCharpoly_character : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ (L χ : D.naut.LP w)
    (u : (ZMod (D.host.g k))ˣ), (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    D.naut.lpDim χ = 1 → D.naut.items₂ k w χ = X - C (u : ZMod (D.host.g k)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.lpChar L χ)) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map
        (· * algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))
  zO : ∀ i : D.nd.Loc,
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (D.nd.Mt i)
  zO_comm : ∀ i z (f : D.nd.T i), zO i z * D.nd.act i f = D.nd.act i f * zO i z

  zL_stable : ∀ (i : D.nd.Loc) (z : MonoidAlgebra D.what₂.LL (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x : D.what₂.MtL (D.nd.mu i) (D.nd.j i), ∃ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef D.what₂.embLL z) (D.what₂.jMt _ _ x)

  zO_act : ∀ i (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (D.what₂.jMt _ _ x) →
    D.nd.prMt i y = (zO i z).baseChange (KK D.nd i) (D.nd.prMt i x)

  prMt_type : ∀ i (PI : D.naut.AV i) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ x ∈ D.naut.typeV i PI →
    (∀ p, D.naut.ptV i PI = some p → D.nd.prMt i x ∈ heckeEig (D.nd.T i) (D.nd.act i) p) ∧
    (D.naut.ptV i PI = none → D.nd.prMt i x = 0)

  Par_surj : ∀ i x Sig, HasParamX D.nd D.naut i x Sig →
    ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w
  kty : ∀ i : D.nd.Loc, D.naut.AV i → ∀ k : Fin 2, D.nd.PlG k → Set ((lz k).Irr D.R.r)

  kty_spec : ∀ i (PI : D.naut.AV i) k (v : D.nd.PlG k) (τ : (lz k).Irr D.R.r),
    τ ∈ kty i PI k v ↔ ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v ((lz k).idem τ)) F ≠ 0

variable {D : D7}

def SignOK (i : D.nd.Loc) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) : Prop :=
  ∀ w w', w ∈ placesOver D.host.E (D.nd.l i) → IsConjPl D.host w w' → w ≠ w' → sg w' = !sg w

def cen : ℚ := ((D.R.t : ℚ) - 1) / 2

def cloud (up : Bool) (H : ℕ) (a : ℤ) : Prop :=
  0 < (if up then (a : ℚ) - cen (D := D) else cen (D := D) - a) ∧
    (if up then (a : ℚ) - cen (D := D) else cen (D := D) - a) ≤ (H : ℚ) - cen (D := D)

def vZeta (i : D.nd.Loc) (q : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})

def eT (C : ℝ) (eta : ℕ) : ℝ := C * (D.R.nV : ℝ) ^ 2 * ((D.R.nV : ℝ) + eta + D.R.t)

def chiGL (i : D.nd.Loc) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Units.map (Matrix.scalar (Fin 1) : D.nd.O i →+* Matrix (Fin 1) (Fin 1) (D.nd.O i)).toMonoidHom).comp
    (D.nd.chi i 1)

def HostJ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (U w).card ≤ D.R.nV ∧
    (∀ (x : D.nd.X i) τ (a : ℤ),
      IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ a →
        a ∈ U w) ∧
    ∀ a ∈ U w, ((0 ≤ a ∧ a < D.R.t) ∨ |(a : ℚ) - cen (D := D)| ≤ (eta : ℚ) + 1 ∨
        cloud (D := D) (sg w) (s + S) a) ∧
      a ≠ -1 ∧ a ≠ D.R.t

def rhs (C : ℝ) (eta : ℕ) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) : ℝ :=
  4 * D.R.f * D.R.nV * eT (D := D) C eta + 2 * D.R.f * (D.R.r : ℝ) ^ 2 +
    (Br.sPi D.loc D.nbr i ρ π : ℝ) +
    (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℝ)) +
    (padicValNat (D.nd.l i) (hE D.host) : ℝ) + 4 * D.R.nV * (D.nd.vdel i : ℝ) +
    D.R.t * (∑ q ∈ D.nd.Q i, (vZeta i q : ℝ))

def admT (CT : ℕ) : Prop := Formalism.MainNotions.ElementDenominator.Conclusion2 D CT

def LocalPushoutProposition : Prop := Formalism.MainNotions.BlochKatoDuality.Conclusion1 D ∧ Formalism.MainNotions.BlochKatoDuality.Conclusion2 D

def ResidualAbsIrreducible : Prop :=
  2 ≤ D.R.r ∧ ∀ i, HG D.nd D.naut i → ∀ rb, IsRhoBar D.nd i rb →
    Submodule.span (IsLocalRing.ResidueField (D.nd.O i))
      (Set.range fun g => ((rb g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r)
        (IsLocalRing.ResidueField (D.nd.O i)))) = ⊤

def CoboundaryLemmaNoColumn (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i) : Prop :=
  (∀ (φ : (S.X' → MatN D.nd i) →ₗ[D.nd.O i] KOr D.nd i) (w : KOr D.nd i),
    (∀ a, InR' D.nd r S a → ∀ y, InY D.nd r S y → φ (a * y) = matQ D.nd (S.ψρ a) (φ y)) →
    (∀ γ : GE D.nd, φ (yg D.nd r S γ) =
      matQ D.nd ((((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π γ - 1) w) →
    del51 D.nd S S.π' ^ 2 • w = 0) ∧
  ∀ c : Fin D.R.t, (c : ℕ) ≠ 0 →
    ∀ (φ : (S.X' → MatN D.nd i) →ₗ[D.nd.O i] KmodO (D.nd.O i)) (w : KmodO (D.nd.O i)),
      (∀ a, InR' D.nd r S a → ∀ y, InY D.nd r S y → φ (a * y) = S.ψχ c a • φ y) →
      (∀ γ : GE D.nd, φ (yg D.nd r S γ) =
        (((chiU D.nd i ((c : ℕ) + 1) γ * (chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) - 1) • w) →
      del51 D.nd S S.π' ^ 2 • w = 0

def WildInertiaElement (i : D.nd.Loc) (S : IdempotentChoiceData D.nd i) : Prop :=
  ∀ w ∈ placesOver D.host.E (D.nd.l i), S.g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
    S.g0 ∈ wildSet D.nd (D.nd.plOm.1 w)

def WildIdempotentChoice (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  π ∈ D.nd.Z i → ∃ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S ∧ WildInertiaElement i S

def TypePrimeChoiceLemmas : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → HG D.nd D.naut i →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    Formalism.MainNotions.LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧
    ∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
      WildIdempotentChoice i r ρ π ∧
      ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → WildInertiaElement i S →
        VanishingLemma D.nd π S ∧ QuotientHomNonvanishingBound D.nd r π S ∧ CoboundaryLemmaNoColumn i r ρ π S

def admG5 : Prop := Formalism.MainNotions.SumRepresentations.ConclusionG5 D

def admG6 : Prop := Formalism.MainNotions.SumRepresentations.ConclusionG6 D

def admTB (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.Conclusion4 D HW F

def admBK : Prop := Formalism.MainNotions.LocalSituation.Conclusion5 D

def admBC : Prop := Formalism.MainNotions.SumRepresentations.adm1 D

def FontaineAtPlacesOverL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def tieBr : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.DegW D.nbr i w hw

def tiePH : Prop := LocTie D.nd D.naut D.loc D.nbr

def tiePar : Prop := MtParTie D.nd D.naut D.ntypes

def tieIne : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)),
    Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) →
    ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      (D.nbr i w hw).e σ ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Iner ∧
      ∀ a : D.nd.O i,
        ((D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) (σ : GE D.nd)).IsRoot
            (iotaO D.nd D.naut i a) ↔
          ∃ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))),
            d ≠ 0 ∧
            actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w)))
              ((D.nbr i w hw).e σ) d =
                @SMul.smul _ _ TensorProduct.leftHasSMul ((D.nbr i w hw).toLL a) d)

def tieChi : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ v : D.nd.PlG k,
    ∃ u : (ZMod (D.host.g k))ˣ, (u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹) ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
        (w = D.naut.plGw k v → Br.IsdRW D.loc D.nbr i w hw (chiGL i) ∧
          D.naut.items₂ k w (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) =
            X - C (u : ZMod (D.host.g k))) ∧
        (IsConjPl D.host (D.naut.plGw k v) w → Br.IsdRW D.loc D.nbr i w hw (chiGL i) ∧
          D.naut.items₂ k w (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) =
            X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))

def Comparison₂ : Prop :=
  Formalism.MainNotions.SumRepresentations.tie0 D ∧ tieBr (D := D) ∧ tiePH (D := D) ∧ tiePar (D := D) ∧ tieIne (D := D) ∧
    tieChi (D := D)

section Pending

variable (P : Pend D)

def admDZ : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i) (τ : (P.lz k).Irr D.R.r),
    τ ∈ P.kty i PI k v →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Squarefree ((P.lz k).lab τ) →
    (∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ).IsRoot (u : ZMod (D.host.g k))) →
    ∃ u : (ZMod (D.host.g k))ˣ, (u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹) ∧
      D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) ∧
      D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
        (P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t ∧
      ∀ w', IsConjPl D.host (D.naut.plGw k v) w' →
        D.naut.mono0 (D.naut.locV i PI w') ∧
        (D.naut.items₂ k w' (D.naut.locV i PI w')).natDegree = D.R.nV ∧
        Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
          (Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)

end Pending

end Formalism.MainNotions.PairedCharacterCondition

end
