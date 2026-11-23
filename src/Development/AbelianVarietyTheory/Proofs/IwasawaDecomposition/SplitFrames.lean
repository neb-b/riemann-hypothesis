module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical

namespace GlobalTheory.LocWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idem (D : D7) : Pl D → AE D
  | .inl v => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin D v
  | .inr τ => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf D (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))

theorem idem_mul_self (v : Pl D) : idem D v * idem D v = idem D v := by
  rcases v with v | τ
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin]
    rw [← map_mul]
    congr 1
    refine Prod.ext (mul_zero _) ?_
    change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
    refine DFunLike.ext _ _ fun u => ?_
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F v 1) = evalV D.host.F u (singleV D.host.F v 1)
    rw [map_mul]
    by_cases h : u = v
    · subst h
      have : evalV D.host.F u (singleV D.host.F u 1) = 1 := RestrictedProduct.single_eq_same
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) u 1
      rw [this, mul_one]
    · have : evalV D.host.F u (singleV D.host.F v 1) = 0 := RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 h
      rw [this, mul_zero]
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf]
    rw [← map_mul]
    congr 1
    refine Prod.ext ?_ (mul_zero _)
    exact (Pi.single_mul (α := fun w : InfinitePlace D.host.F => w.Completion) _ 1 1).symm.trans (by rw [mul_one]; rfl)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem cA_idem (v : Pl D) : cA D (idem D v) = idem D v := by
  rcases v with v | τ <;> exact cA_algebraMap _

def cutGL {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) : GL (Fin n) R →* GL (Fin n) R :=
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun g => e • g + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun g h => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
        have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
          Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add] }
  Units.map f

theorem cutGL_val {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (g : GL (Fin n) R) :
    (cutGL he g).val = e • g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := rfl

theorem cutGL_mem {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (c : R →+* R) (hc : c e = e)
    (J : Matrix (Fin n) (Fin n) R) {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ c J) : cutGL he g ∈ Formalism.UG.UJ c J := by
  have hg' : Formalism.UG.cT c g.val * J * g.val = J := hg
  show Formalism.UG.cT c (cutGL he g).val * J * (cutGL he g).val = J
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : Formalism.UG.cT c (cutGL he g).val = e • Formalism.UG.cT c g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    simp only [cutGL_val, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, hc, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  rw [e1, cutGL_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
    Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add, hg']
  rw [← add_smul]; simp

def comp (V : HSp D) (v : Pl D) : GA D V →* GA D V :=
  ((cutGL (idem_mul_self v)).comp (matHom V)).codRestrict (HR (AF D.host.F) D.sp.cm.sig V.gram) fun g =>
    cutGL_mem (idem_mul_self v) (cA D) (cA_idem v) _ g.2

def GAt (V : HSp D) (v : Pl D) : Subgroup (GA D V) := (comp V v).range

def Gk (θ : InfF D) (V : HSp D) (A : CptF V) : Subgroup (GA D V) :=
  GfC V ⊔ Subgroup.closure {k | V.SigOK ∧ IsKinf θ V A k}

def KAt (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Subgroup (GA D V) := (Gk θ V A).map (comp V (.inr τ))

def OneP (V : HSp D) (τ : D.what₂.Tau) : Type :=
  {γ : Multiplicative ℝ →* GA D V // Continuous γ ∧ ∀ t, γ t ∈ GAt V (.inr τ)}

abbrev HAlg (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Type :=
  MonoidAlgebra ℂ (Monoid.Coprod (KAt θ V A τ) (FreeMonoid (OneP V τ)))

def ofK (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : KAt θ V A τ →* HAlg θ V A τ :=
  (MonoidAlgebra.of ℂ _).comp Monoid.Coprod.inl

def Hloc (θ : InfF D) (V : HSp D) (A : CptF V) : Pl D → Type
  | .inl v => GAt V (.inl v)
  | .inr τ => HAlg θ V A τ

instance (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Monoid (Hloc θ V A v)
  | .inl v => inferInstanceAs (Monoid (GAt V (.inl v)))
  | .inr τ => inferInstanceAs (Monoid (HAlg θ V A τ))

def loc (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Gk θ V A →* Hloc θ V A v
  | .inl v => (comp V (.inl v)).rangeRestrict.comp (Gk θ V A).subtype
  | .inr τ => (ofK θ V A τ).comp ((comp V (.inr τ)).subgroupMap (Gk θ V A))

def IsEvalAt (D : D7) (v : FinF D) (w : FinE D) (φ : AE D →+* v.adicCompletion (FF D)) : Prop :=
  (∀ a, φ (algebraMap (AF D.host.F) (AE D) a) = evalV D.host.F v (sndA D.host.F a)) ∧
    ∀ x : 𝓞 D.host.E, Valued.v (φ (incA D (x : D.host.E))) < 1 ↔ x ∈ w.asIdeal

structure SplitFrames (D : D7) where
  ev : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (AE D →+* v.adicCompletion (FF D))
  ev_spec : ∀ v w hv hw, IsEvalAt D v w (ev v w hv hw)
  ev_conj : ∀ v w w' hv hw hw', w' ≠ w → ∀ x, ev v w' hv hw' x = ev v w hv hw (cA D x)
  sc : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (v.adicCompletion (FF D))ˣ
  sc_spec : ∀ v w hv hw x, IntV v 0 (((sc v w hv hw)⁻¹ : (v.adicCompletion (FF D))ˣ) * x) ↔
    x ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {y | ∃ a ∈ D.host.AA, y = ev v w hv hw (incA D a)}
  fr : ∀ (V : HSp D) (v : FinF D) (w : FinE D), Split D v → Over D w v → GL (Fin V.rank) (v.adicCompletion (FF D))
  fr_spec : ∀ V v w hv hw y, (∀ i, IntV v 0 (((fr V v w hv hw)⁻¹).val.mulVec y i)) ↔
    y ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {z | ∃ x ∈ L0c D V, z = fun i => ev v w hv hw (incA D (x i))}
  fr_dual : ∀ V v w w' hv hw hw', w' ≠ w →
    (fr V v w' hv hw').valᵀ * V.gram.map (fun a => ev v w hv hw (incA D a)) * (fr V v w hv hw).val = 1

def SplitFrames.gl (Fr : SplitFrames D) (V : HSp D) (v : FinF D) (w : FinE D) (hw : Over D w v) :
    GAt V (.inl v) →* GL (Fin V.rank) (v.adicCompletion (FF D)) :=
  if hv : Split D v then
    (MulAut.conj (Fr.fr V v w hv hw)⁻¹).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (Fr.ev v w hv hw)).comp ((matHom V).comp (GAt V (.inl v)).subtype))
  else 1

variable {X : ThetaX D} {T : ThetaTied D X}

def Splitting (T : ThetaTied D X) (V W : HSp D) (χ χ' : X.Chr) : Prop :=
  ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank

structure PairData {Wl : WeilTied D X T} (K : KfinTied Wl) (θ : InfF D) (Fr : SplitFrames D) (V W : HSp D)
    (om : X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Type 1 where
  S : Pl D → Type
  [sA : ∀ v, AddCommGroup (S v)]
  [sM : ∀ v, Module ℂ (S v)]
  omL : X.Chr → X.Chr → ∀ v, Representation ℂ (Hloc θ V (K.cpt V) v × Hloc θ W (K.cpt W) v) (S v)
  vac : ∀ v, S v
  pure : (∀ v, S v) → X.Sch V W
  pure_span : Submodule.span ℂ {Φ | ∃ φ, Restr vac φ ∧ Φ = pure φ} = X.kfin V W
  pure_om : ∀ χ χ', Splitting T V W χ χ' → ∀ (g : Gk θ V (K.cpt V)) (h : Gk θ W (K.cpt W)) φ, Restr vac φ →
    om χ χ' ((g : GA D V), (h : GA D W)) (pure φ) = pure fun v => omL χ χ' v (loc θ V _ v g, loc θ W _ v h) (φ v)
  pure_mlin : ∀ φ v (c : ℂ) (x y : S v), Restr vac φ →
    pure (Function.update φ v (c • x + y)) = c • pure (Function.update φ v x) + pure (Function.update φ v y)
  linM : ∀ (v : FinF D) (w : FinE D), Over D w v →
    S (.inl v) →ₗ[ℂ] (Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ)
  linM_inj : ∀ v w (hw : Over D w v), Split D v → Function.Injective (linM v w hw)
  linM_eq : ∀ χ χ' v w (hw : Over D w v), Splitting T V W χ χ' → Split D v →
    ∀ g k : _, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, linM v w hw (omL χ χ' (.inl v) (g, k) φ) = c • fun (Xm : Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D))) =>
      linM v w hw φ (Units.val (Fr.gl V v w hw g)⁻¹ * Xm * (Units.val (Fr.gl W v w hw k)⁻¹).transpose)

attribute [instance] PairData.sA PairData.sM

end GlobalTheory.LocWeil

end
