module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.Bundle0001
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CongruenceMaxGalois
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (φ : GalE D),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) φ →
    ((r φ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FactorSeriesSupport
section
noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

open Formalism.BasicNotions

def IsLabel (N : ℕ) {g : ℕ} (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0

def rootExp (N g : ℕ) : ℕ := (Finset.Icc 1 N).lcm fun d => g ^ d - 1

def IsPowLabel {g : ℕ} [Fact g.Prime] (a : ℤ) (f f' : (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map fun x => x ^ a


variable (D : D7)

theorem IsPowLabel.unique {g : ℕ} [Fact g.Prime] {a : ℤ} {f f₁ f₂ : (ZMod g)[X]}
    (h₁ : IsPowLabel a f f₁) (h₂ : IsPowLabel a f f₂) (m₁ : f₁.Monic) (m₂ : f₂.Monic) : f₁ = f₂ := by
  have h : Formalism.CyclotomicNorms.rootsBar f₁ = Formalism.CyclotomicNorms.rootsBar f₂ := h₁.trans h₂.symm
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  have e : ∀ p : (ZMod g)[X], p.Monic → p.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) =
      ((Formalism.CyclotomicNorms.rootsBar p).map fun x => X - C x).prod := fun p hp =>
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      (IsAlgClosed.card_roots_eq_natDegree)).symm
  rw [e f₁ m₁, e f₂ m₂, h]

theorem rootExp_ne_zero (N g : ℕ) (hg : 2 ≤ g) : rootExp N g ≠ 0 := by
  unfold rootExp
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨d, hd, h⟩
  have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.1 hd).1; omega
  have : 1 < g ^ d := Nat.one_lt_pow hd1 (by omega)
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]


open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.finKs (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.Ks K s) := by
  classical
  have hl : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hK : FiniteDimensional ℚ_[l] ↥(K.1) := K.2
  have hK0 : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : (K.1 : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) ⊓
        _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l ≤ K.1)).toLinearMap (RingHom.injective _)
  have hfin : {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}.Finite := by
    refine (Polynomial.nthRoots (l ^ s) (1 : _root_.Formalism.BasicNotions.Loc.Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hl] using hx
  have : Finite {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1} := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hl (by rw [show x ^ l ^ s = 1 from hx]; exact isIntegral_one)
  unfold _root_.Formalism.BasicNotions.Loc.Ks
  infer_instance

def levelField (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finKs K s⟩

section Generic

variable {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]

def charLat (hO : Function.Injective (algebraMap O LL)) (ψ : G →* LLˣ)
    (hψ : ∀ g, ∃ a : O, algebraMap O LL a = ((ψ g : LLˣ) : LL)) :
    Lattice (O := O) (charRep ψ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hψ g
    refine ⟨b * a, ?_⟩
    change algebraMap O LL (b * a) = ((ψ g : LLˣ) : LL) * algebraMap O LL a
    rw [map_mul, hb]
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hO)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

variable [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) [Algebra Qp LL] [TopologicalSpace LL]
    [ContinuousAdd LL] [ContinuousConstSMul LL LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))

end Generic


open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem (P : _root_.Formalism.BasicNotions.LocPrime l) (K LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (g : ↥(_root_.Formalism.BasicNotions.Loc.GK K)) :
    ((_root_.Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : _root_.Formalism.BasicNotions.Loc.GQ l) 0 1 (by simp)
  have hnorm : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have ha' : ‖(a : ℚ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] a
    calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
        = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) + a‖ := by ring_nf
      _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le (by simpa using ha) ha'
  unfold _root_.Formalism.MainNotions.N.cycLL
  show algebraMap ℚ_[l] LL (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∈ _
  rw [P.PD_χ K g]
  have hmap : algebraMap ℚ_[l] LL ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) =
      algebraMap ℤ_[l] LL ⟨_, hnorm⟩ := rfl
  rw [hmap]
  unfold _root_.Formalism.BasicNotions.Loc.OL
  exact (integralClosure ℤ_[l] LL).algebraMap_mem _

def negTwist (P : LocPrime l) (K LL : FinExt l) (e : ℕ) : ↥(GK K) →* (↥LL.1)ˣ :=
  ((cycLL (P.PD K) ↥LL.1)⁻¹) ^ e

theorem negTwist_mem (P : LocPrime l) (K LL : FinExt l) (e : ℕ) (g : ↥(GK K)) :
    ((negTwist P K LL e g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  have : negTwist P K LL e g = (cycLL (P.PD K) ↥LL.1 g⁻¹) ^ e := by
    simp [negTwist]
  rw [this, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ (cyc_mem P K LL _) e

def tateLat (P : LocPrime l) (K LL : FinExt l) (e : ℕ) :
    Lattice (O := ↥(OL LL)) (charRep (negTwist P K LL e)) :=
  charLat Subtype.val_injective _ fun g => ⟨⟨_, negTwist_mem P K LL e g⟩, rfl⟩

def wittFixedFrobeniusPow (K : FinExt l) : Set (Ainf l) :=
  {a | (WittVector.frobenius : Ainf l →+* Ainf l)^[Module.finrank ℚ_[l] ↥(K0 K)] a = a}

variable {P : LocPrime l} (AI : LocAinf l P)

def piS (s : ℕ) : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1

def ringAs (K : FinExt l) (s : ℕ) : Subring (Ainf l) :=
  ⨅ m : ℕ, ((Subring.closure (insert (piS AI s) (wittFixedFrobeniusPow K))).map
      (Ideal.Quotient.mk (Ideal.span {piS AI s ^ m}))).comap
    (Ideal.Quotient.mk (Ideal.span {piS AI s ^ m}))

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

def resKs {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (Y : Lat K LL) :
    Representation ↥LL.1 ↥(GK (levelField K s)) Y.V :=
  Y.ρ.comp (Subgroup.inclusion (GK_le (K := K) (K' := levelField K s) h.2.2.1))

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

variable (D : D7)

def cE : ℕ := D.host.QS * D.host.q * D.host.d

def cEIdeal : Ideal (𝓞 D.host.K) := Ideal.span {((cE D : ℕ) : 𝓞 D.host.K)}

def Admissible (g : ℕ) : Prop :=
  g.Prime ∧ ∃ π : 𝓞 D.host.K, π - 1 ∈ cEIdeal D ∧ Algebra.norm ℤ π = (g : ℤ)

def AdmissiblePrimesWithConstant (c₁ : ℝ) : Prop :=
  ∀ (N : ℕ) (X : ℝ), c₁ ≤ (cE D : ℝ) → c₁ ≤ (D.host.d : ℝ) → 21 ≤ N → 0 < X →
    (N : ℝ) ^ 4 * (cE D : ℝ) ^ 500 ≤ (X / (cE D : ℝ) ^ 20) ^ ((1 : ℝ) / 4) →
    Real.log X ≤ (cE D : ℝ) →
    ∃ Y : ℝ, X / (cE D : ℝ) ^ 20 ≤ Y ∧ Y ≤ X / 2 ∧
      (∃ g₁ g₂ : ℕ, g₁ ≠ g₂ ∧ Admissible D g₁ ∧ Admissible D g₂ ∧
        Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
        Formalism.CyclotomicNorms.BB N g₁ ∩ Formalism.CyclotomicNorms.BB N g₂ = ∅) ∧
      Y / (cE D : ℝ) ^ 20 ≤ (({g : ℕ | Admissible D g ∧ Y ≤ g ∧ (g : ℝ) ≤ 2 * Y}).ncard : ℝ)

abbrev GalE : Type := G D.host.E D.nd.Om

def OnW (σ : D.what₂.FT) : Prop := ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥

def OccursOnLevelZero (σ : D.what₂.FT) : Prop := (∃ a, D.what₂.ft a = σ) ∨ ∃ a, D.what₂.ft0 a = σ

def IsBaseChange (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧
  (∀ τ, (isoInf D.nd D.naut Sig τ).Nodup ∧ ∀ z ∈ isoInf D.nd D.naut Sig τ, ∃ n : ℤ, z = (n : ℂ)) ∧
  (∀ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    isoLoc D.nd D.naut Sig w = D.naut.locW i σ w) ∧
  (∀ k v, D.nd.lab k σ v =
    D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) ∧
  D.ntypes.bc σ = Multiset.ofList (Sig.map fun p => (p.a, p.d))

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.mono0 (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) ↔
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' {a} ha := by show ‖-a‖ ≤ 1; rwa [norm_neg]

def IsReduction {a l : ℕ} [Fact l.Prime] (red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l)
    (r : GalE D →* GL (Fin a) (Qbar l)) (ρ : GalE D →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsOpen (ρ.ker : Set (GalE D)) ∧ IsSSRep ρ ∧ ∀ g, ∃ p : (Zbar l)[X],
    p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
    p.map red = ((ρ g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def ResidualTie (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  ∀ w : D.what₂.places.Pl,
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ∃ (ι : Qbar (D.what₂.places.resChar w) ≃+* ℂ)
      (red : Zbar (D.what₂.places.resChar w) →+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w))
      (r : GalE D →* GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))),
      (∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1) ∧
      IsGaloisRepOf D π _ ι r ∧ IsReduction D red r (D.ntypes.rbar σ w) ∧
      ∀ k, D.what₂.places.resChar w ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 →
        ∀ z : Zbar (D.what₂.places.resChar w), (z : Qbar _) = ι.symm (D.ntypes.teichC k x) →
          red z = D.ntypes.iota k v w x

def toFb (k : Fin 2) (c : (ZMod (D.host.g k))ˣ) : Fb (D.host.g k) (D.host.g_prime k) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k))

def LabelLaws : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).Monic ∧ (D.naut.items₂ k _ L).natDegree ≤ D.naut.lpDim L ∧
    (∀ s : ℝ, D.naut.items₂ k _ (D.naut.lpTw L s) = D.naut.items₂ k _ L) ∧
    (∀ χ : D.naut.LP (D.naut.plGw k v), D.naut.lpDim χ = 1 → D.naut.unr χ →
      D.naut.items₂ k _ (D.naut.lpChar L χ) = D.naut.items₂ k _ L) ∧
    ((D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) →
        D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L)

def BaseChangeRows : Prop :=
  ∀ σ, OnW D σ → ∃ Sig, IsBaseChange D σ Sig ∧ ∀ π, Sig = [⟨D.R.r, π, 1⟩] → ResidualTie D σ π

def TransferRows : Prop :=
  ∀ σ, OccursOnLevelZero D σ → (∀ v, Squarefree (D.nd.lab 0 σ v)) →
    (∀ a, 0 < a → a < D.R.r → ∃ v, ¬ ∃ q, q ∣ D.nd.lab 0 σ v ∧ q.natDegree = a) →
    D.what₂.isot D.R.m σ ≠ ⊥

def GaloisReps : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, IsGaloisRepOf D π l ι r

end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TateLocalDualityTopDegree
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

def intSub (LL : FinExt l) : Submodule ↥(OL LL) ↥LL.1 :=
  LinearMap.range (Algebra.linearMap ↥(OL LL) ↥LL.1)

theorem norm_chi_le_one (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    ‖(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : GQ l) 0 1 (by simp)
  rw [P.PD_χ]
  have h1 : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
  have h2 : ‖(a : ℚ_[l])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := l) (a : ℤ)
  have h3 := IsUltrametricDist.norm_add_le_max
    (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) (a : ℚ_[l])
  rw [sub_add_cancel] at h3
  exact h3.trans (max_le h1 h2)

def chiInt (P : LocPrime l) (K : FinExt l) : ↥(GK K) →* ℤ_[l] where
  toFun g := ⟨(((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]), norm_chi_le_one P K g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change (((P.PD K).χ (g * h) : ℚ_[l]ˣ) : ℚ_[l]) =
      (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) * (((P.PD K).χ h : ℚ_[l]ˣ) : ℚ_[l])
    rw [map_mul, Units.val_mul])

end GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeakIdealLattices
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {l : ℕ} [Fact l.Prime]

def cZero (l : ℕ) (m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt l u)

theorem finiteDimensional_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := by
    refine Set.Finite.to_subtype ((Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset ?_)
    intro x hx
    simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

def KsFin (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finiteDimensional_Ks K s⟩

section Ring

variable {P : LocPrime l} (AI : LocAinf l P)

end Ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R : Type} [CommRing R] [Algebra O R]

end Generic

section Hyp

variable {K LL : FinExt l}

variable {P : LocPrime l} (AI : LocAinf l P)


end Hyp

end GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants
end
end

