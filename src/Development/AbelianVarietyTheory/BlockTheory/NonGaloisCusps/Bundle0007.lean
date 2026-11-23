module

public import Mathlib
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

def nlen (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  ((Module.length O M : ℕ∞) : ℝ≥0∞) / ((Module.length O (O ⧸ Ideal.span {(l : O)}) : ℕ∞) : ℝ≥0∞)

def vO (O : Type) [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ := nlen O l (O ⧸ Ideal.span {x})

section Exc

variable {D : D7} (L : SizeData₂ D)

def sgPlus : ℤ := ⌊2 * L.sc.b / LevelStarExponents.lStar L⌋

def baseSizes : Set ℝ :=
  {W | W = L.sc.b ∨ W = L.sc.w'' D.R.n ∨
    ∃ t : D.host.TT, W = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)}

def window (W : ℝ) : Set ℤ :=
  {n | W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)}

def Exc : Set ℕ :=
  {l | l.Prime ∧ LevelStarExponents.lStar L < (l : ℝ) ∧ ∃ W ∈ baseSizes L, ∃ n ∈ window L W, (l : ℤ) ∣ n}

end Exc

section HidaSetting

variable (D : D7) (i : D.nd.Loc)

def liftIx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def param (ρ : D.what₂.Tau) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (D.R.k - 1))).val.map (fun a => (D.hc ρ).v a) +
  (Finset.univ : Finset (Fin D.R.m)).val.map (fun a => -(D.hc ρ).b a) +
  (Finset.Icc 1 D.R.t).val.map
    (fun c : ℕ => -(D.hc ρ).e (liftIx D i) + ((D.R.t : ℚ) + 1) / 2 - (c : ℚ))

def embSide (ρ : D.what₂.Tau) (s : Bool) : D.host.E →+* ℂ :=
  if s then D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)
  else ComplexEmbedding.conjugate (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG))

def WeightTie : Prop :=
  ∃ s : Bool, ∀ ρ : D.what₂.Tau, ∃ c : ℚ,
    D.naut.infWt i (embSide D ρ s) = (param D i ρ).map (fun p => ((p + c : ℚ) : ℂ)) ∧
    D.naut.infWt i (embSide D ρ (!s)) = (param D i ρ).map (fun p => ((-(p + c) : ℚ) : ℂ))

def IsRankRPart (rπ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ (g : GE D.nd) (u : Fin D.R.nV → KK D.nd i),
      e ((((rπ g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
          (toK D.nd i)).mulVec u) =
        ((((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
            (toK D.nd i)).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

def vCC (π : D.nd.X i) : ℝ≥0∞ :=
  ⨅ f ∈ D.nd.cc i, vO (D.nd.O i) (D.nd.l i) (((f : D.nd.T i) : D.nd.X i → D.nd.O i) π)

def sPi (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : ℝ≥0∞ :=
  nlen (D.nd.O i) (D.nd.l i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℝ≥0∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) : ℕ∞) : ℝ≥0∞)

def vClass : ℝ≥0∞ := (padicValNat (D.nd.l i) (NumberField.classNumber D.host.E) : ℝ≥0∞)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def epsQ : ℝ≥0∞ :=
  (D.R.t : ℝ≥0∞) * ∑ P ∈ D.nd.Q i, vO (D.nd.O i) (D.nd.l i) (zetaP D i P - 1)

end HidaSetting

def CongBound_at (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc,
    LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → D.nd.l i ∉ Exc L →
    WeightTie D i → HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), IsRankRPart D i (r π) ρ →
      vCC D i π ≤ sPi D i π ρ + shaSum D i + vClass D i + epsQ D i

theorem zetaP_eq (D : D7) (i : D.nd.Loc) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P ∈ D.nd.Q i) :
    zetaP D i P = D.nd.zeta i P := by
  have hl : P ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i P (Or.inr hP)
  have hS : P ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hP
  rw [D.nd.S_def] at hS
  have h1 : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) (D.nd.gam0 i P) = 1 := by
    refine D.ntw.twistCharacterFamily_unramified _ _ _ P ?_ ?_ ?_ (D.nd.plOm.1 P) (D.nd.plOm.2 P) _ (D.nd.locNd_chebotarevPlace_mem i P)
    · rw [D.ntw.twOf_l]; exact hl
    · intro k hk
      apply hS
      refine ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    · intro h
      apply hS
      have h' : P ∈ (D.ntw.pD (D.ntw.twOf i) : Set _) := h
      rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
      exact ⟨Or.inr (Or.inr h'), hl⟩
  unfold zetaP NData.zeta
  rw [D.ntw.chi_tw]
  simp [h1]

theorem lStar_pos {D : D7} (L : SizeData₂ D) : 0 < LevelStarExponents.lStar L := by
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
  have hn : (0 : ℝ) < D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    exact_mod_cast (by unfold Ranks.n; omega : 0 < D.R.n)
  have hx : 0 < L.sc.x := by have := L.sc.one_lt_alt; linarith
  have hL : 0 < L.sc.L := by unfold Scale.L; positivity
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hS := L.Sc_pos
  unfold LevelStarExponents.lStar
  positivity

theorem vO_l (D : D7) (i : D.nd.Loc) : vO (D.nd.O i) (D.nd.l i) (D.nd.l i : D.nd.O i) = 1 := by
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h0 : (D.nd.l i : D.nd.O i) ≠ 0 := by
    intro h
    have h1 : (D.nd.embK i) ((D.nd.l i : ℕ) : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), h, map_zero]
    have h2 : ((D.nd.l i : ℕ) : D.what₂.LL) = 0 := (map_eq_zero _).1 h1
    exact hp.ne_zero (by exact_mod_cast h2)
  have hu : ¬ IsUnit (D.nd.l i : D.nd.O i) := by
    intro hu
    have hinj : Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro z hz
      by_contra hz0
      rw [PadicInt.unitCoeff_spec hz0, map_mul, map_pow, map_natCast] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact ((PadicInt.unitCoeff hz0).isUnit.map _).ne_zero h
      · exact h0 (pow_eq_zero_iff'.1 h).1
    haveI : FaithfulSMul ℤ_[D.nd.l i] (D.nd.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have : IsUnit ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) :=
      IsLocalHom.map_nonunit (f := algebraMap ℤ_[D.nd.l i] (D.nd.O i)) _ (by rw [map_natCast]; exact hu)
    exact PadicInt.irreducible_p.not_isUnit this
  unfold vO nlen
  apply ENNReal.div_self
  · haveI : Nontrivial (D.nd.O i ⧸ Ideal.span {(D.nd.l i : D.nd.O i)}) :=
      Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
    simpa using (Module.length_pos (R := D.nd.O i)).ne'
  · have hf : IsFiniteLength (D.nd.O i) (D.nd.O i ⧸ Ideal.span {(D.nd.l i : D.nd.O i)}) :=
      isFiniteLength_quotient_span_singleton (D.nd.O i) (mem_nonZeroDivisors_of_ne_zero h0)
    simpa using Module.length_ne_top_iff.2 hf

end GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

section At

variable (D : D7) (i : D.nd.Loc)

def chiRatio (c : ℕ) : GE D.nd →* (D.nd.O i)ˣ := chiU D.nd i c * (chiU D.nd i 1)⁻¹

def IsConstituent {n : ℕ} (χ : GE D.nd →* (D.nd.O i)ˣ)
    (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  ∃ v : Fin n → KK D.nd i, v ≠ 0 ∧
    ∀ g, (mapM (toK D.nd i) M g).mulVec v = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def CharCrysAt (χ : GE D.nd →* (D.nd.O i)ˣ) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (charRep (Br.locChi D.nbr i w hw χ))

def MatCrysAt {n : ℕ} (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M))

def ChiRatioCrysAt : Prop :=
  ∀ c : ℕ, 1 ≤ c → c ≤ D.R.t →
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) ∧ CharCrysAt D i w hw (chiRatio D i c)

end At

theorem chiRatio_eq (D : D7) (i : D.nd.Loc) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) :
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) := by
  unfold chiRatio chiU
  rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
  rfl

theorem chiRatO_apply (D : D7) (i : D.nd.Loc) (c : ℕ) (g : GE D.nd) :
    chiRatO D.nd i c g 0 0 = ((chiRatio D i c g : (D.nd.O i)ˣ) : D.nd.O i) := by
  simp [chiRatO, twistM, chiRatio]

end GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section General

variable {O Γ : Type} [CommRing O] [IsDomain O] [Group Γ]

def fracRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) :
    Representation (FractionRing O) Γ (Fin a → FractionRing O) :=
  glRep (mapRep (algebraMap O (FractionRing O)) ρ)

def charSum (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ (Fin t → FractionRing O) where
  toFun g := LinearMap.pi fun c : Fin t =>
    algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) • LinearMap.proj c
  map_one' := by
    ext v c
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext c
    simp [mul_assoc, Algebra.smul_def]

def blockRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ ((Fin a → FractionRing O) × (Fin t → FractionRing O)) :=
  (fracRep ρ).prod (charSum χ t)

def IsoBlock {n a : ℕ} (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ))
    (t : ℕ) : Prop :=
  ∃ e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin a → FractionRing O) × (Fin t → FractionRing O)),
    ∀ g v, e (fracRep r g v) = blockRep ρ χ t g (e v)

def BlockSemisimple {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) : Prop :=
  (blockRep ρ χ t).IsSemisimpleRepresentation


omit [IsDomain O] in
def LatticeContinuous [TopologicalSpace Γ] [TopologicalSpace O] {a : ℕ}
    (ρ : Γ →* GL (Fin a) O) : Prop :=
  Continuous fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)

theorem blockRep_apply {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : (Fin a → FractionRing O) × (Fin t → FractionRing O)) :
    blockRep ρ χ t g v =
      ((((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map
          (algebraMap O (FractionRing O))).mulVec v.1,
        fun c : Fin t => algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) * v.2 c) := by
  rfl

end General

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

structure IsComplement (r₀ : G H.E N.Om →* GL (Fin R.nV) (N.O i))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop where

  rho : IsoBlock r₀ ρ (N.chi i) R.t

  ss : BlockSemisimple ρ (N.chi i) R.t

  cont : LatticeContinuous ρ

end Record

def Complement_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i,
    ∀ r₀ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i), IsHeckeGalois D.nd i π r₀ →
      ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsComplement D.nd i r₀ ρ

end GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockHodgeTateJumps
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (σ : Representation LL G V)

end Jumps

def blockJumps (t : ℕ) : Multiset ℤ := (Finset.Ico (0 : ℤ) (t : ℤ)).val

def SplitsAs {k Γ : Type} [Field k] [Group Γ] {n r t : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) k)
    (P : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → Γ → k) : Prop :=
  ∃ e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)), ∀ (g : Γ) (u : Fin n → k),
    e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ c g * (e u).2 c)

section HidaSetting

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def BlockSplit (π : N.X i) : Prop :=
  SplitsAs (mapM (toK N i) (rO N i r π)) (mapM (toK N i) (rhoO N i ρ π))
    (fun (c : Fin R.t) g => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i))

def HidaSetting (π : N.X i) : Prop :=
  GoodR N i r ∧ π ∈ N.Z i ∧
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
    BlockSplit N i r ρ π

variable {N} (L : LocTheory) (nbr : Br.NBr N)

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockJumpCount
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def IsJumpMultiset (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, multV PD ρ τ a = (J.count a : ℤ)

end Local

def blockJumps (t : ℕ) : Multiset ℤ := (Multiset.range t).map (fun k : ℕ => (k : ℤ))

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsBlockSum (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ (g : GE N) (u : Fin R.nV → KK N i),
      e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)

end Glob

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < t then 1 else 0 := by
  have hn : (blockJumps t).Nodup := (Multiset.nodup_range t).map Nat.cast_injective
  have hm : a ∈ blockJumps t ↔ 0 ≤ a ∧ a < t := by
    simp only [blockJumps, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨a.toNat, by omega, by omega⟩
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem hn (hm.2 h)
  · exact Multiset.count_eq_zero.2 (fun h' => h (hm.1 h'))

end GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SelmerSumLargePrime
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Exceptional

variable {D : D7} (L : SizeData₂ D)

end Exceptional

section Terms

variable (D : D7) (i : D.nd.Loc)

def ramLen : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def ccLen (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)

def selLen (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℕ∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def twistLen : ℕ∞ :=
  (D.R.t : ℕ∞) * ∑ P ∈ D.nd.Q i,
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {zetaP D i P - 1})

end Terms

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

end
end

