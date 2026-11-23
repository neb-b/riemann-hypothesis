module

public import Mathlib
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.PrimeDegreeVariant

open Formalism.BasicNotions MvPolynomial

def blkHom (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

def embGL (R : Type) [CommRing R] (n N : ℕ) (h : n + 1 = N) : GL (Fin n) R →* GL (Fin N) R :=
  Units.map (((Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))).toAlgHom.toRingHom.toMonoidHom).comp
    (blkHom R n))

def lastGL (R : Type) [CommRing R] (N : ℕ) (a : Rˣ) : GL (Fin N) R :=
  diagGL R N (fun i => if i.1 + 1 = N then a else 1)

def wsum {k : ℕ} (l : DomWeight k) : ℤ := ∑ i, l.w i

def Interlace {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, sg.w i ≤ lam.w ⟨i.1, by omega⟩ ∧ lam.w ⟨i.1 + 1, by omega⟩ ≤ sg.w i

def aa {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  sg.w i - lam.w ⟨i.1 + 1, by omega⟩

def bb {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  lam.w ⟨i.1, by omega⟩ - sg.w i

def D0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, (sg.w i - lam.w ⟨i.1 + 1, by omega⟩)

def D1 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg)

def degZ {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n) : ℤ := wsum lam - wsum sg

def Rset {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg))

def cBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - sg.w j + (j.1 : ℤ))

def rowsZ {n N : ℕ} (h : n + 1 = N) (i : Fin n) : Fin (i.1 + 1) → Fin N :=
  fun p => if p.1 = i.1 then ⟨N - 1, by omega⟩ else ⟨p.1, by omega⟩

def xi (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin n, (Formalism.GradedWeylDivisibility.lpMinor R (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat *
    (Formalism.GradedWeylDivisibility.initMinor R (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat

def cBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  (((2 * lam.spread : ℤ) : ℝ)) ^ ((((N : ℤ) * D1 h lam sg : ℤ) : ℝ))

def brBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  cBd h lam sg * Real.sqrt (Module.finrank ℂ (delSq ℂ N lam))

def IsIota {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
    io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) ∧
  (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
    io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s)) ∧
  io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg ∧
  (∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (io s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • io s) ∧
  (∀ s ∈ nablaSq ℂ n sg,
    (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re)

def IsBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
    br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)

def IsTranspose {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ s ∈ nablaSq ℂ n sg, ∀ f ∈ delSq ℂ N lam, normFock lam (io s) f = normFock sg s (br f)

def Branch {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧ xi ℂ h lam sg ≠ 0 ∧
  degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg ∧
  ∃ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io ∧ IsBr h lam sg br ∧ IsTranspose lam sg io br

def Conclusion6 : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

section Abstract

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

structure GoodSet (K : Type) [Field K] (G : Type) [Group G] where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  W : S → Type
  [acgW : ∀ s, AddCommGroup (W s)]
  [modW : ∀ s, Module K (W s)]
  [fdW : ∀ s, FiniteDimensional K (W s)]
  [ntW : ∀ s, Nontrivial (W s)]
  tau : ∀ s, Representation K G (W s)

  irr : ∀ s, Function.Surjective (tau s).asAlgebraHom

  inj : Function.Injective fun s g => LinearMap.trace K (W s) (tau s g)

attribute [instance] GoodSet.finS GoodSet.decS GoodSet.acgW GoodSet.modW GoodSet.fdW GoodSet.ntW

structure Pair (K : Type) [Field K] (G : Type) [Group G] where
  H : Subgroup G
  chi : H →* Kˣ

def eS (T : GoodSet K G) (s : T.S) : MonoidAlgebra K G :=
  ∑ x : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)) • MonoidAlgebra.of K G x

def eG (T : GoodSet K G) : MonoidAlgebra K G := ∑ s, eS T s


open Classical in
def eps (P : Pair K G) : MonoidAlgebra K G :=
  ((Nat.card P.H : ℕ) : K)⁻¹ • ∑ x : G, if h : x ∈ P.H then
    (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) • MonoidAlgebra.of K G x else 0

def nS (T : GoodSet K G) (P : Pair K G) (s : T.S) : ℕ :=
  Module.finrank K (LinearMap.range ((T.tau s).asAlgebraHom (eps P)))

def M1 (T : GoodSet K G) (P0 : Pair K G) : Prop := ∀ s, nS T P0 s = 1

variable (A : HLat K) (ρ : Representation K G A.V)

def cutE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M ⊓ (LinearMap.range e).restrictScalars (𝓞 K)

def dimE (e : Module.End K A.V) : ℕ := Module.finrank K (LinearMap.range e)

def degL (M : Submodule (𝓞 K) A.V) : ℝ := (Formalism.HN.rkK M : ℝ) * Formalism.HN.muDef A.b A.X M

def muMaxL (M : Submodule (𝓞 K) A.V) : ℝ := Formalism.HN.muMaxDef A.b A.X M

end Abstract

section Lemma2

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def DegreeKernelLowerBound (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  degL A A.L - (dimE A (1 - e) : ℝ) * (muMaxL A A.L + 2 * Real.log (n : ℝ)) ≤ degL A (cutE A e A.L)

end Lemma2

section Lemma4

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

end Lemma4

section Lemma8

structure GMap (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G)
    (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE) where
  VK : Type
  [acgK : AddCommGroup VK]
  [modK : Module K VK]
  [fdK : FiniteDimensional K VK]
  rhoK : Representation K G VK
  V : Type
  [acgV : AddCommGroup V]
  [modV : Module ℂ V]
  rho : Representation ℂ G V

  j : VK →ₛₗ[σ] V
  j_indep : ∀ (n : ℕ) (b : Fin n → VK), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))
  j_span : Submodule.span ℂ (Set.range j) = ⊤
  j_eq : ∀ g x, j (rhoK g x) = rho g (j x)

  good : rhoK.asAlgebraHom (eG T) = 1
  io : V →ₗ[ℂ] EE
  io_eq : ∀ g x, io (rho g x) = ρE g (io x)

attribute [instance] GMap.acgK GMap.modK GMap.fdK GMap.acgV GMap.modV

namespace GMap

variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE} (M : GMap K σ G T EE ρE)

end GMap

end Lemma8

namespace Ten

section Tensor

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (a : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => ∏ i, (a i).coeff (g i))

theorem tens_coeff (a : ∀ i, MonoidAlgebra ℂ (G i)) (g : ∀ i, G i) :
    (tens a).coeff g = ∏ i, (a i).coeff (g i) := rfl

theorem conv_coeff {H : Type} [Group H] [Fintype H] (x y : MonoidAlgebra ℂ H) (g : H) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro i; simp

theorem tens_mul (a b : ∀ i, MonoidAlgebra ℂ (G i)) :
    tens a * tens b = tens (fun i => a i * b i) := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  ext g
  rw [conv_coeff, tens_coeff]
  simp only [tens_coeff, conv_coeff]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem tens_one : tens (fun i => (1 : MonoidAlgebra ℂ (G i))) = 1 := by
  classical
  ext g
  rw [tens_coeff]
  simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.prod_boole]
  simp [funext_iff, eq_comm]

theorem sum_tens {P : ι → Type} [∀ i, Fintype (P i)] [DecidableEq ι]
    (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) :
    ∑ p : ∀ i, P i, tens (fun i => E i (p i)) = tens (fun i => ∑ q, E i q) := by
  ext g
  rw [tens_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [tens_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable [DecidableEq ι]

def plc (i : ι) (a : MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  tens (Function.update (fun _ => 1) i a)

theorem tens_mul_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (i : ι) (b : MonoidAlgebra ℂ (G i)) :
    tens a * plc i b = tens (Function.update a i (a i * b)) := by
  rw [plc, tens_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem mapDomain_mulSingle (i : ι) (a : MonoidAlgebra ℂ (G i)) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun h => Pi.mulSingle (M := G) i h) a.coeff) = plc i a := by
  classical
  ext g
  rw [MonoidAlgebra.coeff_ofCoeff, plc, tens_coeff, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hinj : Function.Injective (fun h : G i => Pi.mulSingle (M := G) i h) := Pi.mulSingle_injective i
  have hrest : ∏ j ∈ Finset.univ.erase i,
      (Function.update (fun j => (1 : MonoidAlgebra ℂ (G j))) i a j).coeff (g j) =
      if ∀ j ∈ Finset.univ.erase i, g j = 1 then 1 else 0 := by
    trans ∏ j ∈ Finset.univ.erase i, (if g j = 1 then (1 : ℂ) else 0)
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), MonoidAlgebra.one_def,
        MonoidAlgebra.coeff_single, Finsupp.single_apply]
      simp [eq_comm]
    · rw [Finset.prod_boole]; congr
  rw [hrest, Function.update_self]
  by_cases hg : ∀ j ∈ Finset.univ.erase i, g j = 1
  · have : g = Pi.mulSingle i (g i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact hg j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
    rw [if_pos hg, mul_one]
    conv_lhs => rw [this]
    exact Finsupp.mapDomain_apply_of_injective hinj _ _
  · rw [if_neg hg, mul_zero]
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨h, rfl⟩
    exact hg fun j hj => Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj) _

variable {P : ι → Type} [∀ i, Fintype (P i)]


open Classical in
def eGood (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) (good : (∀ i, P i) → Prop) :
    MonoidAlgebra ℂ (∀ i, G i) :=
  ∑ p : ∀ i, P i, if good p then tens (fun i => E i (p i)) else 0

end Tensor

end Ten

section Record

open NumberField IsDedekindDomain

@[instance_reducible] def finiteLevelGroupFintype (D : D7) : Fintype (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Finite (G0g D.nd) := inferInstance
  exact Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

structure GSp (D : D7) where
  V : Type
  [nacg : NormedAddCommGroup V]
  [ips : InnerProductSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  lat : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) V
  act : Representation ℂ (G0g D.nd) V

attribute [instance] GSp.nacg GSp.ips GSp.fd

structure Prov (D : D7) (X : BaseLevelRowSide D) where

  T : GoodSet D.what₂.LL (G0g D.nd)

  T_e : ∀ g, (eG T).coeff g = ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL)

  psi0 : D.nexp.U →* (D.what₂.LL)ˣ

  Ps : Pair D.what₂.LL (G0g D.nd)

  EEK : Type
  [nacgEE : NormedAddCommGroup EEK]
  [ipsEE : InnerProductSpace ℂ EEK]
  [fdEE : FiniteDimensional ℂ EEK]

  sK : RowSide D EEK

  actEE : Representation ℂ (G0g D.nd) EEK

  actAmb : ∀ μ, Representation ℂ (G0g D.nd) (sK.Amb μ)

  cen_tie : ∀ μ z, sK.cen μ z = (actAmb μ).asAlgebraHom (z : MonoidAlgebra ℂ (G0g D.nd))

  MtK : D.what₂.Tup → ℕ → GSp D

  MjK : ℕ → GSp D

  thK : ∀ μ j, (MtK μ j).V →ₗ[ℂ] (MjK j).V

  rho : Representation D.what₂.LL (G0g D.nd) sK.RR.V

  j0 : X.principalHermitianLattice.V →ₗ[D.what₂.LL] sK.RR.V

  js : D.div.RR.V →ₗ[D.what₂.LL] sK.RR.V

attribute [instance] Prov.nacgEE Prov.ipsEE Prov.fdEE

variable {D : D7} {X : BaseLevelRowSide D}

def Prov.P0 (Y : Prov D X) : Pair D.what₂.LL (G0g D.nd) := ⟨D.nexp.U, Y.psi0⟩

def Conclusion0 (D : D7) : Prop :=
  ∀ Y : ℝ, (∀ i, (D.host.g i : ℝ) ≤ 2 * Y) → lam0 D ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * Y)

section GoodType

local instance factG (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

namespace Ten

def ESer (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (p : Fin D.R.r → ZMod (D.host.g kv.1)) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p)

def goodVec (D : D7) (p : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) : Prop :=
  D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩))

theorem monicOf_inj {K : Type} [Field K] {N : ℕ} (a b : Fin N → K)
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_inj] at hc
  simpa [i.isLt.ne, Finset.sum_ite_eq, Finset.sum_ite_eq'] using hc

theorem ESer_sum (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) : ∑ p, ESer D kv p = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum kv.1
  rw [← hsum]
  have himg : ∑ p, ESer D kv p =
      ∑ f ∈ Finset.univ.image (fun p : Fin D.R.r → ZMod (D.host.g kv.1) => Formalism.CyclotomicNorms.monicOf p),
        D.ntypes.eSer kv.1 f := by
    rw [Finset.sum_image fun a _ b _ h => monicOf_inj a b h]
    rfl
  rw [himg]
  symm
  refine Finset.sum_subset (fun f hf => ?_) fun f _ hf => ?_
  · obtain ⟨hm, hd, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd⟩
  · exact D.ntypes.eSer_zero _ _ fun hh => hf ((hS f).2 hh)

theorem e0_eq (D : D7) [DecidableEq (Σ k : Fin 2, D.nd.PlG k)] : D.ntypes.e0 = eGood (ESer D) (goodVec D) := by
  classical
  ext g
  rw [eGood, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  show (∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))), _) = _
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : goodVec D p
  · rw [if_pos hp]; exact (if_pos hp).trans rfl
  · rw [if_neg hp]; exact (if_neg hp).trans rfl

theorem atPlace_eq (D : D7) [DecidableEq (Σ k : Fin 2, D.nd.PlG k)] (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a =
      plc (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ a := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  convert mapDomain_mulSingle (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) a
  all_goals rfl

end Ten


end GoodType

theorem sharp_downTo (D : D7) (μ : D.what₂.Tup) (j : ℕ) :
    (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp ((RowSide.sharp D).io μ j) =
      (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]
    all_goals rfl

def frg (D : D7) : ℝ := (D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)

def LabTie (Y : Prov D X) (lab : Y.T.S → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))) : Prop :=
  ∀ s (g : G0g D.nd), D.what₂.embLL ((eS Y.T s).coeff g) =
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (lab s kv.1 kv.2)).coeff (g kv)

def LevelRatioBound (D : D7) : Prop := 4 * D.R.f * D.R.r ≤ min (D.host.g 0) (D.host.g 1)

def LatticeChainWithoutLast (Y : Prov D X) : Prop :=
  ∀ lab, LabTie Y lab → ∀ s, D.ntypes.goodTuple (lab s) → nS Y.T Y.P0 s = 1

end Record

section Herm

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

end Herm

section Whole

variable {D : D7} {X : BaseLevelRowSide D}

end Whole

section Family

open Formalism.MainNotions

variable {ε : ℝ}

end Family

end Formalism.MainNotions.PrimeDegreeVariant
