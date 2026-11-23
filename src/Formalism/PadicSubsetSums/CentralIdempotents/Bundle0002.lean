module

public import Mathlib
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.GaloisIrreducibility.Statement

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
section
open Finset Polynomial Formalism.CyclotomicNorms

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.TW

def CentralIdempotentIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G]
    (e : MonoidAlgebra K G), e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * e.coeff g)

def relLen {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℕ∞ :=
  Module.length O (↥M ⧸ N.comap M.subtype)

def sIdx {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℤ :=
  ((relLen M N).toNat : ℤ) - ((relLen N M).toNat : ℤ)




end Formalism.IrreducibleCountingLemmas.TW
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic
section
noncomputable section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

def ResidueCharpolyEq : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (G : Type) (n : ℕ) (r : X' → G → Matrix (Fin n) (Fin n) O),
    (∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (x y : X') (g : G),
      Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) ∧
      ((r x g).map (IsLocalRing.residue O)).charpoly =
        ((r y g).map (IsLocalRing.residue O)).charpoly

def GoodCuspidalOne : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]), 1 ≤ r →
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    Fintype.card I = 1 ∧ ∀ i, d i = 1 ∧ n i = r

def CharpolyOverSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O))
    (n : ℕ) (M : X' → Matrix (Fin n) (Fin n) O),
    (∀ j : ℕ, (fun x => (Matrix.charpolyRev (M x)).coeff j) ∈ T) →
    ∃ F : T[X], F.Monic ∧ ∀ x, F.map (ev T x) = (M x).charpoly

def FactorOverLocalSubalgebraMonic : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]), F.Monic →
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧ ∀ x, P.map (ev T x) = s x

def FactorAnnihilatorFamily : Prop :=
  ∀ (O K : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K],
    Function.Injective (algebraMap O K) →
    ∀ (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)), IsLocalRing T →
    ∀ (V : X' → Type) [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
      [∀ x, FiniteDimensional K (V x)] (A B : ∀ x, Submodule K (V x))
      (γ₀ γ : ∀ x, Module.End K (V x)) (c cγ : O) (t : ℕ) (F : T[X]),
    (∀ x, (F.map (ev T x)).map (algebraMap O K) = (γ₀ x).charpoly) →
    (∀ x, IsCompl (A x) (B x)) → (∀ x, ∀ v ∈ A x, γ₀ x v ∈ A x) → (∀ x, ∀ v ∈ A x, γ x v ∈ A x) →
    (∀ x, ∀ v ∈ B x, γ₀ x v = algebraMap O K c • v) →
    (∀ x, ∀ v ∈ B x, γ x v = algebraMap O K cγ • v) →
    (∀ x, Module.finrank K (B x) = t) →
    (∀ x, ((F.map (ev T x)).map (IsLocalRing.residue O)).rootMultiplicity
      (IsLocalRing.residue O c) = t) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, (aeval (γ₀ x) ((P.map (ev T x)).map (algebraMap O K))) *
        (γ x - algebraMap K (Module.End K (V x)) (algebraMap O K cγ)) = 0

end Formalism.IrreducibleCountingLemmas.Z
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
section
open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def glEquiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv

variable {K} in
def transp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (τ : FDRep ℂ (GL ι K)) : FDRep ℂ (GL κ K) :=
  FDRep.of (τ.ρ.comp (glEquiv K e).symm.toMonoidHom)

structure LabelMap (C : LabelConv K) where
  lab : ∀ d : ℕ, FDRep ℂ (GL (Fin d) K) → K[X]
  lab_iso : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), Nonempty (τ ≅ τ') → lab d τ = lab d τ'
  lab_spec : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    (lab d τ).Monic ∧ Irreducible (lab d τ) ∧ lab d τ ≠ X ∧ (lab d τ).natDegree = d
  lab_inj : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' → lab d τ = lab d τ' → Nonempty (τ ≅ τ')
  lab_one : ∀ (τ : FDRep ℂ (GL (Fin 1) K)) (x : K), Simple τ → x ≠ 0 →
    (∀ (γ : GL (Fin 1) K) (m : ℕ),
      C.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = C.ι (algebraMap K (AlgebraicClosure K) x) ^ m) →
    lab 1 τ = X - Polynomial.C x


variable {K} in
def LabelMapEquivariant {C : LabelConv K} (O : LabelMap K C) : Prop :=
  (∀ (d : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ),
    (∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 → α ζ = ζ ^ a) →
    ∀ τ τ' : FDRep ℂ (GL (Fin d) K), 1 ≤ d → Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) →
      rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (· ^ a)) ∧
  ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' →
    (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) →
    rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (·⁻¹)

variable {K} {C : LabelConv K}

def labO (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] (σ : FDRep ℂ (GL κ K)) : K[X] :=
  O.lab (Fintype.card κ) (transp (Fintype.equivFin κ) σ)

def HasLabelO (O : LabelMap K C) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, labO O (lam c)

def DisjointMultO (O : LabelMap K C) : Prop :=
  ∀ (n : ℕ) (b : Fin n → Fin 2) (τ σ : ∀ c : Fin 2, FDRep ℂ (GL {i // b i = c} K)) (f f' : Fin 2 → K[X]),
    Function.Surjective b →
    (∀ c, Simple (τ c) ∧ Simple (σ c) ∧ HasLabelO O (τ c) (f c) ∧ HasLabelO O (σ c) (f' c)) →
    IsCoprime (f 0) (f' 1) → IsCoprime (f 1) (f' 0) →
    Module.finrank ℂ (Intw (hcRep K b τ) (hcRep K b σ)) =
      Module.finrank ℂ (Intw (τ 0).ρ (σ 0).ρ) * Module.finrank ℂ (Intw (τ 1).ρ (σ 1).ρ)



def twoBlock (n a : ℕ) : Fin n → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1




def ZIdemOccurs : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Simple τ →
    ((∃ v : V, ρ.asAlgebraHom (zIdem τ) v ≠ 0) ↔ IsConstituent τ ρ)

end Formalism.IrreducibleCountingLemmas.TYPES

namespace Formalism.IrreducibleCountingLemmas.TYPES

section BaseChange
variable {Γ : Type} [Group Γ]

def bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) : Representation ℂ Γ (Fin (Module.finrank ℂ V) → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ ≃ₐ[ℂ]
      ((Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))).toRingEquiv.toMonoidHom.comp
    ((σ.toRingHom.mapMatrix : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →+*
        Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toRingEquiv.toMonoidHom.comp ρ))

def bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : FDRep ℂ Γ := FDRep.of (bcRepr σ τ.ρ)

theorem trace_bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) (γ : Γ) :
    LinearMap.trace ℂ _ (bcRepr σ ρ γ) = σ (LinearMap.trace ℂ V (ρ γ)) := by
  have h1 : bcRepr σ ρ γ = Matrix.toLin' (σ.toRingHom.mapMatrix
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ γ))) := rfl
  rw [h1, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ _), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ γ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem finrank_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) :
    Module.finrank ℂ (bc σ τ) = Module.finrank ℂ τ := by
  exact Module.finrank_fin_fun ℂ

theorem zIdem_coeff [Fintype Γ] (τ : FDRep ℂ Γ) (γ : Γ) :
    (zIdem τ).coeff γ = (Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹) := by
  classical
  unfold zIdem
  simp [MonoidAlgebra.coeff, Finsupp.finsetSum_apply, Finsupp.single_apply, MonoidAlgebra.single]
end BaseChange

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def BcZIdem : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ),
    σ ((zIdem τ).coeff γ) = (zIdem (bc σ τ)).coeff γ

theorem galoisConjCentralIdempotent : BcZIdem := by
  intro Γ _ _ σ τ γ
  have h : LinearMap.trace ℂ (bc σ τ) ((bc σ τ).ρ γ⁻¹) = σ (LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) :=
    trace_bcRepr σ τ.ρ γ⁻¹
  rw [zIdem_coeff, zIdem_coeff, finrank_bc, h, map_mul, map_div₀, map_natCast, map_natCast]

end Formalism.IrreducibleCountingLemmas.TYPES

namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

end Formalism.IrreducibleCountingLemmas.TYPES
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
section
open Finset Polynomial
open scoped Classical ComplexOrder

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)


open Classical in
def BB (g N : ℕ) : Finset ℕ :=
  insert g ((Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))))

def primeToPart {M : Type*} [Monoid M] (l : ℕ) (x : M) : M :=
  x ^ ((ordProj[l] (orderOf x)) ^ Nat.totient (ordCompl[l] (orderOf x)))

def PrimeToPartSpec : Prop :=
  ∀ (M : Type) [Monoid M] (l : ℕ) (x : M), l.Prime → IsOfFinOrder x →
    orderOf (primeToPart l x) = ordCompl[l] (orderOf x) ∧
      ∃ a : ℕ, x ^ (l ^ a) = primeToPart l x ^ (l ^ a)

def PrimeToPartEqIff : Prop :=
  ∀ (M : Type) [Monoid M] (l : ℕ) (x y : M), l.Prime → IsOfFinOrder x → IsOfFinOrder y →
    (primeToPart l x = primeToPart l y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a))

def GoodAt (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {ι J : Type} (N : ℕ)
    (f : ι → K[X]) (χ : ι → J → Kˣ) : Prop :=
  (∀ v, (f v).Monic ∧ (f v).natDegree = N ∧ (f v).coeff 0 ≠ 0) ∧
  (∀ v, Squarefree (f v)) ∧
  (∀ l : ℕ, l.Prime → l ∉ BB (Fintype.card K) N →
    ∀ v, Set.InjOn (primeToPart l) ((f v).rootSet L)) ∧
  (∀ l : ℕ, l.Prime → l ≠ Fintype.card K → ∀ v j, ∀ x ∈ (f v).rootSet L,
    primeToPart l x ≠ primeToPart l (algebraMap K L (χ v j : K)) ∧
    primeToPart l x ≠ primeToPart l (algebraMap K L ((χ v j)⁻¹ : Kˣ))) ∧
  (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ h : K[X], h ∣ f v ∧ h.natDegree = a) ∧
  (∃ v, ∃ P : K[X], Irreducible P ∧ P ∣ f v ∧ P.natDegree.Prime ∧
    N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N)

def Good (K₁ L₁ K₂ L₂ : Type) [Field K₁] [Fintype K₁] [Field L₁] [Algebra K₁ L₁]
    [Field K₂] [Fintype K₂] [Field L₂] [Algebra K₂ L₂] {ι₁ J₁ ι₂ J₂ : Type} (N : ℕ)
    (f₁ : ι₁ → K₁[X]) (χ₁ : ι₁ → J₁ → K₁ˣ) (f₂ : ι₂ → K₂[X]) (χ₂ : ι₂ → J₂ → K₂ˣ) : Prop :=
  GoodAt K₁ L₁ N f₁ χ₁ ∧ GoodAt K₂ L₂ N f₂ χ₂


open Classical in
def DivisorDegreeSubSum : Prop :=
  ∀ (K : Type) [Field K] (f : K[X]) (a : ℕ), f ≠ 0 →
    ((∃ h : K[X], h ∣ f ∧ h.natDegree = a) ↔
      IsSubSum ((UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree) a)


open Classical in
def LemmaP : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A)).card
      ≤ 7 * N.factorial

def monicOf {K : Type*} [Field K] {N : ℕ} (c : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ)


open Classical in
def SquarefreeCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 1 ≤ N →
    Fintype.card K ^ N ≤
      ((Finset.univ : Finset (Fin N → K)).filter
        (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card
      + 2 * Fintype.card K ^ (N - 1)


open Classical in
def IrredCountUpper : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    d * ((Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c))).card
      ≤ Fintype.card K ^ d



open Classical in
def TypeCountExact : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((UniqueFactorizationMonoid.normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
    ∏ d ∈ Finset.Icc 1 N,
      (((Finset.univ : Finset (Fin d → K)).filter
        (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d)


open Classical in
def CycleTypeProb : Prop :=
  ∀ (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ : Equiv.Perm (Fin N) => ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d)).card *
      ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial


open Classical in
def CycleProbPrime : Prop :=
  ∀ N p : ℕ, p.Prime → p ≤ N → N < 2 * p →
    p * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => p ∈ σ.cycleType)).card
      = N.factorial


open Classical in
def CycleProbSum : Prop :=
  ∀ N : ℕ,
    (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) =
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
      (N.factorial : ℝ) / p

def PrimeRecipSum : Prop :=
  ∀ N : ℕ, 100 ≤ N →
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p





open Classical in
def FrobOrbitIrred : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (f : K[X]),
    f.Monic → Irreducible f →
    IsOrbit (fun x : L => x ^ Fintype.card K) (f.aroots L).toFinset ∧
      (f.aroots L).toFinset.card = f.natDegree

def centralIdem {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : MonoidAlgebra ℂ G :=
  ∑ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) •
    MonoidAlgebra.of ℂ G g

def CentralIdempotent : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V),
    (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    centralIdem ρ * centralIdem ρ = centralIdem ρ ∧
      ∀ x : MonoidAlgebra ℂ G, centralIdem ρ * x = x * centralIdem ρ

def CentralIdemOrthogonal : Prop :=
  ∀ (G V W : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial V] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    (∀ U : Submodule ℂ V, (∀ g, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) →
    (¬ ∃ φ : V ≃ₗ[ℂ] W, ∀ g x, φ (ρ g x) = σ g (φ x)) →
    centralIdem ρ * centralIdem σ = 0

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
end

