module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
section
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

def Dinv (ρ : Representation L G V) : Submodule L (V ⊗[F] B) :=
  ⨅ g, LinearMap.ker (AlgebraTensorModule.map (ρ g) (σ g) - LinearMap.id)

theorem mem_Dinv {ρ : Representation L G V} {x : V ⊗[F] B} :
    x ∈ Dinv σ ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (σ g) x = x := by
  simp [Dinv, Submodule.mem_iInf, sub_eq_zero]


variable (L V) in
def onPer : End L (V ⊗[F] B) := AlgebraTensorModule.map LinearMap.id ψ

def admitted (e : ℕ) (ρ : Representation L G V) : Prop := finrank L (Dinv σ ρ) = e * finrank L V

def AnnD (q n : ℕ) (ρ : Representation L G V) (T : ℕ → End L V) : Prop :=
  ∀ x ∈ Dinv σ ρ, ∑ j ∈ Finset.range (n + 1),
    ((-1) ^ j * (q : ℤ) ^ (j.choose 2)) • AlgebraTensorModule.map (T j) (ψ ^ (n - j)) x = 0

def NilD (ρ : Representation L G V) (Q : Polynomial L) : Prop :=
  ∃ N : ℕ, ∀ x ∈ Dinv σ ρ, (Polynomial.aeval (onPer ψ L V) Q ^ N) x = 0


variable (L) in
def Bound (e : ℕ) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U] (ρ : Representation L G U),
    Module.Finite L (Dinv σ ρ) ∧ finrank L (Dinv σ ρ) ≤ e * finrank L U

end

def Inter {L G V W : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) (f : V →ₗ[L] W) : Prop := ∀ g v, f (ρ g v) = ρ' g (f v)

def Subq {L G V W : Type} [Field L] [Group G] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) : Prop :=
  ∃ (U : Type) (_ : AddCommGroup U) (_ : Module L U) (ρU : Representation L G U) (i : U →ₗ[L] V) (p : U →ₗ[L] W),
    Inter ρU ρ i ∧ Function.Injective i ∧ Inter ρU ρ' p ∧ Function.Surjective p

def extRep {F G V : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] (L : Type) [Field L] [Algebra F L]
    (ρ : Representation F G V) : Representation L G (L ⊗[F] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one F V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def DinvExact : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L]
    (U V W : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [AddCommGroup V] [Module L V] [Module F V]
    [IsScalarTower F L V] [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W) (i : U →ₗ[L] V) (p : V →ₗ[L] W),
    Inter ρU ρV i → Inter ρV ρW p → Function.Injective i → Function.Exact i p → Module.Finite L (Dinv σ ρV) →
    (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) ≤ Dinv σ ρW ∧
    finrank L (Dinv σ ρV) = finrank L (Dinv σ ρU) +
      finrank L ((Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))

def AdmExact : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L] (e : ℕ),
    Bound σ L e → ∀ (V W : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρ : Representation L G V) (ρ' : Representation L G W) (f : V →ₗ[L] W), Inter ρ ρ' f →
    (Function.Injective f → admitted σ e ρ' → admitted σ e ρ) ∧
    (Function.Surjective f → admitted σ e ρ → admitted σ e ρ' ∧
      (Dinv σ ρ).map (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρ')

def NilEmb : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (ρ : Representation L G V)
    (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)] [∀ i, Module F (W i)]
    [∀ i, IsScalarTower F L (W i)] (ρ' : ∀ i, Representation L G (W i)) (f : ∀ i, V →ₗ[L] W i),
    (∀ i, Inter ρ (ρ' i) (f i)) → (∀ v, (∀ i, f i v = 0) → v = 0) →
    ∀ Q : Polynomial L, (∀ i, NilD σ ψ (ρ' i) Q) → NilD σ ψ ρ Q

def NilSubq : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (e : ℕ), Bound σ L e → ∀ (V W : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    (ρ : Representation L G V) (ρ' : Representation L G W), Subq ρ ρ' → admitted σ e ρ →
    admitted σ e ρ' ∧ ∀ Q : Polynomial L, NilD σ ψ ρ Q → NilD σ ψ ρ' Q

def NilOfAnn : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B), (∀ g, Commute (σ g) ψ) →
    ∀ (L : Type) [Field L] [Algebra F L] (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (ρ : Representation L G V) (q n : ℕ) (T : ℕ → End L V) (θ : ℕ → L), (∀ j g, Commute (T j) (ρ g)) → (∀ i j, Commute (T i) (T j)) →
    (∀ j ≤ n, IsNilpotent (T j - θ j • (1 : End L V))) → AnnD σ ψ q n ρ T → NilD σ ψ ρ (heckePol q n θ)

def AnnSub : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (U V : Type) [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [AddCommGroup V] [Module L V] [Module F V]
    [IsScalarTower F L V] (ρU : Representation L G U) (ρ : Representation L G V) (i : U →ₗ[L] V), Inter ρU ρ i → Function.Injective i →
    ∀ (q n : ℕ) (TU : ℕ → End L U) (T : ℕ → End L V), (∀ j u, i (TU j u) = T j (i u)) → AnnD σ ψ q n ρ T → AnnD σ ψ q n ρU TU

def DinvExt : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module F V] (ρ : Representation F G V),
    (Dinv σ (extRep L ρ)).map (AlgebraTensorModule.assoc F F L L V B).toLinearMap = (Dinv σ ρ).baseChange L

def AnnExt : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B) (L : Type) [Field L] [Algebra F L]
    (V : Type) [AddCommGroup V] [Module F V] (ρ : Representation F G V),
    (∀ e, admitted σ e ρ → admitted σ e (extRep L ρ)) ∧
    ∀ (q n : ℕ) (T : ℕ → End F V), AnnD σ ψ q n ρ T → AnnD σ ψ q n (extRep L ρ) fun j => (T j).baseChange L

def AnnPer : Prop :=
  ∀ (F G B B' : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (σ : G → End F B) (ψ : End F B) (σ' : G → End F B') (ψ' : End F B') (c : B →ₗ[F] B'), Function.Injective c →
    (∀ g b, c (σ g b) = σ' g (c b)) → (∀ b, c (ψ b) = ψ' (c b)) →
    ∀ (L : Type) [Field L] [Algebra F L] (e : ℕ), Bound σ' L e →
    ∀ (V : Type) [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V] (ρ : Representation L G V),
      admitted σ e ρ → admitted σ' e ρ ∧ ∀ (q n : ℕ) (T : ℕ → End L V), AnnD σ ψ q n ρ T → AnnD σ' ψ' q n ρ T

def JoinAbs : Prop :=
  ∀ (F G B : Type) [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B), (∀ g, Commute (σ g) ψ) →
    ∀ (L : Type) [Field L] [Algebra F L] (e : ℕ), Bound σ L e →
    ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] (ρ : Representation F G V) (q n : ℕ) (T : ℕ → End F V),
      admitted σ e ρ → AnnD σ ψ q n ρ T →
    ∀ (U : Type) [AddCommGroup U] [Module L U] (ρU : Representation L G U) (i : U →ₗ[L] L ⊗[F] V) (TU : ℕ → End L U) (θ : ℕ → L),
      Inter ρU (extRep L ρ) i → Function.Injective i → (∀ j u, i (TU j u) = (T j).baseChange L (i u)) →
      (∀ j g, Commute (TU j) (ρU g)) → (∀ j j', Commute (TU j) (TU j')) → (∀ j ≤ n, IsNilpotent (TU j - θ j • (1 : End L U))) →
    ∀ (W : Type) [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] (ρW : Representation L G W)
      (I : Type) [Finite I] (C : I → Type) [∀ a, AddCommGroup (C a)] [∀ a, Module L (C a)] (ρC : ∀ a, Representation L G (C a))
      (f : ∀ a, W →ₗ[L] C a), (∀ a, Subq ρU (ρC a)) → (∀ a, Inter ρW (ρC a) (f a)) → (∀ v, (∀ a, f a v = 0) → v = 0) →
      NilD σ ψ ρW (heckePol q n θ)

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
section
noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace UpperTheory.Gal.crystallineComparison

theorem pts_map {J P Q : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ) (v : ∀ j, I j → P) (g : P → Q) :
    (pts a v).map g = pts a fun j i => g (v j i) := by
  unfold pts
  have h := map_sum (Multiset.mapAddMonoidHom g) (fun j => a j • Multiset.map (v j) Finset.univ.val) Finset.univ
  simp only [Multiset.mapAddMonoidHom_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Multiset.map_nsmul, Multiset.map_map]
  rfl

abbrev mapP {R B ι : Type} [CommRing R] [CommRing B] (f : R →+* B) (N : Polynomial (MvPolynomial ι R)) : Polynomial (MvPolynomial ι B) :=
  N.map (MvPolynomial.map f)

def MatRep : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Projective R S],
    ∃ (m : ℕ) (M : S → Matrix (Fin m) (Fin m) R), ∀ (B : Type) [CommRing B] [Algebra R B] (I : Type) [Fintype I] [DecidableEq I]
      (z : I → (S →ₐ[R] B)), Splits z → ∃ (P : Matrix I (Fin m) B) (Q : Matrix (Fin m) I B), P * Q = 1 ∧
        ∀ s, (M s).map (algebraMap R B) = Q * Matrix.diagonal (fun i => z i s) * P

def DetSplit : Prop :=
  ∀ (A : Type) [CommRing A] (m : ℕ) (I : Type) [Fintype I] [DecidableEq I] (P : Matrix I (Fin m) A) (Q : Matrix (Fin m) I A),
    P * Q = 1 → ∀ d : I → A, (1 - Q * P + Q * Matrix.diagonal d * P).det = ∏ i, d i

def NormEx : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Projective R S] (ι : Type) [Fintype ι] (s : ι → S),
    ∃ N : Polynomial (MvPolynomial ι R), ∀ (B : Type) [CommRing B] [Algebra R B] (I : Type) [Fintype I] (z : I → (S →ₐ[R] B)),
      Splits z → mapP (algebraMap R B) N = ∏ i, form fun k => z i (s k)

def SplitsBC : Prop :=
  ∀ (R R' S B : Type) [CommRing R] [CommRing R'] [CommRing S] [CommRing B] [Algebra R R'] [Algebra R S] [Algebra R B] [Algebra R' B]
    [IsScalarTower R R' B] (I : Type) (z : I → (S →ₐ[R] B)), Splits z →
    ∃ z' : I → (R' ⊗[R] S →ₐ[R'] B), Splits z' ∧ ∀ i s, z' i (1 ⊗ₜ s) = z i s

def SplitsOfEquiv : Prop :=
  ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B] (I : Type)
    (e : B ⊗[R] S ≃ₐ[B] (I → B)), ∃ z : I → (S →ₐ[R] B), Splits z

def SplitsField : Prop :=
  ∀ (R S K : Type) [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra R K],
    Algebra.Etale K (K ⊗[R] S) → Finite (S →ₐ[R] K) ∧ Splits (fun z : S →ₐ[R] K => z)

def EtOfUnit : Prop :=
  ∀ (l : ℕ) (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B],
    Algebra.Etale (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) → IsUnit (l : B) → Algebra.Etale B (B ⊗[R] S)

def RankOfDeg : Prop :=
  ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] [Module.Finite A S] [Algebra.Etale A S] (d : ℕ),
    (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra A K], Nat.card (S →ₐ[A] K) = d) → Module.rankAtStalk (R := A) S = d

def InjSplit : Prop :=
  ∀ (l d : ℕ) (R S : Type) [CommRing R] [CommRing S] [Algebra R S], EtAway l d R S →
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra (Localization.Away (l : R)) T) (m : ℕ)
      (z : Fin m → (Localization.Away (l : R) ⊗[R] S →ₐ[Localization.Away (l : R)] T)),
      Function.Injective (algebraMap (Localization.Away (l : R)) T) ∧ Splits z

def CoeffInt : Prop :=
  ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (ι I : Type) [Fintype ι] [Fintype I] (c : I → ι → T),
    (∀ i k, IsIntegral R (c i k)) → ∀ (a : ℕ) (m : ι →₀ ℕ), IsIntegral R (AddMonoidAlgebra.coeff ((∏ i, form (c i)).coeff a) m)

def LiftP : Prop :=
  ∀ (R T ι : Type) [CommRing R] [CommRing T] (f : R →+* T) (N' : Polynomial (MvPolynomial ι T)),
    (∀ (a : ℕ) (m : ι →₀ ℕ), ∃ r, f r = AddMonoidAlgebra.coeff (N'.coeff a) m) → ∃ N, mapP f N = N'

def NormInt : Prop :=
  ∀ (l d : ℕ) (R S : Type) [CommRing R] [CommRing S] [Algebra R S], EtAway l d R S →
    (∀ c : Localization.Away (l : R), IsIntegral R c → ∃ r : R, algebraMap R _ r = c) → ∀ (ι : Type) [Fintype ι] (s : ι → S),
    ∃ N : Polynomial (MvPolynomial ι R), ∀ (B : Type) [CommRing B] [Algebra R B], IsUnit (l : B) →
      ∀ (I : Type) [Fintype I] (z : I → (S →ₐ[R] B)), Splits z → mapP (algebraMap R B) N = ∏ i, form fun k => z i (s k)

def NormRead : Prop :=
  ∀ (l d : ℕ) (R S : Type) [CommRing R] [CommRing S] [Algebra R S], EtAway l d R S →
    (∀ c : Localization.Away (l : R), IsIntegral R c → ∃ r : R, algebraMap R _ r = c) → ∀ (ι : Type) [Fintype ι] (s : ι → S),
    ∃ N : Polynomial (MvPolynomial ι R),
      (∀ (B : Type) [CommRing B] [Algebra R B], (l : B) ∈ nonZeroDivisors B →
        ∀ (I : Type) [Fintype I] (z : I → (S →ₐ[R] B)), SplitsAway l z → mapP (algebraMap R B) N = ∏ i, form fun k => z i (s k)) ∧
      (∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [Algebra R V], (l : V) ≠ 0 →
        Finite (S →ₐ[R] V) ∧ ∀ (I : Type) [Fintype I] (z : I → (S →ₐ[R] V)), Function.Bijective z →
          mapP (algebraMap R V) N = ∏ i, form fun k => z i (s k))

def ValPts : Prop :=
  ∀ (R S V : Type) [CommRing R] [CommRing S] [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R S] [Algebra R V] [Module.Finite R S],
    Function.Bijective fun z : S →ₐ[R] V => (IsScalarTower.toAlgHom R V (FractionRing V)).comp z

def ValLift : Prop :=
  ∀ (R : Type) [CommRing R] (l : R), l ∈ nonZeroDivisors R → ∀ (𝔭 : Ideal R) [𝔭.IsPrime],
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (_ : IsAlgClosed (FractionRing V)) (_ : Algebra R V),
      algebraMap R V l ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap (algebraMap R V) = 𝔭

def PtsProd : Prop :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (ι J : Type) [Fintype ι] [Fintype J] (I : J → Type) [∀ j, Fintype (I j)]
    (a : J → ℕ) (v : ∀ j, I j → ι → B),
    ((pts a fun j i k => ρ (v j i k)).map form).prod = mapP ρ (∏ j, (∏ i, form (v j i)) ^ a j)

def CongrRad : Prop :=
  ∀ (R : Type) [CommRing R] (𝔞 : Ideal R), 𝔞.IsRadical → ∀ (ι : Type) (N N' : Polynomial (MvPolynomial ι R)),
    (∀ 𝔭 ∈ 𝔞.minimalPrimes, ∃ (κ : Type) (_ : CommRing κ) (f : R →+* κ), RingHom.ker f = 𝔭 ∧ mapP f N = mapP f N') →
    ∀ (B' : Type) [CommRing B'] (g : R →+* B'), (∀ x ∈ 𝔞, g x = 0) → mapP g N = mapP g N'

def GaussLin : Prop :=
  ∀ (A ι : Type) [CommRing A] (c : A) (s : Multiset (MvPolynomial ι A)), (∀ p ∈ s, ∃ m, AddMonoidAlgebra.coeff p m = 1) →
    MvPolynomial.C c * s.prod = 0 → c = 0

def SameNormBasic : Prop :=
  ∀ (A ι : Type) [CommRing A] [Fintype ι],
    (∀ (A' : Type) [CommRing A'] (ρ : A →+* A') (u u' : Multiset (ι → A)), SameNorm u u' →
      SameNorm (u.map fun c k => ρ (c k)) (u'.map fun c k => ρ (c k))) ∧
    (∀ (x : ι → A) (u u' : Multiset (ι → A)), SameNorm (x ::ₘ u) (x ::ₘ u') → SameNorm u u') ∧
    (Nontrivial A → ∀ u u' : Multiset (ι → A), SameNorm u u' → u.card = u'.card) ∧
    (∀ (x : ι → A) (u u' : Multiset (ι → A)), SameNorm u u' → x ∈ u →
      (u'.map fun y => ∑ k, MvPolynomial.C (x k - y k) * MvPolynomial.X k : Multiset (MvPolynomial ι A)).prod = 0)

def LinFactor : Prop :=
  ∀ (B ι : Type) [CommRing B] [Fintype ι] (w : B) (d : ι → B), (∃ k, d k ∣ w) → (∀ k k', d k ∣ w → d k ∣ d k' ∨ d k' ∣ d k) →
    ∃ (c : B) (e : ι → B) (k₀ : ι), c ∣ w ∧ e k₀ = 1 ∧ ∀ k, d k = c * e k

def MatchStep : Prop :=
  ∀ (B : Type) [CommRing B] (ϖ : B), ϖ ∈ nonZeroDivisors B → ¬ IsUnit ϖ →
  ∀ (ι : Type) [Fintype ι] (N m : ℕ), 0 < m → ∀ (u u' : Multiset (ι → B)), u'.card ≤ N →
    SameNorm (redMod (ϖ ^ (m * (N + 1))) u) (redMod (ϖ ^ (m * (N + 1))) u') → ∀ x ∈ u,
    (∀ y ∈ u', ∀ k k', x k - y k ∣ ϖ ^ m → x k - y k ∣ x k' - y k' ∨ x k' - y k' ∣ x k - y k) →
    (∀ y ∈ u', ∀ k, x k - y k ∣ ϖ ^ m ∨ ϖ ^ m ∣ x k - y k) → ∃ y ∈ u', ∀ k, ϖ ^ m ∣ x k - y k

def IdemCover : Prop :=
  ∀ (B : Type) [CommRing B] (Λ : Type) [Fintype Λ] (J : Λ → Ideal B),
    (∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ σ, ∃ e ∈ J σ, IsIdempotentElem e ∧ e ∉ 𝔪) →
    ∃ e : Λ → B, CompleteOrthogonalIdempotents e ∧ ∀ σ, e σ ∈ J σ

def ValLocal : Prop :=
  ∀ (B : Type) [CommRing B] (ϖ : B), ValLike ϖ → ∀ (𝔪 : Ideal B), 𝔪.IsPrime → ∀ (D : Finset B) (M : ℕ),
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ (∀ d ∈ D, ∀ m ≤ M, d ∣ e * ϖ ^ m ∨ ϖ ^ m ∣ e * d) ∧
      ∀ d ∈ D, ∀ d' ∈ D, d ∣ e * ϖ ^ M → d ∣ e * d' ∨ d' ∣ e * d

def PermOfMap : Prop :=
  ∀ (I I' P : Type) [Fintype I] [Fintype I'] (f : I → P) (g : I' → P), Finset.univ.val.map f = Finset.univ.val.map g →
    ∃ σ : I ≃ I', ∀ i, f i = g (σ i)

def MatchPart : Prop :=
  ∀ (B : Type) [CommRing B] (ϖ : B), ϖ ∈ nonZeroDivisors B →
  ∀ (ι : Type) [Fintype ι] (I I' : Type) [Fintype I] [Fintype I'] (N : ℕ),
    Fintype.card I = N → Fintype.card I' = N → ∀ (u : I → ι → B) (u' : I' → ι → B),
    SameNorm (redMod (ϖ ^ (N + 1) ^ N) (Finset.univ.val.map u)) (redMod (ϖ ^ (N + 1) ^ N) (Finset.univ.val.map u')) →
    ∀ e : B, IsIdempotentElem e →
    (∀ i i' k, ∀ m ≤ (N + 1) ^ N, u i k - u' i' k ∣ e * ϖ ^ m ∨ ϖ ^ m ∣ e * (u i k - u' i' k)) →
    (∀ i i' k k', u i k - u' i' k ∣ e * ϖ ^ (N + 1) ^ N →
      u i k - u' i' k ∣ e * (u i k' - u' i' k') ∨ u i k' - u' i' k' ∣ e * (u i k - u' i' k)) →
    ∃ σ : I ≃ I', ∀ i k, ϖ ∣ e * (u i k - u' (σ i) k)

def CountIn : Prop :=
  ∀ (k H : Type) [Field k] [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H), Module.finrank k C = 1 →
    Function.Bijective (fun D : {D : Submodule k H // C ≤ D} => D.1.map C.mkQ) ∧
    (∀ D : Submodule k H, C ≤ D → Module.finrank k D = Module.finrank k (D.map C.mkQ) + 1) ∧
    (∀ D : Submodule k H, ¬ C ≤ D → Module.finrank k D = Module.finrank k (D.map C.mkQ))

def CountOut : Prop :=
  ∀ (k H : Type) [Field k] [Finite k] [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H), Module.finrank k C = 1 →
    ∀ E : Submodule k (H ⧸ C), Nat.card {D : Submodule k H // ¬ C ≤ D ∧ D.map C.mkQ = E} = Nat.card k ^ Module.finrank k E

def OrdDecomp : Prop :=
  ∀ (q n : ℕ) (P : Type) (F : P → P) (I : Fin (n + 1) → Type) [∀ j, Fintype (I j)] (v : ∀ j, I j → P), OrdRead q n F v →
    ∃ A : ℕ → Multiset P, A n = 0 ∧ Finset.univ.val.map (v 0) = A 0 ∧
      ∀ j : Fin n, Finset.univ.val.map (v j.succ) = (A j).map F + q ^ ((j : ℕ) + 1) • A (j + 1)

def Telescope : Prop :=
  ∀ (q n : ℕ) (P : Type) (F : P → P) (T : Fin (n + 1) → Multiset P) (A : ℕ → Multiset P), A n = 0 → T 0 = A 0 →
    (∀ j : Fin n, T j.succ = (A j).map F + q ^ ((j : ℕ) + 1) • A (j + 1)) →
    ∑ j : Fin (n + 1), wEv q j • (T j).map F^[n - j] = ∑ j : Fin (n + 1), wOd q j • (T j).map F^[n - j]

def BaseOfSmooth : Prop :=
  ∀ (l : ℕ) (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing R] [Algebra O R] [Algebra.Smooth O R] (ϖ : O),
    Irreducible ϖ → (l : O) ≠ 0 → ¬ IsUnit (l : O) → BaseOK l R (Ideal.span {algebraMap O R ϖ})

def SmoothClosed : Prop :=
  ∀ (l : ℕ) (O R : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [CommRing R] [Algebra O R] [Algebra.Smooth O R],
    (l : O) ≠ 0 → ∀ c : Localization.Away (l : R), IsIntegral R c → ∃ r : R, algebraMap R _ r = c

def SmoothReduced : Prop := ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R], IsReduced R

def BaseOfChart : Prop :=
  ∀ (l : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O)), Smooth g →
    ∀ U : Y.Opens, IsAffineOpen U → BaseOK l Γ(Y, U) (Ideal.span {Y.presheaf.map (homOfLE le_top).op (fn g ϖ)}) ∧
      ∃ m : ℕ, (l : Γ(Y, U)) ^ m ∈ Ideal.span {Y.presheaf.map (homOfLE le_top).op (fn g ϖ)}

def ptOf {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (B : Type) [CommRing B] (f : Γ(Y, U) →+* B) :
    Spec (CommRingCat.of B) ⟶ Y := Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec

def SecChart : Prop :=
  ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Y.Opens) (hU : IsAffineOpen U),
    letI := T.alg U
    ∃ hZ : IsAffineOpen (T.p ⁻¹ᵁ U), ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U) B],
      ∃ e : (Γ(T.Z, T.p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B) ≃ T.Sec (ptOf hU B (algebraMap _ _)), ∀ z, (e z).1 = ptOf hZ B z.toRingHom

def EtChart : Prop :=
  ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Y.Opens), IsAffineOpen U →
    letI := T.alg U
    Algebra.Etale (Localization.Away (l : Γ(Y, U))) (Localization.Away (l : Γ(Y, U)) ⊗[Γ(Y, U)] Γ(T.Z, T.p ⁻¹ᵁ U))

def EtAwayChart : Prop :=
  ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Y.Opens), IsAffineOpen U →
    letI := T.alg U
    EtAway l T.d Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U)

def GenChart : Prop :=
  ∀ (Y : Scheme.{0}) (π : Γ(Y, ⊤)) (U : Y.Opens) (hU : IsAffineOpen U) (V : Type) [CommRing V] [IsLocalRing V] (f : Γ(Y, U) →+* V),
    (IsLocalRing.maximalIdeal V).comap f ∈ (Ideal.span {Y.presheaf.map (homOfLE le_top).op π} : Ideal Γ(Y, U)).minimalPrimes →
    GenPt π (ptOf hU V f (IsLocalRing.closedPoint V))

def PtChart : Prop :=
  ∀ (Y : Scheme.{0}) (V : Y.Opens) (hV : IsAffineOpen V) (κ : Type) [CommRing κ],
    Function.Injective (ptOf hV κ) ∧
    (∀ (φ : κ →+* κ) (f : Γ(Y, V) →+* κ) (m : ℕ), (twist φ Y)^[m] (ptOf hV κ f) = ptOf hV κ ((φ ^ m).comp f)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (W : Z.Opens) (hW : IsAffineOpen W) (h : W ≤ r ⁻¹ᵁ V) (B : Type) [CommRing B] (ρ : B →+* κ)
      (z : Γ(Z, W) →+* B),
      Spec.map (CommRingCat.ofHom ρ) ≫ ptOf hW B z ≫ r = ptOf hV κ (ρ.comp (z.comp (r.appLE V W h).hom))

end UpperTheory.Gal.crystallineComparison
end
end

